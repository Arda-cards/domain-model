module reference_data/item/tests/item

open meta/kernel
open reference_data/item/item_implementation

/*
 * Item-module verification (LOG-CARRIED since DT-023 cut 7a). The cross-module
 * supply→supplier reference chain is verified in reference_data/shared/tests (it spans both
 * modules). Content axioms get witnesses (joint satisfiability); lifecycle laws get CHECKS
 * (theorems of the guards + effects).
 */

// ── content witnesses ───────────────────────────────────────────────────────────────────────────

// The module loads: an item with a committed Create carrying a supply exists.
run unit_item_coherent {
  some o: CreateItemOcc | committed[o] and some o.supplies
} for 6 but 2 RoleDetail, 4 Tick, 3 Snapshot, 3 Occurrence expect 1

// Supply-row ownership is exclusive across COMMITTED histories (C1, a THEOREM of the RSupplyNotOwned arm since QA704 Q4 (a)) — UNSAT = holds.
check unit_item_supplyOwnership {
  no c: ItemSupply | some disj i1, i2: Item | c in itemSuppliesOf[i1] and c in itemSuppliesOf[i2]
} for 6 but 2 RoleDetail, 4 Tick, 4 Snapshot, 4 Occurrence expect 0

// ── QA704 Q4 (a), DT-009 Q27: the three content facts are guard arms (reflects dafny-domain src/reference-data/item/item.dfy ContentViol) ──
// A write stating a supply row another item's committed history already holds is refused with exactly RSupplyNotOwned.
// RED on the tree before the arms: `supplyOwnership` was a FACT, so the second item's write was unrepresentable (UNSAT).
run unit_item_supplyNotOwnedRefused {
  some disj i1, i2: Item, c1, c2: CreateItemOcc, s: ItemSupply {
    c1.subject = i1 and committed[c1] and s in c1.supplies
    c2.subject = i2 and precedes[c1.tick, c2.tick] and s in c2.supplies
    c2.admission in Rejected and c2.admission.because = RSupplyNotOwned
  }
} for 6 but 2 RoleDetail, 4 Tick, 3 Snapshot, 3 Occurrence expect 1
// A write whose supply row names a role selector without its pin is refused with exactly RSupplierPinUnsound.
run unit_item_supplierPinUnsoundRefused {
  some c: CreateItemOcc, s: c.supplies | no s.supplierPin and some s.supplierRole
    and c.admission in Rejected and c.admission.because = RSupplierPinUnsound
} for 6 but 2 RoleDetail, 4 Tick, 3 Snapshot, 3 Occurrence expect 1
// A write whose supply row pins a vendor version that is not the current one at the write is refused with exactly
// RSupplierPinStale. RED before: `ItemSupplyPinCurrency` was a FACT over committed writes, and the solver could still make the
// write refused for no reason of the guard's — now the stale pin IS the reason.
run unit_item_supplierPinStaleRefused {
  some c: CreateItemOcc, s: c.supplies, p: s.supplierPin | not pinsCurrentBa[p, c.tick]
    and c.admission in Rejected and c.admission.because = RSupplierPinStale
} for 6 but 2 RoleDetail, 5 Tick, 4 Snapshot, 4 Occurrence expect 1
// The currency law is now a THEOREM of the arm: every committed write's vendor pins are current at its tick.
check unit_item_supplyPinCurrencyHolds {
  all o: ItemWriteOcc | committed[o] implies all s: o.supplies | some s.supplierPin implies pinsCurrentBa[s.supplierPin, o.tick]
} for 6 but 2 RoleDetail, 5 Tick, 4 Snapshot, 4 Occurrence expect 0

// ── Inventory-tracking mode & UoM scheme (DT-009 — identity-carried, version-independent) ──────
// A tracked Item exists with a multi-unit scheme (`each` + another configured unit).
run unit_item_trackedScheme {
  some i: Item | inventoryTracked[i] and some u: i.uom.units | u != Each
} for 6 but 2 RoleDetail, 4 Tick, 3 Snapshot, 3 Occurrence expect 1

// A tracked and a non-tracked Item coexist (the mode is per-Item).
run unit_item_modesCoexist {
  some i, j: Item | inventoryTracked[i] and not inventoryTracked[j]
} for 6 but 2 RoleDetail, 4 Tick, 3 Snapshot, 3 Occurrence expect 1

// Every scheme configures `each` with factor 1.0 — regression on UomSchemeWF.
check unit_item_eachConfigured {
  all s: UomScheme | some s.factor[Each] and s.factor[Each] = SOne
} for 6 but 2 RoleDetail, 4 Tick, 3 Snapshot, 3 Occurrence expect 0

// Converting an amount already in `each` is the identity (factor 1.0) — needs the ring identity.
check unit_item_toEachIdentity {
  ringAxioms implies all s: UomScheme, amt: Scalar | toEach[s, Each, amt] = amt
} for 6 but 2 RoleDetail, 3 Scalar, 4 Tick, 3 Snapshot, 3 Occurrence expect 0

// ── CUT 6 (DT-022 TQ-4): the card-issuance default, now version-carried ────────────────────────
run unit_item_cardMinimumDefault {
  some i: Item, t: Tick | some itemStateAt[i, t].sCardMinimumQuantity
} for 5 but 2 RoleDetail, 4 Tick, 3 Snapshot, 3 Occurrence expect 1

// ── DT-023 cut 7a: the lifecycle (R1) ──────────────────────────────────────────────────────────

// The full arc: Create (live) → Update (live, content changed) → Delete (retired). One item,
// three committed occurrences; the read API tracks the statuses.
run unit_item_lifecycleArc {
  some i: Item, c: CreateItemOcc, u: UpdateItemOcc, d: RetireItemOcc {
    c.subject = i and u.subject = i and d.subject = i
    committed[c] and committed[u] and committed[d]
    precedes[c.tick, u.tick] and precedes[u.tick, d.tick]
    itemLiveAt[i, u.tick] and not itemLiveAt[i, d.tick]
    u.post.sSupplies != c.post.sSupplies
  }
} for 6 but 2 RoleDetail, 5 Tick, 4 Snapshot, 3 Occurrence expect 1

// The lifecycle shape is a THEOREM of the guards + effects — UNSAT = holds.
check unit_item_lifecycleShape { itemLifecycleShape } for 6 but 2 RoleDetail, 6 Tick, 5 Snapshot, 5 Occurrence expect 0

// Reason-precise refusal: mutating a retired item refuses with exactly RItemRetired.
run unit_item_retiredMutateRefused {
  some d: RetireItemOcc, u: UpdateItemOcc {
    committed[d] and u.subject = d.subject and precedes[d.tick, u.tick]
    u.admission in Rejected and u.admission.because = RItemRetired
  }
} for 6 but 2 RoleDetail, 5 Tick, 4 Snapshot, 3 Occurrence expect 1

// ── DT-023 cut 7a: version pins (R3) ───────────────────────────────────────────────────────────

// A pinnable version exists: current at t and Live — what an introducing consumer may pin.
run unit_item_versionPinnable {
  some p: ItemOcc, t: Tick | itemPinnableAt[p, t]
} for 6 but 2 RoleDetail, 4 Tick, 3 Snapshot, 3 Occurrence expect 1

// The pinned read survives retirement (the grandfather half, module-side): a version pinned
// while live still serves its content after the item retires — pins never go stale-by-time.
run unit_item_pinSurvivesRetirement {
  some p: ItemOcc, t1, t2: Tick {
    itemPinnableAt[p, t1]
    precedes[t1, t2] and not itemLiveAt[p.subject, t2]
    some p.post
  }
} for 6 but 2 RoleDetail, 5 Tick, 4 Snapshot, 3 Occurrence expect 1

// ── DT-023 cut 7b: the supply rows' vendor PIN (handle dissolution) ────────────────────────────

// A committed Create carries a vendor-pinned, role-selected supply row; the pin is current
// and Live at the write (the currency fact + supplierPinsSound jointly satisfiable).
// Fixture: reference-data-first — the BA Create precedes the item Create.
run unit_item_supplyVendorPinned {
  some o: CreateItemOcc, s: o.supplies {
    committed[o]
    some s.supplierPin and some s.supplierRole
    baPinnableAt[s.supplierPin, o.tick]
  }
} for 6 but 2 RoleDetail, 5 Tick, 4 Snapshot, 4 Occurrence expect 1

// Reason-precise refusal (the D3 new-supply-row gate, model-realized at 7b): a write
// INTRODUCING a row pinned to a RETIRED affiliate refuses with exactly RRetiredRef.
// Fixture: BA Create → BA Delete → item Create carrying the pin.
run unit_item_supplyRetiredVendorRefused {
  some o: CreateItemOcc, s: o.supplies, d: RetireBaOcc {
    committed[d]
    some s.supplierPin and s.supplierPin.subject = d.subject
    o.admission in Rejected and o.admission.because = RRetiredRef
  }
} for 6 but 2 RoleDetail, 6 Tick, 5 Snapshot, 4 Occurrence expect 1

// ── DT-030 retire cut (2026-09-09): terminality and the tombstone ────────────────────────────────
assert unit_item_nothingAfterRetire {
  all r: RetireItemOcc, o: CreateItemOcc + UpdateItemOcc + RetireItemOcc | (committed[r] and committed[o] and o.subject = r.subject) implies not precedes[r.tick, o.tick]
}
check unit_item_nothingAfterRetire for 6 but 2 RoleDetail, 5 Tick, 4 Snapshot, 3 Occurrence expect 0
assert unit_item_retireIsTombstone { all r: RetireItemOcc | committed[r] implies (r.post = r.pre and not itemLiveAt[r.subject, r.tick]) }
check unit_item_retireIsTombstone for 6 but 2 RoleDetail, 5 Tick, 4 Snapshot, 3 Occurrence expect 0
