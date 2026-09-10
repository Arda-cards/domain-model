module resources/inventory_item/tests/unit/inventory_item

open resources/inventory_item/inventory_item_implementation
open resources/inventory_item/inventory_item_types  // DIRECT (rule 10): `inventory_item_types/CreateOcc` — the module's own kind, disambiguated from the lifecycle family's `lc/CreateOcc` now in the transitive namespace (Tier B 793cfe0 parse red, 2026-09-09)
open resources/inventory_item/inventory_item_contracts
open reference_data/item/item_mock                 // the LOWER LAYER as its CONTRACT (DT-017 two-layer PoC)

/*
 * UNIT suite for the InventoryItem module (DT-017; the former tests/occurrences.als): this
 * module's REAL implementation against the item module's MOCK — proving
 * `II_impl ∧ item_contract ⊨ II_contract` plus the log's own witnesses and theorems. The
 * integration tier (tests/integration/) re-runs the composition on the real item stack.
 * Joint-SAT obligation for the mock (vacuity guard): the witnesses below that force resolved
 * Items and UomSchemes (e.g. unit_occ_invalidUnitRefused) double as the `loads` witness.
 *
 * The cone is fully STATIC — the canonical entity is identity-only (DT-011). Scope notes: each
 * committed occurrence consumes a Tick + record + Quantity atoms — scopes size those families
 * generously and keep the rest small.
 */
// Premises come with the profile: the types file opens meta/profiles/domain_log (DT-012) —
// groupAxioms + orderAxioms are FACTS in this cone; no per-root premise assertion needed.

// ── CONTRACT DISCHARGE (check; UNSAT = the implementation satisfies the published law) ───────────
assert unit_ii_contract_stateFunction { stateIsFunctionOnceStarted }
check unit_ii_contract_stateFunction for 5 but 3 Scalar, 5 Int expect 0

assert unit_ii_contract_liveHaveState { liveHaveState }
check unit_ii_contract_liveHaveState for 5 but 3 Scalar, 5 Int expect 0

assert unit_ii_contract_bornLive { bornLive }
check unit_ii_contract_bornLive for 5 but 3 Scalar, 5 Int expect 0

assert unit_ii_contract_closureIsTerminal { closureIsTerminal }
check unit_ii_contract_closureIsTerminal for 5 but 3 Scalar, 5 Int expect 0

assert unit_ii_contract_touchesLiveness { touchesDetermineLiveness }
check unit_ii_contract_touchesLiveness for 5 but 3 Scalar, 5 Int expect 0

assert unit_ii_contract_readBack { committedWritesReadBack }
check unit_ii_contract_readBack for 5 but 3 Scalar, 5 Int, 8 Quantity expect 0

// ── SAT witnesses ─────────────────────────────────────────────────────────────────────────────────
// A committed Create: read back through the projections — live, with its born record.
run unit_occ_createReadsBack {
  some o: inventory_item_types/CreateOcc | committed[o]
    and liveAt[o.target, o.tick]
    and stateAt[o.target, o.tick] = o.post
    and o.post.sActual = o.qty
} for 5 but 3 Scalar, 5 Int expect 1

// A committed chain create → replenish → consume on one item, each reading the prior record.
run unit_occ_lifecycleChain {
  some ii: InventoryItem, c: inventory_item_types/CreateOcc, r: ReplenishOcc, k: ConsumeOcc | {
    c.target = ii and r.target = ii and k.target = ii
    precedes[c.tick, r.tick] and precedes[r.tick, k.tick]
    committed[c] and committed[r] and committed[k]
    r.pre = c.post and k.pre = r.post
    stateAt[ii, k.tick] = k.post
  }
} for 6 but 3 Scalar, 5 Int, 8 Quantity expect 1

// An overdraw is REFUSED with exactly ROverdraw (reason-precise witnessing).
run unit_occ_overdrawRefused {
  some o: ConsumeOcc | refusedAtAdmission[o] and o.admission.because = ROverdraw
} for 5 but 3 Scalar, 5 Int expect 1

// Resurrection is REFUSED: a Create over a deleted item's history carries RAlreadyExists.
run unit_occ_resurrectionRefused {
  some d: DeleteOcc, c: inventory_item_types/CreateOcc | {
    committed[d] and d.target = c.target and precedes[d.tick, c.tick]
    refusedAtAdmission[c] and RAlreadyExists in c.admission.because
  }
} for 5 but 3 Scalar, 5 Int expect 1

// A committed Split exists: both sides' records produced, the new item live, the origin still live.
run unit_occ_splitProjects {
  some o: SplitOcc | committed[o]
    and liveAt[o.nu, o.tick] and liveAt[o.target, o.tick]
    and stateAt[o.nu, o.tick] = o.nuPost
} for 6 but 3 Scalar, 5 Int, 8 Quantity expect 1

// A committed Merge retires the absorbed item and keeps the survivor live.
run unit_occ_mergeRetiresAbsorbed {
  some o: MergeOcc | committed[o]
    and liveAt[o.target, o.tick] and not liveAt[o.absorbed, o.tick]
} for 6 but 3 Scalar, 5 Int, 8 Quantity expect 1

// A committed Move relocates: only the locator changes (built ON DEMAND 2026-07-02 — the DT-007
// locator classification needed a locator writer; legacy parity rows unit_op_move_*).
run unit_occ_moveRelocates {
  some o: MoveOcc | committed[o]
    and stateAt[o.target, o.tick].sLocator = o.dest and o.pre.sLocator != o.dest
} for 5 but 3 Scalar, 5 Int expect 1

// Moving a SEALED item preserves the seal (D16 — locator change is not a real-quantity change).
run unit_occ_movePreservesSealed {
  some o: MoveOcc | committed[o] and o.pre.sFill = SEALED and o.post.sFill = SEALED
} for 5 but 3 Scalar, 5 Int expect 1

// Move on a LOCKED item is REFUSED with exactly RLocked (ForceMove — the privileged override — on demand).
run unit_occ_moveLockedRefused {
  some o: MoveOcc | refusedAtAdmission[o] and o.admission.because = RLocked
} for 5 but 3 Scalar, 5 Int expect 1

// ── theorems (check; UNSAT = holds) — invariants DERIVED from the witnessed guards ───────────────
// No committed consume overdraws (the guard, seen from the projection side).
assert unit_occ_noCommittedOverdraw {
  all o: ConsumeOcc | committed[o] implies gWithin[o.amount.byUnit, o.pre.sAvailableQty]
}
check unit_occ_noCommittedOverdraw for 5 but 3 Scalar, 5 Int expect 0

// LPN terminality: a committed Create never lands on an item with ANY committed history
// (delete tombstones included — no resurrection).
assert unit_occ_noResurrection {
  all o: inventory_item_types/CreateOcc | committed[o] implies no priorOn[o, o.target]
}
check unit_occ_noResurrection for 5 but 3 Scalar, 5 Int expect 0

// Once retired, an item is never live again (terminal retirement, via the guards).
assert unit_occ_terminalRetirement {
  all ii: InventoryItem, t1, t2: Tick |
    (notAfter[t1, t2] and some lastTouch[ii, t1] and not liveAt[ii, t1]) implies not liveAt[ii, t2]
}
check unit_occ_terminalRetirement for 5 but 3 Scalar, 5 Int expect 0

// CONSERVATION over Split: the origin's read quantity equals remainder + split-off (needs the ring
// premise — add/negate cancellation).
assert unit_occ_splitConserves {
  all o: SplitOcc | committed[o] implies
    o.pre.sActual.byUnit = add[o.post.sActual.byUnit, o.nuPost.sActual.byUnit]
}
check unit_occ_splitConserves for 5 but 3 Scalar, 5 Int, 8 Quantity expect 0

// CONSERVATION over Merge: the survivor's produced quantity is the sum of the two read quantities.
assert unit_occ_mergeConserves {
  all o: MergeOcc | committed[o] implies
    o.post.sActual.byUnit = add[o.pre.sActual.byUnit, o.absPre.sActual.byUnit]
}
check unit_occ_mergeConserves for 5 but 3 Scalar, 5 Int, 8 Quantity expect 0

// ── parity tranche (from the legacy lifecycle/ops checklists) ─────────────────────────────────────
// Seal is re-enterable (D16): seal → unseal round-trip, quantity untouched, fill back to OPEN.
run unit_occ_sealUnsealRoundTrip {
  some ii: InventoryItem, sl: SealOcc, us: UnsealOcc | {
    sl.target = ii and us.target = ii and precedes[sl.tick, us.tick]
    committed[sl] and committed[us] and us.pre = sl.post
    us.post.sFill = OPEN and us.post.sActual = sl.pre.sActual
  }
} for 6 but 3 Scalar, 5 Int, 8 Quantity expect 1

// A lock blocks consumption: a consume after a committed Lock is refused with exactly RLocked.
run unit_occ_lockBlocksConsume {
  some ii: InventoryItem, l: LockOcc, k: ConsumeOcc | {
    l.target = ii and k.target = ii and precedes[l.tick, k.tick]
    committed[l] and refusedAtAdmission[k] and k.admission.because = RLocked
  }
} for 6 but 3 Scalar, 5 Int, 8 Quantity expect 1

// Deplete-vs-delete (the D-rule): consume-to-zero leaves the item LIVE and revivable by Replenish.
run unit_occ_depleteThenRevive {
  some ii: InventoryItem, k: ConsumeOcc, r: ReplenishOcc | {
    k.target = ii and r.target = ii and precedes[k.tick, r.tick]
    committed[k] and committed[r]
    k.post.sFill = EMPTY and liveAt[ii, k.tick]
    r.pre = k.post and r.post.sFill != EMPTY
  }
} for 6 but 3 Scalar, 5 Int, 8 Quantity expect 1

// D17 as a theorem: no committed operation ever LENGTHENS an expiry (creates aside — they set it).
assert unit_occ_expiryNeverLengthens {
  all o: IIOcc - inventory_item_types/CreateOcc | committed[o] implies
    (some o.pre.sExpiration implies (some o.post.sExpiration and o.post.sExpiration <= o.pre.sExpiration))
}
check unit_occ_expiryNeverLengthens for 5 but 3 Scalar, 5 Int expect 0

// D16 as a theorem: SEALED is entered ONLY by Seal — no other committed kind transitions into it.
assert unit_occ_sealedOnlyBySeal {
  all o: IIOcc - SealOcc | committed[o] implies
    not (o.post.sFill = SEALED and o.pre.sFill != SEALED)
}
check unit_occ_sealedOnlyBySeal for 5 but 3 Scalar, 5 Int expect 0

// ── the Quantity-reframing tranche (2026-07-02): partiality + the valid-UoM rule ──────────────────
// An INCOMPARABLE consume (amount on a different unit basis) is refused with exactly RIncomparable —
// the conservative-refusal convention, distinct from a provable overdraw.
run unit_occ_incomparableRefused {
  some o: ConsumeOcc | refusedAtAdmission[o] and o.admission.because = RIncomparable
} for 5 but 3 Scalar, 5 Int expect 1

// DT-009's valid-UoM rule: a TRACKED item's operation using a unit outside its scheme is refused
// carrying RInvalidUnit.
run unit_occ_invalidUnitRefused {
  some o: ConsumeOcc | refusedAtAdmission[o] and RInvalidUnit in o.admission.because
    and some schemeOf[o.target]
} for 5 but 3 Scalar, 5 Int expect 1

// The rule as a theorem: committed operations on tracked items use only scheme units.
assert unit_occ_committedUnitsValid {
  all o: ConsumeOcc | committed[o] implies unitsOk[o.amount.byUnit, o.target]
}
check unit_occ_committedUnitsValid for 5 but 3 Scalar, 5 Int expect 0

// ── PARITY COMPLETION (2026-07-02) — the legacy checklists, log-side ─────────────────────────────
// Firings and per-reason refusals not yet witnessed above; the grouped parity map (incl. recorded
// deviations) is design/resources/inventory-item/verification/occurrences.md §Parity.

// Delete fires: an EMPTY item committed-deleted; not live at the delete's tick.
run unit_occ_deleteFires {
  some o: DeleteOcc | committed[o] and o.pre.sFill = EMPTY and not liveAt[o.target, o.tick]
} for 5 but 3 Scalar, 5 Int expect 1

// WriteOff (privileged) fires on a NON-empty item.
run unit_occ_writeOffFires {
  some o: WriteOffOcc | committed[o] and o.pre.sFill != EMPTY and not liveAt[o.target, o.tick]
} for 5 but 3 Scalar, 5 Int expect 1

// AdjustQuantity to observed zero reconciles to the EMPTY husk (qualifiers cleared).
run unit_occ_adjustToZero {
  some o: AdjustQuantityOcc | committed[o] and isZero[o.good.byUnit] and no o.degObs
    and o.post.sFill = EMPTY and no o.post.sDegraded and no o.post.sLots
} for 5 but 3 Scalar, 5 Int expect 1

// Inspect sets degraded = actual → derived DISABLED; a clearing inspect → ENABLED.
run unit_occ_inspectDisables {
  some o: InspectOcc | committed[o] and some o.degObs
    and o.post.sOperationalState = DISABLED and not isZero[o.post.sActual.byUnit]
} for 5 but 3 Scalar, 5 Int expect 1
run unit_occ_inspectClears {
  some o: InspectOcc | committed[o] and no o.degObs
    and some o.pre.sDegraded and no o.post.sDegraded and o.post.sOperationalState = ENABLED
} for 5 but 3 Scalar, 5 Int expect 1

// rePack preserves SEALED (D16: re-expression is not a real-quantity change).
run unit_occ_rePackPreservesSealed {
  some o: RePackOcc | committed[o] and o.pre.sFill = SEALED and o.post.sFill = SEALED
} for 5 but 3 Scalar, 5 Int, 8 Quantity expect 1

// Unlock fires (LOCKED → UNLOCKED).
run unit_occ_unlockFires {
  some o: UnlockOcc | committed[o] and o.pre.sAdmin = LOCKED and o.post.sAdmin = UNLOCKED
} for 5 but 3 Scalar, 5 Int expect 1

// A real draw breaks the seal: consume on a SEALED item demotes to OPEN.
run unit_occ_consumeDemotesSealed {
  some o: ConsumeOcc | committed[o] and o.pre.sFill = SEALED and o.post.sFill = OPEN
} for 5 but 3 Scalar, 5 Int, 8 Quantity expect 1

// Split isolates spoilage: split off ALL the degraded portion → origin ENABLED, new item DISABLED.
run unit_occ_splitIsolatesDegraded {
  some o: SplitOcc | committed[o] and no o.soGood and some o.soDeg
    and o.post.sOperationalState = ENABLED and o.nuPost.sOperationalState = DISABLED
} for 6 but 3 Scalar, 5 Int, 8 Quantity expect 1

// Consume the available part of a DEGRADED item → the DISABLED husk-of-degraded.
run unit_occ_consumeToDisabled {
  some o: ConsumeOcc | committed[o]
    and some o.pre.sDegraded and not isZero[o.post.sActual.byUnit]
    and o.post.sOperationalState = DISABLED
} for 5 but 3 Scalar, 5 Int, 8 Quantity expect 1

// D17 witnesses: create sets the expiry; merge takes the earlier of the two.
run unit_occ_createWithExpiration {
  some o: inventory_item_types/CreateOcc | committed[o] and o.exp = 4 and o.post.sExpiration = 4
} for 5 but 3 Scalar, 5 Int expect 1
run unit_occ_mergeMinExpiration {
  some o: MergeOcc | committed[o]
    and o.pre.sExpiration = 3 and o.absPre.sExpiration = 7 and o.post.sExpiration = 3
} for 6 but 3 Scalar, 5 Int, 8 Quantity expect 1

// Per-reason refusal witnesses (each recorded with its exact violation set):
run unit_occ_deleteNonEmptyRefused {
  some o: DeleteOcc | refusedAtAdmission[o] and o.admission.because = RNotApplicable
} for 5 but 3 Scalar, 5 Int expect 1
run unit_occ_consumeDisabledRefused {
  some o: ConsumeOcc | refusedAtAdmission[o] and RUnfit in o.admission.because
} for 5 but 3 Scalar, 5 Int expect 1
run unit_occ_replenishLockedRefused {
  some o: ReplenishOcc | refusedAtAdmission[o] and o.admission.because = RLocked
} for 5 but 3 Scalar, 5 Int expect 1
run unit_occ_splitSerializedRefused {
  some o: SplitOcc | refusedAtAdmission[o] and RSerialized in o.admission.because
} for 6 but 3 Scalar, 5 Int expect 1
run unit_occ_mergeDifferentItemRefused {
  some o: MergeOcc | refusedAtAdmission[o] and o.admission.because = RIncompatible
    and o.target.itemPin.subject != o.absorbed.itemPin.subject
} for 6 but 3 Scalar, 5 Int expect 1
run unit_occ_sealEmptyRefused {
  some o: SealOcc | refusedAtAdmission[o] and o.admission.because = REmpty
} for 5 but 3 Scalar, 5 Int expect 1
run unit_occ_lockAlreadyLockedRefused {
  some o: LockOcc | refusedAtAdmission[o] and o.admission.because = RNotApplicable
} for 5 but 3 Scalar, 5 Int expect 1
run unit_occ_nonPositiveRefused {
  some o: inventory_item_types/CreateOcc | refusedAtAdmission[o] and o.admission.because = RNonPositive
} for 5 but 3 Scalar, 5 Int expect 1
run unit_occ_notLiveRefused {
  some o: ConsumeOcc | refusedAtAdmission[o] and RNotLive in o.admission.because
} for 5 but 3 Scalar, 5 Int expect 1

// Structural guards inherited from the legacy structure suite (the entity facts, regression-guarded):
run unit_occ_lpnClashImpossible {
  some disj a, b: InventoryItem | a.licensePlate = b.licensePlate
} for 5 but 3 Scalar, 5 Int expect 0
run unit_occ_serialClashImpossible {
  some disj a, b: InventoryItem | a.tenantId = b.tenantId and a.itemPin.subject = b.itemPin.subject
    and some a.serialNumber and a.serialNumber = b.serialNumber
} for 5 but 3 Scalar, 5 Int expect 0
run unit_occ_crossTenantClassifierImpossible {
  some ii: InventoryItem | let i = ii.itemPin.subject |
    i.tenantId != ii.tenantId
} for 5 but 3 Scalar, 5 Int expect 0

// End-to-end lifecycle (the legacy lifecycle suite's spine): create → consume-to-zero (LIVE husk) →
// replenish (revived) → consume-to-zero → delete (retired forever).
run unit_occ_endToEnd {
  some ii: InventoryItem, c: inventory_item_types/CreateOcc, k1: ConsumeOcc, r: ReplenishOcc, k2: ConsumeOcc, d: DeleteOcc | {
    c.target = ii and k1.target = ii and r.target = ii and k2.target = ii and d.target = ii
    precedes[c.tick, k1.tick] and precedes[k1.tick, r.tick]
    precedes[r.tick, k2.tick] and precedes[k2.tick, d.tick]
    committed[c] and committed[k1] and committed[r] and committed[k2] and committed[d]
    k1.post.sFill = EMPTY and liveAt[ii, k1.tick]
    r.post.sFill != EMPTY
    k2.post.sFill = EMPTY
    not liveAt[ii, d.tick]
  }
} for 7 but 3 Scalar, 5 Int, 10 Quantity, 7 Tick expect 1
