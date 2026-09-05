module reference_data/item/item_contracts

/*
 * ITEM — CONTRACTS (DT-017). The module's laws as NAMED predicates: everything a consumer may
 * rely on, and nothing else. types + contracts = the DOMAIN statement of this module.
 *
 * Since the DT-023 cut 7a log conversion the laws split by NATURE:
 *  - CONTENT laws (supply ownership, UoM ownership, supplier-ref soundness) remain AXIOMS —
 *    nothing deeper derives them; the implementation asserts them as facts, exactly as the
 *    static form did (the degenerate-form heritage, now content-only).
 *  - LIFECYCLE laws (Create-first, retirement-terminal) are THEOREMS of the guards + effects,
 *    proven in the suite (check, UNSAT = holds) and assumable by consumers via the mock.
 *  - The CHAINING law is the spine's, adopted as fact and re-published here so consumer unit
 *    roots get the log shape from the mock.
 */

open reference_data/item/item_types as it
open meta/subject_log/subject_log[it/Item, it/ItemState] as ilog   // same params ⇒ the SAME spine instance as item_types

// ── C1: supply ownership (versioned — DT-023 Q-C folding) ───────────────────────────────────────
/** Every ItemSupply belongs to exactly one Item's history and inherits its tenant; a state's
    default supply, when it resolves, is one of THAT STATE's own supplies. Consumers may
    navigate a version's sSupplies as a strict in-tenant set and trust default resolution. */
pred supplyOwnership {
  all c: ItemSupply | one i: Item | c in itemSuppliesOf[i]
  all i: Item, c: itemSuppliesOf[i] | c.tenantId = i.tenantId
  all s: ItemState | let d = resolve[s.sDefaultSupply] | some d implies d in s.sSupplies
}
/** itemSuppliesOf — every supply row appearing anywhere in `i`'s history (payloads + records). */
fun itemSuppliesOf[i: Item]: set ItemSupply {
  let os = { o: ItemOcc | o.subject = i } | os.post.sSupplies + (os & ItemWriteOcc).supplies
}

// ── C2: UoM schemes are owned (DT-009) ──────────────────────────────────────────────────────────
/** Every UomScheme belongs to exactly one Item (no orphan schemes). Scheme VALUE
    well-formedness is definitional and rides with the vocabulary (uom.als UomSchemeWF). */
pred uomSchemesSound { all s: UomScheme | one i: Item | i.uom = s }

// ── C3: supplier PINS are sound (DT-023 cut 7b — the dissolved-handle form) ─────────────────────
/** The supply row's vendor is a BA VERSION PIN + role selector (was the denormalized
    SupplierReference handle): a selector requires its pin; a pin is in-tenant; when the
    selector is present it is a VENDOR role of the PINNED version. Typed pins cannot dangle —
    the former soft-ref soundness clauses are unrepresentable. */
pred supplierPinsSound {
  all s: ItemSupply {
    some s.supplierPin iff some s.supplierRole   // together or not at all (DT-023 cut 8,
                                                 //   the PDEV-241 re-base: a vendor link
                                                 //   always names its VENDOR role)
    some s.supplierPin implies s.supplierPin.subject.tenantId = s.tenantId
    some s.supplierRole implies roleSelectorAgrees[s.supplierPin, s.supplierRole, VENDOR]
  }
}

// ── C4: the lifecycle shape (DT-023 R1 — theorem of guards + effects) ──────────────────────────
/** A committed first occurrence on an item is its Create (and Creates are only ever first);
    retirement is TERMINAL — nothing commits after the item's state is Retired. With the
    effects this yields the status shape: Live through Create/Update, Retired from Delete on. */
pred itemLifecycleShape {
  all o: ItemOcc | committed[o] implies {
    ((no ilog/priorOn[o]) iff o in CreateItemOcc)
    (some ilog/priorOn[o] implies (ilog/priorOn[o].post & ItemState).sStatus = RD_LIVE)
  }
}

// ── C5: the log is chained (the spine's law, re-published for mock consumers) ──────────────────
/** Every item occurrence — refusals included — reads the item's real current record. */
pred itemLogChained { ilog/chained }

// ── the promise ──────────────────────────────────────────────────────────────────────────────────
/** guarantees — the module's full promise: the conjunction of the published laws. */
pred guarantees {
  supplyOwnership and uomSchemesSound and supplierPinsSound
  and itemLifecycleShape and itemLogChained
}
