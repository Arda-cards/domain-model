module reference_data/item/item_implementation

/*
 * ITEM — IMPLEMENTATION (DT-017). Integration roots open this file to get the REAL module.
 *
 * Since the DT-023 cut 7a log conversion the module is NO LONGER static-degenerate: the
 * lifecycle machinery (chaining, reason-precise admission, effects) lives here, and the
 * contract's lifecycle laws are THEOREMS of it (proven in tests/item.als). The CONTENT laws
 * (ownership/refs — C1..C3) remain asserted axioms: nothing deeper derives them.
 */

open reference_data/item/item_contracts
open reference_data/item/item_types as it   // rule 10: the parameter below was resolving through a transitive open
open meta/subject_log/subject_log[it/Item, it/ItemState] as ilog   // same params ⇒ the SAME spine instance as item_types
open meta/subject_log/lifecycle[it/Item, it/ItemState] as lc       // same params ⇒ the SAME shapes instance

// ── the spine adoptions ─────────────────────────────────────────────────────────────────────────
fact ItemChain { ilog/chained }
fact ItemCommitPolicy { ilog/commitAlwaysAccepts }

// ── reason-precise admission (the witnessing idiom) ─────────────────────────────────────────────
/** supplyRetiredViol — DT-023 cut 7b: a write INTRODUCING a supply row whose vendor pin's
    affiliate is not Live refuses with RRetiredRef (a new supply row is a new sourcing
    commitment — the D3 matrix row, model-realized now that both sides are log-carried);
    re-stated rows already in the prior state are grandfathered. */
fun supplyRetiredViol[o: ItemWriteOcc]: set Reason {
  ((some s: o.supplies - o.pre.sSupplies |
      some s.supplierPin and not baLiveAt[s.supplierPin.subject, o.tick])
   => RRetiredRef else none)
}
/** createItemViol — Create refuses an already-created subject (the generic create arm) or a retired-vendor row. */
fun createItemViol[o: CreateItemOcc]: set Reason {
  lc/createViol[o, RItemExists] + supplyRetiredViol[o]
}
/** itemMutateViol — Update/Retire refuse an uncreated or already-retired subject (the generic liveness
    conditions; the module's two atoms — the closed atom split in two). */
fun itemMutateViol[o: ItemOcc]: set Reason {
  ((not lc/startedBefore[o]) => RItemNotCreated else none)
  + (lc/retiredBefore[o] => RItemRetired else none)
}

fact ItemAdmissionWitnessed {
  all o: CreateItemOcc | (o.admission = Accepted iff no createItemViol[o]) and (o.admission in Rejected implies o.admission.because = createItemViol[o])
  all o: UpdateItemOcc | let v = itemMutateViol[o] + supplyRetiredViol[o] | (o.admission = Accepted iff no v) and (o.admission in Rejected implies o.admission.because = v)
  all o: RetireItemOcc | (o.admission = Accepted iff no itemMutateViol[o]) and (o.admission in Rejected implies o.admission.because = itemMutateViol[o])
}

// ── supply-pin currency (DT-023 Q-A: a committed write's vendor pins are then-current) ─────────
fact ItemSupplyPinCurrency {
  all o: ItemWriteOcc | committed[o] implies
    all s: o.supplies | some s.supplierPin implies pinsCurrentBa[s.supplierPin, o.tick]
}

// ── effects (SET semantics on the write kinds; the retire's tombstone is the lifecycle module's `RetireEffect`) ──
fact ItemEffects {
  all o: ItemWriteOcc | committed[o] implies {
    o.post.sSupplies            = o.supplies
    o.post.sDefaultSupply       = o.defaultSupply
    o.post.sCardMinimumQuantity = o.cardMinimumQuantity
  }
}

// ── the content axioms (C1..C3 — see the contracts header for why these are facts) ─────────────
fact ItemContentLaws { supplyOwnership and uomSchemesSound and supplierPinsSound }
