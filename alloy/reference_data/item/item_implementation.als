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
open meta/activation/activation   // the activation every row cites (DT-015 D1 to D3)

// ── the spine adoptions ─────────────────────────────────────────────────────────────────────────
fact ItemChain { ilog/chained }
one sig ItemService extends Service {}   // DT-015 R2: the service's activation log, adopted beside the spine
fact ItemActivated { activated[ItemService, ilog/SubjectOcc] }

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
/** itemSuppliesBefore — the supply rows in `i`'s committed history strictly before `t` (what a write at `t` reads of its peers). */
fun itemSuppliesBefore[i: Item, t: Tick]: set ItemSupply {
  { o: ItemOcc | o.subject = i and committed[o] and precedes[o.tick, t] }.post.sSupplies
}
/** itemContentViol — QA704 Q4 (a), DT-009 Q27: the three content facts as the arms they are in dafny-domain
    src/reference-data/item/item.dfy `ContentViol`. RSupplyNotOwned: a row ANOTHER item's committed history holds, a row of
    another tenant, or a default supply outside this write's rows (`SuppliesOwnedBy`). RSupplierPinUnsound: a pin without its
    role selector or a selector without its pin, a pin outside the row's tenant, a selector that is not a VENDOR role of the
    pinned version (`PinsSoundAt`). RSupplierPinStale: a pin that is not the vendor's current version at the write
    (`PinsCurrentAt`; was the fact `ItemSupplyPinCurrency`). The contract laws are their theorems over committed history. */
fun itemContentViol[o: ItemWriteOcc]: set Reason {
  ((some s: o.supplies | s.tenantId != o.subject.tenantId or (some i: Item - o.subject | s in itemSuppliesBefore[i, o.tick]))
    or (some resolve[o.defaultSupply] and resolve[o.defaultSupply] not in o.supplies)
   => RSupplyNotOwned else none)
  + ((some s: o.supplies | not (some s.supplierPin iff some s.supplierRole)
       or (some s.supplierPin and s.supplierPin.subject.tenantId != s.tenantId)
       or (some s.supplierRole and not roleSelectorAgrees[s.supplierPin, s.supplierRole, VENDOR]))
     => RSupplierPinUnsound else none)
  + ((some s: o.supplies | some s.supplierPin and not pinsCurrentBa[s.supplierPin, o.tick]) => RSupplierPinStale else none)
}
/** createItemViol — Create refuses an already-created subject (the generic create arm), a retired-vendor row, and the content arms. */
fun createItemViol[o: CreateItemOcc]: set Reason {
  lc/createViol[o, RItemExists] + supplyRetiredViol[o] + itemContentViol[o]
}
/** itemMutateViol — Update/Retire refuse an uncreated or already-retired subject (the generic liveness
    conditions; the module's two atoms — the closed atom split in two). */
fun itemMutateViol[o: ItemOcc]: set Reason {
  ((not lc/startedBefore[o]) => RItemNotCreated else none)
  + (lc/retiredBefore[o] => RItemRetired else none)
}

fact ItemAdmissionWitnessed {
  all o: CreateItemOcc | (o.admission = Accepted iff no createItemViol[o]) and (o.admission in Rejected implies o.admission.because = createItemViol[o])
  all o: UpdateItemOcc | let v = itemMutateViol[o] + supplyRetiredViol[o] + itemContentViol[o] | (o.admission = Accepted iff no v) and (o.admission in Rejected implies o.admission.because = v)
  all o: RetireItemOcc | (o.admission = Accepted iff no itemMutateViol[o]) and (o.admission in Rejected implies o.admission.because = itemMutateViol[o])
}

// (Supply-pin currency, DT-023 Q-A, is the RSupplierPinStale arm of itemContentViol since QA704 Q4 (a); its law is the theorem tests/item.als unit_item_supplyPinCurrencyHolds.)

// ── effects (SET semantics on the write kinds; the retire's tombstone is the lifecycle module's `RetireEffect`) ──
fact ItemEffects {
  all o: ItemWriteOcc | committed[o] implies {
    o.post.sSupplies            = o.supplies
    o.post.sDefaultSupply       = o.defaultSupply
    o.post.sCardMinimumQuantity = o.cardMinimumQuantity
  }
}


// ── the content axiom that STAYS (C2, identity-carried: nothing deeper derives it); C1 and C3 are THEOREMS of itemContentViol
// since QA704 Q4 (a) (tests/item.als unit_item_supplyOwnership and the refusal witnesses) ────────────────────────────────────────
fact ItemContentLaws { uomSchemesSound }
