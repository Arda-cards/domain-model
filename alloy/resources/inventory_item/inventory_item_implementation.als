module resources/inventory_item/inventory_item_implementation

/*
 * INVENTORY ITEM — IMPLEMENTATION (DT-017; the former occurrences.als, strict rename
 * 2026-07-03). The MATH that realizes the contract: the occurrence log plus the BRIDGE facts
 * (end of file) deriving the types-level observables (`stateRel`/`liveTicks`) from it. Opened
 * by integration roots and by this module's own files (metrics.als — intra-module exemption);
 * cross-module consumers open inventory_item_types/_mock instead (lint-guarded).
 *
 * The InventoryItem OCCURRENCE LOG (DT-006 domain build): each staged operation is a
 * StatefulAction kind carrying typed bindings + the state records it read (`pre`) and produced
 * (`post`); guards are REASON-PRECISE witnessed (admission = Accepted iff no violations; a
 * rejection carries EXACTLY the violated reasons); Effects are witnessed against the shared
 * transition cores (transitions.als); chaining is UNCONDITIONAL per touched item (a refused
 * occurrence still read the real state); state-at-t is LOCF of records (stateAt), existence is the
 * separate liveAt projection. Multi-item kinds (Split/Merge) carry per-role record fields beyond
 * pre/post; a retiring occurrence's "post role" for the retired item is its read state (TOMBSTONE
 * — satisfies PostOnlyIfCommitted; liveAt is what readers consult).
 *
 * Kinds: the quantity/degraded writers (Create, Delete, WriteOff, Replenish, Consume,
 * AdjustQuantity, Inspect, RePack, Split, Merge) + the state writers (Lock/Unlock, Seal/Unseal).
 * Move/AdjustProperties follow on demand. Authorization (WriteOff privileged, ABAC via the
 * `attributed` extension) is the deferred commit-guard hook.
 *
 * SPINE NOTE — this log stays BESPOKE (DT-015 Q5, ruled 2026-07-03; deliberately NOT ported to
 * `meta/subject_log`, unlike the InventoryPool and CardCycle logs): the multi-subject kinds
 * (Split/Merge) chain PER-ROLE (`priorOn[o, ii]`, `preFor`/`postFor` over `touches`), which the
 * single-subject spine cannot carry — this log is the maximal exemplar the spine was extracted
 * FROM. A touches-generalized spine becomes a NEW design topic if a second multi-subject
 * consumer appears (`Load`/HU nesting is the likely candidate).
 */

open meta/profiles/domain_log          // PROFILE (DT-012): log anatomy + group/order premises IN FORCE for the whole cone
open meta/action/stateful                            // StatefulAction (pre/post), committed, committedUpTo, …
open resources/inventory_item/inventory_item_types   // entity + record + observables + read API
open resources/inventory_item/transitions            // the value-parameterized cores + g* guard checks

// The Reason taxonomy, the kinds (IIOcc + the fifteen operation sigs), and the per-role read API
// (touches, retiringFor, postFor, preFor, schemeOf, unitsOk) are PUBLIC SURFACE — declared in
// inventory_item_types.als (MP ruling 2026-07-03: the Action sigs are the behavioral contract
// surface). This file supplies their SEMANTICS: guards, witnessing, chaining, effects, bridge.

// ── UNCONDITIONAL chaining: every occurrence read the real prior state of every item it touches ──
fun priorOn[o: IIOcc, ii: InventoryItem]: lone IIOcc {
  { b: IIOcc | committed[b] and ii in touches[b] and precedes[b.tick, o.tick]
      and (no c: IIOcc | committed[c] and ii in touches[c]
             and precedes[b.tick, c.tick] and precedes[c.tick, o.tick]) }
}
fact IIChaining {
  all o: IIOcc, ii: touches[o] - (o & SplitOcc).nu | preFor[o, ii] = postFor[priorOn[o, ii], ii]
}

/** liveBefore — ii exists just before o's tick: some committed history whose last touch didn't retire it. */
pred liveBefore[o: IIOcc, ii: InventoryItem] {
  let p = priorOn[o, ii] | some p and not retiringFor[p, ii]
}

// ── reason-precise admission guards (violation sets; Accepted ⟺ ∅; because = EXACTLY the set) ────
fun createViol[o: inventory_item_types/CreateOcc]: set Reason {
  ((some priorOn[o, o.target]) => RAlreadyExists else none)      // incl. tombstones: LPN never resurrects
  + ((not gPositive[o.qty.byUnit]) => RNonPositive else none)
  + ((not unitsOk[o.qty.byUnit, o.target]) => RInvalidUnit else none)
}
// DT-023 cut 7a: a committed birth pins the item's CURRENT version at its tick (Q-A currency).
// Deliberately NO RRetiredRef guard here — inventory birth is CAPTURE riding upstream-guarded
// commitments (the D3 grandfather principle: a receiving line added pre-retirement still
// births; at-rest stock of a retired item is legal). The new-commitment gates live in
// demand/order/receiving/kanban. A birth after retirement simply pins the retired version.
fact ItemPinCurrency {
  all o: inventory_item_types/CreateOcc | committed[o] implies pinsCurrentItem[o.target.itemPin, o.tick]
}
fun deleteViol[o: DeleteOcc]: set Reason {
  ((not liveBefore[o, o.target]) => RNotLive else none)
  + ((liveBefore[o, o.target] and o.pre.sFill != EMPTY) => RNotApplicable else none)   // use WriteOff
}
fun writeOffViol[o: WriteOffOcc]: set Reason {
  ((not liveBefore[o, o.target]) => RNotLive else none)          // privileged: no fill guard
}
fun replenishViol[o: ReplenishOcc]: set Reason {
  ((not liveBefore[o, o.target]) => RNotLive else none)
  + ((liveBefore[o, o.target] and o.pre.sAdmin != UNLOCKED) => RLocked else none)
  + ((liveBefore[o, o.target] and o.pre.sOperationalState = DISABLED) => RUnfit else none)
  + ((not gPositive[o.delta.byUnit]) => RNonPositive else none)
  + ((liveBefore[o, o.target] and isSerialized[o.target] and not isZero[o.pre.sActual.byUnit])
       => RSerialized else none)
  + ((not unitsOk[o.delta.byUnit, o.target]) => RInvalidUnit else none)
}
fun consumeViol[o: ConsumeOcc]: set Reason {
  ((not liveBefore[o, o.target]) => RNotLive else none)
  + ((liveBefore[o, o.target] and o.pre.sAdmin != UNLOCKED) => RLocked else none)
  + ((liveBefore[o, o.target] and o.pre.sOperationalState = DISABLED) => RUnfit else none)
  + ((liveBefore[o, o.target] and o.pre.sFill = EMPTY) => REmpty else none)
  + ((not gPositive[o.amount.byUnit]) => RNonPositive else none)
  + ((liveBefore[o, o.target] and gComparable[o.amount.byUnit, o.pre.sAvailableQty]
        and not gWithin[o.amount.byUnit, o.pre.sAvailableQty]) => ROverdraw else none)
  + ((liveBefore[o, o.target] and not gComparable[o.amount.byUnit, o.pre.sAvailableQty])
        => RIncomparable else none)
  + ((not unitsOk[o.amount.byUnit, o.target]) => RInvalidUnit else none)
  + ((liveBefore[o, o.target] and isSerialized[o.target]
        and not gAllOf[o.amount.byUnit, o.pre.sAvailableQty]) => RSerialized else none)
}
fun adjustQuantityViol[o: AdjustQuantityOcc]: set Reason {
  ((not liveBefore[o, o.target]) => RNotLive else none)
  + ((not gNonNegative[o.good.byUnit] or (some o.degObs and not gNonNegative[o.degObs.byUnit]))
       => RNonPositive else none)
  + ((not (unitsOk[o.good.byUnit, o.target] and unitsOk[o.degObs.byUnit, o.target]))
       => RInvalidUnit else none)
}
fun inspectViol[o: InspectOcc]: set Reason {
  ((not liveBefore[o, o.target]) => RNotLive else none)
  + ((liveBefore[o, o.target] and o.pre.sFill = EMPTY) => REmpty else none)
  + ((some o.degObs and not gNonNegative[o.degObs.byUnit]) => RNonPositive else none)
  + ((liveBefore[o, o.target] and some o.degObs and gComparable[o.degObs.byUnit, o.pre.sActual.byUnit]
        and not gWithin[o.degObs.byUnit, o.pre.sActual.byUnit]) => RIncompatible else none)
  + ((liveBefore[o, o.target] and some o.degObs
        and not gComparable[o.degObs.byUnit, o.pre.sActual.byUnit]) => RIncomparable else none)
  + ((not unitsOk[o.degObs.byUnit, o.target]) => RInvalidUnit else none)
  + ((liveBefore[o, o.target] and isSerialized[o.target] and some o.degObs
        and not isZero[o.degObs.byUnit]
        and not gAllOf[o.degObs.byUnit, o.pre.sActual.byUnit]) => RSerialized else none)
}
fun rePackViol[o: RePackOcc]: set Reason {
  ((not liveBefore[o, o.target]) => RNotLive else none)
  + ((isSerialized[o.target]) => RSerialized else none)
  + ((liveBefore[o, o.target] and o.pre.sFill = EMPTY) => REmpty else none)
  + ((no o.gNew and no o.dNew) => RNotApplicable else none)
  + ((liveBefore[o, o.target] and
       (let dmap = (some o.dNew => o.dNew.byUnit else o.pre.sDegraded.byUnit) |
        let gmap = (some o.gNew => o.gNew.byUnit else o.pre.sAvailableQty) |
        let amap = add[gmap, dmap] |
          not gWithin[dmap, amap] or isZero[amap] or not gNonNegative[gmap] or not gNonNegative[dmap]))
       => RIncompatible else none)
  + ((not (unitsOk[o.gNew.byUnit, o.target] and unitsOk[o.dNew.byUnit, o.target]))
       => RInvalidUnit else none)
}
fun splitViol[o: SplitOcc]: set Reason {
  ((not liveBefore[o, o.target]) => RNotLive else none)
  + ((some priorOn[o, o.nu]) => RAlreadyExists else none)                 // nu must be genuinely fresh
  + ((isSerialized[o.target] or isSerialized[o.nu]) => RSerialized else none)
  + ((no o.soGood and no o.soDeg) => RNonPositive else none)
  + (((some o.soGood and not gPositive[o.soGood.byUnit])
       or (some o.soDeg and not gPositive[o.soDeg.byUnit])) => RNonPositive else none)
  + ((liveBefore[o, o.target] and
       ((some o.soGood and gComparable[o.soGood.byUnit, o.pre.sAvailableQty]
           and not gWithin[o.soGood.byUnit, o.pre.sAvailableQty])
        or (some o.soDeg and gComparable[o.soDeg.byUnit, o.pre.sDegraded.byUnit]
           and not gWithin[o.soDeg.byUnit, o.pre.sDegraded.byUnit])))
       => ROverdraw else none)
  + ((liveBefore[o, o.target] and
       ((some o.soGood and not gComparable[o.soGood.byUnit, o.pre.sAvailableQty])
        or (some o.soDeg and not gComparable[o.soDeg.byUnit, o.pre.sDegraded.byUnit])))
       => RIncomparable else none)
  + ((not (unitsOk[o.soGood.byUnit, o.target] and unitsOk[o.soDeg.byUnit, o.target]))
       => RInvalidUnit else none)
  + ((o.nu.itemPin.subject != o.target.itemPin.subject or o.nu.tenantId != o.target.tenantId) => RIncompatible else none)
}
fun mergeViol[o: MergeOcc]: set Reason {
  ((not liveBefore[o, o.target] or not liveBefore[o, o.absorbed]) => RNotLive else none)
  + ((isSerialized[o.target] or isSerialized[o.absorbed]) => RSerialized else none)
  + ((o.target.tenantId != o.absorbed.tenantId or o.target.itemPin.subject != o.absorbed.itemPin.subject
      or (liveBefore[o, o.target] and liveBefore[o, o.absorbed]
            and o.pre.sLocator != o.absPre.sLocator)) => RIncompatible else none)
}

fun moveViol[o: MoveOcc]: set Reason {
  ((not liveBefore[o, o.target]) => RNotLive else none)
  + ((liveBefore[o, o.target] and o.pre.sAdmin = LOCKED) => RLocked else none)
}
fun lockViol[o: LockOcc]: set Reason {
  ((not liveBefore[o, o.target]) => RNotLive else none)
  + ((liveBefore[o, o.target] and o.pre.sAdmin != UNLOCKED) => RNotApplicable else none)
}
fun unlockViol[o: UnlockOcc]: set Reason {
  ((not liveBefore[o, o.target]) => RNotLive else none)
  + ((liveBefore[o, o.target] and o.pre.sAdmin != LOCKED) => RNotApplicable else none)
}
fun sealViol[o: SealOcc]: set Reason {
  ((not liveBefore[o, o.target]) => RNotLive else none)
  + ((liveBefore[o, o.target] and o.pre.sFill = EMPTY) => REmpty else none)   // nothing to seal
}
fun unsealViol[o: UnsealOcc]: set Reason {
  ((not liveBefore[o, o.target]) => RNotLive else none)
  + ((liveBefore[o, o.target] and o.pre.sFill != SEALED) => RNotApplicable else none)
}

// ── witnessing: verdicts ⟺ violation sets; Effects ⟺ the cores; per-kind record frames ───────────
fact IIAdmissionWitness {
  all o: inventory_item_types/CreateOcc         | (o.admission = Accepted iff no createViol[o])         and (o.admission in Rejected implies o.admission.because = createViol[o])
  all o: DeleteOcc         | (o.admission = Accepted iff no deleteViol[o])         and (o.admission in Rejected implies o.admission.because = deleteViol[o])
  all o: WriteOffOcc       | (o.admission = Accepted iff no writeOffViol[o])       and (o.admission in Rejected implies o.admission.because = writeOffViol[o])
  all o: ReplenishOcc      | (o.admission = Accepted iff no replenishViol[o])      and (o.admission in Rejected implies o.admission.because = replenishViol[o])
  all o: ConsumeOcc        | (o.admission = Accepted iff no consumeViol[o])        and (o.admission in Rejected implies o.admission.because = consumeViol[o])
  all o: AdjustQuantityOcc | (o.admission = Accepted iff no adjustQuantityViol[o]) and (o.admission in Rejected implies o.admission.because = adjustQuantityViol[o])
  all o: InspectOcc        | (o.admission = Accepted iff no inspectViol[o])        and (o.admission in Rejected implies o.admission.because = inspectViol[o])
  all o: RePackOcc         | (o.admission = Accepted iff no rePackViol[o])         and (o.admission in Rejected implies o.admission.because = rePackViol[o])
  all o: SplitOcc          | (o.admission = Accepted iff no splitViol[o])          and (o.admission in Rejected implies o.admission.because = splitViol[o])
  all o: MergeOcc          | (o.admission = Accepted iff no mergeViol[o])          and (o.admission in Rejected implies o.admission.because = mergeViol[o])
  all o: MoveOcc           | (o.admission = Accepted iff no moveViol[o])           and (o.admission in Rejected implies o.admission.because = moveViol[o])
  all o: LockOcc           | (o.admission = Accepted iff no lockViol[o])           and (o.admission in Rejected implies o.admission.because = lockViol[o])
  all o: UnlockOcc         | (o.admission = Accepted iff no unlockViol[o])         and (o.admission in Rejected implies o.admission.because = unlockViol[o])
  all o: SealOcc           | (o.admission = Accepted iff no sealViol[o])           and (o.admission in Rejected implies o.admission.because = sealViol[o])
  all o: UnsealOcc         | (o.admission = Accepted iff no unsealViol[o])         and (o.admission in Rejected implies o.admission.because = unsealViol[o])
}
// No result policy in v1; the ABAC/authorization commit guard is the deferred hook (DT-006 Layer 2).
fact IICommitAccepts { all o: IIOcc | some o.commit implies o.commit = Accepted }

// Record-frame helpers (the frame conjuncts relocate to records — they do not disappear).
pred samePayloadQty[b, a: InventoryItemState] {
  a.sActual = b.sActual and a.sDegraded = b.sDegraded and a.sLots = b.sLots
}
pred sameDescriptors[b, a: InventoryItemState] {
  a.sLocator = b.sLocator and a.sNotes = b.sNotes and a.sColorCode = b.sColorCode
}
pred sameAdminExp[b, a: InventoryItemState] { a.sAdmin = b.sAdmin and a.sExpiration = b.sExpiration }

fact IIEffectWitness {
  all o: inventory_item_types/CreateOcc | committed[o] implies {
    createE[o.qty.byUnit, o.exp, o.post.sActual.byUnit, o.post.sDegraded.byUnit, o.post.sLots,
            o.post.sFill, o.post.sAdmin, o.post.sExpiration]
    no o.post.sLocator and no o.post.sNotes and no o.post.sColorCode
  }
  all o: DeleteOcc + WriteOffOcc | committed[o] implies o.post = o.pre                    // tombstone
  all o: ReplenishOcc | committed[o] implies {
    replenishE[o.delta.byUnit, o.lots, o.exp,
               o.pre.sActual.byUnit, o.pre.sDegraded.byUnit, o.pre.sLots, o.pre.sExpiration,
               o.post.sActual.byUnit, o.post.sDegraded.byUnit, o.post.sLots, o.post.sFill, o.post.sExpiration]
    sameDescriptors[o.pre, o.post] and o.post.sAdmin = o.pre.sAdmin
  }
  all o: ConsumeOcc | committed[o] implies {
    consumeE[o.amount.byUnit, o.pre.sActual.byUnit, o.pre.sDegraded.byUnit, o.pre.sLots,
             o.post.sActual.byUnit, o.post.sDegraded.byUnit, o.post.sLots, o.post.sFill]
    sameDescriptors[o.pre, o.post] and sameAdminExp[o.pre, o.post]
  }
  all o: AdjustQuantityOcc | committed[o] implies {
    adjustQuantityE[o.good.byUnit, o.degObs.byUnit, (some o.degObs => 1 else 0),
                    o.pre.sDegraded.byUnit, o.pre.sLots,
                    o.post.sActual.byUnit, o.post.sDegraded.byUnit, o.post.sLots, o.post.sFill]
    sameDescriptors[o.pre, o.post] and sameAdminExp[o.pre, o.post]
  }
  all o: InspectOcc | committed[o] implies {
    inspectE[o.degObs.byUnit, o.pre.sActual.byUnit, o.pre.sLots,
             o.post.sActual.byUnit, o.post.sDegraded.byUnit, o.post.sLots, o.post.sFill, o.pre.sFill]
    sameDescriptors[o.pre, o.post] and sameAdminExp[o.pre, o.post]
  }
  all o: RePackOcc | committed[o] implies {
    rePackE[o.gNew.byUnit, o.dNew.byUnit, (some o.gNew => 1 else 0), (some o.dNew => 1 else 0),
            o.pre.sActual.byUnit, o.pre.sDegraded.byUnit, o.pre.sLots, o.pre.sFill,
            o.post.sActual.byUnit, o.post.sDegraded.byUnit, o.post.sLots, o.post.sFill]
    sameDescriptors[o.pre, o.post] and sameAdminExp[o.pre, o.post]
  }
  all o: SplitOcc | committed[o] implies {
    splitE[o.soGood.byUnit, o.soDeg.byUnit,
           o.pre.sActual.byUnit, o.pre.sDegraded.byUnit, o.pre.sLots,
           o.post.sActual.byUnit, o.post.sDegraded.byUnit, o.post.sLots, o.post.sFill,
           o.nuPost.sActual.byUnit, o.nuPost.sDegraded.byUnit, o.nuPost.sLots, o.nuPost.sFill]
    sameDescriptors[o.pre, o.post] and sameAdminExp[o.pre, o.post]
    sameDescriptors[o.pre, o.nuPost] and o.nuPost.sAdmin = o.pre.sAdmin
    o.nuPost.sExpiration = o.pre.sExpiration
  }
  all o: MoveOcc | committed[o] implies {
    o.post.sLocator = o.dest
    samePayloadQty[o.pre, o.post] and o.post.sFill = o.pre.sFill
    o.post.sNotes = o.pre.sNotes and o.post.sColorCode = o.pre.sColorCode
    sameAdminExp[o.pre, o.post]
  }
  all o: LockOcc | committed[o] implies {
    o.post.sAdmin = LOCKED
    samePayloadQty[o.pre, o.post] and o.post.sFill = o.pre.sFill
    sameDescriptors[o.pre, o.post] and o.post.sExpiration = o.pre.sExpiration
  }
  all o: UnlockOcc | committed[o] implies {
    o.post.sAdmin = UNLOCKED
    samePayloadQty[o.pre, o.post] and o.post.sFill = o.pre.sFill
    sameDescriptors[o.pre, o.post] and o.post.sExpiration = o.pre.sExpiration
  }
  all o: SealOcc | committed[o] implies {
    o.post.sFill = SEALED
    samePayloadQty[o.pre, o.post] and sameDescriptors[o.pre, o.post] and sameAdminExp[o.pre, o.post]
  }
  all o: UnsealOcc | committed[o] implies {
    o.post.sFill = OPEN
    samePayloadQty[o.pre, o.post] and sameDescriptors[o.pre, o.post] and sameAdminExp[o.pre, o.post]
  }
  all o: MergeOcc | committed[o] implies {
    mergeE[o.pre.sActual.byUnit, o.pre.sDegraded.byUnit, o.absPre.sActual.byUnit, o.absPre.sDegraded.byUnit,
           o.pre.sLots, o.absPre.sLots, o.pre.sExpiration, o.absPre.sExpiration,
           o.post.sActual.byUnit, o.post.sDegraded.byUnit, o.post.sLots, o.post.sFill, o.post.sExpiration]
    sameDescriptors[o.pre, o.post] and o.post.sAdmin = o.pre.sAdmin
  }
}

// Tight by default — relocated handle no-orphans (this module is the DAG sink over all users):
fact NoOrphanLotNumber { all x: LotNumber | x in InventoryItemState.sLots + ReplenishOcc.lots }
fact NoOrphanText      { all x: Text | x in InventoryItemState.(sNotes + sColorCode) }

// ── the projections and the OBSERVABLE BRIDGE (DT-017) ───────────────────────────────────────────
/** lastTouch — the latest committed occurrence at-or-before `t` that touches `ii`. */
fun lastTouch[ii: InventoryItem, t: Tick]: lone IIOcc {
  { o: IIOcc | committed[o] and ii in touches[o] and notAfter[o.tick, t]
      and (no b: IIOcc | committed[b] and ii in touches[b] and notAfter[b.tick, t]
             and precedes[o.tick, b.tick]) }
}

// The bridge: the types-level observables ARE the log projections. `stateAt`/`liveAt` (the read
// API in inventory_item_types.als) read these fields, so every former call site keeps its
// meaning; the contract laws become theorems about the log, discharged in tests/unit/.
fact IIObservableBridge {
  all ii: InventoryItem, t: Tick {
    ii.stateRel[t] = postFor[lastTouch[ii, t], ii]                        // LOCF of records
    (t in ii.liveTicks iff
      (let o = lastTouch[ii, t] | some o and not retiringFor[o, ii]))     // existence projection
  }
}
