module operations/demand/demand_implementation

/*
 * DEMAND — IMPLEMENTATION (DT-016/DT-017). The log machinery: spine adoption, reason-precise
 * admission guards, and per-kind effects (record frames). The demand ↔ kanban interactions are
 * CONVERGENT/OPERATION with the CALL-FIRST saga shape (see demand_contracts.als): there is NO
 * cross-log enforcement fact — the demand guards ARE the saga commit gates, reading the member
 * cycles' current states; in-flight intermediates are legal. Integration roots open this file
 * to get the REAL module.
 *
 * GUARDS READ `o.pre` (the chained record — the state the operation actually saw; refusals
 * included). Cycle-side reads at `o.tick` are STRICTLY-BEFORE state: OneOccurrencePerTick means
 * `o` itself occupies the tick.
 *
 * ResetQty's Σ effect is CONFINED (R3b): demand_reset.als (opened ONLY by its dedicated root)
 * carries the arity-4 fold; HERE the effect frames everything except sDemandQty. Roots outside
 * the dedicated one must treat a committed ResetQty's quantity as UNSPECIFIED.
 */

open operations/demand/demand_contracts
open operations/demand/demand_types as dt   // rule 10: the parameter below was resolving through a transitive open
open meta/subject_log/subject_log[dt/DemandItem, dt/DemandState] as dlog   // same params ⇒ the SAME spine instance as demand_types
open meta/subject_log/lifecycle[dt/DemandItem, dt/DemandState] as lc       // same params ⇒ the SAME shapes instance
open meta/subject_log/subject_log[dt/ProductionDelivery, dt/PDState] as pdlog  // the second subject's spine (§8.1.2)
open meta/subject_log/lifecycle[dt/ProductionDelivery, dt/PDState] as pdlc     // same params ⇒ the SAME shapes instance (cut 2)

// ── spine adoption (DT-015 Q5; the PD spine §8.1.2) ─────────────────────────────────────────────
fact DemandChaining      { dlog/chained }
fact DemandCommitAccepts { dlog/commitAlwaysAccepts }   // v1 result policy (no commit-gate refusals)
fact PDChaining          { pdlog/chained }
fact PDCommitAccepts     { pdlog/commitAlwaysAccepts }

// ── the §8.1.2 ATOMIC compositions (enforcement facts — the model's rendering of the ONE
// demand tx; see the C8 contracts note for why these are facts here and not in `guarantees`) ──
fact CreateComposesWithRecord  { createRecordsAtomically }
fact RevokeComposesWithExtract { revokeExtractsAtomically }

// ── guard-side reads ────────────────────────────────────────────────────────────────────────────
/** liveAtOccD — the demand item is STARTED, not retired (the lifecycle module's shape half) and in a LIVE status
    (the domain half) as the operation reads it (pre-record). The former started/deleted-before preds are the
    module's `lc/startedBefore` / `lc/retiredBefore` since 2026-09-09. */
pred liveAtOccD[o: dlog/SubjectOcc] { lc/liveAt[o] and dPre[o].sStatus in liveStatuses }
// (preMemberCycles / preLiveMemberRefs moved to demand_types — the contracts' commit-gate laws
// read them too.)

// ── reason-precise admission guards (Accepted ⟺ ∅; because = EXACTLY the set) ───────────────────
/** createGenesisViol — the genesis conditions shared by both create kinds. (NO uniqueness check —
    R1 amended: multiple DemandItems per (Item, Source Station) are legal; single-OPEN, if a
    deployment wants it, is CALLER policy over the `demandsFor` read.) */
fun createGenesisViol[o: lc/CreateOcc]: set Reason {
  lc/createViol[o, RDemandStarted]
  // (No item/station tenancy clause: stationRef is an ENTITY dataRef — kernel isolation makes a
  //  cross-tenant resolution UNREPRESENTABLE; the itemPin's tenancy is the DemandItemPinTenancy
  //  fact (DT-023 — same unrepresentable posture). RForeignRef remains for the RECORD-carried
  //  refs: holding, delivery.)
  // (The retirement clause moved to createViol at DT-023 cut 8 — see there.)
}
// DT-023 cut 7a: a committed genesis pins the item's CURRENT version at its tick (Q-A currency).
fact DemandItemPinCurrency {
  all o: CreateDemandOcc + CreateWithCycleOcc | committed[o] implies
    pinsCurrentItem[o.subject.itemPin, o.tick]
}
/** attachCycleViol — the SAGA COMMIT GATE for attach (C/OP call-first): the member must be an
    in-tenant, live cycle standing at REQUESTED (its Accept — the saga's first leg — already
    committed) and held by no live demand. Conservative refusal on a dangling ref. NB the held
    check excludes `o.subject`: a demand read at `o.tick` would see o's OWN commit (LOCF reads
    are inclusive) and refuse itself; OTHER demands' reads at `o.tick` are strictly-before by
    OneOccurrencePerTick. Already-a-member-of-THIS-demand is the separate pre-side check. */
fun attachCycleViol[o: dlog/SubjectOcc, m: EntityId]: set Reason {
  (let c = resolve[m] & CardCycle |
    ((some c and c.tenantId != o.subject.tenantId) => RForeignCycle else none)
    + ((no c or not liveCycleAt[c, o.tick] or statusAt[c, o.tick] != REQUESTED)
       => RCycleIneligible else none)
    + ((some c and some d2: DemandItem - o.subject | liveDemandAt[d2, o.tick] and c in attachedAt[d2, o.tick])
       => RCycleHeld else none)
    + ((m in dPre[o].sMembership) => RCycleHeld else none))
}
// DT-023 cut 8 (gate at INCEPTION, never at PROPAGATION — MP ruling 2026-08-11): the
// retirement gate binds ONLY on the DIRECT create (the caller chooses the item — F6
// card-less demand, queue-add of a new item). The WITH-CYCLE create is PROPAGATION —
// its pin is inherited from the triggering cycle, whose REQUEST was the gated
// inception — and refusing it would strand the scan workflow.
fun createViol[o: CreateDemandOcc]: set Reason {
  createGenesisViol[o]
  + ((not itemLiveAt[o.subject.itemPin.subject, o.tick]) => RRetiredRef else none)
}
fun createWithViol[o: CreateWithCycleOcc]: set Reason {
  createGenesisViol[o] + attachCycleViol[o, o.member]
}
fun addViol[o: AddCycleOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RFrozen else none)
  + attachCycleViol[o, o.member]
}
fun removeViol[o: RemoveCycleOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RFrozen else none)
  + ((o.member not in dPre[o].sMembership) => RNotAttached else none)
  + ((let c = resolve[o.member] & CardCycle |
       no c or not liveCycleAt[c, o.tick] or statusAt[c, o.tick] != REQUESTING)
     => RCycleIneligible else none)   // C/OP gate: the member's Shelve (saga's first leg) already committed
}
fun detachWithdrawnViol[o: DetachWithdrawnOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RFrozen else none)
  + ((o.member not in dPre[o].sMembership) => RNotAttached else none)
  + ((some c: resolve[o.member] & CardCycle | liveCycleAt[c, o.tick]) => RCycleLive else none)
}
fun adjustViol[o: AdjustQtyOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RFrozen else none)
}
fun resetViol[o: ResetQtyOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RFrozen else none)
}
fun releaseViol[o: ReleaseOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RBadState else none)
}
fun reopenViol[o: ReopenOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_RELEASED) => RBadState else none)
}
fun startProductionViol[o: StartProductionOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_RELEASED) => RBadState else none)
  + ((some p: resolve[o.holding] & InventoryPool | p.tenantId != o.subject.tenantId)
     => RForeignRef else none)
  + ((liveAtOccD[o] and dPre[o].sStatus = DS_RELEASED
      and some c: preMemberCycles[o] | statusAt[c, o.tick] != IN_PROCESS)
     => RCycleIneligible else none)   // C/OP gate: every live member's StartProcessing (saga's first legs) already committed
}
fun recordProductionViol[o: RecordProductionOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_IN_PROCESS) => RBadState else none)
  + ((some pd: resolve[o.delivery] & ProductionDelivery | pd.tenantId != o.subject.tenantId)
     => RForeignRef else none)   // §8.1.2: delivery now = the PD entity, not the transient pool
  // M3 (DT-020 §8.5.3 / SPEARHEAD-D1 A′-2): pool-vs-demand item agreement — the act binds the
  // delivery pool's PIN, not a caller-carried item (SPEARHEAD brief item R2). RecordProduction
  // carries no pool field of its own (compose-don't-subsume: the paired CreateDeliveryOcc
  // asserts it — the same asymmetric shape the Revoke/Extract pair already uses, neither side
  // duplicating the other's fields); this reads the pool through the §8.1.2 ATOMIC pairing
  // (`createRecordsAtomically`) — the CreateDeliveryOcc naming the SAME ProductionDelivery for
  // the SAME demand. Independent of that CreateDeliveryOcc's OWN admission (a candidate `c`
  // need not itself be committed): each half of the composite stays reason-precise on its own
  // terms, not merely inheriting the sibling's guard evaluation order.
  + ((some c: CreateDeliveryOcc, p: resolve[c.pool] & InventoryPool |
        c.subject.eId = o.delivery and c.subject.demandRef = o.subject.eId
        and p.itemPin.subject != o.subject.itemPin.subject)
     => RWrongItem else none)
}
fun extractProductionViol[o: ExtractProductionOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_IN_PROCESS) => RBadState else none)
  + ((some pd: resolve[o.delivery] & ProductionDelivery | pd.tenantId != o.subject.tenantId)
     => RForeignRef else none)
}
// ── the PD subject's guards (§8.1.2/§8.1.4) ────────────────────────────────────────────────────
// startedBeforePD retired at cut 2: the family's `pdlc/startedBefore` is the same reading, declared once.
/** createDeliveryViol — the §8.1.4 target gates. The demandRef is an ENTITY dataRef: kernel
    isolation makes a cross-tenant resolution UNREPRESENTABLE (the entity-lift precedent), so
    there is no tenancy clause; a DANGLING or non-IN_PROCESS target refuses conservatively via
    the status read. Both clauses may fire together (reason-precise = the SET). */
fun createDeliveryViol[o: CreateDeliveryOcc]: set Reason {
  pdlc/createViol[o, RDeliveryStarted]                       // genesis-once — the family's arm (cut 2)
  + ((demandStatusAt[resolve[o.subject.demandRef] & DemandItem, o.tick] != DS_IN_PROCESS)
     => RTargetNotInProcess else none)
  // M3 (DT-020 §8.5.3 / SPEARHEAD-D1 A′-2): re-based from a caller-asserted item to the
  // DELIVERY POOL's pin — §8.1.4 item agreement, the pool module's reason REUSED. Silent
  // (no violation) when `o.pool` doesn't resolve to an InventoryPool — a dangling/unset pool
  // ref is not this guard's concern (mirrors the RForeignRef pattern elsewhere in this file).
  + ((some p: resolve[o.pool] & InventoryPool | p.itemPin.subject != (resolve[o.subject.demandRef] & DemandItem).itemPin.subject)
     => RWrongItem else none)
}
/** revokeDeliveryViol — §8.1.1: subject live + DI live. The content clause (holding content ≥
    contributed) is RUNTIME enforcement + probe — the standing I3 arity-4 exclusion; the
    caller's own source-state check (RL allows) is the CALLER's leg, ordinary call-first. */
fun revokeDeliveryViol[o: RevokeDeliveryOcc]: set Reason {
  pdlc/liveViol[o, RDeliveryClosed]                          // never created / already RETIRED — the family's arm (cut 2)
  + ((pdlc/liveAt[o] and pdPre[o].sStatus = PD_REVOKED) => RDeliveryClosed else none)   // already revoked — the domain's arm, same atom
  + ((let d = resolve[o.subject.demandRef] & DemandItem | no d or not liveDemandAt[d, o.tick])
     => RDemandClosed else none)
}
/** retireDeliveryViol — cut 2 (Q24 (a)): the family's arm (never created / already retired → RDeliveryClosed) + the
    domain's terminality arm: a delivery still CREATED is not terminal — Revoke first (RNotTerminal, the demand's atom). */
fun retireDeliveryViol[o: RetireDeliveryOcc]: set Reason {
  pdlc/retireViol[o, RDeliveryClosed]
  + ((pdlc/liveAt[o] and pdPre[o].sStatus = PD_CREATED) => RNotTerminal else none)
}
fun distributeViol[o: DistributeOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_IN_PROCESS) => RBadState else none)
  + ((liveAtOccD[o] and (o.allocation.Quantity + o.fills) not in preLiveMemberRefs[o])
     => RBadAllocation else none)     // retired members receive NOTHING (R7/R8)
  + ((liveAtOccD[o] and some m: o.fills | some c: resolve[m] & CardCycle | statusAt[c, o.tick] != READY)
     => RCycleIneligible else none)   // C/OP gate: each fill's CompleteProcessing (saga's first leg) already committed
}
fun completeViol[o: CompleteOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_IN_PROCESS) => RBadState else none)
  + ((liveAtOccD[o] and some heldAt[resolve[dPre[o].sHolding] & InventoryPool, o.tick])
     => RUndistributed else none)
  + ((liveAtOccD[o] and some c: preMemberCycles[o] | statusAt[c, o.tick] = IN_PROCESS)
     => RCycleIneligible else none)   // C/OP gate: every member SETTLED first (READY or back to REQUESTING)
}
fun cancelViol[o: CancelOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RBadState else none)
  + ((liveAtOccD[o] and dPre[o].sStatus = DS_OPEN and some dPre[o].sMembership) => RHasCards else none)
}
fun deleteViol[o: DeleteDemandOcc]: set Reason {
  lc/retireViol[o, RDemandClosed]                                                      // not started, or already retired
  + ((lc/startedBefore[o] and dPre[o].sStatus in liveStatuses) => RNotTerminal else none)   // delete requires a TERMINAL demand
}
/** demandDomainViol — the witness BY SHAPE (the lifecycle idiom): one dispatch over the Mutate kinds; each kind's
    own violation set (its liveness arm included) is unchanged. */
fun demandDomainViol[o: lc/MutateOcc]: set Reason {
  (o in AddCycleOcc => addViol[o] else none) + (o in RemoveCycleOcc => removeViol[o] else none)
  + (o in DetachWithdrawnOcc => detachWithdrawnViol[o] else none) + (o in AdjustQtyOcc => adjustViol[o] else none)
  + (o in ResetQtyOcc => resetViol[o] else none) + (o in ReleaseOcc => releaseViol[o] else none)
  + (o in ReopenOcc => reopenViol[o] else none) + (o in StartProductionOcc => startProductionViol[o] else none)
  + (o in RecordProductionOcc => recordProductionViol[o] else none) + (o in ExtractProductionOcc => extractProductionViol[o] else none)
  + (o in DistributeOcc => distributeViol[o] else none) + (o in CompleteOcc => completeViol[o] else none)
  + (o in CancelOcc => cancelViol[o] else none)
}

fact DemandAdmissionWitness {
  // the demand log, BY SHAPE (DT-030, 2026-09-09): one witness per shape; the kinds' violation sets are unchanged
  all o: lc/CreateOcc | let v = (o in CreateDemandOcc => createViol[o] else createWithViol[o]) |
    (o.admission = Accepted iff no v) and (o.admission in Rejected implies o.admission.because = v)
  all o: lc/MutateOcc | let v = demandDomainViol[o] |
    (o.admission = Accepted iff no v) and (o.admission in Rejected implies o.admission.because = v)
  all o: lc/RetireOcc | let v = deleteViol[o] |
    (o.admission = Accepted iff no v) and (o.admission in Rejected implies o.admission.because = v)
  // the delivery log, per kind (a lifecycle adopter since cut 2: pdlc)
  all o: CreateDeliveryOcc   | (o.admission = Accepted iff no createDeliveryViol[o])   and (o.admission in Rejected implies o.admission.because = createDeliveryViol[o])
  all o: RevokeDeliveryOcc   | (o.admission = Accepted iff no revokeDeliveryViol[o])   and (o.admission in Rejected implies o.admission.because = revokeDeliveryViol[o])
  all o: RetireDeliveryOcc   | (o.admission = Accepted iff no retireDeliveryViol[o])   and (o.admission in Rejected implies o.admission.because = retireDeliveryViol[o])
  all o: CompleteOcc         | (o.admission = Accepted iff no completeViol[o])         and (o.admission in Rejected implies o.admission.because = completeViol[o])
  all o: CancelOcc           | (o.admission = Accepted iff no cancelViol[o])           and (o.admission in Rejected implies o.admission.because = cancelViol[o])
  all o: DeleteDemandOcc     | (o.admission = Accepted iff no deleteViol[o])           and (o.admission in Rejected implies o.admission.because = deleteViol[o])
}

// ── effects (committed) — per-kind frames on the record ────────────────────────────────────────
/** sameDemandButStatus — everything except the status is carried over. */
pred sameDemandButStatus[b, a: DemandState] {
  a.sDemandQty = b.sDemandQty and a.sMembership = b.sMembership and a.sHolding = b.sHolding
}
/** sameHolding — the holding ref is carried over (item/station live on the ENTITY now). */
pred sameHolding[b, a: DemandState] { a.sHolding = b.sHolding }

fact DemandEffectWitness {
  all o: CreateDemandOcc | committed[o] implies {
    dPost[o].sStatus = DS_OPEN
    dPost[o].sDemandQty = o.qty                       // seeds the advisory intent (R3b)
    no dPost[o].sMembership
    no dPost[o].sHolding
  }
  all o: CreateWithCycleOcc | committed[o] implies {
    dPost[o].sStatus = DS_OPEN
    qtyMap[dPost[o].sDemandQty] = add[qtyMap[o.qty], effectiveQtyMap[resolve[o.member] & CardCycle]]
    dPost[o].sMembership = o.member
    no dPost[o].sHolding
  }
  all o: AddCycleOcc | committed[o] implies {
    dPost[o].sStatus = dPre[o].sStatus
    qtyMap[dPost[o].sDemandQty] = add[qtyMap[dPre[o].sDemandQty], effectiveQtyMap[resolve[o.member] & CardCycle]]
    dPost[o].sMembership = dPre[o].sMembership + o.member
    sameHolding[dPre[o], dPost[o]]
  }
  all o: RemoveCycleOcc + DetachWithdrawnOcc | committed[o] implies {
    dPost[o].sStatus = dPre[o].sStatus
    qtyMap[dPost[o].sDemandQty] = add[qtyMap[dPre[o].sDemandQty], negate[effectiveQtyMap[resolve[o.member] & CardCycle]]]
    dPost[o].sMembership = dPre[o].sMembership - o.member
    sameHolding[dPre[o], dPost[o]]
  }
  all o: AdjustQtyOcc | committed[o] implies {
    dPost[o].sStatus = dPre[o].sStatus
    dPost[o].sDemandQty = o.qty                       // SET (R3b; delta-adjust is client sugar)
    dPost[o].sMembership = dPre[o].sMembership
    sameHolding[dPre[o], dPost[o]]
  }
  all o: ResetQtyOcc | committed[o] implies {       // Σ semantics CONFINED to demand_reset.als
    dPost[o].sStatus = dPre[o].sStatus
    dPost[o].sMembership = dPre[o].sMembership
    sameHolding[dPre[o], dPost[o]]
  }
  all o: ReleaseOcc | committed[o] implies
    { dPost[o].sStatus = DS_RELEASED and sameDemandButStatus[dPre[o], dPost[o]] }
  all o: ReopenOcc | committed[o] implies
    { dPost[o].sStatus = DS_OPEN and sameDemandButStatus[dPre[o], dPost[o]] }
  all o: StartProductionOcc | committed[o] implies {
    dPost[o].sStatus = DS_IN_PROCESS
    dPost[o].sHolding = o.holding                     // the accumulation pool attaches (R8);
                                                       //   itemPin agreement: StartProductionHoldingPoolPin below
    dPost[o].sDemandQty = dPre[o].sDemandQty
    dPost[o].sMembership = dPre[o].sMembership
  }
  all o: RecordProductionOcc | committed[o] implies o.post = o.pre   // ⟲ — the contribution is the PD row (§8.1.2); pool merges are runtime
  all o: ExtractProductionOcc | committed[o] implies o.post = o.pre  // ⟲ — the reversal is the PD's REVOKED row; pool movement is runtime
  all o: DistributeOcc       | committed[o] implies o.post = o.pre   // ⟲ — allocation moves pools + cycles, not this record
  all o: CreateDeliveryOcc   | committed[o] implies pdPost[o].sStatus = PD_CREATED
  all o: RevokeDeliveryOcc   | committed[o] implies pdPost[o].sStatus = PD_REVOKED
  // RetireDeliveryOcc: the tombstone is the family's `pdlc/RetireEffect` (post = pre) — no effect line here (cut 2)
  all o: CompleteOcc | committed[o] implies
    { dPost[o].sStatus = DS_COMPLETE and sameDemandButStatus[dPre[o], dPost[o]] }
  all o: CancelOcc | committed[o] implies
    { dPost[o].sStatus = DS_CANCELED and sameDemandButStatus[dPre[o], dPost[o]] }
  // (DeleteDemandOcc's tombstone: the lifecycle module's `RetireEffect`, since 2026-09-09)
}

/** StartProductionHoldingPoolPin — M3.2 (DT-020 §8.5.3 / SPEARHEAD-D1 A′-2): the MINTED
    holding pool carries the demand's item pin (already how PDEV-1528 built it at runtime).
    Genesis is runtime-side (no create kind for pools), so this is stated wherever the model
    CAN name the minted pool (`resolve[o.holding] & InventoryPool`) — an annotation on the
    resolved pool, not a create-kind effect; vacuously true when `o.holding` doesn't resolve. */
fact StartProductionHoldingPoolPin {
  all o: StartProductionOcc | committed[o] implies
    (all p: resolve[o.holding] & InventoryPool | p.itemPin.subject = o.subject.itemPin.subject)
}

// (NO cross-log enforcement facts — C/OP, 2026-07-06: the guards above ARE the saga commit
// gates; the commit-gate contract laws are THEOREMS of them, and the quiescence law
// `demandCyclesAlignedAt` is witnessed on settled traces, never asserted globally.)
