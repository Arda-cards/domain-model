module receiving/receiver/receiver_implementation

/*
 * RECEIVER — IMPLEMENTATION (DT-020/DT-017). The log machinery: spine adoption (three
 * subjects), reason-precise admission guards, per-kind effects (record frames), and the
 * SAME-MODULE PAIRING FACTS — the model's rendering of the ONE receiving-module tx for the
 * three atomic compositions (§8.3.1/§8.3.3): line-attach + attribution genesis; line-detach
 * + attribution tombstone; the Receive `sActual` fan-out. The pairing facts are enforcement
 * facts here and deliberately NOT in `guarantees` (the CreateComposesWithRecord precedent).
 *
 * GUARDS READ `o.pre` (the chained record — the state the operation actually saw; refusals
 * included). Cross-subject and cross-module reads at `o.tick` are STRICTLY-BEFORE state:
 * OneOccurrencePerTick means `o` itself occupies the tick.
 *
 * THE Σ-INVARIANT GUARDS (§8.3.3 d) are CASE-WISE — exact at 0/1 pre-existing members
 * (attach) and 0/1/2 allocation keys (Receive); ≥ the ceiling the clause does not fire.
 * This is the order_received solver-budget confinement applied GUARD-SIDE: the general
 * keyed fold is the standing arity-4 exclusion, the runtime computes the real Σ without
 * ceilings, and every suite scope stays within the exact cases BY DESIGN.
 *
 * CROSS-MODULE (C/OP call-first — no enforcement facts, the guards ARE the gates): the
 * Receive commit gates on the caller's resources-side legs (items born located, the pool
 * minted + loaded); RecordDelivery closes the distribute saga after the caller's demand-side
 * PD.Create. The pool AVAILABILITY clause in the Receive guard is receiving's per-entity-type
 * exclusivity semantics (§8.5.3): it refuses a pool visibly in use by any holder RECEIVING
 * CAN SEE (its own lines, live cycles, live demand holdings — all DAG-legal reads); the
 * cross-kind protection against LATER lower-layer attaches is the genesis premise's job
 * (see receiver_contracts.als C9).
 */

open receiving/receiver/receiver_contracts
open receiving/receiver/receiver_types as rt   // rule 10: the parameter below was resolving through a transitive open
open meta/subject_log/subject_log[rt/Receiver, rt/ReceiverState] as rvlog           // same params ⇒ the SAME spine instances
open meta/subject_log/subject_log[rt/ReceivingLine, rt/ReceivingLineState] as rllog //   as receiver_types
open meta/subject_log/subject_log[rt/OrderAttribution, rt/AttributionState] as oalog

// ── spine adoption (DT-015 Q5; three subjects) ─────────────────────────────────────────────────
fact ReceiverChaining       { rvlog/chained }
fact ReceiverCommitAccepts  { rvlog/commitAlwaysAccepts }   // v1 result policy (no commit-gate refusals)
fact RcvLineChaining        { rllog/chained }
fact RcvLineCommitAccepts   { rllog/commitAlwaysAccepts }
fact AttributionChaining    { oalog/chained }
fact AttributionCommitAccepts { oalog/commitAlwaysAccepts }

// ── the same-module ATOMIC compositions (enforcement facts — NOT in `guarantees`; see the
// contracts header for why) ─────────────────────────────────────────────────────────────────────
/** An attribution's genesis commits iff exactly one line-side CARRIER commits naming it —
    the order-connected line birth (AddReceivingLine's attribution arm) or the standalone
    pre-RECEIVED attach (AppendAttribution). Ownership by genesis: the attribution is born
    in the line's own act, so it lands in exactly one membership. */
fact AttachComposesWithAppend {
  all g: AttachAttributionOcc | committed[g] implies
    one ({ c: AddReceivingLineOcc | committed[c] and c.attribution = g.subject.eId }
         + { c: AppendAttributionOcc | committed[c] and c.attribution = g.subject.eId })
  all c: AppendAttributionOcc | committed[c] implies
    (one g: AttachAttributionOcc | committed[g] and g.subject.eId = c.attribution)
  all c: AddReceivingLineOcc | (committed[c] and some c.attribution) implies
    (one g: AttachAttributionOcc | committed[g] and g.subject.eId = c.attribution)
}
/** A detach tombstone commits iff exactly one line-side Remove commits naming it (the
    §8.3.3 pre-RECEIVED detach; the membership-freeze timing rides the LINE guard — the
    attribution subject stays line-ignorant). */
fact DetachComposesWithRemove {
  all g: DetachAttributionOcc | committed[g] implies
    (one c: RemoveAttributionOcc | committed[c] and c.attribution = g.subject.eId)
  all c: RemoveAttributionOcc | committed[c] implies
    (one g: DetachAttributionOcc | committed[g] and g.subject.eId = c.attribution)
}
/** The Receive `sActual` fan-out (§8.3.3 c): one committed RecordActual per allocation
    entry, carrying the allocated quantity — and every committed RecordActual comes from
    exactly one Receive's allocation (never a standalone act). ONE atomic receiving commit
    across the line log and the attribution logs, rendered both-or-neither. */
fact ReceiveFansOutActuals {
  all r: ReceiveLineOcc | committed[r] implies
    (all k: r.allocation.Quantity |
      (one x: RecordActualOcc | committed[x] and x.subject.eId = k and x.actual = k.(r.allocation)))
  all x: RecordActualOcc | committed[x] implies
    (one r: ReceiveLineOcc | committed[r]
       and x.subject.eId in r.allocation.Quantity and x.actual = (x.subject.eId).(r.allocation))
}

// ── guard-side reads ────────────────────────────────────────────────────────────────────────────
/** startedBeforeRV / startedBeforeRL / startedBeforeOA — the subject has committed history
    strictly before `o` (genesis-once, per subject). */
pred startedBeforeRV[o: rvlog/SubjectOcc] {
  some b: rvlog/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
pred startedBeforeRL[o: rllog/SubjectOcc] {
  some b: rllog/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
pred startedBeforeOA[o: oalog/SubjectOcc] {
  some b: oalog/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
/** detachedBeforeOA — a committed Detach tombstone exists strictly before `o`. */
pred detachedBeforeOA[o: oalog/SubjectOcc] {
  some b: DetachAttributionOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
/** carrierTenancyViol — DT-023 cut 7b (the dissolved-handle form): the carrier PIN must be
    in-tenant (record-carried — tenancy is guard-side; role/type agreement is definitional,
    ReceiverCarrierPinAgrees). Deliberately NO RRetiredRef — the carrier is CAPTURE (who
    physically delivered), the D3 Receiver.sCarrier KEEP row. */
fun carrierTenancyViol[o: ReceiverHeaderOcc]: set Reason {
  ((some o.carrierPin and o.carrierPin.subject.tenantId != o.subject.tenantId)
   => RForeignRef else none)
}
/** attachSumViol — the §8.3.3(d) Σ-expected clause, CASE-WISE (exact at 0/1 pre-existing
    resolved members; ≥2 is the documented ceiling — suite scopes stay within it BY DESIGN):
    with the cap (`sExpectedQty`) present, the would-be membership's Σ expected must stay
    ≤ the cap. Absent cap (a blind line gaining its first linkage) — no bound (§8.3: the
    invariant binds the ORDER's position; there is none to bind). */
fun attachSumViol[o: rllog/SubjectOcc, m: EntityId, cap: Quantity]: set Reason {
  (let a = resolve[m] & OrderAttribution,
       ex = { x: OrderAttribution | some r: rlPre[o].sAttributions | resolve[r] = x } | (
    ((some cap and some a and no ex
       and not lte[qtyMap[a.expected], qtyMap[cap]]) => ROverAttributed else none)
    + ((some cap and some a and one ex
       and not lte[add[qtyMap[a.expected], qtyMap[ex.expected]], qtyMap[cap]]) => ROverAttributed else none)))
}
/** receiveSumViol — the §8.3.3(d) Σ-actual clause, CASE-WISE over the allocation keys
    (exact at 0/1/2; same ceiling note): Σ allocation ≤ the accepted count (≤, not = —
    the blind remainder attributes to nothing). */
fun receiveSumViol[o: ReceiveLineOcc]: set Reason {
  (let ks = o.allocation.Quantity | (
    ((#ks = 1 and (some k: ks | not lte[qtyMap[k.(o.allocation)], qtyMap[o.receivedQty]]))
      => ROverAllocated else none)
    + ((#ks = 2 and (some disj k1, k2: ks |
         not lte[add[qtyMap[k1.(o.allocation)], qtyMap[k2.(o.allocation)]], qtyMap[o.receivedQty]]))
      => ROverAllocated else none)))
}

// ── reason-precise admission guards (Accepted ⟺ ∅; because = EXACTLY the set) ───────────────────
// RECEIVER subject:
fun createReceiverViol[o: CreateReceiverOcc]: set Reason {
  (startedBeforeRV[o] => RReceiverStarted else none)
  + carrierTenancyViol[o]
}
fun updateReceiverViol[o: UpdateReceiverOcc]: set Reason {
  ((no o.pre) => RReceiverClosed else none)
  + ((some o.pre and rvPre[o].sStatus != RV_EDITING) => RFrozen else none)
  + carrierTenancyViol[o]
}
fun annotateReceiverViol[o: AnnotateReceiverOcc]: set Reason {
  ((no o.pre) => RReceiverClosed else none)   // any state incl. RV_COMPLETE (TQ-7(c)); the subject must exist
}
fun completeReceiverViol[o: CompleteReceiverOcc]: set Reason {
  ((no o.pre) => RReceiverClosed else none)
  + ((some o.pre and rvPre[o].sStatus != RV_EDITING) => RBadState else none)
  + ((some o.pre and rvPre[o].sStatus = RV_EDITING
      and some l: linesOfReceiver[o.subject] | rlStatusAt[l, o.tick] = RL_RECEIVING)
     => RLinesReceiving else none)
}
// LINE subject:
fun addLineViol[o: AddReceivingLineOcc]: set Reason {
  (startedBeforeRL[o] => RLineStarted else none)
  + ((no receiverStatusAt[parentReceiverOf[o.subject], o.tick]) => RReceiverClosed else none)
  + ((receiverStatusAt[parentReceiverOf[o.subject], o.tick] = RV_COMPLETE) => RFrozen else none)
  + ((some a: resolve[o.attribution] & OrderAttribution | a.tenantId != o.subject.tenantId)
     => RForeignRef else none)
  + ((some o.item and o.item.subject.tenantId != o.subject.tenantId)
     => RForeignRef else none)   // DT-023: the pin's tenancy (record-carried — guard-side)
  + ((no o.attribution and some o.item and not itemLiveAt[o.item.subject, o.tick])
     => RRetiredRef else none)   // D3 blind-receiving refinement: a BLIND line IS the
                                 // acceptance decision — only currently defined items
                                 // may be received without an order behind them
  + attachSumViol[o, o.attribution, o.expectedQty]   // the newborn's cap is the payload's
}
fun updateLineViol[o: UpdateReceivingLineOcc]: set Reason {
  ((no o.pre) => RLineClosed else none)
  + ((some o.pre and rlPre[o].sStatus != RL_RECEIVING) => RFrozen else none)
  + ((some o.item and o.item.subject.tenantId != o.subject.tenantId)
     => RForeignRef else none)   // DT-023: the pin's tenancy
  + ((some o.pre and no rlPre[o].sAttributions
      and some o.item and not itemLiveAt[o.item.subject, o.tick])
     => RRetiredRef else none)   // D3 blind-receiving refinement: re-pin on a line with
                                 // no attributions is a blind acceptance — gated
}
// DT-023 cut 7a: capture-window writes RE-PIN the item's CURRENT version (the Q-A floating
// semantics — sExpectedItem floats until the Receive freeze). The RRetiredRef gate follows
// the COMMITMENT DECISION (D3 blind-receiving refinement, MP 2026-08-10): ORDER-CONNECTED
// add/re-pin stays UNGATED — capture riding the order's already-gated commitment (the D3
// grandfather rows: ordered goods arrive regardless); BLIND add/re-pin refuses a retired
// item with RRetiredRef (there is no upstream gate — the blind write is the commitment).
fact LineExpectedItemPinCurrency {
  all o: AddReceivingLineOcc    | (committed[o] and some o.item) implies pinsCurrentItem[o.item, o.tick]
  all o: UpdateReceivingLineOcc | (committed[o] and some o.item) implies pinsCurrentItem[o.item, o.tick]
}
// DT-023 cut 7b: a committed header write's carrier pin is THEN-CURRENT (capture re-pins
// current; the COMPLETE freeze then freezes the pin with the other captured facts).
fact CarrierPinCurrency {
  all o: ReceiverHeaderOcc | (committed[o] and some o.carrierPin) implies
    pinsCurrentBa[o.carrierPin, o.tick]
}
fun appendAttributionViol[o: AppendAttributionOcc]: set Reason {
  ((no o.pre) => RLineClosed else none)
  + ((some o.pre and rlPre[o].sStatus != RL_RECEIVING) => RFrozen else none)
  + ((o.attribution in rlPre[o].sAttributions) => RAlreadyMember else none)
  + ((some a: resolve[o.attribution] & OrderAttribution | a.tenantId != o.subject.tenantId)
     => RForeignRef else none)
  + attachSumViol[o, o.attribution, rlPre[o].sExpectedQty]
}
fun removeAttributionViol[o: RemoveAttributionOcc]: set Reason {
  ((no o.pre) => RLineClosed else none)
  + ((some o.pre and rlPre[o].sStatus != RL_RECEIVING) => RFrozen else none)
  + ((some o.pre and o.attribution not in rlPre[o].sAttributions) => RNotAttached else none)
}
fun receiveViol[o: ReceiveLineOcc]: set Reason {
  ((no o.pre) => RLineClosed else none)
  + ((some o.pre and rlPre[o].sStatus != RL_RECEIVING) => RBadState else none)
  + ((some o.birthPins and no rlPre[o].sExpectedItem) => RNoItem else none)
  + ((some p: resolve[o.pool] & InventoryPool | p.tenantId != o.subject.tenantId)
     => RForeignPool else none)
  + ((some o.pool and some rlPre[o].sExpectedItem
      and (resolve[o.pool] & InventoryPool).itemPin.subject != rlPre[o].sExpectedItem.subject)
     => RWrongItem else none)   // a DANGLING pool refuses conservatively through this same
                                //   clause (an empty resolution can never agree — the
                                //   attachCycleViol dangling-ref precedent)
  + ((some p: resolve[o.pool] & InventoryPool | (
        (some l2: ReceivingLine - o.subject | resolve[rlStateAt[l2, o.tick].sPool] = p)
        or (some c: CardCycle | liveCycleAt[c, o.tick] and resolve[stateOfCycleAt[c, o.tick].sPool] = p)
        or (some d: DemandItem | liveDemandAt[d, o.tick] and resolve[demandStateAt[d, o.tick].sHolding] = p)))
     => RPoolInUse else none)   // receiving's per-entity-type availability semantics (§8.5.3)
  + ((some (o.allocation.Quantity - rlPre[o].sAttributions)) => RBadAllocation else none)
  + receiveSumViol[o]
}
fun recordDeliveryViol[o: RecordDeliveryOcc]: set Reason {
  ((no o.pre) => RLineClosed else none)
  + ((some o.pre and rlPre[o].sStatus != RL_RECEIVED) => RBadState else none)
  + ((some pd: resolve[o.delivery] & ProductionDelivery | pd.tenantId != o.subject.tenantId)
     => RForeignRef else none)
}
fun releaseLineViol[o: ReleaseLineOcc]: set Reason {
  ((no o.pre) => RLineClosed else none)
  + ((some o.pre and rlPre[o].sStatus != RL_RECEIVED) => RBadState else none)
}
// ATTRIBUTION subject:
fun attachAttributionViol[o: AttachAttributionOcc]: set Reason {
  (startedBeforeOA[o] => RAttributionStarted else none)
}
fun recordActualViol[o: RecordActualOcc]: set Reason {
  ((no o.pre or detachedBeforeOA[o]) => RAttributionClosed else none)
  + ((some oaPre[o].sActual) => RActualRecorded else none)
}
fun detachAttributionViol[o: DetachAttributionOcc]: set Reason {
  ((no o.pre or detachedBeforeOA[o]) => RAttributionClosed else none)
}

fact ReceivingAdmissionWitness {
  all o: CreateReceiverOcc     | (o.admission = Accepted iff no createReceiverViol[o])     and (o.admission in Rejected implies o.admission.because = createReceiverViol[o])
  all o: UpdateReceiverOcc     | (o.admission = Accepted iff no updateReceiverViol[o])     and (o.admission in Rejected implies o.admission.because = updateReceiverViol[o])
  all o: AnnotateReceiverOcc   | (o.admission = Accepted iff no annotateReceiverViol[o])   and (o.admission in Rejected implies o.admission.because = annotateReceiverViol[o])
  all o: CompleteReceiverOcc   | (o.admission = Accepted iff no completeReceiverViol[o])   and (o.admission in Rejected implies o.admission.because = completeReceiverViol[o])
  all o: AddReceivingLineOcc   | (o.admission = Accepted iff no addLineViol[o])            and (o.admission in Rejected implies o.admission.because = addLineViol[o])
  all o: UpdateReceivingLineOcc | (o.admission = Accepted iff no updateLineViol[o])        and (o.admission in Rejected implies o.admission.because = updateLineViol[o])
  all o: AppendAttributionOcc  | (o.admission = Accepted iff no appendAttributionViol[o])  and (o.admission in Rejected implies o.admission.because = appendAttributionViol[o])
  all o: RemoveAttributionOcc  | (o.admission = Accepted iff no removeAttributionViol[o])  and (o.admission in Rejected implies o.admission.because = removeAttributionViol[o])
  all o: ReceiveLineOcc            | (o.admission = Accepted iff no receiveViol[o])            and (o.admission in Rejected implies o.admission.because = receiveViol[o])
  all o: RecordDeliveryOcc     | (o.admission = Accepted iff no recordDeliveryViol[o])     and (o.admission in Rejected implies o.admission.because = recordDeliveryViol[o])
  all o: ReleaseLineOcc        | (o.admission = Accepted iff no releaseLineViol[o])        and (o.admission in Rejected implies o.admission.because = releaseLineViol[o])
  all o: AttachAttributionOcc  | (o.admission = Accepted iff no attachAttributionViol[o])  and (o.admission in Rejected implies o.admission.because = attachAttributionViol[o])
  all o: RecordActualOcc       | (o.admission = Accepted iff no recordActualViol[o])       and (o.admission in Rejected implies o.admission.because = recordActualViol[o])
  all o: DetachAttributionOcc  | (o.admission = Accepted iff no detachAttributionViol[o])  and (o.admission in Rejected implies o.admission.because = detachAttributionViol[o])
}

// ── effects (committed) — per-kind frames on the record ────────────────────────────────────────
/** sameLineCapture — the captured-facts cluster is carried over. */
pred sameLineCapture[b, a: ReceivingLineState] {
  a.sExpectedItem = b.sExpectedItem and a.sExpectedQty = b.sExpectedQty
  and a.sStatedQty = b.sStatedQty and a.sReceivedQty = b.sReceivedQty
  and a.sRejectedQty = b.sRejectedQty and a.sOffManifest = b.sOffManifest
  and a.sRejectionReason = b.sRejectionReason and a.sNote = b.sNote
  and a.sBirthPins = b.sBirthPins
}
/** sameLineOperational — pool + deliveries + attributions carried over. */
pred sameLineOperational[b, a: ReceivingLineState] {
  a.sPool = b.sPool and a.sDeliveries = b.sDeliveries and a.sAttributions = b.sAttributions
}

fact ReceivingEffectWitness {
  // RECEIVER subject:
  all o: CreateReceiverOcc | committed[o] implies {
    rvPost[o].sStatus = RV_EDITING
    rvPost[o].sBillOfLading = o.bol           // SET semantics — the payload IS the header
    rvPost[o].sCarrierPin  = o.carrierPin
    rvPost[o].sCarrierRole = o.carrierRole
    rvPost[o].sOperator = o.operator
    no rvPost[o].sInternalNotes               // notes start empty (AnnotateReceiver adds them)
  }
  all o: UpdateReceiverOcc | committed[o] implies {
    rvPost[o].sStatus = RV_EDITING            // Update stays inside the window (guard)
    rvPost[o].sBillOfLading = o.bol           // SET semantics — the payload IS the header
    rvPost[o].sCarrierPin  = o.carrierPin
    rvPost[o].sCarrierRole = o.carrierRole
    rvPost[o].sOperator = o.operator
    rvPost[o].sInternalNotes = rvPre[o].sInternalNotes   // NOT this kind's facet
  }
  all o: AnnotateReceiverOcc | committed[o] implies {     // SET the internal notes (any state — TQ-7(c))
    rvPost[o].sInternalNotes = o.notes
    rvPost[o].sStatus = rvPre[o].sStatus
    rvPost[o].sBillOfLading = rvPre[o].sBillOfLading
    rvPost[o].sCarrierPin  = rvPre[o].sCarrierPin
    rvPost[o].sCarrierRole = rvPre[o].sCarrierRole
    rvPost[o].sOperator = rvPre[o].sOperator
  }
  all o: CompleteReceiverOcc | committed[o] implies {
    rvPost[o].sStatus = RV_COMPLETE
    rvPost[o].sBillOfLading = rvPre[o].sBillOfLading
    rvPost[o].sCarrierPin  = rvPre[o].sCarrierPin
    rvPost[o].sCarrierRole = rvPre[o].sCarrierRole
    rvPost[o].sOperator = rvPre[o].sOperator
    rvPost[o].sInternalNotes = rvPre[o].sInternalNotes
  }
  // LINE subject:
  all o: AddReceivingLineOcc | committed[o] implies {
    rlPost[o].sStatus = RL_RECEIVING
    rlPost[o].sExpectedItem = o.item
    rlPost[o].sExpectedQty = o.expectedQty
    no rlPost[o].sStatedQty and no rlPost[o].sReceivedQty and no rlPost[o].sRejectedQty
    no rlPost[o].sOffManifest and no rlPost[o].sRejectionReason and no rlPost[o].sNote
    no rlPost[o].sBirthPins and no rlPost[o].sPool
    no rlPost[o].sDeliveries
    rlPost[o].sAttributions = o.attribution   // born WITH its attribution when order-connected (§8.3.1)
  }
  all o: UpdateReceivingLineOcc | committed[o] implies {
    rlPost[o].sStatus = rlPre[o].sStatus
    rlPost[o].sExpectedItem = o.item          // SET — the payload IS the expectation/evidence cluster
    rlPost[o].sExpectedQty = o.expectedQty
    rlPost[o].sStatedQty = o.statedQty
    rlPost[o].sReceivedQty = o.receivedQty    // the capture-window running count (authoritative at Receive)
    rlPost[o].sOffManifest = o.offManifest
    rlPost[o].sRejectedQty = rlPre[o].sRejectedQty
    rlPost[o].sRejectionReason = rlPre[o].sRejectionReason   // land AT Receive (TQ-2), not here
    rlPost[o].sNote = rlPre[o].sNote
    rlPost[o].sBirthPins = rlPre[o].sBirthPins
    sameLineOperational[rlPre[o], rlPost[o]]
  }
  all o: AppendAttributionOcc | committed[o] implies {
    rlPost[o].sStatus = rlPre[o].sStatus
    sameLineCapture[rlPre[o], rlPost[o]]
    rlPost[o].sPool = rlPre[o].sPool and rlPost[o].sDeliveries = rlPre[o].sDeliveries
    rlPost[o].sAttributions = rlPre[o].sAttributions + o.attribution
  }
  all o: RemoveAttributionOcc | committed[o] implies {
    rlPost[o].sStatus = rlPre[o].sStatus
    sameLineCapture[rlPre[o], rlPost[o]]
    rlPost[o].sPool = rlPre[o].sPool and rlPost[o].sDeliveries = rlPre[o].sDeliveries
    rlPost[o].sAttributions = rlPre[o].sAttributions - o.attribution
  }
  all o: ReceiveLineOcc | committed[o] implies {
    rlPost[o].sStatus = RL_RECEIVED           // THE FREEZE (§8.4.1)
    rlPost[o].sExpectedItem = rlPre[o].sExpectedItem
    rlPost[o].sExpectedQty = rlPre[o].sExpectedQty
    rlPost[o].sStatedQty = rlPre[o].sStatedQty
    rlPost[o].sOffManifest = rlPre[o].sOffManifest
    rlPost[o].sReceivedQty = o.receivedQty    // the FINAL accepted count (genesis births exactly it)
    rlPost[o].sRejectedQty = o.rejectedQty
    rlPost[o].sRejectionReason = o.rejectionReason   // WHY — with the final counts (TQ-2)
    rlPost[o].sNote = o.lineNote                         // the operator's clarification (TQ-2)
    rlPost[o].sBirthPins = o.birthPins        // pinned at THIS tick (§7 note; the audit boundary)
    rlPost[o].sPool = o.pool                  // born with the line's act (§8.5.3)
    rlPost[o].sDeliveries = rlPre[o].sDeliveries
    rlPost[o].sAttributions = rlPre[o].sAttributions   // membership freezes AS IS (§8.3.3)
  }
  all o: RecordDeliveryOcc | committed[o] implies {
    rlPost[o].sStatus = rlPre[o].sStatus
    sameLineCapture[rlPre[o], rlPost[o]]
    rlPost[o].sPool = rlPre[o].sPool
    rlPost[o].sDeliveries = rlPre[o].sDeliveries + o.delivery   // idempotent by set semantics (§8.1.3)
    rlPost[o].sAttributions = rlPre[o].sAttributions
  }
  all o: ReleaseLineOcc | committed[o] implies {
    rlPost[o].sStatus = RL_DISTRIBUTED
    sameLineCapture[rlPre[o], rlPost[o]]
    no rlPost[o].sPool                        // custody ends — the pool detaches, persists (§8.2.1/§8.5.1)
    rlPost[o].sDeliveries = rlPre[o].sDeliveries
    rlPost[o].sAttributions = rlPre[o].sAttributions
  }
  // ATTRIBUTION subject:
  all o: AttachAttributionOcc | committed[o] implies no oaPost[o].sActual
  all o: RecordActualOcc      | committed[o] implies oaPost[o].sActual = o.actual
  all o: DetachAttributionOcc | committed[o] implies o.post = o.pre   // the tombstone (II precedent)
}

// (NO cross-log enforcement facts beyond the three SAME-MODULE pairings above — C/OP: the
// guards ARE the saga commit gates; the §8.1.3 sDeliveries window is legally open in-flight,
// closed by the caller's RecordDelivery retry — runtime reconciliation rides the PD handle.)
