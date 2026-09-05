module procurement/order/order_implementation

/*
 * ORDER — IMPLEMENTATION (DT-018/DT-017). The log machinery for BOTH subjects: spine adoption
 * ×2, reason-precise admission guards, per-kind effects (record frames). The order ↔ demand
 * interactions are CONVERGENT/OPERATION call-first (see order_contracts.als): there is NO
 * cross-log enforcement fact — the guards ARE the saga commit gates, reading the serviced
 * demand items' current states; in-flight intermediates are legal. The same-module
 * order ↔ line laws are ATOMIC: line guards read the PARENT order's log directly.
 *
 * GUARDS READ `o.pre` (the chained record — the state the operation actually saw; refusals
 * included). Cross-log reads at `o.tick` are STRICTLY-BEFORE state: OneOccurrencePerTick means
 * `o` itself occupies the tick.
 *
 * The accumulate-completeness reading of `sReceived` (Σ of postings) is a THEOREM of
 * receiptAccrues + genesis + framing; its case-wise statement is CONFINED to order_received.als
 * and discharged only in the dedicated root (the demand_reset precedent — solver budget, not a
 * domain rule).
 */

open procurement/order/order_contracts
open procurement/order/order_types as ot   // rule 10: the parameter below was resolving through a transitive open
open meta/subject_log/subject_log[ot/Order, ot/OrderState] as olog          // same params ⇒ SAME spine as order_types
open meta/subject_log/subject_log[ot/OrderLine, ot/OrderLineState] as llog  // same params ⇒ SAME spine as order_types

// ── spine adoption ×2 (DT-015 Q5) ───────────────────────────────────────────────────────────────
fact OrderChaining       { olog/chained }
fact OrderCommitAccepts  { olog/commitAlwaysAccepts }   // v1 result policy
fact LineChaining        { llog/chained }
fact LineCommitAccepts   { llog/commitAlwaysAccepts }

// ── guard-side reads ────────────────────────────────────────────────────────────────────────────
/** liveAtOccO — the order is STARTED and LIVE as the operation reads it (pre-record). */
pred liveAtOccO[o: olog/SubjectOcc] { some o.pre and oPre[o].sStatus in liveOrderStatuses }
/** startedBeforeO / deletedBeforeO — order-subject history strictly before `o`. */
pred startedBeforeO[o: olog/SubjectOcc] {
  some b: olog/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
pred deletedBeforeO[o: olog/SubjectOcc] {
  some b: DeleteOrderOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
/** startedBeforeL / removedBeforeL — line-subject history strictly before `o`. */
pred startedBeforeL[o: llog/SubjectOcc] {
  some b: llog/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
pred removedBeforeL[o: llog/SubjectOcc] {
  some b: RemoveLineOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
/** usableLineAtOcc — the line is started, unremoved, and not L_CLOSED as `o` reads it. */
pred usableLineAtOcc[o: llog/SubjectOcc] {
  startedBeforeL[o] and not removedBeforeL[o] and lPre[o].sLineStatus != L_CLOSED
}
/** parentStatusAtOcc — the PARENT order's status as a line operation reads it (same-module
    ATOMIC: the guard reads the order log directly; strictly-before by OneOccurrencePerTick). */
fun parentStatusAtOcc[o: llog/SubjectOcc]: lone OrderStatus {
  orderStatusAt[parentOf[o.subject], o.tick]
}

// ── shared guard fragments ──────────────────────────────────────────────────────────────────────
/** supplierRefViol — DT-023 cut 7b (the dissolved-handle form): the binding's vendor PIN must
    be IN-TENANT (RForeignRef — role/type agreement is definitional, SupplierBindingPinAgrees)
    and its affiliate LIVE at the introducing write (RRetiredRef — the C-law: no committed
    introducing occurrence pins a retired-current target; a name-only/unpinned binding stays
    LEGAL, PDEV-241). `tid` is the acting subject's tenant; `t` the write's tick. */
fun supplierRefViol[b: SupplierBinding, tid: EntityId, t: Tick]: set Reason {
  ((some b.vendorPin and b.vendorPin.subject.tenantId != tid) => RForeignRef else none)
  + ((some b.vendorPin and not baLiveAt[b.vendorPin.subject, t]) => RRetiredRef else none)
}
/** assigneeRefViol — DT-023 cut 7c (the pin form): the assignee PIN must be IN-TENANT
    (RForeignRef) and its member LIVE at the introducing write (RRetiredRef — the D3
    pre-Submit new-ref row; an absent assignee stays LEGAL). `tid` is the acting subject's
    tenant; `t` the write's tick. */
fun assigneeRefViol[m: lone StaffOcc, tid: EntityId, t: Tick]: set Reason {
  ((some m and m.subject.tenantId != tid) => RForeignRef else none)
  + ((some m and not staffLiveAt[m.subject, t]) => RRetiredRef else none)
}
/** parentGateViol — the line-mutator preconditions on the PARENT order: it must be live
    (ROrderClosed) and DRAFT (RFrozen — the F5 freeze family). */
fun parentGateViol[o: llog/SubjectOcc]: set Reason {
  (let ord = parentOf[o.subject] |
    ((no ord or not liveOrderAt[ord, o.tick]) => ROrderClosed else none)
    + ((some ord and liveOrderAt[ord, o.tick] and orderStatusAt[ord, o.tick] != OS_DRAFT)
       => RFrozen else none))
}
/** attachDemandViol — the C/OP attach gate (order-side ONLY — O3): the demand item must resolve
    IN-TENANT (RForeignRef), be live and standing at RELEASED (RDemandIneligible — dangling
    refuses conservatively), be DENOMINATED in the line's item (RDemandIneligible — C3b: wrong
    item, or a FREE-FORM target line whose empty item resolution can never agree), retirement-guarded
    (RRetiredRef — DT-023 D3), and be serviced by
    NO live line (RDemandHeld; `self` excludes the acting line — its read at o.tick would be
    strictly-before anyway, but the acting line's own pre-membership is the separate
    double-attach check). */
fun attachDemandViol[o: llog/SubjectOcc, m: EntityId]: set Reason {
  (let d = resolve[m] & DemandItem |
    ((some d and d.tenantId != o.subject.tenantId) => RForeignRef else none)
    + ((no d or not liveDemandAt[d, o.tick] or demandStatusAt[d, o.tick] != DS_RELEASED)
       => RDemandIneligible else none)
    + ((some d and d.itemPin.subject != resolve[o.subject.itemRef] & Item)
       => RDemandIneligible else none)   // C3b item-agreement (MP 2026-07-10): wrong item OR free-form target
    // (The former attach RRetiredRef clause was REMOVED at DT-023 cut 8 — MP ruling
    //  2026-08-11: servicing an EXISTING demand is reference PROPAGATION, not inception;
    //  an order line MAY be created for a demand whose item has retired — otherwise the
    //  workflow strands the demand. The vendor commitment re-check stays at Submit.)
    + ((some d and some (holdingLineOf[d, o.tick] - o.subject))
       => RDemandHeld else none)   // the hold reading — parent-live lines only (a canceled order's holds are gone)
    + ((m in lPre[o].sDemand) => RDemandHeld else none))
}

// ── reason-precise admission guards (Accepted ⟺ ∅; because = EXACTLY the set) ───────────────────
// ORDER subject:
fun createOrderViol[o: CreateOrderOcc]: set Reason {
  (startedBeforeO[o] => ROrderStarted else none)
  + supplierRefViol[o.supplier, o.subject.tenantId, o.tick]
}
fun updateSupplierViol[o: UpdateSupplierOcc]: set Reason {
  ((not liveAtOccO[o]) => ROrderClosed else none)
  + ((liveAtOccO[o] and oPre[o].sStatus != OS_DRAFT) => RFrozen else none)
  + supplierRefViol[o.supplier, o.subject.tenantId, o.tick]
}
fun resetToSupplierViol[o: ResetToSupplierOcc]: set Reason {
  ((not liveAtOccO[o]) => ROrderClosed else none)
  + ((liveAtOccO[o] and oPre[o].sStatus != OS_DRAFT) => RFrozen else none)
}
fun submitViol[o: SubmitOcc]: set Reason {
  ((not liveAtOccO[o]) => ROrderClosed else none)
  + ((liveAtOccO[o] and oPre[o].sStatus != OS_DRAFT) => RBadState else none)
  + ((liveAtOccO[o] and no liveLinesOf[o.subject, o.tick]) => RNoLines else none)
  + ((liveAtOccO[o] and no oPre[o].sSupplier.name) => RNoSupplier else none)
  + ((liveAtOccO[o] and no oPre[o].sSupplier.vendorPin) => RNoSupplier else none)
                                 // DT-023 cut 8 (the PDEV-241 re-base): Submit requires a
                                 //   LINKED vendor — a draft may compose unlinked, but it
                                 //   cannot go out without a real BusinessAffiliate(VENDOR)
  + ((liveAtOccO[o] and some oPre[o].sSupplier.vendorPin
      and not baLiveAt[oPre[o].sSupplier.vendorPin.subject, o.tick])
     => RRetiredRef else none)   // DT-023 D3: Submit is the VENDOR commitment point — a draft
                                 //   against a since-retired vendor must not go out
  + ((liveAtOccO[o] and some d: servicedOf[o.subject, o.tick] | demandStatusAt[d, o.tick] != DS_IN_PROCESS)
     => RDemandIneligible else none)   // C/OP gate: every serviced item's StartProduction (saga's first legs) already committed
}
fun closeOrderViol[o: CloseOrderOcc]: set Reason {
  ((not liveAtOccO[o]) => ROrderClosed else none)
  + ((liveAtOccO[o] and oPre[o].sStatus != OS_SUBMITTED) => RBadState else none)
  + ((liveAtOccO[o] and some l: liveLinesOf[o.subject, o.tick] | lineStatusAt[l, o.tick] != L_CLOSED)
     => RLinesOpen else none)
}
fun cancelOrderViol[o: CancelOrderOcc]: set Reason {
  ((not liveAtOccO[o]) => ROrderClosed else none)
  + ((liveAtOccO[o] and oPre[o].sStatus != OS_DRAFT) => RBadState else none)   // O4: DRAFT-only; post-submission cancellation is PARKED
}
fun updateOrderDetailsViol[o: UpdateOrderDetailsOcc]: set Reason {
  ((not liveAtOccO[o]) => ROrderClosed else none)
  + ((liveAtOccO[o] and oPre[o].sStatus != OS_DRAFT) => RFrozen else none)   // the F5 family
  + assigneeRefViol[o.assignee, o.subject.tenantId, o.tick]
}
fun annotateOrderViol[o: AnnotateOrderOcc]: set Reason {
  ((not startedBeforeO[o] or deletedBeforeO[o]) => ROrderClosed else none)     // any lifecycle state (TQ-7(c): internal notes edit at ANY time), but the subject must exist
}
fun deleteOrderViol[o: DeleteOrderOcc]: set Reason {
  ((not startedBeforeO[o] or deletedBeforeO[o]) => ROrderClosed else none)
  + ((startedBeforeO[o] and oPre[o].sStatus in liveOrderStatuses) => RNotTerminal else none)
}
// LINE subject:
fun addLineViol[o: AddLineOcc]: set Reason {
  (startedBeforeL[o] => RLineStarted else none)
  + parentGateViol[o]
  + (some o.demand => attachDemandViol[o, o.demand] else none)
  // DT-023 cut 8 (inception vs propagation): the retirement gate binds only on the
  // FROM-SCRATCH arm (`no o.demand` — the buyer directly chooses the item); the QUEUE
  // arm (`some o.demand` — servicing an existing demand) inherits the reference —
  // propagation, ungated. Free-form lines skip either way. Cut 10 (the soft identity ref):
  // a DANGLING item reference refuses RForeignRef, a resolvable-but-retired one RRetiredRef
  // — the demand guardLiveItem shape one rung down. Tenancy rides the kernel (itemRef is a
  // dataRef since cut 10 — the LineItemPinTenancy side-fact dissolved).
  + ((no o.demand and some o.subject.itemRef and no (resolve[o.subject.itemRef] & Item))
     => RForeignRef else none)
  + ((no o.demand and some (resolve[o.subject.itemRef] & Item)
      and not itemLiveAt[resolve[o.subject.itemRef] & Item, o.tick])
     => RRetiredRef else none)
}
// (LinePinCurrency RETIRED at cut 10 — PDEV-1536: the line stores the item IDENTITY only; the
//  effective version is the read-time derivation `effectiveItemAt`, so genesis-currency of a
//  stored version pin is no longer meaningful. Genesis liveness stays guarded in addLineViol.)
// DT-023 cut 7b: a committed binding write's vendor pin is THEN-CURRENT (Q-A floating during
// DRAFT — each choose/override re-pins current; the Submit freeze then freezes the pin).
fact BindingPinCurrency {
  all o: CreateOrderOcc     | (committed[o] and some o.supplier.vendorPin) implies
    pinsCurrentBa[o.supplier.vendorPin, o.tick]
  all o: UpdateSupplierOcc  | (committed[o] and some o.supplier.vendorPin) implies
    pinsCurrentBa[o.supplier.vendorPin, o.tick]
}
// DT-023 cut 7c: a committed details write's assignee pin is THEN-CURRENT (floats pre-Submit;
// the headerDetailFrozen freeze then freezes the pin at Submit).
fact AssigneePinCurrency {
  all o: UpdateOrderDetailsOcc | (committed[o] and some o.assignee) implies
    pinsCurrentStaff[o.assignee, o.tick]
}
fun updateLineViol[o: UpdateLineOcc]: set Reason {
  ((not usableLineAtOcc[o]) => RLineClosed else none)
  + parentGateViol[o]
}
fun attachViol[o: AttachDemandOcc]: set Reason {
  ((not usableLineAtOcc[o]) => RLineClosed else none)
  + parentGateViol[o]
  + attachDemandViol[o, o.demand]
}
fun detachViol[o: DetachDemandOcc]: set Reason {
  ((not usableLineAtOcc[o]) => RLineClosed else none)
  + parentGateViol[o]
  + ((o.demand not in lPre[o].sDemand) => RNotAttached else none)
}
fun removeLineViol[o: RemoveLineOcc]: set Reason {
  ((not usableLineAtOcc[o]) => RLineClosed else none)
  + parentGateViol[o]
}
fun recordAckViol[o: RecordAcknowledgmentOcc]: set Reason {
  (let ord = parentOf[o.subject] |
    ((no ord or not liveOrderAt[ord, o.tick]) => ROrderClosed else none)
    + ((some ord and liveOrderAt[ord, o.tick] and orderStatusAt[ord, o.tick] != OS_SUBMITTED)
       => RBadState else none))
  + ((not usableLineAtOcc[o]) => RLineClosed else none)
}
fun recordReceiptViol[o: RecordReceiptOcc]: set Reason {
  (let ord = parentOf[o.subject] |
    ((no ord or not liveOrderAt[ord, o.tick]) => ROrderClosed else none))
  + ((not usableLineAtOcc[o]) => RLineClosed else none)
  + (freeForm[o.subject] => RNoDemand else none)   // F7: no received tracking on a free-form line
}
/** reverseReceiptViol — the accrual gate MIRRORED (F9b, cut 9). The RLineClosed/ROrderClosed
    refusals are LOAD-BEARING financially: after close the received quantity has priced the
    order, so a late revocation must NOT silently decrement — it refuses, and the runtime
    listener ALARMS on that refusal (MP 2026-08-14; post-close correction is credit-note
    territory, out of a listener's authority). */
fun reverseReceiptViol[o: ReverseReceiptOcc]: set Reason {
  (let ord = parentOf[o.subject] |
    ((no ord or not liveOrderAt[ord, o.tick]) => ROrderClosed else none))
  + ((not usableLineAtOcc[o]) => RLineClosed else none)
  + (freeForm[o.subject] => RNoDemand else none)   // F7: a free-form line never accrued
}
fun closeLineViol[o: CloseLineOcc]: set Reason {
  (let ord = parentOf[o.subject] |
    ((no ord or not liveOrderAt[ord, o.tick]) => ROrderClosed else none))
  + ((not usableLineAtOcc[o]) => RLineClosed else none)
}
fun annotateLineViol[o: AnnotateLineOcc]: set Reason {
  ((not startedBeforeL[o]) => RLineClosed else none)   // any state — removed/closed lines take notes
}

fact OrderAdmissionWitness {
  all o: CreateOrderOcc        | (o.admission = Accepted iff no createOrderViol[o])     and (o.admission in Rejected implies o.admission.because = createOrderViol[o])
  all o: UpdateSupplierOcc     | (o.admission = Accepted iff no updateSupplierViol[o])  and (o.admission in Rejected implies o.admission.because = updateSupplierViol[o])
  all o: ResetToSupplierOcc    | (o.admission = Accepted iff no resetToSupplierViol[o]) and (o.admission in Rejected implies o.admission.because = resetToSupplierViol[o])
  all o: SubmitOcc             | (o.admission = Accepted iff no submitViol[o])          and (o.admission in Rejected implies o.admission.because = submitViol[o])
  all o: CloseOrderOcc         | (o.admission = Accepted iff no closeOrderViol[o])      and (o.admission in Rejected implies o.admission.because = closeOrderViol[o])
  all o: CancelOrderOcc        | (o.admission = Accepted iff no cancelOrderViol[o])     and (o.admission in Rejected implies o.admission.because = cancelOrderViol[o])
  all o: UpdateOrderDetailsOcc | (o.admission = Accepted iff no updateOrderDetailsViol[o]) and (o.admission in Rejected implies o.admission.because = updateOrderDetailsViol[o])
  all o: AnnotateOrderOcc      | (o.admission = Accepted iff no annotateOrderViol[o])   and (o.admission in Rejected implies o.admission.because = annotateOrderViol[o])
  all o: DeleteOrderOcc        | (o.admission = Accepted iff no deleteOrderViol[o])     and (o.admission in Rejected implies o.admission.because = deleteOrderViol[o])
  all o: AddLineOcc            | (o.admission = Accepted iff no addLineViol[o])         and (o.admission in Rejected implies o.admission.because = addLineViol[o])
  all o: UpdateLineOcc         | (o.admission = Accepted iff no updateLineViol[o])      and (o.admission in Rejected implies o.admission.because = updateLineViol[o])
  all o: AttachDemandOcc       | (o.admission = Accepted iff no attachViol[o])          and (o.admission in Rejected implies o.admission.because = attachViol[o])
  all o: DetachDemandOcc       | (o.admission = Accepted iff no detachViol[o])          and (o.admission in Rejected implies o.admission.because = detachViol[o])
  all o: RemoveLineOcc         | (o.admission = Accepted iff no removeLineViol[o])      and (o.admission in Rejected implies o.admission.because = removeLineViol[o])
  all o: RecordAcknowledgmentOcc | (o.admission = Accepted iff no recordAckViol[o])     and (o.admission in Rejected implies o.admission.because = recordAckViol[o])
  all o: RecordReceiptOcc      | (o.admission = Accepted iff no recordReceiptViol[o])   and (o.admission in Rejected implies o.admission.because = recordReceiptViol[o])
  all o: ReverseReceiptOcc     | (o.admission = Accepted iff no reverseReceiptViol[o])  and (o.admission in Rejected implies o.admission.because = reverseReceiptViol[o])
  all o: CloseLineOcc          | (o.admission = Accepted iff no closeLineViol[o])       and (o.admission in Rejected implies o.admission.because = closeLineViol[o])
  all o: AnnotateLineOcc       | (o.admission = Accepted iff no annotateLineViol[o])    and (o.admission in Rejected implies o.admission.because = annotateLineViol[o])
}

// ── effects (committed) — per-kind frames on the records ────────────────────────────────────────
/** sameOrderDetail — the cut-6 header details carried over (priority / assignee / vendor
    notes / internal notes; the frame fragment every non-detail mutator composes). */
pred sameOrderDetail[b, a: OrderState] {
  a.sPriority = b.sPriority and a.sAssignee = b.sAssignee
  and a.sNotes = b.sNotes and a.sInternalNotes = b.sInternalNotes
}
/** sameOrderButStatus — everything except the status is carried over. */
pred sameOrderButStatus[b, a: OrderState] { a.sSupplier = b.sSupplier and sameOrderDetail[b, a] }
/** sameLineBut… — line-record carry-overs (each effect names what it changes; the rest framed.
    The item reference needs NO framing — it is the line's IDENTITY `itemRef`, immutable by
    construction; the effective version is a read-time derivation (cut 10), never record
    state). */
pred sameLineButQuantity[b, a: OrderLineState] {
  a.sConfirmation = b.sConfirmation and a.sReceived = b.sReceived
  and a.sLineStatus = b.sLineStatus and a.sDemand = b.sDemand
}
pred sameLineButDemand[b, a: OrderLineState] {
  a.sQuantity = b.sQuantity and a.sConfirmation = b.sConfirmation
  and a.sReceived = b.sReceived and a.sLineStatus = b.sLineStatus
}
pred sameLineButConfirmation[b, a: OrderLineState] {
  a.sQuantity = b.sQuantity and a.sReceived = b.sReceived
  and a.sLineStatus = b.sLineStatus and a.sDemand = b.sDemand
}
pred sameLineButReceived[b, a: OrderLineState] {
  a.sQuantity = b.sQuantity and a.sConfirmation = b.sConfirmation
  and a.sLineStatus = b.sLineStatus and a.sDemand = b.sDemand
}
pred sameLineButStatus[b, a: OrderLineState] {
  a.sQuantity = b.sQuantity and a.sConfirmation = b.sConfirmation
  and a.sReceived = b.sReceived and a.sDemand = b.sDemand
}

fact OrderEffectWitness {
  all o: CreateOrderOcc | committed[o] implies {
    oPost[o].sStatus = OS_DRAFT
    oPost[o].sSupplier = o.supplier               // seeds the binding (name may be the only content)
    oPost[o].sPriority = OP_UNDEFINED             // the seeded default (TQ-7(a), MP 2026-08-08)
    no oPost[o].sAssignee
    no oPost[o].sNotes
    no oPost[o].sInternalNotes
  }
  all o: UpdateSupplierOcc | committed[o] implies {
    oPost[o].sStatus = oPre[o].sStatus
    oPost[o].sSupplier = o.supplier
    sameOrderDetail[oPre[o], oPost[o]]
  }
  all o: ResetToSupplierOcc | committed[o] implies {
    oPost[o].sStatus = oPre[o].sStatus
    oPost[o].sSupplier.name       = oPre[o].sSupplier.name      // F8: overrides drop, the rest carries
    oPost[o].sSupplier.vendorPin  = oPre[o].sSupplier.vendorPin
    oPost[o].sSupplier.vendorRole = oPre[o].sSupplier.vendorRole
    oPost[o].sSupplier.base       = oPre[o].sSupplier.base
    no oPost[o].sSupplier.overrides
    sameOrderDetail[oPre[o], oPost[o]]
  }
  all o: UpdateOrderDetailsOcc | committed[o] implies {          // SET the DRAFT-mutable cluster
    oPost[o].sStatus = oPre[o].sStatus
    oPost[o].sSupplier = oPre[o].sSupplier
    oPost[o].sInternalNotes = oPre[o].sInternalNotes             // NOT this kind's facet
    oPost[o].sPriority = (some o.priority => o.priority else OP_UNDEFINED)   // absent ⇒ the default
    oPost[o].sAssignee = o.assignee                              // absent ⇒ cleared
    oPost[o].sNotes    = o.notes                                 // absent ⇒ cleared
  }
  all o: SubmitOcc | committed[o] implies
    { oPost[o].sStatus = OS_SUBMITTED and sameOrderButStatus[oPre[o], oPost[o]] }   // the freeze instant
  all o: CloseOrderOcc | committed[o] implies
    { oPost[o].sStatus = OS_CLOSED and sameOrderButStatus[oPre[o], oPost[o]] }
  all o: CancelOrderOcc | committed[o] implies
    { oPost[o].sStatus = OS_CANCELED and sameOrderButStatus[oPre[o], oPost[o]] }
  all o: AnnotateOrderOcc | committed[o] implies {               // SET the internal notes (any state)
    oPost[o].sInternalNotes = o.notes
    oPost[o].sStatus = oPre[o].sStatus
    oPost[o].sSupplier = oPre[o].sSupplier
    oPost[o].sPriority = oPre[o].sPriority
    oPost[o].sAssignee = oPre[o].sAssignee
    oPost[o].sNotes    = oPre[o].sNotes
  }
  all o: DeleteOrderOcc   | committed[o] implies o.post = o.pre   // the tombstone

  all o: AddLineOcc | committed[o] implies {
    lPost[o].sQuantity = o.qty
    no lPost[o].sConfirmation
    no lPost[o].sReceived                          // the keyed zero — accrual starts empty (F9)
    lPost[o].sLineStatus = L_OPEN
    lPost[o].sDemand = o.demand                    // lone → the singleton or empty set
  }
  all o: UpdateLineOcc | committed[o] implies {
    lPost[o].sQuantity = o.qty                     // SET (delta is client sugar)
    sameLineButQuantity[lPre[o], lPost[o]]
  }
  all o: AttachDemandOcc | committed[o] implies {
    lPost[o].sDemand = lPre[o].sDemand + o.demand
    sameLineButDemand[lPre[o], lPost[o]]
  }
  all o: DetachDemandOcc | committed[o] implies {
    lPost[o].sDemand = lPre[o].sDemand - o.demand
    sameLineButDemand[lPre[o], lPost[o]]
  }
  all o: RemoveLineOcc | committed[o] implies {    // the tombstone; refs DROP — the demand is back in the queue
    no lPost[o].sDemand
    sameLineButDemand[lPre[o], lPost[o]]
  }
  all o: RecordAcknowledgmentOcc | committed[o] implies {
    lPost[o].sConfirmation = o.confirmation
    sameLineButConfirmation[lPre[o], lPost[o]]
  }
  all o: RecordReceiptOcc | committed[o] implies {
    qtyMap[lPost[o].sReceived] = add[qtyMap[lPre[o].sReceived], qtyMap[o.qty]]   // += (pairwise — F9)
    sameLineButReceived[lPre[o], lPost[o]]
  }
  all o: ReverseReceiptOcc | committed[o] implies {
    qtyMap[lPost[o].sReceived] = add[qtyMap[lPre[o].sReceived], negate[qtyMap[o.qty]]]   // −= (pairwise — F9b, cut 9)
    sameLineButReceived[lPre[o], lPost[o]]
  }
  all o: CloseLineOcc | committed[o] implies {
    lPost[o].sLineStatus = L_CLOSED
    sameLineButStatus[lPre[o], lPost[o]]
  }
  all o: AnnotateLineOcc | committed[o] implies o.post = o.pre
}

// (NO cross-log enforcement facts — C/OP: the guards above ARE the saga commit gates; the
// commit-gate contract laws are THEOREMS of them, and the quiescence law `receiptsSettledAt`
// is witnessed on settled traces, never asserted globally.)
