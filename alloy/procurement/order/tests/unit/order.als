module procurement/order/tests/unit/order

open procurement/order/order_implementation
open procurement/order/order_contracts
open operations/demand/demand_mock                            // demand as CONTRACT (DT-017 — the FIRST consumer of demand_mock)
open reference_data/item/item_mock                            // lower layers as CONTRACT
open reference_data/business_affiliate/business_affiliate_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock
open reference_data/staff/staff_mock                          // StaffMember as CONTRACT (cut 6 — the sAssignee target)

/*
 * UNIT suite for the order module (DT-018; TWO subjects on the spine). Every demand-side state
 * this suite needs rides the demand MOCK (contract only — no demand chaining/effects), so
 * demand records are cheap to instantiate at whatever status a scenario needs. Machine pins:
 * the PRINT machine (5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard) rides the
 * kanban types open; 5 Int. NB `for N` silently caps the TOTALS of the ABSTRACT parents —
 * Snapshot (records across ALL subjects) and the occurrence pool: heavy traces pin Snapshot,
 * Tick, and EntityId explicitly (the 2026-07-06 folklore).
 * The sReceived accumulate reading is discharged in the DEDICATED root (order_received.als).
 */

// ── CONTRACT DISCHARGE (check; UNSAT = the law holds of the implementation) ─────────────────────
assert unit_ord_contract_frozenOutsideDraft { frozenOutsideDraft }
check unit_ord_contract_frozenOutsideDraft for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station, 2 Note expect 0

assert unit_ord_contract_demandIndivisible { demandIndivisible }
check unit_ord_contract_demandIndivisible for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station, 2 Note expect 0

assert unit_ord_contract_attachRequiresReleased { attachRequiresReleased }
check unit_ord_contract_attachRequiresReleased for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station, 2 Note expect 0

assert unit_ord_contract_attachItemAgrees { attachItemAgrees }
check unit_ord_contract_attachItemAgrees for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station, 2 Note expect 0

assert unit_ord_contract_submitRequiresStarted { submitRequiresStarted }
check unit_ord_contract_submitRequiresStarted for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station, 2 Note expect 0

assert unit_ord_contract_receiptAccrues { receiptAccrues }
check unit_ord_contract_receiptAccrues for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station, 8 Quantity, 2 Note expect 0

assert unit_ord_contract_receiptReverses { receiptReverses }
check unit_ord_contract_receiptReverses for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station, 8 Quantity, 2 Note expect 0

assert unit_ord_contract_lineClosureByAct { lineClosureByAct }
check unit_ord_contract_lineClosureByAct for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station, 2 Note expect 0

assert unit_ord_contract_closeRequiresSettled { closeRequiresSettled }
check unit_ord_contract_closeRequiresSettled for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station, 2 Note expect 0

assert unit_ord_contract_supplierBindingFrozen { supplierBindingFrozen }
check unit_ord_contract_supplierBindingFrozen for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station, 2 Note expect 0

assert unit_ord_contract_orderTerminalClosure { orderTerminalClosure }
check unit_ord_contract_orderTerminalClosure for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station, 2 Note expect 0

// (unit_ord_contract_lineDescriptorFrozen RETIRED at DT-023 cut 7a: the law dissolved — the
//  item reference is the line's IDENTITY `itemRef`; the freeze semantics are the read-time
//  derivation — witnessed by unit_ord_effectiveItemFloatsWhileDraft /
//  unit_ord_effectiveItemFreezesAtSubmit below, cut 10.)

// ── SAT witnesses — the §2 scenarios ────────────────────────────────────────────────────────────
// Smoke/genesis: Create births DRAFT.
run unit_ord_createDraft {
  some o: CreateOrderOcc | committed[o] and orderStatusAt[o.subject, o.tick] = OS_DRAFT
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      7 EntityId, 2 Note expect 1

// Scenario 1 (build and submit, C/OP call-first): Create → AddLine servicing a RELEASED item →
// (the item's StartProduction commits demand-side — the mock supplies IN_PROCESS) → Submit.
run unit_ord_buildAndSubmit {
  some ord: Order, a: AddLineOcc, s: SubmitOcc, d: DemandItem | {
    parentOf[a.subject] = ord
    s.subject = ord
    committed[a] and committed[s]
    resolve[a.demand] = d
    precedes[a.tick, s.tick]
    demandStatusAt[d, a.tick] = DS_RELEASED
    demandStatusAt[d, s.tick] = DS_IN_PROCESS
    orderStatusAt[ord, s.tick] = OS_SUBMITTED
    d in servicedOf[ord, s.tick]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 12 EntityId, 10 Snapshot, 8 Occurrence, 2 Note expect 1
      // census +2 EntityId / +2 Occurrence at DT-023 cut 8: Submit now requires a LINKED
      // vendor, so the trace carries the BA Create fixture (the PDEV-241 re-base)

// Scenario 3 (acknowledgment, WAIVED flavor): the auto-confirm fires after Submit; the CONFIRMED
// derived reading holds (transient — a reading, not a transition).
run unit_ord_waivedConfirm {
  some ord: Order, k: RecordAcknowledgmentOcc | {
    parentOf[k.subject] = ord
    committed[k]
    k.confirmation.disposition = DISP_WAIVED
    confirmedReadingAt[ord, k.tick]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 9 EntityId, 10 Snapshot, 2 Note expect 1

// Scenario 4a (the C/NOTIF accrual, settled): a demand-side accrual is posted to the holding
// line; the quiescence law holds WITH REAL CONTENT and the RECEIVING reading flips.
run unit_ord_receiptSettles {
  some rp: RecordProductionOcc, rr: RecordReceiptOcc, t: Tick | {
    committed[rp] and committed[rr]
    rr.subject in holdingLineOf[rp.subject, t]
    precedes[rp.tick, rr.tick] and notAfter[rr.tick, t]
    receiptsSettledAt[t]
    receivingReadingAt[parentOf[rr.subject], t]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 Tick, 11 EntityId, 11 Snapshot, 4 Quantity, 2 Note, 8 Occurrence expect 1
      // census +1 at DT-023 cut 7a: the item-log fixture behind the attach agreement pushed
      // this deep witness past the old default-6 occurrence ceiling

// Cut 9 (F9b — MP 2026-08-14): a reversal COMPENSATES its accrual — record then reverse the
// same quantity and the stored sReceived reads the keyed zero again (the financially binding
// counter returns to its pre-record value; the keyed monoid zero-nets collapse).
run unit_ord_reverseCompensatesReceipt {
  some rr: RecordReceiptOcc, rv: ReverseReceiptOcc, t: Tick | {
    committed[rr] and committed[rv]
    rv.subject = rr.subject
    rv.qty = rr.qty
    precedes[rr.tick, rv.tick] and notAfter[rv.tick, t]
    some qtyMap[rr.qty]
    no qtyMap[lineStateAt[rr.subject, t].sReceived]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 9 EntityId, 10 Snapshot, 5 Quantity, 2 Note expect 1

// Cut 9 (the refusal-and-ALARM posture): a reversal against a CLOSED line refuses with exactly
// RLineClosed — the received quantity has priced the order, a late revocation must not silently
// decrement (the runtime listener alarms on this refusal).
run unit_ord_reverseOnClosedLineRefused {
  some o: ReverseReceiptOcc | {
    o.admission in Rejected
    o.admission.because = RLineClosed
    lPre[o].sLineStatus = L_CLOSED
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 9 EntityId, 10 Snapshot, 4 Quantity, 2 Note expect 1

// Scenario 4b (the C/NOTIF MISSED-NOTIFICATION WINDOW — must be LEGAL): an accrual committed,
// no posting yet, the quiescence law FALSE. The emitter cannot fix it; the listener/probe will.
run unit_ord_missedNotificationLegal {
  some rp: RecordProductionOcc, t: Tick | {
    committed[rp] and notAfter[rp.tick, t]
    some holdingLineOf[rp.subject, t]
    no rr: RecordReceiptOcc | committed[rr]
    not receiptsSettledAt[t]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 10 EntityId, 10 Snapshot, 2 Note expect 1

// Scenario 4c (the SELF-HEAL trace): the missed window is later repaired by the SAME kind (the
// probe's re-drive / manual posting) and quiescence is restored.
run unit_ord_selfHealRestores {
  some rp: RecordProductionOcc, rr: RecordReceiptOcc, t1, t2: Tick | {
    committed[rp] and committed[rr]
    rr.subject in holdingLineOf[rp.subject, t2]
    notAfter[rp.tick, t1] and precedes[t1, rr.tick] and notAfter[rr.tick, t2]
    some holdingLineOf[rp.subject, t1]
    not receiptsSettledAt[t1]
    receiptsSettledAt[t2]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 Tick, 10 EntityId, 10 Snapshot, 4 Quantity, 2 Note expect 1

// Scenario 5 (close short): a line closed BY ACT with open ≠ 0 (the derived "short" reading),
// then the order closes.
run unit_ord_closeShort {
  some ord: Order, cl: CloseLineOcc, c: CloseOrderOcc | {
    parentOf[cl.subject] = ord and c.subject = ord
    committed[cl] and committed[c]
    precedes[cl.tick, c.tick]
    some openOf[cl.subject, cl.tick]              // short: the open reading is non-zero at the close tick
    orderStatusAt[ord, c.tick] = OS_CLOSED
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 9 EntityId, 10 Snapshot, 4 Quantity, 2 Note expect 1

// Scenario 6 (cancel, DRAFT only): plain abandonment while composing.
run unit_ord_cancelDraft {
  some c: CancelOrderOcc | committed[c] and orderStatusAt[c.subject, c.tick] = OS_CANCELED
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      7 EntityId, 2 Note expect 1

// Scenario 6 corollary: THE HOLD DIES WITH THE ORDER — after Cancel, the serviced item is back
// in the queue (holdingLineOf empty) with NO line-by-line choreography; a NEW order may attach
// it (the guard's held-scan sees no live-order hold).
run unit_ord_cancelReturnsToQueue {
  some c: CancelOrderOcc, d: DemandItem, l: OrderLine | {
    committed[c]
    parentOf[l] = c.subject
    d in servicedAt[l, c.tick]                       // the line still RECORDS the servicing…
    no holdingLineOf[d, c.tick]                      // …but the HOLD is gone with the order
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 10 EntityId, 10 Snapshot, 2 Note expect 1

// The read-time derivation, DRAFT half (cut 10, PDEV-1536): while the parent is un-submitted
// the line's EFFECTIVE item version FLOATS — an item Update after line genesis moves it to the
// NEW current version (the runtime's C/NOTIF refresh is the performance shadow of this read).
run unit_ord_effectiveItemFloatsWhileDraft {
  some a: AddLineOcc, u: UpdateItemOcc, t: Tick | {
    committed[a] and committed[u]
    resolve[a.subject.itemRef] = u.subject and precedes[a.tick, u.tick] and notAfter[u.tick, t]
    no lineFreezeTick[a.subject, t]
    effectiveItemAt[a.subject, t] = itemVersionAt[u.subject, t]
    effectiveItemAt[a.subject, t] != itemVersionAt[u.subject, a.tick]   // it MOVED off the genesis version
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 9 EntityId, 9 Snapshot, 3 Quantity, 2 Note, 7 Occurrence expect 1

// The read-time derivation, FROZEN half (cut 10): after the parent's Submit the effective
// version is PINNED at the submit-tick version — a LATER item Update moves the current version
// on, the line's denotation stays (repeatable/auditable vendor commitments: what was agreed is
// the SUBMIT-time version, the [eId, rId] runtime coordinate).
run unit_ord_effectiveItemFreezesAtSubmit {
  some l: OrderLine, s: SubmitOcc, u: UpdateItemOcc, t: Tick | {
    committed[s] and committed[u]
    s.subject = parentOf[l] and some l.itemRef
    precedes[s.tick, u.tick] and resolve[l.itemRef] = u.subject and notAfter[u.tick, t]
    effectiveItemAt[l, t] = itemVersionAt[u.subject, s.tick]
    effectiveItemAt[l, t] != itemVersionAt[u.subject, t]   // the current version moved on; the line did not
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      11 Tick, 12 EntityId, 12 Snapshot, 4 Quantity, 2 Note, 10 Occurrence expect 1

// The F8 arc: choose → override → ResetToSupplier discards the overrides, keeps the identity.
run unit_ord_resetToSupplier {
  some r: ResetToSupplierOcc | {
    committed[r]
    some oPre[r].sSupplier.overrides
    no oPost[r].sSupplier.overrides
    oPost[r].sSupplier.vendorPin  = oPre[r].sSupplier.vendorPin
    oPost[r].sSupplier.vendorRole = oPre[r].sSupplier.vendorRole
    oPost[r].sSupplier.name = oPre[r].sSupplier.name
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      8 EntityId, 8 Snapshot, 3 SupplierBinding, 2 Note expect 1

// ── refusal witnesses — one per Reason, reason-PRECISE (because = exactly the set) ──────────────
run unit_ord_orderStartedRefused {
  some o: CreateOrderOcc | refusedAtAdmission[o] and o.admission.because = ROrderStarted
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      7 EntityId, 2 Note expect 1

run unit_ord_orderClosedRefused {
  some o: UpdateSupplierOcc | refusedAtAdmission[o] and o.admission.because = ROrderClosed
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      7 EntityId, 2 Note expect 1

run unit_ord_lineStartedRefused {
  some o: AddLineOcc | refusedAtAdmission[o] and o.admission.because = RLineStarted
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      8 EntityId, 2 Note expect 1

run unit_ord_lineClosedRefused {
  some o: UpdateLineOcc | refusedAtAdmission[o] and o.admission.because = RLineClosed
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      8 EntityId, 8 Snapshot, 2 Note expect 1

run unit_ord_frozenRefused {
  some o: AddLineOcc | refusedAtAdmission[o] and o.admission.because = RFrozen
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 2 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot, 2 Note expect 1

run unit_ord_badStateRefused {
  some o: CancelOrderOcc | refusedAtAdmission[o] and o.admission.because = RBadState
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot, 2 Note expect 1

run unit_ord_noLinesRefused {
  some o: SubmitOcc | refusedAtAdmission[o] and o.admission.because = RNoLines
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      7 EntityId, 2 Note expect 1

run unit_ord_noSupplierRefused {
  some o: SubmitOcc | refusedAtAdmission[o] and o.admission.because = RNoSupplier
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierName, 9 EntityId, 8 Snapshot, 2 Note expect 1

// DT-023 cut 7b re-shape of the PDEV-928 resolution-integrity refusal: a non-VENDOR selector
// became UNREPRESENTABLE (definitional SupplierBindingPinAgrees), so the refusal seat is now
// TENANCY — a cross-tenant vendor PIN refuses with exactly RForeignRef.
run unit_ord_foreignRefRefused {
  some o: CreateOrderOcc | {
    refusedAtAdmission[o] and o.admission.because = RForeignRef
    some o.supplier.vendorPin and o.supplier.vendorPin.subject.tenantId != o.subject.tenantId
  }
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      1 BusinessRole, 1 BusinessAffiliate, 10 EntityId, 6 Tick, 4 Snapshot, 4 Occurrence, 2 Note expect 1

run unit_ord_demandHeldRefused {
  some o: AttachDemandOcc | refusedAtAdmission[o] and o.admission.because = RDemandHeld
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 2 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 EntityId, 9 Snapshot, 2 Note expect 1

run unit_ord_demandIneligibleRefused {
  some o: AttachDemandOcc | {
    refusedAtAdmission[o] and o.admission.because = RDemandIneligible
    demandStatusAt[resolve[o.demand] & DemandItem, o.tick] = DS_OPEN   // the item is not yet in the queue
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot, 2 Note expect 1

// C3b (MP ruling 2026-07-10) — the WRONG-ITEM pairing: a RELEASED, live, unheld demand for a
// DIFFERENT item than the line's refuses RDemandIneligible; reason-PRECISE (the status conjunct
// is satisfied, so only the item-agreement fires).
run unit_ord_wrongItemRefused {
  some o: AttachDemandOcc, d: DemandItem | {
    refusedAtAdmission[o] and o.admission.because = RDemandIneligible
    resolve[o.demand] = d
    demandStatusAt[d, o.tick] = DS_RELEASED
    some o.subject.itemRef
    d.itemPin.subject != resolve[o.subject.itemRef] & Item
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      12 EntityId, 10 Snapshot, 10 Tick, 9 Occurrence, 2 Note expect 1
      // census +: two item logs (the line's and the demand's) ride the trace since cut 7a

// C3b corollary — the FREE-FORM target: attaching ANY demand (even RELEASED) to a line with no
// itemRef refuses RDemandIneligible. "Documentary only, no demand pairing" (F7 flag 3) is now a
// GUARD, not just prose.
run unit_ord_freeFormAttachRefused {
  some o: AttachDemandOcc, d: DemandItem | {
    refusedAtAdmission[o] and o.admission.because = RDemandIneligible
    resolve[o.demand] = d
    demandStatusAt[d, o.tick] = DS_RELEASED
    freeForm[o.subject]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 EntityId, 8 Snapshot, 2 Note expect 1

run unit_ord_notAttachedRefused {
  some o: DetachDemandOcc | refusedAtAdmission[o] and o.admission.because = RNotAttached
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot, 2 Note expect 1

run unit_ord_linesOpenRefused {
  some o: CloseOrderOcc | refusedAtAdmission[o] and o.admission.because = RLinesOpen
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot, 2 Note expect 1

run unit_ord_noDemandRefused {
  some o: RecordReceiptOcc | {
    refusedAtAdmission[o] and o.admission.because = RNoDemand
    freeForm[o.subject]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot, 3 Quantity, 2 Note expect 1

run unit_ord_notTerminalRefused {
  some o: DeleteOrderOcc | refusedAtAdmission[o] and o.admission.because = RNotTerminal
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      7 EntityId, 2 Note expect 1

// DT-023 D2/D3 (cut-8 form): LINE-ADD on a retired item refuses with exactly RRetiredRef
// on the FROM-SCRATCH arm only (`no o.demand` — the buyer's direct item choice; the queue
// arm is propagation, ungated — see the cut-8 witnesses below).
run unit_ord_lineRetiredItemRefused {
  some o: AddLineOcc | {
    no o.demand
    refusedAtAdmission[o] and o.admission.because = RRetiredRef
    some o.subject.itemRef
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot, 8 Tick, 6 Occurrence, 2 Note expect 1

// ── DT-023 cut 8: propagation ungated + the PDEV-241 re-base (MP rulings, 2026-08-11) ──────────

// PROPAGATION is ungated: attaching an EXISTING demand whose item has since RETIRED
// COMMITS — servicing a demand passes its reference along; refusing would strand the
// demand (the anti-deadlock half; the vendor commitment re-check stays at Submit).
run unit_ord_attachRetiredDemandAllowed {
  some o: AttachDemandOcc, x: RetireItemOcc | {
    committed[o] and committed[x]
    x.subject = resolve[o.subject.itemRef] and precedes[x.tick, o.tick]
    not itemLiveAt[resolve[o.subject.itemRef] & Item, o.tick]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      11 EntityId, 9 Snapshot, 9 Tick, 8 Occurrence, 2 Note expect 1

// The PDEV-241 re-base: Submit requires a LINKED vendor — a named-but-unpinned binding
// refuses with exactly RNoSupplier (the draft may compose unlinked; it cannot go out).
run unit_ord_submitUnlinkedSupplierRefused {
  some sub: SubmitOcc | {
    some oPre[sub].sSupplier.name
    no oPre[sub].sSupplier.vendorPin
    refusedAtAdmission[sub] and sub.admission.because = RNoSupplier
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      1 SupplierName, 10 EntityId, 8 Snapshot, 8 Tick, 6 Occurrence, 2 Note expect 1

// ── boundary witnesses (must be LEGAL — never UNSAT) ────────────────────────────────────────────
// A free-form line: documentary only — no item, no demand, no received tracking.
run unit_ord_freeFormLineLegal {
  some a: AddLineOcc | {
    committed[a]
    freeForm[a.subject] and no a.demand
    no lineStateAt[a.subject, a.tick].sDemand
    no qtyMap[lineStateAt[a.subject, a.tick].sReceived]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      8 EntityId, 8 Snapshot, 2 Note expect 1

// PDEV-241: a name-only, UNLINKED supplier is legal from genesis (no pin, no selector — the
// cut-7b form of "both handles empty").
run unit_ord_nameOnlySupplierLegal {
  some o: CreateOrderOcc | {
    committed[o]
    some o.supplier.name
    no o.supplier.vendorPin and no o.supplier.vendorRole
  }
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 BusinessRole, 0 BusinessAffiliate, 7 EntityId, 2 Note expect 1

// ── DT-023 cut 7b: the vendor pin at the Submit gate ───────────────────────────────────────────

// Reason-precise refusal (the D3 Submit row): a DRAFT whose pinned vendor retires before
// Submit refuses with exactly RRetiredRef — a draft against a dropped vendor must not go out.
// Fixture: BA Create → order Create (pin, name, line) → BA Delete → Submit refused.
run unit_ord_submitRetiredVendorRefused {
  some sub: SubmitOcc, d: RetireBaOcc {
    committed[d] and precedes[d.tick, sub.tick]
    oPre[sub].sSupplier.vendorPin.subject = d.subject
    refusedAtAdmission[sub] and sub.admission.because = RRetiredRef
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      1 BusinessAffiliate, 1 BusinessRole, 13 EntityId, 8 Tick, 8 Snapshot, 8 Occurrence, 2 Note expect 1

// Grandfather (the D3 SUBMITTED+ row): an order SUBMITTED against a live vendor stays legally
// SUBMITTED after the vendor retires — the frozen binding's PIN keeps serving the agreed
// version; no reactive law exists.
run unit_ord_submittedSurvivesVendorRetirement {
  some sub: SubmitOcc, d: RetireBaOcc, t: Tick {
    committed[sub] and committed[d]
    precedes[sub.tick, d.tick] and precedes[d.tick, t]
    some oPost[sub].sSupplier.vendorPin
    orderStatusAt[sub.subject, t] = OS_SUBMITTED
    not baLiveAt[oPost[sub].sSupplier.vendorPin.subject, t]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      1 BusinessAffiliate, 1 BusinessRole, 13 EntityId, 8 Tick, 8 Snapshot, 8 Occurrence, 2 Note expect 1

// Over-receipt is admissible (the advisory stance): two postings commit; the line stays open.
run unit_ord_overReceiptLegal {
  some disj r1, r2: RecordReceiptOcc | {
    committed[r1] and committed[r2]
    r1.subject = r2.subject
    lineStatusAt[r1.subject, r2.tick] = L_OPEN
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 9 EntityId, 10 Snapshot, 5 Quantity, 2 Note expect 1

// R1 one rung up: TWO live lines servicing DIFFERENT DemandItems of the SAME (item, station)
// pair — demandIndivisible constrains ITEMS, not identity pairs.
run unit_ord_samePairDifferentItemsLegal {
  some disj l1, l2: OrderLine, disj d1, d2: DemandItem, t: Tick | {
    d1.itemPin.subject = d2.itemPin.subject and d1.stationRef = d2.stationRef
    liveLineAt[l1, t] and liveLineAt[l2, t]
    d1 in servicedAt[l1, t] and d2 in servicedAt[l2, t]
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 2 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 Tick, 14 EntityId, 12 Snapshot, 2 Note expect 1

// The C/OP in-flight intermediate (O2): serviced items already IN_PROCESS, the order still
// DRAFT (no Submit committed) — the crash window is a LEGAL, queryable state.
run unit_ord_inFlightSubmitLegal {
  some ord: Order, d: DemandItem, t: Tick | {
    orderStatusAt[ord, t] = OS_DRAFT
    d in servicedOf[ord, t]
    demandStatusAt[d, t] = DS_IN_PROCESS
    no s: SubmitOcc | committed[s]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 10 EntityId, 10 Snapshot, 2 Note expect 1

// Tombstoned retirement: Delete commits on a CLOSED order; the terminal record persists.
// (Reaching CLOSED needs the FULL arc — Submit refuses RNoLines on a line-less order — so the
// trace is Create → AddLine → Submit → CloseLine → Close → Delete: six occurrences.)
run unit_ord_deleteRetiresTerminal {
  some x: DeleteOrderOcc | {
    committed[x]
    orderStatusAt[x.subject, x.tick] = OS_CLOSED
    orderDeletedAt[x.subject, x.tick]
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 Tick, 9 EntityId, 10 Snapshot, 2 Note expect 1

// ── CUT 6 (DT-022 TQ-7): header details + internal notes ────────────────────────────────────────
// The C11 law: priority / assignee / vendor notes unchanged by every post-DRAFT reader.
assert unit_ord_contract_headerDetailFrozen { headerDetailFrozen }
check unit_ord_contract_headerDetailFrozen for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 2 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 8 EntityId, 7 Tick, 8 Snapshot, 2 Note expect 0

// The seeded default (TQ-7(a), MP 2026-08-08): a committed Create births priority UNDEFINED.
assert unit_ord_contract_priorityDefault {
  all o: CreateOrderOcc | committed[o] implies oPost[o].sPriority = OP_UNDEFINED
}
check unit_ord_contract_priorityDefault for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      6 EntityId, 6 Tick, 6 Snapshot, 2 Note expect 0

// SET the DRAFT-mutable cluster: priority + assignee PIN + vendor notes land on the record
// (DT-023 cut 7c: the assignee is a staff VERSION pin — current-and-Live at the write).
run unit_ord_detailsSetWhileDraft {
  some o: UpdateOrderDetailsOcc | {
    committed[o]
    o.priority = OP_HIGH
    some o.assignee and staffPinnableAt[o.assignee, o.tick]
    some o.notes
    oPost[o].sPriority = OP_HIGH
    oPost[o].sAssignee = o.assignee
    oPost[o].sNotes = o.notes
  }
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      1 StaffMember, 8 EntityId, 6 Tick, 6 Snapshot, 5 Occurrence, 2 Note expect 1

// The freeze refusal: details cannot change once SUBMITTED — exactly RFrozen.
run unit_ord_detailsFrozenRefused {
  some o: UpdateOrderDetailsOcc | {
    o.admission in Rejected
    o.admission.because = RFrozen
    oPre[o].sStatus = OS_SUBMITTED
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 EntityId, 9 Tick, 10 Snapshot, 2 Note expect 1

// A foreign assignee refuses precisely: exactly RForeignRef (a cross-tenant staff PIN —
// the cut-7c form of the cross-tenant soft ref).
run unit_ord_assigneeForeignRefused {
  some o: UpdateOrderDetailsOcc | {
    o.admission in Rejected
    o.admission.because = RForeignRef
    some o.assignee and o.assignee.subject.tenantId != o.subject.tenantId
  }
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 9 EntityId, 6 Tick, 6 Snapshot, 5 Occurrence, 2 Note expect 1

// DT-023 cut 7c (the D3 pre-Submit new-ref row): assigning a RETIRED staff member refuses
// with exactly RRetiredRef. Fixture: staff Create → staff Delete → details write refused.
run unit_ord_assigneeRetiredRefused {
  some o: UpdateOrderDetailsOcc, d: RetireStaffOcc | {
    committed[d]
    some o.assignee and o.assignee.subject = d.subject
    o.admission in Rejected
    o.admission.because = RRetiredRef
  }
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      1 StaffMember, 9 EntityId, 7 Tick, 6 Snapshot, 6 Occurrence, 2 Note expect 1

// INTERNAL notes are editable at ANY time (TQ-7(c)): Annotate commits on a CLOSED order and
// CHANGES the internal note set — the deliberate exemption, witnessed not legislated.
run unit_ord_internalNotesAnyTime {
  some o: AnnotateOrderOcc | {
    committed[o]
    oPre[o].sStatus = OS_CLOSED
    oPost[o].sInternalNotes != oPre[o].sInternalNotes
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 Tick, 9 EntityId, 12 Snapshot, 2 Note expect 1

// ── DT-030 retire cut (2026-09-09): two acts, the annotate-line fix, terminality ─────────────────
// RemoveLine on a line still servicing a demand is refused RDemandAttached (TWO ACTS: detach first — MP's word).
run unit_ord_removeWithDemandRefused {
  some o: RemoveLineOcc | some lPre[o].sDemand and refusedAtAdmission[o] and RDemandAttached in o.admission.because
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 EntityId, 8 Snapshot, 2 Note expect 1
// A committed RemoveLine saw no demand attached (the law behind the two acts).
assert unit_ord_removeRequiresDetached { all o: RemoveLineOcc | committed[o] implies no lPre[o].sDemand }
check unit_ord_removeRequiresDetached for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 EntityId, 8 Snapshot, 2 Note expect 0
// Internal notes on a CLOSED line: Annotate commits and CHANGES the line's note set (TQ-7(c) one rung down; the point-defect fix).
run unit_ord_lineNotesOnClosedLine {
  some o: AnnotateLineOcc | committed[o] and lPre[o].sLineStatus = L_CLOSED and lPost[o].sInternalNotes != lPre[o].sInternalNotes
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot, 2 Note expect 1
// Annotate AFTER the line's retire is refused RLineClosed: terminality covers the line's notes (MP 2026-09-09).
run unit_ord_annotateAfterRemoveRefused {
  some r: RemoveLineOcc, o: AnnotateLineOcc | committed[r] and o.subject = r.subject and precedes[r.tick, o.tick]
    and refusedAtAdmission[o] and o.admission.because = RLineClosed
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot, 2 Note expect 1
// Terminality, both logs: nothing commits on an order after its committed delete, nor on a line after its committed remove.
assert unit_ord_nothingAfterRetire {
  all r: DeleteOrderOcc, o: CreateOrderOcc + UpdateSupplierOcc + ResetToSupplierOcc + SubmitOcc + CloseOrderOcc + CancelOrderOcc + UpdateOrderDetailsOcc + AnnotateOrderOcc + DeleteOrderOcc | (committed[r] and committed[o] and o.subject = r.subject) implies not precedes[r.tick, o.tick]
  all r: RemoveLineOcc, o: AddLineOcc + UpdateLineOcc + AttachDemandOcc + DetachDemandOcc + RemoveLineOcc + RecordAcknowledgmentOcc + RecordReceiptOcc + ReverseReceiptOcc + CloseLineOcc + AnnotateLineOcc | (committed[r] and committed[o] and o.subject = r.subject) implies not precedes[r.tick, o.tick]
}
check unit_ord_nothingAfterRetire for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot, 2 Note expect 0
