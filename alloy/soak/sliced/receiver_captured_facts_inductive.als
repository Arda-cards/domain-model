module soak/sliced/receiver_captured_facts_inductive

/*
 * E7 generalization ladder, rung 3d (DT-024 plan-of-record, priority 3 — the FREEZE
 * FAMILY): inductiveness check of receiving `capturedFactsFrozen` (C3, §8.3.4/§8.3.5), on
 * the proven receiver_pool_inductive template (the conventions/inductive_invariant idiom).
 * Sibling of order_supplier_binding_inductive — read that header for the per-occurrence
 * shape; this file repeats only what differs.
 *
 * THE LAW: committed[o] ∧ some rlPre[o] ∧ rlPre[o].sStatus ≠ RL_RECEIVING ⇒ the ten-field
 * captured-facts cluster (expectation, counts, rejection reason, note, birth pins, and the
 * attribution MEMBERSHIP) carried over. Guard/frame-derived: the capture mutators
 * (UpdateReceivingLine / Append- / RemoveAttribution) refuse RFrozen off-RECEIVING, Receive
 * refuses RBadState off-RECEIVING (the freeze instant reads RECEIVING), and the
 * post-freeze kinds (RecordDelivery / ReleaseLine) carry the cluster (sameLineCapture +
 * the membership frame). UNCONDITIONAL in the contracts — nothing to thread. Seeds:
 * HavocLineOcc on the line log — the SAME seed kind receiver_pool_inductive proved sound on
 * this log (the pairing facts AttachComposesWithAppend / DetachComposesWithRemove /
 * ReceiveFansOutActuals and the pin-currency facts all name their kinds).
 *
 * Cone: the receiving_soak cone verbatim (ten mocks) — the same assurance perimeter as
 * `soak_rcv_capturedFactsFrozen`, the row this rung is to supersede.
 *
 * NIGHTWATCH 2026-08-27: base-scope shake-out by day; _w then _s gates in the night window.
 */

open receiving/receiver/receiver_implementation
open receiving/receiver/receiver_contracts
open operations/demand/demand_mock
open procurement/order/order_mock
open reference_data/item/item_mock
open reference_data/business_affiliate/business_affiliate_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock
open resources/inventory_item/inventory_item_mock
open reference_data/staff/staff_mock
open receiving/receiver/receiver_types as rt
open meta/subject_log/subject_log[rt/ReceivingLine, rt/ReceivingLineState] as rllog
open meta/model_time/model_time as mt
open util/ordering[mt/Tick] as tord

// CREATED-ONLY SLICE — same environment restriction as receiving_soak.als.
fact CreatedOnlySlice {
  ItemOcc in CreateItemOcc
  BaOcc in CreateBaOcc
  StaffOcc in CreateStaffOcc
}

// ── the havoc seed ─────────────────────────────────────────────────────────────────────
/** HavocLineOcc — induction seed: committed, frame-free line occurrence; its post is an
    arbitrary well-formed record, so line pre-states range over ALL states, not just
    reachable ones. */
sig HavocLineOcc extends rllog/SubjectOcc {} { bindings = subject }

fact HavocDiscipline {
  all h: HavocLineOcc | h.admission = Accepted
  all h: HavocLineOcc, o: rllog/SubjectOcc - HavocLineOcc | precedes[h.tick, o.tick]
}

// ── the candidate inductive invariant ──────────────────────────────────────────────────
/** capturedFrozenAt — the published law's clause for ONE occurrence (the ten-field frame). */
pred capturedFrozenAt[o: rllog/SubjectOcc] {
  (committed[o] and some rlPre[o] and rlPre[o].sStatus != RL_RECEIVING) implies {
    rlPost[o].sExpectedItem = rlPre[o].sExpectedItem
    rlPost[o].sExpectedQty  = rlPre[o].sExpectedQty
    rlPost[o].sStatedQty    = rlPre[o].sStatedQty
    rlPost[o].sReceivedQty  = rlPre[o].sReceivedQty
    rlPost[o].sRejectedQty  = rlPre[o].sRejectedQty
    rlPost[o].sOffManifest  = rlPre[o].sOffManifest
    rlPost[o].sRejectionReason = rlPre[o].sRejectionReason
    rlPost[o].sNote         = rlPre[o].sNote
    rlPost[o].sBirthPins    = rlPre[o].sBirthPins
    rlPost[o].sAttributions = rlPre[o].sAttributions
  }
}
/** e7Inv — the per-tick slice: the clause over the occurrences AT t (the invariant itself). */
pred e7Inv[t: Tick] { all o: rlOccKinds | o.tick = t implies capturedFrozenAt[o] }

/** lawSliceAt — the published law at a fixed tick (per-occurrence: identical to the slice). */
pred lawSliceAt[t: Tick] { e7Inv[t] }

// ── obligations ────────────────────────────────────────────────────────────────────────
assert e7_slice_faithful { (all t: Tick | lawSliceAt[t]) iff capturedFactsFrozen }

assert e7_base { (no h: HavocLineOcc | h.tick = tord/first) implies e7Inv[tord/first] }

assert e7_step {
  all t: Tick - tord/last | let t2 = tord/next[t] |
    (e7Inv[t] and (no h: HavocLineOcc | h.tick = t2)) implies e7Inv[t2]
}

assert e7_law { all t: Tick | e7Inv[t] implies lawSliceAt[t] }

// ── vacuity guards (the §8 soundness-ledger discipline) ────────────────────────────────
/** A seeded post-freeze line state read by a later committed real occurrence on that line
    — the clause's antecedent realized FROM A SEED (the step's interesting configuration). */
run e7_seeded_frozen_read {
  some h: HavocLineOcc, o: rllog/SubjectOcc - HavocLineOcc |
    committed[h] and rlPost[h].sStatus != RL_RECEIVING
    and committed[o] and o.subject = h.subject and some rlPre[o] and rlPre[o].sStatus != RL_RECEIVING
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 2 OrderAttribution, 0 Order, 2 OrderLine, 0 DemandItem, 1 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 1

/** A seeded RECEIVING line state followed by a committed capture edit on it — the SETTER
    commits legally from a seeded pre (the guard/frame boundary is exercised, not starved). */
run e7_seeded_capture_edit {
  some h: HavocLineOcc, o: UpdateReceivingLineOcc |
    committed[h] and rlPost[h].sStatus = RL_RECEIVING and committed[o] and o.subject = h.subject
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 2 OrderAttribution, 0 Order, 2 OrderLine, 0 DemandItem, 1 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 1

check e7_slice_faithful for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 2 OrderAttribution, 0 Order, 2 OrderLine, 0 DemandItem, 1 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_base for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 2 OrderAttribution, 0 Order, 2 OrderLine, 0 DemandItem, 1 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_step for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 2 OrderAttribution, 0 Order, 2 OrderLine, 0 DemandItem, 1 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_law for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 2 OrderAttribution, 0 Order, 2 OrderLine, 0 DemandItem, 1 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

// ── W-scope escalation (the adoption gate: the unit-root trace window) ─────────────────
e7_step_w: check e7_step for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 2 OrderAttribution, 0 Order, 2 OrderLine, 0 DemandItem, 1 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

e7_law_w: check e7_law for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 2 OrderAttribution, 0 Order, 2 OrderLine, 0 DemandItem, 1 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

// ── supersession gate (b): SOAK-MATCHED entity scopes (soak_rcv_capturedFactsFrozen), trace window collapsed ──
e7_step_s: check e7_step for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 Receiver, 4 ReceivingLine, 3 OrderAttribution, 0 Order, 3 OrderLine, 0 DemandItem, 2 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 2 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0

e7_law_s: check e7_law for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 Receiver, 4 ReceivingLine, 3 OrderAttribution, 0 Order, 3 OrderLine, 0 DemandItem, 2 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 2 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0
