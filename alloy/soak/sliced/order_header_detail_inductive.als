module soak/sliced/order_header_detail_inductive

/*
 * E7 generalization ladder, rung 3c (DT-024 plan-of-record, priority 3 — the FREEZE
 * FAMILY): inductiveness check of order `headerDetailFrozen` (C11), on the proven
 * receiver_pool_inductive template (the conventions/inductive_invariant idiom). Sibling of
 * order_supplier_binding_inductive — read that header for the per-occurrence shape; this
 * file repeats only what differs.
 *
 * THE LAW: committed[o] ∧ some oPre[o] ∧ oPre[o].sStatus ≠ DRAFT ⇒ sPriority, sAssignee,
 * sNotes carried over (sInternalNotes deliberately exempt — TQ-7(c)). Guard/frame-derived:
 * UpdateOrderDetails refuses RFrozen off-DRAFT; every other kind carries the cluster
 * (sameOrderDetail / the explicit Annotate frame / the Delete tombstone). UNCONDITIONAL in
 * the contracts — nothing to thread. Seeds: HavocOrderOcc on the order log (the details
 * live on the order record only).
 *
 * NIGHTWATCH 2026-08-27: base-scope shake-out by day; _w then _s gates in the night window.
 */

open procurement/order/order_implementation
open procurement/order/order_contracts
open operations/demand/demand_mock
open reference_data/item/item_mock
open reference_data/business_affiliate/business_affiliate_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock
open reference_data/staff/staff_mock
open procurement/order/order_types as ot
open meta/subject_log/subject_log[ot/Order, ot/OrderState] as olog
open meta/model_time/model_time as mt
open util/ordering[mt/Tick] as tord

// CREATED-ONLY SLICE — same environment restriction as order_soak.als (DT-023 Q-D).
fact CreatedOnlySlice {
  ItemOcc in CreateItemOcc
  BaOcc in CreateBaOcc
  StaffOcc in CreateStaffOcc
}

// ── the havoc seed ─────────────────────────────────────────────────────────────────────
/** HavocOrderOcc — induction seed: committed, frame-free order occurrence (see the sibling). */
sig HavocOrderOcc extends olog/SubjectOcc {} { bindings = subject }

fact HavocDiscipline {
  all h: HavocOrderOcc | h.admission = Accepted
  all h: HavocOrderOcc, o: olog/SubjectOcc - HavocOrderOcc | precedes[h.tick, o.tick]
}

// ── the candidate inductive invariant ──────────────────────────────────────────────────
/** detailFrozenAt — the published law's clause for ONE occurrence. */
pred detailFrozenAt[o: olog/SubjectOcc] {
  (committed[o] and some oPre[o] and oPre[o].sStatus != OS_DRAFT) implies {
    oPost[o].sPriority = oPre[o].sPriority
    oPost[o].sAssignee = oPre[o].sAssignee
    oPost[o].sNotes    = oPre[o].sNotes
  }
}
/** e7Inv — the per-tick slice: the clause over the occurrences AT t (the invariant itself). */
pred e7Inv[t: Tick] { all o: orderOccKinds | o.tick = t implies detailFrozenAt[o] }

/** lawSliceAt — the published law at a fixed tick (per-occurrence: identical to the slice). */
pred lawSliceAt[t: Tick] { e7Inv[t] }

// ── obligations ────────────────────────────────────────────────────────────────────────
assert e7_slice_faithful { (all t: Tick | lawSliceAt[t]) iff headerDetailFrozen }

assert e7_base { (no h: HavocOrderOcc | h.tick = tord/first) implies e7Inv[tord/first] }

assert e7_step {
  all t: Tick - tord/last | let t2 = tord/next[t] |
    (e7Inv[t] and (no h: HavocOrderOcc | h.tick = t2)) implies e7Inv[t2]
}

assert e7_law { all t: Tick | e7Inv[t] implies lawSliceAt[t] }

// ── vacuity guards (the §8 soundness-ledger discipline) ────────────────────────────────
/** A seeded post-DRAFT order state read by a later committed real occurrence on that
    order — the clause's antecedent realized FROM A SEED. */
run e7_seeded_frozen_read {
  some h: HavocOrderOcc, o: olog/SubjectOcc - HavocOrderOcc |
    committed[h] and oPost[h].sStatus != OS_DRAFT
    and committed[o] and o.subject = h.subject and some oPre[o] and oPre[o].sStatus != OS_DRAFT
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 2 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 1

/** A seeded DRAFT order state followed by a committed UpdateOrderDetails on it — the SETTER
    commits legally from a seeded pre. */
run e7_seeded_setter {
  some h: HavocOrderOcc, o: UpdateOrderDetailsOcc |
    committed[h] and oPost[h].sStatus = OS_DRAFT and committed[o] and o.subject = h.subject
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 2 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 1

check e7_slice_faithful for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 2 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_base for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 2 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_step for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 2 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_law for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 2 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

// ── W-scope escalation (the adoption gate: the unit-root trace window) ─────────────────
e7_step_w: check e7_step for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 2 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

e7_law_w: check e7_law for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 2 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

// ── supersession gate (b): SOAK-MATCHED entity scopes (soak_ord_headerDetailFrozen), trace window collapsed ──
e7_step_s: check e7_step for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 Order, 3 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      3 StaffMember, 6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0

e7_law_s: check e7_law for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 Order, 3 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      3 StaffMember, 6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0
