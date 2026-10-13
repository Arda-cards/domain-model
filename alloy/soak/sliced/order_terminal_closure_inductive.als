module soak/sliced/order_terminal_closure_inductive

/*
 * E7 generalization ladder, priority 4 — RUNG T (DT-024 priority-4 plan, window-2 report):
 * inductiveness check of order `orderTerminalClosure` (C10 / SL-4, ATOMIC): once an order is
 * CLOSED or CANCELED it is CLOSED/CANCELED at every later tick. Supersedes the trace row
 * `soak_ord_terminalClosure` (order_soak.als — UNVERIFIED-at-cut after 12h + ~17h orphaned).
 * Built on the freeze-family template (order_frozen_outside_draft_inductive.als); read that
 * header for the per-occurrence shape — this file repeats only what differs.
 *
 * THE LAW is a two-tick statement over the order's state reading; its PER-OCCURRENCE slice
 * is a frame theorem on ONE log: every committed order occurrence whose pre-record is
 * terminal has a terminal post-record (or none — Delete tombstones, `none in terminal` is
 * vacuously true, and `orderStatusAt` reads nothing thereafter). The guards that make it
 * hold: no kind moves status except Submit (DRAFT→SUBMITTED), Close (→CLOSED), Cancel
 * (→CANCELED); Close/Cancel require a live pre-record (`ROrderClosed` otherwise); Annotate
 * and Delete frame or drop the status. No history conjunct — state-local, like the freeze
 * rungs, so seeded pre-states are exercised directly (no "arbitrary pre-state" caveat).
 *
 * SEEDS on the order log only (HavocOrderOcc): the law reads no line record.
 *
 * CP-1 (base scope) by day; `_w` then `_s` gates in a NIGHTWATCH window (lane T).
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

// ── the havoc seed (order log) ─────────────────────────────────────────────────────────
/** HavocOrderOcc — induction seed: committed, frame-free occurrence whose post is an
    arbitrary well-formed order record, so pre-states range over ALL states. */
sig HavocOrderOcc extends olog/SubjectOcc {} { bindings = subject }

fact HavocDiscipline {
  all h: HavocOrderOcc | h.admission = Accepted
  all h: HavocOrderOcc, o: olog/SubjectOcc - HavocOrderOcc | precedes[h.tick, o.tick]
}
pred seedAt[t: Tick] { some h: HavocOrderOcc | h.tick = t }

// ── the candidate inductive invariant ──────────────────────────────────────────────────
fun terminalStatuses: set OrderStatus { OS_CLOSED + OS_CANCELED }

/** terminalPreservedAt — ONE occurrence: a committed occurrence read at a terminal record
    leaves a terminal record (or none). */
pred terminalPreservedAt[o: olog/SubjectOcc] {
  (committed[o] and some oPre[o] and oPre[o].sStatus in terminalStatuses)
    implies oPost[o].sStatus in terminalStatuses
}
/** e7Inv — the per-tick slice: preservation over the occurrences AT t. */
pred e7Inv[t: Tick] { all o: orderOccKinds | o.tick = t implies terminalPreservedAt[o] }

/** lawSliceAt — the published law at a fixed tick (per-occurrence: identical to the slice). */
pred lawSliceAt[t: Tick] { e7Inv[t] }

// ── obligations ────────────────────────────────────────────────────────────────────────
assert e7_slice_faithful { (all t: Tick | lawSliceAt[t]) iff orderTerminalClosure }

assert e7_base { (not seedAt[tord/first]) implies e7Inv[tord/first] }

assert e7_step {
  all t: Tick - tord/last | let t2 = tord/next[t] |
    (e7Inv[t] and not seedAt[t2]) implies e7Inv[t2]
}

assert e7_law { all t: Tick | e7Inv[t] implies lawSliceAt[t] }

// ── vacuity guards (the §8 soundness-ledger discipline) ────────────────────────────────
/** A seeded TERMINAL order with a later committed real occurrence on it (Annotate commits at
    any state; Delete on a terminal record) — the preservation path is realizable from a
    seeded terminal state. */
run e7_seeded_terminal_act {
  some h: HavocOrderOcc, o: olog/SubjectOcc - HavocOrderOcc |
    committed[h] and oPost[h].sStatus in terminalStatuses
    and committed[o] and o.subject = h.subject and precedes[h.tick, o.tick]
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 1

/** A seeded LIVE order that later closes — the entry into the terminal set is realizable
    from a seeded pre-state (the step is not vacuous on the non-terminal side). */
run e7_seeded_close {
  some h: HavocOrderOcc, o: CloseOrderOcc + CancelOrderOcc |
    committed[h] and oPost[h].sStatus in liveOrderStatuses
    and committed[o] and o.subject = h.subject and precedes[h.tick, o.tick]
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 1

check e7_slice_faithful for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_base for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_step for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_law for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

// ── W-scope escalation (the adoption gate: the unit-root trace window) ─────────────────
e7_step_w: check e7_step for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

e7_law_w: check e7_law for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

// ── supersession gate (b): SOAK-MATCHED entity scopes (soak_ord_terminalClosure), trace window collapsed ──
e7_step_s: check e7_step for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 Order, 4 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0

e7_law_s: check e7_law for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 Order, 4 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0
