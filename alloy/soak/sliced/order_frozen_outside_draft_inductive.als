module soak/sliced/order_frozen_outside_draft_inductive

/*
 * E7 generalization ladder, rung 3a (DT-024 plan-of-record, priority 3 — the FREEZE
 * FAMILY): inductiveness check of order `frozenOutsideDraft` (C1/F5), on the proven
 * receiver_pool_inductive template (the conventions/inductive_invariant idiom). Sibling of
 * order_supplier_binding_inductive — read that header for the per-occurrence shape; this
 * file repeats only what differs.
 *
 * THE LAW (two clauses, TWO LOGS): a committed ORDER structural mutator (UpdateSupplier /
 * ResetToSupplier / UpdateOrderDetails) read its own record at DRAFT; a committed LINE
 * structural mutator (AddLine / UpdateLine / AttachDemand / DetachDemand / RemoveLine) read
 * the PARENT order's log at DRAFT (`orderStatusAt[parentOf[o.subject], o.tick]` — same
 * module, the guard reads it directly: parentGateViol's RFrozen). Guard-derived,
 * UNCONDITIONAL in the contracts — nothing to thread.
 *
 * SEEDS ON BOTH LOGS: HavocOrderOcc makes the parent's status arbitrary at the line
 * mutator's read (the clause that matters); HavocLineOcc makes the line's own pre-state
 * arbitrary as well, so the line guards are exercised from any line record, not only
 * reachable ones. Both kinds are frame-free, always committed, strictly before every real
 * occurrence on their log; e7_step excludes steps INTO a seed tick on either log.
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
open meta/subject_log/subject_log[ot/OrderLine, ot/OrderLineState] as llog
open meta/model_time/model_time as mt
open util/ordering[mt/Tick] as tord

// CREATED-ONLY SLICE — same environment restriction as order_soak.als (DT-023 Q-D).
fact CreatedOnlySlice {
  ItemOcc in CreateItemOcc
  BaOcc in CreateBaOcc
  StaffOcc in CreateStaffOcc
}

// ── the havoc seeds (one kind per log) ─────────────────────────────────────────────────
/** HavocOrderOcc / HavocLineOcc — induction seeds: committed, frame-free occurrences whose
    posts are arbitrary well-formed records, so pre-states on BOTH logs range over ALL
    states, not just reachable ones. */
sig HavocOrderOcc extends olog/SubjectOcc {} { bindings = subject }
sig HavocLineOcc  extends llog/SubjectOcc {} { bindings = subject }

fact HavocDiscipline {
  all h: HavocOrderOcc + HavocLineOcc | h.admission = Accepted
  all h: HavocOrderOcc, o: olog/SubjectOcc - HavocOrderOcc | precedes[h.tick, o.tick]
  all h: HavocLineOcc,  o: llog/SubjectOcc - HavocLineOcc  | precedes[h.tick, o.tick]
}
pred seedAt[t: Tick] { some h: HavocOrderOcc + HavocLineOcc | h.tick = t }

// ── the candidate inductive invariant ──────────────────────────────────────────────────
/** orderMutatorDraftAt / lineMutatorDraftAt — the published law's two clauses, for ONE
    occurrence each. */
pred orderMutatorDraftAt[o: olog/SubjectOcc] {
  committed[o] implies oPre[o].sStatus = OS_DRAFT
}
pred lineMutatorDraftAt[o: llog/SubjectOcc] {
  committed[o] implies orderStatusAt[parentOf[o.subject], o.tick] = OS_DRAFT
}
/** e7Inv — the per-tick slice: both clauses over the mutators AT t (the invariant itself). */
pred e7Inv[t: Tick] {
  all o: orderStructuralMutators | o.tick = t implies orderMutatorDraftAt[o]
  all o: lineStructuralMutators  | o.tick = t implies lineMutatorDraftAt[o]
}

/** lawSliceAt — the published law at a fixed tick (per-occurrence: identical to the slice). */
pred lawSliceAt[t: Tick] { e7Inv[t] }

// ── obligations ────────────────────────────────────────────────────────────────────────
assert e7_slice_faithful { (all t: Tick | lawSliceAt[t]) iff frozenOutsideDraft }

assert e7_base { (not seedAt[tord/first]) implies e7Inv[tord/first] }

assert e7_step {
  all t: Tick - tord/last | let t2 = tord/next[t] |
    (e7Inv[t] and not seedAt[t2]) implies e7Inv[t2]
}

assert e7_law { all t: Tick | e7Inv[t] implies lawSliceAt[t] }

// ── vacuity guards (the §8 soundness-ledger discipline) ────────────────────────────────
/** A seeded DRAFT parent whose line gets a committed AddLine later — the line clause's
    LEGAL path is realizable from a seeded parent state. */
run e7_seeded_line_add {
  some h: HavocOrderOcc, o: AddLineOcc |
    committed[h] and oPost[h].sStatus = OS_DRAFT
    and committed[o] and parentOf[o.subject] = h.subject and precedes[h.tick, o.tick]
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 1

/** A seeded post-DRAFT parent beside a seeded line record, with a later line structural
    mutator on that line — the freeze REFUSAL path (the guard reading a seeded parent) is
    realizable, and so is an arbitrary line pre-state under it. */
run e7_seeded_frozen_parent {
  some h: HavocOrderOcc, hl: HavocLineOcc, o: lineStructuralMutators - HavocLineOcc |
    committed[h] and oPost[h].sStatus != OS_DRAFT
    and committed[hl] and o.subject = hl.subject and parentOf[o.subject] = h.subject
    and precedes[h.tick, o.tick] and not committed[o]
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
e7_step_w: check e7_step for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

e7_law_w: check e7_law for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

// ── supersession gate (b): SOAK-MATCHED entity scopes (soak_ord_frozenOutsideDraft), trace window collapsed ──
e7_step_s: check e7_step for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 Order, 4 OrderLine, 3 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0

e7_law_s: check e7_law for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 Order, 4 OrderLine, 3 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0
