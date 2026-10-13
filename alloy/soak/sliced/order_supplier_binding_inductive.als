module soak/sliced/order_supplier_binding_inductive

/*
 * E7 generalization ladder, rung 3b (DT-024 plan-of-record, priority 3 — the FREEZE
 * FAMILY): inductiveness check of order `supplierBindingFrozen` (C9), on the proven
 * receiver_pool_inductive template (the conventions/inductive_invariant idiom).
 *
 * SHAPE — A PER-OCCURRENCE LAW. The published law quantifies over OCCURRENCES, not ticks:
 *   committed[o] ∧ some oPre[o] ∧ oPre[o].sStatus ≠ DRAFT ⇒ oPost[o].sSupplier = oPre[o].sSupplier.
 * Its per-tick slice is the clause over the occurrences AT that tick, and the slice IS the
 * candidate invariant — a frame law carries no state-shaped strengthening (nothing
 * accumulates). The four-obligation chain therefore reads:
 *   e7_slice_faithful — the per-tick slices ∧-compose to the published law (traceability).
 *   e7_base — the slice at the first tick (havoc-free; genesis reads no pre).
 *   e7_step — THE SUBSTANTIVE OBLIGATION: the real occurrence at t2 satisfies the clause
 *             from an ARBITRARY pre-state at t (HavocOrderOcc seeds) — the direct
 *             guard/frame theorem the plan-of-record row anticipates: UpdateSupplier and
 *             ResetToSupplier refuse RFrozen off-DRAFT; every other kind carries sSupplier
 *             (sameOrderButStatus / the explicit frames / the Delete tombstone).
 *   e7_law  — invariant ⇒ law slice: the identity for a per-occurrence law, kept so the
 *             chain reads uniformly across the ladder.
 * Unlike the exclusivity rows, the seeds' arbitrary posts are exercised DIRECTLY as the
 * step's pre-states — the slice references no history, so no witness conjunct filters
 * seeded states out of the antecedent.
 *
 * HAVOC SOUNDNESS: HavocOrderOcc extends the order-log SubjectOcc with NO effect frame —
 * its post is an arbitrary well-formed OrderState. Seeds are forced committed and strictly
 * BEFORE every real order occurrence; e7_step excludes steps INTO a seed tick. The order
 * module's admission/effect witnessing and its pin-currency facts (BindingPinCurrency,
 * AssigneePinCurrency) all name their kinds, so seeds are swept only by olog/chained +
 * commitAlwaysAccepts — benign (the receiving precedent). The law is UNCONDITIONAL in the
 * contracts (guard/frame-derived, no genesis premise) — nothing to thread.
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
/** HavocOrderOcc — induction seed: committed, frame-free order occurrence; its post is an
    arbitrary well-formed record, so order pre-states range over ALL states, not just
    reachable ones. */
sig HavocOrderOcc extends olog/SubjectOcc {} { bindings = subject }

fact HavocDiscipline {
  all h: HavocOrderOcc | h.admission = Accepted
  all h: HavocOrderOcc, o: olog/SubjectOcc - HavocOrderOcc | precedes[h.tick, o.tick]
}

// ── the candidate inductive invariant ──────────────────────────────────────────────────
/** supplierFrozenAt — the published law's clause for ONE occurrence. */
pred supplierFrozenAt[o: olog/SubjectOcc] {
  (committed[o] and some oPre[o] and oPre[o].sStatus != OS_DRAFT) implies
    oPost[o].sSupplier = oPre[o].sSupplier
}
/** e7Inv — the per-tick slice: the clause over the occurrences AT t (the invariant itself). */
pred e7Inv[t: Tick] { all o: orderOccKinds | o.tick = t implies supplierFrozenAt[o] }

/** lawSliceAt — the published law at a fixed tick (per-occurrence: identical to the slice). */
pred lawSliceAt[t: Tick] { e7Inv[t] }

// ── obligations ────────────────────────────────────────────────────────────────────────
assert e7_slice_faithful { (all t: Tick | lawSliceAt[t]) iff supplierBindingFrozen }

assert e7_base { (no h: HavocOrderOcc | h.tick = tord/first) implies e7Inv[tord/first] }

assert e7_step {
  all t: Tick - tord/last | let t2 = tord/next[t] |
    (e7Inv[t] and (no h: HavocOrderOcc | h.tick = t2)) implies e7Inv[t2]
}

assert e7_law { all t: Tick | e7Inv[t] implies lawSliceAt[t] }

// ── vacuity guards (the §8 soundness-ledger discipline) ────────────────────────────────
/** A seeded post-DRAFT order state read by a later committed real occurrence on that
    order — the clause's antecedent realized FROM A SEED (the step's interesting
    configuration is realizable). */
run e7_seeded_frozen_read {
  some h: HavocOrderOcc, o: olog/SubjectOcc - HavocOrderOcc |
    committed[h] and oPost[h].sStatus != OS_DRAFT
    and committed[o] and o.subject = h.subject and some oPre[o] and oPre[o].sStatus != OS_DRAFT
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 1

/** A seeded DRAFT order state followed by a committed UpdateSupplier on it — the SETTER
    commits legally from a seeded pre (the guard/frame boundary is exercised, not starved). */
run e7_seeded_setter {
  some h: HavocOrderOcc, o: UpdateSupplierOcc |
    committed[h] and oPost[h].sStatus = OS_DRAFT and committed[o] and o.subject = h.subject
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

// ── supersession gate (b): SOAK-MATCHED entity scopes (soak_ord_supplierBindingFrozen), trace window collapsed ──
e7_step_s: check e7_step for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 Order, 4 OrderLine, 3 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0

e7_law_s: check e7_law for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 Order, 4 OrderLine, 3 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0
