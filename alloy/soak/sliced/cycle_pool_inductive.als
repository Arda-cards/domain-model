module soak/sliced/cycle_pool_inductive

/*
 * E7 generalization ladder, rung 1a (DT-024 plan-of-record, MP 2026-08-26) —
 * inductiveness check of kanban `poolExclusiveWhileLive`, on the proven
 * receiver_pool_inductive template (the conventions/inductive_invariant idiom).
 *
 * SHAPE: candidate inductive invariant, per-tick:
 *   e7Inv[t] = poolProvenanceAt[t] (the module's OWN published provenance,
 *              sliced per-tick) ∧ loneHolderAt[t].
 * Obligations (the four-obligation chain + both vacuity guards):
 *   e7_slice_faithful / e7_prov_faithful — per-tick slices ≡ the published laws.
 *   e7_base — e7Inv at the first tick (havoc-free).
 *   e7_step — e7Inv[t] preserved by ANY single real step from an ARBITRARY
 *             pre-state (HavocCycleOcc seeds); guards + frames + closure intact.
 *   e7_law  — e7Inv[t] ⇒ the law slice at t (here the lone-holder facet itself —
 *             the chain's value is the STEP obligation).
 * This module's law has NO genesis premise and NO cross-kind clause (those live on
 * the demand/receiving lattice rows); the proof is fully module-local.
 *
 * HAVOC SOUNDNESS: HavocCycleOcc extends the cycle-log SubjectOcc with NO effect
 * frame — its post ranges over arbitrary well-formed CycleState records. Seeds are
 * forced committed and strictly BEFORE every real cycle occurrence; e7_step excludes
 * steps INTO a seed tick. Kanban's admission/effect witnessing is per-kind, so seeds
 * are swept only by the unconditional chaining facts (benign — receiving precedent).
 * The vacuity guards below prove the seeded configurations are realizable.
 *
 * W-SCOPE ONLY this window (MP 2026-08-26): the soak-matched escalation is authored
 * (suffix _s) but NOT in the launch lanes — MP decides after the W results.
 */

open resources/kanban_card/kanban_card_implementation
open resources/kanban_card/kanban_card_contracts
open resources/kanban_card/kanban_card_types as kt
open meta/subject_log/subject_log[kt/CardCycle, kt/CycleState] as clog
open meta/model_time/model_time as mt
open util/ordering[mt/Tick] as tord

// CREATED-ONLY SLICE — same environment restriction as kanban_soak.als (DT-023 Q-D).
fact CreatedOnlySlice {
  ItemOcc in CreateItemOcc
  BaOcc in CreateBaOcc
}

// ── the havoc seed ─────────────────────────────────────────────────────────────────────
/** HavocCycleOcc — induction seed: committed, frame-free cycle occurrence; its post is
    an arbitrary well-formed record, so cycle pre-states range over ALL states, not just
    reachable ones. */
sig HavocCycleOcc extends clog/SubjectOcc {} { bindings = subject }

fact HavocDiscipline {
  all h: HavocCycleOcc | h.admission = Accepted
  all h: HavocCycleOcc, o: clog/SubjectOcc - HavocCycleOcc | precedes[h.tick, o.tick]
}

// ── the candidate inductive invariant ──────────────────────────────────────────────────
/** poolProvenanceAt — the published `poolProvenance` sliced per-tick: a cycle-held pool
    ref is EXACTLY some committed StartProcessing's payload on that cycle. */
pred poolProvenanceAt[t: Tick] {
  all c: CardCycle | some stateOfCycleAt[c, t].sPool implies
    (some o: StartProcessingOcc | committed[o] and o.subject = c and notAfter[o.tick, t]
       and stateOfCycleAt[c, t].sPool = o.pool)
}
/** loneHolderAt — the published law at a fixed tick. */
pred loneHolderAt[t: Tick] {
  all p: InventoryPool |
    lone { c: CardCycle | liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p }
}
pred e7Inv[t: Tick] { poolProvenanceAt[t] and loneHolderAt[t] }

/** lawSliceAt — kanban's lattice row is exactly the lone-holder facet. */
pred lawSliceAt[t: Tick] { loneHolderAt[t] }

// ── obligations ────────────────────────────────────────────────────────────────────────
assert e7_slice_faithful { (all t: Tick | lawSliceAt[t]) iff poolExclusiveWhileLive }

/** The per-tick provenance slices conjoin to the PUBLISHED law (ladder rung 2a credit). */
assert e7_prov_faithful { (all t: Tick | poolProvenanceAt[t]) iff poolProvenance }

assert e7_base { (no h: HavocCycleOcc | h.tick = tord/first) implies e7Inv[tord/first] }

assert e7_step {
  all t: Tick - tord/last | let t2 = tord/next[t] |
    (e7Inv[t] and (no h: HavocCycleOcc | h.tick = t2)) implies e7Inv[t2]
}

assert e7_law { all t: Tick | e7Inv[t] implies lawSliceAt[t] }

// ── vacuity guards (the §8 soundness-ledger discipline) ────────────────────────────────
/** A seeded pool-holding cycle state coexisting with a later committed StartProcessing —
    the step check's interesting configuration is realizable. */
run e7_seeded_start {
  some h: HavocCycleOcc | committed[h] and some (h.post & CycleState).sPool
  some o: StartProcessingOcc | committed[o] and some o.pool
} for 5 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 3 InventoryPool,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 1

/** Two simultaneously live cycles — the lone-holder facet's interesting configuration
    is realizable (the check is not vacuously UNSAT-by-starvation). */
run e7_two_live {
  some t: Tick, disj c1, c2: CardCycle | liveCycleAt[c1, t] and liveCycleAt[c2, t]
} for 5 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 3 InventoryPool,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 1

check e7_slice_faithful for 5 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 3 InventoryPool,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_prov_faithful for 5 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 3 InventoryPool,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_base for 5 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 3 InventoryPool,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_step for 5 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 3 InventoryPool,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_law for 5 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 3 InventoryPool,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

// ── W-scope escalation (THIS window's adoption gate — MP 2026-08-26) ───────────────────
e7_step_w: check e7_step for 5 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 3 InventoryPool,
      8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

e7_law_w: check e7_law for 5 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 3 InventoryPool,
      8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

// ── soak-matched entity scopes (authored, NOT launched — awaits MP's post-W ruling) ────
e7_step_s: check e7_step for 6 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      4 CardCycle, 3 KanbanCard, 3 InventoryItem, 3 InventoryPool,
      6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0

e7_law_s: check e7_law for 6 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      4 CardCycle, 3 KanbanCard, 3 InventoryItem, 3 InventoryPool,
      6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0

// ── ladder rung 2a — the provenance row's OWN verdict (DT-024 priority 2; NIGHTWATCH 2026-08-27) ──
// `soak_cyc_poolProvenance` is the retained trace row. Its formal induction verdict:
//   e7_prov_faithful (above) — per-tick provenance slice ≡ the published `poolProvenance`;
//   e7_prov_base / e7_prov_step — poolProvenanceAt is inductive BY ITSELF: the antecedent
//   carries NO lone-holder conjunct (the single-setter + carry-frames argument verbatim —
//   StartProcessing is the only sPool setter and witnesses itself; every other kind carries
//   or clears). Strictly stronger than the credit e7_step gives it (where it rides inside
//   e7Inv). Gates: _w then _s, the receiving supersession standard.
assert e7_prov_base {
  (no h: HavocCycleOcc | h.tick = tord/first) implies poolProvenanceAt[tord/first]
}
assert e7_prov_step {
  all t: Tick - tord/last | let t2 = tord/next[t] |
    (poolProvenanceAt[t] and (no h: HavocCycleOcc | h.tick = t2)) implies poolProvenanceAt[t2]
}

check e7_prov_base for 5 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 3 InventoryPool,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_prov_step for 5 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 3 InventoryPool,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

e7_prov_step_w: check e7_prov_step for 5 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem, 3 InventoryPool,
      8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

e7_prov_step_s: check e7_prov_step for 6 but 5 Int, 3 Scalar, 5 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      4 CardCycle, 3 KanbanCard, 3 InventoryItem, 3 InventoryPool,
      6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0
