module soak/sliced/demand_holding_inductive

/*
 * E7 generalization ladder, rung 1b (DT-024 plan-of-record, MP 2026-08-26) —
 * inductiveness check of demand `holdingExclusiveWhileLive`, on the proven
 * receiver_pool_inductive template (the conventions/inductive_invariant idiom).
 *
 * SHAPE: candidate inductive invariant, per-tick:
 *   e7Inv[t] = holdingProvenanceAt[t] (the module's OWN published provenance,
 *              sliced per-tick) ∧ loneHolderAt[t].
 * Obligations (the four-obligation chain + both vacuity guards):
 *   e7_slice_faithful / e7_prov_faithful — per-tick slices ≡ the published laws.
 *   e7_base — e7Inv at the first tick (havoc-free).
 *   e7_step — e7Inv[t] preserved by ANY single real step from an ARBITRARY
 *             pre-state (HavocDemandOcc seeds); guards + frames + closure intact.
 *   e7_law  — e7Inv[t] ∧ genesis premise ∧ peer contracts (kanban MOCK facts —
 *             published `poolProvenance`) ⇒ the law slice at t, STATE-LOCAL. The
 *             cross-kind clause (no live cycle holds a demand-held pool) reasons
 *             from the attach payloads through the disjoint-genesis premise,
 *             exactly the receiving row's argument.
 *
 * HAVOC SOUNDNESS: HavocDemandOcc extends the demand-log SubjectOcc with NO effect
 * frame — its post ranges over arbitrary well-formed DemandState records. Seeds are
 * forced committed and strictly BEFORE every real demand occurrence; e7_step excludes
 * steps INTO a seed tick. Demand's admission/effect witnessing is per-kind, so seeds
 * are swept only by the unconditional chaining facts (benign — receiving precedent).
 * The vacuity guards below prove the seeded configurations are realizable.
 *
 * W-SCOPE ONLY this window (MP 2026-08-26): the soak-matched escalation is authored
 * (suffix _s) but NOT in the launch lanes — MP decides after the W results.
 */

open operations/demand/demand_implementation
open operations/demand/demand_contracts
open reference_data/item/item_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock
open operations/demand/demand_types as dt
open meta/subject_log/subject_log[dt/DemandItem, dt/DemandState] as dlog
open meta/model_time/model_time as mt
open util/ordering[mt/Tick] as tord

// CREATED-ONLY SLICE — same environment restriction as demand_soak.als (DT-023 Q-D).
fact CreatedOnlySlice {
  ItemOcc in CreateItemOcc
  BaOcc in CreateBaOcc
}

// ── the havoc seed ─────────────────────────────────────────────────────────────────────
/** HavocDemandOcc — induction seed: committed, frame-free demand occurrence; its post is
    an arbitrary well-formed record, so demand pre-states range over ALL states, not just
    reachable ones. */
sig HavocDemandOcc extends dlog/SubjectOcc {} { bindings = subject }

fact HavocDiscipline {
  all h: HavocDemandOcc | h.admission = Accepted
  all h: HavocDemandOcc, o: dlog/SubjectOcc - HavocDemandOcc | precedes[h.tick, o.tick]
}

// ── the candidate inductive invariant ──────────────────────────────────────────────────
/** holdingProvenanceAt — the published `holdingProvenance` sliced per-tick: a demand-held
    pool ref is EXACTLY some committed StartProduction's payload on that demand. */
pred holdingProvenanceAt[t: Tick] {
  all d: DemandItem | some demandStateAt[d, t].sHolding implies
    (some o: StartProductionOcc | committed[o] and o.subject = d and notAfter[o.tick, t]
       and demandStateAt[d, t].sHolding = o.holding)
}
/** loneHolderAt — the lone-live-demand facet at a fixed tick. */
pred loneHolderAt[t: Tick] {
  all p: InventoryPool |
    lone { d: DemandItem | liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p }
}
pred e7Inv[t: Tick] { holdingProvenanceAt[t] and loneHolderAt[t] }

/** lawSliceAt — the published law at a fixed tick (both facets under the genesis
    premise, exactly as in the contracts). */
pred lawSliceAt[t: Tick] {
  demandPoolGenesis implies {
    all p: InventoryPool {
      lone { d: DemandItem | liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p }
      (some d: DemandItem | liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p)
        implies (no c: CardCycle | liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p)
    }
  }
}

// ── obligations ────────────────────────────────────────────────────────────────────────
assert e7_slice_faithful { (all t: Tick | lawSliceAt[t]) iff holdingExclusiveWhileLive }

/** The per-tick provenance slices conjoin to the PUBLISHED law (ladder rung 2b credit). */
assert e7_prov_faithful { (all t: Tick | holdingProvenanceAt[t]) iff holdingProvenance }

// PREMISE-CONDITIONED (CTI at first W-window attempt, 2026-08-26, 36s at base scope):
// unlike receiving — whose lone-holder facet is UNCONDITIONAL in its published law and
// guard-derived — demand's lone-holder facet lives INSIDE the demandPoolGenesis premise:
// pool distinctness across pool-attaching acts is the premise's job, not a guard's, so
// from a havoc state where d1 holds p, a real StartProduction on d2 naming p commits
// legally and the unconditioned invariant breaks. Induction under the trace-global
// premise composes soundly: premise ∧ base ∧ step ⇒ ∀t e7Inv; e7Inv ⇒ lawSlice
// (premise-conditioned itself); together: premise ⇒ the published law — exactly its form.
assert e7_base {
  (demandPoolGenesis and (no h: HavocDemandOcc | h.tick = tord/first))
    implies e7Inv[tord/first]
}

assert e7_step {
  all t: Tick - tord/last | let t2 = tord/next[t] |
    (demandPoolGenesis and e7Inv[t] and (no h: HavocDemandOcc | h.tick = t2))
      implies e7Inv[t2]
}

assert e7_law { all t: Tick | e7Inv[t] implies lawSliceAt[t] }

// ── vacuity guards (the §8 soundness-ledger discipline) ────────────────────────────────
/** A seeded holding-carrying demand state coexisting with a later committed
    StartProduction — the step check's interesting configuration is realizable. */
run e7_seeded_production {
  some h: HavocDemandOcc | committed[h] and some dPost[h].sHolding
  some o: StartProductionOcc | committed[o] and some o.holding
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool, 0 ProductionDelivery,
      5 Occurrence, 14 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 1

/** A live pool-holding cycle coexisting with a seeded demand holding — e7_law's
    cross-kind antecedent is realizable. */
run e7_cross_kind_live {
  some t: Tick, c: CardCycle | liveCycleAt[c, t] and some stateOfCycleAt[c, t].sPool
  some h: HavocDemandOcc | committed[h] and some dPost[h].sHolding
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool, 0 ProductionDelivery,
      5 Occurrence, 14 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 1

check e7_slice_faithful for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool, 0 ProductionDelivery,
      5 Occurrence, 14 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_prov_faithful for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool, 0 ProductionDelivery,
      5 Occurrence, 14 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_base for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool, 0 ProductionDelivery,
      5 Occurrence, 14 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_step for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool, 0 ProductionDelivery,
      5 Occurrence, 14 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_law for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool, 0 ProductionDelivery,
      5 Occurrence, 14 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

// ── W-scope escalation (THIS window's adoption gate — MP 2026-08-26) ───────────────────
e7_step_w: check e7_step for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool, 0 ProductionDelivery,
      8 Occurrence, 14 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

e7_law_w: check e7_law for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool, 0 ProductionDelivery,
      8 Occurrence, 14 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

// ── soak-matched entity scopes (authored, NOT launched — awaits MP's post-W ruling) ────
e7_step_s: check e7_step for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool, 0 ProductionDelivery,
      6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0

e7_law_s: check e7_law for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool, 0 ProductionDelivery,
      6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0

// ── ladder rung 2b — the provenance row's OWN verdict (DT-024 priority 2; NIGHTWATCH 2026-08-27) ──
// `soak_dem_holdingProvenance` is the retained trace row. Its formal induction verdict:
//   e7_prov_faithful (above) — per-tick provenance slice ≡ the published `holdingProvenance`;
//   e7_prov_base / e7_prov_step — holdingProvenanceAt is inductive BY ITSELF: NO lone-holder
//   conjunct and NO genesis premise in the antecedent (provenance is frame-only —
//   StartProduction is the only sHolding setter and witnesses itself; every other kind
//   carries or clears — so, unlike the lone-holder facet, it owes the premise nothing).
//   Strictly stronger than the credit e7_step gives it. Gates: _w then _s.
assert e7_prov_base {
  (no h: HavocDemandOcc | h.tick = tord/first) implies holdingProvenanceAt[tord/first]
}
assert e7_prov_step {
  all t: Tick - tord/last | let t2 = tord/next[t] |
    (holdingProvenanceAt[t] and (no h: HavocDemandOcc | h.tick = t2)) implies holdingProvenanceAt[t2]
}

check e7_prov_base for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool, 0 ProductionDelivery,
      5 Occurrence, 14 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_prov_step for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool, 0 ProductionDelivery,
      5 Occurrence, 14 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

e7_prov_step_w: check e7_prov_step for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool, 0 ProductionDelivery,
      8 Occurrence, 14 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

e7_prov_step_s: check e7_prov_step for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool, 0 ProductionDelivery,
      6 Occurrence, 14 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0
