module soak/sliced/receiver_pool_inductive

/*
 * E7 (DT-024 plan-of-record) — inductiveness check of `linePoolExclusiveWhileLive`.
 *
 * SHAPE: the classic invariant proof, not a trace soak. The candidate inductive
 * invariant is per-tick:
 *   e7Inv[t] = linePoolProvenanceAt[t] (line-held pool = some committed Receive's
 *              payload — the receiver-side MIRROR of the peers' published
 *              poolProvenance/holdingProvenance) ∧ loneHolderAt[t] (facet (i) slice).
 * Obligations:
 *   e7_slice_faithful — the per-tick slice conjunction ≡ the published law (traceability).
 *   e7_base — e7Inv at the first tick (havoc-free), trivial by empty history.
 *   e7_step — e7Inv[t] preserved by ANY single real step (arbitrary pre-states supplied
 *             by the HavocLineOcc seed kind; guards + frames + chaining stay intact).
 *   e7_law  — e7Inv[t] ∧ genesis premise ∧ peer contracts (mock facts) ⇒ law slice at t,
 *             STATE-LOCAL (no trace reasoning; rests on resolve = eId.id + EntityIdIsKey).
 * Together: base + step give e7Inv at every tick of every real trace; e7_law converts
 * that to the law — replacing trace-length-scaling search with state-local checks.
 *
 * HAVOC SOUNDNESS: HavocLineOcc extends the line-log SubjectOcc with NO effect frame,
 * so its post is an arbitrary well-formed ReceivingLineState (types-file extensionality
 * and ref-integrity facts still apply — they are record-level well-formedness we keep).
 * Seeds are forced committed and strictly BEFORE every real line occurrence; e7_step
 * excludes steps INTO a seed tick. All admission/effect witnessing in the implementation
 * is per-kind, so seeds are swept only by `chained`/`commitAlwaysAccepts` (both benign).
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

// CREATED-ONLY SLICE — same environment restriction as receiver_pool_exclusive.als.
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
/** linePoolProvenanceAt — receiver-side provenance (the peers' poolProvenance mirrored):
    a line-held pool ref is EXACTLY some committed Receive's payload on that line. */
pred linePoolProvenanceAt[t: Tick] {
  all l: ReceivingLine | some rlStateAt[l, t].sPool implies
    (some o: ReceiveLineOcc | committed[o] and o.subject = l and notAfter[o.tick, t]
       and rlStateAt[l, t].sPool = o.pool)
}
/** loneHolderAt — facet (i) at a fixed tick. */
pred loneHolderAt[t: Tick] {
  all p: InventoryPool | lone { l: ReceivingLine | resolve[rlStateAt[l, t].sPool] = p }
}
pred e7Inv[t: Tick] { linePoolProvenanceAt[t] and loneHolderAt[t] }

/** lawSliceAt — the published law at a fixed tick (facets (ii)/(iii) under the genesis
    premise, exactly as in the contracts). */
pred lawSliceAt[t: Tick] {
  loneHolderAt[t]
  receivingPoolGenesis implies
    all p: InventoryPool |
      (some l: ReceivingLine | resolve[rlStateAt[l, t].sPool] = p) implies
        ((no c: CardCycle | liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p)
         and (no d: DemandItem | liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p))
}

// ── obligations ────────────────────────────────────────────────────────────────────────
assert e7_slice_faithful { (all t: Tick | lawSliceAt[t]) iff linePoolExclusiveWhileLive }

/** The per-tick provenance slices conjoin to the PUBLISHED law (contracts, 2026-08-24). */
assert e7_prov_faithful { (all t: Tick | linePoolProvenanceAt[t]) iff linePoolProvenance }

assert e7_base { (no h: HavocLineOcc | h.tick = tord/first) implies e7Inv[tord/first] }

assert e7_step {
  all t: Tick - tord/last | let t2 = tord/next[t] |
    (e7Inv[t] and (no h: HavocLineOcc | h.tick = t2)) implies e7Inv[t2]
}

assert e7_law { all t: Tick | e7Inv[t] implies lawSliceAt[t] }

// ── vacuity guards (the §8 soundness-ledger discipline) ────────────────────────────────
/** A seeded pool-holding state coexisting with a later committed Receive — the step
    check's interesting configuration is realizable. */
run e7_seeded_receive {
  some h: HavocLineOcc | committed[h] and some rlPost[h].sPool
  some o: ReceiveLineOcc | committed[o] and some o.pool
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 2 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      1 CardCycle, 1 KanbanCard, 1 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 1

/** A live pool-holding cycle coexisting with a seeded line state — e7_law's cross-kind
    antecedent is realizable. */
run e7_cross_kind_live {
  some t: Tick, c: CardCycle | liveCycleAt[c, t] and some stateOfCycleAt[c, t].sPool
  some h: HavocLineOcc | committed[h] and some rlPost[h].sPool
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 2 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      1 CardCycle, 1 KanbanCard, 1 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 1

check e7_slice_faithful for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 2 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      1 CardCycle, 1 KanbanCard, 1 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_prov_faithful for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 2 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      1 CardCycle, 1 KanbanCard, 1 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_base for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 2 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      1 CardCycle, 1 KanbanCard, 1 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_step for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 2 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      1 CardCycle, 1 KanbanCard, 1 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

check e7_law for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 2 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      1 CardCycle, 1 KanbanCard, 1 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      5 Occurrence, 12 EntityId, 5 Tick, 8 Snapshot, 2 Note expect 0

// ── scope-escalation confirmation (the adoption gate): the unit-root scopes ────────────
e7_step_w: check e7_step for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 2 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      1 CardCycle, 1 KanbanCard, 1 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

e7_law_w: check e7_law for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 2 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      1 CardCycle, 1 KanbanCard, 1 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0

// ── supersession gate (b): SOAK-MATCHED ENTITY scopes, trace window collapsed ──────────
e7_step_s: check e7_step for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 2 DemandItem, 0 ProductionDelivery,
      2 CardCycle, 2 KanbanCard, 2 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      6 Occurrence, 16 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0

e7_law_s: check e7_law for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 2 DemandItem, 0 ProductionDelivery,
      2 CardCycle, 2 KanbanCard, 2 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      6 Occurrence, 16 EntityId, 6 Tick, 9 Snapshot, 2 Note expect 0
