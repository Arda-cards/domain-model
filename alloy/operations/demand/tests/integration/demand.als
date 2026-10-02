module operations/demand/tests/integration/demand

open operations/demand/demand_implementation
open operations/demand/demand_contracts
open reference_data/item/item_implementation                        // the LOWER LAYERS for real
open resources/processing_network/processing_network_implementation
open resources/kanban_card/kanban_card_implementation

// (The SupplierReference CLOSURE fact DIED at DT-023 cut 7b: the handle dissolved into typed
// BA version pins — no orphan-closure obligation exists for typed occurrence references.)

/*
 * INTEGRATION suite for the demand module (DT-016/DT-017; C/OP call-first shape): the real
 * demand log composed with the REAL item + station stacks (the kanban cycle log and the pool
 * are already real in the unit tier — the INTERIM R3 seam). Gate tier: a joint loads witness,
 * the full R8 production arc, the re-collation-after-failure arc, and re-discharge of two key
 * laws on the composed stack.
 */

// ── joint loads: the composed stack is satisfiable, refs resolve across all layers ──────────────
run int_dem_loads {
  some o: CreateWithCycleOcc | {
    committed[o]
    itemLiveAt[o.subject.itemPin.subject, o.tick]
    some resolve[o.subject.stationRef] & Station
    some resolve[o.member] & CardCycle
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 12 EntityId, 10 Snapshot, 2 Note expect 1

// ── the R8 production arc (call-first): Accept → CreateWithCycle → Release → StartProcessing →
// StartProduction → PoolAdd (the member's pool fills on ITS log) → CompleteProcessing → Complete:
// the member ends READY off real pool content, the demand COMPLETE. ─────────────────────────────
run int_dem_productionToReady {
  some d: DemandItem, c: CardCycle, o: CompleteOcc, k: CompleteProcessingOcc | {
    o.subject = d and k.cycle = c
    committed[o] and committed[k] and precedes[k.tick, o.tick]
    demandStatusAt[d, o.tick] = DS_COMPLETE
    statusAt[c, o.tick] = READY
    some heldAt[resolve[stateOfCycleAt[c, o.tick].sPool] & InventoryPool, o.tick]
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 2 InventoryItem, 1 InventoryPool,
      12 Tick, 12 EntityId, 14 Snapshot, 11 Occurrence, 2 Note expect 1

// ── re-collation after production failure (R8 amended: PF → REQUESTING): the failed member
// re-enters the queue and joins a NEW demand item via a fresh Accept + attach. ──────────────────
run int_dem_recollationAfterFailure {
  some disj d1, d2: DemandItem, c: CardCycle, pf: ProductionFailureOcc, a2: MemberOcc & (AddCycleOcc + CreateWithCycleOcc) | {
    committed[pf] and pf.cycle = c
    committed[a2] and a2.subject = d2 and resolve[a2.member] = c
    precedes[pf.tick, a2.tick]
    demandStatusAt[d1, a2.tick] = DS_COMPLETE and c in attachedAt[d1, a2.tick]
    c in attachedAt[d2, a2.tick]
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem,
      14 Tick, 14 EntityId, 14 Snapshot, 12 Occurrence, 2 Note expect 1

// ── contract re-discharge on the composed stack (UNSAT = holds with the real lower layers) ──────
assert int_dem_contract_cycleIndivisible { cycleIndivisible }
check int_dem_contract_cycleIndivisible for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 0

assert int_dem_contract_frozenOutsideOpen { frozenOutsideOpen }
check int_dem_contract_frozenOutsideOpen for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 Note expect 0
