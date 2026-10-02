module operations/demand/tests/unit/demand_reset

open operations/demand/demand_reset
open reference_data/item/item_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock

/*
 * THE DEDICATED ResetQty root (R3b confinement): the ONLY root that opens demand_reset.als.
 * The Σ is case-wise (0/1/2 live members — see the demand_reset.als header finding on the
 * arity-4 atom budget); scopes here stay within those sizes BY DESIGN.
 */

// Scenario 4 (reset-to-sum): the intent drifted via SET; ResetQty snaps it to the members' Σ of
// genesis-fixed effective quantities.
run unit_demr_resetSnapsToSum {
  some o: ResetQtyOcc, disj c1, c2: CardCycle | {
    committed[o]
    preMemberCycles[o] = c1 + c2
    some genesisOf[c1].qtyOverride and some genesisOf[c2].qtyOverride
    qtyMap[dPost[o].sDemandQty] = add[effectiveQtyMap[c1], effectiveQtyMap[c2]]
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 2 KanbanCard, 0 InventoryItem,
      10 Tick, 12 EntityId, 6 Quantity, 12 Snapshot, 2 Note expect 1

// Emptied-demand reset: with no live members the Σ is the keyed zero (the demand PERSISTS — R3b).
run unit_demr_resetEmptyIsZero {
  some o: ResetQtyOcc | committed[o] and no preMemberCycles[o]
    and no qtyMap[dPost[o].sDemandQty]
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 8 Tick, 6 EntityId, 4 Quantity, 2 Note expect 1
