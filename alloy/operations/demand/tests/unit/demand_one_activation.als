module operations/demand/tests/unit/demand_one_activation
// Reflects dafny-domain src/operations/demand/tests/demand-tests.dfy: SplitCreatePairRefused, SplitRevokePairRefused and
//   DeliverUnderOneActivation (the reference model since MP's ruling of 2026-11-04; alloy/EXTENSIONS.md)

open operations/demand/demand_implementation
open operations/demand/demand_contracts
open reference_data/item/item_mock                            // lower layer as CONTRACT (DT-017)
open resources/processing_network/processing_network_mock    // Station stub as CONTRACT
open resources/kanban_card/kanban_card_mock                   // kanban as CONTRACT (DT-017)

/*
 * THE ONE-ACTIVATION LAW of the demand's two atomic compositions (the project owner's ruling QA764, option (a),
 * 2026-11-12; dafny-domain MD-089, `DemandsContract.PairsOneActivation`): the two halves of a committed pair cite the
 * same activation.
 *
 * DEDICATED ROOT: per composition, a NEGATIVE CONTROL and its POSITIVE TWIN at one scope.
 *  - The control asks for a committed pair whose halves cite TWO activations, `expect 0`. Without the law it finds one:
 *    each half cites an accepted activation of the service and agrees with it, which is all `activated` asks.
 *  - The twin asks for the same pair under ONE activation, `expect 1`: the scope holds the pair, so the control can fail.
 * A split pair needs two activations: the scopes count them among the occurrences (each is one more occurrence and one
 * more tick than its twin needs).
 */

// ── the create pairing (§8.1.2): CreateDelivery with the RecordProduction naming its delivery on its demand ──────────
run unit_dem_createPairOneActivation {
  some c: CreateDeliveryOcc, r: RecordProductionOcc | {
    committed[c] and committed[r]
    r.delivery = c.subject.eId and r.subject.eId = c.subject.demandRef
    r.arche = c.arche
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery, 2 Contribution, 0 Placement,
      12 Occurrence, 12 Tick, 14 EntityId, 14 Snapshot, 2 Note, 2 Reference expect 1

run unit_dem_splitCreatePairRefused {
  some c: CreateDeliveryOcc, r: RecordProductionOcc | {
    committed[c] and committed[r]
    r.delivery = c.subject.eId and r.subject.eId = c.subject.demandRef
    r.arche != c.arche
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery, 2 Contribution, 0 Placement,
      12 Occurrence, 12 Tick, 14 EntityId, 14 Snapshot, 2 Note, 2 Reference expect 0

// ── the revoke pairing: RevokeDelivery with the ExtractProduction naming its delivery on its demand ──────────────────
run unit_dem_revokePairOneActivation {
  some v: RevokeDeliveryOcc, x: ExtractProductionOcc | {
    committed[v] and committed[x]
    x.delivery = v.subject.eId and x.subject.eId = v.subject.demandRef
    x.arche = v.arche
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery, 2 Contribution, 0 Placement,
      14 Occurrence, 14 Tick, 14 EntityId, 15 Snapshot, 2 Note, 2 Reference expect 1

run unit_dem_splitRevokePairRefused {
  some v: RevokeDeliveryOcc, x: ExtractProductionOcc | {
    committed[v] and committed[x]
    x.delivery = v.subject.eId and x.subject.eId = v.subject.demandRef
    x.arche != v.arche
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 ProductionDelivery, 2 Contribution, 0 Placement,
      14 Occurrence, 14 Tick, 14 EntityId, 15 Snapshot, 2 Note, 2 Reference expect 0
