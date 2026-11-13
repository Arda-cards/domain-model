module operations/demand/tests/unit/demand_quantity
// Reflects dafny-domain src/operations/demand/tests/demand-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open operations/demand/demand_quantity
open reference_data/item/item_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock

/*
 * THE DEDICATED root of the demand's QUANTITY READ (TN-004; dafny-domain MD-076): the ONLY root that opens
 * demand_quantity.als. It replaces tests/unit/demand_reset.als, whose law (`ResetSnapsToSum`) left the reference model with
 * the stored intent. The quantity is no longer stored: it is the keyed sum of the LIVE contributions' quantities (a card
 * contribution's is its cycle's effective quantity; an external contribution's is its own), read at an instant.
 * The sum is stated CASE-WISE (0, 1 and 2 live contributions), as the reset's was: the demand cone cannot carry the general
 * keyed fold (the arity-4 atom budget, demand_reset.als's finding of 2026-07-06). Scopes here stay within those sizes BY DESIGN.
 *
 * WRITTEN FIRST (test-first, TN-005 section 10): `demand_quantity.als`, `demandQuantityAt` and `liveContributionsAt` arrive
 * with the model's commit. SCOPES ARE FIRST ESTIMATES, NOT YET RUN.
 */

// DemandTests.ContributionsSum — a card contribution and an external one: the quantity is their keyed sum.
run unit_demq_twoKindSum {
  some d: DemandItem, t: Tick, cc: CardContribution, e: ExternalContribution | {
    liveContributionsAt[d, t] = cc + e
    some genesisOf[resolve[cc.cycleRef] & CardCycle].qtyOverride
    demandQuantityAt[d, t] = add[effectiveQtyMap[resolve[cc.cycleRef] & CardCycle], qtyMap[e.quantity]]
    some demandQuantityAt[d, t]
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 2 Contribution,
      11 Tick, 12 EntityId, 6 Quantity, 13 Snapshot, 2 Note, 2 Reference, 2 ContributionId expect 1

// The same witness, after the card's cycle is WITHDRAWN: the card's entry is still in the state, it no longer counts, and the
// quantity is the external contribution's alone.
run unit_demq_withdrawnCardLeavesSum {
  some d: DemandItem, w: WithdrawOcc, t: Tick, cc: CardContribution, e: ExternalContribution | {
    committed[w] and notAfter[w.tick, t] and (resolve[cc.cycleRef] & CardCycle) = w.subject
    demandStateAt[d, t].sContributions = cc + e
    liveContributionsAt[d, t] = e
    demandQuantityAt[d, t] = qtyMap[e.quantity]
    some demandQuantityAt[d, t]
  }
} for 9 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 2 Contribution,
      12 Tick, 12 EntityId, 6 Quantity, 14 Snapshot, 11 Occurrence, 2 Note, 2 Reference, 2 ContributionId expect 1

// A demand with no live contribution reads the keyed zero.
run unit_demq_emptyIsZero {
  some d: DemandItem, t: Tick | {
    liveDemandAt[d, t] and no liveContributionsAt[d, t]
    no demandQuantityAt[d, t]
  }
} for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 0 CardCycle, 1 KanbanCard, 0 InventoryItem, 0 Contribution, 6 EntityId, 4 Quantity, 2 Note, 2 Reference, 2 ContributionId expect 1
