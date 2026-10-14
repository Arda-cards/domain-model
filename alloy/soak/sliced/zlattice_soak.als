module soak/sliced/zlattice_soak

/*
 * SOAK tier (DT-022 TQ-5): the GLOBAL exclusivity-lattice row at WIDENED scopes — the
 * heaviest soak check by far (the gate's tuned form ran ~14 min at cut 4); deliberately
 * LAST in the sequential soak order. Composes the three holder contracts (mocks), the
 * gate root's shape (tests/pool_lattice.als) with +1 on every holder census and widened
 * abstract parents. `make soak` only; never on the push path.
 */

open receiving/receiver/receiver_mock
open operations/demand/demand_mock
open resources/kanban_card/kanban_card_mock
open reference_data/item/item_mock
open reference_data/business_affiliate/business_affiliate_mock
open resources/processing_network/processing_network_mock
open resources/inventory_item/inventory_item_mock

assert soak_sys_poolLatticeGlobal {
  receivingPoolGenesis implies
    all t: Tick, p: InventoryPool |
      lone ({ l: ReceivingLine | resolve[rlStateAt[l, t].sPool] = p }
            + { c: CardCycle | liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p }
            + { d: DemandItem | liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p })
}
check soak_sys_poolLatticeGlobal for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      10 Occurrence, 15 EntityId, 8 Tick, 12 Snapshot, 2 Note expect 0

// CREATED-ONLY SLICE (DT-023 Q-D / DT-024, closing pass 7c): reference-data version
// dynamics are proven WIDE in soak/tests/reference_data_dynamics — this root reads
// reference data only through the pin/liveness API, so each subject carries exactly its
// Create and no Update/Delete atoms inflate the census (the lemma-then-slice retune).
fact CreatedOnlySlice {
  ItemOcc in CreateItemOcc
  BaOcc in CreateBaOcc
  StaffOcc in CreateStaffOcc
}
