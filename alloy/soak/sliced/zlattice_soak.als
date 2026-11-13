module soak/sliced/zlattice_soak
// Refines Dafny: PoolLattice.PoolLatticeGlobal
//   (dafny-domain, the reference model; this root is listed in alloy/EXTENSIONS.md)

/*
 * SOAK tier (DT-022 TQ-5): the GLOBAL exclusivity-lattice row at WIDENED scopes — the
 * heaviest soak check by far (the gate's tuned form ran ~14 min at cut 4, and 2 h 21 min for its
 * last verdict); deliberately LAST in the sequential soak order. Composes the three holder
 * contracts (mocks), the gate root's shape (tests/pool_lattice.als) with +1 on every holder census
 * and widened abstract parents. `make soak` only; never on the push path.
 *
 * FOUR HOLDER KINDS since the TN-004 projection (the project owner's ruling QA773, second question,
 * option (i), 2026-11-12: this check is kept, extended and run in the night window, while its gate
 * twin `sys_poolLatticeGlobal` is retired). The fourth kind is a live demand's EXTERNAL CONTRIBUTION
 * (dafny-domain `HContribution`, MD-086). A contribution is a value, so the fourth kind is counted by
 * its OWNERS and, per owner, by its contributions: the assertion is the four-conjunct form the gate
 * check had before its retirement.
 *
 * THE SCOPE HOLDS THE CASE THE CHECK IS ABOUT: the law refuses a second holder on a held pool, so a
 * scope too small for a holder AND a second attach examines nothing. The sixteen `soak_lat_*` finders,
 * one per ordered pair of holder kinds, exhibit at the check's own scope a world where the genesis
 * premise holds, a pool is held, and a second attach names it. All sixteen are found at 10 ticks and
 * occurrences (measured 2026-11-13; smaller bounds were not measured). Before, the check stated
 * "10 Occurrence, 8 Tick": with one occurrence per tick that held 8 occurrences, and a second holder
 * between two cycles needs 9.
 */

open receiving/receiver/receiver_mock
open operations/demand/demand_mock
open resources/kanban_card/kanban_card_mock
open reference_data/item/item_mock
open reference_data/business_affiliate/business_affiliate_mock
open resources/processing_network/processing_network_mock
open resources/inventory_item/inventory_item_mock

/** The holders of pool `p` at `t`, by kind. The fourth kind's are the OWNERS: the live demands holding `p` through an
    external contribution. */
fun lineHolders[p: InventoryPool, t: Tick]: set ReceivingLine {
  { l: ReceivingLine | resolve[rlStateAt[l, t].sPool] = p }
}
fun cycleHolders[p: InventoryPool, t: Tick]: set CardCycle {
  { c: CardCycle | liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p }
}
fun holdingHolders[p: InventoryPool, t: Tick]: set DemandItem {
  { d: DemandItem | liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p }
}
fun contributionOwners[p: InventoryPool, t: Tick]: set DemandItem {
  { d: DemandItem | some c: ExternalContribution | contributionHolds[d, c, c.cPool, t] and resolve[c.cPool] = p }
}

assert soak_sys_poolLatticeGlobal {
  receivingPoolGenesis implies
    all t: Tick, p: InventoryPool | {
      lone (lineHolders[p, t] + cycleHolders[p, t] + holdingHolders[p, t])
      lone contributionOwners[p, t]
      all d: DemandItem | lone { c: ExternalContribution | contributionHolds[d, c, c.cPool, t] and resolve[c.cPool] = p }
      (some contributionOwners[p, t]) implies no (lineHolders[p, t] + cycleHolders[p, t] + holdingHolders[p, t])
    }
}
check soak_sys_poolLatticeGlobal for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 0

// ── the companion finders: a held pool and a second attach naming it, one per ordered pair of kinds ──────────────
// The second attach is an occurrence naming the pool, committed or refused; in a world where the premise holds it is
// refused. A same-kind pair excludes the attach's own subject from the holders.
pred receiveOn[o: ReceiveLineOcc, p: InventoryPool]             { p in resolve[o.pool] }
pred startProcessingOn[o: StartProcessingOcc, p: InventoryPool] { p in resolve[o.pool] }
pred startProductionOn[o: StartProductionOcc, p: InventoryPool] { p in resolve[o.holding] }
pred attachOn[o: AttachOcc, p: InventoryPool] {
  o.contribution in ExternalContribution and p in resolve[o.contribution.cPool]
}
run soak_lat_line_then_line {
  receivingPoolGenesis
  some p: InventoryPool, o: ReceiveLineOcc | receiveOn[o, p] and some (lineHolders[p, o.tick] - o.subject)
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1
run soak_lat_line_then_cycle {
  receivingPoolGenesis
  some p: InventoryPool, o: StartProcessingOcc | startProcessingOn[o, p] and some lineHolders[p, o.tick]
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1
run soak_lat_line_then_holding {
  receivingPoolGenesis
  some p: InventoryPool, o: StartProductionOcc | startProductionOn[o, p] and some lineHolders[p, o.tick]
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1
run soak_lat_line_then_contribution {
  receivingPoolGenesis
  some p: InventoryPool, o: AttachOcc | attachOn[o, p] and some lineHolders[p, o.tick]
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1
run soak_lat_cycle_then_line {
  receivingPoolGenesis
  some p: InventoryPool, o: ReceiveLineOcc | receiveOn[o, p] and some cycleHolders[p, o.tick]
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1
run soak_lat_cycle_then_cycle {
  receivingPoolGenesis
  some p: InventoryPool, o: StartProcessingOcc | startProcessingOn[o, p] and some (cycleHolders[p, o.tick] - o.subject)
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1
run soak_lat_cycle_then_holding {
  receivingPoolGenesis
  some p: InventoryPool, o: StartProductionOcc | startProductionOn[o, p] and some cycleHolders[p, o.tick]
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1
run soak_lat_cycle_then_contribution {
  receivingPoolGenesis
  some p: InventoryPool, o: AttachOcc | attachOn[o, p] and some cycleHolders[p, o.tick]
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1
run soak_lat_holding_then_line {
  receivingPoolGenesis
  some p: InventoryPool, o: ReceiveLineOcc | receiveOn[o, p] and some holdingHolders[p, o.tick]
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1
run soak_lat_holding_then_cycle {
  receivingPoolGenesis
  some p: InventoryPool, o: StartProcessingOcc | startProcessingOn[o, p] and some holdingHolders[p, o.tick]
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1
run soak_lat_holding_then_holding {
  receivingPoolGenesis
  some p: InventoryPool, o: StartProductionOcc | startProductionOn[o, p] and some (holdingHolders[p, o.tick] - o.subject)
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1
run soak_lat_holding_then_contribution {
  receivingPoolGenesis
  some p: InventoryPool, o: AttachOcc | attachOn[o, p] and some holdingHolders[p, o.tick]
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1
run soak_lat_contribution_then_line {
  receivingPoolGenesis
  some p: InventoryPool, o: ReceiveLineOcc | receiveOn[o, p] and some contributionOwners[p, o.tick]
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1
run soak_lat_contribution_then_cycle {
  receivingPoolGenesis
  some p: InventoryPool, o: StartProcessingOcc | startProcessingOn[o, p] and some contributionOwners[p, o.tick]
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1
run soak_lat_contribution_then_holding {
  receivingPoolGenesis
  some p: InventoryPool, o: StartProductionOcc | startProductionOn[o, p] and some contributionOwners[p, o.tick]
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1
run soak_lat_contribution_then_contribution {
  receivingPoolGenesis
  some p: InventoryPool, o: AttachOcc | attachOn[o, p] and some (contributionOwners[p, o.tick] - o.subject)
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 3 DemandItem, 0 ProductionDelivery,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 3 Contribution, 1 Placement,
      10 Occurrence, 15 EntityId, 10 Tick, 14 Snapshot, 2 Note, 2 Reference, 3 ContributionId expect 1

// CREATED-ONLY SLICE (DT-023 Q-D / DT-024, closing pass 7c): reference-data version
// dynamics are proven WIDE in soak/tests/reference_data_dynamics — this root reads
// reference data only through the pin/liveness API, so each subject carries exactly its
// Create and no Update/Delete atoms inflate the census (the lemma-then-slice retune).
fact CreatedOnlySlice {
  ItemOcc in CreateItemOcc
  BaOcc in CreateBaOcc
  StaffOcc in CreateStaffOcc
}
