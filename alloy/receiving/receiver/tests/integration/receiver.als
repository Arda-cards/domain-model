module receiving/receiver/tests/integration/receiver

open receiving/receiver/receiver_implementation
open receiving/receiver/receiver_contracts
open operations/demand/demand_implementation                 // REAL — the composed arc runs demand's effects
open resources/kanban_card/kanban_card_implementation        // REAL — and kanban's
open reference_data/item/item_mock                           // solver budget: the arc reads no item/station
open resources/processing_network/processing_network_mock    //   machinery (lean-root discipline)

// (The SupplierReference CLOSURE fact DIED at DT-023 cut 7b: the handle dissolved into typed
// BA version pins — no orphan-closure obligation exists for typed occurrence references.)

/*
 * INTEGRATION suite for the receiving module (DT-020 cut 4): the real receiving log composed
 * with the REAL demand + kanban stacks (item/station ride their mocks — solver
 * budget: the composed arc reads neither). Gate tier: the COMPOSED-ARC witnesses — joint
 * loads and the three-holder lattice companion against the REAL receiving + demand + kanban
 * machinery. The §8.5.3 lattice ROW discharges at the UNIT tier since cut 5 (kanban and
 * demand publish their pool-provenance laws, so the mocks tie record bindings to attach
 * payloads); at cut 4, before that publication, the row's discharge lived here — the
 * interim is recorded in knowledge-base/pool-lattice-genesis-premise.md.
 *
 * The ORDER module rides this cone TYPES-ONLY (receiving reads no order log); order-cone
 * value sigs are pinned to 0 throughout.
 */

// ── joint loads: the composed stack is satisfiable across all layers ────────────────────────────
run int_rcv_loads {
  some o: ReceiveLineOcc | {
    committed[o] and some o.pool
    some resolve[o.pool] & InventoryPool
    some rlPre[o].sExpectedItem
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      12 EntityId, 8 Tick, 10 Snapshot, 3 Quantity, 2 Note expect 1

// The composed three-holder arc (the S5 scenario as a REAL-machinery witness): the genesis
// premise HOLDS with a line holding its pool, a LIVE cycle holding a second, and a LIVE
// demand holding a third — the full call-first chains all the way down.
run int_rcv_latticeCompanion {
  receivingPoolGenesis
  some t: Tick, l: ReceivingLine, c: CardCycle, d: DemandItem, p1, p2, p3: InventoryPool | {
    p1 != p2 and p2 != p3 and p1 != p3
    resolve[rlStateAt[l, t].sPool] = p1
    liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p2
    liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p3
  }
} for 10 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      1 CardCycle, 1 KanbanCard, 1 InventoryItem, 3 InventoryPool, 1 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      16 EntityId, 12 Tick, 14 Snapshot, 4 Quantity, 12 Occurrence, 2 Note expect 1
