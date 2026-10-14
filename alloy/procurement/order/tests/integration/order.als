module procurement/order/tests/integration/order

open procurement/order/order_implementation
open procurement/order/order_contracts
open operations/demand/demand_implementation                        // the demand stack for REAL
open reference_data/item/item_implementation
open reference_data/business_affiliate/business_affiliate_implementation
open resources/processing_network/processing_network_implementation
open resources/kanban_card/kanban_card_implementation

// (The SupplierReference CLOSURE fact DIED at DT-023 cut 7b: the handle dissolved into typed
// BA version pins — no orphan-closure obligation exists for typed occurrence references.)

/*
 * INTEGRATION suite for the order module (DT-018/DT-017): the two order logs composed with the
 * REAL demand implementation (chaining + guards + effects) and the real lower stacks. Gate
 * tier: a joint loads witness, the O2 Submit arc down the real ladder (cycle legs stay empty —
 * 0 CardCycle keeps the cone within budget; the demand↔kanban legs are demand's own
 * integration suite), the cancel-returns-to-queue arc, and re-discharge of two key laws on the
 * composed stack.
 */

// ── joint loads: the composed stack is satisfiable; refs resolve across the layers ──────────────
run int_ord_loads {
  some a: AddLineOcc, d: DemandItem | {
    committed[a]
    resolve[a.demand] = d
    some resolve[a.subject.orderRef] & Order
    demandStatusAt[d, a.tick] = DS_RELEASED
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 10 EntityId, 10 Snapshot, 2 Note expect 1

// ── the O2 Submit arc on the REAL demand log: demand Create → Release (real chaining/effects),
// order AddLine attaches the RELEASED item, demand StartProduction (the saga's first leg — its
// REAL gate holds vacuously with no member cycles), then Submit commits on the C/OP gate. ──────
run int_ord_submitArc {
  some ord: Order, d: DemandItem,
       dc: CreateDemandOcc, dr: ReleaseOcc, dsp: StartProductionOcc,
       a: AddLineOcc, s: SubmitOcc | {
    dc.subject = d and dr.subject = d and dsp.subject = d
    parentOf[a.subject] = ord and s.subject = ord
    committed[dc] and committed[dr] and committed[dsp] and committed[a] and committed[s]
    resolve[a.demand] = d
    precedes[dc.tick, dr.tick] and precedes[dr.tick, a.tick]
    precedes[a.tick, dsp.tick] and precedes[dsp.tick, s.tick]
    orderStatusAt[ord, s.tick] = OS_SUBMITTED
    demandStatusAt[d, s.tick] = DS_IN_PROCESS
    d in servicedOf[ord, s.tick]
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      12 Tick, 14 EntityId, 14 Snapshot, 9 Occurrence, 2 Note expect 1
      // census +2 EntityId / +2 Occurrence at DT-023 cut 8 (mirrors unit_ord_buildAndSubmit):
      // Submit requires a LINKED vendor, so the arc carries the BA Create fixture (PDEV-241 re-base)

// ── the cancel arc on the real stack: the hold dies with the order; the item is STILL RELEASED
// on its own (sovereign) log and back in the queue. ─────────────────────────────────────────────
run int_ord_cancelReturnsToQueue {
  some c: CancelOrderOcc, d: DemandItem, l: OrderLine | {
    committed[c]
    parentOf[l] = c.subject
    d in servicedAt[l, c.tick]
    no holdingLineOf[d, c.tick]
    demandStatusAt[d, c.tick] = DS_RELEASED       // demand knew nothing of the order (O3)
  }
} for 7 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 Tick, 11 EntityId, 11 Snapshot, 2 Note expect 1

// ── law re-discharge on the composed stack ──────────────────────────────────────────────────────
assert int_ord_contract_demandIndivisible { demandIndivisible }
check int_ord_contract_demandIndivisible for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station, 2 Note expect 0

assert int_ord_contract_frozenOutsideDraft { frozenOutsideDraft }
check int_ord_contract_frozenOutsideDraft for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station, 2 Note expect 0
