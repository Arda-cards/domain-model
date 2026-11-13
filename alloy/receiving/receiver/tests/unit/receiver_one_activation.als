module receiving/receiver/tests/unit/receiver_one_activation
// Reflects dafny-domain src/receiving/receiver/tests/receiver-tests.dfy: SplitAttachPairRefused, SplitDetachPairRefused,
//   SplitReceivePairRefused and SplitSecondActualRefused (the reference model since MP's ruling of 2026-11-04; alloy/EXTENSIONS.md)

open receiving/receiver/receiver_implementation
open receiving/receiver/receiver_contracts
open operations/demand/demand_mock                            // demand as CONTRACT (DT-017)
open procurement/order/order_mock                             // order as CONTRACT (the OrderLine targets)
open reference_data/item/item_mock                            // lower layers as CONTRACT
open reference_data/business_affiliate/business_affiliate_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock
open resources/inventory_item/inventory_item_mock

/*
 * THE ONE-ACTIVATION LAW of the receiver's three same-module pairings (the project owner's ruling QA764, option (a),
 * 2026-11-12; dafny-domain MD-089, `ReceiversContract.LinePairsOneActivation`): a committed line-side row and its
 * committed attribution-side partner cite the same activation.
 *
 * DEDICATED ROOT: per pairing, a NEGATIVE CONTROL and its POSITIVE TWIN at one scope.
 *  - The control asks for a committed pair whose halves cite TWO activations, `expect 0`. Without the law it finds one.
 *  - The twin asks for the same pair under ONE activation, `expect 1`: the scope holds the pair, so the control can fail.
 * The attach has two line-side carriers here (a new line born with its attribution; an append to an existing line) where
 * the reference model has one: each has its control and twin. The last pair is the receive against TWO allocation keys
 * with only the second actual split: the law is about every actual, not the first.
 * A split pair needs two activations: the scopes count them among the occurrences.
 */

// ── the attach pairing, carrier 1: AddReceivingLine born with its attribution, with the AttachAttribution ────────────
run unit_rcv_addLineAttachOneActivation {
  some c: AddReceivingLineOcc, g: AttachAttributionOcc | {
    committed[c] and committed[g]
    c.attribution = g.subject.eId
    c.arche = g.arche
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 1 OrderAttribution, 0 Order, 1 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 Contribution, 0 Placement,
      8 Occurrence, 8 Tick, 10 EntityId, 9 Snapshot, 3 Quantity, 2 Note, 2 Reference expect 1

run unit_rcv_splitAddLineAttachRefused {
  some c: AddReceivingLineOcc, g: AttachAttributionOcc | {
    committed[c] and committed[g]
    c.attribution = g.subject.eId
    c.arche != g.arche
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 1 OrderAttribution, 0 Order, 1 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 Contribution, 0 Placement,
      8 Occurrence, 8 Tick, 10 EntityId, 9 Snapshot, 3 Quantity, 2 Note, 2 Reference expect 0

// ── the attach pairing, carrier 2: AppendAttribution on an existing line, with the AttachAttribution ─────────────────
run unit_rcv_appendAttachOneActivation {
  some c: AppendAttributionOcc, g: AttachAttributionOcc | {
    committed[c] and committed[g]
    c.attribution = g.subject.eId
    c.arche = g.arche
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 1 OrderAttribution, 0 Order, 1 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 Contribution, 0 Placement,
      10 Occurrence, 10 Tick, 10 EntityId, 11 Snapshot, 3 Quantity, 2 Note, 2 Reference expect 1

run unit_rcv_splitAppendAttachRefused {
  some c: AppendAttributionOcc, g: AttachAttributionOcc | {
    committed[c] and committed[g]
    c.attribution = g.subject.eId
    c.arche != g.arche
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 1 OrderAttribution, 0 Order, 1 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 Contribution, 0 Placement,
      10 Occurrence, 10 Tick, 10 EntityId, 11 Snapshot, 3 Quantity, 2 Note, 2 Reference expect 0

// ── the detach pairing: RemoveAttribution on the line, with the DetachAttribution ────────────────────────────────────
run unit_rcv_detachPairOneActivation {
  some c: RemoveAttributionOcc, g: DetachAttributionOcc | {
    committed[c] and committed[g]
    c.attribution = g.subject.eId
    c.arche = g.arche
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 1 OrderAttribution, 0 Order, 1 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 Contribution, 0 Placement,
      11 Occurrence, 11 Tick, 10 EntityId, 12 Snapshot, 3 Quantity, 2 Note, 2 Reference expect 1

run unit_rcv_splitDetachPairRefused {
  some c: RemoveAttributionOcc, g: DetachAttributionOcc | {
    committed[c] and committed[g]
    c.attribution = g.subject.eId
    c.arche != g.arche
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 1 OrderAttribution, 0 Order, 1 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 Contribution, 0 Placement,
      11 Occurrence, 11 Tick, 10 EntityId, 12 Snapshot, 3 Quantity, 2 Note, 2 Reference expect 0

// ── the receive pairing: ReceiveLine, with the RecordActual of one of its allocation keys ────────────────────────────
run unit_rcv_receivePairOneActivation {
  some r: ReceiveLineOcc, x: RecordActualOcc | {
    committed[r] and committed[x]
    x.subject.eId in r.allocation.Quantity and x.actual = (x.subject.eId).(r.allocation)
    x.arche = r.arche
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 1 OrderAttribution, 0 Order, 1 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 Contribution, 0 Placement,
      10 Occurrence, 10 Tick, 12 EntityId, 12 Snapshot, 4 Quantity, 2 Note, 2 Reference expect 1

run unit_rcv_splitReceivePairRefused {
  some r: ReceiveLineOcc, x: RecordActualOcc | {
    committed[r] and committed[x]
    x.subject.eId in r.allocation.Quantity and x.actual = (x.subject.eId).(r.allocation)
    x.arche != r.arche
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 1 OrderAttribution, 0 Order, 1 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 Contribution, 0 Placement,
      10 Occurrence, 10 Tick, 12 EntityId, 12 Snapshot, 4 Quantity, 2 Note, 2 Reference expect 0

// ── the receive against TWO allocation keys: the first actual under the receive's activation, the second split ───────
run unit_rcv_receiveTwoKeysOneActivation {
  some r: ReceiveLineOcc, x, y: RecordActualOcc | {
    committed[r] and committed[x] and committed[y] and x.subject != y.subject
    (x.subject.eId + y.subject.eId) in r.allocation.Quantity
    x.actual = (x.subject.eId).(r.allocation) and y.actual = (y.subject.eId).(r.allocation)
    x.arche = r.arche and y.arche = r.arche
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 2 OrderAttribution, 0 Order, 2 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 Contribution, 0 Placement,
      13 Occurrence, 13 Tick, 14 EntityId, 14 Snapshot, 4 Quantity, 2 Note, 2 Reference expect 1

run unit_rcv_splitSecondActualRefused {
  some r: ReceiveLineOcc, x, y: RecordActualOcc | {
    committed[r] and committed[x] and committed[y] and x.subject != y.subject
    (x.subject.eId + y.subject.eId) in r.allocation.Quantity
    x.actual = (x.subject.eId).(r.allocation) and y.actual = (y.subject.eId).(r.allocation)
    x.arche = r.arche and y.arche != r.arche
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 2 OrderAttribution, 0 Order, 2 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 Contribution, 0 Placement,
      13 Occurrence, 13 Tick, 14 EntityId, 14 Snapshot, 4 Quantity, 2 Note, 2 Reference expect 0
