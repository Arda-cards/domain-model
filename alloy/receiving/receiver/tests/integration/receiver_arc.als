module receiving/receiver/tests/integration/receiver_arc

open receiving/receiver/receiver_implementation
open receiving/receiver/receiver_contracts
open operations/demand/demand_implementation                 // REAL — the PD leg composes with demand's effects
open resources/kanban_card/kanban_card_mock                  // lean-root discipline: this arc reads no
open reference_data/item/item_mock                           //   cycle/item/station machinery (laws via mocks;
open resources/processing_network/processing_network_mock    //   the cut-5 solver-budget lesson)

// (The SupplierReference CLOSURE fact DIED at DT-023 cut 7b: the handle dissolved into typed
// BA version pins — no orphan-closure obligation exists for typed occurrence references.)

/*
 * DEDICATED integration root (DT-022 TQ-5, cut 6): the receive → PD.Create → RecordDelivery →
 * release arc END TO END against the REAL demand machinery — the distribute C/OP saga composed:
 * demand Create → Release → StartProduction (real chaining/effects; cycle legs vacuous), the
 * PD's CreateDelivery (ATOMIC with demand's RecordProduction — the same-module pairing fires
 * for real), then the line's own RecordDelivery close and the Release.
 *
 * SCOPING (honest): the ORDER module stays types-only in this cone (receiving never posts to
 * the order — the order-driven capture arc and the attribution fan-out are unit-tier
 * witnesses; composing order's real machinery would buy no new cross-module semantics for
 * THIS arc). Kanban/item/station ride their MOCKS (no machinery of theirs is exercised).
 */

run int_rcv_deliveryArc {
  some d: DemandItem, pd: ProductionDelivery,
       dc: CreateDemandOcc, dr: ReleaseOcc, dsp: StartProductionOcc, pc: CreateDeliveryOcc,
       rv: CreateReceiverOcc, al: AddReceivingLineOcc, rc: ReceiveLineOcc,
       rd: RecordDeliveryOcc, rl: ReleaseLineOcc | {
    dc.subject = d and dr.subject = d and dsp.subject = d
    pc.subject = pd and resolve[pd.demandRef] = d
    al.subject = rc.subject and rc.subject = rd.subject and rd.subject = rl.subject
    parentReceiverOf[al.subject] = rv.subject
    committed[dc] and committed[dr] and committed[dsp] and committed[pc]
    committed[rv] and committed[al] and committed[rc] and committed[rd] and committed[rl]
    resolve[rd.delivery] = pd
    precedes[dc.tick, dr.tick] and precedes[dr.tick, dsp.tick] and precedes[dsp.tick, pc.tick]
    precedes[rv.tick, al.tick] and precedes[al.tick, rc.tick]
    precedes[rc.tick, pc.tick] and precedes[pc.tick, rd.tick] and precedes[rd.tick, rl.tick]
    rlStatusAt[rl.subject, rl.tick] = RL_DISTRIBUTED
  }
} for 10 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem,
      1 ProductionDelivery, 0 CardCycle, 0 KanbanCard, 2 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      14 Tick, 18 EntityId, 14 Snapshot, 5 Quantity, 13 Occurrence, 2 Note expect 1
