module tests/pool_lattice
// Reflects dafny-domain src/system/tests/pool-lattice-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

/*
 * THE GLOBAL EXCLUSIVITY-LATTICE ROW (§8.5.3) — the whole-system pairwise-disjointness
 * check, CHECK-ONLY (no owning module, so it never joins any `guarantees`/mock). It
 * composes the three holder modules' CONTRACTS (their mocks): each module's own lattice
 * row is assumed (kanban `poolExclusiveWhileLive`; demand `holdingExclusiveWhileLive`;
 * receiving `linePoolExclusiveWhileLive` — the latter two premise-conditional), and this
 * root verifies the rows COMPOSE into global exclusivity under the one genesis premise —
 * a contract-composition validation, not an implementation discharge (those live in each
 * module's own tier).
 *
 * DEDICATED ROOT (solver-budget confinement — the demand_reset/order_received precedent):
 * `tests/system.als` composes the live-entity implementations and would inflate every
 * existing command with the receiving + demand + order cones; the global row rides its own
 * system-tier root over MOCKS instead.
 *
 * `receivingPoolGenesis` (the widest premise — its clauses cover every attach kind all
 * three rows mention) structurally implies `demandPoolGenesis`, so one antecedent serves.
 *
 * THE FOURTH HOLDER (TN-004; dafny-domain MD-086, DT-016 PR B): a live demand's EXTERNAL CONTRIBUTION holds its pool.
 * A contribution is a VALUE here, so two demands holding equal contributions hold ONE atom and a `lone` over
 * contribution atoms would not see two holders: the fourth kind is counted by its OWNERS (`contributionHoldsPool`) and
 * its rows are stated as pairwise exclusions, as dafny-domain's `PairExclusive` states them. The demand's row for it is
 * `contributionPoolExclusiveWhileLive`, the receiving one `lineContributionPoolDisjoint`.
 */

open receiving/receiver/receiver_mock
open operations/demand/demand_mock
open resources/kanban_card/kanban_card_mock
open reference_data/item/item_mock
open reference_data/business_affiliate/business_affiliate_mock
open resources/processing_network/processing_network_mock
open resources/inventory_item/inventory_item_mock

/** entityHolders — a pool's holders of the three ENTITY kinds at `t`: the lines holding it, the live cycles whose pool it
    is, the live demands whose holding it is. */
fun entityHolders[p: InventoryPool, t: Tick]: set (ReceivingLine + CardCycle + DemandItem) {
  { l: ReceivingLine | resolve[rlStateAt[l, t].sPool] = p }
  + { c: CardCycle | liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p }
  + { d: DemandItem | liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p }
}
/** contributionHoldsPool — the FOURTH holder kind (dafny-domain `HContribution`): the live demand `d` holds pool `p` at `t`
    through one of its external contributions. */
pred contributionHoldsPool[d: DemandItem, p: InventoryPool, t: Tick] {
  some c: ExternalContribution | contributionHolds[d, c, c.cPool, t] and resolve[c.cPool] = p
}

// Under the genesis premise, NO pool has two holders ACROSS ALL KINDS at any moment: the
// union of a pool's line holders, live cycle holders, and live demand holders is `lone`; and the
// fourth kind is exclusive pairwise — against itself (two demands; two contributions of one demand)
// and against the three entity kinds.
assert sys_poolLatticeGlobal {
  receivingPoolGenesis implies
    all t: Tick, p: InventoryPool | {
      lone ({ l: ReceivingLine | resolve[rlStateAt[l, t].sPool] = p }
            + { c: CardCycle | liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p }
            + { d: DemandItem | liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p })
      lone { d: DemandItem | contributionHoldsPool[d, p, t] }
      all d: DemandItem | lone { c: ExternalContribution | contributionHolds[d, c, c.cPool, t] and resolve[c.cPool] = p }
      (some d: DemandItem | contributionHoldsPool[d, p, t]) implies no entityHolders[p, t]
    }
}
check sys_poolLatticeGlobal for 5 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 2 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 2 DemandItem, 0 ProductionDelivery,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot, 2 Note, 2 Reference expect 0

// M2c (DT-020 §8.5.3/§8.2.1, SPEARHEAD-D1 A′-2): "AT REST" — a pool with NO live holder among
// the FOUR kinds this root composes (the fourth since TN-004: a live demand's external contribution). DERIVED here (never a stored pool-side state — a pool
// cannot know who holds it, the DAG requirement; `inventory_pool.als` carries the annotation,
// this root carries the reading since it is the one place all three holder kinds are visible).
pred atRestAt[p: InventoryPool, t: Tick] {
  no l: ReceivingLine | resolve[rlStateAt[l, t].sPool] = p
  no c: CardCycle | liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p
  no d: DemandItem | liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p
  no d: DemandItem | contributionHoldsPool[d, p, t]
}
// Anti-vacuity companion: a pool exists that is at rest (no holder), and — contrast — a pool
// held by a live cycle is NOT at rest (the derivation has real, non-trivial content both ways).
run sys_poolAtRestWitness {
  some p1, p2: InventoryPool, t: Tick, c: CardCycle | {
    atRestAt[p1, t]
    liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p2 and not atRestAt[p2, t]
  }
} for 8 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      1 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      12 EntityId, 9 Tick, 10 Snapshot, 4 Quantity, 9 Occurrence, 2 Note, 2 Reference expect 1

// The SAT companion (anti-vacuity): the premise + one holder of EACH kind, three distinct
// pools — the global reading has real content.
run sys_poolLatticeCompanion {
  receivingPoolGenesis
  some t: Tick, l: ReceivingLine, c: CardCycle, d: DemandItem, p1, p2, p3: InventoryPool | {
    p1 != p2 and p2 != p3 and p1 != p3
    resolve[rlStateAt[l, t].sPool] = p1
    liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p2
    liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p3
  }
} for 10 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      1 CardCycle, 1 KanbanCard, 0 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      16 EntityId, 10 Tick, 14 Snapshot, 4 Quantity, 10 Occurrence, 2 Note, 2 Reference expect 1

// ── the fourth holder's witnesses (TN-004; dafny-domain PoolLatticeTests, DT-016 PR B) ──────────────────────────────────────
// PoolLatticeTests.ContributionHolder: a live demand's external contribution holds a pool, ALONE on it (no holder of the
// three entity kinds), and the pool is therefore not at rest.
run sys_poolContributionHolder {
  receivingPoolGenesis
  some t: Tick, d: DemandItem, p: InventoryPool | {
    contributionHoldsPool[d, p, t]
    no entityHolders[p, t] and not atRestAt[p, t]
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      0 Receiver, 0 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 1 Contribution, 0 Placement,
      8 EntityId, 7 Tick, 8 Snapshot, 4 Quantity, 7 Occurrence, 2 Note, 2 Reference expect 1

// PoolLatticeTests.ContributionReleasedAtRest (QA738 (a)): a committed Cancel of the demand releases its external
// contribution's pool — held just before, at rest from the Cancel on (the demand's promise `holdersReleasedAtComplete`).
run sys_poolContributionReleasedAtRest {
  some cn: CancelOcc, p: InventoryPool, t: Tick | {
    committed[cn] and precedes[t, cn.tick]
    contributionHoldsPool[cn.subject, p, t]
    atRestAt[p, cn.tick]
  }
} for 6 but 2 RoleDetail, 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      0 Receiver, 0 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 1 KanbanCard, 0 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 1 Contribution, 0 Placement,
      8 EntityId, 8 Tick, 9 Snapshot, 4 Quantity, 8 Occurrence, 2 Note, 2 Reference expect 1
