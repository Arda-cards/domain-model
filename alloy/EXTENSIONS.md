# Alloy extensions of the Dafny reference model

> Status: DRAFT for the resulting model version (TN-003, approved by MP 2026-11-05; the Alloy cut follows the Dafny cut,
> DT-015). Written by SAMWISE, 2026-11-05. This file is the list the Dafny tree's `// Alloy extension:` comments point at.

Since MP's ruling of 2026-11-04 the Dafny tree (`dafny-domain`) is the reference model. This Alloy tree REFLECTS it, module for
module, and adds the **extensions** below: the verifications Dafny's tools cannot do, each tied to the Dafny lemma or module it
refines. A root that is not an extension and not teaching material is retired when the Alloy cut lands.

## The three extension classes (TN-001 §5, MP's point 4.2)

| Class | What Alloy does that Dafny cannot | Kept as |
| --- | --- | --- |
| 1. Instance finding | A `run` finds an instance nobody wrote: the solver exhibits a history that satisfies a predicate at a scope, where a Dafny `{:test}` is a hand-written trace | every `run` of a reflecting root, as the FINDER behind the Dafny witness of the same name |
| 2. Bounded counter-example search | A `check` under a scope explores every instance up to the bound before a proof is attempted, and an inductive slice (the E7 ladder) finds the seeded state a step lemma would reject | the soak slices TN-001 §12.1 names; a `check` on a law whose Dafny proof is DEFERRED (F-28) or on an S-07-type property over worlds no operation produced |
| 3. Scenario traces | A `run` as a GENERATOR of histories for runtime testing (O-05), replayed as Dafny witnesses | the generator roots, when O-05 starts; none today |

Everything else a root contains, every `check` of a law Dafny proves unboundedly, is RETIRED: it is evidence Dafny supersedes.

## Rules of a kept root

1. Its header names the Dafny module it reflects: `// Reflects dafny-domain src/<path>.dfy`.
   A soak root, which refines lemmas and reflects no single module, names them instead:
   `// Refines Dafny: <Module>.<Lemma>`, one line per lemma.
2. Each kept command names what it extends: `// Extension class 1: finder for <Module>.<Witness>` or
   `// Extension class 2: counter-example search for <Module>.<Lemma> (deferred | S-07)`.
3. The Dafny lemma's docstring carries the reverse pointer, `// Alloy extension: <root> <command>` (DT-015 D6).
4. `make check-alloy` runs the kept roots only.

## Inventory (MEASURED at `ca51fc7f0`; the per-command classification is the Alloy cut's work; step A's removals marked)

The counts are commands per root today. The class is the ROOT's default; a command may be reclassified in the cut.

| Root | runs | checks | Default classification |
| --- | --- | --- | --- |
| `conventions/call_first_saga/tests/call_first_saga.als` | 5 | 1 | teaching material: kept compiling, stale header (MP's confirmation 3) |
| `conventions/denormalized_observables/tests/denormalized_observables.als` | 3 | 2 | teaching material: kept compiling, stale header (MP's confirmation 3) |
| `conventions/inductive_invariant/tests/inductive_invariant.als` | 2 | 5 | teaching material: kept compiling, stale header (MP's confirmation 3) |
| `conventions/intent_log/tests/intent_log.als` | 14 | 7 | REMOVED in step A (2026-11-05): the intent chains left the tree (TN-003 row 2, DT-015 D4) |
| `conventions/metrics/tests/metrics.als` | 4 | 1 | teaching material: kept compiling, stale header (MP's confirmation 3) |
| `conventions/notification_convergence/tests/notification_convergence.als` | 4 | 2 | teaching material: kept compiling, stale header (MP's confirmation 3) |
| `conventions/pinning_freezing/tests/pinning_freezing.als` | 4 | 2 | teaching material: kept compiling, stale header (MP's confirmation 3) |
| `conventions/reason_precise_refusals/tests/reason_precise_refusals.als` | 7 | 2 | teaching material: kept compiling, stale header (MP's confirmation 3) |
| `meta/action/tests/action.als` | 5 | 6 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/action/tests/attributed.als` | 2 | 1 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/action/tests/stateful.als` | 5 | 0 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/intent_log/tests/intent_log.als` | 16 | 14 | REMOVED in step A (2026-11-05): the intent chains left the tree (TN-003 row 2, DT-015 D4) |
| `meta/keyed_value_algebra/tests/keyed_monoid.als` | 5 | 9 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/keyed_value_algebra/tests/keyed_order.als` | 4 | 6 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/keyed_value_algebra/tests/keyed_sum.als` | 2 | 4 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/keyed_value_algebra/tests/scalar_int.als` | 3 | 8 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/measurement/tests/measurement.als` | 4 | 4 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/model_time/tests/model_time.als` | 1 | 4 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/occurrence/tests/occurrence.als` | 5 | 5 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/occurrence/tests/timed.als` | 3 | 1 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/principal/tests/principal.als` | 1 | 3 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/profiles/tests/profiles.als` | 2 | 1 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/scalar/tests/scalar.als` | 1 | 3 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/state_machine/tests/machine.als` | 1 | 3 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/subject_log/tests/affirm.als` | 4 | 5 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/subject_log/tests/lifecycle.als` | 8 | 6 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/subject_log/tests/subject_log.als` | 5 | 6 | REFLECTS Dafny (step B, 2026-11-05: the duplicate-origin commands left with D3; the sibling witnesses arrived): runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/activation/tests/activation.als` | 10 | 5 | NEW in step B (2026-11-05): REFLECTS dafny-domain src/meta/tests/activation-tests.dfy; runs kept as finders (class 1), the negative controls among them; checks RETIRED (Dafny proves them) |
| `meta/tests/kernel.als` | 5 | 1 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/time/tests/duration.als` | 2 | 4 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `meta/time/tests/time.als` | 4 | 6 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `operations/demand/tests/integration/demand.als` | 3 | 2 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `operations/demand/tests/unit/delivery_retire.als` | 6 | 3 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `operations/demand/tests/unit/demand.als` | 42 | 19 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `operations/demand/tests/unit/demand_claim.als` | 11 | 7 | REMOVED in step A (2026-11-05): the intent chains left the tree (TN-003 row 2, DT-015 D4) |
| `operations/demand/tests/unit/demand_movement.als` | 10 | 3 | REMOVED in step A (2026-11-05): the intent chains left the tree (TN-003 row 2, DT-015 D4) |
| `operations/demand/tests/unit/demand_reset.als` | 2 | 0 | REPLACED in the TN-004 projection (2026-11-11) by `operations/demand/tests/unit/demand_quantity.als` (3 runs, 0 checks: the finders of `DemandTests.ContributionsSum`, class 1); the reset left the reference model with the stored intent (dafny-domain MD-076) |
| `procurement/order/tests/integration/order.als` | 3 | 2 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `procurement/order/tests/unit/order.als` | 51 | 16 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `procurement/order/tests/unit/order_received.als` | 3 | 1 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `receiving/receiver/tests/integration/receiver.als` | 2 | 0 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `receiving/receiver/tests/integration/receiver_arc.als` | 1 | 0 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `receiving/receiver/tests/unit/receiver.als` | 22 | 13 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `reference_data/business_affiliate/tests/business_affiliate.als` | 11 | 9 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `reference_data/item/tests/item.als` | 10 | 6 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `reference_data/item/tests/uom_collapse.als` | 2 | 4 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `reference_data/shared/tests/shared.als` | 4 | 2 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `reference_data/staff/tests/staff.als` | 5 | 4 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `resources/inventory_item/tests/integration/inventory_item.als` | 2 | 2 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `resources/inventory_item/tests/inventory_pool.als` | 18 | 6 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `resources/inventory_item/tests/metrics.als` | 8 | 3 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `resources/inventory_item/tests/pool_lifecycle.als` | 17 | 4 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `resources/inventory_item/tests/unit/inventory_item.als` | 39 | 14 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `resources/kanban_card/tests/cycle_occurrences.als` | 20 | 9 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `resources/kanban_card/tests/cycle_retire.als` | 19 | 6 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `resources/kanban_card/tests/kanban_card.als` | 17 | 2 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `resources/processing_network/tests/processing_network.als` | 5 | 1 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `shared/certainty/tests/certainty.als` | 3 | 3 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `shared/measurement/tests/quantity.als` | 4 | 4 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `shared/time/tests/calendar.als` | 3 | 4 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `shared/x731_state/tests/state.als` | 1 | 5 | REFLECTS Dafny: runs kept as finders (class 1); checks RETIRED (Dafny proves them) |
| `soak/lemmas/reference_data_dynamics.als` | 2 | 3 | EXTENSION class 2 (bounded induction and counter-example search) — KEPT: refines `BusinessAffiliatesContract.BaLifecycleShape`, `ItemsContract.ItemLifecycleShape`, and finds the witnesses `ItemTests.SoakDynamicsCompanion` and `ItemTests.SoakPinnedFloatingDiverge` |
| `soak/sliced/cycle_pool_inductive.als` | 2 | 7 | EXTENSION class 2 (bounded induction and counter-example search) — KEPT: refines `KanbanCardsContract.PoolExclusiveWhileLive` |
| `soak/sliced/demand_holding_inductive.als` | 2 | 7 | EXTENSION class 2 (bounded induction and counter-example search) — KEPT: refines `DemandsContract.HoldingExclusiveWhileLive`, `DemandsContract.HoldingNotACyclePool` |
| `soak/sliced/demand_soak.als` | 0 | 1 | EXTENSION class 2 (bounded induction and counter-example search) — KEPT: refines `DemandsContract.HoldingProvenance` |
| `soak/sliced/intent_log_arche_inductive.als` | 4 | 7 | REMOVED in step A (2026-11-05): the intent chains left the tree (TN-003 row 2, DT-015 D4) |
| `soak/sliced/intent_log_arche_movement_inductive.als` | 9 | 6 | REMOVED in step A (2026-11-05): the intent chains left the tree (TN-003 row 2, DT-015 D4) |
| `soak/sliced/intent_log_claim_inductive.als` | 2 | 4 | REMOVED in step A (2026-11-05): the intent chains left the tree (TN-003 row 2, DT-015 D4) |
| `soak/sliced/kanban_soak.als` | 0 | 1 | EXTENSION class 2 (bounded induction and counter-example search) — KEPT: refines `KanbanCardsContract.PoolProvenance` |
| `soak/sliced/order_frozen_outside_draft_inductive.als` | 2 | 4 | EXTENSION class 2 (bounded induction and counter-example search) — KEPT: refines `OrdersContract.FrozenOutsideDraftOrder`, `OrdersContract.FrozenOutsideDraftLine` |
| `soak/sliced/order_header_detail_inductive.als` | 2 | 4 | EXTENSION class 2 (bounded induction and counter-example search) — KEPT: refines `OrdersContract.HeaderDetailFrozen` |
| `soak/sliced/order_soak.als` | 0 | 0 | NO COMMAND: its four trace rows were RETIRED on MP's signoffs of 2026-08-28 and 2026-09-02, superseded by the four order rungs; the file is kept as their record |
| `soak/sliced/order_supplier_binding_inductive.als` | 2 | 4 | EXTENSION class 2 (bounded induction and counter-example search) — KEPT: refines `OrdersContract.SupplierBindingFrozen` |
| `soak/sliced/order_terminal_closure_inductive.als` | 2 | 4 | EXTENSION class 2 (bounded induction and counter-example search) — KEPT: refines `OrdersContract.OrderTerminalClosure` |
| `soak/sliced/receiver_captured_facts_inductive.als` | 2 | 4 | EXTENSION class 2 (bounded induction and counter-example search) — KEPT: refines `ReceiversContract.CapturedFactsFrozen` |
| `soak/sliced/receiver_pool_inductive.als` | 2 | 5 | EXTENSION class 2 (bounded induction and counter-example search) — KEPT: refines `ReceiversContract.LinePoolProvenance`, `ReceiversContract.LinesPoolLoneHolder`, `ReceiversContract.LineCyclePoolDisjoint`, `ReceiversContract.LineDemandPoolDisjoint` |
| `soak/sliced/receiving_soak.als` | 0 | 0 | NO COMMAND: its two trace rows were RETIRED on MP's signoffs of 2026-08-26 and 2026-08-28, superseded by the two receiver rungs; the file is kept as their record |
| `soak/sliced/zlattice_soak.als` | 0 | 1 | EXTENSION class 2 (bounded induction and counter-example search) — KEPT and EXTENDED (the project owner's ruling QA773, second question, option (i), 2026-11-12): refines `PoolLattice.PoolLatticeGlobal` with the FOUR holder kinds, in the four-conjunct form the gate check had before its retirement. Since the TN-004 projection: 16 runs, 1 check. The check's scope is 10 ticks and occurrences (it stated "10 Occurrence, 8 Tick", which held 8 occurrences and so no second holder on a held pool). The sixteen `soak_lat_*` finders, one per ordered pair of holder kinds, exhibit at the check's own scope a held pool and a second attach naming it, under the genesis premise: all sixteen found on 2026-11-13 (119 s to 286 s each). The check runs in a night window |
| `tests/pool_lattice.als` | 2 | 1 | REFLECTS Dafny: runs kept as finders (class 1). Since the TN-004 projection: 4 runs, 0 checks — the check `sys_poolLatticeGlobal` is RETIRED (the project owner's ruling QA761, Q1 (a), 2026-11-12: Dafny proves `PoolLattice.PoolLatticeGlobal` for every log), and the finders cover the four holder kinds |
| `tests/system.als` | 5 | 0 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |

## Retired with the cut, by design item of DT-015

- D3: `meta/subject_log/tests/subject_log.als`'s duplicate-origin commands (`unit_slog_archeSelfMintedReactionAllowed` and its pair), the pool's `RDuplicateOrigin` witnesses in `resources/inventory_item/tests/inventory_pool.als`.
- D4: `meta/intent_log/`, `operations/demand/demand_claim.als`, `demand_movement.als`, their roots, `soak/sliced/intent_log_*`, `conventions/intent_log/`, `meta/examples/ex20_intent_log.als`.
- D5: `meta/bitemporal.als`, `shared/std/iof.als`.
- D1 to D3 (step B): `ArcheUnique`, `archeUniquePerSubject`, `archeDuplicate`, the pool's `RDuplicateOrigin` atom and arms; the activation module arrives (`meta/activation/activation.als`, NOT parametric on the service — see its header) and the nine log-owning modules adopt it.
- TN-003 row 9 (step C, MP's ruling Journal 193772): the second gate — `commit`, `CommitOnlyIfAdmitted`, `refusedAtCommit`, the commit half of `refusalReasons`, `commitAlwaysAccepts` and every adoption, `unit_action_commitRejected`.
- QA704 Q4 (a) (step D): the fourteen content facts are guard arms with the model's codes (`RStaffNameTaken`, `RRoleNotOwned`, `RSupplyNotOwned`, `RSupplierPinUnsound`, `RSupplierPinStale`, `RLicensePlateTaken`, `RSerialTaken`, `RItemPinStale`, `RReversalUnlawful`, `RWrongItem` at StartProduction, `RVendorPinUnsound`, `RVendorPinStale`, `RAssigneePinStale`, `RCarrierPinUnsound`, `RCarrierPinStale`); the laws are theorems over committed history, checked in the roots. QA704 Q3 (a): `demand_reset.als` KEPT as a class-2 extension of `ResetSnapsToSum` (confined for the solver budget). S-05: the in-range premise and the bounded theorem `unit_invmet_usableNonNegativeInRange` (class 2) beside the boundary witness.

## Retired with the TN-004 projection

- QA761, Q1 (a) (the project owner, 2026-11-12): `tests/pool_lattice.als`'s `sys_poolLatticeGlobal`, the bounded check of the whole-system pool-lattice row, under this file's rule: Dafny proves the law for every log (`PoolLattice.PoolLatticeGlobal`). Its last verdict, with three holder kinds, was UNSAT in 8,475 s. The root keeps four finders with the four holder kinds (`sys_poolLatticeCompanion`, `sys_poolAtRestWitness`, `sys_poolContributionHolder`, `sys_poolContributionReleasedAtRest`). The soak-tier copy, `soak/sliced/zlattice_soak.als`'s `soak_sys_poolLatticeGlobal`, is NOT covered by that ruling: it still states three kinds and its fate is open.
- QA779, option (a) (the project owner, 2026-11-12): the five bounded checks the projection had added, each of a law Dafny proves for every log, under this file's rule: `unit_dem_contract_holdersReleasedAtComplete`, `unit_dem_contract_completedItemsPlaced`, `unit_dem_contract_contributionFrom`, `unit_dem_contract_contributionPoolExclusiveWhileLive` (the demand's unit root) and `unit_rcv_contract_lineContributionPoolDisjoint` (the receiver's). Their last verdicts, at 8 and 9 occurrences: `holdersReleasedAtComplete`, `completedItemsPlaced` and `contributionFrom` held (25 s, 199 s and 318 s); `contributionPoolExclusiveWhileLive` had no verdict in 600 s; the receiver's was never run. The five predicates stay conjuncts of their modules' `guarantees`, on the strength of the Dafny lemmas (`HoldersReleasedAtComplete`, `CompletedItemsPlaced`, `ContributionFrom`, `ContributionPoolExclusiveWhileLive`, `LineContributionPoolDisjoint`).
- With the reference model (dafny-domain MD-084): the demand's `completeRequiresDistributed` and `completeRequiresRetiredHolding` with their two checks, and the finder `unit_dem_undistributedRefused` with the reason `RUndistributed`.

## Open

- The TN-004 projection (dafny-domain MD-076 to MD-087; 2026-11-11): the demand's roots gain the finders of the eighteen new Dafny witnesses and the lattice root the fourth holder's two (class 1). DONE in the projection; its five added checks are under "Retired with the TN-004 projection".
- OQ-1 (DT-015): RULED, QA708 (a) with the activation atom standing for `ActId` (MP, 2026-11-05); taken verbatim in step B.
- QA704 Q2 (b): DONE at `bb7570a` — `RNoSuchPool` (declared in `inventory_pool.als`, `poolLiveAt`/`namedPoolLive`) at StartProduction, CreateDelivery and RecordProduction (demand) and at StartProcessing (kanban), reading A of dafny-domain #33: a holding retired between two deliveries refuses the second `Deliver` whole; witnesses `unit_dem_startProductionNoSuchPoolRefused`, `unit_dem_recordProductionHoldingRetiredRefused`, `unit_dem_createDeliveryHoldingRetiredRefused`, `unit_cyr_startProcessingNoSuchPoolRefused`; theorems `unit_dem_startedHoldingLive`, `unit_dem_recordedHoldingLive`, `unit_cyr_startedPoolLive`.
- MF-004 (dafny-domain #32's bot finding, #33's remedy): `RAttributionStarted` on the receiver's line-side attach (`appendAttributionViol`, `addLineViol`) at `4c29334`; the pairing fact stays, `unit_rcv_lineAttachAgreesWithPartner` checks it no longer excludes what the partner refuses.
- The per-command classification of the 300-odd `check` commands, root by root, with the Dafny lemma named for each kept one. RULED: QA779, option (a) (the project owner, 2026-11-12): every unit-root `check` of a law Dafny proves is retired, the finders stay, and each kept check is named here with its class. Measured before the ruling: of the 65 contract checks of the demand's, the order's, the inventory item's and the receiver's unit roots, 12 found no instance of their scenario at their scope and 2 more only half of it. The classification is its own change, after the TN-004 projection.
- The three roots the container cannot finish (`receiving/receiver/tests/integration/receiver.als`, `operations/demand/tests/integration/demand.als`, `receiving/receiver/tests/unit/receiver.als`) run in the next night window on the dedicated machine (HARRY-TUTTLE's slot, requested 2026-11-05 14:3xZ); the PR opens `heavy-cone` citing the container runs and says which roots the window still owes.
