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
2. A kept command is tied to the reference model in writing where it mirrors something there. The reference model's
   pointer check (`tools/check-pointer-parity.py` in `dafny-domain`) resolves every tie that is written.
   - **A finder that mirrors a Dafny witness** is named in that witness's docstring, in its `Alloy:` clause. Where
     the Dafny side does not name it, a comment directly above the command does:
     `// Extension class 1: finder for <Module>.<Witness>`.
   - **A finder with no Dafny witness** has no tie of its own. Its root's `Reflects` header (rule 1) ties it to the
     module. That is class 1 as defined above: an instance nobody wrote.
   - **A soak check (class 2):** the Dafny lemma's docstring carries rule 3's pointer, and the root names the lemma
     in its `Refines Dafny` marker (rule 1).
   - **A kept check that guards Alloy's own encoding** has no Dafny lemma that implies it. It is named, with the
     reason, in the table
     under "The checks, classified command by command" below.

   Measured at `2f78f3e`, over the commands outside the modeling cookbook (`meta/examples/`): of the 580 finders, at
   most 329 are named in a Dafny docstring at `dafny-domain` `bedfb64fa`, and at most 390 at the head of its pull
   request 59 (`92066ce`). The rest have no tie of their own: their root's header (rule 1) is the tie, and the
   conventions' teaching roots carry none. No command carries the comment form at `2f78f3e`; the four integration
   refusal finders (`int_dem_cycleHeldRefused`, `int_dem_frozenRefused`, `int_ord_demandHeldRefused`,
   `int_ord_frozenRefused`) are the first.
3. The Dafny lemma's docstring carries the reverse pointer, `Alloy extension: <root> · <what>` (DT-015 D6). The
   `· <what>` part may be left out.
4. `make check-alloy` runs the kept roots only.

## Inventory (MEASURED at `ca51fc7f0`; the per-command classification is applied below; step A's removals marked)

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
| `operations/demand/tests/unit/demand_one_activation.als` | 4 | 0 | NEW with the one-activation law's mirror (2026-11-13; the project owner's ruling QA764, option (a)). REFLECTS Dafny's `SplitCreatePairRefused`, `SplitRevokePairRefused` and `DeliverUnderOneActivation`: per pairing a negative control (a committed pair under two activations, `expect 0`) and its positive twin at the same scope (class 1) |
| `procurement/order/tests/integration/order.als` | 3 | 2 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `procurement/order/tests/unit/order.als` | 51 | 16 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `procurement/order/tests/unit/order_received.als` | 3 | 1 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `receiving/receiver/tests/integration/receiver.als` | 2 | 0 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `receiving/receiver/tests/integration/receiver_arc.als` | 1 | 0 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `receiving/receiver/tests/unit/receiver.als` | 22 | 13 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `receiving/receiver/tests/unit/receiver_one_activation.als` | 10 | 0 | NEW with the one-activation law's mirror (2026-11-13; the project owner's ruling QA764, option (a)). REFLECTS Dafny's `SplitAttachPairRefused`, `SplitDetachPairRefused`, `SplitReceivePairRefused` and `SplitSecondActualRefused`: per pairing a negative control and its positive twin at the same scope (class 1); the attach has its two Alloy carriers |
| `reference_data/business_affiliate/tests/business_affiliate.als` | 11 | 9 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `reference_data/item/tests/item.als` | 10 | 6 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `reference_data/item/tests/mock.als` | 2 | 0 | NEW (MPBOT-399, 2026-11-15): REFLECTS dafny-domain src/reference-data/item/item-contract.dfy (`SupplierPinsSound` over `RowSupplies`); what a consumer of the item's MOCK may read; `supplierPinsSound` ranges over committed writes' payloads AND committed occurrences' records (`committedRowSupplies`); runs kept as finders (class 1): a control and the record-pin finder |
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

## The checks, classified command by command (applied 2026-11-16)

The project owner's rulings QA779, option (a) (2026-11-12), and QA808, option (c) (2026-11-16): a `check` of a law the
reference model proves is retired, and a check Dafny has no proof of is kept. An executed test is not a proof. The scope
is the 249 `check` commands outside `soak/`, `conventions/` and `meta/examples/`, as main stood at `2986f32`. The
13 checks of the modeling cookbook (`meta/examples/`, run by `make check-examples`, not by `make check-alloy`) are
teaching material, as the conventions are: they are neither retired nor in the table of kept checks.

The kept checks are none of the three classes above. They guard Alloy's own encoding: properties that Dafny cannot
state, need not prove, tests on one machine, assumes, or has no lemma for. Since the reading of 2026-11-18, 113 more are
kept for another reason: a Dafny lemma states the law, and it is not yet shown to cover every instance of the check's
root.

- **Retired, 90.** 86 are each a check of a law that a Dafny lemma proves, in a root whose instances satisfy the
  lemma's premises. Four are retired by a ruling of their own (the last item below). The record is
  [`RETIRED-CHECKS.md`](RETIRED-CHECKS.md): check by check, the lemma, where it is at a named Dafny revision, the
  premises it assumes, why its statement implies the check's property, and what in the Alloy model implies each
  premise.
  - The pairings were first made by the lemma's `Alloy:` pointer, by name, or by reading, and 211 commands were
    recorded as retired, under 210 names: one check, `unit_pool_membershipExclusive`, has two commands. On 2026-11-18
    each was read again, the check's text beside the lemma's statement, and each premise of each lemma was looked for
    in the Alloy model. Of the 210, 68 stand, 18 had their citation corrected, 120 were restored to the tree and are
    kept (below), and four are retired by a ruling of their own (the last item).
  - 86 left the tree with this classification.
  - Four left with the four integration finders that replace them, by a ruling of their own (QA787, second
    question, option (a)): `int_dem_contract_cycleIndivisible`, `int_dem_contract_frozenOutsideOpen`,
    `int_ord_contract_demandIndivisible` and `int_ord_contract_frozenOutsideDraft`. Their roots open a lower
    module by its types alone, so the rule of the reading would keep them; the ruling decides.
- **Kept, 159 commands under 158 names** (the check named above has two). The card for QA808 counted 36.
  - The kanban card's two print-machine checks were counted as retired there. They are kept, since Dafny decides
    them by an executed test, as it does the kit's machines.
  - The reading of 2026-11-18 restored 120:
    - five that restate a fact Dafny only assumes;
    - two that no lemma states;
    - 113 in a root that opens a lower module without its implementation facts: 75 in the five unit roots that
      give their lower modules as contract mocks, and 38 in eight roots that open one by its types alone.

| Why Dafny has no proof | Kept checks | Root |
| --- | --- | --- |
| **The arithmetic is Alloy's own** (8). They show that Alloy's bounded `Int` behaves as a ring. Dafny proves the same axioms of its unbounded scalar, so it says nothing of Alloy's integers. | `int_addAssoc`, `int_addComm`, `int_addId`, `int_addInv`, `int_distrib`, `int_mulComm`, `int_mulId`, `int_posClosed_bounded` | `meta/keyed_value_algebra/tests/scalar_int.als` |
| **True by construction in Dafny** (14). In Dafny each is a type or a function, with nothing to prove. In Alloy each is a relation that a wrong fact could break. | `unit_action_outcomesPartition`, `unit_action_refusalHasReason`, `unit_action_successNoReason`, `unit_action_prePostDomains`, `unit_action_prefixMonotone`, `unit_action_prefixOnlyCommitted` | `meta/action/tests/action.als` |
| | `unit_attr_oneActor` | `meta/action/tests/attributed.als` |
| | `unit_aff_refusalWritesNothing` | `meta/subject_log/tests/affirm.als` |
| | `unit_lc_refusalWritesNothing` | `meta/subject_log/tests/lifecycle.als` |
| | `unit_occ_archeTotal` | `meta/occurrence/tests/occurrence.als` |
| | `unit_act_originsAreSelfInitiated` | `meta/activation/tests/activation.als` |
| | `unit_duration_zeroIsMin` | `meta/time/tests/duration.als` |
| | `unit_time_endpointsUnique` | `meta/time/tests/time.als` |
| | `unit_meas_endpointsLone` | `meta/measurement/tests/measurement.als` |
| **Tested on each concrete state machine** (9). Reachability and live signals are properties of one machine. Dafny decides them by an executed test per machine, not by a lemma. | `unit_sm_allReachable`, `unit_sm_firedInto`, `unit_sm_liveSignals` | `meta/state_machine/tests/machine.als` |
| | `x731_admin_reachable`, `x731_op_reachable`, `x731_usage_reachable`, `x731_liveSignals` | `shared/x731_state/tests/state.als` |
| | `unit_kc_printReachable`, `unit_kc_printLiveSignals` | `resources/kanban_card/tests/kanban_card.als` |
| **A premise in Dafny** (7). Dafny assumes it, and no lemma establishes it. Alloy checks that its facts imply it. One sample per instant, in the measurement lemmas. | `unit_meas_oneSamplePerInstant` | `meta/measurement/tests/measurement.als` |
| Tenant isolation, in the kernel's well-formed universe. | `unit_shared_tenantIsolation` | `reference_data/shared/tests/shared.als` |
| Entity ids are keys (`Keyed`). The lemma `Kernel.EIdIsKey` concludes it only from that premise. | `unit_kernel_eIdIsKey` | `meta/tests/kernel.als` |
| Principal names are keys (`NamesUnique`). The lemma `Principal.NameIsKey` concludes it only from that premise. | `unit_principal_nameIsKey` | `meta/principal/tests/principal.als` |
| The X.731 interlocks (`ResourceInterlocks`). The lemma `X731State.X731Consistency` requires both interlocks and concludes the first. | `X731Consistency` | `shared/x731_state/tests/state.als` |
| One occurrence per tick (`OneOccurrencePerTick`). The lemma `Trace.TickIndexUnique` concludes it inside one log; across the logs of a world it is the premise `ServicesTicksDisjoint`. | `unit_occ_onePerTick` | `meta/occurrence/tests/occurrence.als` |
| A cited origin precedes the occurrence that cites it (`ArcheOriginPrecedes`). Dafny establishes it inside one service (`Activated`); across services it is the premise `CrossCallersPrecede`. | `unit_occ_archeOriginPrecedes` | `meta/occurrence/tests/occurrence.als` |
| **No Dafny lemma states it** (2). Every chain of citations reaches an origin. `Activation.TreeWalkNonIncreasing` and `Activation.NoProperCycle` state that a walk never goes forward and that only an origin loops; no lemma concludes that a walk reaches one. | `unit_act_walkEndsAtOrigin` | `meta/activation/tests/activation.als` |
| Scaling the zero value gives the zero value. The lemma `KeyedAlgebra.ScaleZeroValue` states it for `int` keys only. | `unit_alg_scaleZeroValue` | `meta/keyed_value_algebra/tests/keyed_monoid.als` |
| **True by construction in Dafny, in a domain module** (3). The state is a datatype and the effect a function, and the transfer composite takes one stamp. | `unit_ba_postHoldsExactlyTheWrittenVersions`, `unit_ba_statesWithEqualPayloadsAreEqual` | `reference_data/business_affiliate/tests/business_affiliate.als` |
| | `unit_pool_transferPairOneStamp` | `resources/inventory_item/tests/inventory_pool.als` |
| **True of the Alloy universe only** (1). The record-side wrong-item refusal never fires where ids are keys and pins are static. Dafny's witness `RecordWrongItem` shows it firing. | `unit_dem_recordProductionItemArmSubsumed` | `operations/demand/tests/unit/demand.als` |
| **The bounded theorem the Dafny tree names as an extension** (1; TN-001's row S-05). | `unit_invmet_usableNonNegativeInRange` | `resources/inventory_item/tests/metrics.als` |
| **The root opens a lower module without its implementation facts** (113). A Dafny lemma states each law, and the lemma is not yet shown to cover every instance of the root. In Dafny a lower state is always the `Effect` folded over a lower log. Such a root allows lower records that the chaining and effect facts would exclude, and it is not shown that every one is the state of some lower log. A follow-up in the project's plan (activity AC-04-03-02-31) reads each such root: what the checked module reads of the lower module, and whether that is fixed as in Dafny. As a contract mock (75), which keeps the lower occurrences and replaces the chaining and effect facts with the contract's `guarantees`. (19 in this root.) | `unit_dem_contract_cycleIndivisible`, `unit_dem_contract_frozenOutsideOpen`, `unit_dem_contract_attachRequiresAccepted`, `unit_dem_contract_removeRequiresShelved`, `unit_dem_contract_startProductionRequiresStarted`, `unit_dem_contract_distributeRequiresReady`, `unit_dem_contract_completeRequiresSettled`, `unit_dem_contract_withdrawnDetachReconciles`, `unit_dem_contract_terminalClosure`, `unit_dem_contract_holdingProvenance`, `unit_dem_contract_holdingExclusive`, `unit_dem_contract_createDeliveryGated`, `unit_dem_contract_deliveryTerminalRevoke`, `unit_dem_holdingPoolPinMatchesItem`, `unit_dem_nothingAfterRetire`, `unit_dem_contract_completeStampedAfterHolding`, `unit_dem_holdingPoolPinHolds`, `unit_dem_startedHoldingLive`, `unit_dem_recordedHoldingLive` | `operations/demand/tests/unit/demand.als` |
| (3 in this root.) | `unit_pdr_retireIsTombstone`, `unit_pdr_nothingAfterRetire`, `unit_pdr_noRecordedRefusalWithoutGenesis` | `operations/demand/tests/unit/delivery_retire.als` |
| (19 in this root.) | `unit_ord_contract_frozenOutsideDraft`, `unit_ord_contract_demandIndivisible`, `unit_ord_contract_attachRequiresReleased`, `unit_ord_contract_attachItemAgrees`, `unit_ord_contract_submitRequiresStarted`, `unit_ord_contract_receiptAccrues`, `unit_ord_contract_receiptReverses`, `unit_ord_contract_lineClosureByAct`, `unit_ord_contract_closeRequiresSettled`, `unit_ord_contract_supplierBindingFrozen`, `unit_ord_contract_orderTerminalClosure`, `unit_ord_contract_headerDetailFrozen`, `unit_ord_contract_priorityDefault`, `unit_ord_removeRequiresDetached`, `unit_ord_nothingAfterRetire`, `unit_ord_noRecordedRefusalWithoutGenesis`, `unit_ord_bindingPinCurrencyHolds`, `unit_ord_assigneePinCurrencyHolds`, `unit_ord_supplierBindingPinAgreesHolds` | `procurement/order/tests/unit/order.als` |
| (17 in this root.) | `unit_rcv_contract_linePoolProvenance`, `unit_rcv_contract_captureWindowFrozen`, `unit_rcv_contract_completeRequiresLinesFinalized`, `unit_rcv_contract_capturedFactsFrozen`, `unit_rcv_contract_receiveSameItemPool`, `unit_rcv_contract_receiveAllocationBounded`, `unit_rcv_contract_actualSetOnce`, `unit_rcv_contract_deliveriesAppendOnly`, `unit_rcv_contract_lineForwardMonotone`, `unit_rcv_contract_receiverTerminalComplete`, `unit_rcv_contract_linesPoolLoneHolder`, `unit_rcv_contract_lineCyclePoolDisjoint`, `unit_rcv_contract_lineDemandPoolDisjoint`, `unit_rcv_carrierPinCurrencyHolds`, `unit_rcv_lineItemPinCurrencyHolds`, `unit_rcv_receiverCarrierPinAgreesHolds`, `unit_rcv_lineAttachAgreesWithPartner` | `receiving/receiver/tests/unit/receiver.als` |
| (17 in this root.) | `unit_ii_contract_stateFunction`, `unit_ii_contract_liveHaveState`, `unit_ii_contract_bornLive`, `unit_ii_contract_closureIsTerminal`, `unit_ii_contract_touchesLiveness`, `unit_ii_contract_readBack`, `unit_occ_noCommittedOverdraw`, `unit_occ_noResurrection`, `unit_occ_terminalRetirement`, `unit_occ_splitConserves`, `unit_occ_mergeConserves`, `unit_occ_expiryNeverLengthens`, `unit_occ_sealedOnlyBySeal`, `unit_occ_committedUnitsValid`, `unit_occ_lpnUniqueAmongStarted`, `unit_occ_serialUniqueAmongStarted`, `unit_occ_itemPinCurrencyHolds` | `resources/inventory_item/tests/unit/inventory_item.als` |

| By its types alone, with neither its facts nor a mock (38). Without facts here: the affiliate. (7 in this root.) | `unit_item_supplyOwnership`, `unit_item_supplyPinCurrencyHolds`, `unit_item_eachConfigured`, `unit_item_toEachIdentity`, `unit_item_lifecycleShape`, `unit_item_nothingAfterRetire`, `unit_item_retireIsTombstone` | `reference_data/item/tests/item.als` |
| Without facts here: the affiliate, the item, the inventory item and the processing network. (9 in this root.) | `unit_cyc_oneLiveCyclePerCard`, `unit_cyc_forwardMonotone`, `unit_cyc_noPoolBeforeInProcess`, `unit_cyc_poolFrozenOnceAttached`, `unit_cyc_poolProvenance`, `unit_cyc_poolExclusiveWhileLive`, `unit_cyc_closureIsTerminal`, `unit_cyc_quantityFixedAtGenesis`, `unit_cyc_poolItemHomogeneous` | `resources/kanban_card/tests/cycle_occurrences.als` |
| Without facts here: the affiliate, the item, the inventory item and the processing network. (7 in this root.) | `unit_cyr_nothingAfterRetire`, `unit_cyr_abandonedIsWithdrawn`, `unit_cyr_closedBeforeSuccessorGenesis`, `unit_cyr_poolAttachedOnce`, `unit_cyr_startedPoolLive`, `unit_cyr_attachedOnceById`, `unit_cyr_noRecordedRefusalWithoutGenesis` | `resources/kanban_card/tests/cycle_retire.als` |
| Without facts here: the affiliate, the item and the inventory item. (5 in this root.) | `unit_pool_homogeneous`, `unit_pool_sameTenant`, `unit_pool_membershipExclusive`, `unit_pool_stampsMonotone`, `unit_pool_reversalDisciplineHolds` | `resources/inventory_item/tests/inventory_pool.als` |
| Without facts here: the affiliate, the item and the inventory item. (4 in this root.) | `unit_plc_nothingAfterRetire`, `unit_plc_affirmNeverCreatedIsNotClosed`, `unit_plc_affirmIsInert`, `unit_plc_noRecordedRefusalWithoutGenesis` | `resources/inventory_item/tests/pool_lifecycle.als` |
| Without facts here: the affiliate and the item. (3 in this root.) | `unit_invmet_partitionAdditivity`, `unit_invmet_quietPeriodRepeats`, `unit_invmet_frameworkMatchesLog` | `resources/inventory_item/tests/metrics.als` |
| Without facts here: the affiliate. (2 in this root.) | `int_ii_contract_stateFunction`, `int_ii_contract_closureIsTerminal` | `resources/inventory_item/tests/integration/inventory_item.als` |
| Without facts here: every domain module it reads. (1 in this root.) | `unit_ordr_receivedIsAccumulated` | `procurement/order/tests/unit/order_received.als` |
The Inventory table above keeps its counts as measured at the cut. A root's row there that reads "checks RETIRED" is now
exact, except for the roots this table names.

## Retired with the cut, by design item of DT-015

- D3: `meta/subject_log/tests/subject_log.als`'s duplicate-origin commands (`unit_slog_archeSelfMintedReactionAllowed` and its pair), the pool's `RDuplicateOrigin` witnesses in `resources/inventory_item/tests/inventory_pool.als`.
- D4: `meta/intent_log/`, `operations/demand/demand_claim.als`, `demand_movement.als`, their roots, `soak/sliced/intent_log_*`, `conventions/intent_log/`, `meta/examples/ex20_intent_log.als`.
- D5: `meta/bitemporal.als`, `shared/std/iof.als`.
- D1 to D3 (step B): `ArcheUnique`, `archeUniquePerSubject`, `archeDuplicate`, the pool's `RDuplicateOrigin` atom and arms; the activation module arrives (`meta/activation/activation.als`, NOT parametric on the service — see its header) and the nine log-owning modules adopt it.
- TN-003 row 9 (step C, MP's ruling Journal 193772): the second gate — `commit`, `CommitOnlyIfAdmitted`, `refusedAtCommit`, the commit half of `refusalReasons`, `commitAlwaysAccepts` and every adoption, `unit_action_commitRejected`.
- QA704 Q4 (a) (step D): the fourteen content facts are guard arms with the model's codes (`RStaffNameTaken`, `RRoleNotOwned`, `RSupplyNotOwned`, `RSupplierPinUnsound`, `RSupplierPinStale`, `RLicensePlateTaken`, `RSerialTaken`, `RItemPinStale`, `RReversalUnlawful`, `RWrongItem` at StartProduction, `RVendorPinUnsound`, `RVendorPinStale`, `RAssigneePinStale`, `RCarrierPinUnsound`, `RCarrierPinStale`); the laws are theorems over committed history, checked in the roots. QA704 Q3 (a): `demand_reset.als` KEPT as a class-2 extension of `ResetSnapsToSum` (confined for the solver budget). S-05: the in-range premise and the bounded theorem `unit_invmet_usableNonNegativeInRange` (class 2) beside the boundary witness.

## Retired with the TN-004 projection

- QA761, Q1 (a) (the project owner, 2026-11-12): `tests/pool_lattice.als`'s `sys_poolLatticeGlobal`, the bounded check of the whole-system pool-lattice row, under this file's rule: Dafny proves the law for every log (`PoolLattice.PoolLatticeGlobal`). Its last verdict, with three holder kinds, was UNSAT in 8,475 s. The root keeps four finders with the four holder kinds (`sys_poolLatticeCompanion`, `sys_poolAtRestWitness`, `sys_poolContributionHolder`, `sys_poolContributionReleasedAtRest`). The soak-tier copy, `soak/sliced/zlattice_soak.als`'s `soak_sys_poolLatticeGlobal`, is NOT retired: the project owner KEPT it and had it EXTENDED to the four holder kinds (ruling QA773, second question, option (i), 2026-11-12; its row in the inventory above).
- QA779, option (a) (the project owner, 2026-11-12): the five bounded checks the projection had added, each of a law Dafny proves for every log, under this file's rule: `unit_dem_contract_holdersReleasedAtComplete`, `unit_dem_contract_completedItemsPlaced`, `unit_dem_contract_contributionFrom`, `unit_dem_contract_contributionPoolExclusiveWhileLive` (the demand's unit root) and `unit_rcv_contract_lineContributionPoolDisjoint` (the receiver's). Their last verdicts, at 8 and 9 occurrences: `holdersReleasedAtComplete`, `completedItemsPlaced` and `contributionFrom` held (25 s, 199 s and 318 s); `contributionPoolExclusiveWhileLive` had no verdict in 600 s; the receiver's was never run. The five predicates stay conjuncts of their modules' `guarantees`, on the strength of the Dafny lemmas (`HoldersReleasedAtComplete`, `CompletedItemsPlaced`, `ContributionFrom`, `ContributionPoolExclusiveWhileLive`, `LineContributionPoolDisjoint`).
- With the reference model (dafny-domain MD-084): the demand's `completeRequiresDistributed` and `completeRequiresRetiredHolding` with their two checks, and the finder `unit_dem_undistributedRefused` with the reason `RUndistributed`.

## Open

- The TN-004 projection (dafny-domain MD-076 to MD-087; 2026-11-11): the demand's roots gain the finders of the eighteen new Dafny witnesses and the lattice root the fourth holder's two (class 1). DONE in the projection; its five added checks are under "Retired with the TN-004 projection". The demand's unit root also carries one twin and its control with no Dafny witness of their own, `unit_dem_affirmedPoolStaysFresh` and `unit_dem_affirmedOnlyPoolNotFreshRefused` (class 1): they guard this tree's transcription of `KC.PoolUsed`, which reads the pool's membership rows only, so an affirmed pool is still fresh. A third, `unit_dem_contributionKeyIsItsOwn`, guards the key's type: a contribution's key is a `ContributionId`, no entity's identity or reference.
- OQ-1 (DT-015): RULED, QA708 (a) with the activation atom standing for `ActId` (MP, 2026-11-05); taken verbatim in step B.
- QA704 Q2 (b): DONE at `bb7570a` — `RNoSuchPool` (declared in `inventory_pool.als`, `poolLiveAt`/`namedPoolLive`) at StartProduction, CreateDelivery and RecordProduction (demand) and at StartProcessing (kanban), reading A of dafny-domain #33: a holding retired between two deliveries refuses the second `Deliver` whole; witnesses `unit_dem_startProductionNoSuchPoolRefused`, `unit_dem_recordProductionHoldingRetiredRefused`, `unit_dem_createDeliveryHoldingRetiredRefused`, `unit_cyr_startProcessingNoSuchPoolRefused`; theorems `unit_dem_startedHoldingLive`, `unit_dem_recordedHoldingLive`, `unit_cyr_startedPoolLive`.
- MF-004 (dafny-domain #32's bot finding, #33's remedy): `RAttributionStarted` on the receiver's line-side attach (`appendAttributionViol`, `addLineViol`) at `4c29334`; the pairing fact stays, `unit_rcv_lineAttachAgreesWithPartner` checks it no longer excludes what the partner refuses.
- The per-command classification of the 300-odd `check` commands, root by root, with the Dafny lemma named for each kept one. RULED: QA779, option (a) (the project owner, 2026-11-12): every unit-root `check` of a law Dafny proves is retired, the finders stay, and each kept check is named here with its class. Measured before the ruling: of the 65 contract checks of the demand's, the order's, the inventory item's and the receiver's unit roots, 12 found no instance of their scenario at their scope and 2 more only half of it. The classification is its own change, after the TN-004 projection. DONE. The first classification, of 2026-11-16, retired 211 commands and kept 38; the reading of 2026-11-18 superseded those counts. The section "The checks, classified command by command" gives the scope and the present result. The kit's checks followed QA808, option (c).
- `int_dem_recollationAfterFailure` (`operations/demand/tests/integration/demand.als`): FOUND in 856 s at `36ea315` (2026-11-14, a day run), in its form with the twelve rows named and ordered (`41f277e`). Before that form it had no verdict: 4 hours at 15 occurrences (2026-11-06), where it could not have an instance (the arc counts 16), and 4 hours at 20 (the bound QA740 (c) set on paper) in the night window of 2026-11-13.
- QA807 (a) (the project owner, 2026-11-16: "Option (a) plus add an extended scope check in the nightly window to try to verify the pending ones"): four commands are NOT DECIDED at their present scope. They stay in the tree, and an extended run in a night window the project owner opens tries them again. None found a counterexample or was refuted. A fifth, `unit_dem_twoFreshHoldings`, was on this list until the night window of 2026-11-17 decided it; it is retired, and the next entry records it.
  - `soak_sys_poolLatticeGlobal` (`soak/sliced/zlattice_soak.als`), the check of the whole-system pool-lattice row over four holder kinds, at 10 ticks and occurrences: no verdict in 3 h 50 min (the window of 2026-11-13, at `c788153`) or in 7 h 45 min (2026-11-14, at `005a59b`). The law is proven for every log in the reference model (`PoolLattice.PoolLatticeGlobal`); its sixteen companion finders are found at this scope.
  - `soak_dem_holdingProvenance` (`soak/sliced/demand_soak.als`): no verdict in 2 h (2026-11-13) or in 4 h (2026-11-14, at `005a59b`). Its inductive rung is decided at `005a59b`; the law is proven in the reference model (`Demands.HoldingProvenance`).
  - `int_rcv_latticeCompanion` (`receiving/receiver/tests/integration/receiver.als`): no verdict in 4 h (2026-11-13, at its earlier scope) or in 6 h (2026-11-14, at `b4d017b`, after its re-size in `6aa5530`). The reference model's witness of the same history runs in every gate (`ReceiverTests.LatticeCompanion`).
  - `int_rcv_deliveryArc` (`receiving/receiver/tests/integration/receiver_arc.als`): still running after 3 h 36 min when the window of 2026-11-13 ended; no verdict in 6 h (2026-11-14, at `b4d017b`). The reference model's witness runs in every gate (`ReceiverTests.DeliveryArc`).
- QA819, question 1, option (A) (the project owner, 2026-11-17): `unit_dem_twoFreshHoldings` (`operations/demand/tests/unit/demand.als`), the witness of `holdingAttachedOnce`, is RETIRED. It was decided with no example at its scope: in its named-and-ordered form the solver answered UNSAT in 8,237 s (the night window of 2026-11-17, at main `2986f32`; CNF export, gimsatul, 2 threads), against its `expect 1`. The cause is not identified: by reading, no guard and no fact excludes the scenario, and its two siblings are found at `b6cdfc3`. Before that verdict it had none in 1,800 s at `005a59b` and `b4d017b`, nor in five day runs of its named-and-ordered forms (2026-11-15): 1,800 s at `b6cdfc3`, 1,800 s and 3,600 s at `b48b912`, 1,800 s at five pools (`a0d1762`), and the diagnostic at `72ede78` (evidence refs `jmpicnic-ag/two-fresh-holdings-*`). Dafny's `DemandTests.HoldingsAttachedOnce` witnesses the scenario in every gate, and the reference model proves the law (`DemandsContract.HoldingAttachedOnce`). What the retirement costs: `holdingAttachedOnce` now has neither a check nor a witness in this tree. The command's last text is in its root's history, at `80192da`. Its repair is ticketed: two variant runs, the finder without its pinned calls and the finder in the shape of Dafny's witness, with no window time until the project owner schedules them. The law's docstring in `operations/demand/demand_contracts.als` still names the finder as its witness; it is corrected with the next change to that file, because a comment there would put every root that opens the demand's contract into this change's gate.
- The three roots the container cannot finish (`receiving/receiver/tests/integration/receiver.als`, `operations/demand/tests/integration/demand.als`, `receiving/receiver/tests/unit/receiver.als`) run in the next night window on the dedicated machine (HARRY-TUTTLE's slot, requested 2026-11-05 14:3xZ); the PR opens `heavy-cone` citing the container runs and says which roots the window still owes.
