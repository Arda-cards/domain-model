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
| `operations/demand/tests/unit/demand_reset.als` | 2 | 0 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
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
| `soak/lemmas/reference_data_dynamics.als` | 2 | 3 | EXTENSION class 2 (bounded induction and counter-example search) — keep only where TN-001 §12.1 names it; else RETIRED |
| `soak/sliced/cycle_pool_inductive.als` | 2 | 7 | EXTENSION class 2 (bounded induction and counter-example search) — keep only where TN-001 §12.1 names it; else RETIRED |
| `soak/sliced/demand_holding_inductive.als` | 2 | 7 | EXTENSION class 2 (bounded induction and counter-example search) — keep only where TN-001 §12.1 names it; else RETIRED |
| `soak/sliced/demand_soak.als` | 0 | 1 | EXTENSION class 2 (bounded induction and counter-example search) — keep only where TN-001 §12.1 names it; else RETIRED |
| `soak/sliced/intent_log_arche_inductive.als` | 4 | 7 | REMOVED in step A (2026-11-05): the intent chains left the tree (TN-003 row 2, DT-015 D4) |
| `soak/sliced/intent_log_arche_movement_inductive.als` | 9 | 6 | REMOVED in step A (2026-11-05): the intent chains left the tree (TN-003 row 2, DT-015 D4) |
| `soak/sliced/intent_log_claim_inductive.als` | 2 | 4 | REMOVED in step A (2026-11-05): the intent chains left the tree (TN-003 row 2, DT-015 D4) |
| `soak/sliced/kanban_soak.als` | 0 | 1 | EXTENSION class 2 (bounded induction and counter-example search) — keep only where TN-001 §12.1 names it; else RETIRED |
| `soak/sliced/order_frozen_outside_draft_inductive.als` | 2 | 4 | EXTENSION class 2 (bounded induction and counter-example search) — keep only where TN-001 §12.1 names it; else RETIRED |
| `soak/sliced/order_header_detail_inductive.als` | 2 | 4 | EXTENSION class 2 (bounded induction and counter-example search) — keep only where TN-001 §12.1 names it; else RETIRED |
| `soak/sliced/order_supplier_binding_inductive.als` | 2 | 4 | EXTENSION class 2 (bounded induction and counter-example search) — keep only where TN-001 §12.1 names it; else RETIRED |
| `soak/sliced/order_terminal_closure_inductive.als` | 2 | 4 | EXTENSION class 2 (bounded induction and counter-example search) — keep only where TN-001 §12.1 names it; else RETIRED |
| `soak/sliced/receiver_captured_facts_inductive.als` | 2 | 4 | EXTENSION class 2 (bounded induction and counter-example search) — keep only where TN-001 §12.1 names it; else RETIRED |
| `soak/sliced/receiver_pool_inductive.als` | 2 | 5 | EXTENSION class 2 (bounded induction and counter-example search) — keep only where TN-001 §12.1 names it; else RETIRED |
| `soak/sliced/zlattice_soak.als` | 0 | 1 | EXTENSION class 2 (bounded induction and counter-example search) — keep only where TN-001 §12.1 names it; else RETIRED |
| `tests/pool_lattice.als` | 2 | 1 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |
| `tests/system.als` | 5 | 0 | REFLECTS Dafny: runs kept as finders (class 1); checks kept only for a deferred or S-07-type law, else RETIRED |

## Retired with the cut, by design item of DT-015

- D3: `meta/subject_log/tests/subject_log.als`'s duplicate-origin commands (`unit_slog_archeSelfMintedReactionAllowed` and its pair), the pool's `RDuplicateOrigin` witnesses in `resources/inventory_item/tests/inventory_pool.als`.
- D4: `meta/intent_log/`, `operations/demand/demand_claim.als`, `demand_movement.als`, their roots, `soak/sliced/intent_log_*`, `conventions/intent_log/`, `meta/examples/ex20_intent_log.als`.
- D5: `meta/bitemporal.als`, `shared/std/iof.als`.
- D1 to D3 (step B): `ArcheUnique`, `archeUniquePerSubject`, `archeDuplicate`, the pool's `RDuplicateOrigin` atom and arms; the activation module arrives (`meta/activation/activation.als`, NOT parametric on the service — see its header) and the nine log-owning modules adopt it.
- TN-003 row 9 (step C, MP's ruling Journal 193772): the second gate — `commit`, `CommitOnlyIfAdmitted`, `refusedAtCommit`, the commit half of `refusalReasons`, `commitAlwaysAccepts` and every adoption, `unit_action_commitRejected`.
- QA704 Q4 (a) (step D): the fourteen content facts are guard arms with the model's codes (`RStaffNameTaken`, `RRoleNotOwned`, `RSupplyNotOwned`, `RSupplierPinUnsound`, `RSupplierPinStale`, `RLicensePlateTaken`, `RSerialTaken`, `RItemPinStale`, `RReversalUnlawful`, `RWrongItem` at StartProduction, `RVendorPinUnsound`, `RVendorPinStale`, `RAssigneePinStale`, `RCarrierPinUnsound`, `RCarrierPinStale`); the laws are theorems over committed history, checked in the roots. QA704 Q3 (a): `demand_reset.als` KEPT as a class-2 extension of `ResetSnapsToSum` (confined for the solver budget). S-05: the in-range premise and the bounded theorem `unit_invmet_usableNonNegativeInRange` (class 2) beside the boundary witness.

## Open

- OQ-1 (DT-015): RULED, QA708 (a) with the activation atom standing for `ActId` (MP, 2026-11-05); taken verbatim in step B.
- QA704 Q2 (b): the `RNoSuchPool` arms at StartProduction and StartProcessing and the holding's liveness at RecordProduction mirror dafny-domain's PR 4 when it lands.
- The per-command classification of the 300-odd `check` commands: done root by root in the cut, with the Dafny lemma named for each kept one.
