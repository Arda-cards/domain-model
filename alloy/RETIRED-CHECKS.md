# The retired checks, and the Dafny lemma that proves each law

This file is the record behind the classification in [`EXTENSIONS.md`](EXTENSIONS.md): for every `check` that was
retired, the lemma of the Dafny reference model (the repository `dafny-domain`) that proves the same law, where it is,
and what the lemma assumes. With it a retired obligation can be traced to its replacement without any other source.

## How to read it

- **The Dafny revision** is `ac608469423b3dad0614407337a3bb3fc2b77b1d` (`ac60846`, dafny-domain's main on 2026-11-15, when the matches were made).
  Each lemma is cited as `file:line` at that revision. Later revisions move the lines, not the names.
- **Premises** are the lemma's `requires` clauses at that revision, as written. `none` means the lemma has no
  `requires` clause. A premise such as `WellFormed(...)` is the model's well-formedness of the logs it is given: it
  holds of every log the model's own `Append` builds, which is the Dafny counterpart of an Alloy instance.
- **Matched by** says how the check and the lemma were paired, before each pair was read against the lemma's
  statement:
  - the lemma's own `Alloy:` pointer names the check (117 checks);
  - the names agree (62 checks);
  - by reading the two statements (32 checks).
- **A check with several rows** is a law that Dafny states in several lemmas: per module, or in parts.
- **The scope:** the `check` commands outside `soak/` and `conventions/`, as main stood at `2986f32`. The kept
  checks are listed in `EXTENSIONS.md`, each with its reason.

**Counts:** 211 retired checks, 270 check-and-lemma rows, 25 modules.

**Four of them are still in the tree** until the integration finders that replace them merge (the project owner's
ruling on card QA787, second question, option (a)): `int_dem_contract_cycleIndivisible`,
`int_dem_contract_frozenOutsideOpen`, `int_ord_contract_demandIndivisible` and `int_ord_contract_frozenOutsideDraft`.

## `meta`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_kernel_eIdIsKey` | `kernel.als` | `EIdIsKey` | `src/meta/kernel.dfy:85` | `Keyed(u) && a in u && b in u && u[a].eId == u[b].eId` | the lemma's own `Alloy:` pointer |

## `meta/activation`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_act_callersPrecede` | `activation.als` | `CiteNotAfter` | `src/meta/activation.dfy:366` | `WorldWellFormed(w) && InWorld(w, t)` | reading |
| `unit_act_effectsFollow` | `activation.als` | `ActivationPrecedes` | `src/meta/activation.dfy:188` | `Activated(alog, elog, lift) && i < \|elog\|` | reading |
| `unit_act_noProperCycle` | `activation.als` | `NoProperCycle` | `src/meta/activation.dfy:392` | `WorldWellFormed(w) && Walk(w, path) && \|path\| >= 2 && path[0] == path[\|path\| - 1]` | the name |
| `unit_act_walkEndsAtOrigin` | `activation.als` | `NoProperCycle` | `src/meta/activation.dfy:392` | `WorldWellFormed(w) && Walk(w, path) && \|path\| >= 2 && path[0] == path[\|path\| - 1]` | reading |
| `unit_act_walkEndsAtOrigin` | `activation.als` | `TreeWalkNonIncreasing` | `src/meta/activation.dfy:371` | `WorldWellFormed(w) && Walk(w, path) && k < \|path\|` | reading |

## `meta/keyed_value_algebra`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_alg_addAssociative` | `keyed_monoid.als` | `AddAssociative` | `src/meta/keyed-algebra.dfy:115` | none | the name |
| `unit_alg_addClosedNf` | `keyed_monoid.als` | `AddClosedNf` | `src/meta/keyed-algebra.dfy:88` | none | the name |
| `unit_alg_addCommutative` | `keyed_monoid.als` | `AddCommutative` | `src/meta/keyed-algebra.dfy:101` | none | the name |
| `unit_alg_addIdentity` | `keyed_monoid.als` | `AddIdentity` | `src/meta/keyed-algebra.dfy:108` | `Nf(a)` | the name |
| `unit_alg_addInverse` | `keyed_monoid.als` | `AddInverse` | `src/meta/keyed-algebra.dfy:126` | none | the name |
| `unit_alg_scaleDistribAdd` | `keyed_monoid.als` | `ScaleDistribAdd` | `src/meta/keyed-algebra.dfy:156` | none | the name |
| `unit_alg_scaleOneIdentity` | `keyed_monoid.als` | `ScaleOneIdentity` | `src/meta/keyed-algebra.dfy:139` | `Nf(a)` | the name |
| `unit_alg_scaleZeroScalar` | `keyed_monoid.als` | `ScaleZeroScalar` | `src/meta/keyed-algebra.dfy:135` | none | the name |
| `unit_alg_scaleZeroValue` | `keyed_monoid.als` | `ScaleZeroValue` | `src/meta/keyed-algebra.dfy:137` | none | the name |
| `unit_ord_lteAntisymmetric` | `keyed_order.als` | `LteAntisymmetric` | `src/meta/keyed-algebra.dfy:209` | `Nf(a) && Nf(b) && Lte(a, b) && Lte(b, a)` | the name |
| `unit_ord_lteReflexive` | `keyed_order.als` | `LteReflexive` | `src/meta/keyed-algebra.dfy:165` | none | the name |
| `unit_ord_lteTransitive` | `keyed_order.als` | `LteTransitive` | `src/meta/keyed-algebra.dfy:167` | `Lte(a, b) && Lte(b, c)` | the name |
| `unit_ord_positiveIsAboveZero` | `keyed_order.als` | `PositiveIsAboveZero` | `src/meta/keyed-algebra.dfy:215` | `Nf(a)` | the name |
| `unit_ord_semEqualIffLexical` | `keyed_order.als` | `SemEqualIffLexical` | `src/meta/keyed-algebra.dfy:246` | `Nf(a) && Nf(b)` | the name |
| `unit_ord_semUnequalImpliesDifferent` | `keyed_order.als` | `SemUnequalImpliesDifferent` | `src/meta/keyed-algebra.dfy:252` | `SemanticEq(a, b) == UNEQUAL` | the name |
| `unit_sum_baseIsVal` | `keyed_sum.als` | `BaseIsVal` | `src/meta/keyed-sum.dfy:46` | `\|vals\| > 0 && Nf(vals[0])` | the name |
| `unit_sum_cumNf` | `keyed_sum.als` | `SumNf` | `src/meta/keyed-sum.dfy:41` | none | reading |
| `unit_sum_stepFolds` | `keyed_sum.als` | `StepFolds` | `src/meta/keyed-sum.dfy:56` | `0 < i < \|vals\|` | the name |
| `unit_sum_telescope` | `keyed_sum.als` | `Telescope` | `src/meta/keyed-sum.dfy:77` | `0 < m < \|vals\|` | the name |

## `meta/measurement`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_meas_countMatches` | `measurement.als` | `CountMatches` | `src/meta/measurement.dfy:190` | none | the name |
| `unit_meas_lastIsSampled` | `measurement.als` | `LastIsSampled` | `src/meta/measurement.dfy:168` | `OneSamplePerInstant(ms) && MeasurementsIn(ms, s, p) != {}` | the lemma's own `Alloy:` pointer |

## `meta/model_time`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_mt_strict` | `model_time.als` | `AllLevels` | `src/shared/certainty/certainty.dfy:34` | none | the lemma's own `Alloy:` pointer |
| `unit_mt_total` | `model_time.als` | `SumNf` | `src/meta/keyed-sum.dfy:41` | none | the lemma's own `Alloy:` pointer |
| `unit_mt_total` | `model_time.als` | `Total` | `src/meta/model-time.dfy:29` | `a != b` | the lemma's own `Alloy:` pointer |
| `unit_mt_total` | `model_time.als` | `AppendWellFormed` | `src/meta/tests/trace-tests.dfy:82` | `WellFormed(log) && AllBefore(log, t)` | the lemma's own `Alloy:` pointer |
| `unit_mt_transitive` | `model_time.als` | `Transitive` | `src/meta/model-time.dfy:38` | `Precedes(a, b) && Precedes(b, c)` | the name |
| `unit_mt_vocabulary` | `model_time.als` | `Vocabulary` | `src/meta/model-time.dfy:43` | none | the name |

## `meta/occurrence`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_occ_archeNoProperCycle` | `occurrence.als` | `NoProperCycle` | `src/meta/activation.dfy:392` | `WorldWellFormed(w) && Walk(w, path) && \|path\| >= 2 && path[0] == path[\|path\| - 1]` | reading |
| `unit_occ_archeOriginPrecedes` | `occurrence.als` | `CiteNotAfter` | `src/meta/activation.dfy:366` | `WorldWellFormed(w) && InWorld(w, t)` | reading |
| `unit_occ_onePerTick` | `occurrence.als` | `TickIndexUnique` | `src/meta/trace.dfy:214` | `StrictTicks(log) && i < \|log\| && j < \|log\| && log[i].tick == log[j].tick` | reading |
| `unit_occ_total` | `occurrence.als` | `SumNf` | `src/meta/keyed-sum.dfy:41` | none | the lemma's own `Alloy:` pointer |
| `unit_occ_total` | `occurrence.als` | `Total` | `src/meta/model-time.dfy:29` | `a != b` | the lemma's own `Alloy:` pointer |
| `unit_occ_total` | `occurrence.als` | `AppendWellFormed` | `src/meta/tests/trace-tests.dfy:82` | `WellFormed(log) && AllBefore(log, t)` | the lemma's own `Alloy:` pointer |
| `unit_timed_alignedForbidsBackdating` | `timed.als` | `AlignedForbidsBackdating` | `src/meta/occurrence-timed.dfy:34` | `ClocksAligned(log, at) && i < j < \|log\| && at(log[i]).Some? && at(log[j]).Some?` | the lemma's own `Alloy:` pointer |

## `meta/principal`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_principal_nameIsKey` | `principal.als` | `NameIsKey` | `src/meta/principal.dfy:52` | `NamesUnique(ps) && i < \|ps\| && j < \|ps\| && ps[i].name == ps[j].name` | the name |
| `unit_principal_recoverable` | `principal.als` | `Recoverable` | `src/meta/principal.dfy:57` | `NamesUnique(ps) && i < \|ps\|` | the name |
| `unit_principal_resolvesAsEntity` | `principal.als` | `ResolvesAsEntity` | `src/meta/principal.dfy:47` | `Keyed(u) && p.entity.eId in u && u[p.entity.eId] == p.entity` | the lemma's own `Alloy:` pointer |

## `meta/profiles`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_prof_premisesInForce` | `profiles.als` | `DomainLogPremises` | `src/meta/profiles.dfy:41` | none | reading |

## `meta/scalar`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_scalar_addInverse` | `scalar.als` | `GroupAxioms` | `src/meta/scalar.dfy:35` | none | reading |
| `unit_scalar_distributes` | `scalar.als` | `RingAxioms` | `src/meta/scalar.dfy:42` | none | reading |
| `unit_scalar_zeroNeOne` | `scalar.als` | `RingAxioms` | `src/meta/scalar.dfy:42` | none | reading |

## `meta/subject_log`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_aff_lastTouchMoves` | `affirm.als` | `LastTouchMoves` | `src/meta/affirm.dfy:64` | `i < \|log\| && Committed(log[i])` | the name |
| `unit_aff_neverCommitsStale` | `affirm.als` | `NeverCommitsStale` | `src/meta/affirm.dfy:73` | `AffirmViol(prefix, shape, s, pre, affirmed, rNotCreated, rClosed, rStale) == {}` | the name |
| `unit_aff_nothingAfterRetire` | `affirm.als` | `BaNothingAfterRetire` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:264` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_aff_nothingAfterRetire` | `affirm.als` | `ItemNothingAfterRetire` | `src/reference-data/item/item-contract.dfy:278` | `WellFormed(log, ba) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_aff_nothingAfterRetire` | `affirm.als` | `StaffNothingAfterRetire` | `src/reference-data/staff/staff-contract.dfy:151` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_aff_recordUnchanged` | `affirm.als` | `StateUnchanged` | `src/meta/affirm.dfy:54` | `AffirmKeeps(effect, shape) && i < \|log\| && Committed(log[i]) && shape(log[i].kind) == Affirm && StateAt(log[..i], log[i].subject, effect).Some?` | reading |
| `unit_lc_createIsFirst` | `lifecycle.als` | `CreateIsFirst` | `src/meta/trace.dfy:497` | `ShapeAdmission(log, shape) && i < \|log\| && Committed(log[i]) && shape(log[i].kind) == Create` | the name |
| `unit_lc_mutateHasPre` | `lifecycle.als` | `MutateHasState` | `src/meta/trace.dfy:502` | `ShapeAdmission(log, shape) && i < \|log\| && Committed(log[i]) && shape(log[i].kind) != Create && shape(log[i].kind) != Affirm` | reading |
| `unit_lc_noRecordedRefusalWithoutGenesis` | `lifecycle.als` | `OrderNoRecordedRefusalWithoutGenesis` | `src/procurement/order/order-contract.dfy:791` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Recorded(olog, OShapeOf, i) && !Committed(olog[i])` | the lemma's own `Alloy:` pointer |
| `unit_lc_noRecordedRefusalWithoutGenesis` | `lifecycle.als` | `LineNoRecordedRefusalWithoutGenesis` | `src/procurement/order/order-contract.dfy:797` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Recorded(llog, LShapeOf, i) && !Committed(llog[i])` | the lemma's own `Alloy:` pointer |
| `unit_lc_noRecordedRefusalWithoutGenesis` | `lifecycle.als` | `CycleNoRecordedRefusalWithoutGenesis` | `src/resources/kanban-card/kanban-card-contract.dfy:491` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Recorded(log, ShapeOf, i) && !Committed(log[i])` | the lemma's own `Alloy:` pointer |
| `unit_lc_nothingAfterRetire` | `lifecycle.als` | `BaNothingAfterRetire` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:264` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_lc_nothingAfterRetire` | `lifecycle.als` | `ItemNothingAfterRetire` | `src/reference-data/item/item-contract.dfy:278` | `WellFormed(log, ba) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_lc_nothingAfterRetire` | `lifecycle.als` | `StaffNothingAfterRetire` | `src/reference-data/staff/staff-contract.dfy:151` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_lc_tombstone` | `lifecycle.als` | `RetireKeepsState` | `src/meta/trace.dfy:510` | `ShapeAdmission(log, shape) && Tombstone(effect, shape) && i < \|log\| && Committed(log[i]) && shape(log[i].kind) == Retire` | reading |
| `unit_slog_firstReadsNothing` | `subject_log.als` | `FirstReadsNothing` | `src/meta/tests/trace-tests.dfy:147` | `i < \|log\| && !StartedBefore(log[..i], log[i].subject)` | the name |
| `unit_slog_locf` | `subject_log.als` | `Locf` | `src/meta/tests/trace-tests.dfy:153` | `i < \|log\| && Committed(log[i])` | the name |
| `unit_slog_recordIsFunctionOnceStarted` | `subject_log.als` | `StateIffStarted` | `src/meta/trace.dfy:285` | none | reading |
| `unit_slog_refusalContributesNothing` | `subject_log.als` | `RefusalContributesNothing` | `src/meta/tests/trace-tests.dfy:159` | `i < \|log\| && Refused(log[i])` | the name |
| `unit_slog_threadIsCommitted` | `subject_log.als` | `ThreadIsCommitted` | `src/meta/tests/trace-tests.dfy:165` | `i < \|log\| && PreOf(log, i).Some?` | the name |

## `meta/time`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_duration_antisym` | `duration.als` | `DurationOrder` | `src/meta/time.dfy:160` | none | reading |
| `unit_duration_total` | `duration.als` | `SumNf` | `src/meta/keyed-sum.dfy:41` | none | the lemma's own `Alloy:` pointer |
| `unit_duration_total` | `duration.als` | `Total` | `src/meta/model-time.dfy:29` | `a != b` | the lemma's own `Alloy:` pointer |
| `unit_duration_total` | `duration.als` | `AppendWellFormed` | `src/meta/tests/trace-tests.dfy:82` | `WellFormed(log) && AllBefore(log, t)` | the lemma's own `Alloy:` pointer |
| `unit_duration_transitive` | `duration.als` | `DurationOrder` | `src/meta/time.dfy:160` | none | reading |
| `unit_time_elapsedWhenOrdered` | `time.als` | `ElapsedWhenOrdered` | `src/meta/time.dfy:153` | none | the name |
| `unit_time_nonEmptyHasEndpoints` | `time.als` | `NonEmptyHasEndpoints` | `src/meta/time.dfy:144` | `ts != {}` | the name |
| `unit_time_total` | `time.als` | `SumNf` | `src/meta/keyed-sum.dfy:41` | none | the lemma's own `Alloy:` pointer |
| `unit_time_total` | `time.als` | `Total` | `src/meta/model-time.dfy:29` | `a != b` | the lemma's own `Alloy:` pointer |
| `unit_time_total` | `time.als` | `AppendWellFormed` | `src/meta/tests/trace-tests.dfy:82` | `WellFormed(log) && AllBefore(log, t)` | the lemma's own `Alloy:` pointer |
| `unit_time_withinBounds` | `time.als` | `WithinBounds` | `src/meta/time.dfy:149` | none | the name |
| `unit_time_zeroAtPoint` | `time.als` | `ZeroAtPoint` | `src/meta/time.dfy:151` | none | the name |

## `operations/demand`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `int_dem_contract_cycleIndivisible` | `demand.als` | `CycleIndivisible` | `src/operations/demand/demand-contract.dfy:886` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && d1 in DemandOf(log, c) && d2 in DemandOf(log, c)` | the lemma's own `Alloy:` pointer |
| `int_dem_contract_frozenOutsideOpen` | `demand.als` | `FrozenOutsideOpen` | `src/operations/demand/demand-contract.dfy:894` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && IsMutator(log[i].kind)` | the lemma's own `Alloy:` pointer |
| `unit_pdr_noRecordedRefusalWithoutGenesis` | `delivery_retire.als` | `OrderNoRecordedRefusalWithoutGenesis` | `src/procurement/order/order-contract.dfy:791` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Recorded(olog, OShapeOf, i) && !Committed(olog[i])` | the lemma's own `Alloy:` pointer |
| `unit_pdr_noRecordedRefusalWithoutGenesis` | `delivery_retire.als` | `LineNoRecordedRefusalWithoutGenesis` | `src/procurement/order/order-contract.dfy:797` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Recorded(llog, LShapeOf, i) && !Committed(llog[i])` | the lemma's own `Alloy:` pointer |
| `unit_pdr_noRecordedRefusalWithoutGenesis` | `delivery_retire.als` | `CycleNoRecordedRefusalWithoutGenesis` | `src/resources/kanban-card/kanban-card-contract.dfy:491` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Recorded(log, ShapeOf, i) && !Committed(log[i])` | the lemma's own `Alloy:` pointer |
| `unit_pdr_nothingAfterRetire` | `delivery_retire.als` | `BaNothingAfterRetire` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:264` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_pdr_nothingAfterRetire` | `delivery_retire.als` | `ItemNothingAfterRetire` | `src/reference-data/item/item-contract.dfy:278` | `WellFormed(log, ba) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_pdr_nothingAfterRetire` | `delivery_retire.als` | `StaffNothingAfterRetire` | `src/reference-data/staff/staff-contract.dfy:151` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_pdr_retireIsTombstone` | `delivery_retire.als` | `DeliveryRetireIsTombstone` | `src/operations/demand/demand-contract.dfy:1258` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && j < \|pdlog\| && Committed(pdlog[j]) && pdlog[j].kind.RetireDelivery?` | reading |
| `unit_dem_contract_attachRequiresAccepted` | `demand.als` | `AttachRequiresAccepted` | `src/operations/demand/demand-contract.dfy:904` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && KeyedCycles(clog) && i < \|log\| && Committed(log[i]) && IsAttach(log[i].kind) && log[i].kind.c.CardContribution?`, and `c in CyclesNamed(PrefixBefore(clog, log[i].tick), log[i].kind.c.cycle)` | the lemma's own `Alloy:` pointer |
| `unit_dem_contract_completeRequiresSettled` | `demand.als` | `CompleteRequiresSettled` | `src/operations/demand/demand-contract.dfy:943` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Complete?`, and `c in AttachedLiveAt(log[..i], PrefixBefore(clog, log[i].tick), log[i].subject)` | the lemma's own `Alloy:` pointer |
| `unit_dem_contract_completeStampedAfterHolding` | `demand.als` | `CompleteStampedAfterHolding` | `src/operations/demand/demand-contract.dfy:952` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Complete?`, and `PreOf(log, i).Some? && PreOf(log, i).value.sHolding.Some?`, and `p in KC.PoolsNamed(PrefixBefore(plog, log[i].tick), PreOf(log, i).value.sHolding.value)` | the lemma's own `Alloy:` pointer |
| `unit_dem_contract_createDeliveryGated` | `demand.als` | `CreateDeliveryGated` | `src/operations/demand/demand-contract.dfy:995` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && KeyedDemands(log) && j < \|pdlog\| && Committed(pdlog[j]) && pdlog[j].kind.CreateDelivery?`, and `d in DemandsNamed(PrefixBefore(log, pdlog[j].tick), pdlog[j].subject.demandRef)` | the lemma's own `Alloy:` pointer |
| `unit_dem_contract_cycleIndivisible` | `demand.als` | `CycleIndivisible` | `src/operations/demand/demand-contract.dfy:886` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && d1 in DemandOf(log, c) && d2 in DemandOf(log, c)` | the lemma's own `Alloy:` pointer |
| `unit_dem_contract_deliveryTerminalRevoke` | `demand.als` | `DeliveryTerminalRevoke` | `src/operations/demand/demand-contract.dfy:1006` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && n1 <= n2 <= \|pdlog\| && DeliveryStatusAt(pdlog[..n1], pd) == Some(PD_REVOKED)` | the lemma's own `Alloy:` pointer |
| `unit_dem_contract_distributeRequiresReady` | `demand.als` | `DistributeRequiresReady` | `src/operations/demand/demand-contract.dfy:933` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Distribute? && m in log[i].kind.fills`, and `PreOf(log, i).Some? && m in PreOf(log, i).value.sContributions && PreOf(log, i).value.sContributions[m].CardContribution?`, and `c in CyclesNamed(PrefixBefore(clog, log[i].tick), PreOf(log, i).value.sContributions[m].cycle)` | the lemma's own `Alloy:` pointer |
| `unit_dem_contract_frozenOutsideOpen` | `demand.als` | `FrozenOutsideOpen` | `src/operations/demand/demand-contract.dfy:894` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && IsMutator(log[i].kind)` | the lemma's own `Alloy:` pointer |
| `unit_dem_contract_holdingExclusive` | `demand.als` | `HoldingExclusiveWhileLive` | `src/operations/demand/demand-contract.dfy:1061` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && DemandPoolGenesis(log, clog)`, and `LiveDemandAt(log, d1) && HoldingAt(log, d1) == Some(e) && LiveDemandAt(log, d2) && HoldingAt(log, d2) == Some(e)` | the lemma's own `Alloy:` pointer |
| `unit_dem_contract_holdingExclusive` | `demand.als` | `HoldingNotACyclePool` | `src/operations/demand/demand-contract.dfy:1071` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && DemandPoolGenesis(log, clog) && KC.WellFormed(clog, cards, plog, items, cfg)`, and `LiveDemandAt(log, d) && HoldingAt(log, d) == Some(e)`, and `KC.LiveCycleAt(clog, c) && KC.StateOfCycleAt(clog, c).Some?` | the lemma's own `Alloy:` pointer |
| `unit_dem_contract_holdingProvenance` | `demand.als` | `HoldingProvenance` | `src/operations/demand/demand-contract.dfy:1032` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && HoldingAt(log, d) == Some(e)` | the lemma's own `Alloy:` pointer |
| `unit_dem_contract_removeRequiresShelved` | `demand.als` | `RemoveRequiresShelved` | `src/operations/demand/demand-contract.dfy:914` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && KeyedCycles(clog) && i < \|log\| && Committed(log[i]) && log[i].kind.RemoveContribution?`, and `PreOf(log, i).Some? && log[i].kind.id in PreOf(log, i).value.sContributions && PreOf(log, i).value.sContributions[log[i].kind.id].CardContribution?`, and `c in CyclesNamed(PrefixBefore(clog, log[i].tick), PreOf(log, i).value.sContributions[log[i].kind.id].cycle)` | the lemma's own `Alloy:` pointer |
| `unit_dem_contract_startProductionRequiresStarted` | `demand.als` | `StartProductionRequiresStarted` | `src/operations/demand/demand-contract.dfy:925` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.StartProduction?`, and `c in AttachedLiveAt(log[..i], PrefixBefore(clog, log[i].tick), log[i].subject)` | the lemma's own `Alloy:` pointer |
| `unit_dem_contract_terminalClosure` | `demand.als` | `TerminalClosure` | `src/operations/demand/demand-contract.dfy:974` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && n1 <= n2 <= \|log\|`, and `DemandStatusAt(log[..n1], d).Some? && TerminalStatus(DemandStatusAt(log[..n1], d).value)` | the lemma's own `Alloy:` pointer |
| `unit_dem_contract_withdrawnDetachReconciles` | `demand.als` | `WithdrawnDetachReconciles` | `src/operations/demand/demand-contract.dfy:963` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.DetachWithdrawn?` | the lemma's own `Alloy:` pointer |
| `unit_dem_holdingPoolPinHolds` | `demand.als` | `HoldingPoolPinMatchesItem` | `src/operations/demand/demand-contract.dfy:1082` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.StartProduction? && log[i].kind.holding.Some?`, and `p in KC.PoolsNamed(PrefixBefore(plog, log[i].tick), log[i].kind.holding.value)` | reading |
| `unit_dem_holdingPoolPinMatchesItem` | `demand.als` | `HoldingPoolPinMatchesItem` | `src/operations/demand/demand-contract.dfy:1082` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.StartProduction? && log[i].kind.holding.Some?`, and `p in KC.PoolsNamed(PrefixBefore(plog, log[i].tick), log[i].kind.holding.value)` | the lemma's own `Alloy:` pointer |
| `unit_dem_nothingAfterRetire` | `demand.als` | `BaNothingAfterRetire` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:264` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_dem_nothingAfterRetire` | `demand.als` | `ItemNothingAfterRetire` | `src/reference-data/item/item-contract.dfy:278` | `WellFormed(log, ba) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_dem_nothingAfterRetire` | `demand.als` | `StaffNothingAfterRetire` | `src/reference-data/staff/staff-contract.dfy:151` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_dem_recordedHoldingLive` | `demand.als` | `RecordedHoldingLive` | `src/operations/demand/demand-contract.dfy:1051` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.RecordProduction? && HoldingAt(log[..i], log[i].subject).Some?` | the name |
| `unit_dem_recordedHoldingLive` | `demand.als` | `RecordedHoldingLive` | `src/operations/demand/demand.dfy:1027` | none | the name |
| `unit_dem_startedHoldingLive` | `demand.als` | `StartedHoldingLive` | `src/operations/demand/demand-contract.dfy:1041` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.StartProduction? && log[i].kind.holding.Some?` | the name |
| `unit_dem_startedHoldingLive` | `demand.als` | `StartedHoldingLive` | `src/operations/demand/demand.dfy:1004` | none | the name |

## `procurement/order`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `int_ord_contract_demandIndivisible` | `order.als` | `DemandIndivisible` | `src/procurement/order/order-contract.dfy:640` | `WellFormed(olog, llog, dlog, items, ba, staff) && KeyedOrders(olog)`, and `l1 in HoldingLineOf(PrefixUpTo(olog, t), PrefixUpTo(llog, t), PrefixUpTo(dlog, t), d)`, and `l2 in HoldingLineOf(PrefixUpTo(olog, t), PrefixUpTo(llog, t), PrefixUpTo(dlog, t), d)` | the lemma's own `Alloy:` pointer |
| `int_ord_contract_frozenOutsideDraft` | `order.als` | `FrozenOutsideDraftOrder` | `src/procurement/order/order-contract.dfy:623` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && IsOrderStructural(olog[i].kind)` | the lemma's own `Alloy:` pointer |
| `int_ord_contract_frozenOutsideDraft` | `order.als` | `FrozenOutsideDraftLine` | `src/procurement/order/order-contract.dfy:630` | `WellFormed(olog, llog, dlog, items, ba, staff) && KeyedOrders(olog) && i < \|llog\| && Committed(llog[i]) && IsLineStructural(llog[i].kind)`, and `o in ParentsOf(PrefixBefore(olog, llog[i].tick), llog[i].subject)` | the lemma's own `Alloy:` pointer |
| `unit_ord_assigneePinCurrencyHolds` | `order.als` | `AssigneePinCurrency` | `src/procurement/order/order-contract.dfy:759` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && olog[i].kind.UpdateOrderDetails? && olog[i].kind.assignee.Some?` | the lemma's own `Alloy:` pointer |
| `unit_ord_bindingPinCurrencyHolds` | `order.als` | `BindingPinCurrency` | `src/procurement/order/order-contract.dfy:752` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && SupplierWritten(olog[i].kind).Some? && SupplierWritten(olog[i].kind).value.vendorPin.Some?` | the lemma's own `Alloy:` pointer |
| `unit_ord_contract_attachItemAgrees` | `order.als` | `AttachItemAgrees` | `src/procurement/order/order-contract.dfy:658` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Committed(llog[i]) && DemandPaired(llog[i].kind).Some?`, and `d in DM.DemandsNamed(PrefixBefore(dlog, llog[i].tick), DemandPaired(llog[i].kind).value)` | the lemma's own `Alloy:` pointer |
| `unit_ord_contract_attachRequiresReleased` | `order.als` | `AttachRequiresReleased` | `src/procurement/order/order-contract.dfy:650` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Committed(llog[i]) && DemandPaired(llog[i].kind).Some?`, and `d in DM.DemandsNamed(PrefixBefore(dlog, llog[i].tick), DemandPaired(llog[i].kind).value)` | the lemma's own `Alloy:` pointer |
| `unit_ord_contract_closeRequiresSettled` | `order.als` | `CloseRequiresSettled` | `src/procurement/order/order-contract.dfy:707` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && olog[i].kind.CloseOrder?`, and `l in LiveLinesOf(PrefixBefore(llog, olog[i].tick), olog[i].subject)` | the lemma's own `Alloy:` pointer |
| `unit_ord_contract_demandIndivisible` | `order.als` | `DemandIndivisible` | `src/procurement/order/order-contract.dfy:640` | `WellFormed(olog, llog, dlog, items, ba, staff) && KeyedOrders(olog)`, and `l1 in HoldingLineOf(PrefixUpTo(olog, t), PrefixUpTo(llog, t), PrefixUpTo(dlog, t), d)`, and `l2 in HoldingLineOf(PrefixUpTo(olog, t), PrefixUpTo(llog, t), PrefixUpTo(dlog, t), d)` | the lemma's own `Alloy:` pointer |
| `unit_ord_contract_frozenOutsideDraft` | `order.als` | `FrozenOutsideDraftOrder` | `src/procurement/order/order-contract.dfy:623` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && IsOrderStructural(olog[i].kind)` | the lemma's own `Alloy:` pointer |
| `unit_ord_contract_frozenOutsideDraft` | `order.als` | `FrozenOutsideDraftLine` | `src/procurement/order/order-contract.dfy:630` | `WellFormed(olog, llog, dlog, items, ba, staff) && KeyedOrders(olog) && i < \|llog\| && Committed(llog[i]) && IsLineStructural(llog[i].kind)`, and `o in ParentsOf(PrefixBefore(olog, llog[i].tick), llog[i].subject)` | the lemma's own `Alloy:` pointer |
| `unit_ord_contract_headerDetailFrozen` | `order.als` | `HeaderDetailFrozen` | `src/procurement/order/order-contract.dfy:725` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i])`, and `OPreOf(olog, i).Some? && OPreOf(olog, i).value.sStatus != OS_DRAFT` | the lemma's own `Alloy:` pointer |
| `unit_ord_contract_lineClosureByAct` | `order.als` | `LineClosureByAct` | `src/procurement/order/order-contract.dfy:694` | `WellFormed(olog, llog, dlog, items, ba, staff) && n <= \|llog\| && LineStatusAt(llog[..n], l) == Some(L_CLOSED)` | the lemma's own `Alloy:` pointer |
| `unit_ord_contract_lineClosureByAct` | `order.als` | `LineClosurePermanent` | `src/procurement/order/order-contract.dfy:700` | `WellFormed(olog, llog, dlog, items, ba, staff) && n1 <= n2 <= \|llog\| && LineStatusAt(llog[..n1], l) == Some(L_CLOSED)` | the lemma's own `Alloy:` pointer |
| `unit_ord_contract_orderTerminalClosure` | `order.als` | `OrderTerminalClosure` | `src/procurement/order/order-contract.dfy:735` | `WellFormed(olog, llog, dlog, items, ba, staff) && n1 <= n2 <= \|olog\|`, and `OrderStatusAt(olog[..n1], o).Some? && TerminalOrderStatus(OrderStatusAt(olog[..n1], o).value)` | the lemma's own `Alloy:` pointer |
| `unit_ord_contract_priorityDefault` | `order.als` | `PriorityDefault` | `src/procurement/order/order-contract.dfy:765` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && olog[i].kind.CreateOrder?` | the lemma's own `Alloy:` pointer |
| `unit_ord_contract_receiptAccrues` | `order.als` | `ReceiptAccrues` | `src/procurement/order/order-contract.dfy:673` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Committed(llog[i]) && llog[i].kind.RecordReceipt?` | the lemma's own `Alloy:` pointer |
| `unit_ord_contract_receiptReverses` | `order.als` | `ReceiptReverses` | `src/procurement/order/order-contract.dfy:680` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Committed(llog[i]) && llog[i].kind.ReverseReceipt?` | the lemma's own `Alloy:` pointer |
| `unit_ord_contract_submitRequiresStarted` | `order.als` | `SubmitRequiresStarted` | `src/procurement/order/order-contract.dfy:666` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && olog[i].kind.Submit?`, and `d in ServicedOf(PrefixBefore(dlog, olog[i].tick), PrefixBefore(llog, olog[i].tick), olog[i].subject)` | the lemma's own `Alloy:` pointer |
| `unit_ord_contract_supplierBindingFrozen` | `order.als` | `SupplierBindingFrozen` | `src/procurement/order/order-contract.dfy:716` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i])`, and `OPreOf(olog, i).Some? && OPreOf(olog, i).value.sStatus != OS_DRAFT` | the lemma's own `Alloy:` pointer |
| `unit_ord_noRecordedRefusalWithoutGenesis` | `order.als` | `OrderNoRecordedRefusalWithoutGenesis` | `src/procurement/order/order-contract.dfy:791` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Recorded(olog, OShapeOf, i) && !Committed(olog[i])` | the lemma's own `Alloy:` pointer |
| `unit_ord_noRecordedRefusalWithoutGenesis` | `order.als` | `LineNoRecordedRefusalWithoutGenesis` | `src/procurement/order/order-contract.dfy:797` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Recorded(llog, LShapeOf, i) && !Committed(llog[i])` | the lemma's own `Alloy:` pointer |
| `unit_ord_noRecordedRefusalWithoutGenesis` | `order.als` | `CycleNoRecordedRefusalWithoutGenesis` | `src/resources/kanban-card/kanban-card-contract.dfy:491` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Recorded(log, ShapeOf, i) && !Committed(log[i])` | the lemma's own `Alloy:` pointer |
| `unit_ord_nothingAfterRetire` | `order.als` | `BaNothingAfterRetire` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:264` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_ord_nothingAfterRetire` | `order.als` | `ItemNothingAfterRetire` | `src/reference-data/item/item-contract.dfy:278` | `WellFormed(log, ba) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_ord_nothingAfterRetire` | `order.als` | `StaffNothingAfterRetire` | `src/reference-data/staff/staff-contract.dfy:151` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_ord_removeRequiresDetached` | `order.als` | `RemoveRequiresDetached` | `src/procurement/order/order-contract.dfy:771` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Committed(llog[i]) && llog[i].kind.RemoveLine?` | the lemma's own `Alloy:` pointer |
| `unit_ord_supplierBindingPinAgreesHolds` | `order.als` | `BindingsSound` | `src/procurement/order/order-contract.dfy:744` | `WellFormed(olog, llog, dlog, items, ba, staff) && StrictTicks(ba) && i < \|olog\| && Committed(olog[i]) && SupplierWritten(olog[i].kind).Some?` | the lemma's own `Alloy:` pointer |
| `unit_ordr_receivedIsAccumulated` | `order_received.als` | `ReceivedIsAccumulated` | `src/procurement/order/order-contract.dfy:688` | `WellFormed(olog, llog, dlog, items, ba, staff) && n <= \|llog\|` | the name |
| `unit_ordr_receivedIsAccumulated` | `order_received.als` | `ReceivedIsAccumulated` | `src/procurement/order/order.dfy:1097` | none | the name |

## `receiving/receiver`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_rcv_carrierPinCurrencyHolds` | `receiver.als` | `CarrierPinCurrency` | `src/receiving/receiver/receiver-contract.dfy:895` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && i < \|rvlog\| && Committed(rvlog[i]) && IsHeaderWrite(rvlog[i].kind) && rvlog[i].kind.carrierPin.Some?` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_actualSetOnce` | `receiver.als` | `ActualNeverChanges` | `src/receiving/receiver/receiver-contract.dfy:780` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && i < \|oalog\| && Committed(oalog[i]) && OAPreOf(oalog, i).Some? && OAPreOf(oalog, i).value.sActual.Some?` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_actualSetOnce` | `receiver.als` | `ActualByRecord` | `src/receiving/receiver/receiver-contract.dfy:789` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && n <= \|oalog\| && OAStateAt(oalog[..n], a).Some? && OAStateAt(oalog[..n], a).value.sActual.Some?` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_captureWindowFrozen` | `receiver.als` | `HeaderFrozenOutsideEditing` | `src/receiving/receiver/receiver-contract.dfy:708` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && i < \|rvlog\| && Committed(rvlog[i]) && rvlog[i].kind.UpdateReceiver?` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_captureWindowFrozen` | `receiver.als` | `CaptureFrozenOutsideReceiving` | `src/receiving/receiver/receiver-contract.dfy:716` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && i < \|rllog\| && Committed(rllog[i]) && IsCaptureMutator(rllog[i].kind)` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_captureWindowFrozen` | `receiver.als` | `LineGenesisInEditing` | `src/receiving/receiver/receiver-contract.dfy:724` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && KeyedReceivers(rvlog) && i < \|rllog\| && Committed(rllog[i]) && rllog[i].kind.AddReceivingLine?`, and `r in ParentsOf(PrefixBefore(rvlog, rllog[i].tick), rllog[i].subject)` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_capturedFactsFrozen` | `receiver.als` | `CapturedFactsFrozen` | `src/receiving/receiver/receiver-contract.dfy:744` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && i < \|rllog\| && Committed(rllog[i]) && RLPreOf(rllog, i).Some? && RLPreOf(rllog, i).value.sStatus != RL_RECEIVING` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_completeRequiresLinesFinalized` | `receiver.als` | `CompleteRequiresLinesFinalized` | `src/receiving/receiver/receiver-contract.dfy:733` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && i < \|rvlog\| && Committed(rvlog[i]) && rvlog[i].kind.CompleteReceiver?`, and `l in LinesOfReceiver(PrefixBefore(rllog, rvlog[i].tick), rvlog[i].subject)` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_deliveriesAppendOnly` | `receiver.als` | `DeliveriesAppendOnly` | `src/receiving/receiver/receiver-contract.dfy:797` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && i < \|rllog\| && Committed(rllog[i]) && RLPreOf(rllog, i).Some?` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_lineCyclePoolDisjoint` | `receiver.als` | `LineCyclePoolDisjoint` | `src/receiving/receiver/receiver-contract.dfy:853` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && ReceivingPoolGenesis(rllog, dlog, clog)`, and `DM.KC.WellFormed(clog, cards, plog, items, cfg) && LineHoldsPool(rllog, l, e)`, and `DM.KC.LiveCycleAt(clog, c) && DM.KC.StateOfCycleAt(clog, c).Some?` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_lineDemandPoolDisjoint` | `receiver.als` | `LineDemandPoolDisjoint` | `src/receiving/receiver/receiver-contract.dfy:864` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && ReceivingPoolGenesis(rllog, dlog, clog)`, and `DM.WellFormed(dlog, pdlog, clog, cards, plog, il, items) && LineHoldsPool(rllog, l, e)`, and `DM.LiveDemandAt(dlog, d)` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_lineForwardMonotone` | `receiver.als` | `LineForwardMonotone` | `src/receiving/receiver/receiver-contract.dfy:806` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && n1 <= n2 <= \|rllog\|` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_linePoolProvenance` | `receiver.als` | `LinePoolProvenance` | `src/receiving/receiver/receiver-contract.dfy:835` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && n <= \|rllog\| && LineHoldsPool(rllog[..n], l, e)` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_linesPoolLoneHolder` | `receiver.als` | `LinesPoolLoneHolder` | `src/receiving/receiver/receiver-contract.dfy:844` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba)`, and `LineHoldsPool(PrefixUpTo(rllog, t), l1, e) && LineHoldsPool(PrefixUpTo(rllog, t), l2, e)` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_receiveAllocationBounded` | `receiver.als` | `ReceiveAllocationBounded` | `src/receiving/receiver/receiver-contract.dfy:771` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && i < \|rllog\| && Committed(rllog[i]) && rllog[i].kind.ReceiveLine?` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_receiveSameItemPool` | `receiver.als` | `ReceiveSameItemPool` | `src/receiving/receiver/receiver-contract.dfy:760` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && KeyedPools(plog) && i < \|rllog\| && Committed(rllog[i]) && rllog[i].kind.ReceiveLine? && rllog[i].kind.pool.Some?` | the lemma's own `Alloy:` pointer |
| `unit_rcv_contract_receiverTerminalComplete` | `receiver.als` | `ReceiverTerminalComplete` | `src/receiving/receiver/receiver-contract.dfy:816` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && n1 <= n2 <= \|rvlog\| && ReceiverStatusAt(rvlog[..n1], r) == Some(RV_COMPLETE)` | the lemma's own `Alloy:` pointer |
| `unit_rcv_lineAttachAgreesWithPartner` | `receiver.als` | `LineAdmitsAttach` | `src/receiving/receiver/receiver.dfy:1359` | `(k.AppendAttribution? && AppendAttributionViol(prefix, oat, l, k.attribution) == {}) \|\| (k.AddReceivingLine? && k.withAttribution.Some? && AddLineViol(prefix, rvt, oat, it, l, k) == {})` | the lemma's own `Alloy:` pointer |
| `unit_rcv_lineItemPinCurrencyHolds` | `receiver.als` | `ItemPinCurrency` | `src/receiving/receiver/receiver-contract.dfy:905` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && i < \|rllog\| && Committed(rllog[i]) && ItemWritten(rllog[i].kind).Some?` | reading |
| `unit_rcv_receiverCarrierPinAgreesHolds` | `receiver.als` | `CarrierPinAgrees` | `src/receiving/receiver/receiver-contract.dfy:886` | `WellFormed(rvlog, rllog, oalog, dlog, pdlog, clog, plog, items, ba) && StrictTicks(ba) && i < \|rvlog\| && Committed(rvlog[i]) && IsHeaderWrite(rvlog[i].kind)` | the lemma's own `Alloy:` pointer |

## `reference_data/business_affiliate`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_ba_committedStatesAgreeOnKind` | `business_affiliate.als` | `RoleKindFixedAtBirthHolds` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:272` | `WellFormed(log) && i < \|log\| && Committed(log[i])` | reading |
| `unit_ba_lifecycleShape` | `business_affiliate.als` | `BaLifecycleShape` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:251` | `WellFormed(log) && i < \|log\| && Committed(log[i])` | the lemma's own `Alloy:` pointer |
| `unit_ba_nothingAfterRetire` | `business_affiliate.als` | `BaNothingAfterRetire` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:264` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_ba_nothingAfterRetire` | `business_affiliate.als` | `ItemNothingAfterRetire` | `src/reference-data/item/item-contract.dfy:278` | `WellFormed(log, ba) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_ba_nothingAfterRetire` | `business_affiliate.als` | `StaffNothingAfterRetire` | `src/reference-data/staff/staff-contract.dfy:151` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_ba_oneVersionPerRole` | `business_affiliate.als` | `RoleIdsAreKeysHolds` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:281` | `WellFormed(log)` | the lemma's own `Alloy:` pointer |
| `unit_ba_oneVersionPerRole` | `business_affiliate.als` | `OneVersionPerRoleHolds` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:288` | none | the lemma's own `Alloy:` pointer |
| `unit_ba_retireIsTombstone` | `business_affiliate.als` | `BaRetireIsTombstone` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:293` | `WellFormed(log) && i < \|log\| && Committed(log[i]) && log[i].kind.RetireBa?` | reading |
| `unit_ba_roleKindFixedAtBirth` | `business_affiliate.als` | `RoleKindFixedAtBirthHolds` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:272` | `WellFormed(log) && i < \|log\| && Committed(log[i])` | the lemma's own `Alloy:` pointer |
| `unit_ba_roleKindFixedAtBirth` | `business_affiliate.als` | `RoleIdsAreKeysHolds` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:281` | `WellFormed(log)` | the lemma's own `Alloy:` pointer |
| `unit_ba_roleOwnership` | `business_affiliate.als` | `RoleOwnershipHolds` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:244` | `WellFormed(log)` | the lemma's own `Alloy:` pointer |

## `reference_data/item`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_item_eachConfigured` | `item.als` | `EachConfigured` | `src/reference-data/item/uom.dfy:48` | none | the lemma's own `Alloy:` pointer |
| `unit_item_lifecycleShape` | `item.als` | `ItemLifecycleShape` | `src/reference-data/item/item-contract.dfy:266` | `WellFormed(log, ba) && i < \|log\| && Committed(log[i])` | the lemma's own `Alloy:` pointer |
| `unit_item_nothingAfterRetire` | `item.als` | `BaNothingAfterRetire` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:264` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_item_nothingAfterRetire` | `item.als` | `ItemNothingAfterRetire` | `src/reference-data/item/item-contract.dfy:278` | `WellFormed(log, ba) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_item_nothingAfterRetire` | `item.als` | `StaffNothingAfterRetire` | `src/reference-data/staff/staff-contract.dfy:151` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_item_retireIsTombstone` | `item.als` | `ItemRetireIsTombstone` | `src/reference-data/item/item-contract.dfy:284` | `WellFormed(log, ba) && i < \|log\| && Committed(log[i]) && log[i].kind.RetireItem?` | reading |
| `unit_item_supplyOwnership` | `item.als` | `SupplyOwnershipHolds` | `src/reference-data/item/item-contract.dfy:252` | `WellFormed(log, ba)` | the lemma's own `Alloy:` pointer |
| `unit_item_supplyPinCurrencyHolds` | `item.als` | `SupplierPinsSoundHolds` | `src/reference-data/item/item-contract.dfy:259` | `WellFormed(log, ba) && StrictTicks(ba)` | reading |
| `unit_item_toEachIdentity` | `item.als` | `EachConfigured` | `src/reference-data/item/uom.dfy:48` | none | the lemma's own `Alloy:` pointer |
| `unit_collapse_eachIdentity` | `uom_collapse.als` | `EachIdentity` | `src/reference-data/item/uom-collapse.dfy:79` | `q.Keys == {Each}` | the name |
| `unit_collapse_eachKeyed` | `uom_collapse.als` | `EachKeyed` | `src/reference-data/item/uom-collapse.dfy:69` | none | the name |
| `unit_collapse_singleIsToEach` | `uom_collapse.als` | `SingleIsToEach` | `src/reference-data/item/uom-collapse.dfy:71` | `q.Keys == {u} && u in sch.factor` | the name |
| `unit_collapse_twoUnitFolds` | `uom_collapse.als` | `TwoUnitFolds` | `src/reference-data/item/uom-collapse.dfy:89` | `q.Keys == {u1, u2} && u1 != u2 && Covers(sch, q)` | the name |

## `reference_data/shared`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_shared_supplierIsVendor` | `shared.als` | `SupplierIsVendor` | `src/reference-data/shared/tests/shared-tests.dfy:70` | `IM.WellFormed(log, ba) && StrictTicks(ba) && s in AllSupplies(log) && s.supplierRole.Some?` | the name |

## `reference_data/staff`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_staff_nothingAfterRetire` | `staff.als` | `BaNothingAfterRetire` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:264` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_staff_nothingAfterRetire` | `staff.als` | `ItemNothingAfterRetire` | `src/reference-data/item/item-contract.dfy:278` | `WellFormed(log, ba) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_staff_nothingAfterRetire` | `staff.als` | `StaffNothingAfterRetire` | `src/reference-data/staff/staff-contract.dfy:151` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_staff_retireIsTombstone` | `staff.als` | `StaffRetireIsTombstone` | `src/reference-data/staff/staff-contract.dfy:157` | `WellFormed(log) && i < \|log\| && Committed(log[i]) && log[i].kind.RetireStaff?` | reading |
| `unit_stf_lifecycleShape` | `staff.als` | `StaffLifecycleShape` | `src/reference-data/staff/staff-contract.dfy:139` | `WellFormed(log) && i < \|log\| && Committed(log[i])` | the lemma's own `Alloy:` pointer |
| `unit_stf_nameUniqueInTenant` | `staff.als` | `StaffNameUniqueHolds` | `src/reference-data/staff/staff-contract.dfy:133` | `WellFormed(log)` | the lemma's own `Alloy:` pointer |

## `resources/inventory_item`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `int_ii_contract_closureIsTerminal` | `inventory_item.als` | `ClosureIsTerminal` | `src/resources/inventory-item/inventory-item-contract.dfy:330` | `WellFormed(log, items) && n1 <= n2 <= \|log\| && Started(log[..n1], ii) && !LiveAt(log[..n1], ii)` | the lemma's own `Alloy:` pointer |
| `int_ii_contract_closureIsTerminal` | `inventory_item.als` | `ClosureIsTerminal` | `src/resources/kanban-card/kanban-card-contract.dfy:447` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && ClosedAt(log[..i], log[i].subject)` | the lemma's own `Alloy:` pointer |
| `int_ii_contract_stateFunction` | `inventory_item.als` | `StateIsFunctionOnceStarted` | `src/resources/inventory-item/inventory-item-contract.dfy:313` | `WellFormed(log, items) && n1 <= n2 <= \|log\| && StateAt(log[..n1], ii).Some?` | the lemma's own `Alloy:` pointer |
| `unit_pool_homogeneous` | `inventory_pool.als` | `PoolMembersAgree` | `src/resources/inventory-item/inventory-pool-contract.dfy:382` | `WellFormed(log)` | the lemma's own `Alloy:` pointer |
| `unit_pool_membershipExclusive` | `inventory_pool.als` | `PoolMembershipExclusive` | `src/resources/inventory-item/inventory-pool-contract.dfy:388` | `WellFormed(log)` | the lemma's own `Alloy:` pointer |
| `unit_pool_membershipExclusive` | `inventory_pool.als` | `PoolMembershipExclusive` | `src/resources/inventory-item/inventory-pool-contract.dfy:388` | `WellFormed(log)` | the lemma's own `Alloy:` pointer |
| `unit_pool_reversalDisciplineHolds` | `inventory_pool.als` | `PoolLogChained` | `src/resources/inventory-item/inventory-pool-contract.dfy:395` | `WellFormed(log)` | the lemma's own `Alloy:` pointer |
| `unit_pool_sameTenant` | `inventory_pool.als` | `PoolMembersAgree` | `src/resources/inventory-item/inventory-pool-contract.dfy:382` | `WellFormed(log)` | the lemma's own `Alloy:` pointer |
| `unit_pool_stampsMonotone` | `inventory_pool.als` | `PoolStampsMonotoneHolds` | `src/resources/inventory-item/inventory-pool-contract.dfy:415` | `WellFormed(log)` | the lemma's own `Alloy:` pointer |
| `unit_invmet_frameworkMatchesLog` | `metrics.als` | `FrameworkMatchesLog` | `src/resources/inventory-item/metrics.dfy:387` | `Aligned(log, at) && StrictChronology(log, at)` | the name |
| `unit_invmet_partitionAdditivity` | `metrics.als` | `PartitionAdditivity` | `src/resources/inventory-item/metrics.dfy:199` | `x.cAsOf == z.cAsOf && y.cAsOf == z.cAsOf`, and `MembersOf(log, at, x) !! MembersOf(log, at, y) && MembersOf(log, at, z) == MembersOf(log, at, x) + MembersOf(log, at, y)` | the name |
| `unit_invmet_quietPeriodRepeats` | `metrics.als` | `QuietPeriodRepeats` | `src/resources/inventory-item/metrics.dfy:255` | `c1.cTenant == c2.cTenant && c1.cItem == c2.cItem && c1.cNode.None? && c2.cNode.None? && AtOrBefore(c1.cAsOf, c2.cAsOf)`, and `forall i :: 0 <= i < \|log\| && Committed(log[i]) ==> !(EarlierThan(c1.cAsOf, at(log[i])) && AtOrBefore(at(log[i]), c2.cAsOf))` | the name |
| `unit_plc_affirmIsInert` | `pool_lifecycle.als` | `PoolAffirmIsInert` | `src/resources/inventory-item/inventory-pool-contract.dfy:429` | `WellFormed(log) && i < \|log\| && Committed(log[i]) && log[i].kind.AffirmPool?` | the lemma's own `Alloy:` pointer |
| `unit_plc_affirmNeverCreatedIsNotClosed` | `pool_lifecycle.als` | `PoolAffirmNeverCreatedIsNotClosed` | `src/resources/inventory-item/inventory-pool-contract.dfy:435` | `WellFormed(log) && i < \|log\| && log[i].kind.AffirmPool? && Refused(log[i]) && PreOf(log, i).None?` | the lemma's own `Alloy:` pointer |
| `unit_plc_noRecordedRefusalWithoutGenesis` | `pool_lifecycle.als` | `OrderNoRecordedRefusalWithoutGenesis` | `src/procurement/order/order-contract.dfy:791` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Recorded(olog, OShapeOf, i) && !Committed(olog[i])` | the lemma's own `Alloy:` pointer |
| `unit_plc_noRecordedRefusalWithoutGenesis` | `pool_lifecycle.als` | `LineNoRecordedRefusalWithoutGenesis` | `src/procurement/order/order-contract.dfy:797` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Recorded(llog, LShapeOf, i) && !Committed(llog[i])` | the lemma's own `Alloy:` pointer |
| `unit_plc_noRecordedRefusalWithoutGenesis` | `pool_lifecycle.als` | `PoolNoRecordedRefusalWithoutGenesis` | `src/resources/inventory-item/inventory-pool-contract.dfy:441` | `WellFormed(log) && i < \|log\| && Recorded(log, ShapeOf, i) && !Committed(log[i])` | the lemma's own `Alloy:` pointer |
| `unit_plc_nothingAfterRetire` | `pool_lifecycle.als` | `BaNothingAfterRetire` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:264` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_plc_nothingAfterRetire` | `pool_lifecycle.als` | `ItemNothingAfterRetire` | `src/reference-data/item/item-contract.dfy:278` | `WellFormed(log, ba) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_plc_nothingAfterRetire` | `pool_lifecycle.als` | `StaffNothingAfterRetire` | `src/reference-data/staff/staff-contract.dfy:151` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_ii_contract_bornLive` | `inventory_item.als` | `BornLive` | `src/resources/inventory-item/inventory-item-contract.dfy:324` | `WellFormed(log, items) && i < \|log\| && Committed(log[i]) && ii in Touches(log[i]) && !Started(log[..i], ii)` | the lemma's own `Alloy:` pointer |
| `unit_ii_contract_closureIsTerminal` | `inventory_item.als` | `ClosureIsTerminal` | `src/resources/inventory-item/inventory-item-contract.dfy:330` | `WellFormed(log, items) && n1 <= n2 <= \|log\| && Started(log[..n1], ii) && !LiveAt(log[..n1], ii)` | the lemma's own `Alloy:` pointer |
| `unit_ii_contract_closureIsTerminal` | `inventory_item.als` | `ClosureIsTerminal` | `src/resources/kanban-card/kanban-card-contract.dfy:447` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && ClosedAt(log[..i], log[i].subject)` | the lemma's own `Alloy:` pointer |
| `unit_ii_contract_liveHaveState` | `inventory_item.als` | `LiveHaveState` | `src/resources/inventory-item/inventory-item-contract.dfy:318` | `WellFormed(log, items) && n <= \|log\| && LiveAt(log[..n], ii)` | the lemma's own `Alloy:` pointer |
| `unit_ii_contract_readBack` | `inventory_item.als` | `CommittedWritesReadBack` | `src/resources/inventory-item/inventory-item-contract.dfy:342` | `WellFormed(log, items) && i < \|log\| && Committed(log[i]) && ii in Touches(log[i])` | the lemma's own `Alloy:` pointer |
| `unit_ii_contract_stateFunction` | `inventory_item.als` | `StateIsFunctionOnceStarted` | `src/resources/inventory-item/inventory-item-contract.dfy:313` | `WellFormed(log, items) && n1 <= n2 <= \|log\| && StateAt(log[..n1], ii).Some?` | the lemma's own `Alloy:` pointer |
| `unit_ii_contract_touchesLiveness` | `inventory_item.als` | `TouchesDetermineLiveness` | `src/resources/inventory-item/inventory-item-contract.dfy:336` | `WellFormed(log, items) && i < \|log\| && Committed(log[i]) && ii in Touches(log[i])` | the lemma's own `Alloy:` pointer |
| `unit_occ_committedUnitsValid` | `inventory_item.als` | `CommittedUnitsValid` | `src/resources/inventory-item/tests/inventory-item-tests.dfy:363` | `IIM.WellFormed(log, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Consume?` | the name |
| `unit_occ_expiryNeverLengthens` | `inventory_item.als` | `ExpiryNeverLengthens` | `src/resources/inventory-item/tests/inventory-item-tests.dfy:342` | `IIM.WellFormed(log, items) && i < \|log\| && Committed(log[i]) && !log[i].kind.Create? && PreT(log, i).sExpiration.Some?` | the name |
| `unit_occ_itemPinCurrencyHolds` | `inventory_item.als` | `ItemPinCurrencyHolds` | `src/resources/inventory-item/inventory-item-contract.dfy:361` | `WellFormed(log, items)` | the lemma's own `Alloy:` pointer |
| `unit_occ_lpnUniqueAmongStarted` | `inventory_item.als` | `LicensePlateUniqueHolds` | `src/resources/inventory-item/inventory-item-contract.dfy:348` | `WellFormed(log, items)` | reading |
| `unit_occ_mergeConserves` | `inventory_item.als` | `MergeConserves` | `src/resources/inventory-item/tests/inventory-item-tests.dfy:332` | `IIM.WellFormed(log, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Merge?` | the name |
| `unit_occ_noCommittedOverdraw` | `inventory_item.als` | `NoCommittedOverdraw` | `src/resources/inventory-item/tests/inventory-item-tests.dfy:294` | `IIM.WellFormed(log, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Consume?` | the name |
| `unit_occ_noResurrection` | `inventory_item.als` | `NoResurrection` | `src/resources/inventory-item/tests/inventory-item-tests.dfy:302` | `IIM.WellFormed(log, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Create?` | the name |
| `unit_occ_sealedOnlyBySeal` | `inventory_item.als` | `SealedOnlyBySeal` | `src/resources/inventory-item/tests/inventory-item-tests.dfy:353` | `IIM.WellFormed(log, items) && i < \|log\| && Committed(log[i]) && !log[i].kind.Seal?` | the name |
| `unit_occ_serialUniqueAmongStarted` | `inventory_item.als` | `SerialNumberUniquePerItemHolds` | `src/resources/inventory-item/inventory-item-contract.dfy:354` | `WellFormed(log, items)` | reading |
| `unit_occ_splitConserves` | `inventory_item.als` | `SplitConserves` | `src/resources/inventory-item/tests/inventory-item-tests.dfy:310` | `IIM.WellFormed(log, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Split?` | the name |
| `unit_occ_terminalRetirement` | `inventory_item.als` | `ClosureIsTerminal` | `src/resources/inventory-item/inventory-item-contract.dfy:330` | `WellFormed(log, items) && n1 <= n2 <= \|log\| && Started(log[..n1], ii) && !LiveAt(log[..n1], ii)` | reading |

## `resources/kanban_card`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_cyc_closureIsTerminal` | `cycle_occurrences.als` | `ClosureIsTerminal` | `src/resources/inventory-item/inventory-item-contract.dfy:330` | `WellFormed(log, items) && n1 <= n2 <= \|log\| && Started(log[..n1], ii) && !LiveAt(log[..n1], ii)` | the lemma's own `Alloy:` pointer |
| `unit_cyc_closureIsTerminal` | `cycle_occurrences.als` | `ClosureIsTerminal` | `src/resources/kanban-card/kanban-card-contract.dfy:447` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && ClosedAt(log[..i], log[i].subject)` | the lemma's own `Alloy:` pointer |
| `unit_cyc_forwardMonotone` | `cycle_occurrences.als` | `ForwardMonotone` | `src/resources/kanban-card/kanban-card-contract.dfy:392` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && IsForward(log[i].kind)` | the lemma's own `Alloy:` pointer |
| `unit_cyc_noPoolBeforeInProcess` | `cycle_occurrences.als` | `NoPoolBeforeInProcess` | `src/resources/kanban-card/kanban-card-contract.dfy:398` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && PostOf(log, i).Some? && RegionBefore(PostOf(log, i).value.sStatus, IN_PROCESS)` | the lemma's own `Alloy:` pointer |
| `unit_cyc_oneLiveCyclePerCard` | `cycle_occurrences.als` | `OneLiveCyclePerCard` | `src/resources/kanban-card/kanban-card-contract.dfy:384` | `WellFormed(log, cards, plog, items, cfg) && CardsWF(cards) && k in cards && c1 in k.cycles && c2 in k.cycles`, and `LiveCycleAt(log, c1) && LiveCycleAt(log, c2)` | the lemma's own `Alloy:` pointer |
| `unit_cyc_poolExclusiveWhileLive` | `cycle_occurrences.als` | `PoolExclusiveWhileLive` | `src/resources/kanban-card/kanban-card-contract.dfy:430` | `WellFormed(log, cards, plog, items, cfg)`, and `LiveCycleAt(log, c1) && StateOfCycleAt(log, c1).Some? && StateOfCycleAt(log, c1).value.sPool == Some(e)`, and `LiveCycleAt(log, c2) && StateOfCycleAt(log, c2).Some? && StateOfCycleAt(log, c2).value.sPool == Some(e)` | the lemma's own `Alloy:` pointer |
| `unit_cyc_poolFrozenOnceAttached` | `cycle_occurrences.als` | `PoolFrozenOnceAttached` | `src/resources/kanban-card/kanban-card-contract.dfy:405` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && !log[i].kind.StartProcessing? && !log[i].kind.ProductionFailure?`, and `PreOf(log, i).Some? && PreOf(log, i).value.sPool.Some?` | the lemma's own `Alloy:` pointer |
| `unit_cyc_poolItemHomogeneous` | `cycle_occurrences.als` | `PoolItemHomogeneous` | `src/resources/kanban-card/kanban-card-contract.dfy:460` | `WellFormed(log, cards, plog, items, cfg) && CardsWF(cards) && i < \|log\| && Committed(log[i]) && log[i].kind.StartProcessing?`, and `p in PoolsNamed(PrefixBefore(plog, log[i].tick), log[i].kind.pool) && k in Owners(cards, log[i].subject)` | the lemma's own `Alloy:` pointer |
| `unit_cyc_poolProvenance` | `cycle_occurrences.als` | `PoolProvenance` | `src/resources/kanban-card/kanban-card-contract.dfy:414` | `WellFormed(log, cards, plog, items, cfg) && StateOfCycleAt(log, c).Some? && StateOfCycleAt(log, c).value.sPool == Some(e)` | the lemma's own `Alloy:` pointer |
| `unit_cyc_quantityFixedAtGenesis` | `cycle_occurrences.als` | `QuantityFixedAtGenesis` | `src/resources/kanban-card/kanban-card-contract.dfy:453` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && !log[i].kind.Request? && PreOf(log, i).Some?` | the lemma's own `Alloy:` pointer |
| `unit_cyr_abandonedIsWithdrawn` | `cycle_retire.als` | `AbandonedIsWithdrawn` | `src/resources/kanban-card/kanban-card-contract.dfy:498` | none | the lemma's own `Alloy:` pointer |
| `unit_cyr_attachedOnceById` | `cycle_retire.als` | `PoolAttachedOnce` | `src/resources/kanban-card/kanban-card-contract.dfy:421` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && j < \|log\| && Committed(log[i]) && Committed(log[j])`, and `log[i].kind.StartProcessing? && log[j].kind.StartProcessing? && log[i].kind.pool == log[j].kind.pool` | reading |
| `unit_cyr_closedBeforeSuccessorGenesis` | `cycle_retire.als` | `ClosedBeforeSuccessorGenesis` | `src/resources/kanban-card/kanban-card-contract.dfy:439` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && log[i].kind.Request? && log[i].subject.precededBy.Some?` | the lemma's own `Alloy:` pointer |
| `unit_cyr_noRecordedRefusalWithoutGenesis` | `cycle_retire.als` | `OrderNoRecordedRefusalWithoutGenesis` | `src/procurement/order/order-contract.dfy:791` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Recorded(olog, OShapeOf, i) && !Committed(olog[i])` | the lemma's own `Alloy:` pointer |
| `unit_cyr_noRecordedRefusalWithoutGenesis` | `cycle_retire.als` | `LineNoRecordedRefusalWithoutGenesis` | `src/procurement/order/order-contract.dfy:797` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Recorded(llog, LShapeOf, i) && !Committed(llog[i])` | the lemma's own `Alloy:` pointer |
| `unit_cyr_noRecordedRefusalWithoutGenesis` | `cycle_retire.als` | `CycleNoRecordedRefusalWithoutGenesis` | `src/resources/kanban-card/kanban-card-contract.dfy:491` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Recorded(log, ShapeOf, i) && !Committed(log[i])` | the lemma's own `Alloy:` pointer |
| `unit_cyr_nothingAfterRetire` | `cycle_retire.als` | `BaNothingAfterRetire` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:264` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_cyr_nothingAfterRetire` | `cycle_retire.als` | `ItemNothingAfterRetire` | `src/reference-data/item/item-contract.dfy:278` | `WellFormed(log, ba) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_cyr_nothingAfterRetire` | `cycle_retire.als` | `StaffNothingAfterRetire` | `src/reference-data/staff/staff-contract.dfy:151` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer |
| `unit_cyr_poolAttachedOnce` | `cycle_retire.als` | `PoolAttachedOnce` | `src/resources/kanban-card/kanban-card-contract.dfy:421` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && j < \|log\| && Committed(log[i]) && Committed(log[j])`, and `log[i].kind.StartProcessing? && log[j].kind.StartProcessing? && log[i].kind.pool == log[j].kind.pool` | the lemma's own `Alloy:` pointer |
| `unit_cyr_startedPoolLive` | `cycle_retire.als` | `StartedPoolLive` | `src/resources/kanban-card/kanban-card-contract.dfy:477` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && log[i].kind.StartProcessing?` | the name |
| `unit_cyr_startedPoolLive` | `cycle_retire.als` | `StartedPoolLive` | `src/resources/kanban-card/kanban-card.dfy:419` | none | the name |

## `resources/processing_network`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_pnet_unretiredAlwaysLive` | `processing_network.als` | `UnretiredAlwaysLive` | `src/resources/processing-network/processing-network.dfy:51` | `s.retiredAt.None?` | the name |

## `shared/certainty`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_cert_decayNeverRaises` | `certainty.als` | `DecayNeverRaises` | `src/shared/certainty/certainty.dfy:40` | `ComputedFrom(c, s)` | the name |
| `unit_cert_floorIsLowest` | `certainty.als` | `FloorIsLowest` | `src/shared/certainty/certainty.dfy:42` | none | the name |
| `unit_cert_order` | `certainty.als` | `FrozenOutsideDraftOrder` | `src/procurement/order/order-contract.dfy:623` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && IsOrderStructural(olog[i].kind)` | the lemma's own `Alloy:` pointer |
| `unit_cert_order` | `certainty.als` | `AllLevels` | `src/shared/certainty/certainty.dfy:34` | none | the lemma's own `Alloy:` pointer |

## `shared/measurement`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_q_dispatchLastFirst` | `quantity.als` | `DispatchLastFirst` | `src/shared/measurement/quantity.dfy:148` | `OneSamplePerInstant(ms)` | the name |
| `unit_q_minLeMax` | `quantity.als` | `MinLeMax` | `src/shared/measurement/quantity.dfy:130` | `MinIn(ms, s, p).Some? && MaxIn(ms, s, p).Some?` | the lemma's own `Alloy:` pointer |
| `unit_q_minMaxSampled` | `quantity.als` | `MinMaxSampled` | `src/shared/measurement/quantity.dfy:139` | none | the name |
| `unit_q_sumSingleton` | `quantity.als` | `SumSingleton` | `src/shared/measurement/quantity.dfy:177` | `i < \|ms\| && forall j :: 0 <= j < \|ms\| ==> ((ms[j].of == s && Within(ms[j].at, p)) <==> j == i)` | the name |

## `shared/time`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `unit_time_closeAtOrAfter` | `calendar.als` | `DayPeriodsLawful` | `src/shared/time/calendar.dfy:51` | none | reading |
| `unit_time_closeAtOrAfter` | `calendar.als` | `HourPeriodsLawful` | `src/shared/time/calendar.dfy:69` | none | reading |
| `unit_time_closeIdempotent` | `calendar.als` | `DayPeriodsLawful` | `src/shared/time/calendar.dfy:51` | none | reading |
| `unit_time_closeIdempotent` | `calendar.als` | `HourPeriodsLawful` | `src/shared/time/calendar.dfy:69` | none | reading |
| `unit_time_inOwnPeriod` | `calendar.als` | `DayPeriodsLawful` | `src/shared/time/calendar.dfy:51` | none | reading |
| `unit_time_inOwnPeriod` | `calendar.als` | `HourPeriodsLawful` | `src/shared/time/calendar.dfy:69` | none | reading |
| `unit_time_samePeriodEquiv` | `calendar.als` | `SamePeriodEquiv` | `src/shared/time/tests/calendar-tests.dfy:43` | `Time.Calendar(ps)` | the name |

## `shared/x731_state`

| Check | Root | Dafny lemma | At | Premises | Matched by |
| --- | --- | --- | --- | --- | --- |
| `X731Consistency` | `state.als` | `X731Consistency` | `src/shared/x731-state/state.dfy:63` | `ResourceInterlocks(r)` | the name |
