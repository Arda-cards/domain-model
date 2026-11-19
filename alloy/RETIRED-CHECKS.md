# The retired checks, and the Dafny lemma that proves each law

This file is the record behind the classification in [`EXTENSIONS.md`](EXTENSIONS.md): for every `check` that was
retired, the lemma of the Dafny reference model (the repository `dafny-domain`) that proves the same law, where it is,
what the lemma assumes, and why its statement implies the check's property. With it a retired obligation can be
traced to its replacement without any other source.

## How to read it

- **The Dafny revision** is `ac608469423b3dad0614407337a3bb3fc2b77b1d` (`ac60846`, dafny-domain's main on 2026-11-15, when the matches were made).
  Each lemma is cited as `file:line` at that revision. Later revisions move the lines, not the names.
- **Premises** are the lemma's `requires` clauses at that revision, as written. `none` means the lemma has no
  `requires` clause. "The premises", below, lists each kind of premise with the facts of the Alloy model that imply
  it.
- **Matched by** says how the row's check and lemma were first paired:
  - the lemma's own `Alloy:` pointer names the check (49 rows);
  - the names agree (51 rows);
  - by reading the two statements (20 rows);
  - the audit added the lemma (22 rows; see "The audit" below).
- **Why the lemma implies the check** is the audit's sentence for the check, on the check's first row. **P** is what
  the lemma states, or what the lemmas state together when the check has several rows. **Q** is what the check states.
  The cell then says why P implies Q.
- **A check with several rows** is a law that Dafny states in several lemmas: per module, or in parts.
- **The scope:** the `check` commands outside `soak/`, `conventions/` and `meta/examples/`, as main stood at
  `2986f32`. The kept checks are listed in `EXTENSIONS.md`, each with its reason.

**Counts:** 129 retired `check` commands under 128 names (`unit_pool_membershipExclusive` has two
commands, one of them with a transfer in scope), 142 check-and-lemma rows, 22 modules.

**Four of them are still in the tree** until the integration finders that replace them merge (the project owner's
ruling on card QA787, second question, option (a)): `int_dem_contract_cycleIndivisible`,
`int_dem_contract_frozenOutsideOpen`, `int_ord_contract_demandIndivisible` and `int_ord_contract_frozenOutsideDraft`.

## The audit (2026-11-18)

The pairings were first made by pointer, by name and by reading, and 210 checks (211 commands) were recorded as
retired. Three review comments on this file then showed pairings that a shared name had made across modules. So every
pairing was read again: the check's text beside the lemma's statement, at the revisions above. The check's text is
the same at `2986f32` and at main `80192da`, where the audit read it.

**The rule.** A check stays retired only where both of these hold:

1. the lemma's statement implies the check's property, and the reason can be written plainly in its row;
2. each premise of the lemma holds of every instance of the check's root: the check states the same premise, or
   facts of the Alloy model imply it ("The premises", below).

**The result.**

- **128 checks stay retired** (129 commands).
  - 101 pairings stand as first recorded.
  - 27 had a citation that was wrong or incomplete, and the right lemma exists. Their rows now cite it. Most were a
    name matched across modules: each module's `nothingAfterRetire` check, for example, was paired with the
    affiliate's, the item's and the staff's lemmas.
- **82 checks are restored to the tree.** `EXTENSIONS.md` lists them among the kept checks, each with its reason.
  - **5 restate a fact of the Alloy model that Dafny only assumes.** Each is the guard of that fact:
    `unit_kernel_eIdIsKey`, `unit_principal_nameIsKey`, `X731Consistency`, `unit_occ_onePerTick` and
    `unit_occ_archeOriginPrecedes`.
  - **2 have no lemma that implies them:** `unit_act_walkEndsAtOrigin` and `unit_alg_scaleZeroValue`. The reference
    model was searched for a lemma whose statement concludes the property, by statement and not by name.
  - **75 are in a unit root that gives its lower modules as contract mocks:** the demand's two unit roots (22), the
    order's (19), the receiver's (17) and the inventory item's (17). A mock keeps the lower module's occurrences and
    replaces its chaining and effect facts with the contract's `guarantees`. In Dafny a lower module's state is
    always its `Effect` folded over its log. It is not shown that every lower state of a mock is the state of some
    lower log, so the lemma is not shown to cover every instance of such a root.
    A follow-up in the project's plan (activity AC-04-03-02-31) compares each mock with the effect's fold; the
    checks whose root passes retire then.

## The premises

A Dafny lemma holds of the logs that satisfy its `requires` clauses. An Alloy check holds of every instance of its
root. So a lemma replaces a check only where the root's instances satisfy the lemma's premises. This section lists
every kind of premise in the rows below, with what implies it in the Alloy model, by file and line under `alloy/` at
this revision. A premise with nothing that implies it would make its checks kept: none is left in the rows below.

The table matches predicates. It takes the two guards and the two effects of a module to be the same functions,
which is what the Alloy model is a mirror of: each refusal has its finder, and the reference model's pointer check
reads the names.

**Case hypotheses** are not in the table: an index within the log, a row that is `Committed`, a kind, a subject that
is live. Each restricts the lemma to the case the check's own antecedent names, and the row's last column says so.
35 checks have a lemma with no premise at all.

| Premise | Checks | In Dafny | What implies it in Alloy |
| --- | --- | --- | --- |
| `WellFormed(…)` of a module's own logs | 48 | Its body is about the module's own logs only: the ticks are ordered (`Ordered`, `src/meta/trace.dfy:68`) and every row's verdict is the guard's (`Generated`), with the pairing conjuncts of the pool and of the demand. The lower logs are arguments of the guard, with no condition on them. Every `Append` keeps it. | The order: `OneOccurrencePerTick` (`meta/occurrence/occurrence.als:40`). The verdicts: the module's admission fact, with its chaining and effect facts for the state the guard reads. Per module, in the next table. Every root of these 48 checks opens the lower modules' implementations, not their mocks. |
| `StrictTicks(ba)`: the affiliate log is ordered | 2 | A conjunct of the affiliate's own well-formedness, which every `Append` keeps. | `OneOccurrencePerTick` (`meta/occurrence/occurrence.als:40`). The kept check `unit_occ_onePerTick` guards it. |
| `KeyedOrders(olog)`, `Keyed(u)`: entity ids are keys | 3 | Assumed. No lemma establishes it. | `EntityIdIsKey` (`meta/kernel.als:22`). The kept check `unit_kernel_eIdIsKey` guards it. |
| `NamesUnique(ps)`: principal names are keys | 1 | Assumed. | `PrincipalNameUnique` (`meta/principal/principal.als:37`). The kept check `unit_principal_nameIsKey` guards it. |
| `CardsWF(cards)`: the static card set is well formed | 2 | Assumed: the cards are given, not built by a log. | Conjunct by conjunct, in `resources/kanban_card/kanban_card_types.als`: a cycle is in one card, of its tenant (`CardCycleOwnership`, :281); the chain stays in the card (`PrecededByWithinCard`, :287); one head (`OneChainPerCard`, :290); no fork (`PrecededByLinear`, :52); serials are unique in a tenant (`SerialNumberUniqueInTenant`, :275). Print consistency: `KanbanPrintConsistency` (`resources/kanban_card/kanban_card_implementation.als:189`). |
| `ShapeAdmission(log, shape)`: the lifecycle's admission | 5 | Established for each adopter, the demand and the order among them. | `ShapeAdmission` (`meta/subject_log/lifecycle.als:80`). |
| `Tombstone(effect, shape)`: a retire keeps the state | 1 | Established for each adopter's effect. | `RetireEffect` (`meta/subject_log/lifecycle.als:64`). |
| `AffirmKeeps(effect, shape)`: an affirmation keeps the state | 1 | Discharged where the lemma is used (`src/meta/tests/affirm-tests.dfy:101`). | `AffirmEffect` (`meta/subject_log/affirm.als:35`). |
| `OneSamplePerInstant(ms)` | 2 | Established for the inventory item's metrics; assumed in the measurement lemmas. | `OneSamplePerInstant` (`meta/measurement/measurement.als:38`). The kept check `unit_meas_oneSamplePerInstant` guards it. |
| `Activated(alog, elog, lift)`: an effect cites an activation that precedes it | 1 | Established: appending an activation or an effect keeps it. | `OnlyActivationsAreCited` and `OnlyActivationsSelfCite` (`meta/activation/activation.als:58`, :60), with `ArcheOriginPrecedes` (`meta/occurrence/occurrence.als:55`). The check reads no verdict, so the conjunct on agreeing verdicts is not needed. |
| `WorldWellFormed(w)`: the world's citations | 3 | Established of the system's world by `SysWorldWellFormed`, from the three services' `Activated` and from five premises it assumes: the ticks and the ids of two services are disjoint, a caller is in the world, a caller in another service precedes, and the boundary's rows are origins. | Conjunct by conjunct. Ordered logs and disjoint ticks: `OneOccurrencePerTick` (`meta/occurrence/occurrence.als:40`). Disjoint ids: an occurrence cites its activation as an atom (`arche`, `meta/occurrence/occurrence.als:26`), so there is no id to bear twice. Callers cited: `OnlyActivationsAreCited` (`meta/activation/activation.als:58`). Citations precede: `ArcheOriginPrecedes` (`meta/occurrence/occurrence.als:55`), which the kept check `unit_occ_archeOriginPrecedes` guards. Only origins cite themselves: `OnlyActivationsSelfCite` (:60) with `origin` (:63). |
| `Time.Calendar(ps)`: the calendar axioms | 4 | Assumed. | The check states it: `calendarAxioms implies …` (`meta/time/time.als:46`). |
| `Nf(a)`: a keyed value is in normal form | 7 | Established where a value is computed; assumed of an argument. | Five checks state it: `nf[a] implies …` (`meta/keyed_value_algebra/keyed_monoid.als:31`). For the two checks of the running sum: `ChainWellFormed` (`meta/keyed_value_algebra/keyed_sum.als:34`). |
| `ClocksAligned(log, at)` | 1 | Assumed. | The check states it: `clocksAligned implies …` (`meta/occurrence/timed.als:25`). |
| `Aligned(log, at)` and `StrictChronology(log, at)` | 1 | Assumed. | The check states both: `(clocksAligned and strictChronology) implies …` (`resources/inventory_item/metrics.als:50`). |
| `ComputedFrom(c, s)` | 1 | The lemma's case. | The check states it: `computedFrom[c, s] implies …` (`shared/certainty/certainty.als:38`). |
| `Covers(sch, q)`: every unit of the quantity has a factor | 1 | Assumed. | The check's `hasGroup[sch, q]` with `ConvNodesWF` (`reference_data/item/uom_collapse.als:32`): a group that is present covers exactly its quantity's units, each configured in the scheme. |

**A module's own well-formedness, fact by fact.** The file is the module's implementation file unless the row says
otherwise.

| Module | Checks | Admission: each verdict is the guard's | Chaining and effect: the state the guard reads | Other conjuncts |
| --- | --- | --- | --- | --- |
| business affiliate | 7 | `BaAdmissionWitnessed` (`reference_data/business_affiliate/business_affiliate_implementation.als:51`) | `BaChain` (:20), `BaEffects` (:58) | |
| item | 6 | `ItemAdmissionWitnessed` (`reference_data/item/item_implementation.als:64`) | `ItemChain` (:19), `ItemEffects` (:73) | |
| staff | 4 | `StaffAdmissionWitnessed` (`reference_data/staff/staff_implementation.als:35`) | `StaffChain` (:15). The staff has no effect fact of its own: a staff record has no content that a write changes | |
| inventory item | 2 | `IIAdmissionWitness` (`resources/inventory_item/inventory_item_implementation.als:200`) | `IIChaining` (:50), `IIEffectWitness` (:229) | |
| inventory pool | 9 | `PoolAdmissionWitness` (`resources/inventory_item/inventory_pool.als:225`), `PoolAffirmWitness` (:224) | `PoolChaining` (:165), `PoolEffectWitness` (:234) | `TransferPairing`: the fact of the same name (:263) |
| kanban card | 15 | `CycleAdmissionWitness` (`resources/kanban_card/kanban_card_implementation.als:128`) | `CycleChain` (:25), `CycleEffectWitness` (:142) | |
| demand | 2 | `DemandAdmissionWitness` (`operations/demand/demand_implementation.als:340`) | `DemandChaining` (:29), `PDChaining` (:30), `DemandEffectWitness` (:398) | `CreatePaired`, `RevokePaired` and `HalvesUnique`: `CreateComposesWithRecord` (:38) and `RevokeComposesWithExtract` (:39), each of which pairs a delivery's row with exactly one row of the demand |
| order | 3 | `OrderAdmissionWitness` (`procurement/order/order_implementation.als:255`) | `OrderChaining` (:30), `LineChaining` (:31), `OrderEffectWitness` (:314) | |

**Not checked by this table:** that each guard and each effect of the Alloy model equals the Dafny one arm by arm.
That is the mirror itself, kept by the finders of each refusal and by the pointer check, not by this record.

## `meta/activation`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_act_callersPrecede` | `activation.als` | `CiteNotAfter` | `src/meta/activation.dfy:366` | `WorldWellFormed(w) && InWorld(w, t)` | reading | P: in a well-formed world a row's cited tick is not after its own (CiteNotAfter), and only an origin cites its own tick (the conjunct OnlyOriginsSelfCite of WorldWellFormed, which SysWorldWellFormed proves of the system's world). Q: a non-origin activation's cited tick is strictly before its own. P implies Q: a non-origin's cited tick is not its own, so 'not after' is 'before'. The world's premise that a caller in another service precedes (CrossCallersPrecede) is Alloy's fact ArcheOriginPrecedes, which the KEPT check unit_occ_archeOriginPrecedes guards. |
| `unit_act_callersPrecede` | `activation.als` | `SysWorldWellFormed` | `src/system/system-activations.dfy:561` | `SysActivated(w, a) && BoundaryWF(b) && SkeletonsDefined(w, a, b)`, and `ServicesTicksDisjoint(w, a, b) && ServicesIdsDisjoint(a, b) && CallersInWorld(a, b) && CrossCallersPrecede(a, b)` | the audit of 2026-11-18 | See the first row of this check. |
| `unit_act_effectsFollow` | `activation.als` | `ActivationPrecedes` | `src/meta/activation.dfy:188` | `Activated(alog, elog, lift) && i < \|elog\|` | reading | P: under Activated, every effect row's activation exists and its tick is strictly before the effect's. Q: every effect of the test's two services strictly follows its activation. P implies Q: it is the same statement, for every effect log; the premise Activated is the model's well-formedness of the two logs. |
| `unit_act_noProperCycle` | `activation.als` | `NoProperCycle` | `src/meta/activation.dfy:392` | `WorldWellFormed(w) && Walk(w, path) && \|path\| >= 2 && path[0] == path[\|path\| - 1]` | the name | P: a walk of two or more rows that returns to its start starts at an activation citing itself (an origin). Q: an occurrence that reaches itself along the citations is an origin. P implies Q: `o in o.^arche` is such a walk. P's premise WorldWellFormed is implied by Alloy's facts OneOccurrencePerTick, OnlyActivationsAreCited, OnlyActivationsSelfCite and ArcheOriginPrecedes (the premise table). |

## `meta/keyed_value_algebra`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_alg_addAssociative` | `keyed_monoid.als` | `AddAssociative` | `src/meta/keyed-algebra.dfy:115` | none | the name | P: Add is associative for all keyed values. Q: under the ring axioms, add is associative on normal-form values. P implies Q: the same law, without Q's normal-form restriction. |
| `unit_alg_addClosedNf` | `keyed_monoid.als` | `AddClosedNf` | `src/meta/keyed-algebra.dfy:88` | none | the name | P: Add(a, b) is in normal form, for all a and b. Q: the sum of two normal-form values is in normal form. P implies Q: the same conclusion with no premise. |
| `unit_alg_addCommutative` | `keyed_monoid.als` | `AddCommutative` | `src/meta/keyed-algebra.dfy:101` | none | the name | P: Add(a, b) == Add(b, a) for all keyed values. Q: the same on normal-form values, under the ring axioms. P implies Q. |
| `unit_alg_addIdentity` | `keyed_monoid.als` | `AddIdentity` | `src/meta/keyed-algebra.dfy:108` | `Nf(a)` | the name | P: for a normal-form a, Add(a, Zero()) == a. Q: the same, under the ring axioms. The same statement. |
| `unit_alg_addInverse` | `keyed_monoid.als` | `AddInverse` | `src/meta/keyed-algebra.dfy:126` | none | the name | P: Add(a, Negate(a)) == Zero() for all a. Q: the same on normal-form values. P implies Q. |
| `unit_alg_scaleDistribAdd` | `keyed_monoid.als` | `ScaleDistribAdd` | `src/meta/keyed-algebra.dfy:156` | none | the name | P: Scale(s, Add(a, b)) == Add(Scale(s, a), Scale(s, b)) for all s, a, b. Q: the same on normal-form values, under the ring axioms. P implies Q. |
| `unit_alg_scaleOneIdentity` | `keyed_monoid.als` | `ScaleOneIdentity` | `src/meta/keyed-algebra.dfy:139` | `Nf(a)` | the name | P: for a normal-form a, Scale(SOne, a) == a. Q: the same. The same statement. |
| `unit_alg_scaleZeroScalar` | `keyed_monoid.als` | `ScaleZeroScalar` | `src/meta/keyed-algebra.dfy:135` | none | the name | P: Scale(SZero, a) == Zero() for all a. Q: the same. The same statement. |
| `unit_ord_lteAntisymmetric` | `keyed_order.als` | `LteAntisymmetric` | `src/meta/keyed-algebra.dfy:209` | `Nf(a) && Nf(b) && Lte(a, b) && Lte(b, a)` | the name | P: normal-form a, b with Lte(a, b) and Lte(b, a) are equal. Q: the same. The same statement. |
| `unit_ord_lteReflexive` | `keyed_order.als` | `LteReflexive` | `src/meta/keyed-algebra.dfy:165` | none | the name | P: Lte(a, a) for all a. Q: the same. The same statement. |
| `unit_ord_lteTransitive` | `keyed_order.als` | `LteTransitive` | `src/meta/keyed-algebra.dfy:167` | `Lte(a, b) && Lte(b, c)` | the name | P: Lte(a, b) and Lte(b, c) give Lte(a, c). Q: the same. The same statement. |
| `unit_ord_positiveIsAboveZero` | `keyed_order.als` | `PositiveIsAboveZero` | `src/meta/keyed-algebra.dfy:215` | `Nf(a)` | the name | P: for a normal-form a, Classify(a) == POSITIVE exactly when a is not zero and Lte(Zero(), a). Q: the same. The same statement. |
| `unit_ord_semEqualIffLexical` | `keyed_order.als` | `SemEqualIffLexical` | `src/meta/keyed-algebra.dfy:246` | `Nf(a) && Nf(b)` | the name | P: for normal-form a, b, SemanticEq(a, b) == EQUAL exactly when they are structurally equal. Q: the same. The same statement. |
| `unit_ord_semUnequalImpliesDifferent` | `keyed_order.als` | `SemUnequalImpliesDifferent` | `src/meta/keyed-algebra.dfy:252` | `SemanticEq(a, b) == UNEQUAL` | the name | P: SemanticEq(a, b) == UNEQUAL gives a != b. Q: the same. The same statement. |
| `unit_sum_baseIsVal` | `keyed_sum.als` | `BaseIsVal` | `src/meta/keyed-sum.dfy:46` | `\|vals\| > 0 && Nf(vals[0])` | the name | P: for a non-empty sequence whose first value is in normal form, Cum(vals, 0) == vals[0]. Q: at the head the running total is the node's value. P implies Q: Alloy's fact ChainWellFormed puts every value in normal form, which is P's premise. |
| `unit_sum_cumNf` | `keyed_sum.als` | `SumNf` | `src/meta/keyed-sum.dfy:41` | none | reading | P: Sum(vals) is in normal form for every sequence. Q: the running total at every node is in normal form. P implies Q: Cum(vals, i) is Sum(vals[..i+1]) by definition, a sequence. |
| `unit_sum_stepFolds` | `keyed_sum.als` | `StepFolds` | `src/meta/keyed-sum.dfy:56` | `0 < i < \|vals\|` | the name | P: at every index after the first, the running total is the total at the index before plus the value at the index (`Cum(vals, i) == Add(Cum(vals, i - 1), vals[i])`). Q: at a node with an earlier one, the running total is the earlier total plus the node's value. The same statement. |
| `unit_sum_telescope` | `keyed_sum.als` | `AddCommutative` | `src/meta/keyed-algebra.dfy:101` | none | the audit of 2026-11-18 | Q, with Alloy's rangeSum unfolded, is: A + (B + (-A)) = B, for A the running total before m and B the total at the last node. P: Add is commutative and associative, Add(a, Negate(a)) == Zero(), and Add(b, Zero()) == b for a normal-form b; every total is in normal form (SumNf). P implies Q: A + (B + (-A)) = (A + (-A)) + B = Zero + B = B. KeyedSum.Telescope states the same fact for Dafny's range sum, which is the direct sum of the sub-chain and not Alloy's difference of two totals. |
| `unit_sum_telescope` | `keyed_sum.als` | `AddAssociative` | `src/meta/keyed-algebra.dfy:115` | none | the audit of 2026-11-18 | See the first row of this check. |
| `unit_sum_telescope` | `keyed_sum.als` | `AddInverse` | `src/meta/keyed-algebra.dfy:126` | none | the audit of 2026-11-18 | See the first row of this check. |
| `unit_sum_telescope` | `keyed_sum.als` | `AddIdentity` | `src/meta/keyed-algebra.dfy:108` | `Nf(a)` | the audit of 2026-11-18 | See the first row of this check. |
| `unit_sum_telescope` | `keyed_sum.als` | `SumNf` | `src/meta/keyed-sum.dfy:41` | none | the audit of 2026-11-18 | See the first row of this check. |

## `meta/measurement`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_meas_countMatches` | `measurement.als` | `CountMatches` | `src/meta/measurement.dfy:190` | none | the name | P: `CountIn(ms, s, p)` is the size of `MeasurementsIn(ms, s, p)`. Q: countIn is the number of in-period samples. The same statement; definitional on both sides. |
| `unit_meas_lastIsSampled` | `measurement.als` | `LastIsSampled` | `src/meta/measurement.dfy:168` | `OneSamplePerInstant(ms) && MeasurementsIn(ms, s, p) != {}` | the lemma's own `Alloy:` pointer | P: under OneSamplePerInstant, in a non-empty period LastValueIn is defined and is the value of some in-period measurement. Q: in a non-empty period the last value is one of the sampled values. The same statement. P's premise is what the KEPT check unit_meas_oneSamplePerInstant shows of Alloy's facts. |

## `meta/model_time`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_mt_strict` | `model_time.als` | `Strict` | `src/meta/model-time.dfy:34` | none | the audit of 2026-11-18 | P: !Precedes(a, a), and Precedes(a, b) implies !Precedes(b, a). Q: precedes is irreflexive and asymmetric. The same statement. The recorded pairing was wrong: a stem matched across modules. |
| `unit_mt_total` | `model_time.als` | `Total` | `src/meta/model-time.dfy:29` | `a != b` | the lemma's own `Alloy:` pointer | P: two distinct ticks are comparable by Precedes. Q: the same. The same statement. |
| `unit_mt_transitive` | `model_time.als` | `Transitive` | `src/meta/model-time.dfy:38` | `Precedes(a, b) && Precedes(b, c)` | the name | P: Precedes(a, b) and Precedes(b, c) give Precedes(a, c). Q: the same. The same statement. |
| `unit_mt_vocabulary` | `model_time.als` | `Vocabulary` | `src/meta/model-time.dfy:43` | none | the name | P: Follows is the converse of Precedes, and NotAfter is Precedes or equal. Q: the same two equivalences. The same statement. |

## `meta/occurrence`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_occ_archeNoProperCycle` | `occurrence.als` | `NoProperCycle` | `src/meta/activation.dfy:392` | `WorldWellFormed(w) && Walk(w, path) && \|path\| >= 2 && path[0] == path[\|path\| - 1]` | reading | P: a closed walk of two or more rows starts at a row whose cited tick is its own. Q: an occurrence that reaches itself along the citations cites itself. P implies Q: `o in o.^arche` is such a walk, and citing one's own tick is citing oneself (one row per tick). P's premise WorldWellFormed is implied by Alloy's facts OneOccurrencePerTick, OnlyActivationsAreCited, OnlyActivationsSelfCite and ArcheOriginPrecedes (the premise table). |
| `unit_occ_total` | `occurrence.als` | `Total` | `src/meta/model-time.dfy:29` | `a != b` | the lemma's own `Alloy:` pointer | P: two distinct ticks are comparable by Precedes. Q: two distinct occurrences are comparable by their ticks. P implies Q where distinct occurrences have distinct ticks, which Alloy holds as the fact OneOccurrencePerTick (meta/occurrence/occurrence.als:40); the KEPT check unit_occ_onePerTick guards it. |
| `unit_timed_alignedForbidsBackdating` | `timed.als` | `AlignedForbidsBackdating` | `src/meta/occurrence-timed.dfy:34` | `ClocksAligned(log, at) && i < j < \|log\| && at(log[i]).Some? && at(log[j]).Some?` | the lemma's own `Alloy:` pointer | P: under ClocksAligned, a later row's stamp is not earlier than an earlier row's. Q: under clocksAligned, no occurrence that precedes another carries a later stamp. The same statement under the same premise. |

## `meta/principal`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_principal_recoverable` | `principal.als` | `Recoverable` | `src/meta/principal.dfy:57` | `NamesUnique(ps) && i < \|ps\|` | the name | P: under NamesUnique, PrincipalNamed(ps, ps[i].name) == Some(ps[i]). Q: principalNamed[p.name] = p. The same statement. P's premise NamesUnique is what the KEPT check unit_principal_nameIsKey shows of Alloy's facts. |
| `unit_principal_resolvesAsEntity` | `principal.als` | `ResolvesAsEntity` | `src/meta/principal.dfy:47` | `Keyed(u) && p.entity.eId in u && u[p.entity.eId] == p.entity` | the lemma's own `Alloy:` pointer | P: in a keyed universe that files the principal's entity, Resolve(u, id) is that entity. Q: resolve[p.eId] = p. The same statement. P's premise Keyed is what the KEPT check unit_kernel_eIdIsKey shows of Alloy's facts. |

## `meta/profiles`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_prof_premisesInForce` | `profiles.als` | `DomainLogPremises` | `src/meta/profiles.dfy:41` | none | reading | P: for Dafny's scalar, SPlus(a, SZero) == a (with commutativity, the inverse, and the order's totality), proven. Q: a.splus[SZero] = a for the profile's scalar, which Alloy's fact DomainLogPremises declares. The same law: Dafny proves it where Alloy assumes it; the lemma's docstring names this check. |

## `meta/scalar`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_scalar_addInverse` | `scalar.als` | `GroupAxioms` | `src/meta/scalar.dfy:35` | none | reading | P: SPlus(a, SNeg(a)) == SZero, with the other group laws. Q: under the ring axioms, a + (-a) = 0. The same law; Q's premise includes it. |
| `unit_scalar_distributes` | `scalar.als` | `RingAxioms` | `src/meta/scalar.dfy:42` | none | reading | P: SMul(a, SPlus(b, c)) == SPlus(SMul(a, b), SMul(a, c)), with the other ring laws. Q: under the ring axioms, multiplication distributes over addition. The same law. |
| `unit_scalar_zeroNeOne` | `scalar.als` | `RingAxioms` | `src/meta/scalar.dfy:42` | none | reading | P: SZero != SOne. Q: under the ring axioms, SZero != SOne. The same statement. |

## `meta/subject_log`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_aff_lastTouchMoves` | `affirm.als` | `LastTouchMoves` | `src/meta/affirm.dfy:64` | `i < \|log\| && Committed(log[i])` | the name | P: for any committed row i, LastTouch(log[..i+1], its subject) is that row. Q: a committed affirmation is the last touch of its subject at its tick. P implies Q: P holds of every committed row, an affirmation among them. |
| `unit_aff_neverCommitsStale` | `affirm.als` | `NeverCommitsStale` | `src/meta/affirm.dfy:73` | `AffirmViol(prefix, shape, s, pre, affirmed, rNotCreated, rClosed, rStale) == {}` | the name | P: a row whose affirm arm raises nothing found a state, and the affirmed version is that state. Q: a committed affirmation's affirmed record is its pre. The same statement: committed means the guard's arm raised nothing. |
| `unit_aff_nothingAfterRetire` | `affirm.als` | `NothingAfterRetire` | `src/meta/trace.dfy:482` | `ShapeAdmission(log, shape) && i < \|log\| && Committed(log[i])` | the audit of 2026-11-18 | P: under ShapeAdmission, a committed row's subject was not retired in the prefix before it. Q: no committed occurrence has a committed retire of its subject before it (lc/nothingAfterRetire, here on the affirm root). The same statement, in the generic kit this root tests. ShapeAdmission is what each adopter proves of its guard. |
| `unit_aff_recordUnchanged` | `affirm.als` | `StateUnchanged` | `src/meta/affirm.dfy:54` | `AffirmKeeps(effect, shape) && i < \|log\| && Committed(log[i]) && shape(log[i].kind) == Affirm && StateAt(log[..i], log[i].subject, effect).Some?` | reading | P: for a committed affirmation on a subject with a state, under AffirmKeeps (the effect keeps the state on an affirmation), the state right after it is the state before it. Q: a committed affirmation's post is its pre, and the as-of read at its tick is its pre. P implies Q: in Dafny the post and the as-of read at the row's tick are the one fold StateAt(log[..i+1]); the state exists by NeverCommitsStale. |
| `unit_lc_createIsFirst` | `lifecycle.als` | `CreateIsFirst` | `src/meta/trace.dfy:497` | `ShapeAdmission(log, shape) && i < \|log\| && Committed(log[i]) && shape(log[i].kind) == Create` | the name | P: under ShapeAdmission, a committed create's subject has no committed row before it. Q: a committed create is not started before. The same statement. |
| `unit_lc_mutateHasPre` | `lifecycle.als` | `MutateHasState` | `src/meta/trace.dfy:502` | `ShapeAdmission(log, shape) && i < \|log\| && Committed(log[i]) && shape(log[i].kind) != Create && shape(log[i].kind) != Affirm` | reading | P: under ShapeAdmission, a committed row that is neither a create nor an affirmation found a state. Q: a committed mutation has a pre. P implies Q: a mutation is such a row. |
| `unit_lc_noRecordedRefusalWithoutGenesis` | `lifecycle.als` | `NoRecordedRefusalWithoutGenesis` | `src/meta/trace.dfy:527` | `i < \|log\| && Recorded(log, shape, i) && !Committed(log[i])` | the audit of 2026-11-18 | P: a recorded row that did not commit sits on a subject started before it. Q: a recorded occurrence that is not committed is started before. The same statement, in the generic kit this root tests. |
| `unit_lc_nothingAfterRetire` | `lifecycle.als` | `NothingAfterRetire` | `src/meta/trace.dfy:482` | `ShapeAdmission(log, shape) && i < \|log\| && Committed(log[i])` | the audit of 2026-11-18 | P: under ShapeAdmission, a committed row's subject was not retired in the prefix before it. Q: no committed occurrence has a committed retire of its subject before it. The same statement, in the generic kit this root tests. |
| `unit_lc_tombstone` | `lifecycle.als` | `RetireKeepsState` | `src/meta/trace.dfy:510` | `ShapeAdmission(log, shape) && Tombstone(effect, shape) && i < \|log\| && Committed(log[i]) && shape(log[i].kind) == Retire` | reading | P: under ShapeAdmission and Tombstone(effect, shape), the state right after a committed retire is the state before it. Q: a committed retire's post is its pre, and the as-of read at its tick is its pre. P implies Q: in Dafny the post and the as-of read at the row's tick are the one fold StateAt(log[..i+1]). Each adopter proves Tombstone of its effect (TombstoneEffect). |
| `unit_slog_firstReadsNothing` | `subject_log.als` | `FirstReadsNothing` | `src/meta/tests/trace-tests.dfy:147` | `i < \|log\| && !StartedBefore(log[..i], log[i].subject)` | the name | P: a row whose subject has no committed row before it reads no state (FirstReadsNothing, for the kit's test adopter); a state is defined exactly when the subject has committed history (StateIffStarted, for every log). Q: an occurrence with no prior on its subject has no pre. The same statement. |
| `unit_slog_firstReadsNothing` | `subject_log.als` | `StateIffStarted` | `src/meta/trace.dfy:285` | none | the audit of 2026-11-18 | See the first row of this check. |
| `unit_slog_locf` | `subject_log.als` | `Locf` | `src/meta/tests/trace-tests.dfy:153` | `i < \|log\| && Committed(log[i])` | the name | Q: the as-of read at a committed occurrence's tick is its post. In Dafny the post of row i is by definition that read (`PostOf(log, i)` is `StateAt(log[..i+1])`), and P states its value: the effect of the row's kind on the state it read. P implies Q: a committed row is the last touch at its tick (LastTouchMoves), so the read at its tick is the read right after it. |
| `unit_slog_locf` | `subject_log.als` | `LastTouchMoves` | `src/meta/affirm.dfy:64` | `i < \|log\| && Committed(log[i])` | the audit of 2026-11-18 | See the first row of this check. |
| `unit_slog_recordIsFunctionOnceStarted` | `subject_log.als` | `StateIffStarted` | `src/meta/trace.dfy:285` | none | reading | P: StateAt(log, s) is defined exactly when s has committed history in the log. Q: a started subject has exactly one record at a tick, and a subject not started has none. P implies Q: StateAt is a function, so it gives at most one record, and P says when it gives one; a read at a tick is StateAt of the prefix up to it. |
| `unit_slog_refusalContributesNothing` | `subject_log.als` | `RefusalContributesNothing` | `src/meta/tests/trace-tests.dfy:159` | `i < \|log\| && Refused(log[i])` | the name | P: for a refused row i, every subject's state after it is its state before it. Q: at a refused occurrence's tick the record is the post of the last committed occurrence, which is committed or absent. P implies Q: the refused row leaves the fold as the last committed row left it. |
| `unit_slog_threadIsCommitted` | `subject_log.als` | `ThreadIsCommitted` | `src/meta/tests/trace-tests.dfy:165` | `i < \|log\| && PreOf(log, i).Some?` | the name | P: a row that reads a state has a committed earlier row on its subject whose post is that state. Q: an occurrence with a pre has a committed prior. P implies Q. |

## `meta/time`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_duration_antisym` | `duration.als` | `DurationOrder` | `src/meta/time.dfy:160` | none | reading | P's second clause: DAtOrBefore(a, b) and DAtOrBefore(b, a) give a == b. Q: the same. The same statement. |
| `unit_duration_total` | `duration.als` | `DurationOrder` | `src/meta/time.dfy:160` | none | the audit of 2026-11-18 | P's first clause: DAtOrBefore(a, b) or DAtOrBefore(b, a). Q: any two durations are comparable. The same statement. The recorded lemmas were of other modules: a stem matched across modules. |
| `unit_duration_transitive` | `duration.als` | `DurationOrder` | `src/meta/time.dfy:160` | none | reading | P's third clause: DAtOrBefore is transitive. Q: the same. The same statement. |
| `unit_time_elapsedWhenOrdered` | `time.als` | `ElapsedWhenOrdered` | `src/meta/time.dfy:153` | none | the name | P: DurationBetween(a, b) is defined exactly when AtOrBefore(a, b). Q: the same, under the duration axioms, which state it. The same law: Dafny proves it of its metric where Alloy assumes it. |
| `unit_time_nonEmptyHasEndpoints` | `time.als` | `NonEmptyHasEndpoints` | `src/meta/time.dfy:144` | `ts != {}` | the name | P: a non-empty set of instants has an Earliest and a Latest. Q: the same. The same statement. |
| `unit_time_total` | `time.als` | `Total` | `src/meta/time.dfy:132` | none | the audit of 2026-11-18 | P: AtOrBefore(a, b) or AtOrBefore(b, a) for any two instants. Q: the same. The same statement. |
| `unit_time_withinBounds` | `time.als` | `WithinBounds` | `src/meta/time.dfy:149` | none | the name | P: Within(t, i) exactly when the interval's ends bound t. Q: the same. The same statement, definitional on both sides. |
| `unit_time_zeroAtPoint` | `time.als` | `ZeroAtPoint` | `src/meta/time.dfy:151` | none | the name | P: DurationBetween(a, a) == Some(ZeroDuration). Q: the same, under the duration axioms, which state it. The same law: Dafny proves it of its metric. |

## `operations/demand`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `int_dem_contract_cycleIndivisible` | `demand.als` | `CycleIndivisible` | `src/operations/demand/demand-contract.dfy:886` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && d1 in DemandOf(log, c) && d2 in DemandOf(log, c)` | the lemma's own `Alloy:` pointer | P: in a well-formed world, two demands that hold a cycle are the same demand. Q: at every tick a cycle has at most one demand, on the composed stack. P implies Q: P holds of every well-formed log, so of the prefix at each tick; Dafny's WellFormed takes the real lower logs, as the integration root does. |
| `int_dem_contract_frozenOutsideOpen` | `demand.als` | `FrozenOutsideOpen` | `src/operations/demand/demand-contract.dfy:894` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && IsMutator(log[i].kind)` | the lemma's own `Alloy:` pointer | P: a committed contribution mutator read a state whose status is OPEN. Q: the same, on the composed stack. The same statement; Dafny's WellFormed takes the real lower logs. |

## `procurement/order`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `int_ord_contract_demandIndivisible` | `order.als` | `DemandIndivisible` | `src/procurement/order/order-contract.dfy:640` | `WellFormed(olog, llog, dlog, items, ba, staff) && KeyedOrders(olog)`, and `l1 in HoldingLineOf(PrefixUpTo(olog, t), PrefixUpTo(llog, t), PrefixUpTo(dlog, t), d)`, and `l2 in HoldingLineOf(PrefixUpTo(olog, t), PrefixUpTo(llog, t), PrefixUpTo(dlog, t), d)` | the lemma's own `Alloy:` pointer | P: as of a tick, two lines that hold a demand are the same line. Q: at every tick a demand has at most one holding line, on the composed stack. The same statement. P's premise KeyedOrders is Alloy's kernel fact EntityIdIsKey; both sides assume it. |
| `int_ord_contract_frozenOutsideDraft` | `order.als` | `FrozenOutsideDraftOrder` | `src/procurement/order/order-contract.dfy:623` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && IsOrderStructural(olog[i].kind)` | the lemma's own `Alloy:` pointer | P: a committed structural change of an order read it DRAFT; a committed structural change of a line found its parent order DRAFT as of its tick. Q: the same two clauses, on the composed stack. The same statement. The line clause's premise KeyedOrders is Alloy's kernel fact EntityIdIsKey. |
| `int_ord_contract_frozenOutsideDraft` | `order.als` | `FrozenOutsideDraftLine` | `src/procurement/order/order-contract.dfy:630` | `WellFormed(olog, llog, dlog, items, ba, staff) && KeyedOrders(olog) && i < \|llog\| && Committed(llog[i]) && IsLineStructural(llog[i].kind)`, and `o in ParentsOf(PrefixBefore(olog, llog[i].tick), llog[i].subject)` | the lemma's own `Alloy:` pointer | See the first row of this check. |
| `unit_ordr_receivedIsAccumulated` | `order_received.als` | `ReceivedIsAccumulated` | `src/procurement/order/order-contract.dfy:688` | `WellFormed(olog, llog, dlog, items, ba, staff) && n <= \|llog\|` | the name | P: for every line and every prefix of the line log, the stored sReceived is the sum of its committed receipts minus the sum of its reversals. Q: the same at every tick, written case by case for up to two postings. P implies Q: P holds for any number of postings. |
| `unit_ordr_receivedIsAccumulated` | `order_received.als` | `ReceivedIsAccumulated` | `src/procurement/order/order.dfy:1097` | none | the name | See the first row of this check. |

## `reference_data/business_affiliate`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_ba_committedStatesAgreeOnKind` | `business_affiliate.als` | `RoleKindFixedAtBirthHolds` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:272` | `WellFormed(log) && i < \|log\| && Committed(log[i])` | reading | P's second clause: every version in a committed row's post state states its identity's kind. Q: the same. The same statement. |
| `unit_ba_lifecycleShape` | `business_affiliate.als` | `BaLifecycleShape` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:251` | `WellFormed(log) && i < \|log\| && Committed(log[i])` | the lemma's own `Alloy:` pointer | P: a committed row is the first on its affiliate exactly when it is a Create, and a prior head is never a retire. Q: the same two clauses. The same statement. |
| `unit_ba_nothingAfterRetire` | `business_affiliate.als` | `BaNothingAfterRetire` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:264` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer | P: of two committed rows on one affiliate, the earlier is not a retire. Q: no committed row of an affiliate follows its committed retire. The same statement. |
| `unit_ba_oneVersionPerRole` | `business_affiliate.als` | `RoleIdsAreKeysHolds` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:281` | `WellFormed(log)` | the lemma's own `Alloy:` pointer | P: a payload holds at most one version per role identity (it is a map keyed by the identity, so by the type), and in a well-formed log a role id names one role across all rows. Q: no committed write and no committed post state holds two versions of one role identity. P implies Q: every write and state is such a payload. In Dafny the first half holds by the type; the lemma states it for the catalog. |
| `unit_ba_oneVersionPerRole` | `business_affiliate.als` | `OneVersionPerRoleHolds` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:288` | none | the lemma's own `Alloy:` pointer | See the first row of this check. |
| `unit_ba_retireIsTombstone` | `business_affiliate.als` | `BaRetireIsTombstone` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:293` | `WellFormed(log) && i < \|log\| && Committed(log[i]) && log[i].kind.RetireBa?` | reading | P: a committed retire's post state is its pre state, and the affiliate is not live after it. Q: the same. The same statement. |
| `unit_ba_roleKindFixedAtBirth` | `business_affiliate.als` | `RoleKindFixedAtBirthHolds` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:272` | `WellFormed(log) && i < \|log\| && Committed(log[i])` | the lemma's own `Alloy:` pointer | P: every version a committed write states, and every version a committed post state holds, states its identity's kind. Q: every committed role version states its identity's kind. The same statement. |
| `unit_ba_roleKindFixedAtBirth` | `business_affiliate.als` | `RoleIdsAreKeysHolds` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:281` | `WellFormed(log)` | the lemma's own `Alloy:` pointer | See the first row of this check. |
| `unit_ba_roleOwnership` | `business_affiliate.als` | `RoleOwnershipHolds` | `src/reference-data/business-affiliate/business-affiliate-contract.dfy:244` | `WellFormed(log)` | the lemma's own `Alloy:` pointer | P: a well-formed log owns its roles: no role belongs to two affiliates. Q: no role is among two affiliates' committed roles. The same statement. |

## `reference_data/item`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_item_eachConfigured` | `item.als` | `EachConfigured` | `src/reference-data/item/uom.dfy:48` | none | the lemma's own `Alloy:` pointer | P: every well-formed scheme has Each among its units with factor one. Q: every scheme configures Each with factor one. The same statement. In Dafny the scheme is a subset type, so the verifier enforces it wherever a scheme is built; in Alloy it is the fact UomSchemeWF. |
| `unit_item_lifecycleShape` | `item.als` | `ItemLifecycleShape` | `src/reference-data/item/item-contract.dfy:266` | `WellFormed(log, ba) && i < \|log\| && Committed(log[i])` | the lemma's own `Alloy:` pointer | P: a committed row is the first on its item exactly when it is a Create, and a prior head is never a retire. Q: the same two clauses. The same statement. |
| `unit_item_nothingAfterRetire` | `item.als` | `ItemNothingAfterRetire` | `src/reference-data/item/item-contract.dfy:278` | `WellFormed(log, ba) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer | P: of two committed rows on one item, the earlier is not a retire. Q: no committed row of an item follows its committed retire. The same statement. |
| `unit_item_retireIsTombstone` | `item.als` | `ItemRetireIsTombstone` | `src/reference-data/item/item-contract.dfy:284` | `WellFormed(log, ba) && i < \|log\| && Committed(log[i]) && log[i].kind.RetireItem?` | reading | P: a committed retire's post state is its pre state, and the item is not live after it. Q: the same. The same statement. |
| `unit_item_supplyOwnership` | `item.als` | `SupplyOwnershipHolds` | `src/reference-data/item/item-contract.dfy:252` | `WellFormed(log, ba)` | the lemma's own `Alloy:` pointer | P: in a well-formed log every supply belongs to exactly one item. Q: no supply is among two items' committed supplies. The same statement. |
| `unit_item_supplyPinCurrencyHolds` | `item.als` | `SupplierPinsSoundHolds` | `src/reference-data/item/item-contract.dfy:259` | `WellFormed(log, ba) && StrictTicks(ba)` | reading | P's second clause (SupplyPinCurrency): every supply's vendor pin was current at its write. Q: every committed write's vendor pins are current at its tick. The same statement. P's premise StrictTicks(ba) is the affiliate log's own order. |
| `unit_item_toEachIdentity` | `item.als` | `ToEachIdentity` | `src/reference-data/item/uom.dfy:50` | none | the audit of 2026-11-18 | P: for a well-formed scheme, ToEach(s, Each, amt) == Some(amt). Q: under the ring axioms, converting an amount already in each returns it. The same statement. EachConfigured alone says the factor is one, not that the conversion is the identity. |
| `unit_collapse_eachIdentity` | `uom_collapse.als` | `EachIdentity` | `src/reference-data/item/uom-collapse.dfy:79` | `q.Keys == {Each}` | the name | P: collapsing a quantity whose only key is Each returns it unchanged. Q: for such a quantity the collapse's Each amount is the quantity's. P implies Q. Alloy's premise hasGroup says its fold nodes exist for the pair; Dafny's Collapse is a total function. |
| `unit_collapse_eachKeyed` | `uom_collapse.als` | `EachKeyed` | `src/reference-data/item/uom-collapse.dfy:69` | none | the name | P: Collapse(sch, q)'s keys are within {Each}, and it is in normal form. Q: the collapse's keys are within Each. P implies Q. |
| `unit_collapse_singleIsToEach` | `uom_collapse.als` | `SingleIsToEach` | `src/reference-data/item/uom-collapse.dfy:71` | `q.Keys == {u} && u in sch.factor` | the name | P: collapsing a quantity with one unit the scheme configures gives ToEach of its amount, keyed by Each. Q: the same. The same statement. |
| `unit_collapse_twoUnitFolds` | `uom_collapse.als` | `TwoUnitFolds` | `src/reference-data/item/uom-collapse.dfy:89` | `q.Keys == {u1, u2} && u1 != u2 && Covers(sch, q)` | the name | P: for a quantity with two units the scheme covers, the Each total is the sum of the two converted amounts, and when it is not zero the collapse is that total keyed by Each. Q: when the two-unit collapse has an Each amount, it is that sum. P implies Q. |

## `reference_data/shared`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_shared_supplierIsVendor` | `shared.als` | `SupplierIsVendor` | `src/reference-data/shared/tests/shared-tests.dfy:70` | `IM.WellFormed(log, ba) && StrictTicks(ba) && s in AllSupplies(log) && s.supplierRole.Some?` | the name | P: in a well-formed world a supply's supplier role, when present, has a pin whose pinned version holds that role as a VENDOR role. Q: a committed write's supply with a role has it among the pinned version's roles, and it is a VENDOR role. The same statement. The lemma is proven in the tests module, for every well-formed world. |

## `reference_data/staff`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_staff_nothingAfterRetire` | `staff.als` | `StaffNothingAfterRetire` | `src/reference-data/staff/staff-contract.dfy:151` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer | P: of two committed rows on one staff member, the earlier is not a retire. Q: no committed row of a staff member follows its committed retire. The same statement. |
| `unit_staff_retireIsTombstone` | `staff.als` | `StaffRetireIsTombstone` | `src/reference-data/staff/staff-contract.dfy:157` | `WellFormed(log) && i < \|log\| && Committed(log[i]) && log[i].kind.RetireStaff?` | reading | P: a committed retire's post state is its pre state, and the staff member is not live after it. Q: the same. The same statement. |
| `unit_stf_lifecycleShape` | `staff.als` | `StaffLifecycleShape` | `src/reference-data/staff/staff-contract.dfy:139` | `WellFormed(log) && i < \|log\| && Committed(log[i])` | the lemma's own `Alloy:` pointer | P: a committed row is the first on its staff member exactly when it is a Create, and a prior head is never a retire. Q: the same two clauses. The same statement. |
| `unit_stf_nameUniqueInTenant` | `staff.als` | `StaffNameUniqueHolds` | `src/reference-data/staff/staff-contract.dfy:133` | `WellFormed(log)` | the lemma's own `Alloy:` pointer | P: in a well-formed log two different staff members of one tenant never share a name. Q: two created members of one tenant have different names. The same statement. |

## `resources/inventory_item`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `int_ii_contract_closureIsTerminal` | `inventory_item.als` | `ClosureIsTerminal` | `src/resources/inventory-item/inventory-item-contract.dfy:330` | `WellFormed(log, items) && n1 <= n2 <= \|log\| && Started(log[..n1], ii) && !LiveAt(log[..n1], ii)` | the lemma's own `Alloy:` pointer | P: an inventory item started and not live in a prefix is not live in any longer prefix. Q: an inventory item with a state and not live at a tick is not live at any later tick, on the composed stack. The same statement. |
| `int_ii_contract_stateFunction` | `inventory_item.als` | `StateIsFunctionOnceStarted` | `src/resources/inventory-item/inventory-item-contract.dfy:313` | `WellFormed(log, items) && n1 <= n2 <= \|log\| && StateAt(log[..n1], ii).Some?` | the lemma's own `Alloy:` pointer | P: an inventory item with a state in a prefix has one in every longer prefix. Q: the same, by ticks, on the composed stack. The same statement. |
| `unit_pool_homogeneous` | `inventory_pool.als` | `PoolMembersAgree` | `src/resources/inventory-item/inventory-pool-contract.dfy:382` | `WellFormed(log)` | the lemma's own `Alloy:` pointer | P: in a well-formed pool log every held item agrees with its pool on the item and on the tenant. Q: every item a pool holds at a tick is of the pool's item. P implies Q: Q is P's item clause. |
| `unit_pool_membershipExclusive` | `inventory_pool.als` | `PoolMembershipExclusive` | `src/resources/inventory-item/inventory-pool-contract.dfy:388` | `WellFormed(log)` | the lemma's own `Alloy:` pointer | P: in a well-formed pool log an inventory item is held by at most one pool, with transfers in scope. Q: at any tick an inventory item is held by at most one pool; the second command adds a transfer to the scope. The same statement for both commands. |
| `unit_pool_membershipExclusive` | `inventory_pool.als` | `PoolMembershipExclusive` | `src/resources/inventory-item/inventory-pool-contract.dfy:388` | `WellFormed(log)` | the lemma's own `Alloy:` pointer | See the first row of this check. |
| `unit_pool_reversalDisciplineHolds` | `inventory_pool.als` | `PoolLogChained` | `src/resources/inventory-item/inventory-pool-contract.dfy:395` | `WellFormed(log)` | the lemma's own `Alloy:` pointer | P's second clause: a well-formed pool log satisfies ReversalDiscipline (and TransferPairing). Q: reversalDiscipline over the committed rows. The same statement. |
| `unit_pool_sameTenant` | `inventory_pool.als` | `PoolMembersAgree` | `src/resources/inventory-item/inventory-pool-contract.dfy:382` | `WellFormed(log)` | the lemma's own `Alloy:` pointer | P: in a well-formed pool log every held item agrees with its pool on the item and on the tenant. Q: every item a pool holds at a tick is of the pool's tenant. P implies Q: Q is P's tenant clause. |
| `unit_pool_stampsMonotone` | `inventory_pool.als` | `PoolStampsMonotoneHolds` | `src/resources/inventory-item/inventory-pool-contract.dfy:415` | `WellFormed(log)` | the lemma's own `Alloy:` pointer | P: no committed write of a pool is dated before an earlier committed write of the same pool. Q: the same. The same statement. |
| `unit_invmet_frameworkMatchesLog` | `metrics.als` | `FrameworkMatchesLog` | `src/resources/inventory-item/metrics.dfy:387` | `Aligned(log, at) && StrictChronology(log, at)` | the name | P: under aligned clocks and strict chronology, the measurement framework's value at an instant is the actual of the log's as-of seat. Q: the same, under the same two premises. The same statement. |
| `unit_invmet_partitionAdditivity` | `metrics.als` | `PartitionAdditivity` | `src/resources/inventory-item/metrics.dfy:199` | `x.cAsOf == z.cAsOf && y.cAsOf == z.cAsOf`, and `MembersOf(log, at, x) !! MembersOf(log, at, y) && MembersOf(log, at, z) == MembersOf(log, at, x) + MembersOf(log, at, y)` | the name | P: a cell whose members are the disjoint union of two cells' members, all as of one instant, has the sum of their totals. Q: the same. The same statement. |
| `unit_invmet_quietPeriodRepeats` | `metrics.als` | `QuietPeriodRepeats` | `src/resources/inventory-item/metrics.dfy:255` | `c1.cTenant == c2.cTenant && c1.cItem == c2.cItem && c1.cNode.None? && c2.cNode.None? && AtOrBefore(c1.cAsOf, c2.cAsOf)`, and `forall i :: 0 <= i < \|log\| && Committed(log[i]) ==> !(EarlierThan(c1.cAsOf, at(log[i])) && AtOrBefore(at(log[i]), c2.cAsOf))` | the name | P: two cells of one tenant and item, with no level, and no committed row stamped between their instants, have the same members and total. Q: the same, under aligned clocks. P implies Q: P needs no clock premise. |
| `unit_plc_affirmIsInert` | `pool_lifecycle.als` | `PoolAffirmIsInert` | `src/resources/inventory-item/inventory-pool-contract.dfy:429` | `WellFormed(log) && i < \|log\| && Committed(log[i]) && log[i].kind.AffirmPool?` | the lemma's own `Alloy:` pointer | P: a committed AffirmPool's post state is its pre state (and its holdings are unchanged). Q: a committed affirmation's post is its pre. P implies Q. |
| `unit_plc_affirmNeverCreatedIsNotClosed` | `pool_lifecycle.als` | `PoolAffirmNeverCreatedIsNotClosed` | `src/resources/inventory-item/inventory-pool-contract.dfy:435` | `WellFormed(log) && i < \|log\| && log[i].kind.AffirmPool? && Refused(log[i]) && PreOf(log, i).None?` | the lemma's own `Alloy:` pointer | P: an AffirmPool refused on a pool with no state does not carry RPoolClosed. Q: the same. The same statement. |
| `unit_plc_noRecordedRefusalWithoutGenesis` | `pool_lifecycle.als` | `PoolNoRecordedRefusalWithoutGenesis` | `src/resources/inventory-item/inventory-pool-contract.dfy:441` | `WellFormed(log) && i < \|log\| && Recorded(log, ShapeOf, i) && !Committed(log[i])` | the lemma's own `Alloy:` pointer | P: a recorded row of the pool log that did not commit sits on a pool started before it. Q: the recording law on the pool log. The same statement. |
| `unit_plc_nothingAfterRetire` | `pool_lifecycle.als` | `PoolNothingAfterRetire` | `src/resources/inventory-item/inventory-pool-contract.dfy:402` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the audit of 2026-11-18 | P: of two committed rows on one pool, the earlier is not a RetirePool. Q: nothing commits on a pool after its committed retire (lc/nothingAfterRetire on the pool log). The same statement. |

## `resources/kanban_card`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_cyc_closureIsTerminal` | `cycle_occurrences.als` | `ClosureIsTerminal` | `src/resources/kanban-card/kanban-card-contract.dfy:447` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && ClosedAt(log[..i], log[i].subject)` | the lemma's own `Alloy:` pointer | P: a row on a cycle closed in the prefix before it does not commit. Q: an occurrence on a cycle closed strictly before its tick is not committed. The same statement. |
| `unit_cyc_forwardMonotone` | `cycle_occurrences.als` | `ForwardMonotone` | `src/resources/kanban-card/kanban-card-contract.dfy:392` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && IsForward(log[i].kind)` | the lemma's own `Alloy:` pointer | P: a committed forward operation's post status is strictly after its pre status in the region order. Q: the same. The same statement. |
| `unit_cyc_noPoolBeforeInProcess` | `cycle_occurrences.als` | `NoPoolBeforeInProcess` | `src/resources/kanban-card/kanban-card-contract.dfy:398` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && PostOf(log, i).Some? && RegionBefore(PostOf(log, i).value.sStatus, IN_PROCESS)` | the lemma's own `Alloy:` pointer | P: a committed row whose post status is before IN_PROCESS leaves no pool. Q: the same. The same statement. |
| `unit_cyc_oneLiveCyclePerCard` | `cycle_occurrences.als` | `OneLiveCyclePerCard` | `src/resources/kanban-card/kanban-card-contract.dfy:384` | `WellFormed(log, cards, plog, items, cfg) && CardsWF(cards) && k in cards && c1 in k.cycles && c2 in k.cycles`, and `LiveCycleAt(log, c1) && LiveCycleAt(log, c2)` | the lemma's own `Alloy:` pointer | P: two live cycles of one card are the same cycle. Q: a card has at most one current cycle at a tick. The same statement, for the prefix at each tick. P's premise CardsWF is the well-formedness of the static card set, which Alloy holds as facts of the card's types (CardCycleOwnership, PrecededByWithinCard, OneChainPerCard, PrecededByLinear). |
| `unit_cyc_poolExclusiveWhileLive` | `cycle_occurrences.als` | `PoolExclusiveWhileLive` | `src/resources/kanban-card/kanban-card-contract.dfy:430` | `WellFormed(log, cards, plog, items, cfg)`, and `LiveCycleAt(log, c1) && StateOfCycleAt(log, c1).Some? && StateOfCycleAt(log, c1).value.sPool == Some(e)`, and `LiveCycleAt(log, c2) && StateOfCycleAt(log, c2).Some? && StateOfCycleAt(log, c2).value.sPool == Some(e)` | the lemma's own `Alloy:` pointer | P: two live cycles whose state holds the same pool id are the same cycle. Q: at each tick a pool has at most one live cycle. P implies Q: P is stated over the pool id, which is stronger than Alloy's resolved pool. |
| `unit_cyc_poolFrozenOnceAttached` | `cycle_occurrences.als` | `PoolFrozenOnceAttached` | `src/resources/kanban-card/kanban-card-contract.dfy:405` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && !log[i].kind.StartProcessing? && !log[i].kind.ProductionFailure?`, and `PreOf(log, i).Some? && PreOf(log, i).value.sPool.Some?` | the lemma's own `Alloy:` pointer | P: a committed row other than a StartProcessing or a ProductionFailure that read a pool leaves the same pool. Q: the same. The same statement. |
| `unit_cyc_poolItemHomogeneous` | `cycle_occurrences.als` | `PoolItemHomogeneous` | `src/resources/kanban-card/kanban-card-contract.dfy:460` | `WellFormed(log, cards, plog, items, cfg) && CardsWF(cards) && i < \|log\| && Committed(log[i]) && log[i].kind.StartProcessing?`, and `p in PoolsNamed(PrefixBefore(plog, log[i].tick), log[i].kind.pool) && k in Owners(cards, log[i].subject)` | the lemma's own `Alloy:` pointer | P: a committed StartProcessing's pool is of its card's item (PoolItemHomogeneous), and a cycle's attached pool is exactly the pool its committed StartProcessing named (PoolProvenance). Q: at every tick a cycle's pool is of its card's item. P implies Q: the pool in a cycle's state is the one its attach named, and that one is of the card's item; a pool's item pin does not change. P's premise CardsWF is the static card set's well-formedness. |
| `unit_cyc_poolItemHomogeneous` | `cycle_occurrences.als` | `PoolProvenance` | `src/resources/kanban-card/kanban-card-contract.dfy:414` | `WellFormed(log, cards, plog, items, cfg) && StateOfCycleAt(log, c).Some? && StateOfCycleAt(log, c).value.sPool == Some(e)` | the audit of 2026-11-18 | See the first row of this check. |
| `unit_cyc_poolProvenance` | `cycle_occurrences.als` | `PoolProvenance` | `src/resources/kanban-card/kanban-card-contract.dfy:414` | `WellFormed(log, cards, plog, items, cfg) && StateOfCycleAt(log, c).Some? && StateOfCycleAt(log, c).value.sPool == Some(e)` | the lemma's own `Alloy:` pointer | P: a cycle whose state holds a pool has a committed StartProcessing of its own naming that pool. Q: the same, at each tick. The same statement. |
| `unit_cyc_quantityFixedAtGenesis` | `cycle_occurrences.als` | `QuantityFixedAtGenesis` | `src/resources/kanban-card/kanban-card-contract.dfy:453` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && !log[i].kind.Request? && PreOf(log, i).Some?` | the lemma's own `Alloy:` pointer | P: a committed row other than a Request leaves the quantity override it read. Q: the same. The same statement. |
| `unit_cyr_abandonedIsWithdrawn` | `cycle_retire.als` | `AbandonedIsWithdrawn` | `src/resources/kanban-card/kanban-card-contract.dfy:498` | none | the lemma's own `Alloy:` pointer | P: a cycle is abandoned exactly when it has a committed Withdraw. Q: the same, at each tick. The same statement, definitional on both sides. |
| `unit_cyr_attachedOnceById` | `cycle_retire.als` | `PoolAttachedOnce` | `src/resources/kanban-card/kanban-card-contract.dfy:421` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && j < \|log\| && Committed(log[i]) && Committed(log[j])`, and `log[i].kind.StartProcessing? && log[j].kind.StartProcessing? && log[i].kind.pool == log[j].kind.pool` | reading | P: two committed StartProcessing rows that name the same pool id are the same row. Q: a pool id is named by at most one committed StartProcessing. The same statement. |
| `unit_cyr_closedBeforeSuccessorGenesis` | `cycle_retire.als` | `ClosedBeforeSuccessorGenesis` | `src/resources/kanban-card/kanban-card-contract.dfy:439` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && log[i].kind.Request? && log[i].subject.precededBy.Some?` | the lemma's own `Alloy:` pointer | P: a committed Request of a cycle with a predecessor found that predecessor closed in the prefix before it. Q: the same. The same statement. |
| `unit_cyr_noRecordedRefusalWithoutGenesis` | `cycle_retire.als` | `CycleNoRecordedRefusalWithoutGenesis` | `src/resources/kanban-card/kanban-card-contract.dfy:491` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Recorded(log, ShapeOf, i) && !Committed(log[i])` | the lemma's own `Alloy:` pointer | P: a recorded row of the cycle log that did not commit sits on a cycle started before it. Q: the recording law on the cycle log. The same statement. |
| `unit_cyr_nothingAfterRetire` | `cycle_retire.als` | `CycleNothingAfterRetire` | `src/resources/kanban-card/kanban-card-contract.dfy:483` | `WellFormed(log, cards, plog, items, cfg) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the audit of 2026-11-18 | P: of two committed rows on one cycle, the earlier is not of the Retire shape. Q: nothing commits on a cycle after either of its retires (lc/nothingAfterRetire on the cycle log). The same statement. |
| `unit_cyr_poolAttachedOnce` | `cycle_retire.als` | `PoolAttachedOnce` | `src/resources/kanban-card/kanban-card-contract.dfy:421` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && j < \|log\| && Committed(log[i]) && Committed(log[j])`, and `log[i].kind.StartProcessing? && log[j].kind.StartProcessing? && log[i].kind.pool == log[j].kind.pool` | the lemma's own `Alloy:` pointer | P: two committed StartProcessing rows that name the same pool id are the same row. Q: the same. The same statement. |
| `unit_cyr_startedPoolLive` | `cycle_retire.als` | `StartedPoolLive` | `src/resources/kanban-card/kanban-card-contract.dfy:477` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && log[i].kind.StartProcessing?` | the name | P: a committed StartProcessing names a pool live as of its tick. Q: the same. The same statement. |
| `unit_cyr_startedPoolLive` | `cycle_retire.als` | `StartedPoolLive` | `src/resources/kanban-card/kanban-card.dfy:419` | none | the name | See the first row of this check. |

## `resources/processing_network`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_pnet_unretiredAlwaysLive` | `processing_network.als` | `UnretiredAlwaysLive` | `src/resources/processing-network/processing-network.dfy:51` | `s.retiredAt.None?` | the name | P: a station with no retire tick is live at every tick. Q: the same. The same statement, definitional on both sides. |

## `shared/certainty`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_cert_decayNeverRaises` | `certainty.als` | `DecayNeverRaises` | `src/shared/certainty/certainty.dfy:40` | `ComputedFrom(c, s)` | the name | P: a level computed from a start is at or below it. Q: the same. The same statement. |
| `unit_cert_floorIsLowest` | `certainty.als` | `FloorIsLowest` | `src/shared/certainty/certainty.dfy:42` | none | the name | P: AtOrBelow(LOW) == {LOW}. Q: the same. The same statement. |
| `unit_cert_order` | `certainty.als` | `Order` | `src/shared/certainty/certainty.dfy:36` | none | the audit of 2026-11-18 | P: LteC(LOW, MEDIUM), LteC(MEDIUM, HIGH), LteC(LOW, HIGH), and neither LteC(MEDIUM, LOW) nor LteC(HIGH, MEDIUM). Q: the same five clauses. The same statement. |

## `shared/measurement`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_q_dispatchLastFirst` | `quantity.als` | `DispatchLastFirst` | `src/shared/measurement/quantity.dfy:148` | `OneSamplePerInstant(ms)` | the name | P: under OneSamplePerInstant, a LAST metric's result is LastValueIn and a FIRST metric's is FirstValueIn. Q: the same. The same statement. P's premise is what the KEPT check unit_meas_oneSamplePerInstant shows of Alloy's facts. |
| `unit_q_minLeMax` | `quantity.als` | `MinLeMax` | `src/shared/measurement/quantity.dfy:130` | `MinIn(ms, s, p).Some? && MaxIn(ms, s, p).Some?` | the lemma's own `Alloy:` pointer | P: when both exist, MinIn is at or below MaxIn. Q: the same. The same statement. |
| `unit_q_minMaxSampled` | `quantity.als` | `MinMaxSampled` | `src/shared/measurement/quantity.dfy:139` | none | the name | P: MinIn and MaxIn, when present, are among the period's sampled values. Q: the same. The same statement. |
| `unit_q_sumSingleton` | `quantity.als` | `SumSingleton` | `src/shared/measurement/quantity.dfy:177` | `i < \|ms\| && forall j :: 0 <= j < \|ms\| ==> ((ms[j].of == s && Within(ms[j].at, p)) <==> j == i)` | the name | P: a period with exactly one sample sums to that sample's value. Q: the same. The same statement. |

## `shared/time`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_time_closeAtOrAfter` | `calendar.als` | `CloseLaws` | `src/shared/time/tests/calendar-tests.dfy:36` | `Time.Calendar(ps)` | the audit of 2026-11-18 | P's first clause: under Time.Calendar(ps), an instant is at or before the close of its period, for every period specification and instant. Q: under the calendar axioms, the same. The same statement under the same premise, which the check itself states. |
| `unit_time_closeIdempotent` | `calendar.als` | `CloseLaws` | `src/shared/time/tests/calendar-tests.dfy:36` | `Time.Calendar(ps)` | the audit of 2026-11-18 | P's second clause: under Time.Calendar(ps), the close of a close is itself. Q: under the calendar axioms, the same. The same statement under the same premise, which the check itself states. |
| `unit_time_inOwnPeriod` | `calendar.als` | `CloseLaws` | `src/shared/time/tests/calendar-tests.dfy:36` | `Time.Calendar(ps)` | the audit of 2026-11-18 | P's third clause: under Time.Calendar(ps), an instant and the close of its period are in the same period. Q: under the calendar axioms, the same. The same statement under the same premise, which the check itself states. |
| `unit_time_samePeriodEquiv` | `calendar.als` | `SamePeriodEquiv` | `src/shared/time/tests/calendar-tests.dfy:43` | `Time.Calendar(ps)` | the name | P: under Time.Calendar(ps), SamePeriod is reflexive, symmetric and transitive, for every period specification. Q: the same, under the calendar axioms. The same statement under the same premise. |
