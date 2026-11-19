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
  - the lemma's own `Alloy:` pointer names the check (78 rows);
  - the names agree (61 rows);
  - by reading the two statements (25 rows);
  - the audit added the lemma (26 rows; see "The audit" below).
- **Why the lemma implies the check** is the audit's sentence for the check, on the check's first row. **P** is what
  the lemma states, or what the lemmas state together when the check has several rows. **Q** is what the check states.
  The cell then says why P implies Q.
- **A check with several rows** is a law that Dafny states in several lemmas: per module, or in parts.
- **The scope:** the `check` commands outside `soak/`, `conventions/` and `meta/examples/`, as main stood at
  `2986f32`. The kept checks are listed in `EXTENSIONS.md`, each with its reason.

**Counts:** 176 retired `check` commands under 175 names (`unit_pool_membershipExclusive` had two), 190
check-and-lemma rows, 23 modules. 86 names are retired under the audit's rule, and 89 under the project owner's
ruling on the roots without lower facts: "The ruling", below, says which rows are which.

**Four more checks are retired by a ruling of their own, and are not rows of this record.** The project owner's ruling
on card QA787, second question, option (a), replaces them with four integration finders, one per refusal on the real
stack. They left the tree with those finders: `int_dem_cycleHeldRefused` and `int_dem_frozenRefused` in the demand's
root, `int_ord_demandHeldRefused` and `int_ord_frozenRefused` in the order's. Their roots open a lower module by its
types alone, so the audit's rule below would keep them; the ruling decides. The lines in this table are at the Dafny
revision named above (`ac60846`), as every line in this record is.

| Check | Root | The Dafny lemma that states the law |
| --- | --- | --- |
| `int_dem_contract_cycleIndivisible` | `operations/demand/tests/integration/demand.als` | `CycleIndivisible` (`src/operations/demand/demand-contract.dfy:886`) |
| `int_dem_contract_frozenOutsideOpen` | `operations/demand/tests/integration/demand.als` | `FrozenOutsideOpen` (`src/operations/demand/demand-contract.dfy:894`) |
| `int_ord_contract_demandIndivisible` | `procurement/order/tests/integration/order.als` | `DemandIndivisible` (`src/procurement/order/order-contract.dfy:640`) |
| `int_ord_contract_frozenOutsideDraft` | `procurement/order/tests/integration/order.als` | `FrozenOutsideDraftOrder` and `FrozenOutsideDraftLine` (`src/procurement/order/order-contract.dfy:623`, :630) |

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

- **86 checks stay retired under the rule,** and the four of the ruling above beside them.
  - 68 pairings stand as first recorded.
  - 18 had a citation that was wrong or incomplete, and the right lemma exists. Their rows now cite it. Most were a
    name matched across modules: each module's `nothingAfterRetire` check, for example, was paired with the
    affiliate's, the item's and the staff's lemmas.
- **120 checks were restored to the tree.** 89 of them are retired since, under the ruling below. `EXTENSIONS.md`
  lists the other 31 among the kept checks, each with its reason.
  - **5 restate a fact of the Alloy model that Dafny only assumes.** Each is the guard of that fact:
    `unit_kernel_eIdIsKey`, `unit_principal_nameIsKey`, `X731Consistency`, `unit_occ_onePerTick` and
    `unit_occ_archeOriginPrecedes`.
  - **2 have no lemma that implies them:** `unit_act_walkEndsAtOrigin` and `unit_alg_scaleZeroValue`. The reference
    model was searched for a lemma whose statement concludes the property, by statement and not by name.
  - **113 are in a root that opens a lower module without its implementation facts.** In Dafny a lower module's
    state is always its `Effect` folded over its log. Such a root allows lower records that the chaining and effect
    facts would exclude, and it is not shown that every one of them is the state of some lower log. So the lemma
    is not shown to cover every instance of the root.
    - 75 are in a unit root that gives its lower modules as contract mocks: the demand's two unit roots (22), the
      order's (19), the receiver's (17) and the inventory item's (17). A mock keeps the lower module's occurrences
      and replaces its chaining and effect facts with the contract's `guarantees`.
    - 38 are in a root that opens a lower module by its types alone, with neither its facts nor a mock: the item's
      root (7), the kanban card's two (16), the pool's two (9), the inventory metrics' (3), the inventory item's
      integration root (2) and the order's received root (1). The demand's and the order's integration roots are
      of this kind too: their four contract checks are the ones the ruling above retires.
    - The project owner ruled on these 113 on 2026-11-18 (card QA835, option (ii)): "The ruling on the roots
      without lower facts", below. 89 are retired under it and are rows of this record. 24 stay.

## The ruling on the roots without lower facts (2026-11-18)

The audit kept 113 checks whose root opens a lower module without its implementation facts: the lemma was not shown
to cover every instance of such a root. The project owner ruled on them (card QA835, option (ii)): **such a check
retires once every premise of its Dafny lemma is established in the reference model.** In Dafny a lower state is
always the effect folded over a lower log. A lemma whose premises are all established holds of every state the
system can reach. An instance of the root with a lower record that no log produces is outside what the model
describes.

- **89 checks retire under the ruling,** with 90 commands. Their rows are the sections `operations/demand`,
  `procurement/order`, `receiving/receiver`, `resources/inventory_item` and `resources/kanban_card`, and the seven
  rows of `reference_data/item` whose root is `item.als`. Each row's sentence is the audit's.
- **Their premises were read in the reference model** at `1c868f2ee` (dafny-domain's main on 2026-11-19), lemma by
  lemma. Each lemma has the same `requires` clauses there as at the revision this record cites. "The premises"
  ends with the table of what establishes each.
- **24 stay,** each for a premise that is not established. `EXTENSIONS.md` lists them.
  - Twelve need only the receiver's well-formedness. The reference model proves that the unpaired appends keep
    it. For the paired line kinds it is a declared obligation (dafny-domain's SO-1), not a lemma.
  - Twelve need a premise that Dafny only assumes: ids are keys (`KeyedCycles`, `KeyedDemands`, `KeyedOrders`,
    `KeyedPools`, `KeyedReceivers`), a pool has its genesis (`DemandPoolGenesis`, `ReceivingPoolGenesis`), or the
    card set is well formed (`CardsWF`). Four of them need the receiver's well-formedness too.
- **For the 89 the audit's second condition is not claimed.** What implies a premise of theirs is a lemma of the
  reference model, not a fact of the Alloy root.

## The premises

A Dafny lemma holds of the logs that satisfy its `requires` clauses. An Alloy check holds of every instance of its
root. So a lemma replaces a check only where the root's instances satisfy the lemma's premises. This section lists
every kind of premise in the rows of the 86 checks retired under the audit's rule, with what implies it in the
Alloy model, by file and line under `alloy/` at this revision. A premise with nothing that implies it would make its
checks kept: none is left in those rows. Each fact the table cites for a check is in the import cone of that check's
root (checked with `tools/cone.sh`, check by check). The 89 retired under the ruling are apart: their table,
"Established in the reference model", ends this section.

The table matches predicates. It takes the two guards and the two effects of a module to be the same functions,
which is what the Alloy model is a mirror of: each refusal has its finder, and the reference model's pointer check
reads the names.

**Case hypotheses** are not in the table: an index within the log, a row that is `Committed`, a kind, a subject that
is live. Each restricts the lemma to the case the check's own antecedent names, and the row's last column says so.
Of the 86, 30 checks have a lemma with no premise at all.

| Premise | Checks | In Dafny | What implies it in Alloy |
| --- | --- | --- | --- |
| `WellFormed(…)` of a module's own logs | 12 | Its body is about the module's own logs only: the ticks are ordered (`Ordered`, `src/meta/trace.dfy:68`) and every row's verdict is the guard's (`Generated`). The lower logs are arguments of the guard, with no condition on them. Every `Append` keeps it. | The order: `OneOccurrencePerTick` (`meta/occurrence/occurrence.als:40`). The verdicts: the module's admission fact, with its chaining and effect facts for the state the guard reads. Per module, in the next table. The roots of these 12 checks open every module they read with its implementation facts: the affiliate's and the staff's roots read no lower module, and the shared root opens the item's and the affiliate's implementations. |
| `StrictTicks(ba)`: the affiliate log is ordered | 1 | A conjunct of the affiliate's own well-formedness, which every `Append` keeps. | `OneOccurrencePerTick` (`meta/occurrence/occurrence.als:40`). The kept check `unit_occ_onePerTick` guards it. |
| `Keyed(u)`: entity ids are keys | 1 | Assumed. No lemma establishes it. | `EntityIdIsKey` (`meta/kernel.als:22`). The kept check `unit_kernel_eIdIsKey` guards it. |
| `NamesUnique(ps)`: principal names are keys | 1 | Assumed. | `PrincipalNameUnique` (`meta/principal/principal.als:37`). The kept check `unit_principal_nameIsKey` guards it. |
| `ShapeAdmission(log, shape)`: the lifecycle's admission | 5 | Established for each adopter, the demand and the order among them. | `ShapeAdmission` (`meta/subject_log/lifecycle.als:80`). |
| `Tombstone(effect, shape)`: a retire keeps the state | 1 | Established for each adopter's effect. | `RetireEffect` (`meta/subject_log/lifecycle.als:64`). |
| `AffirmKeeps(effect, shape)`: an affirmation keeps the state | 1 | Discharged where the lemma is used (`src/meta/tests/affirm-tests.dfy:101`). | `AffirmEffect` (`meta/subject_log/affirm.als:35`). |
| `OneSamplePerInstant(ms)` | 2 | Established for the inventory item's metrics; assumed in the measurement lemmas. | `OneSamplePerInstant` (`meta/measurement/measurement.als:38`). The kept check `unit_meas_oneSamplePerInstant` guards it. |
| `Activated(alog, elog, lift)`: an effect cites an activation that precedes it | 1 | Established: appending an activation or an effect keeps it. | `OnlyActivationsAreCited` and `OnlyActivationsSelfCite` (`meta/activation/activation.als:58`, :60), with `ArcheOriginPrecedes` (`meta/occurrence/occurrence.als:55`). The check reads no verdict, so the conjunct on agreeing verdicts is not needed. |
| `WorldWellFormed(w)`: the world's citations | 3 | Established of the system's world by `SysWorldWellFormed`, from the three services' `Activated`, from `SkeletonsDefined` (each log is ordered and each activation log's ids are unique, which `OrderOfTheWorld` establishes), and from five premises it assumes: `BoundaryWF` (the boundary log is ordered, its ids are unique and its rows are origins), `ServicesTicksDisjoint`, `ServicesIdsDisjoint`, `CallersInWorld` and `CrossCallersPrecede`. | Conjunct by conjunct. Ordered logs and disjoint ticks: `OneOccurrencePerTick` (`meta/occurrence/occurrence.als:40`). Unique and disjoint ids: an occurrence cites its activation as an atom (`arche`, `meta/occurrence/occurrence.als:26`), so there is no id to bear twice. Callers cited: `OnlyActivationsAreCited` (`meta/activation/activation.als:58`). Citations precede: `ArcheOriginPrecedes` (`meta/occurrence/occurrence.als:55`), which the kept check `unit_occ_archeOriginPrecedes` guards. Only origins cite themselves: `OnlyActivationsSelfCite` (:60) with `origin` (:63). **In the occurrence root,** which does not open the activation module, the two activation facts are not in force and are not needed (`unit_occ_archeNoProperCycle` is the one check there). Every occurrence of that root is read as an activation row of one log: a citation resolves to a row of that log because `arche` is total (`meta/occurrence/occurrence.als:26`), and a row that cites its own tick is an origin by that reading. `OneOccurrencePerTick` and `ArcheOriginPrecedes` are enough. |
| `Time.Calendar(ps)`: the calendar axioms | 4 | Assumed. | The check states it: `calendarAxioms implies …` (`meta/time/time.als:46`). |
| `Nf(a)`: a keyed value is in normal form | 7 | Established where a value is computed; assumed of an argument. | Five checks state it: `nf[a] implies …` (`meta/keyed_value_algebra/keyed_monoid.als:31`). For the two checks of the running sum: `ChainWellFormed` (`meta/keyed_value_algebra/keyed_sum.als:34`). |
| `ClocksAligned(log, at)` | 1 | Assumed. | The check states it: `clocksAligned implies …` (`meta/occurrence/timed.als:25`). |
| `ComputedFrom(c, s)` | 1 | The lemma's case. | The check states it: `computedFrom[c, s] implies …` (`shared/certainty/certainty.als:38`). |
| `Covers(sch, q)`: every unit of the quantity has a factor | 1 | Assumed. | The check's `hasGroup[sch, q]` with `ConvNodesWF` (`reference_data/item/uom_collapse.als:32`): a group that is present covers exactly its quantity's units, each configured in the scheme. |

**A module's own well-formedness, fact by fact.** The file is the module's implementation file unless the row says
otherwise.

| Module | Checks | Admission: each verdict is the guard's | Chaining and effect: the state the guard reads | Other conjuncts |
| --- | --- | --- | --- | --- |
| business affiliate | 7 | `BaAdmissionWitnessed` (`reference_data/business_affiliate/business_affiliate_implementation.als:51`) | `BaChain` (:20), `BaEffects` (:58) | |
| item, in the reference data's shared root | 1 | `ItemAdmissionWitnessed` (`reference_data/item/item_implementation.als:64`) | `ItemChain` (:19), `ItemEffects` (:73) | |
| staff | 4 | `StaffAdmissionWitnessed` (`reference_data/staff/staff_implementation.als:35`) | `StaffChain` (:15). The staff has no effect fact of its own: a staff record has no content that a write changes | |

**Established in the reference model: the premises of the 89.** By file under `src/` at dafny-domain `1c868f2ee`.
A check with lemmas of two kinds is counted in both.

| Premise | Checks | The predicate | What establishes it |
| --- | --- | --- | --- |
| The inventory item's `WellFormed` | 20 | `resources/inventory-item/inventory-item.dfy:285` | `AppendWellFormed` (:345): every append keeps it. |
| The demand's `WellFormed` | 18 | `operations/demand/demand.dfy:516` | `AppendWellFormed` (:2240) for every kind but the two halves of a pairing; `DeliverWellFormed` (:2430) and `RevokeWellFormed` (:2578) for the pairings; `AppendPDWellFormed` (:2254) for a delivery's retire. |
| The order's `WellFormed` | 18 | `procurement/order/order.dfy:325` | `AppendOWellFormed` (:1377) and `AppendLWellFormed` (:1398). |
| The kanban card's `WellFormed` | 16 | `resources/kanban-card/kanban-card.dfy:180` | `AppendWellFormed` (:227). |
| The inventory pool's `WellFormed` | 9 | `resources/inventory-item/inventory-pool.dfy:163` | `AppendWellFormed` (:414) for every kind but a transfer; `TransferWellFormed` (:471). |
| The item's `WellFormed` | 5 | `reference-data/item/item.dfy:105` | `AppendWellFormed` (:136). |
| `StrictTicks(ba)`: the affiliate log is ordered | 2 | `meta/trace.dfy:61` | A conjunct of the affiliate's `WellFormed`, which its `AppendWellFormed` keeps (`reference-data/business-affiliate/business-affiliate.dfy:103`). |
| `Aligned(log, at)` and `StrictChronology(log, at)` | 1 | `resources/inventory-item/metrics.dfy:67`, :71 | Nothing, and nothing needs to: the check states both as its own antecedent (`clocksAligned and strictChronology implies …`). |
| No standing premise | 6 | | The lemma has no `requires` clause, or only case hypotheses. |

**Not checked by this table:** that each guard and each effect of the Alloy model equals the Dafny one arm by arm.
That is the mirror itself, kept by the finders of each refusal and by the pointer check, not by this record.

**An abstract structure in Alloy, a single structure in Dafny.** For 40 of the retired checks the lemma proves the
law of one structure, where the check stated it of every structure its root admits. The rows of these checks say
"the same law" or "the same statement": read them with this paragraph.

- **The scalar, 38 checks.** Alloy's `Scalar` is an uninterpreted signature (`meta/scalar/scalar.als:18`). A root
  admits every structure that satisfies what it assumes of the scalar: the ring and order axioms as a premise of the
  check (`ringAxioms`, `meta/scalar/scalar.als:44`; `orderAxioms`, `meta/keyed_value_algebra/keyed_order.als:59`),
  the group and order axioms as a fact (`DomainLogPremises`, `meta/profiles/domain_log.als:24`), or nothing. At the
  checks' scopes these are small finite structures, the integers modulo 3 among them. Dafny's `Scalar` is `real`
  (`src/meta/scalar.dfy:13`), and each lemma is the law for the reals. The lemmas `GroupAxioms`, `RingAxioms` and
  `OrderAxioms` (`src/meta/scalar.dfy:35`, :42, :51) and `DomainLogPremises` (`src/meta/profiles.dfy:41`) prove
  that the reals satisfy Alloy's axioms, so each law holds of the scalar the reference model uses. Of another
  structure with those axioms, nothing checks the law any more. The first 30, retired under the audit's rule:
  - the keyed algebra's eight: `unit_alg_addAssociative`, `unit_alg_addClosedNf`, `unit_alg_addCommutative`,
    `unit_alg_addIdentity`, `unit_alg_addInverse`, `unit_alg_scaleDistribAdd`, `unit_alg_scaleOneIdentity`,
    `unit_alg_scaleZeroScalar`;
  - the keyed order's six: `unit_ord_lteAntisymmetric`, `unit_ord_lteReflexive`, `unit_ord_lteTransitive`,
    `unit_ord_positiveIsAboveZero`, `unit_ord_semEqualIffLexical`, `unit_ord_semUnequalImpliesDifferent`;
  - the keyed sum's four: `unit_sum_baseIsVal`, `unit_sum_cumNf`, `unit_sum_stepFolds`, `unit_sum_telescope`;
  - the unit collapse's four: `unit_collapse_eachIdentity`, `unit_collapse_eachKeyed`,
    `unit_collapse_singleIsToEach`, `unit_collapse_twoUnitFolds`;
  - the quantity's four: `unit_q_dispatchLastFirst`, `unit_q_minLeMax`, `unit_q_minMaxSampled`,
    `unit_q_sumSingleton`;
  - the scalar's own three and the profile's one, which state an axiom itself: `unit_scalar_addInverse`,
    `unit_scalar_distributes`, `unit_scalar_zeroNeOne`, `unit_prof_premisesInForce`.
  - Eight more are among the 89 retired under the ruling. Each is a law of quantities in a root where the group
    and order axioms hold as a fact (`DomainLogPremises`). The last assumes the ring axioms too, as its premise:
    `unit_occ_mergeConserves`, `unit_occ_splitConserves`, `unit_occ_noCommittedOverdraw`,
    `unit_invmet_partitionAdditivity`, `unit_ord_contract_receiptAccrues`, `unit_ord_contract_receiptReverses`,
    `unit_ordr_receivedIsAccumulated`, `unit_item_toEachIdentity`.
  - Three more of the 89 name a scalar or a quantity and state no law of its values:
    `unit_occ_committedUnitsValid` (the units of an amount, its keys), `unit_item_eachConfigured` (a constant: the
    factor of each is one) and `unit_invmet_quietPeriodRepeats` (equal members give equal totals).
  - Every one of the 89 is in a root with that fact, and these modules add and compare quantities in their
    guards and effects. So each of the 89 was checked over small abstract scalars and is proved over the reals.
- **Elapsed time, 2 checks.** Alloy's metric is abstract, under the premise `durationAxioms`
  (`meta/time/time.als:66`). Dafny's instants are integers and its durations naturals (`src/meta/time.dfy:20`, :99),
  and each law is a theorem of that metric: `unit_time_elapsedWhenOrdered`, `unit_time_zeroAtPoint`.

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
| `unit_occ_archeNoProperCycle` | `occurrence.als` | `NoProperCycle` | `src/meta/activation.dfy:392` | `WorldWellFormed(w) && Walk(w, path) && \|path\| >= 2 && path[0] == path[\|path\| - 1]` | reading | P: a closed walk of two or more rows starts at a row whose cited tick is its own. Q: an occurrence that reaches itself along the citations cites itself. P implies Q: `o in o.^arche` is such a walk, and citing one's own tick is citing oneself (one row per tick). P's premise WorldWellFormed holds of this root from Alloy's facts OneOccurrencePerTick and ArcheOriginPrecedes, each occurrence being read as an activation row of one log (the premise table). |
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
| `unit_dem_contract_completeRequiresSettled` | `unit/demand.als` | `CompleteRequiresSettled` | `src/operations/demand/demand-contract.dfy:943` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Complete? && c in AttachedLiveAt(log[..i], PrefixBefore(clog, log[i].tick), log[i].subject)` | the lemma's own `Alloy:` pointer | P: a committed Complete found no attached live member cycle IN_PROCESS as of its tick. Q: the same. The same statement. |
| `unit_dem_contract_completeStampedAfterHolding` | `unit/demand.als` | `CompleteStampedAfterHolding` | `src/operations/demand/demand-contract.dfy:952` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Complete? && PreOf(log, i).Some? && PreOf(log, i).value.sHolding.Some? && p in KC.PoolsNamed(PrefixBefore(plog, log[i].tick), PreOf(log, i).value.sHolding.value)` | the lemma's own `Alloy:` pointer | P: no committed write of the holding pool before a committed Complete is dated after the Complete's stamp. Q: every committed write of the holding pool causally before a committed Complete is dated at or before it. The same statement. |
| `unit_dem_contract_cycleIndivisible` | `unit/demand.als` | `CycleIndivisible` | `src/operations/demand/demand-contract.dfy:886` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && d1 in DemandOf(log, c) && d2 in DemandOf(log, c)` | the lemma's own `Alloy:` pointer | P: in a well-formed world, two demands that hold a cycle are the same demand. Q: at every tick a cycle has at most one demand. P implies Q: P holds of every well-formed log, so of the prefix at each tick. |
| `unit_dem_contract_deliveryTerminalRevoke` | `unit/demand.als` | `DeliveryTerminalRevoke` | `src/operations/demand/demand-contract.dfy:1006` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && n1 <= n2 <= \|pdlog\| && DeliveryStatusAt(pdlog[..n1], pd) == Some(PD_REVOKED)` | the lemma's own `Alloy:` pointer | P: a delivery that reads REVOKED in a prefix of its log reads REVOKED in every longer prefix. Q: a delivery REVOKED at a tick is REVOKED at every later tick. The same statement: a later tick is a longer prefix. |
| `unit_dem_contract_distributeRequiresReady` | `unit/demand.als` | `DistributeRequiresReady` | `src/operations/demand/demand-contract.dfy:933` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Distribute? && m in log[i].kind.fills && PreOf(log, i).Some? && m in PreOf(log, i).value.sContributions && PreOf(log, i).value.sContributions[m].CardContribution? && c in CyclesNamed(PrefixBefore(clog, log[i].tick), PreOf(log, i).value.sContributions[m].cycle)` | the lemma's own `Alloy:` pointer | P: a committed Distribute found the cycle of every card contribution it asserts as filled READY as of its tick. Q: the same. The same statement. |
| `unit_dem_contract_frozenOutsideOpen` | `unit/demand.als` | `FrozenOutsideOpen` | `src/operations/demand/demand-contract.dfy:894` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && IsMutator(log[i].kind)` | the lemma's own `Alloy:` pointer | P: a committed contribution mutator read a state whose status is OPEN. Q: the same. The same statement. |
| `unit_dem_contract_holdingProvenance` | `unit/demand.als` | `HoldingProvenance` | `src/operations/demand/demand-contract.dfy:1032` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && HoldingAt(log, d) == Some(e)` | the lemma's own `Alloy:` pointer | P: a demand whose holding is e has a committed StartProduction naming e in its log. Q: a demand with a holding at a tick has a committed StartProduction at or before it naming that holding. The same statement, for the prefix at each tick. |
| `unit_dem_contract_startProductionRequiresStarted` | `unit/demand.als` | `StartProductionRequiresStarted` | `src/operations/demand/demand-contract.dfy:925` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.StartProduction? && c in AttachedLiveAt(log[..i], PrefixBefore(clog, log[i].tick), log[i].subject)` | the lemma's own `Alloy:` pointer | P: a committed StartProduction found every attached live member cycle IN_PROCESS as of its tick. Q: the same. The same statement. |
| `unit_dem_contract_terminalClosure` | `unit/demand.als` | `TerminalClosure` | `src/operations/demand/demand-contract.dfy:974` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && n1 <= n2 <= \|log\| && DemandStatusAt(log[..n1], d).Some? && TerminalStatus(DemandStatusAt(log[..n1], d).value)` | the lemma's own `Alloy:` pointer | P: a demand whose status is terminal in a prefix of its log has a terminal status in every longer prefix. Q: a demand COMPLETE or CANCELED at a tick is COMPLETE or CANCELED at every later tick. The same statement: a later tick is a longer prefix. |
| `unit_dem_contract_withdrawnDetachReconciles` | `unit/demand.als` | `WithdrawnDetachReconciles` | `src/operations/demand/demand-contract.dfy:963` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.DetachWithdrawn?` | the lemma's own `Alloy:` pointer | P: a committed DetachWithdrawn's post contributions are its pre contributions without the entry it names (and that entry was a card contribution). Q: the post contributions are the pre contributions without the target. P implies Q: P's third clause is Q. |
| `unit_dem_holdingPoolPinHolds` | `unit/demand.als` | `HoldingPoolPinMatchesItem` | `src/operations/demand/demand-contract.dfy:1082` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.StartProduction? && log[i].kind.holding.Some? && p in KC.PoolsNamed(PrefixBefore(plog, log[i].tick), log[i].kind.holding.value)` | reading | P: every pool that a committed StartProduction's holding names carries the demand's item pin. Q: the same. The same statement. |
| `unit_dem_holdingPoolPinMatchesItem` | `unit/demand.als` | `HoldingPoolPinMatchesItem` | `src/operations/demand/demand-contract.dfy:1082` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.StartProduction? && log[i].kind.holding.Some? && p in KC.PoolsNamed(PrefixBefore(plog, log[i].tick), log[i].kind.holding.value)` | the lemma's own `Alloy:` pointer | P: every pool that a committed StartProduction's holding names carries the demand's item pin. Q: the same. The same statement. |
| `unit_dem_nothingAfterRetire` | `unit/demand.als` | `DemandNothingAfterRetire` | `src/operations/demand/demand-contract.dfy:1242` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the audit of 2026-11-18 | P: of two committed rows on one demand, the earlier is not a DeleteDemand. Q: no committed row of a demand follows its committed delete. The same statement, on the demand log. |
| `unit_dem_recordedHoldingLive` | `unit/demand.als` | `RecordedHoldingLive` | `src/operations/demand/demand-contract.dfy:1051` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.RecordProduction? && HoldingAt(log[..i], log[i].subject).Some?` | the name | P: a committed RecordProduction on a demand with a holding found that holding's pool live as of its tick. Q: the same. The same statement. |
| `unit_dem_recordedHoldingLive` | `unit/demand.als` | `RecordedHoldingLive` | `src/operations/demand/demand.dfy:1027` | none | the name | |
| `unit_dem_startedHoldingLive` | `unit/demand.als` | `StartedHoldingLive` | `src/operations/demand/demand-contract.dfy:1041` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < \|log\| && Committed(log[i]) && log[i].kind.StartProduction? && log[i].kind.holding.Some?` | the name | P: a committed StartProduction that names a holding names a pool live as of its tick. Q: the same. The same statement. |
| `unit_dem_startedHoldingLive` | `unit/demand.als` | `StartedHoldingLive` | `src/operations/demand/demand.dfy:1004` | none | the name | |
| `unit_pdr_noRecordedRefusalWithoutGenesis` | `unit/delivery_retire.als` | `DeliveryNoRecordedRefusalWithoutGenesis` | `src/operations/demand/demand-contract.dfy:1265` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && j < \|pdlog\| && Recorded(pdlog, PDShapeOf, j) && !Committed(pdlog[j])` | the audit of 2026-11-18 | P: a recorded row of the delivery log that did not commit sits on a delivery started before it. Q: the recording law on the delivery log. The same statement, on the delivery log. |
| `unit_pdr_nothingAfterRetire` | `unit/delivery_retire.als` | `DeliveryNothingAfterRetire` | `src/operations/demand/demand-contract.dfy:1250` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && i < j < \|pdlog\| && Committed(pdlog[i]) && Committed(pdlog[j]) && pdlog[i].subject == pdlog[j].subject` | the audit of 2026-11-18 | P: of two committed rows on one delivery, the earlier is not a RetireDelivery. Q: nothing commits on the delivery's log after a committed retire. The same statement, on the delivery log. |
| `unit_pdr_retireIsTombstone` | `unit/delivery_retire.als` | `DeliveryRetireIsTombstone` | `src/operations/demand/demand-contract.dfy:1258` | `WellFormed(log, pdlog, clog, cards, plog, il, items) && j < \|pdlog\| && Committed(pdlog[j]) && pdlog[j].kind.RetireDelivery?` | reading | P: a committed RetireDelivery's post state is its pre state. Q: the same. The same statement. |

## `procurement/order`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_ord_assigneePinCurrencyHolds` | `unit/order.als` | `AssigneePinCurrency` | `src/procurement/order/order-contract.dfy:759` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && olog[i].kind.UpdateOrderDetails? && olog[i].kind.assignee.Some?` | the lemma's own `Alloy:` pointer | P: a committed details write's assignee pin is the staff member's current version as of its tick. Q: the same. The same statement. |
| `unit_ord_bindingPinCurrencyHolds` | `unit/order.als` | `BindingPinCurrency` | `src/procurement/order/order-contract.dfy:752` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && SupplierWritten(olog[i].kind).Some? && SupplierWritten(olog[i].kind).value.vendorPin.Some?` | the lemma's own `Alloy:` pointer | P: a committed row that writes a supplier with a vendor pin pins the affiliate's current version as of its tick. Q: the same for a CreateOrder and an UpdateSupplier, the two kinds that write a supplier. P implies Q. |
| `unit_ord_contract_attachItemAgrees` | `unit/order.als` | `AttachItemAgrees` | `src/procurement/order/order-contract.dfy:658` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Committed(llog[i]) && DemandPaired(llog[i].kind).Some? && d in DM.DemandsNamed(PrefixBefore(dlog, llog[i].tick), DemandPaired(llog[i].kind).value)` | the lemma's own `Alloy:` pointer | P: a committed line row that pairs a demand (an attach, or an add with a demand) names the item of that demand. Q: the same two cases. The same statement. |
| `unit_ord_contract_attachRequiresReleased` | `unit/order.als` | `AttachRequiresReleased` | `src/procurement/order/order-contract.dfy:650` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Committed(llog[i]) && DemandPaired(llog[i].kind).Some? && d in DM.DemandsNamed(PrefixBefore(dlog, llog[i].tick), DemandPaired(llog[i].kind).value)` | the lemma's own `Alloy:` pointer | P: a committed line row that pairs a demand found that demand live and RELEASED as of its tick. Q: a committed pairing found the demand RELEASED at its tick. P implies Q. |
| `unit_ord_contract_closeRequiresSettled` | `unit/order.als` | `CloseRequiresSettled` | `src/procurement/order/order-contract.dfy:707` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && olog[i].kind.CloseOrder? && l in LiveLinesOf(PrefixBefore(llog, olog[i].tick), olog[i].subject)` | the lemma's own `Alloy:` pointer | P: a committed CloseOrder found every live line of the order L_CLOSED as of its tick. Q: the same. The same statement. |
| `unit_ord_contract_headerDetailFrozen` | `unit/order.als` | `HeaderDetailFrozen` | `src/procurement/order/order-contract.dfy:725` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && OPreOf(olog, i).Some? && OPreOf(olog, i).value.sStatus != OS_DRAFT` | the lemma's own `Alloy:` pointer | P: a committed order row that read a state not DRAFT leaves the priority, the assignee and the notes as they were. Q: the same. The same statement. |
| `unit_ord_contract_lineClosureByAct` | `unit/order.als` | `LineClosureByAct` | `src/procurement/order/order-contract.dfy:694` | `WellFormed(olog, llog, dlog, items, ba, staff) && n <= \|llog\| && LineStatusAt(llog[..n], l) == Some(L_CLOSED)` | the lemma's own `Alloy:` pointer | P: a line that reads L_CLOSED in a prefix has a committed CloseLine in it; and it reads L_CLOSED in every longer prefix. Q: the same two clauses, by ticks. The same statement. |
| `unit_ord_contract_lineClosureByAct` | `unit/order.als` | `LineClosurePermanent` | `src/procurement/order/order-contract.dfy:700` | `WellFormed(olog, llog, dlog, items, ba, staff) && n1 <= n2 <= \|llog\| && LineStatusAt(llog[..n1], l) == Some(L_CLOSED)` | the lemma's own `Alloy:` pointer | |
| `unit_ord_contract_orderTerminalClosure` | `unit/order.als` | `OrderTerminalClosure` | `src/procurement/order/order-contract.dfy:735` | `WellFormed(olog, llog, dlog, items, ba, staff) && n1 <= n2 <= \|olog\| && OrderStatusAt(olog[..n1], o).Some? && TerminalOrderStatus(OrderStatusAt(olog[..n1], o).value)` | the lemma's own `Alloy:` pointer | P: an order whose status is terminal in a prefix has a terminal status in every longer prefix. Q: an order CLOSED or CANCELED at a tick is CLOSED or CANCELED at every later tick. The same statement. |
| `unit_ord_contract_priorityDefault` | `unit/order.als` | `PriorityDefault` | `src/procurement/order/order-contract.dfy:765` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && olog[i].kind.CreateOrder?` | the lemma's own `Alloy:` pointer | P: a committed CreateOrder's post state has priority OP_UNDEFINED. Q: the same. The same statement. |
| `unit_ord_contract_receiptAccrues` | `unit/order.als` | `ReceiptAccrues` | `src/procurement/order/order-contract.dfy:673` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Committed(llog[i]) && llog[i].kind.RecordReceipt?` | the lemma's own `Alloy:` pointer | P: a committed RecordReceipt's post sReceived is its pre sReceived plus the row's quantity. Q: the same. The same statement. |
| `unit_ord_contract_receiptReverses` | `unit/order.als` | `ReceiptReverses` | `src/procurement/order/order-contract.dfy:680` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Committed(llog[i]) && llog[i].kind.ReverseReceipt?` | the lemma's own `Alloy:` pointer | P: a committed ReverseReceipt's post sReceived is its pre sReceived minus the row's quantity. Q: the same, written as a sum with the negation. The same statement. |
| `unit_ord_contract_submitRequiresStarted` | `unit/order.als` | `SubmitRequiresStarted` | `src/procurement/order/order-contract.dfy:666` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && olog[i].kind.Submit? && d in ServicedOf(PrefixBefore(dlog, olog[i].tick), PrefixBefore(llog, olog[i].tick), olog[i].subject)` | the lemma's own `Alloy:` pointer | P: a committed Submit found every demand its order services IN_PROCESS as of its tick. Q: the same. The same statement. |
| `unit_ord_contract_supplierBindingFrozen` | `unit/order.als` | `SupplierBindingFrozen` | `src/procurement/order/order-contract.dfy:716` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Committed(olog[i]) && OPreOf(olog, i).Some? && OPreOf(olog, i).value.sStatus != OS_DRAFT` | the lemma's own `Alloy:` pointer | P: a committed order row that read a state not DRAFT leaves the supplier binding as it was. Q: the same. The same statement. |
| `unit_ord_noRecordedRefusalWithoutGenesis` | `unit/order.als` | `OrderNoRecordedRefusalWithoutGenesis` | `src/procurement/order/order-contract.dfy:791` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && Recorded(olog, OShapeOf, i) && !Committed(olog[i])` | the lemma's own `Alloy:` pointer | P: a recorded row of the order log, and of the line log, that did not commit has a committed row on its subject before it. Q: the recording law on both order logs. The same statement, one lemma per log. |
| `unit_ord_noRecordedRefusalWithoutGenesis` | `unit/order.als` | `LineNoRecordedRefusalWithoutGenesis` | `src/procurement/order/order-contract.dfy:797` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Recorded(llog, LShapeOf, i) && !Committed(llog[i])` | the lemma's own `Alloy:` pointer | |
| `unit_ord_nothingAfterRetire` | `unit/order.als` | `OrderNothingAfterRetire` | `src/procurement/order/order-contract.dfy:777` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|olog\| && j < \|olog\| && Committed(olog[i]) && olog[i].kind.DeleteOrder? && Committed(olog[j]) && olog[j].subject == olog[i].subject` | the audit of 2026-11-18 | P: a committed DeleteOrder's tick does not precede the tick of any committed row on the same order; the same for a committed RemoveLine on the line log. Q: nothing commits on an order after its committed delete, nor on a line after its committed remove. The same statement, one lemma per log. |
| `unit_ord_nothingAfterRetire` | `unit/order.als` | `LineNothingAfterRetire` | `src/procurement/order/order-contract.dfy:784` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && j < \|llog\| && Committed(llog[i]) && llog[i].kind.RemoveLine? && Committed(llog[j]) && llog[j].subject == llog[i].subject` | the audit of 2026-11-18 | |
| `unit_ord_removeRequiresDetached` | `unit/order.als` | `RemoveRequiresDetached` | `src/procurement/order/order-contract.dfy:771` | `WellFormed(olog, llog, dlog, items, ba, staff) && i < \|llog\| && Committed(llog[i]) && llog[i].kind.RemoveLine?` | the lemma's own `Alloy:` pointer | P: a committed RemoveLine read a line state with no paired demand. Q: the same. The same statement. |
| `unit_ord_supplierBindingPinAgreesHolds` | `unit/order.als` | `BindingsSound` | `src/procurement/order/order-contract.dfy:744` | `WellFormed(olog, llog, dlog, items, ba, staff) && StrictTicks(ba) && i < \|olog\| && Committed(olog[i]) && SupplierWritten(olog[i].kind).Some?` | the lemma's own `Alloy:` pointer | P: a committed row that writes a supplier binding writes one that agrees with the affiliate log. Q: a committed CreateOrder or UpdateSupplier's binding pin agrees. The same statement: those are the kinds that write a supplier. P's premise StrictTicks(ba) is the affiliate log's own order, which its append ensures. |
| `unit_ordr_receivedIsAccumulated` | `unit/order_received.als` | `ReceivedIsAccumulated` | `src/procurement/order/order-contract.dfy:688` | `WellFormed(olog, llog, dlog, items, ba, staff) && n <= \|llog\|` | the name | P: for every line and every prefix of the line log, the stored sReceived is the sum of its committed receipts minus the sum of its reversals. Q: the same at every tick, written case by case for up to two postings. P implies Q: P holds for any number of postings. |

## `receiving/receiver`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_rcv_lineAttachAgreesWithPartner` | `unit/receiver.als` | `LineAdmitsAttach` | `src/receiving/receiver/receiver.dfy:1359` | `(k.AppendAttribution? && AppendAttributionViol(prefix, oat, l, k.attribution) == {}) \|\| (k.AddReceivingLine? && k.withAttribution.Some? && AddLineViol(prefix, rvt, oat, it, l, k) == {})` | the lemma's own `Alloy:` pointer | P: a line-side attach that its guard admits (an AppendAttribution, or an AddReceivingLine with an attribution) names an attribution whose AttachAttribution guard raises nothing. Q: a committed line-side attach names an attribution with no committed attach before it. P implies Q: that guard raises RAttributionStarted exactly when the attribution has a committed row before (OAViol, receiver.dfy:316), so 'raises nothing' is 'not started'. |

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
| `unit_collapse_eachIdentity` | `uom_collapse.als` | `EachIdentity` | `src/reference-data/item/uom-collapse.dfy:79` | `q.Keys == {Each}` | the name | P: collapsing a quantity whose only key is Each returns it unchanged. Q: for such a quantity the collapse's Each amount is the quantity's. P implies Q. Alloy's premise hasGroup says its fold nodes exist for the pair; Dafny's Collapse is a total function. |
| `unit_collapse_eachKeyed` | `uom_collapse.als` | `EachKeyed` | `src/reference-data/item/uom-collapse.dfy:69` | none | the name | P: Collapse(sch, q)'s keys are within {Each}, and it is in normal form. Q: the collapse's keys are within Each. P implies Q. |
| `unit_collapse_singleIsToEach` | `uom_collapse.als` | `SingleIsToEach` | `src/reference-data/item/uom-collapse.dfy:71` | `q.Keys == {u} && u in sch.factor` | the name | P: collapsing a quantity with one unit the scheme configures gives ToEach of its amount, keyed by Each. Q: the same. The same statement. |
| `unit_collapse_twoUnitFolds` | `uom_collapse.als` | `TwoUnitFolds` | `src/reference-data/item/uom-collapse.dfy:89` | `q.Keys == {u1, u2} && u1 != u2 && Covers(sch, q)` | the name | P: for a quantity with two units the scheme covers, the Each total is the sum of the two converted amounts, and when it is not zero the collapse is that total keyed by Each. Q: when the two-unit collapse has an Each amount, it is that sum. P implies Q. |
| `unit_item_eachConfigured` | `item.als` | `EachConfigured` | `src/reference-data/item/uom.dfy:48` | none | the lemma's own `Alloy:` pointer | P: every well-formed scheme has Each among its units with factor one. Q: every scheme configures Each with factor one. The same statement. In Dafny the scheme is a subset type, so the verifier enforces it wherever a scheme is built; in Alloy it is the fact UomSchemeWF. |
| `unit_item_lifecycleShape` | `item.als` | `ItemLifecycleShape` | `src/reference-data/item/item-contract.dfy:266` | `WellFormed(log, ba) && i < \|log\| && Committed(log[i])` | the lemma's own `Alloy:` pointer | P: a committed row is the first on its item exactly when it is a Create, and a prior head is never a retire. Q: the same two clauses. The same statement. |
| `unit_item_nothingAfterRetire` | `item.als` | `ItemNothingAfterRetire` | `src/reference-data/item/item-contract.dfy:278` | `WellFormed(log, ba) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the lemma's own `Alloy:` pointer | P: of two committed rows on one item, the earlier is not a retire. Q: no committed row of an item follows its committed retire. The same statement. |
| `unit_item_retireIsTombstone` | `item.als` | `ItemRetireIsTombstone` | `src/reference-data/item/item-contract.dfy:284` | `WellFormed(log, ba) && i < \|log\| && Committed(log[i]) && log[i].kind.RetireItem?` | reading | P: a committed retire's post state is its pre state, and the item is not live after it. Q: the same. The same statement. |
| `unit_item_supplyOwnership` | `item.als` | `SupplyOwnershipHolds` | `src/reference-data/item/item-contract.dfy:252` | `WellFormed(log, ba)` | the lemma's own `Alloy:` pointer | P: in a well-formed log every supply belongs to exactly one item. Q: no supply is among two items' committed supplies. The same statement. |
| `unit_item_supplyPinCurrencyHolds` | `item.als` | `SupplierPinsSoundHolds` | `src/reference-data/item/item-contract.dfy:259` | `WellFormed(log, ba) && StrictTicks(ba)` | reading | P's second clause (SupplyPinCurrency): every supply's vendor pin was current at its write. Q: every committed write's vendor pins are current at its tick. The same statement. P's premise StrictTicks(ba) is the affiliate log's own order. |
| `unit_item_toEachIdentity` | `item.als` | `ToEachIdentity` | `src/reference-data/item/uom.dfy:50` | none | the audit of 2026-11-18 | P: for a well-formed scheme, ToEach(s, Each, amt) == Some(amt). Q: under the ring axioms, converting an amount already in each returns it. The same statement. EachConfigured alone says the factor is one, not that the conversion is the identity. |

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
| `int_ii_contract_closureIsTerminal` | `integration/inventory_item.als` | `ClosureIsTerminal` | `src/resources/inventory-item/inventory-item-contract.dfy:330` | `WellFormed(log, items) && n1 <= n2 <= \|log\| && Started(log[..n1], ii) && !LiveAt(log[..n1], ii)` | the lemma's own `Alloy:` pointer | P: an inventory item started and not live in a prefix is not live in any longer prefix. Q: an inventory item with a state and not live at a tick is not live at any later tick, on the composed stack. The same statement. |
| `int_ii_contract_stateFunction` | `integration/inventory_item.als` | `StateIsFunctionOnceStarted` | `src/resources/inventory-item/inventory-item-contract.dfy:313` | `WellFormed(log, items) && n1 <= n2 <= \|log\| && StateAt(log[..n1], ii).Some?` | the lemma's own `Alloy:` pointer | P: an inventory item with a state in a prefix has one in every longer prefix. Q: the same, by ticks, on the composed stack. The same statement. |
| `unit_ii_contract_bornLive` | `unit/inventory_item.als` | `BornLive` | `src/resources/inventory-item/inventory-item-contract.dfy:324` | `WellFormed(log, items) && i < \|log\| && Committed(log[i]) && ii in Touches(log[i]) && !Started(log[..i], ii)` | the lemma's own `Alloy:` pointer | P: a committed row that touches an inventory item not started before leaves it live. Q: at the first tick an inventory item has a state, it is live. The same statement. |
| `unit_ii_contract_closureIsTerminal` | `unit/inventory_item.als` | `ClosureIsTerminal` | `src/resources/inventory-item/inventory-item-contract.dfy:330` | `WellFormed(log, items) && n1 <= n2 <= \|log\| && Started(log[..n1], ii) && !LiveAt(log[..n1], ii)` | the lemma's own `Alloy:` pointer | P: an inventory item started and not live in a prefix is not live in any longer prefix. Q: an inventory item with a state and not live at a tick is not live at any later tick. The same statement. |
| `unit_ii_contract_liveHaveState` | `unit/inventory_item.als` | `LiveHaveState` | `src/resources/inventory-item/inventory-item-contract.dfy:318` | `WellFormed(log, items) && n <= \|log\| && LiveAt(log[..n], ii)` | the lemma's own `Alloy:` pointer | P: an inventory item live in a prefix has a state in it. Q: an inventory item live at a tick has a state at it. The same statement. |
| `unit_ii_contract_readBack` | `unit/inventory_item.als` | `CommittedWritesReadBack` | `src/resources/inventory-item/inventory-item-contract.dfy:342` | `WellFormed(log, items) && i < \|log\| && Committed(log[i]) && ii in Touches(log[i])` | the lemma's own `Alloy:` pointer | Q: the state of a touched item at a committed row's tick is the row's post for it. In Dafny the post of row i for an item is by definition the state read right after the row (PostFor), and P states its value: the role effect of the row's kind on the prefix. P implies Q: the read at the row's tick is the read right after it. |
| `unit_ii_contract_stateFunction` | `unit/inventory_item.als` | `StateIsFunctionOnceStarted` | `src/resources/inventory-item/inventory-item-contract.dfy:313` | `WellFormed(log, items) && n1 <= n2 <= \|log\| && StateAt(log[..n1], ii).Some?` | the lemma's own `Alloy:` pointer | P: an inventory item with a state in a prefix has one in every longer prefix. Q: the same, by ticks. The same statement. |
| `unit_ii_contract_touchesLiveness` | `unit/inventory_item.als` | `TouchesDetermineLiveness` | `src/resources/inventory-item/inventory-item-contract.dfy:336` | `WellFormed(log, items) && i < \|log\| && Committed(log[i]) && ii in Touches(log[i])` | the lemma's own `Alloy:` pointer | P: after a committed row, an item it touches is live exactly when the row does not retire it. Q: the same two directions. The same statement. |
| `unit_invmet_frameworkMatchesLog` | `metrics.als` | `FrameworkMatchesLog` | `src/resources/inventory-item/metrics.dfy:387` | `Aligned(log, at) && StrictChronology(log, at)` | the name | P: under aligned clocks and strict chronology, the measurement framework's value at an instant is the actual of the log's as-of seat. Q: the same, under the same two premises. The same statement. |
| `unit_invmet_partitionAdditivity` | `metrics.als` | `PartitionAdditivity` | `src/resources/inventory-item/metrics.dfy:199` | `x.cAsOf == z.cAsOf && y.cAsOf == z.cAsOf && MembersOf(log, at, x) !! MembersOf(log, at, y) && MembersOf(log, at, z) == MembersOf(log, at, x) + MembersOf(log, at, y)` | the name | P: a cell whose members are the disjoint union of two cells' members, all as of one instant, has the sum of their totals. Q: the same. The same statement. |
| `unit_invmet_quietPeriodRepeats` | `metrics.als` | `QuietPeriodRepeats` | `src/resources/inventory-item/metrics.dfy:255` | `c1.cTenant == c2.cTenant && c1.cItem == c2.cItem && c1.cNode.None? && c2.cNode.None? && AtOrBefore(c1.cAsOf, c2.cAsOf) && forall i :: 0 <= i < \|log\| && Committed(log[i]) ==> !(EarlierThan(c1.cAsOf, at(log[i])) && AtOrBefore(at(log[i]), c2.cAsOf))` | the name | P: two cells of one tenant and item, with no level, and no committed row stamped between their instants, have the same members and total. Q: the same, under aligned clocks. P implies Q: P needs no clock premise. |
| `unit_occ_committedUnitsValid` | `unit/inventory_item.als` | `CommittedUnitsValid` | `src/resources/inventory-item/tests/inventory-item-tests.dfy:363` | `IIM.WellFormed(log, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Consume?` | the name | P: a committed Consume's amount uses only units of its item's scheme. Q: the same. The same statement. |
| `unit_occ_expiryNeverLengthens` | `unit/inventory_item.als` | `ExpiryNeverLengthens` | `src/resources/inventory-item/tests/inventory-item-tests.dfy:342` | `IIM.WellFormed(log, items) && i < \|log\| && Committed(log[i]) && !log[i].kind.Create? && PreT(log, i).sExpiration.Some?` | the name | P: a committed row other than a Create that read an expiry leaves an expiry no later than it. Q: the same. The same statement. |
| `unit_occ_itemPinCurrencyHolds` | `unit/inventory_item.als` | `ItemPinCurrencyHolds` | `src/resources/inventory-item/inventory-item-contract.dfy:361` | `WellFormed(log, items)` | the lemma's own `Alloy:` pointer | P: in a well-formed log every committed Create's item pin is current at its tick. Q: the same. The same statement. |
| `unit_occ_lpnUniqueAmongStarted` | `unit/inventory_item.als` | `LicensePlateUniqueHolds` | `src/resources/inventory-item/inventory-item-contract.dfy:348` | `WellFormed(log, items)` | reading | P: in a well-formed log the items with committed history have distinct license plates. Q: two distinct started inventory items have different license plates. The same statement. |
| `unit_occ_mergeConserves` | `unit/inventory_item.als` | `MergeConserves` | `src/resources/inventory-item/tests/inventory-item-tests.dfy:332` | `IIM.WellFormed(log, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Merge?` | the name | P: a committed Merge's post actual is the sum of the survivor's and the absorbed item's read actuals. Q: the same. The same statement. |
| `unit_occ_noCommittedOverdraw` | `unit/inventory_item.als` | `NoCommittedOverdraw` | `src/resources/inventory-item/tests/inventory-item-tests.dfy:294` | `IIM.WellFormed(log, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Consume?` | the name | P: a committed Consume's amount is within the available quantity it read. Q: the same. The same statement. |
| `unit_occ_noResurrection` | `unit/inventory_item.als` | `NoResurrection` | `src/resources/inventory-item/tests/inventory-item-tests.dfy:302` | `IIM.WellFormed(log, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Create?` | the name | P: a committed Create's item has no committed history before it. Q: the same. The same statement. |
| `unit_occ_sealedOnlyBySeal` | `unit/inventory_item.als` | `SealedOnlyBySeal` | `src/resources/inventory-item/tests/inventory-item-tests.dfy:353` | `IIM.WellFormed(log, items) && i < \|log\| && Committed(log[i]) && !log[i].kind.Seal?` | the name | P: a committed row other than a Seal does not move the fill into SEALED. Q: the same. The same statement. |
| `unit_occ_serialUniqueAmongStarted` | `unit/inventory_item.als` | `SerialNumberUniquePerItemHolds` | `src/resources/inventory-item/inventory-item-contract.dfy:354` | `WellFormed(log, items)` | reading | P: in a well-formed log a serial number is unique within a tenant and an item. Q: two distinct started inventory items of one tenant and item, one with a serial, have different serials. The same statement. |
| `unit_occ_splitConserves` | `unit/inventory_item.als` | `SplitConserves` | `src/resources/inventory-item/tests/inventory-item-tests.dfy:310` | `IIM.WellFormed(log, items) && i < \|log\| && Committed(log[i]) && log[i].kind.Split?` | the name | P: a committed Split's remainder and split-off actuals sum to the actual it read. Q: the same. The same statement. |
| `unit_occ_terminalRetirement` | `unit/inventory_item.als` | `ClosureIsTerminal` | `src/resources/inventory-item/inventory-item-contract.dfy:330` | `WellFormed(log, items) && n1 <= n2 <= \|log\| && Started(log[..n1], ii) && !LiveAt(log[..n1], ii)` | reading | P: an inventory item started and not live in a prefix is not live in any longer prefix. Q: an inventory item with a last touch and not live at a tick is not live at any later tick. The same statement. |
| `unit_plc_affirmIsInert` | `pool_lifecycle.als` | `PoolAffirmIsInert` | `src/resources/inventory-item/inventory-pool-contract.dfy:429` | `WellFormed(log) && i < \|log\| && Committed(log[i]) && log[i].kind.AffirmPool?` | the lemma's own `Alloy:` pointer | P: a committed AffirmPool's post state is its pre state (and its holdings are unchanged). Q: a committed affirmation's post is its pre. P implies Q. |
| `unit_plc_affirmNeverCreatedIsNotClosed` | `pool_lifecycle.als` | `PoolAffirmNeverCreatedIsNotClosed` | `src/resources/inventory-item/inventory-pool-contract.dfy:435` | `WellFormed(log) && i < \|log\| && log[i].kind.AffirmPool? && Refused(log[i]) && PreOf(log, i).None?` | the lemma's own `Alloy:` pointer | P: an AffirmPool refused on a pool with no state does not carry RPoolClosed. Q: the same. The same statement. |
| `unit_plc_noRecordedRefusalWithoutGenesis` | `pool_lifecycle.als` | `PoolNoRecordedRefusalWithoutGenesis` | `src/resources/inventory-item/inventory-pool-contract.dfy:441` | `WellFormed(log) && i < \|log\| && Recorded(log, ShapeOf, i) && !Committed(log[i])` | the lemma's own `Alloy:` pointer | P: a recorded row of the pool log that did not commit sits on a pool started before it. Q: the recording law on the pool log. The same statement. |
| `unit_plc_nothingAfterRetire` | `pool_lifecycle.als` | `PoolNothingAfterRetire` | `src/resources/inventory-item/inventory-pool-contract.dfy:402` | `WellFormed(log) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the audit of 2026-11-18 | P: of two committed rows on one pool, the earlier is not a RetirePool. Q: nothing commits on a pool after its committed retire (lc/nothingAfterRetire on the pool log). The same statement. |
| `unit_pool_homogeneous` | `inventory_pool.als` | `PoolMembersAgree` | `src/resources/inventory-item/inventory-pool-contract.dfy:382` | `WellFormed(log)` | the lemma's own `Alloy:` pointer | P: in a well-formed pool log every held item agrees with its pool on the item and on the tenant. Q: every item a pool holds at a tick is of the pool's item. P implies Q: Q is P's item clause. |
| `unit_pool_membershipExclusive` | `inventory_pool.als` | `PoolMembershipExclusive` | `src/resources/inventory-item/inventory-pool-contract.dfy:388` | `WellFormed(log)` | the lemma's own `Alloy:` pointer | P: in a well-formed pool log an inventory item is held by at most one pool, with transfers in scope. Q: at any tick an inventory item is held by at most one pool; the second command adds a transfer to the scope. The same statement for both commands. |
| `unit_pool_reversalDisciplineHolds` | `inventory_pool.als` | `PoolLogChained` | `src/resources/inventory-item/inventory-pool-contract.dfy:395` | `WellFormed(log)` | the lemma's own `Alloy:` pointer | P's second clause: a well-formed pool log satisfies ReversalDiscipline (and TransferPairing). Q: reversalDiscipline over the committed rows. The same statement. |
| `unit_pool_sameTenant` | `inventory_pool.als` | `PoolMembersAgree` | `src/resources/inventory-item/inventory-pool-contract.dfy:382` | `WellFormed(log)` | the lemma's own `Alloy:` pointer | P: in a well-formed pool log every held item agrees with its pool on the item and on the tenant. Q: every item a pool holds at a tick is of the pool's tenant. P implies Q: Q is P's tenant clause. |
| `unit_pool_stampsMonotone` | `inventory_pool.als` | `PoolStampsMonotoneHolds` | `src/resources/inventory-item/inventory-pool-contract.dfy:415` | `WellFormed(log)` | the lemma's own `Alloy:` pointer | P: no committed write of a pool is dated before an earlier committed write of the same pool. Q: the same. The same statement. |

## `resources/kanban_card`

| Check | Root | Dafny lemma | At | Premises | Matched by | Why the lemma implies the check |
| --- | --- | --- | --- | --- | --- | --- |
| `unit_cyc_closureIsTerminal` | `cycle_occurrences.als` | `ClosureIsTerminal` | `src/resources/kanban-card/kanban-card-contract.dfy:447` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && ClosedAt(log[..i], log[i].subject)` | the lemma's own `Alloy:` pointer | P: a row on a cycle closed in the prefix before it does not commit. Q: an occurrence on a cycle closed strictly before its tick is not committed. The same statement. |
| `unit_cyc_forwardMonotone` | `cycle_occurrences.als` | `ForwardMonotone` | `src/resources/kanban-card/kanban-card-contract.dfy:392` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && IsForward(log[i].kind)` | the lemma's own `Alloy:` pointer | P: a committed forward operation's post status is strictly after its pre status in the region order. Q: the same. The same statement. |
| `unit_cyc_noPoolBeforeInProcess` | `cycle_occurrences.als` | `NoPoolBeforeInProcess` | `src/resources/kanban-card/kanban-card-contract.dfy:398` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && PostOf(log, i).Some? && RegionBefore(PostOf(log, i).value.sStatus, IN_PROCESS)` | the lemma's own `Alloy:` pointer | P: a committed row whose post status is before IN_PROCESS leaves no pool. Q: the same. The same statement. |
| `unit_cyc_poolExclusiveWhileLive` | `cycle_occurrences.als` | `PoolExclusiveWhileLive` | `src/resources/kanban-card/kanban-card-contract.dfy:430` | `WellFormed(log, cards, plog, items, cfg) && LiveCycleAt(log, c1) && StateOfCycleAt(log, c1).Some? && StateOfCycleAt(log, c1).value.sPool == Some(e) && LiveCycleAt(log, c2) && StateOfCycleAt(log, c2).Some? && StateOfCycleAt(log, c2).value.sPool == Some(e)` | the lemma's own `Alloy:` pointer | P: two live cycles whose state holds the same pool id are the same cycle. Q: at each tick a pool has at most one live cycle. P implies Q: P is stated over the pool id, which is stronger than Alloy's resolved pool. |
| `unit_cyc_poolFrozenOnceAttached` | `cycle_occurrences.als` | `PoolFrozenOnceAttached` | `src/resources/kanban-card/kanban-card-contract.dfy:405` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && !log[i].kind.StartProcessing? && !log[i].kind.ProductionFailure? && PreOf(log, i).Some? && PreOf(log, i).value.sPool.Some?` | the lemma's own `Alloy:` pointer | P: a committed row other than a StartProcessing or a ProductionFailure that read a pool leaves the same pool. Q: the same. The same statement. |
| `unit_cyc_poolProvenance` | `cycle_occurrences.als` | `PoolProvenance` | `src/resources/kanban-card/kanban-card-contract.dfy:414` | `WellFormed(log, cards, plog, items, cfg) && StateOfCycleAt(log, c).Some? && StateOfCycleAt(log, c).value.sPool == Some(e)` | the lemma's own `Alloy:` pointer | P: a cycle whose state holds a pool has a committed StartProcessing of its own naming that pool. Q: the same, at each tick. The same statement. |
| `unit_cyc_quantityFixedAtGenesis` | `cycle_occurrences.als` | `QuantityFixedAtGenesis` | `src/resources/kanban-card/kanban-card-contract.dfy:453` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && !log[i].kind.Request? && PreOf(log, i).Some?` | the lemma's own `Alloy:` pointer | P: a committed row other than a Request leaves the quantity override it read. Q: the same. The same statement. |
| `unit_cyr_abandonedIsWithdrawn` | `cycle_retire.als` | `AbandonedIsWithdrawn` | `src/resources/kanban-card/kanban-card-contract.dfy:498` | none | the lemma's own `Alloy:` pointer | P: a cycle is abandoned exactly when it has a committed Withdraw. Q: the same, at each tick. The same statement, definitional on both sides. |
| `unit_cyr_attachedOnceById` | `cycle_retire.als` | `PoolAttachedOnce` | `src/resources/kanban-card/kanban-card-contract.dfy:421` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].kind.StartProcessing? && log[j].kind.StartProcessing? && log[i].kind.pool == log[j].kind.pool` | reading | P: two committed StartProcessing rows that name the same pool id are the same row. Q: a pool id is named by at most one committed StartProcessing. The same statement. |
| `unit_cyr_closedBeforeSuccessorGenesis` | `cycle_retire.als` | `ClosedBeforeSuccessorGenesis` | `src/resources/kanban-card/kanban-card-contract.dfy:439` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && log[i].kind.Request? && log[i].subject.precededBy.Some?` | the lemma's own `Alloy:` pointer | P: a committed Request of a cycle with a predecessor found that predecessor closed in the prefix before it. Q: the same. The same statement. |
| `unit_cyr_noRecordedRefusalWithoutGenesis` | `cycle_retire.als` | `CycleNoRecordedRefusalWithoutGenesis` | `src/resources/kanban-card/kanban-card-contract.dfy:491` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Recorded(log, ShapeOf, i) && !Committed(log[i])` | the lemma's own `Alloy:` pointer | P: a recorded row of the cycle log that did not commit sits on a cycle started before it. Q: the recording law on the cycle log. The same statement. |
| `unit_cyr_nothingAfterRetire` | `cycle_retire.als` | `CycleNothingAfterRetire` | `src/resources/kanban-card/kanban-card-contract.dfy:483` | `WellFormed(log, cards, plog, items, cfg) && i < j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].subject == log[j].subject` | the audit of 2026-11-18 | P: of two committed rows on one cycle, the earlier is not of the Retire shape. Q: nothing commits on a cycle after either of its retires (lc/nothingAfterRetire on the cycle log). The same statement. |
| `unit_cyr_poolAttachedOnce` | `cycle_retire.als` | `PoolAttachedOnce` | `src/resources/kanban-card/kanban-card-contract.dfy:421` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && j < \|log\| && Committed(log[i]) && Committed(log[j]) && log[i].kind.StartProcessing? && log[j].kind.StartProcessing? && log[i].kind.pool == log[j].kind.pool` | the lemma's own `Alloy:` pointer | P: two committed StartProcessing rows that name the same pool id are the same row. Q: the same. The same statement. |
| `unit_cyr_startedPoolLive` | `cycle_retire.als` | `StartedPoolLive` | `src/resources/kanban-card/kanban-card-contract.dfy:477` | `WellFormed(log, cards, plog, items, cfg) && i < \|log\| && Committed(log[i]) && log[i].kind.StartProcessing?` | the name | P: a committed StartProcessing names a pool live as of its tick. Q: the same. The same statement. |
| `unit_cyr_startedPoolLive` | `cycle_retire.als` | `StartedPoolLive` | `src/resources/kanban-card/kanban-card.dfy:419` | none | the name | |

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
