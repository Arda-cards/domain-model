# A refused SECOND genesis carries a `pre` — recording rules must exclude create occurrences

**Symptom (MPBOT-11 M2, 2026-10-01, the first green run of the recording law):** the witness
`unit_lc_refusedGenesisNotRecorded` ("a refused genesis is NOT recorded", `expect 1`) came back
UNSAT on the generic lifecycle root, and `unit_plc_refusedSecondGenesisNotRecorded` the same on the
pool root, while the theorem `noRecordedRefusalWithoutGenesis` held. The formula shipped in the
ticket was `recorded[o] = committed[o] or (refusedAtAdmission[o] and some o.pre)`.

**Mechanism:** the subject-log spine's chaining gives EVERY occurrence on a started subject a `pre`
(the subject's latest record, the tombstone included after a retire). A create is refused by the
generic module only when the subject is already started (`createViol = startedBefore[o] => rStarted`),
so in the generic fixture every refused genesis is a refused SECOND genesis — and it has a `pre`.
`some o.pre` therefore counts it as "refused on a hosted subject" = recorded, which contradicts the
runtime (a second `CREATE` on an existing id is refused before any row is written, COORDINATOR-Q179
D7) and the ticket's own prose ("a refused genesis is never recorded").

**Rule:** a recording predicate over `log/SubjectOcc` must exclude the create shape explicitly:
`recorded[o] = committed[o] or (refusedAtAdmission[o] and o not in CreateOcc and some o.pre)`
(`meta/subject_log/lifecycle.als`). Do not read `some o.pre` as "live": under chaining it equals
`startedBefore[o]` (closed subjects included); the `CreateOcc` exclusion is what carries the
"never a genesis" clause.

**Discipline:** when a definition ships with prose, enumerate the prose's boundary cases against the
formula (here: "a refused genesis" × "has a pre") before the run; a witness written from the ruling
is the spec — when it fails at green time, suspect the definition first.
