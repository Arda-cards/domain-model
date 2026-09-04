# Parametric modules: qualify open-parameters, re-open instances in roots, cast `univ` joins

Found building `meta/intent_log/intent_log[Key, Sem]` (DT-027, 2026-08-28) — a parametric
module that itself opens the parametric spine `subject_log[Key, IntentRec]` and a shared,
non-parametric vocabulary module (`meta/intent_log/semantics`).

## 1. An open-PARAMETER is resolved before module instances collapse

`open meta/intent_log/intent_log[Peg, HoldSem]` fails with *"The name HoldSem is ambiguous:
sig semantics/HoldSem · sig hold/semantics/HoldSem"* whenever the root ALSO opens the
vocabulary module directly. Names used in a `open …[params]` list are resolved in
`CompModule.resolveParams` — before the parser deduplicates the instance's transitive opens —
so a sig reachable both directly and through the parametric instance has two paths. Body
references (`HoldSem` in a `run`) resolve fine after the collapse; only the parameter list is
affected. The same class as DT-024's E4b note (`util/ordering[mt/Tick]`).

**Rule:** alias the vocabulary open and pass QUALIFIED parameters —

```alloy
open meta/intent_log/semantics as sem
open meta/intent_log/intent_log[CardCycle, sem/HoldSem] as claim
```

## 2. A root cannot see a library's alias for a parametric instance

A root that opens an exemplar/library which opened `intent_log[Cart, sem/HoldSem] as claim`
gets *"The name claim/ReserveOcc cannot be found"*. Non-parametric aliases (`jlog/…` in the
call_first_saga root) are visible; parametric-instance aliases are not. **Rule:** the root
re-opens the instance with IDENTICAL parameters and the same alias — identical parameters
re-open the SAME instance (the DT-024 rule for `subject_log`), so nothing is duplicated:

```alloy
open conventions/intent_log/intent_log
open meta/intent_log/semantics as sem
open meta/intent_log/intent_log[Cart, sem/HoldSem] as claim   // same instance as the library's
```

A predicate name shared by the library and the instances (`guarantees`) must then be
qualified in the root (`intent_log/guarantees`) — "This name is ambiguous due to multiple
matches".

## 3. `univ`-typed fields need a cast before a join

`ownerVersion: one univ` lets a meta module carry an identity the applying module binds to its
own atoms (the runtime's `owner_rid`); `arche` is kernel-typed `one Occurrence` since DT-029 E1 (total since ruling A, 2026-09-03: `o.arche = o` is self-initiation).
Either way a join to a PER-INSTANTIATION field (`p.arche.subject` — every `subject_log` instance
declares its own `subject`) is ambiguous — cast first: `(p.arche & pour/ReserveOcc).subject`.
(`p.arche.tick` needs no cast: `tick` is the kernel's.)

## 3a. A `univ` binding names a MARKER atom, never a kind SET

`act: one univ` on a sub-intent is bound by the applying module. `o.act = LoadOcc` compares the
singleton binding with the SET of all `LoadOcc` atoms — true only when exactly one such atom
exists, so witnesses pass by scope coincidence and laws quantify over the wrong thing. Bind to a
marker atom (`abstract sig CartAct {} one sig A_LOAD, A_PARK extends CartAct {}`; `o.act = A_LOAD`)
— the act's occurrence does not exist yet at reservation time, and a kind set is not a value.
(Caught writing the E7 rung for `conventions/intent_log`, 2026-08-28.)

## 4. Never redirect the solver log INTO the `-o` directory

`alloy exec -f -o DIR` wipes DIR before running. A shell redirect `> DIR/run.log` created
before the JVM starts is deleted with it — the run's verdicts survive only in
`DIR/receipt.json` and the solution files. Log beside the output directory, never inside.

## Timing reference (glucose, Apple silicon, 2026-08-28)

`meta/intent_log/tests/intent_log.als` (two instances, 11 runs + 13 checks): 209 s at
`for 5`; a single check at `for 6` ≈ 3 s, but `guarantees` (the twelve-law conjunction)
is the heavy one (57 s at `for 4`). `for 5` is the gate scope; `for 6` on the whole root
exceeded 10 minutes.

## Open parameters resolve at parse time — qualify EVERY one (B-mov, 2026-09-04)

A ROOT that instantiates a parametric module with a sig reachable by several import paths fails at parse time —
"The name InventoryPool is ambiguous" — although the same name in scopes and expressions dedups. Open the types
module ALIASED and qualify the parameter (`open resources/inventory_item/inventory_pool as ip` +
`intent_log[ip/InventoryPool, sem/MoveSem]`; the soak slices' `kt/CardCycle`); the instance dedups with the
module's own. A module opening the instance by one path parses; the root is where paths multiply — a
never-executed root hides this until its first run. **Rule (MINESWEEPER): qualify EVERY open parameter, in modules
too** — the loud failure is a property of several candidates being visible; with exactly one same-named sig in
scope (a mock's, a peer module's) the parameter resolves SILENTLY to it and every verdict reads green against the
wrong import. Gate-grep candidate: `grep -rn '^open .*\[[A-Za-z]' alloy` lists unqualified parameters.
