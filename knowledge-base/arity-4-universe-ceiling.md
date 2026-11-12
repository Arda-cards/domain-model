# Arity-4 relations die past ~215 atoms — confine them to dedicated roots

Kodkod (Alloy's backend) cannot represent an **arity-4 relation** once the command's
universe exceeds roughly **215 atoms**. Domain-log universes routinely exceed that, so
any arity-4 relation reachable from a big root kills the run — not with a clean error,
but with translation blow-ups or capacity failures.

## The two mitigations in the tree (follow them, don't re-discover)

1. **Split the dependency cone.** `meta/time` was split (2026-07-02) into `instant.als`
   (the bare axis — what `meta/occurrence` and hence the whole action/log cone opens)
   and `time.als` (which adds the arity-4 instant→duration metric). Cheap vocabulary an
   entire cone must open goes in a file with **no** arity-4 relations.
2. **The confined-root pattern.** A file whose formulation needs an arity-4 relation
   (a Σ over three keys, a case-wise accumulate) gets its own module opened **only** by
   one dedicated test root, never by the module's main libraries. Precedents:
   `operations/demand/demand_quantity.als` (which replaced `demand_reset.als` with TN-004) and
   `procurement/order/order_received.als` —
   each verified in its own root with a small universe, invisible to every other cone.

## Checking

`make check-budget` estimates the largest command universe per root and warns past the
ceiling. It is a **heuristic**: unscoped sigs at the `for N` default are not counted —
treat its warnings as real and its silence as advisory only. The ceiling matters only
when the cone actually contains an arity-4 relation; a >215 estimate over an arity-≤3
cone is fine.

## Symptom to recognize

A root that was green becomes pathologically slow or fails in translation after an
`open` was added — first suspect: the new open pulled an arity-4 relation into a big
universe. Check the cone (`tools/cone.sh <root>`) before debugging the model.
