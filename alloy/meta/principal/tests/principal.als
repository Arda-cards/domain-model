module meta/principal/tests/principal
// Reflects dafny-domain src/meta/tests/principal-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/principal/principal   // re-exports meta/kernel (Entity, resolve, …)

/*
 * Minimal sanity for `Principal`, plus confirmation it is fully an `Entity` (identity resolves).
 * SAT = a witnessing instance; UNSAT (check) = property holds.
 *
 * DECISION #2 (NOT Scoped) needs no command: `Principal extends Entity` is a SIBLING of `Scoped`, so
 * `Principal & Scoped` is empty by TYPING (the analyzer flags the intersection as always-disjoint). The
 * type system enforces "global, never tenant-scoped" more strongly than any runtime fact could.
 */

// Two distinguishable principals (distinct handles, and distinct eIds by the kernel) coexist.
run unit_principal_loads {
  some disj p, q: Principal | p.name != q.name
} for 4 expect 1

// DECISION #1 — fully an Entity: a principal's identity resolves back to it (`resolve[eId] = p`).
assert unit_principal_resolvesAsEntity { all p: Principal | resolve[p.eId] = p }
check unit_principal_resolvesAsEntity for 6 expect 0

// The readable handle is a KEY: equal handles imply the same principal.
assert unit_principal_nameIsKey { all p, q: Principal | p.name = q.name implies p = q }
check unit_principal_nameIsKey for 6 expect 0

// A principal is recoverable from its handle (`principalNamed` round-trips).
assert unit_principal_recoverable { all p: Principal | principalNamed[p.name] = p }
check unit_principal_recoverable for 6 expect 0
