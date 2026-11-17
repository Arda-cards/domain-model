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
