module meta/time/tests/duration
// Reflects dafny-domain src/meta/tests/time-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/time/duration

/*
 * Sanity suite for the Duration VALUE TYPE (meta/time/duration) — independent of the instant→duration
 * metric (that is verified in tests/time). `Duration` is opaque and totally ordered by `dlte`, with
 * `ZeroDuration` the minimum. SAT = a witnessing instance; UNSAT (check) = the property holds always.
 */

// ── coherence (expect SAT) ────────────────────────────────────────────────────────────────────────
// A non-trivial chain of three distinct, strictly-increasing durations exists.
run unit_duration_chain {
  some disj a, b, c: Duration | dAtOrBefore[a, b] and dAtOrBefore[b, c]
} for 4 expect 1

// A duration strictly longer than zero exists (Zero is not the only duration).
run unit_duration_aboveZero {
  some d: Duration | d != ZeroDuration
} for 4 expect 1

// ── order invariants (check; UNSAT = holds) ─────────────────────────────────────────────────────────
// The order is total: any two durations are comparable.
assert unit_duration_total {
  all a, b: Duration | dAtOrBefore[a, b] or dAtOrBefore[b, a]
}
check unit_duration_total for 6 expect 0

// Antisymmetry: mutually-≤ durations are equal (so `dlte` is a partial order, not a preorder).
assert unit_duration_antisym {
  all a, b: Duration | (dAtOrBefore[a, b] and dAtOrBefore[b, a]) implies a = b
}
check unit_duration_antisym for 6 expect 0

// Transitivity of the ≤ relation.
assert unit_duration_transitive {
  all a, b, c: Duration | (dAtOrBefore[a, b] and dAtOrBefore[b, c]) implies dAtOrBefore[a, c]
}
check unit_duration_transitive for 6 expect 0

// ZeroDuration is the global minimum — no time is the shortest length.
assert unit_duration_zeroIsMin {
  all d: Duration | dAtOrBefore[ZeroDuration, d]
}
check unit_duration_zeroIsMin for 6 expect 0
