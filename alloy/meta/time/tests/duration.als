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

// ZeroDuration is the global minimum — no time is the shortest length.
assert unit_duration_zeroIsMin {
  all d: Duration | dAtOrBefore[ZeroDuration, d]
}
check unit_duration_zeroIsMin for 6 expect 0
