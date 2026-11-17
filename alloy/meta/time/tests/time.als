module meta/time/tests/time
// Reflects dafny-domain src/meta/tests/time-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/time/time

/*
 * Sanity suite for meta/time: the order is a genuine total order, earliest/latest pick the
 * endpoints, and interval membership behaves. SAT = a witnessing instance; UNSAT (check) = the
 * property holds in every instance.
 */

// ── coherence (expect SAT) ────────────────────────────────────────────────────────────────
// A non-trivial chain of three distinct, strictly-ordered instants exists.
run unit_time_chain {
  some disj a, b, c: Instant | earlierThan[a, b] and earlierThan[b, c]
} for 4 expect 1

// An interval that strictly contains a third instant.
run unit_time_intervalContains {
  some i: TimeInterval, t: Instant | earlierThan[i.from, t] and earlierThan[t, i.to]
} for 4 expect 1

// earliest/latest of a 3-element set are its min/max.
run unit_time_endpoints {
  some disj a, b, c: Instant |
    earlierThan[a, b] and earlierThan[b, c] and earliest[a+b+c] = a and latest[a+b+c] = c
} for 4 expect 1

// ── invariants (check; UNSAT = holds) ───────────────────────────────────────────────────────

// earliest/latest are unique when present (a consequence of antisymmetry + totality).
assert unit_time_endpointsUnique {
  all ts: set Instant | lone earliest[ts] and lone latest[ts]
}
check unit_time_endpointsUnique for 6 expect 0

// ── Duration / elapsed-time metric (DT-010) ─────────────────────────────────────────────────────
// A consistent metric with a non-zero elapsed span exists.
run unit_time_durationLoads {
  durationAxioms and (some a, b: Instant | durationBetween[a, b] != ZeroDuration)
} for 4 expect 1
