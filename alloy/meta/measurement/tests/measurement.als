module meta/measurement/tests/measurement
// Reflects dafny-domain src/meta/tests/measurement-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

/*
 * Structure + value-agnostic-selector tests for the generic meta/measurement[V] framework.
 * V is instantiated with a root-LOCAL opaque stand-in (`Reading` — an unconstrained value sig) so
 * these tests exercise only what's value-type-independent: the Signal/Measurement/Metric/Report
 * shape and the LAST/FIRST/COUNT/valueAt selectors. Value-dependent stats (MIN/MAX/SUM) are tested
 * in the V=Quantity instantiation (shared/measurement/tests/quantity — meta never opens shared,
 * DT-001.12, so the stand-in must not come from shared/values).
 */

open meta/time/time              // Instant, TimeInterval, earlierThan, within, atOrBefore
open meta/measurement/measurement[Reading]

/** Reading — a root-local opaque value stand-in for the V parameter. */
sig Reading {}

// ── coherence (expect SAT) ────────────────────────────────────────────────────────────────
// Two ordered samples of one signal inside a period: FIRST/LAST pick the endpoints' values.
run unit_meas_firstLast {
  some s: Signal, p: TimeInterval, disj m1, m2: Measurement |
    m1.of = s and m2.of = s
    and earlierThan[m1.at, m2.at] and within[m1.at, p] and within[m2.at, p]
    and firstValueIn[s, p] = m1.value
    and lastValueIn[s, p] = m2.value
} for 6 expect 1

// LOCF: the value carried at `t` is the last sample at-or-before `t`.
run unit_meas_locf {
  some s: Signal, disj m1, m2: Measurement, t: Instant |
    m1.of = s and m2.of = s and earlierThan[m1.at, m2.at]
    and atOrBefore[m2.at, t] and valueAt[s, t] = m2.value
} for 6 expect 1

// A LEVEL signal carrying a sample.
run unit_meas_levelSignal {
  some s: Signal | s.kind = LEVEL and some m: Measurement | m.of = s
} for 6 expect 1

// A Metric and a Report over a signal (structure is inhabited).
run unit_meas_metricReport {
  some mt: Metric | mt.stat = LAST
  some r: Report | no r.cadence            // an on-demand report
} for 6 expect 1

// ── invariants (check; UNSAT = holds) ───────────────────────────────────────────────────────
// One sample per (signal, instant).
assert unit_meas_oneSamplePerInstant {
  all disj m1, m2: Measurement | (m1.of = m2.of and m1.at = m2.at) implies m1 = m2
}
check unit_meas_oneSamplePerInstant for 6 expect 0

// first/last of a period are unique (lone).
assert unit_meas_endpointsLone {
  all s: Signal, p: TimeInterval | lone latestIn[s, p] and lone firstIn[s, p]
}
check unit_meas_endpointsLone for 6 expect 0

// LAST is always one of the period's actually-sampled values (when the period is non-empty).
assert unit_meas_lastIsSampled {
  all s: Signal, p: TimeInterval |
    some measurementsIn[s, p] implies lastValueIn[s, p] in measurementsIn[s, p].value
}
check unit_meas_lastIsSampled for 6 expect 0

// COUNT is exactly the number of in-period samples.
assert unit_meas_countMatches {
  all s: Signal, p: TimeInterval | countIn[s, p] = #measurementsIn[s, p]
}
check unit_meas_countMatches for 6 expect 0
