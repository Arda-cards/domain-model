module meta/occurrence/tests/timed
// Reflects dafny-domain src/meta/tests/occurrence-timed-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/occurrence/timed

/*
 * The two-clock BRIDGE, as the opt-in `Timed` extension (DT-011): the clocks are INDEPENDENT unless
 * the `clocksAligned` premise is assumed — which is exactly what lets the model represent backdating.
 * The test kind opts in with one fact, the pattern domains follow.
 */

/** TOcc — a concrete occurrence kind, opted into the domain-time stamp. */
sig TOcc extends Occurrence {}
fact TOccIsTimed { TOcc in Timed }

/** UOcc — a kind NOT opted in (for the mixed-log witness; membership left free). */
sig UOcc extends Occurrence {}

// A forward-aligned chain exists: two occurrences, causally ordered, with in-order domain stamps.
run unit_timed_loads {
  clocksAligned and (some disj a, b: TOcc | occPrecedes[a, b] and earlierThan[a.at, b.at])
} for 4 expect 1

// BACKDATING is representable: WITHOUT `clocksAligned`, an occurrence causally BEFORE another may
// carry a LATER domain stamp. SAT = the two-axis model expresses what a single fused axis cannot.
run unit_timed_backdating {
  some disj a, b: TOcc | occPrecedes[a, b] and not atOrBefore[a.at, b.at]
} for 4 expect 1

// `clocksAligned` does its job: under the premise, no backdating is possible.
assert unit_timed_alignedForbidsBackdating {
  clocksAligned implies (no disj a, b: TOcc | occPrecedes[a, b] and not atOrBefore[a.at, b.at])
}
check unit_timed_alignedForbidsBackdating for 5 expect 0

// The stamp is per-atom opt-in: an un-timed occurrence kind carries no `at` (membership is the fact).
run unit_timed_mixedLog {
  some o: Occurrence | o not in Timed
} for 4 expect 1
