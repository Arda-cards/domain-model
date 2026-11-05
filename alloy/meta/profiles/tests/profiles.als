module meta/profiles/tests/profiles
// Reflects dafny-domain src/meta/tests/profiles-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open meta/profiles/timed_log   // transitively: domain_log, baseline, profile

/*
 * Non-vacuity witnesses per profile (the premise-as-fact discipline: if a profile's premises were
 * jointly unsatisfiable, every check in its cone would pass vacuously — these witnesses forbid that).
 */

// The full profile stack loads: a universe satisfying ALL bundled facts exists.
run unit_prof_stackLoads {} for 3 but 3 Scalar expect 1

// The markers are present and distinct — adoption is visible in the instance.
run unit_prof_markersVisible {
  some P_Baseline and some P_DomainLog and some P_TimedLog and #Profile = 3
} for 3 but 3 Scalar expect 1

// The premises are genuinely in force (not just declared): the group law holds categorically.
assert unit_prof_premisesInForce { all a: Scalar | a.splus[SZero] = a }
check unit_prof_premisesInForce for 3 but 3 Scalar expect 0
