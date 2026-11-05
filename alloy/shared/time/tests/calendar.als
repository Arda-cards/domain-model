module shared/time/tests/calendar
// Reflects dafny-domain src/shared/time/tests/calendar-tests.dfy (the reference model since MP's ruling of 2026-11-04; this root's kept commands are its extensions, alloy/EXTENSIONS.md)

open shared/time/calendar

/*
 * Period-boundary suite (moved with the calendar from meta/time — DT-001.12 earmark fulfilled).
 * All commands assume the `calendarAxioms` PREMISE.
 */

// A real-world-bound spec loads: a CalendarSpec dividing the timeline lawfully.
run unit_time_calendarSpecLoads {
  calendarAxioms and (some cs: CalendarSpec | some cs.closes)
} for 4 expect 1

// ── period boundaries (PeriodSpec / endOfPeriod) — under the calendarAxioms premise ─────────────
// SAT: two distinct instants in the SAME period (a non-degenerate period).
run unit_time_samePeriod {
  calendarAxioms and (some ps: PeriodSpec, disj a, b: Instant | earlierThan[a, b] and samePeriod[ps, a, b])
} for 4 expect 1

// SAT: two instants in DIFFERENT periods (boundaries actually divide the timeline).
run unit_time_differentPeriods {
  calendarAxioms and (some ps: PeriodSpec, disj a, b: Instant | not samePeriod[ps, a, b])
} for 4 expect 1

// check: the close is always at-or-after the instant.
assert unit_time_closeAtOrAfter {
  calendarAxioms implies all ps: PeriodSpec, t: Instant | atOrBefore[t, endOfPeriod[ps, t]]
}
check unit_time_closeAtOrAfter for 4 expect 0

// check: idempotent — the close of a close is itself.
assert unit_time_closeIdempotent {
  calendarAxioms implies all ps: PeriodSpec, t: Instant | endOfPeriod[ps, endOfPeriod[ps, t]] = endOfPeriod[ps, t]
}
check unit_time_closeIdempotent for 4 expect 0

// check: samePeriod is an equivalence relation.
assert unit_time_samePeriodEquiv {
  calendarAxioms implies all ps: PeriodSpec, a, b, c: Instant |
    samePeriod[ps, a, a]
    and (samePeriod[ps, a, b] implies samePeriod[ps, b, a])
    and ((samePeriod[ps, a, b] and samePeriod[ps, b, c]) implies samePeriod[ps, a, c])
}
check unit_time_samePeriodEquiv for 4 expect 0

// check: an instant shares its period with its own close (a consequence of idempotence).
assert unit_time_inOwnPeriod {
  calendarAxioms implies all ps: PeriodSpec, t: Instant | samePeriod[ps, t, endOfPeriod[ps, t]]
}
check unit_time_inOwnPeriod for 4 expect 0

