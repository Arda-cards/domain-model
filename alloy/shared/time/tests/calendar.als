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
