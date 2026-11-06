# Solver choice: glucose by default, SAT4J as the portable fallback

The Makefile runs every `alloy exec` with `ALLOY_FLAGS ?= -s glucose` (MP ruling
2026-07-17, DT-015 completion session). Glucose is a JNI-native solver bundled in the
pinned Alloy jar; it loads on darwin/arm64 and is **dramatically** faster than the
pure-Java SAT4J default on this model — the difference is minutes vs. tens of minutes on
the full gate.

## The rule

- Leave the default alone: `make check-alloy` and friends already pass `-s glucose`.
- On a machine where the native library fails to load (a `UnsatisfiedLinkError` or a
  solver-init failure in the log), revert to SAT4J with `ALLOY_FLAGS=''` — as an
  environment variable or a make argument (`make check-alloy ALLOY_FLAGS=''`); the `?=`
  assignment yields to either.
- When running the jar directly (outside make), pass `-s glucose` yourself or accept the
  slow default.

## CI heap

The `affected-cones` solver job and all `full-regression` solver jobs (including the
cookbook examples) set `JAVA_TOOL_OPTIONS=-Xmx5g`. Java reads this for every solver
process, including commands launched by Make. The limit leaves room for JNI solver
allocations and runner processes on a 7 GB hosted runner. It is a heap ceiling, not
a limit on the JVM's total resident memory; native solver memory is additional.

## Why switching is always safe

Both solvers are sound and complete: SAT/UNSAT answers and `expect` verdicts are
identical under either. Only speed differs. Never treat a solver swap as a possible
cause of a changed verdict — if a verdict changed, the model changed.
