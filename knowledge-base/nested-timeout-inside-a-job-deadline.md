# A nested `timeout` must be bounded by the job budget remaining when it starts

**Symptom (domain-model PR #4, Copilot's seventh finding; MP's Q284 ruling, 2026-10-05):** the
affected-cones check ran the cone under `timeout 15m` inside a job with `timeout-minutes: 20`. With
a late cone start (a 330 s setup in the witness), the job deadline arrived first: GitHub ended the
job with "The job has exceeded the maximum execution time of 20m0s", the step was *cancelled*, no
explicit exhaustion error and no `exhausted` outcome were produced, and the dependent advisory job
was skipped because a job-limit kill reports the job as `cancelled` — the same conclusion a
concurrency cancellation gives (run 37380832254, the RED).

**Mechanism:** an inner `timeout` guarantees nothing about the outer deadline. It fires `nominal`
seconds after the cone starts; the job limit fires `JOB_LIMIT_S` seconds after the job starts; the
difference is whatever setup consumed, which the inner timeout does not know. Any reporting that
lives after the inner timeout (the `::error::`, the outcome output, the advisory) is lost when the
outer limit wins.

**Rule (`.github/workflows/affected-cones.yaml`):**

- A first step records the job's clock (`JOB_START`). The cone step applies
  `effective = min(CONE_BUDGET, JOB_LIMIT_S − elapsed − DEADLINE_MARGIN_S)` and logs nominal,
  effective, elapsed setup and the remaining budget; the effective value is exported as a job output
  and named in the error annotation and the advisory.
- `JOB_LIMIT_S` is coupled to the job's `timeout-minutes` by hand; the cone step reads the
  checked-out workflow's `timeout-minutes` and fails the run with `::error::` if `× 60` differs.
- `DEADLINE_MARGIN_S` = 60: the 20 s SIGKILL grace after the cone's SIGTERM (`timeout -k 20s`), the
  2–5 s between the job's own clock and the clock step, the step's wrap-up (outputs, the
  annotation) and slack for the runner's deadline check.
- If less than the margin remains at cone start, fail immediately as a deadline failure (outcome
  `setup-failed`); never start a 1 s timeout that cannot fit.
- Exit status 137 is ambiguous: `timeout`'s SIGKILL after the grace, or an outside kill (OOM,
  infrastructure). It counts as exhaustion only when the cone's elapsed time reached the effective
  budget; earlier, it is a failed verdict with a warning.
- The dependent advisory job runs on `always()` — a job-limit kill reports `cancelled` — and refuses
  to write when the PR's head has moved on (a superseded run), so a concurrency cancellation never
  writes stale state.

**Evidence:** RED run 37380832254 on 693f5a4 (job kill at 20 min, advisory skipped); GREEN run
37383335112 on 904b811 — `791s effective (setup took 349s; job budget remaining 851s of 1200s;
margin 60s)`, exhaustion at 19 min 02 s, advisory refreshed. Setup on the PR's ordinary runs: 14–24 s.
