# Label a model PR `heavy-cone` when its cone reaches the long roots

**Symptom (domain-model PRs #6 and #7, 2026-10-15/16):** both opened without the label, and
`affected-cones` failed on each: the cone ran its whole 900 s budget while still on the first root
(`operations/demand/tests/integration/demand.als`). No root reported a wrong verdict. The cone of a
change to `inventory_pool` or `demand` is 19 roots, and it reaches the receiver unit root, which alone
takes over six hours. The check cannot pass on such a PR without the label, so the red is certain
from the moment the PR opens.

**Rule (MP, 2026-10-16: "for PR's that expect a big impact on verification, you should tag the PR
with `heavy-cone` to avoid the timeouts"):**

- **Before opening a model PR, compute its cone:** `make merge-plan FILES="…"` or `tools/cone.sh`.
  If it reaches a root that cannot finish in 15 minutes (the receiver unit root, `tests/pool_lattice.als`,
  `tests/system.als`; MP's ruling of 2026-08-15 names "anything reaching the receiver unit root"),
  open it with the `heavy-cone` label.
- **What stands behind the label** (COORDINATOR-Q483, ruled A on 2026-10-13): the module-scoped set the
  model-gate policy asks for the change's tier. For a change under one module, that is `make
  check-affected` plus the base obligations (`e7_base`, `e7_prov_base`) of the E7 rungs in the cone.
  The label's own text says "local full gate". Q483 lets it stand on the narrower set provided the PR body
  says so. The roots outside the cone go to the next night window.
- **The PR body cites the run:** each root's verdict counts and time, the end line, and the head SHA.
  While the run is still going, the body says so and what remains. If a root misses its `expect`,
  remove the label and fix the cause on the PR.
- **Running the set in a cloud session** (measured on #7's head, 2026-10-16, on a 4-core machine with a 16 GB
  memory cgroup): one JVM per root, glucose, each root resumable through its own result file.
  - **The rung base commands need `-Xmx5g`.** At `-Xmx2g` the order and receiver rungs died of `OutOfMemoryError`
    while parsing, with no verdict. At `-Xmx5g` all 8 rungs (10 commands) are UNSAT as expected: about a minute each
    for the order rungs, 5 to 7 minutes for the receiver ones.
  - **Run nothing else heavy beside the long lanes.** Two lanes (`-Xmx7g` for the receiver unit root, `-Xmx6g` for
    the rest) fill the cgroup. A Dafny gate started beside them got `tests/pool_lattice.als` killed by the cgroup's
    OOM killer after 3.4 hours, still on its first command (`sys_poolLatticeGlobal`: 896k variables, 2.3M clauses).
  - **A session container is not a night window.** A restart killed the remaining lanes, the receiver unit root at
    10 of 35 commands after 4.9 hours. Roots that run for hours belong in the night window's slots; the cloud
    session can carry the rung base commands and the roots that finish in minutes.

**Measured again on the activation cut (2026-11-05, DAFNY's container, same 4-core / 16 GB shape, head `bb7570a`):**

- **The receiver INTEGRATION root is a long root too.** `int_rcv_latticeCompanion` reaches 3.7M variables and
  11.8M clauses at `-Xmx7g`; the run was killed by the cgroup's OOM killer after 3 h 19 min with no verdict when a
  third lane started beside it. The demand integration root (`operations/demand/tests/integration/demand.als`) was
  still on command 2 of 5 after 2 h 55 min. The heavy set that belongs in a night window is therefore five roots:
  the receiver unit root, the receiver integration root, the demand integration root, `tests/pool_lattice.als`
  and `tests/system.als`.
- **Two lanes, never three.** The 7 GB lane plus a 3 GB lane fill the cgroup; any third JVM gets the biggest lane
  killed, not itself. Guard the lane count in the runner, not by eye.

**Set the label after the push's `check-affected` run exists, never together with the push (domain-model PR #16,
2026-11-20):**

- **Symptom:** the PR carried the label and its local gate was green, and `affected-cones` still failed: "the cone run
  exceeded its budget (900s effective of 15m nominal; setup took 22s of the 1200s job limit)". No root reported a wrong
  verdict.
- **What happened:** the head was pushed at 00:36:18Z and the label was set at 00:36:21Z. GitHub created the label's run
  first (00:36:24Z) and the push's run one second later (00:36:25Z). The workflow keeps one run per branch (`concurrency`
  with `cancel-in-progress`), so the later run, the push's, cancelled the label's. A run decides from its own event
  (`contains(github.event.pull_request.labels.*.name, 'heavy-cone')`), and the push's event was made before the label
  existed. Its step "heavy-cone escape valve" shows as skipped, and it ran the cone to the end of the budget.
- **Rule:** push, wait until the push's `check-affected` run is listed, then set the label. The label's run is then the
  later one: it cancels the push's run and skips the solve. A PR that already carries the label before a push is not
  expected to be affected, because the push's event then lists the label (not measured here).
- **Recovery:** remove the label and set it again. Do not re-run the failed job: a re-run uses the push's event again.
- **How to tell it from a real failure:** the PR shows the label, the failed run's "heavy-cone escape valve" step is
  skipped, and the error is the budget's, with no root named.

**Why not let CI decide:** the check's budget (`knowledge-base/nested-timeout-inside-a-job-deadline.md`)
guarantees the explicit failure, never a verdict. An unlabeled heavy PR spends 15 minutes of runner
time to learn what the cone script already says.
