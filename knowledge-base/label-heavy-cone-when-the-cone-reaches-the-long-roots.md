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

**Why not let CI decide:** the check's budget (`knowledge-base/nested-timeout-inside-a-job-deadline.md`)
guarantees the explicit failure, never a verdict. An unlabeled heavy PR spends 15 minutes of runner
time to learn what the cone script already says.
