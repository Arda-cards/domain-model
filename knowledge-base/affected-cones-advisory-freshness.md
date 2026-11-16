# An advisory must validate the run and live label state before posting

The `affected-cones` workflow runs for label changes as well as new commits. Its
workflow concurrency group cancels older executions, but the advisory uses
`always()` so that a job-limit cancellation can still be reported. A cancelled run
or a manually re-run old label event can therefore reach the comment writer with
the same head SHA and an obsolete label snapshot.

The advisory job reads the newest `affected-cones.yaml` run associated with this
PR number and head SHA across all API pages, compares its id to `GITHUB_RUN_ID`, and verifies
`GITHUB_RUN_ATTEMPT`. After comment discovery, it reads the live PR head and
`heavy-cone` label. Only a current run whose outcome agrees with that label may
create or update the marker-keyed bot comment. An obsolete event logs
`stale event; nothing posted`; failed API reads also prevent posting.

The workflow-specific runs endpoint matters: another workflow on the same SHA
must not supersede this one. Run ids order newly created events; an old run's
manual re-run keeps the old id and increments its attempt. A newer event with the
same labels still supersedes an older event. The API checks precede the comment
write, but GitHub offers no atomic compare-and-swap across PR state and comments;
a new event arriving after the final read is handled by that event's own run.

A branch can back two PRs against different bases. Filter the runs by their
`pull_requests` associations before selecting the greatest id so a newer run on
the other PR does not suppress this PR's advisory. An unknown association does
not authorize a write.

Keep the advisory job free of checkouts and PR-controlled code. Its token has
`actions: read` and `pull-requests: write`; the solver job stays read-only.
`python3 tools/test-ci-advisory.py -v` exercises the actual inline advisory with
mocked API responses, including stale runs, label changes, failed reads, and
current-run updates. These tests also run in `fast-checks`.
