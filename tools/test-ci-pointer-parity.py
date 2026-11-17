#!/usr/bin/env python3
"""Check the workflow that starts dafny-domain's pointer parity check for this repository's commits.

The check lives in dafny-domain; `.github/workflows/pointer-parity-trigger.yaml` starts it and waits. What must hold
for the check to protect a pull request here: it is started for every pull request and for main, for the commit under
review, it is waited for, and a run that could not start is a failure and never a pass.

Two kinds of test: the workflow's text (triggers, conditions, permissions), and the step's script itself, executed the
way the runner executes it, with a fake `gh` first on the PATH.
"""

import os
from pathlib import Path
import re
import subprocess
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / '.github/workflows/pointer-parity-trigger.yaml'


def text():
    return WORKFLOW.read_text()


def block(header, indent=''):
    """The lines under a `header:` line at the given indent, up to the next line at that indent or less."""
    lines = text().splitlines()
    start = next(i for i, line in enumerate(lines) if line.rstrip() == f'{indent}{header}:') + 1
    end = start
    while end < len(lines) and (not lines[end].strip() or lines[end].startswith(indent + ' ')):
        end += 1
    return [line for line in lines[start:end] if line.strip() and not line.strip().startswith('#')]


def step_script():
    """The dispatch step's inline script, dedented: what the runner executes."""
    lines = text().splitlines()
    start = next(i for i, line in enumerate(lines) if "- name: Start dafny-domain's pointer parity check" in line)
    start = next(i for i in range(start, len(lines)) if lines[i].strip() == 'run: |') + 1
    end = start
    while end < len(lines) and (not lines[end].strip() or lines[end].startswith(' ' * 10)):
        end += 1
    script = textwrap.dedent('\n'.join(lines[start:end]))
    assert 'gh workflow run' in script and 'gh run watch' in script, 'the step script was not found in the workflow'
    return script


# A stand-in for `gh`: it records each call, answers `workflow run` with the output and status the test sets, and
# `run watch` with the status the test sets. Any other call is a mistake of the script: status 64.
FAKE_GH = '''#!/bin/sh
echo "$*" >> "$GH_CALLS"
case "$1 $2" in
  "workflow run") [ -z "$GH_DISPATCH_OUT" ] || echo "$GH_DISPATCH_OUT"; exit "$GH_DISPATCH_RC" ;;
  "run watch") exit "$GH_WATCH_RC" ;;
esac
exit 64
'''
RUN_URL = 'https://github.com/Arda-cards/dafny-domain/actions/runs/4242'
DISPATCH = 'workflow run pointer-parity.yaml --repo Arda-cards/dafny-domain --ref main -f domain_model_ref=abc123'
WATCH = 'run watch 4242 --repo Arda-cards/dafny-domain --exit-status'


class DispatchAndWait(unittest.TestCase):
    """The step's script, run as the runner runs a `run:` block with no `shell:` (`bash -e`), against the fake `gh`."""

    def run_step(self, *, token='a-token', dispatch_out=RUN_URL, dispatch_rc=0, watch_rc=0):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            gh = work / 'gh'
            gh.write_text(FAKE_GH)
            gh.chmod(0o755)
            calls = work / 'calls'
            env = dict(os.environ, PATH=f'{work}:{os.environ["PATH"]}', GH_CALLS=str(calls), GITHUB_TOKEN=token,
                       HEAD_SHA='abc123', GH_DISPATCH_OUT=dispatch_out, GH_DISPATCH_RC=str(dispatch_rc),
                       GH_WATCH_RC=str(watch_rc))
            result = subprocess.run(['bash', '-e', '-c', step_script()], cwd=work, env=env, capture_output=True,
                                    text=True, timeout=10)
            return result.returncode, result.stdout + result.stderr, \
                calls.read_text().splitlines() if calls.exists() else []

    def test_it_dispatches_for_the_commit_and_watches_the_run_it_started(self):
        status, log, calls = self.run_step()
        self.assertEqual(status, 0, log)
        self.assertEqual(calls, [DISPATCH, WATCH])

    def test_the_run_id_is_the_last_segment_of_the_last_line(self):
        # `gh` may say more before the run's address; the id is what follows the last slash
        status, log, calls = self.run_step(dispatch_out='created a workflow_dispatch event\n' + RUN_URL)
        self.assertEqual(status, 0, log)
        self.assertEqual(calls, [DISPATCH, WATCH])

    def test_an_empty_dispatch_output_fails_and_watches_nothing(self):
        status, log, calls = self.run_step(dispatch_out='')
        self.assertEqual(status, 1, log)
        self.assertIn('::error::no run id', log)
        self.assertEqual(calls, [DISPATCH])

    def test_an_output_with_no_slash_fails_and_watches_nothing(self):
        status, log, calls = self.run_step(dispatch_out='done')
        self.assertEqual(status, 1, log)
        self.assertIn('::error::no run id', log)
        self.assertEqual(calls, [DISPATCH])

    def test_a_failed_dispatch_fails_and_watches_nothing(self):
        # the dispatch is refused (no permission, no such workflow): whatever it printed, nothing is watched
        for out in ['', RUN_URL]:
            with self.subTest(out=out):
                status, log, calls = self.run_step(dispatch_out=out, dispatch_rc=1)
                self.assertNotEqual(status, 0, log)
                self.assertEqual(calls, [DISPATCH])

    def test_a_failing_remote_run_fails_the_job(self):
        status, log, calls = self.run_step(watch_rc=1)
        self.assertEqual(status, 1, log)
        self.assertEqual(calls, [DISPATCH, WATCH])

    def test_no_secret_fails_before_any_call(self):
        status, log, calls = self.run_step(token='')
        self.assertEqual(status, 1, log)
        self.assertIn('::error::the secret ARDA_API_TEST_WORKFLOW_DISPATCH is not set', log)
        self.assertEqual(calls, [])


class PointerParityTrigger(unittest.TestCase):
    def test_runs_on_every_pull_request_and_on_main(self):
        on = [line.strip() for line in block('on')]
        self.assertEqual(on, ['pull_request:', 'push:', 'branches: [main]'])

    def test_the_only_condition_is_the_fork_guard(self):
        job = block('dispatch', '  ')
        conditions = [line.strip() for line in job if re.match(r'\s*(- )?(if|needs|continue-on-error):', line)]
        self.assertEqual(conditions, ["if: github.event_name == 'push' || github.event.pull_request.head.repo.full_name == github.repository"])

    def test_it_starts_the_check_for_the_commit_under_review(self):
        job = '\n'.join(block('dispatch', '  '))
        self.assertIn('HEAD_SHA: ${{ github.event.pull_request.head.sha || github.sha }}', job)
        # the token is the organization's existing dispatch key, whose applicability the project owner widened (card QA814)
        self.assertIn('GITHUB_TOKEN: ${{ secrets.ARDA_API_TEST_WORKFLOW_DISPATCH }}', job)
        self.assertIn('gh workflow run pointer-parity.yaml', job)
        self.assertIn('--repo Arda-cards/dafny-domain --ref main', job)
        self.assertIn('-f domain_model_ref="$HEAD_SHA"', job)

    def test_it_waits_and_takes_the_runs_result(self):
        job = '\n'.join(block('dispatch', '  '))
        self.assertIn('gh run watch "$id" --repo Arda-cards/dafny-domain --exit-status', job)

    def test_a_run_that_cannot_start_fails(self):
        job = '\n'.join(block('dispatch', '  '))
        # no secret, or no run id back from the dispatch: both exit 1, and nothing in the step swallows a failure
        self.assertRegex(job, r'\[ -n "\$\{GITHUB_TOKEN:-\}" \] \|\| \{ echo "::error::[^"]*"; exit 1; \}')
        self.assertRegex(job, r'\[ -n "\$id" \] && \[ "\$id" != "\$url" \] \|\| \{ echo "::error::[^"]*"; exit 1; \}')
        self.assertNotIn('|| true', job)
        self.assertIn('set -u', job)

    def test_the_workflow_token_cannot_write(self):
        self.assertEqual([line.strip() for line in block('permissions')], ['contents: read'])


if __name__ == '__main__':
    unittest.main()
