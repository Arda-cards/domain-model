#!/usr/bin/env python3
"""Check the workflow that starts dafny-domain's pointer parity check for this repository's commits.

The check lives in dafny-domain; `.github/workflows/pointer-parity-trigger.yaml` starts it and waits. What must hold
for the check to protect a pull request here: it is started for every pull request and for main, for the commit under
review, it is waited for, and a run that could not start is a failure and never a pass.
"""

from pathlib import Path
import re
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
