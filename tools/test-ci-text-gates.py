#!/usr/bin/env python3
"""Check that the text gates run on every pull request, in the actual fast-checks workflow.

The three gates need no solver: `check-layering` (the layer law), `check-open-params` (model-gate rule 10) and
`check-lifecycle` (the shape partition). A gate that only the local push discipline runs can be red at review:
the Alloy cut reached review with `check-open-params` red.
"""

from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / '.github/workflows/fast-checks.yaml'


def trigger_block():
    """The lines of the top-level `on:` block."""
    lines = WORKFLOW.read_text().splitlines()
    start = next(i for i, line in enumerate(lines) if line.rstrip() == 'on:') + 1
    end = start
    while end < len(lines) and (not lines[end].strip() or lines[end].startswith(' ')):
        end += 1
    return [line for line in lines[start:end] if line.strip()]


def jobs():
    """Job name -> the lines of its block."""
    lines = WORKFLOW.read_text().splitlines()
    start = next(i for i, line in enumerate(lines) if line.rstrip() == 'jobs:') + 1
    found, name = {}, None
    for line in lines[start:]:
        header = re.fullmatch(r'  ([A-Za-z0-9_-]+):\s*(#.*)?', line)
        if header:
            name = header.group(1)
            found[name] = []
        elif name is not None:
            found[name].append(line)
    return found


def jobs_running(command):
    """The jobs with a step whose whole `run:` is the command."""
    return {name: block for name, block in jobs().items()
            if any(line.strip() == f'run: {command}' for line in block)}


def suppressors(block):
    """The lines of a job's block that can switch the job off or hide its failure."""
    return [line.strip() for line in block if re.match(r'\s*(- )?if:', line)]


def workflow_permissions():
    """The lines of the top-level `permissions:` block (empty when the workflow has none)."""
    lines = WORKFLOW.read_text().splitlines()
    starts = [i for i, line in enumerate(lines) if line.rstrip() == 'permissions:']
    if not starts:
        return []
    start = starts[0] + 1
    end = start
    while end < len(lines) and lines[end].startswith(' '):
        end += 1
    return [line.strip() for line in lines[start:end] if line.strip()]


class TextGatesTest(unittest.TestCase):
    def assert_gate_runs_unconditionally(self, command):
        running = jobs_running(command)
        self.assertEqual(len(running), 1, f'expected exactly one job running `{command}`, found {sorted(running)}')
        (name, block), = running.items()
        self.assertEqual(suppressors(block), [],
                         f'job {name} must not be conditional, depend on another job or suppress its failure')
        self.assertIn('persist-credentials: false', [line.strip() for line in block],
                      f'job {name} runs pull-request code: its checkout must not persist the token')

    def test_layering_gate_runs(self):
        self.assert_gate_runs_unconditionally('make check-layering')

    def test_open_params_gate_runs(self):
        self.assert_gate_runs_unconditionally('make check-open-params')

    def test_lifecycle_gate_runs(self):
        self.assert_gate_runs_unconditionally('make check-lifecycle')

    def test_guard_flags_what_switches_a_job_off_or_hides_its_failure(self):
        # Review of the pull request: `needs:` skips the job when its dependency fails, and `continue-on-error: true`
        # (on the job or on a step) reports a failing gate as passed. Both defeat a gate as `if:` does.
        self.assertEqual(suppressors(['    if: github.event.label.name == \'x\'']), ["if: github.event.label.name == 'x'"])
        self.assertEqual(suppressors(['      - if: always()']), ['- if: always()'])
        self.assertEqual(suppressors(['    needs: ci-tests']), ['needs: ci-tests'])
        self.assertEqual(suppressors(['    needs: [ci-tests, shellcheck]']), ['needs: [ci-tests, shellcheck]'])
        self.assertEqual(suppressors(['    continue-on-error: true']), ['continue-on-error: true'])
        self.assertEqual(suppressors(['        continue-on-error: true']), ['continue-on-error: true'])
        self.assertEqual(suppressors(['    runs-on: ubuntu-latest', '      - uses: actions/checkout@v4']), [])

    def test_workflow_token_is_read_only(self):
        # The jobs run the pull request's own Makefile and Python: the token they could reach must not write.
        self.assertEqual(workflow_permissions(), ['contents: read'])

    def test_workflow_runs_on_every_pull_request(self):
        # No path, branch or type filter: the gates read the whole tree, and a filter would skip them.
        self.assertEqual([line.strip() for line in trigger_block()], ['pull_request:'])


if __name__ == '__main__':
    unittest.main()
