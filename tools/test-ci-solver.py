#!/usr/bin/env python3
"""Check solver selection and diagnostics in the actual workflow shell steps."""

import os
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[1]


def solver_script(workflow):
    lines = (ROOT / '.github/workflows' / workflow).read_text().splitlines()
    start = next(i for i, line in enumerate(lines) if '- name: pick solver' in line)
    start = next(i for i in range(start, len(lines)) if lines[i].strip() == 'run: |') + 1
    end = start
    while end < len(lines) and (not lines[end].strip() or lines[end].startswith('          ')):
        end += 1
    return textwrap.dedent('\n'.join(lines[start:end]))


class SolverTest(unittest.TestCase):
    def run_solver(self, workflow, *, succeeds, choice='auto'):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            java = work / 'java'
            java.write_text('#!/bin/sh\necho "probe diagnostic witness" >&2\n'
                            'echo "$*" >> "$JAVA_CALLS"\nexit "$JAVA_RESULT"\n')
            java.chmod(0o755)
            env_file = work / 'env'
            calls = work / 'calls'
            env = dict(os.environ, PATH=f'{work}:{os.environ["PATH"]}',
                       GITHUB_ENV=str(env_file), JAVA_CALLS=str(calls),
                       JAVA_RESULT='0' if succeeds else '1')
            script = solver_script(workflow).replace('${{ inputs.solver }}', choice)
            # Keep the baseline workflow's fixed /tmp names inside this test's sandbox.
            script = script.replace('/tmp/', f'{work}/')
            result = subprocess.run(['bash', '-e', '-o', 'pipefail', '-c', script],
                                    cwd=work, env=env, capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return result.stdout + result.stderr, env_file.read_text(), \
                calls.read_text() if calls.exists() else ''

    def test_success_selects_glucose(self):
        for workflow in ['affected-cones.yaml', 'full-regression.yaml']:
            with self.subTest(workflow=workflow):
                log, env, calls = self.run_solver(workflow, succeeds=True)
                self.assertIn('ALLOY_FLAGS=-s glucose\n', env)
                self.assertIn('solver: glucose (native loaded)', log)
                self.assertIn('exec -s glucose -c probe', calls)

    def test_failure_shows_diagnostics_and_selects_sat4j(self):
        for workflow in ['affected-cones.yaml', 'full-regression.yaml']:
            with self.subTest(workflow=workflow):
                log, env, _ = self.run_solver(workflow, succeeds=False)
                self.assertEqual(env, 'ALLOY_FLAGS=\n')
                self.assertIn('solver: SAT4J', log)
                self.assertIn('probe diagnostic witness', log)
                self.assertIn('::warning::', log)

    def test_explicit_solver_choice_is_preserved(self):
        for choice, flags in [('glucose', '-s glucose'), ('sat4j', '')]:
            with self.subTest(choice=choice):
                _, env, calls = self.run_solver('full-regression.yaml', succeeds=False, choice=choice)
                self.assertEqual(env, f'ALLOY_FLAGS={flags}\n')
                self.assertEqual(calls, '')


if __name__ == '__main__':
    unittest.main()
