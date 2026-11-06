#!/usr/bin/env python3
"""Exercise the actual no-checkout advisory step with a local GitHub API double."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[1]


def advisory_script():
    workflow = (ROOT / '.github/workflows/affected-cones.yaml').read_text()
    step = workflow.split('      - name: create or update the one marker-keyed', 1)[1]
    return textwrap.dedent(step.split('        run: |\n', 1)[1])


class AdvisoryTest(unittest.TestCase):
    def run_advisory(self, *, head='head', heavy=False, outcome='exhausted',
                     pages=None, attempt=1, comment=True, fail=''):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            fixtures = {
                'pr': {'head': {'sha': head}, 'labels': [{'name': 'heavy-cone'}] if heavy else []},
                'pages': pages if pages is not None else [{'workflow_runs': [{'id': 100}]}],
                'run': {'run_attempt': attempt},
                'comments': [{'id': 42, 'user': {'login': 'github-actions[bot]'},
                              'body': '<!-- affected-cones-advisory --> old'}] if comment else [],
            }
            (work / 'fixtures.json').write_text(json.dumps(fixtures))
            gh = work / 'gh'
            gh.write_text(textwrap.dedent('''\
                #!/usr/bin/env python3
                import json, os, pathlib, subprocess, sys
                args = sys.argv[1:]
                root = pathlib.Path(__file__).parent
                fixtures = json.loads((root / 'fixtures.json').read_text())
                with (root / 'calls.jsonl').open('a') as log:
                    log.write(json.dumps(args) + '\\n')
                if '-X' in args:
                    with (root / 'writes.jsonl').open('a') as log:
                        log.write(json.dumps(args) + '\\n')
                    sys.exit(0)
                endpoint = args[1]
                if '/actions/workflows/' in endpoint:
                    expected = ('repos/example/model/actions/workflows/affected-cones.yaml/runs'
                                '?head_sha=head&event=pull_request&per_page=100')
                    if endpoint != expected or '--paginate' not in args or '--slurp' not in args:
                        sys.exit('run lookup must cover this workflow, head, event and all pages')
                    key = 'pages'
                elif '/actions/runs/' in endpoint:
                    key = 'run'
                elif '/pulls/' in endpoint:
                    key = 'pr'
                elif endpoint.endswith('/comments'):
                    key = 'comments'
                else:
                    sys.exit('unexpected API call: ' + endpoint)
                if os.environ['FAIL_API'] == key:
                    sys.exit('simulated API failure')
                value = fixtures[key]
                if '--jq' in args:
                    query = args[args.index('--jq') + 1]
                    result = subprocess.run(['jq', '-r', query], input=json.dumps(value),
                                            text=True, capture_output=True)
                    sys.stdout.write(result.stdout)
                    sys.stderr.write(result.stderr)
                    sys.exit(result.returncode)
                print(json.dumps(value))
                '''))
            gh.chmod(0o755)
            env = dict(os.environ, PATH=f'{work}:{os.environ["PATH"]}',
                       GH_TOKEN='test-token', PR_NUMBER='7', HEAD_SHA='head',
                       GITHUB_REPOSITORY='example/model', GITHUB_RUN_ID='100',
                       GITHUB_RUN_ATTEMPT='1', RUN_URL='https://example.invalid/run/100',
                       OUTCOME=outcome, BUDGET='900s', CONE_BUDGET='15m', FAIL_API=fail)
            trace_dir = os.environ.get('ADVISORY_TRACE_DIR')
            env['PS4'] = '+${LINENO}: '
            command = ['bash', '-e', '-o', 'pipefail'] + (['-x'] if trace_dir else [])
            result = subprocess.run(command + ['-c', advisory_script()],
                                    cwd=work, env=env, capture_output=True, text=True, timeout=10)
            if trace_dir:
                trace = Path(trace_dir)
                trace.mkdir(parents=True, exist_ok=True)
                (trace / f'{work.name}.log').write_text(result.stderr)
            writes_file = work / 'writes.jsonl'
            writes = [json.loads(line) for line in writes_file.read_text().splitlines()] \
                if writes_file.exists() else []
            body = (work / 'advisory.md').read_text() if (work / 'advisory.md').exists() else ''
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return writes, result.stdout, body

    def test_current_run_updates_existing_comment_for_every_outcome(self):
        for outcome in ['label', 'exhausted', 'within-budget', 'verdict-failed', '', 'setup-failed']:
            with self.subTest(outcome=outcome):
                writes, _, body = self.run_advisory(outcome=outcome, heavy=outcome == 'label')
                self.assertEqual(len(writes), 1)
                self.assertIn('PATCH', writes[0])
                self.assertIn('<!-- affected-cones-advisory -->', body)

    def test_only_label_and_exhaustion_create_a_comment(self):
        for outcome in ['label', 'exhausted', 'within-budget', 'verdict-failed', '', 'setup-failed']:
            with self.subTest(outcome=outcome):
                writes, _, _ = self.run_advisory(outcome=outcome, heavy=outcome == 'label', comment=False)
                self.assertEqual(len(writes), int(outcome in ['label', 'exhausted']))
                if writes:
                    self.assertIn('POST', writes[0])

    def test_old_head_does_not_post(self):
        self.assertEqual(self.run_advisory(head='new-head')[0], [])

    def test_newer_same_sha_run_blocks_update_and_creation(self):
        for comment in [True, False]:
            with self.subTest(comment=comment):
                writes, log, _ = self.run_advisory(
                    pages=[{'workflow_runs': [{'id': 101}, {'id': 100}]}], comment=comment)
                self.assertEqual(writes, [], 'a stale same-SHA run overwrote the advisory')
                self.assertIn('stale event; nothing posted', log)

    def test_latest_run_is_selected_across_pages_without_assuming_order(self):
        writes, _, _ = self.run_advisory(pages=[{'workflow_runs': [{'id': 99}]},
                                                {'workflow_runs': [{'id': 101}, {'id': 100}]}])
        self.assertEqual(writes, [])

    def test_unknown_latest_run_does_not_post(self):
        self.assertEqual(self.run_advisory(pages=[{'workflow_runs': []}])[0], [])

    def test_older_attempt_of_same_run_does_not_post(self):
        self.assertEqual(self.run_advisory(attempt=2)[0], [])

    def test_removed_heavy_label_blocks_label_advisory(self):
        self.assertEqual(self.run_advisory(outcome='label', heavy=False)[0], [])

    def test_added_heavy_label_blocks_every_nonlabel_outcome(self):
        for outcome in ['exhausted', 'within-budget', 'verdict-failed', '', 'setup-failed']:
            with self.subTest(outcome=outcome):
                self.assertEqual(self.run_advisory(outcome=outcome, heavy=True)[0], [])

    def test_api_failures_do_not_post(self):
        for fail in ['pr', 'pages', 'run', 'comments']:
            with self.subTest(fail=fail):
                self.assertEqual(self.run_advisory(fail=fail)[0], [])

    def test_unknown_outcome_does_not_post(self):
        self.assertEqual(self.run_advisory(outcome='unexpected')[0], [])


if __name__ == '__main__':
    unittest.main()
