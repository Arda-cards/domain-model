#!/usr/bin/env python3
"""Check the chunked soak runner (tools/soak-chunk.sh) on a small tree, with a stand-in for java.

Two defects it must not have:
- a labelled command (`e7_step_w: check e7_step for ...`) is a command; the tool selects it by its label;
- two roots may state commands of the same name (the soak rungs all have `e7_base`); each is its own command,
  so results are kept per root and command, and running one never skips the other.
"""

import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / 'tools/soak-chunk.sh'

ROOT_A = '''module soak/sliced/a
run e7_base {} for 3 expect 1
e7_step_w: check e7_step for 4 expect 0
  check indented_one for 3 expect 0
// run commented_out {} for 3 expect 1
'''
ROOT_B = '''module soak/sliced/b
check e7_base for 3 expect 0
run only_b {} for 3 expect 1
'''
ROOT_L = '''module soak/lemmas/l
check lemma_one for 3 expect 0
'''
EXPECTED = {('alloy/soak/lemmas/l.als', 'lemma_one'),
            ('alloy/soak/sliced/a.als', 'e7_base'),
            ('alloy/soak/sliced/a.als', 'e7_step_w'),
            ('alloy/soak/sliced/a.als', 'indented_one'),
            ('alloy/soak/sliced/b.als', 'e7_base'),
            ('alloy/soak/sliced/b.als', 'only_b')}


def stated_commands(tree):
    """(root, command) for every command stated under <tree>/alloy/soak: its label if it has one, else its name."""
    found = set()
    for path in sorted((tree / 'alloy/soak').rglob('*.als')):
        for line in path.read_text().splitlines():
            m = re.match(r'\s*(?:([A-Za-z_][A-Za-z_0-9]*)\s*:\s*)?(run|check)\s+([A-Za-z_][A-Za-z_0-9]*)', line)
            if m:
                found.add((str(path.relative_to(tree)), m.group(1) or m.group(3)))
    return found


class SoakChunkTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.work = Path(self.tmp.name)
        (self.work / 'tools').mkdir()
        shutil.copy(RUNNER, self.work / 'tools/soak-chunk.sh')
        (self.work / 'alloy/soak/sliced').mkdir(parents=True)
        (self.work / 'alloy/soak/lemmas').mkdir(parents=True)
        (self.work / 'alloy/soak/sliced/a.als').write_text(ROOT_A)
        (self.work / 'alloy/soak/sliced/b.als').write_text(ROOT_B)
        (self.work / 'alloy/soak/lemmas/l.als').write_text(ROOT_L)
        # The stand-in for java: records the command and the root it was asked for, and reports a verdict.
        java = self.work / 'bin/java'
        java.parent.mkdir()
        java.write_text('#!/bin/sh\n'
                        'c=""; f=""\n'
                        'while [ $# -gt 0 ]; do case "$1" in -c) c="$2"; shift;; -f) f="$2"; shift;; esac; shift; done\n'
                        'echo "$f $c" >> "$JAVA_CALLS"\n'
                        'echo "[main] INFO alloy -    UNSAT!"\n')
        java.chmod(0o755)
        self.calls = self.work / 'java-calls'
        self.env = dict(os.environ, PATH=f'{self.work}/bin:{os.environ["PATH"]}', JAVA_CALLS=str(self.calls),
                        FORCE='1', POLL='1', UNKNOWN_FLOOR='0', CORPUS=str(self.work / 'corpus'))

    def tearDown(self):
        self.tmp.cleanup()

    def runner(self, *args, tree=None):
        return subprocess.run(['bash', 'tools/soak-chunk.sh', *args], cwd=tree or self.work, env=self.env,
                              capture_output=True, text=True, timeout=120)

    def planned(self, batch):
        rows = [line.split('\t') for line in (batch / 'plan.tsv').read_text().splitlines()]
        return [(row[1], row[2]) for row in rows]

    def test_plan_lists_every_stated_command_once(self):
        # A labelled command is planned under its label; a commented-out one is not planned.
        result = self.runner('plan', 'batch')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        planned = self.planned(self.work / 'batch')
        self.assertEqual(sorted(planned), sorted(EXPECTED))

    def test_chunk_runs_same_named_commands_of_two_roots(self):
        self.assertEqual(self.runner('plan', 'batch').returncode, 0)
        result = self.runner('chunk', 'batch', '60', '1', '1')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        ran = {tuple(line.split()) for line in self.calls.read_text().splitlines()}
        self.assertEqual(ran, EXPECTED)

    def test_status_reports_every_command_done(self):
        self.assertEqual(self.runner('plan', 'batch').returncode, 0)
        self.assertEqual(self.runner('chunk', 'batch', '60', '1', '1').returncode, 0)
        result = self.runner('status', 'batch')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        ledger = [line.split('\t') for line in (self.work / 'batch/ledger.tsv').read_text().splitlines()[1:]]
        self.assertEqual(sorted((row[1], row[2], row[5]) for row in ledger),
                         sorted((root, command, 'done') for root, command in EXPECTED))

    def test_resume_of_a_batch_from_before_the_key_keeps_its_results(self):
        # Review of the pull request. A batch made before results were kept per root and command has its artifacts under
        # the bare command name, and its meta records the root. Resuming it must read that result as done for THAT root,
        # never run it again, and still run the same-named command of the other root, which the old runner skipped.
        self.assertEqual(self.runner('plan', 'batch').returncode, 0)
        cmd = self.work / 'batch/cmd'
        (cmd / 'e7_base.rc').write_text('0\n')
        (cmd / 'e7_base.log').write_text('[main] INFO alloy -    SAT!\n')
        (cmd / 'e7_base.meta').write_text('start\t100\nscope_hash\tabc\nroot\talloy/soak/sliced/a.als\nend\t160\n')
        result = self.runner('chunk', 'batch', '60', '1', '1')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        ran = {tuple(line.split()) for line in self.calls.read_text().splitlines()}
        self.assertEqual(ran, EXPECTED - {('alloy/soak/sliced/a.als', 'e7_base')})
        ledger = [line.split('\t') for line in (self.work / 'batch/ledger.tsv').read_text().splitlines()[1:]]
        self.assertEqual(sorted((row[1], row[2], row[5]) for row in ledger),
                         sorted((root, command, 'done') for root, command in EXPECTED))
        elapsed = {(row[1], row[2]): row[6] for row in ledger}
        self.assertEqual(elapsed[('alloy/soak/sliced/a.als', 'e7_base')], '60')

    def test_watchdog_caps_a_running_job_of_an_old_batch_by_its_own_root(self):
        # Review of the pull request. A job still running from before the key has its pid under the bare command name.
        # Its cap is its OWN root's estimate times CAP_NUM, not that of a same-named command of another root.
        hash_a = self.runner('conehash', 'alloy/soak/sliced/a.als').stdout.strip()
        hash_b = self.runner('conehash', 'alloy/soak/sliced/b.als').stdout.strip()
        (self.work / 'alloy/soak/estimates.tsv').write_text(f'e7_base\t{hash_a}\t1\ne7_base\t{hash_b}\t1000\n')
        self.assertEqual(self.runner('plan', 'batch').returncode, 0)
        cmd = self.work / 'batch/cmd'
        job = subprocess.Popen(['sh', '-c', 'sleep 60; true'])
        try:
            (cmd / 'e7_base.pid').write_text(f'{job.pid}\n')
            (cmd / 'e7_base.meta').write_text(f'start\t{int(__import__("time").time()) - 10}\nscope_hash\t{hash_a}\n'
                                              'root\talloy/soak/sliced/a.als\n')
            env = dict(self.env, CAP_NUM='3')
            subprocess.run(['bash', 'tools/soak-chunk.sh', 'chunk', 'batch', '4', '1', '1'], cwd=self.work, env=env,
                           capture_output=True, text=True, timeout=120)
            over = cmd / 'e7_base.overbudget'
            self.assertTrue(over.exists(), 'ten seconds into a job capped at 3 s (1 s x 3), the watchdog must record it over budget')
            self.assertIn('cap_s\t3\n', over.read_text())
        finally:
            job.kill()
            job.wait()

    def test_plan_of_the_repository_lists_every_stated_soak_command(self):
        # The real tree: what the runner plans is what the soak roots state, each once.
        with tempfile.TemporaryDirectory() as directory:
            batch = Path(directory) / 'batch'
            result = self.runner('plan', str(batch), tree=ROOT)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            planned = self.planned(batch)
            self.assertEqual(len(planned), len(set(planned)), 'a (root, command) pair is planned twice')
            self.assertEqual(set(planned), stated_commands(ROOT))


if __name__ == '__main__':
    unittest.main()
