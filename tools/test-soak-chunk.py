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
