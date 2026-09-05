#!/usr/bin/env python3
"""adoption-gate.py <alloy-root> — Q5 mitigation (b), DT-029 E5 §3: for every instantiation of meta/subject_log or
meta/intent_log in a NON-test module, report whether the module adopts the pattern's opt-in preds for that alias:
  subject_log[...] as Y  -> no obligation since DT-029 Q8 (archeUniquePerSubject is a module FACT)
  intent_log[...]  as X  -> X/spineAdopted AND X/citationView
Exit 1 if any instantiation lacks an adoption (a red gate, never a silent pass)."""
import re, sys, pathlib
root = pathlib.Path(sys.argv[1]); bad = 0; rows = []  # NOTE: obligation set = EVERY instantiation; DT-029 Q8 decides whether that is the rule (D-3 made adoption opt-in without saying who must opt in)
for f in sorted(root.rglob('*.als')):
    parts = f.relative_to(root).parts
    if 'tests' in parts or 'legacy' in parts or parts[0] in ('soak', 'examples') or (len(parts) > 1 and parts[1] == 'examples'): continue
    s = f.read_text(errors='replace')
    # subject_log instances: NO obligation since Q8 (uniqueness is a module FACT); the guard's refusal is the kind's choice.
    for m in re.finditer(r'^\s*open\s+meta/intent_log/intent_log\[([^\]]*)\]\s+as\s+(\w+)', s, re.M):
        params, x = m.group(1), m.group(2)
        for pred in ('spineAdopted', 'citationView'):
            ok = bool(re.search(rf'\b{x}/{pred}\b', s)); rows.append((str(f.relative_to(root)), f'intent_log as {x}', pred, ok)); bad += (not ok)
        if 'HoldSem' in params:   # E2b (DT-029 Q9): a HOLD-chain seat owes the HELD rule — a fact binding peerView at prePhase = I_HELD
            ok = bool(re.search(rf'{x}/prePhase\[[^\]]*\]\s*=\s*(?:sem/)?I_HELD\s+implies', s)); rows.append((str(f.relative_to(root)), f'intent_log as {x}', 'HELD rule (peerView at I_HELD)', ok)); bad += (not ok)
w = max(len(r[0]) for r in rows) if rows else 10
for r in rows: print(f'{"OK  " if r[3] else "MISSING"}  {r[0]:{w}s}  {r[1]:28s}  {r[2]}')
print(f'\n{len(rows)} adoption obligations, {bad} MISSING -> {"RED" if bad else "GREEN"}'); sys.exit(1 if bad else 0)
