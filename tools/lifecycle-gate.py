#!/usr/bin/env python3
"""lifecycle-gate.py <alloy-root> [--selftest] — the SHAPE PARTITION gate (DT-030, plan of record 2026-09-09; MINESWEEPER's
risk-3 condition: mechanized, not prose). For every NON-test module that opens meta/subject_log/lifecycle[...] as X:
  (1) no CONCRETE sig may extend the spine's SubjectOcc directly (`sig K extends Y/SubjectOcc`, Y the module's subject_log
      alias for the same parameters) — every kind is declared under a shape (X/CreateOcc, X/RetireOcc, X/MutateOcc, an
      affirm alias's AffirmOcc) or under a LOCAL abstract sig that is;
  (2) the set of adopting modules must EQUAL the declared set below — a seventh adopter fails loudly until it is listed,
      so a shape theorem is never cited as coverage of more logs than it binds.
Exit 1 on any finding (a red gate, never a silent pass)."""
import re, sys, pathlib

ADOPTERS = {   # module path (relative to the alloy root) -> the lifecycle alias it opens. EDIT THIS LIST WHEN A LOG ADOPTS.
    'operations/demand/demand_types.als': 'lc',
    'procurement/order/order_types.als': 'lco, lcl',
    'reference_data/item/item_types.als': 'lc',
    'reference_data/item/item_implementation.als': 'lc',
    'reference_data/staff/staff_types.als': 'lc',
    'reference_data/staff/staff_implementation.als': 'lc',
    'reference_data/business_affiliate/business_affiliate_types.als': 'lc',
    'reference_data/business_affiliate/business_affiliate_implementation.als': 'lc',
    'operations/demand/demand_implementation.als': 'lc',
    'procurement/order/order_implementation.als': 'lco, lcl',
    'meta/subject_log/affirm.als': 'lc',
}

OPEN_LC = re.compile(r'^\s*open\s+meta/subject_log/lifecycle\[([^\]]*)\]\s+as\s+(\w+)', re.M)
OPEN_SL = re.compile(r'^\s*open\s+meta/subject_log/subject_log\[([^\]]*)\]\s+as\s+(\w+)', re.M)
SIG = re.compile(r'^\s*(abstract\s+)?sig\s+([A-Za-z_][\w]*(?:\s*,\s*[A-Za-z_][\w]*)*)\s+extends\s+([\w/]+)', re.M)

SHAPE_MODULES = {'meta/subject_log/affirm.als'}   # declares a SHAPE (AffirmOcc) beside lifecycle: exempt from rule (1), counted as an adopter

def check(root: pathlib.Path, adopters=None):
    adopters = ADOPTERS if adopters is None else adopters
    rows, bad, found = [], 0, {}
    for f in sorted(root.rglob('*.als')):
        parts = f.relative_to(root).parts
        if 'tests' in parts or 'legacy' in parts or parts[0] in ('soak', 'examples') or (len(parts) > 1 and parts[1] == 'examples'): continue
        s = f.read_text(errors='replace'); rel = str(f.relative_to(root))
        lcs = OPEN_LC.findall(s)
        if not lcs: continue
        params_to_lc = {p.replace(' ', ''): a for p, a in lcs}
        found[rel] = ', '.join(a for _, a in lcs)
        spine_aliases = {a for p, a in OPEN_SL.findall(s) if p.replace(' ', '') in params_to_lc}
        for m in SIG.finditer(s):
            abstract, names, parent = m.group(1), m.group(2), m.group(3)
            if abstract or rel in SHAPE_MODULES: continue
            if '/' in parent and parent.split('/')[0] in spine_aliases and parent.endswith('/SubjectOcc'):
                rows.append((rel, names, parent, False)); bad += 1
            else:
                rows.append((rel, names, parent, True))
    declared = set(adopters); actual = set(found)
    for extra in sorted(actual - declared): rows.append((extra, '(module)', 'adopts lifecycle but is NOT in the declared adopter set', False)); bad += 1
    for missing in sorted(declared - actual): rows.append((missing, '(module)', 'declared an adopter but does not open lifecycle', False)); bad += 1
    return rows, bad

def selftest():
    import tempfile
    cases = 0
    with tempfile.TemporaryDirectory() as d:
        r = pathlib.Path(d); (r / 'x').mkdir()
        good = "open meta/subject_log/subject_log[A, B] as al\nopen meta/subject_log/lifecycle[A, B] as lc\nabstract sig M extends lc/MutateOcc {}\nsig K1 extends M {}\nsig K2 extends lc/RetireOcc {}\n"
        badk = good + "sig Stray extends al/SubjectOcc {}\n"
        A = {'x/m.als': 'lc'}
        for text, adopters, expect_bad in ((good, A, 0), (badk, A, 1), (good, {}, 1), ("sig Plain extends Snapshot {}\n", A, 1)):
            # 0: clean adopter; 1: the stray kind under SubjectOcc; 1: adopts but not declared; 1: declared but does not adopt
            (r / 'x' / 'm.als').write_text(text); rows, bad = check(r, adopters); assert bad == expect_bad, (text[:30], bad, expect_bad); cases += 1
    print(f'selftest OK ({cases} cases)')

if __name__ == '__main__':
    if '--selftest' in sys.argv: selftest(); sys.exit(0)
    rows, bad = check(pathlib.Path(sys.argv[1]))
    w = max((len(r[0]) for r in rows), default=10)
    for r in rows: print(f'{"OK  " if r[3] else "FAIL"}  {r[0]:{w}s}  {r[1]:34s}  extends {r[2]}')
    print(f'\n{len(rows)} declarations, {bad} FAIL -> {"RED" if bad else "GREEN"}'); sys.exit(1 if bad else 0)
