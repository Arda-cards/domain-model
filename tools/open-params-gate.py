#!/usr/bin/env python3
"""open-params-gate.py <alloy-root> | --selftest — model-gate rule 10 (2026-09-04): every parameter of a parametric `open`
is either ALIAS-QUALIFIED (`kt/CardCycle`) or DECLARED IN THE SAME FILE (a local sig, or the module's own parameter) —
never a bare name imported from elsewhere, which resolves by whatever import paths happen to be in scope (loud with several,
SILENT with one). Checked PER PARAMETER, not per line (a mixed list `[inv/Pool, CardCycle]` must flag `CardCycle`).
Trailing `//` comments are stripped first. Exit 1 if any parameter is flagged."""
import re, sys, pathlib, tempfile
BUILTIN = {'Int', 'univ', 'none', 'String', 'seq/Int', 'iden'}   # Alloy's own names: one declaration, in the language

def flagged(path: pathlib.Path):
    s = path.read_text(errors='replace'); local = set()
    for names in re.findall(r'^\s*(?:(?:abstract|one|lone|some|var)\s+)*sig\s+([\w\s,]+?)\b\s*(?:extends\b|in\b|\{)', s, re.M):
        local.update(n.strip() for n in names.split(',') if n.strip())
    mp = re.search(r'^\s*module\s+\S+\s*\[([^\]]*)\]', s, re.M)
    if mp: local.update(p.strip().split()[-1] for p in mp.group(1).split(',') if p.strip())   # `exactly Key` forms
    out = []
    for ln, line in enumerate(s.splitlines(), 1):
        code = line.split('//', 1)[0]
        m = re.match(r'^\s*open\s+\S+?\[([^\]]*)\]', code)
        if not m: continue
        for p in m.group(1).split(','):
            p = p.strip()
            if p and '/' not in p and p not in local and p not in BUILTIN: out.append((ln, p))
    return out

def selftest():
    cases = [  # (file text, expected flagged parameter names)
        ("open util/ordering[Foo]\n", ['Foo']),
        ("open meta/subject_log/subject_log[kt/CardCycle, kt/CycleState] as clog\n", []),
        ("open hold/citation[CardCycle]\n", ['CardCycle']),
        ("open inventory/pool[inv/Pool, kt/Card]\n", []),
        ("open mixed/case[inv/Pool, CardCycle]\n", ['CardCycle']),            # MINESWEEPER's mixed list
        ("open m[ kt/A , B ]\n", ['B']),                                       # whitespace
        ("sig Item {}\nsig ItemState extends Snapshot {}\nopen meta/subject_log/subject_log[Item, ItemState] as ilog\n", []),   # local sigs
        ("module meta/intent_log/intent_log[Key, Sem]\nsig IntentRec extends IntentRecord {}\nopen meta/subject_log/subject_log[Key, IntentRec] as ilog\n", []),   # module parameter + local
        ("open shared/measurement/quantity   // Signal [x] in a comment\n", []),   # comment noise, no parameters
        ("one sig A_START, A_SHELVE extends CycleAct {}\nopen x/y[A_START, Other]\n", ['Other']),   # comma-declared local sigs
        ("sig Reading {}\nopen meta/measurement/measurement[Reading]\n", []),                       # a name containing "in" is local (regex bug 3)
        ("sig OrderLine extends Scoped {\n  x: one Int\n}\nopen m[OrderLine, OrderLineState]\n", ['OrderLineState']),   # multi-line decl; the other is not local
        ("sig Bin in Item {}\nopen m[Bin]\n", []),                                                # `sig X in Y` form still recognized
        ("open meta/measurement/measurement[Int]\n", []),                                           # a builtin is not a parameter to qualify
    ]
    bad = 0
    with tempfile.TemporaryDirectory() as d:
        for i, (txt, want) in enumerate(cases):
            p = pathlib.Path(d) / f'c{i}.als'; p.write_text(txt); got = [n for _, n in flagged(p)]
            ok = got == want; bad += (not ok); print(f'{"ok  " if ok else "FAIL"} case {i}: want {want} got {got}')
    print('selftest', 'GREEN' if not bad else 'RED'); sys.exit(1 if bad else 0)

if __name__ == '__main__':
    if sys.argv[1] == '--selftest': selftest()
    root = pathlib.Path(sys.argv[1]); rows = []; decls = {}
    for f in sorted(root.rglob('*.als')):
        for ln, p in flagged(f): rows.append((str(f.relative_to(root)), ln, p))
        for names in re.findall(r'^\s*(?:(?:abstract|one|lone|some|var)\s+)*sig\s+([\w\s,]+?)\b\s*(?:extends\b|in\b|\{)', f.read_text(errors='replace'), re.M):
            for n in names.split(','):
                if n.strip(): decls.setdefault(n.strip(), []).append(str(f.relative_to(root)))
    # MINESWEEPER's discriminator (2026-09-04): a name declared ONCE tree-wide resolves by construction (hygiene); declared in TWO or more
    # files it resolves by accident of scope — the silent variant waiting to happen (fix first). Multi-name `sig A, B extends` lists counted.
    for r in rows:
        d = decls.get(r[2], []); tag = 'BY-CONSTRUCTION (1 decl)' if len(d) == 1 else f'BY-SCOPE ({len(d)} decls: {", ".join(sorted(set(d)))})' if d else 'NO DECLARATION FOUND (module parameter of an opened module?)'
        print(f'{r[0]}:{r[1]}  <- unqualified, not local: {r[2]}   [{tag}]')
    files = len({r[0] for r in rows}); multi = [r for r in rows if len(decls.get(r[2], [])) != 1]
    print(f'\n{len(rows)} unqualified non-local open parameters in {files} files -> {"RED" if rows else "GREEN"}; {len(multi)} resolve by scope (fix FIRST), {len(rows) - len(multi)} by construction'); sys.exit(1 if rows else 0)
