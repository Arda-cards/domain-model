#!/usr/bin/env python3
"""cone.py — the verification cone of a change, derived from the model's `open` graph (never by eye).

A root (any alloy/**/tests/*.als, alloy/soak/**/*.als — the Makefile's gate walk plus the soak tree) is IN the cone of a changed
file when the file is reachable from the root through `open` lines, transitively. Alloy resolves unqualified
names across the whole transitive open graph, so a root that never names a changed module can still fail to
parse because of it (Tier B at 793cfe0, 2026-09-09: `inventory_item_implementation.als:59` became ambiguous
through two `lc/` opens three levels away).

Usage:
  tools/cone.py [--repo DIR] [--base REV] [--head REV|WORKTREE] [--files f1 f2 ...] [--roots-only] [--selftest]
  default: changed files = `git diff --name-only <base>..<head> -- alloy` with base = origin/main, head = the
  working tree (staged + unstaged + committed since base). `--files` overrides the change set.
Output: one line per root in the cone: `<root>\t<changed file(s) it reaches>`; then a summary line
`cone: roots=N of M (changed files=K)`. Exit 0 always (a gate reads the list; the launch record cites it).
"""
import argparse, os, re, subprocess, sys

OPEN_RE = re.compile(r'^\s*open\s+([A-Za-z0-9_/]+)')          # `open path[Params] as alias` → path


def rel_module(path_from_alloy: str) -> str:
    return path_from_alloy[:-4] if path_from_alloy.endswith('.als') else path_from_alloy


def opens_of(alloy_dir: str, module: str, cache: dict) -> set:
    if module in cache:
        return cache[module]
    p = os.path.join(alloy_dir, module + '.als')
    res = set()
    if os.path.isfile(p):
        with open(p, encoding='utf-8', errors='replace') as fh:
            for line in fh:
                m = OPEN_RE.match(line)
                if m:
                    res.add(m.group(1))
    cache[module] = res
    return res


def closure(alloy_dir: str, module: str, cache: dict) -> set:
    seen, todo = set(), [module]
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        todo.extend(opens_of(alloy_dir, m, cache) - seen)
    return seen


def find_roots(alloy_dir: str) -> list:
    roots = []
    for d, _, files in os.walk(alloy_dir):
        rel_d = os.path.relpath(d, alloy_dir)
        if '/legacy' in ('/' + rel_d) or rel_d.startswith('legacy'):
            continue
        for f in files:
            if not f.endswith('.als'):
                continue
            rel = os.path.normpath(os.path.join(rel_d, f))
            if '/tests/' in '/' + rel or rel.startswith('soak/'):   # = the Makefile's gate walk + the soak tree
                roots.append(rel)
    return sorted(roots)


def cone(alloy_dir: str, changed: set) -> tuple:
    """changed: module paths relative to alloy/ (no .als). Returns ([(root, [changed modules reached])], all roots)."""
    cache, out = {}, []
    roots = find_roots(alloy_dir)
    for r in roots:
        reach = closure(alloy_dir, rel_module(r), cache)
        hit = sorted(reach & changed)
        if hit:
            out.append((r, hit))
    return out, roots


def changed_from_git(repo: str, base: str, head: str) -> set:
    if head == 'WORKTREE':
        cmd = ['git', '-C', repo, 'diff', '--name-only', base, '--', 'alloy']
    else:
        cmd = ['git', '-C', repo, 'diff', '--name-only', f'{base}..{head}', '--', 'alloy']
    files = subprocess.check_output(cmd, text=True).split()
    return {rel_module(f[len('alloy/'):]) for f in files if f.startswith('alloy/') and f.endswith('.als')}


def selftest() -> int:
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        a = os.path.join(d, 'alloy')
        for path, body in {
            'meta/lc.als': 'module meta/lc\n',
            'ref/item_types.als': 'module ref/item_types\nopen meta/lc[Item, Rec] as lc\n',
            'res/inv_types.als': 'module res/inv_types\nopen ref/item_types\n',
            'res/inv_impl.als': 'module res/inv_impl\nopen res/inv_types\n',
            'res/tests/unit/inv.als': 'module res/tests/unit/inv\nopen res/inv_impl\n',
            'res/tests/metrics.als': 'module res/tests/metrics\nopen res/inv_impl\n',
            'other/tests/x.als': 'module other/tests/x\nopen meta/kernel\n',
            'soak/sliced/s.als': 'module soak/sliced/s\nopen res/inv_types\n',
            'meta/kernel.als': 'module meta/kernel\n',
            'legacy/tests/old.als': 'open meta/lc\n',
        }.items():
            os.makedirs(os.path.dirname(os.path.join(a, path)), exist_ok=True)
            with open(os.path.join(a, path), 'w') as fh:
                fh.write(body)
        hits, roots = cone(a, {'meta/lc'})
        got = sorted(r for r, _ in hits)
        exp = ['res/tests/metrics.als', 'res/tests/unit/inv.als', 'soak/sliced/s.als']
        assert got == exp, (got, exp)                      # three levels of opens; metrics + soak count as roots
        assert 'other/tests/x.als' in roots and 'other/tests/x.als' not in got   # a root outside the cone
        assert 'legacy/tests/old.als' not in roots         # legacy excluded
        hits2, _ = cone(a, {'meta/kernel'})
        assert [r for r, _ in hits2] == ['other/tests/x.als'], hits2
    print('cone.py selftest: 4 cases OK')
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--repo', default=os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    ap.add_argument('--base', default='origin/main')
    ap.add_argument('--head', default='WORKTREE')
    ap.add_argument('--files', nargs='*', help='changed files (alloy/... paths) instead of git diff')
    ap.add_argument('--roots-only', action='store_true')
    ap.add_argument('--selftest', action='store_true')
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    alloy_dir = os.path.join(args.repo, 'alloy')
    if args.files:
        changed = {rel_module(f[len('alloy/'):] if f.startswith('alloy/') else f) for f in args.files}
    else:
        changed = changed_from_git(args.repo, args.base, args.head)
    hits, roots = cone(alloy_dir, changed)
    for r, hit in hits:
        print(r if args.roots_only else f'{r}\t{" ".join(hit)}')
    print(f'cone: roots={len(hits)} of {len(roots)} (changed files={len(changed)})', file=sys.stderr)
    return 0


if __name__ == '__main__':
    sys.exit(main())
