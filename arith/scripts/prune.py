"""Post-pass for the row-table generators: drop the declarations the reachability audit found DEAD.

Each generator calls `prune(text, module)` on its output before writing. The names to drop live in
`scripts/pruned/<module>.txt` (one Lean declaration name per line, `#` comments; the module name is the
Lean module without the `ArithS.` prefix, e.g. `Necessitation.RowInstB`). The lists are the DEAD set of
`docs/notes/ARITH_DEAD_CODE_AUDIT.md` (2026-09-28, `scripts/DeadCode.lean`): nothing in the census
reaches them, so dropping them changes no statement the package prints. A name in the list that the
generator no longer emits is ignored; a live row that cites a pruned lemma fails the build, which is the
check. To resurrect a row, delete its line from the list and regenerate.

A declaration chunk = an optional preceding docstring (`/-- … -/`) and `set_option … in` / `open … in`
prefix lines, the column-0 declaration line, and every following line up to the next column-0
non-blank line (continuation lines are indented), plus the blank lines after it.
"""
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
DECL = re.compile(r'^(@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |scoped |local )*'
                  r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|opaque)\s+([^\s:({\[]+)')


def load_names(module):
    path = os.path.join(HERE, 'pruned', module + '.txt')
    if not os.path.exists(path):
        return set()
    names = set()
    for line in open(path, encoding='utf-8'):
        line = line.split('#', 1)[0].strip()
        if line:
            names.add(line)
    return names


def prune(text, module, names=None):
    names = load_names(module) if names is None else set(names)
    if not names:
        return text
    lines = text.split('\n')
    n = len(lines)
    # 1. column-0 declaration starts, outside block comments
    starts = {}  # line index -> name
    depth = 0
    for i, ln in enumerate(lines):
        if depth == 0 and ln and not ln[0].isspace():
            m = DECL.match(ln)
            if m:
                starts[i] = m.group(2)
        depth += ln.count('/-') - ln.count('-/')
    # 2. chunks to delete
    delete = [False] * n
    idxs = sorted(starts)
    for pos, i in enumerate(idxs):
        if starts[i] not in names:
            continue
        # end: next column-0 non-blank line
        j = i + 1
        while j < n and (lines[j] == '' or lines[j][0].isspace()):
            j += 1
        # trailing blanks already included; keep ONE blank line before the next chunk if there was one
        end = j
        if end > i + 1 and lines[end - 1] == '':
            end -= 1
        # start: swallow preceding docstring / `… in` prefix lines
        s = i
        while s > 0:
            prev = lines[s - 1]
            if prev.rstrip().endswith(' in') and (prev.startswith('set_option') or prev.startswith('open')):
                s -= 1
                continue
            if prev.rstrip().endswith('-/'):
                k = s - 1
                while k >= 0 and not lines[k].startswith('/--'):
                    if lines[k].startswith('/-!') or (lines[k] and not lines[k][0].isspace() and k != s - 1 and lines[k].startswith('/-') is False and DECL.match(lines[k])):
                        k = -1
                        break
                    k -= 1
                if k >= 0:
                    s = k
                    continue
            break
        for t in range(s, end):
            delete[t] = True
    out = [ln for t, ln in enumerate(lines) if not delete[t]]
    # 3. drop a `/-! ### row -/` header whose whole row was pruned (the next non-blank line is another
    #    header or an `end`), then collapse runs of blank lines left behind
    kept = []
    for i, ln in enumerate(out):
        if ln.startswith('/-! ###') and ln.rstrip().endswith('-/'):
            j = i + 1
            while j < len(out) and out[j] == '':
                j += 1
            if j >= len(out) or out[j].startswith('/-!') or out[j].startswith('end'):
                continue
        kept.append(ln)
    res = []
    for ln in kept:
        if ln == '' and res and res[-1] == '':
            continue
        res.append(ln)
    return '\n'.join(res)


def decl_names(text):
    names = []
    depth = 0
    for ln in text.split('\n'):
        if depth == 0 and ln and not ln[0].isspace():
            m = DECL.match(ln)
            if m:
                names.append(m.group(2))
        depth += ln.count('/-') - ln.count('-/')
    return names
