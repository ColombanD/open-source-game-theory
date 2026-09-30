#!/usr/bin/env python3
"""Import direction between the tiers of ArithS (README §1). Exit 0 iff no module imports upward.

Tiers (by module name; the roots ArithS/{Core,Frozen,PBLT,Matrix}.lean must import exactly their tier):
  core     Basic, Notation, Readings, Theory.*, Length.*, Box.*, Agents.* (but Fit, FitBox, Instance, InstanceV),
           Eval.* (but Det, Transparency), Cells.RedCell
  frozen   Agents.Fit, Agents.FitBox, Eval.Det, Bridge.*                       may import: core
  loeb     Loeb.*, Agents.Instance, Agents.InstanceV, Eval.Transparency,
           Assembly.*, Necessitation.*                                         may import: core, frozen
  results  Cells.* (but RedCell), Outcome.*                                    may import: core, frozen, loeb
           (of Necessitation only Package and ClosedNec)
  top      Audit.*, Audit, Tour, Outcome.Check, Outcome.Export (lake roots), ArithS   may import: anything
Lake cannot enforce this (libraries of one package see every module); this script does.
"""
import pathlib, re, sys
root = pathlib.Path(__file__).resolve().parent.parent
files = sorted(root.glob("ArithS/**/*.lean")) + [root / "ArithS.lean"]
def modname(p):
    rel = p.relative_to(root).with_suffix("")
    return ".".join(rel.parts)
FROZEN = {"ArithS.Agents.Fit", "ArithS.Agents.FitBox", "ArithS.Eval.Det"}
LOEBX = {"ArithS.Agents.Instance", "ArithS.Agents.InstanceV", "ArithS.Eval.Transparency"}
def tier(m):
    if m in ("ArithS", "ArithS.Core", "ArithS.Frozen", "ArithS.PBLT", "ArithS.Matrix", "ArithS.Tour", "ArithS.Audit",
             "ArithS.Outcome.Check", "ArithS.Outcome.Export") or m.startswith("ArithS.Audit."): return "top"
    if m == "ArithS.Cells.RedCell": return "core"
    if m in FROZEN or m.startswith("ArithS.Bridge"): return "frozen"
    if m in LOEBX or m.startswith(("ArithS.Loeb", "ArithS.Assembly", "ArithS.Necessitation")): return "loeb"
    if m.startswith(("ArithS.Cells", "ArithS.Outcome")): return "results"
    if m in ("ArithS.Basic", "ArithS.Notation", "ArithS.Readings") or m.startswith(("ArithS.Theory", "ArithS.Length", "ArithS.Box", "ArithS.Agents", "ArithS.Eval")): return "core"
    return None
RANK = {"core": 0, "frozen": 1, "loeb": 2, "results": 3, "top": 4}
ROOTS = {"core": "ArithS.Core", "frozen": "ArithS.Frozen", "loeb": "ArithS.PBLT", "results": "ArithS.Matrix"}
imports = {}
for p in files:
    imports[modname(p)] = re.findall(r"^import (ArithS[\w.]*)", p.read_text(), re.M)
bad = []
for m, deps in imports.items():
    t = tier(m)
    if t is None: bad.append(f"{m}: no tier"); continue
    for d in deps:
        td = tier(d)
        if td is None: bad.append(f"{m}: imports {d}, which has no tier"); continue
        if RANK[td] > RANK[t]: bad.append(f"{m} ({t}) imports {d} ({td})")
        if t == "results" and d.startswith("ArithS.Necessitation") and d not in ("ArithS.Necessitation.Package", "ArithS.Necessitation.ClosedNec"):
            bad.append(f"{m} (results) imports the U10 construction {d}; only Package/ClosedNec are allowed")
# roots complete
for t, r in ROOTS.items():
    if t == "loeb":
        want = {m for m in imports if tier(m) == t and not (m.startswith("ArithS.Necessitation") and m not in ("ArithS.Necessitation.Package", "ArithS.Necessitation.ClosedNec"))}
    else:
        want = {m for m in imports if tier(m) == t}
    have = set(imports.get(r, []))
    for m in sorted(want - have): bad.append(f"root {r} misses {m}")
    for m in sorted(have - want): bad.append(f"root {r} imports {m}, which is not in tier {t}")
if bad:
    print("\n".join(bad)); print(f"{len(bad)} tier violation(s)"); sys.exit(1)
n = {t: sum(1 for m in imports if tier(m) == t) for t in RANK}
print("tiers ok:", ", ".join(f"{t} {n[t]}" for t in RANK))
