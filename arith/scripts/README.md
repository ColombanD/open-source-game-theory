# arith/scripts — the generators of the U10 row tables

U10 (bounded inner necessitation, `ArithS/Necessitation/`) is assembled from ROW TABLES: universal
lemma-sentences and per-rule fragments, each row a DSL formula plus the same ~25-line block of shape,
formula-ness and instantiation lemmas. Nine Python generators write nine `*Rows.lean` files (~27k lines)
from spec tables; the generated files are CHECKED IN and carry a `GENERATED` marker. The rule:

> **Never edit a generated `.lean` by hand.** Edit the generator (or its `.head`), regenerate, run
> `scripts/regen_all.sh` (regenerates all nine and diffs them against the tracked files — exit 0 iff
> all in sync; never runs `lake`), rebuild `ArithS`, re-check the census.

The one violation so far (2026-09-13, `6185743`: 154 lines appended to `RowInst.lean` after generation)
was split off into the hand-written `Necessitation/RowInstC.lean` on 2026-09-28.

| generator | writes | header | invocation (from `arith/`) |
|---|---|---|---|
| `gen_rowinst.py` | `Necessitation/RowInst.lean` (87 rows) | `RowInst.lean.head`, read as `<out>.head` — copy it next to the output first | `cp scripts/RowInst.lean.head ArithS/Necessitation/RowInst.lean.head && python3 scripts/gen_rowinst.py ArithS/Necessitation/RowInst.lean [subset]; rm ArithS/Necessitation/RowInst.lean.head` |
| `gen_frag.py` | `Necessitation/Lib/Frag.lean` AND `Necessitation/RowInstB.lean` (207 rows, one table) | `Frag.lean.head`, `RowInstB.lean.head` (read from this directory) | `python3 scripts/gen_frag.py ArithS/Necessitation/Lib/Frag.lean ArithS/Necessitation/RowInstB.lean [group,…]` |
| `gen_cert.py` | `Necessitation/CertRows.lean` (87) | inline | `python3 scripts/gen_cert.py` |
| `gen_frag1.py` | `Necessitation/Frag1Rows.lean` (39) | inline | `python3 scripts/gen_frag1.py` |
| `gen_frag2.py` | `Necessitation/Frag2Rows.lean` (24) | inline | `python3 scripts/gen_frag2.py` |
| `gen_indrec.py` | `Necessitation/IndRecRows.lean` (34) | `IndRecRows.lean.head` (this directory) | `python3 scripts/gen_indrec.py` |
| `gen_numid.py` | `Necessitation/NumIdRows.lean` (6) | inline | `python3 scripts/gen_numid.py` |
| `gen_proaxm.py` | `Necessitation/ProAxmRows.lean` (1) | inline | `python3 scripts/gen_proaxm.py` |
| `gen_prologue.py` | `Necessitation/PrologueRows.lean` | inline | `python3 scripts/gen_prologue.py` |

The in-place writers must run from `arith/` (relative paths). Per-row proofs live in the tables as Lean
strings; the design is `Research/Notes/M4_BOUNDED_HBL/DESIGN_fragments.md` §8.1. Verified in sync on
2026-09-28 (`regen_all.sh`: all nine `ok`).

## `DeadCode.lean` — the reachability audit

`lake env lean --run scripts/DeadCode.lean scripts/roots.txt <out.tsv>` (≈3 min on a built package) marks
every `ArithS` constant ROOT (in the `#print axioms` census, `roots.txt`; refresh it with
`grep -rhoE '^\s*#print axioms\s+\S+' ArithS | awk '{print $3}' | sort -u > scripts/roots.txt`),
LIVE (reachable from a root through types and proof terms) or DEAD. Report and tiers:
`engine/PrisonersDilemma/Research/Notes/ARITH_DEAD_CODE_AUDIT.md` (2026-09-28). The TSV is not committed.
