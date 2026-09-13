# arith/scripts

`gen_rowinst.py` regenerates `arith/ArithS/Necessitation/RowInst.lean` (the row-shape and
instantiation lemmas of the verification proof's formula walk, 2026-09-13):

    python3 arith/scripts/gen_rowinst.py arith/ArithS/Necessitation/RowInst.lean

It reads the hand-written header `<out>.head` — kept here as `RowInst.lean.head`; copy it next to
the output (or symlink) before running. The generated file is checked in; regenerate only when
a row's shape changes, then rebuild `ArithS` and re-check the census.

`gen_frag.py` generates BOTH `arith/ArithS/Necessitation/Lib/Frag.lean` (the fragment rows of
`DESIGN_fragments.md` §8.1: bodies, `models_`, `pa_proves_`, `lib_`) and
`arith/ArithS/Necessitation/RowInstB.lean` (their predicate/fact codes, row-shape and `inst_` lemmas)
from ONE row table (2026-09-13):

    python3 arith/scripts/gen_frag.py arith/ArithS/Necessitation/Lib/Frag.lean arith/ArithS/Necessitation/RowInstB.lean [group,group,…]

The hand-written headers `Frag.lean.head` / `RowInstB.lean.head` are read from this directory
(no copying). The optional third argument restricts both outputs to the listed groups
(`copy,ident,fun,sets,fstIdx,nodes,lengths,cert,num,axm`) — for checking a group in isolation;
the checked-in files are the full generation. Per-row proofs live in the table as Lean strings.
