# arith/scripts

`gen_rowinst.py` regenerates `arith/ArithS/Necessitation/RowInst.lean` (the row-shape and
instantiation lemmas of the verification proof's formula walk, 2026-09-13):

    python3 arith/scripts/gen_rowinst.py arith/ArithS/Necessitation/RowInst.lean

It reads the hand-written header `<out>.head` — kept here as `RowInst.lean.head`; copy it next to
the output (or symlink) before running. The generated file is checked in; regenerate only when
a row's shape changes, then rebuild `ArithS` and re-check the census.
