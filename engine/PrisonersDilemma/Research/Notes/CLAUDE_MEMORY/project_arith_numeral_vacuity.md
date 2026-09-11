---
name: project-arith-numeral-vacuity
description: "2026-09-10/11 — unary numerals made every bounded search fail (theorem, fixed by binary descriptions + guard_fits); SECOND finding: under Cantor pairing the CODE of a binary numeral term is as long as a unary numeral, so a searcher naming its own budget inside a box cannot fit (blocks T3, not T1/T2); traps about giant-term evaluation"
metadata: 
  node_type: memory
  type: project
  originSessionId: 1a734d76-f764-480d-8461-59dedf4d8e0a
  modified: 2026-09-11T09:31:47.262Z
---

**Finding 1 (theorem, `Vacuity.lean` at 470ee43, retired):** a guard sentence named the
searcher by a UNARY numeral of its own code (≥ its budget k); every proof is at least as
long as its conclusion, so no top-level search node could ever succeed. Critch's (b) is
load-bearing. FIXED: binary numeral terms in descriptions (`Bnum.lean`, `descVec`), and
`Fit.lean`'s `guard_fits` (T1 non-vacuous, all large k).

**Finding 2 (theorem, `arith/ArithS/FitBox.lean`, commit 7fd38cc, wired, `box_guard_never_fits`
at EVERY budget; `legibleBot_guard_never_fits`; positive side `exists_flen_tmpl_const`):** `size_bnum_ge : n + 2 ≤ Nat.size (bnum n)` — the
Cantor-pairing CODE of the binary numeral term of value n has bit length ≥ n + 2 (each `2·t+1`
step nests a pair, doubling the bit length; depth log n ⇒ length n). Consequence: a searcher
whose stored template mentions ITS OWN budget k inside a box (`numTB k` in `tmpl_box`) has a
description of length ≥ k, so such a guard cannot fit its budget. T1/T2 unaffected (box-free
guards); blocks the T3 Löbian program until the coding changes. Fix options (not built): box
budgets as node data referenced by a template variable; or BALANCED numeral terms
(`n = a·b + c`, `a, b ≈ √n`, depth O(log log n) ⇒ polylog code). Occurrence of `#0` in the provability formula IS provable syntactically in 10 s
(`simp only [sigma_mkDelta, val_mkSigma]` exposes only the connective skeleton); the hangs
were unification unfolding `qqAnd/qqExs` to `pair`, an index mismatch making `isDefEq` unfold
a giant quote, and `whnf` of closed `Nat` arithmetic on symbol counts (see the file's note).

**Traps:** a theorem stated with CLOSED constants built from a template (`10 * cG₀`,
`Nat.size cP`) makes Lean EVALUATE `flen`/`encode` on the giant DSL term (hours, then kernel
"deterministic timeout"); `@[irreducible]` does not stop the kernel — package such constants
EXISTENTIALLY, arithmetic over variables. `lake env lean` output is block-buffered when
redirected (a partial log shows nothing); bisect slow files by truncation with `timeout`;
`set_option maxHeartbeats N in` goes BEFORE the docstring. State "for all large k", never
quote a constant. See [[project-arithmetized-s-roadmap]].
