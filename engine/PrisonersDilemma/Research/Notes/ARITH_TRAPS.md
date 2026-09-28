# ARITH_TRAPS — the proof-craft trap list for `arith/ArithS` (consolidated 2026-09-24)

*One place for what used to be scattered across `HANDOVER_ARITHMETIZED_S.md` §6, the `TRAPS`
paragraphs of `ROUTE_B_SCOPE.md` §6, the roadmap's status log and the M4 brief §9. Every entry cost
an agent-hour or more. Add to it when you lose one. Grouped by where it bites.*

## 1. `V` vs `ℕ` (the two-instance world)

* At `V = ℕ`, `<` is `Nat.lt` but `≤` is PeanoMinus's `le_def` (`x = y ∨ x < y`). Bridge with
  `le_def.mp/.mpr`; `nat_le_of_le_def`, `le_def_trans` exist.
* `omega` is USELESS on `V` — use `le_self_add`/`le_add_self`/`gcongr` under `open PeanoMinus`; do
  the arithmetic at ℕ and transport.
* Two `Nat.cast` instances at ℕ: `((K : ℕ) : ℕ)` in a `have` elaborates the cast AWAY
  (`instNatCastNat`) while V-generic lemmas instantiated at ℕ want Foundation's cast — never state a
  threshold hypothesis separately; discharge it INLINE at the use site (`by rw [natCast_nat]; exact
  le_def.mpr …`). `Nat.cast_id` does not fire on that cast; `natCast_nat` does.
* Never restate at ℕ a term carrying `‖k‖ ^ d` / `gBudget k ^ d`: the pow instance is
  `instCommSemiring_foundation ℕ`, not `Nat.instMonoid` — `rw [pow_one]`/`simp [pow_one]` do not fire.
  Take the Nat inequality with its sides INFERRED (`nat_le_of_le_def (le_def.mp h)`); remove exponents
  inside the V-generic binder (`linear_size_le_eventually`).
* A statement mentioning only `MirrorV`/`pBot`/`pConst` without a `V`-pinned term elaborates at ℕ
  SILENTLY (`models_ISigmaOne` found by TC with a metavariable `V`) — write `(MirrorV : V)`.
* `IsSemiterm LAct n t` with `n : ℕ` silently forces `V = ℕ` — cast the arity `((n : ℕ) : V)`, or
  `have … ; rwa [← seven_eq]` so the arity literal is not rewritten.
* `Describes`/`LoebSound` fields quantify `(V : Type)` explicitly so they are usable at ℕ and inside
  other `(V : Type)`-quantified proofs — not under a file-level `{V : Type*}`.
* Foundation shadows Mathlib: `add_le_add_left h a : h.lhs + a ≤ h.rhs + a`, `add_le_add_right h a :
  a + … ≤ a + …` (SWAPPED vs Mathlib), `add_lt_add_right` is the LEFT version; `one_ne_zero` is
  ambiguous under `open Arithmetic`. Use `_root_.`.

## 2. Gödel quotes, numerals, giant DSL terms

* NEVER `simp` a goal containing a closed quote of a big sentence (`⌜qDupoc⌝`, `⌜tactDiag θ⌝`,
  `⌜tmplD⌝`): the kernel builds a numeral over `LEAN_NAT_MAX_SIZE`. State for a VARIABLE sentence,
  instantiate, bridge by `rfl`. Never put a closed numeral inside a Δ₁ fixpoint blueprint (26 GB).
* Closed constants built from a giant template (`flen (GtmplA 0)`, `⌜GtmplA 0⌝ ≤ ⌜GtmplA 1⌝`, `KP`,
  `innerP2`) must never be evaluated: package existentially or as irreducible ℕ-constants; case-split
  with `le_total`; decide code ORDERS by `unfold … pConst pOpp ppair; norm_num` — Cantor pairing is NOT
  lexicographic, componentwise `ppair_lt_*` chains cannot decide `TftV < TftTV`.
* `simp [closedDesc, descF, cl, dnumT]` on a template HANGS — separate templates SEMANTICALLY
  (`tcode_ne_of_models`).
* Foundation numerals are unary; every budget entering a sentence goes through `bnum`; the CODE of a
  binary numeral term is exponential under Cantor pairing (`size_bnum_ge`, `box_guard_never_fits`).
* A typed `Rewriting.subst` equality closed by bare `rfl` passes the ELABORATOR but times out in the
  KERNEL — factor into small `descF_*_subst` lemmas with explicit `show`.
* `rw [show (4:V) = 0+1+1+1+1]` also rewrites the `4` inside `^#4`; `rw [relabel_const]` rewrites EVERY
  `pConst 1` at once; `rw [cast_pConst, cast_pConst, cast_pConst]` fails on the third (the first
  instantiates `a`).
* `nth_adjoin_one/two` SHIFT (`(x ∷ v).[1] = v.[0]`) — finish with `simp only [nth_adjoin_zero, …]`.
* `LogicalConnective.HomClass.map_and` fires on `Semiformula.Eval` — unfold the family defs and
  `simp only`, do not chain `rw [map_and, map_and]`.
* `Template.lMap_swap_dnumT` already exists with the OTHER normal form — a same-named local lemma is
  silently shadowed by the import.

## 3. Fixpoints, blueprints, long lists (U10 territory)

* The house pattern for every `Fixpoint`/`PR` definability proof: targeted `simp only` +
  `rw [eval_fixpointDef]`; a blanket `simp` over a five-disjunct blueprint hangs 30 min.
  In `TermRec`/`UformulaRec1` blueprints, ∃-wrap graph clauses (`∃ s, !listSumDef s v' ∧ y = s`).
* A `getElem` on a ~200-row list with a CLOSED index or an implicit bound proof makes
  `get_elem_tactic` walk the list — state for a VARIABLE index with `hi : i = cIdx` and explicit
  `l[i]'h`; go through `getElem?` (`List.getElem?_append_left/right`). `(l₁ ++ l₂)[i]?` does not parse
  (collides with `?[…]`) — `unfold` first.
* An `obtain`ed `x` is not definitionally `⌜σ⌝` — feed pins `hxdef ▸ …`; shift with the
  `numeral`-stated `termShiftIterV_numeral`.
* U10 specifics: witness lists are the row's DSL variable list read RIGHT-TO-LEFT; Foundation's
  `exsIntro` keeps the principal formula; `IsUTermVec` hypotheses arrive unfolded after
  `pi1_succ_induction`; `derivation TAct` only as `!(derivation TAct).sigma`; the `.pi`/`.sigma`
  polarity convention (hypotheses `.pi`, conclusions `.sigma`).

## 4. `EvalGraph`, `psubst`, `closedP`

* `EvalGraph.mono_le (by omega)` needs the SOURCE fuel explicit (`(n := 0+1+1)`, `const_play 3 _ _ _`).
* `closedP` is FALSE on DBot/EBot/TFT/OBot (pronouns inside `.sim`), so `fragF` of a closed atom over
  them fails — state τ on `tmpl (.plays p q a)` with `fragP` only (`lMap_swap_tmpl_plays`); `rfl` does
  not reduce `closedP` on concrete programs (mutual recursion) — `simp [closedP, …]`.
* `Formula` is ambiguous with Foundation's: `PD.Formula`. `simp` never rewrites the instance-implicit
  structure of `Semiformula.Eval` — `rw [stdAct_lMap_emb]`.
* `set t := …`/`set s := Nat.size k` AFTER the facts that mention them (`lenProvable_inst_size`,
  `lenProvable_le_bnumT`, `hE.nec`) or `omega` sees two atoms; `set` does not fold into later facts.
* `AgentConverse.eval_iff_evalGraph` quantifies `GuardAgree` over ALL formulas — it cannot be
  discharged per cell; the search-free/lockstep induction (`Cells/SearchFree`) is the template.
* `k̂`/`lit` are not identifiers; uniform existential constants are pure terms; pin `(k := 0)` on
  `qqTwo_semiterm.isUTerm`.

## 5. Tooling

* Never compile Foundation/mathlib (`lake build --try-cache`; `arith/.lake` is a symlink outside
  OneDrive). ONE lake build on the machine at a time: `pgrep -f 'elan/toolchains.*bin/lake build'`
  (plain `pgrep -f 'lake build'` matches your own polling shell; `pgrep -f "lake env lean …"` too —
  watch a SENTINEL file instead).
* `lake env lean` output is block-buffered when redirected; bisect slow files by truncation; only
  exit 124 + an EMPTY log is a stall. Check the exit code of `lake env lean` ITSELF: in zsh
  `${pipestatus[1]}`, not `${PIPESTATUS[0]}`; a `timeout` kill upstream of `tail`/`grep` looks green.
* A full `lake build ArithS` rebuilds everything downstream of an edited trusted-base file
  (`Agents/Guard`/`Agents/Subst`/`Eval/Eval`: ~3350 jobs, 10–30 min) — targeted `lake build ArithS.<Module>` and
  single-file checks per agent; the coordinator runs the one full build.
* BSD `sed` has no `\b` (`perl -pi`); python heredocs die on `'''` inside Lean text (`VerifyKit'''`) —
  write Lean and notes via SHELL heredocs; a `-/` inside prose (`four-/seven-`) closes a docstring.
* Agents stall on open-ended background waits — bounded polling (≤ 60 s, ≤ 900 s per call), never end
  a turn while your own check runs; resume a stalled agent by message, its commits are usually on disk.
* Every new module is imported in BOTH `ArithS.lean` and the relevant `ArithS/Audit/<Layer>.lean` (nine
  per-layer census files since 2026-09-28, each with its own minimal import list, imported by the thin
  `Audit.lean`); the census is every `#print axioms` the build runs, not `Audit/` alone. The top level of
  `ArithS/` is grouped into layer folders since the same day — old→new map in `arith/PATHS.md`.

## 6. Generated files

* Nine `Necessitation/*Rows.lean` files (and `Lib/Frag.lean`, `RowInst.lean`, `RowInstB.lean`) are
  GENERATED by `arith/scripts/gen_*.py` and carry a marker. Never hand-edit them: edit the generator or
  its `.head`, regenerate, run `arith/scripts/regen_all.sh` (diffs all nine against the tree), rebuild,
  re-check the census. Hand-written additions go in a SEPARATE module (`RowInstC.lean` is the precedent —
  the one drift found, 2026-09-28, was 154 lines appended after generation).
