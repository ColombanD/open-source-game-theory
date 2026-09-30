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
  `⌜templateD⌝`): the kernel builds a numeral over `LEAN_NAT_MAX_SIZE`. State for a VARIABLE sentence,
  instantiate, bridge by `rfl`. Never put a closed numeral inside a Δ₁ fixpoint blueprint (26 GB).
* Closed constants built from a giant template (`formulaLenMeta (guardTemplate 0)`, `⌜guardTemplate 0⌝ ≤ ⌜guardTemplate 1⌝`, `KP`,
  `innerP2`) must never be evaluated: package existentially or as irreducible ℕ-constants; case-split
  with `le_total`; decide code ORDERS by `unfold … pConst pOpp ppair; norm_num` — Cantor pairing is NOT
  lexicographic, componentwise `ppair_lt_*` chains cannot decide `TftV < TftTV`.
* `simp [closedDesc, descF, cl, canonicalMeta]` on a template HANGS — separate templates SEMANTICALLY
  (`templateCode_ne_of_models`).
* Foundation numerals are unary; every budget entering a sentence goes through `binNumeral`; the CODE of a
  binary numeral term is exponential under Cantor pairing (`size_binNumeral_ge`, `box_guard_never_fits`).
* A typed `Rewriting.subst` equality closed by bare `rfl` passes the ELABORATOR but times out in the
  KERNEL — factor into small `descF_*_subst` lemmas with explicit `show`.
* `rw [show (4:V) = 0+1+1+1+1]` also rewrites the `4` inside `^#4`; `rw [revalue_const]` rewrites EVERY
  `pConst 1` at once; `rw [cast_pConst, cast_pConst, cast_pConst]` fails on the third (the first
  instantiates `a`).
* `nth_adjoin_one/two` SHIFT (`(x ∷ v).[1] = v.[0]`) — finish with `simp only [nth_adjoin_zero, …]`.
* `LogicalConnective.HomClass.map_and` fires on `Semiformula.Eval` — unfold the family defs and
  `simp only`, do not chain `rw [map_and, map_and]`.
* `Template.lMap_swap_canonicalMeta` already exists with the OTHER normal form — a same-named local lemma is
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

## 4. `EvalGraph`, `substCode`, `closedP`

* `EvalGraph.mono_le (by omega)` needs the SOURCE fuel explicit (`(n := 0+1+1)`, `const_play 3 _ _ _`).
* `closedP` is FALSE on DBot/EBot/TFT/OBot (pronouns inside `.sim`), so `fragF` of a closed atom over
  them fails — state τ on `template (.plays p q a)` with `fragP` only (`lMap_swap_template_plays`); `rfl` does
  not reduce `closedP` on concrete programs (mutual recursion) — `simp [closedP, …]`.
* `Formula` is ambiguous with Foundation's: `PD.Formula`. `simp` never rewrites the instance-implicit
  structure of `Semiformula.Eval` — `rw [stdReadingNat_lMap_emb]`.
* `set t := …`/`set s := Nat.size k` AFTER the facts that mention them (`lenBoxNat_inst_size`,
  `lenBoxNat_le_binNumeralMeta`, `hE.nec`) or `omega` sees two atoms; `set` does not fold into later facts.
* `AgentConverse.eval_iff_evalGraph` quantifies `GuardAgree` over ALL formulas — it cannot be
  discharged per cell; the search-free/lockstep induction (`Cells/SearchFree`) is the template.
* `k̂`/`lit` are not identifiers; uniform existential constants are pure terms; pin `(k := 0)` on
  `qqTwo_semiterm.isUTerm`.

## 4b. The tau constructors on codes (Phase 2, 2026-09-30)

* An UNTAGGED list cons (`ppair x rest + 1`) collides with the program shapes — `pCons 3 p = pBot p`,
  `[const D]` would be `pBot 0` — and every fixpoint that descends into a member list (`revalue`,
  `codeTerm`) would have two clauses for one code. The cons is the tagged shape `pCons x rest = ppair 10
  (ppair x rest) + 1`; `pNil = 0` is not a shape and falls to the catch-all clauses.
* `IsShape` has eleven disjuncts: every `rcases hx with ⟨a, rfl⟩ | rfl | … ` over it needs eleven
  alternatives (`⟨v, θ, p, q, rfl⟩ | ⟨d, i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩` after `search`), and the `intro
  h₀ _ … h` counts in the `_iff` inversion lemmas grow to twelve. Use the introductions `IsShape.const … cons`
  rather than hand-built `Or.inr` chains.
* `pair_ext_iff` on a NESTED pair (`⟪⟪d, i⟫, m⟫`) gives a nested conjunction: the `rintro` pattern is
  `⟨⟨rfl, rfl⟩, rfl⟩`, not `⟨rfl, rfl, rfl⟩`. `zero_ne_add_one a : 0 ≠ a + 1` (not `a + 1 ≠ 0`).
* A Π₂ predicate cannot drive `pi1_order_induction`: state the existence of a lookup with a BOUND
  (`∀ i, ∃ m ≤ d, ListGetGraph d i m`), which is Π₁.
* Two `Sub ℕ` instances: a V-generic lemma mentioning `θ - w` instantiated at ℕ carries PeanoMinus's
  scoped instance, while `θ - w` written at ℕ elaborates to `instSubNat`; bridge with `pm_sub_eq_nat_sub`
  (`Eval/TauCheck.lean`), stated with the explicit instance `⟨FFL.FirstOrder.Arithmetic.sub⟩`.
* A ten-disjunct blueprint exceeds the default heartbeats in the `defined` proof of a `Fixpoint.Construction`
  (`set_option maxHeartbeats 6400000 in` on `EvalFix.construction`; it then builds in ~10 s).
* `lake env lean File.lean` compiles the file against the EXISTING oleans of its imports — it does not
  rebuild them. After editing `Agents/Prog.lean`, check a downstream file with the targeted
  `lake build --try-cache ArithS.<Module>` (one lake process at a time), not with `lake env lean`.
* The pronoun reading of `.selfIdx j` (member slots `#7+3j..`) landed 2026-10-01 as a SECOND translation
  `template13` (thirteen variables, stored by `pSearch`) beside the six-variable `template`, NOT by widening
  `template` in place: twenty files state facts about `template`/`sentenceAt`, and a member's guard genuinely has
  no six-variable reading. The price is the bridge `templateCode_eq_quote_template : noSelfIdxF φ → templateCode φ
  = ⌜template φ⌝` — every lemma that used `templateCode φ = ⌜template φ⌝` by DEFEQ (`unfold templateCode`) now
  needs it, and the universally stated `isSemiformula_templateCode`/`quote_sentenceAt` (and their generic
  consumers: `hingeB`, `search_else/then`, `found_of_tact`, `models_sentenceAt_of_lenBox`, `snd_else_of_false`,
  `templateCode_ne_of_*`, FitBox's `HasBox` chain) carry a trailing `(hφ : noSelfIdxF φ = true := by
  noSelfIdx_tac)` — an autoParam, so concrete call sites are unchanged. What the autoParam does NOT survive: a
  bare `rw [← quote_sentenceAt]` whose formula is fixed only by unification ("could not synthesize default value
  … must not contain free variables") — pass `me opp φ rfl` explicitly. `progCode_subst`/`templateCode_subst`
  need `noSelfIdxP me`/`noSelfIdxP opp` as PLAIN hypotheses (a player `.bot (.selfIdx j)` is read as a pronoun
  after substitution, so the equation is false without them; `noSelfIdxP_of_modestP` at the `Inv` call sites).
* `noSelfIdxF (.diag _ _) = true` (the body is frozen, `fragF` says the same), so "`noSelfIdx` is a syntactic
  fixpoint of `sysClose`" is FALSE; the member equation needs only the CODE-level fixpoint
  `progCode_sysClose_of_noSelfIdxP`/`template13_sysClose_of_noSelfIdxF` (a frozen `.diag` body is `⊥` either way).
* `ext x` on a goal `ω₁ ▹ A = ω₂ ▹ A` after `congr 1` picks the hom extensionality on `Rewriting.app` — ONE goal
  over formulas, not `Rew.ext`'s bvar/fvar pair — so `simp [Rew.comp_app]` "makes no progress". State the
  rewriter equality as a `have hc : ω₁ = ω₂ := by ext x …` first (`comp_subst_eq`'s pattern) and `rw [hc]`.
* `Fin.castLE (by norm_num) i` inside a bigger term leaves `?n ≤ ?m` for `norm_num` before unification: name the
  proof (`have h613 : (6 : ℕ) ≤ 13 := by norm_num`) and pass it. `idVec6_semitermVec (n := 13) (hn : 6 ≤ n)` at
  ℕ wants PeanoMinus's `≤`: `le_def.mpr (Or.inr hlt)` with `hlt : (6 : ℕ) < 13` typed BEFORE the call (§1).
* `simp only [quote_emb_cl, ← Semiterm.empty_quote_def, quote_canonicalMeta]` in ONE call rewrites
  `⌜Rew.emb (cl t)⌝` to `⌜cl t⌝` (a `ClosedSemiterm 13` quote) before `quote_emb_cl` can strip the cast — stage
  the three rewrites in separate `simp only` calls.
* `lMap emb`/`Rew.castLE` commute with `‘a + b’`, `‘a * b’`, `‘1’` only after unfolding to `func`
  (`Semiterm.Operator.operator`, `Add.term_eq`, `Rew.func`, `Semiterm.lMap_func`; `‘1’` is `numeral L 1`, go through
  `numeral_one` and `One.term_eq`; finish with `funext i; fin_cases i <;> simp`) — `lMap_emb_add/mul/one`,
  `cl_add/mul/one` in `Agents/Code.lean`; `succTT_eq`/`ppairTermMeta_eq` are the closed twins by `rfl`.
* A `match` on `PD.Prog` with nat-literal patterns (`.selfIdx 0`, `.bot (.selfIdx 1)`) reduces by `rfl` on
  constructor-headed arguments and on `1 - 0`, but NOT on `1 - i` for a variable `i`: state member facts for
  `i ≤ 1` and `rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl <;> rfl`.

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
* The generated tables are PRUNED at generation time (`scripts/prune.py`, lists in `scripts/pruned/`, the
  dead set of `ARITH_DEAD_CODE_AUDIT.md`). A row missing from a table is not a generator bug: check the
  list first. Consumers (`gen_cert`, `gen_frag1`, `gen_frag2`, `gen_prologue`, `gen_indrec`) read the
  producers' `.lean` files as TEXT to copy `inst_<row>` statements, so regenerate producers
  (`gen_frag`, `gen_rowinst`) BEFORE consumers; a pruned producer row keeps its table entry (indices are
  append-only) and drops only the consumer's applicability lemma, with an assertion that it is pruned too.
* `ConstantInfo.value?` returns `none` for THEOREMS unless `(allowOpaque := true)` — a reachability
  script that forgets it sees only definition bodies and reports most of the library dead (the first
  audit run: 57 %, all false). Cross-check any "dead" verdict textually before believing it.
