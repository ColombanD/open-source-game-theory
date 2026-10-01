import ArithS.Agents.Template
import ArithS.Agents.CodeTermAbs
import ArithS.Agents.SubstTemplate
import ArithS.Eval.SimTest
import PrisonersDilemma.Base.Transpose
import PrisonersDilemma.Bots.DupocBot

/-!
# ArithS.Code — the code translation of the engine's programs and formulas (roadmap M3, step (c))

`progCode : PD.Prog → ℕ` sends an engine program to its HFS pair-code (`ArithS.Prog`), and
`template : PD.Formula → Semisentence LAct 6` sends an engine formula to a SIX-VARIABLE
TEMPLATE over `LAct` — the me-triple `x₁ u₁ w₁` in `#0 #1 #2`, the opp-triple `x₂ u₂ w₂`
in `#3 #4 #5` (`ArithS.Guard`): the placeholders `.self`/`.opp` of the formula are read as
"the program described by the me- or opp-triple", every other program as the CANONICAL
DESCRIPTION of its own code (`canonicalMeta`/`revalueUMeta`/`revalueWMeta` of `ArithS.Template`, binary numerals —
no unary numeral of a code appears anywhere). `templateCode φ := ⌜template φ⌝` is the template code
stored by `pSearch`; the two are mutually recursive exactly as `Prog`/`Formula` are.

* `.plays p q a ↦ ∃ x y n, D_p(x) ∧ D_q(y) ∧ EvalGraph n x y x c_a` — the engine's
  `play fuel p q = eval fuel p q p` (`Dynamics.play`); a description `D_p(x)` is
  `∃ d, d = T_p ∧ x = revalue U_p W_p d` (`descF`), with `(T, U, W)` the frame variables
  for a placeholder and the closed description terms of `progCode p` otherwise;
* `.impl`/`.neg` are `🡒`/`∼`; `.eq p q ↦ ∃ x y, D_p(x) ∧ D̂_q(y) ∧ x = y` with the frozen
  literal `q` always described by its code;
* `.box k ψ ↦ ∃ me opp, (me, opp reconstructed from the triples) ∧ ∃ g, guardCodeGraph g
  ⌜template ψ⌝ me opp ∧ LenBox TAct k g` — "the instance of `ψ` at the current players
  has a `TAct`-proof of length `≤ k`" (the constant `⌜template ψ⌝` is a binary numeral);
* `.diag ↦ ⊥`: the engine's `.diag` is a meta-level fixpoint sentence with no bounded
  reading here (T2-CORE reads it as Foundation's `fixedpoint`, budget erased) — recorded by
  the side condition `noDiag`; the tau constructors have REAL codes since 2026-09-30 (Phase 2 of
  `SPRIME_SOURCE_OF_TRUTH.md`): `.tvote v θ p q ↦ pTvote (voteListCode v) θ …`, `.sys defs i ↦ pSys
  (progListCode defs) i`, `.selfIdx j ↦ pSelfIdx j`, with the list codes `progListCode`/`voteListCode`
  (`pNil`/`pCons`, an entry `(w, I)` being `ppair w (progCode I)`). The side condition `noTauP` and the
  fragment `fragP` still EXCLUDE them: the substitution and τ equations below are proved on the
  search-bot fragment only. **The pronoun reading (2026-10-01, the last item of §2.5 of the phase note):** the translation
  stored by `pSearch` is the THIRTEEN-variable `template13 φ` (`templateCode φ := ⌜template13 φ⌝`): the frame
  `#0..#5`, the budget slot `#6`, and the two member triples `#7..#9`, `#10..#12` (`descriptionsSys`). Its
  `progAux13` reads the pronoun `.selfIdx j` (`j ∈ {0, 1}`) from member `j`'s triple and `.bot (.selfIdx j)` as
  that triple with `pBotTerm` on the code term; deeper nestings and `j ≥ 2` (never emitted) keep the closed
  description of the dangling code. The six-variable `template` is kept beside it (the reading every `Cells/`
  file uses) and the two agree on the `noSelfIdx` fragment — `templateCode_eq_quote_template : noSelfIdxF φ →
  templateCode φ = ⌜template φ⌝`, by `template13_eq_castLE` (index for index) and `quote_castLE₆` (codes do not
  see the arity). The member-slot equation `sysCloseTemplate d (templateCode φ) = templateCode (φ.sysClose defs)`
  and the closer equation on compiled members are in `ArithS.Agents.SysTemplate`.

## The code equations (`progCode_subst`, `templateCode_subst`)

`progCode (p.subst me opp) = substCode (progCode me) (progCode opp) (progCode p)` and
`templateCode (ψ.subst me opp) = substTemplate (progCode me) (progCode opp) (templateCode ψ)` — proved on the
SEARCH-BOT FRAGMENT `fragP`/`fragF`: the atoms `.plays P Q a` / `.eq P Q` have `P, Q` a
placeholder or a CLOSED program (`closedP`: no placeholder at a `subst`-visible position), no
`.box` occurs inside a template, no tau constructor, and the players `me`, `opp` are not bare
placeholders. The heart is the meta equation `template_subst`: `template (ψ.subst me opp) = template ψ ⇜
(the closed description terms of `progCode me`, `progCode opp`)`, which holds LITERALLY because
after substitution the frame variables are unused and every description has the uniform
shape `descF`.

WHY `.box` IS EXCLUDED (an honest boundary, not a gap in the proof): the translated box
carries the CODE of its body as a numeral constant, and codes are not compositional under
substitution — `template (.box k (ψ.subst me opp))` mentions `⌜template (ψ.subst me opp)⌝` while
`template (.box k ψ) ⇜ desc` mentions `⌜template ψ⌝` and the descriptions: two sentences that are
PA-provably equivalent (both say that the same instantiated sentence is provable) but not
identical, and length-bounded provability is not invariant under provable equivalence. This
is the same phenomenon as `□A(x)` vs `Prov(sub(⌜A⌝, x))` in provability logic. The zoo's
templates are box-free except LegibleBot/OptimBot (their two-budget box guards), which are
outside the fragment.

## τ (`transposeCode_progCode`, `revalueTemplate_templateCode`)

On the same fragment the code-level transposition of `ArithS.Prog` is the code of the
engine's `Prog.transpose`/`Formula.transpose` (`Base/Transpose`): `lMap swap (template φ) =
template φ.transpose` (`lMap_swap_template`), then `revalueTemplate_quote_sentence`. The box is
excluded here for the same reason (its code constant is not re-valued by `swap`).

**Reading guide.** Definition: `actCode`, `progCode`, `template13` and `template` (§The translation) — the bridge from the engine's `Prog`/`Formula` to codes and templates; `sentenceAt` is the closed guard sentence of a pair. Facts: the description lemma, the substitution equation (`progCode_subst`), τ, and the sanity checks on the engine's `DupocBot`. §The Σ₁ graphs over `LAct` and §The description shape are plumbing for the translation — skip on first reading. At ℕ: `progCode_subst` (`ArithS.Readings`).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

/-! ### Closed terms in any bound-variable context -/

/-- A closed term, cast into a context with `n` bound variables. Every rewriter fixes it
(`rew_cl`). -/
noncomputable def cl {n : ℕ} (t : ClosedSemiterm LAct 0) : Semiterm LAct Empty n :=
  Rew.castLE (Nat.zero_le n) t

lemma rew_cl {n m : ℕ} (ω : Rew LAct Empty n Empty m) (t : ClosedSemiterm LAct 0) :
    ω (cl t) = cl t := by
  induction t with
  | bvar x => exact x.elim0
  | fvar x => exact x.elim
  | func f v ih =>
    show ω (Rew.castLE _ (Semiterm.func f v)) = Rew.castLE _ (Semiterm.func f v)
    rw [Rew.func, Rew.func]
    congr 1
    funext i
    exact ih i

lemma lMap_swap_cl {n : ℕ} (t : ClosedSemiterm LAct 0) :
    Semiterm.lMap swap (cl t : Semiterm LAct Empty n) = cl (Semiterm.lMap swap t) := by
  unfold cl
  change Semiterm.lMap swap (Rew.map (Fin.castLE (Nat.zero_le n)) id t) =
    Rew.map (Fin.castLE (Nat.zero_le n)) id (Semiterm.lMap swap t)
  rw [Semiterm.lMap_map]

lemma quote_emb_cl {n : ℕ} (t : ClosedSemiterm LAct 0) :
    (⌜(Rew.emb (cl t) : SyntacticSemiterm LAct n)⌝ : ℕ) = ⌜(Rew.emb t : SyntacticSemiterm LAct 0)⌝ := by
  induction t with
  | bvar x => exact x.elim0
  | fvar x => exact x.elim
  | func f v ih =>
    show (⌜(Rew.emb (Rew.castLE _ (Semiterm.func f v)) : SyntacticSemiterm LAct n)⌝ : ℕ) = _
    rw [Rew.func, Rew.func, Rew.func, Semiterm.quote_func, Semiterm.quote_func]
    congr 1
    unfold SemitermVec.val
    exact matrixToVec_congr (fun i ↦ ih i)

lemma termLenMeta_emb_cl {n : ℕ} (t : ClosedSemiterm LAct 0) :
    termLenMeta (Rew.emb (cl t) : SyntacticSemiterm LAct n) = termLenMeta (Rew.emb t : SyntacticSemiterm LAct 0) := by
  induction t with
  | bvar x => exact x.elim0
  | fvar x => exact x.elim
  | func f v ih =>
    show termLenMeta (Rew.emb (Rew.castLE _ (Semiterm.func f v)) : SyntacticSemiterm LAct n) = _
    rw [Rew.func, Rew.func, Rew.func, termLenMeta_func, termLenMeta_func]
    congr 1
    exact Finset.sum_congr rfl (fun i _ ↦ ih i)

lemma comp_subst_eq {n m k : ℕ} (ω : Rew LAct Empty m Empty k) (v : Fin n → Semiterm LAct Empty m) :
    ω.comp (Rew.subst v) = Rew.subst (fun i ↦ ω (v i)) := by
  ext x
  · simp [Rew.comp_app]
  · exact x.elim

/-- The binary numeral of a code, as an `LAct`-term. -/
noncomputable def numTB (c : ℕ) : ClosedSemiterm LAct 0 := Semiterm.lMap emb (binNumeralMeta c)

/-! ### The Σ₁ graphs over `LAct` -/

/-- `#0 = revalue #1 #2 #3` (`revalueDef`, argument order `y u w x`). -/
noncomputable def relDesc : Semisentence LAct 4 := Semiformula.lMap emb revalueDef.val
/-- `EvalGraph #0 #1 #2 #3 #4` (`n me opp p a`). -/
noncomputable def evalG : Semisentence LAct 5 := Semiformula.lMap emb evalGraphDef.val
/-- `#0 = guardCode #1 #2 #3` (`y g me opp`). -/
noncomputable def guardCodeG : Semisentence LAct 4 := Semiformula.lMap emb guardCodeGraph.val
/-- `LenBox TAct #0 #1` (`k φ`), the Σ₁ side. -/
noncomputable def lenProvG : Semisentence LAct 2 := Semiformula.lMap emb (lenBox TAct).sigma.val

lemma lMap_swap_relDesc : Semiformula.lMap swap relDesc = relDesc := lMap_swap_emb _
lemma lMap_swap_evalG : Semiformula.lMap swap evalG = evalG := lMap_swap_emb _
lemma lMap_swap_guardCodeG : Semiformula.lMap swap guardCodeG = guardCodeG := lMap_swap_emb _
lemma lMap_swap_lenProvG : Semiformula.lMap swap lenProvG = lenProvG := lMap_swap_emb _

/-! ### The description shape -/

/-- `∃ d, d = T ∧ X = revalue U W d`: "`X` is the program with canonical numeral `T` and
re-valuation terms `U`, `W`". One shape for placeholders and for closed programs — that
uniformity is what makes substitution literal. -/
noncomputable def descF {n : ℕ} (X T U W : Semiterm LAct Empty (n + 1)) : Semisentence LAct n :=
  ∃¹ (Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#0, T] ⋏ (relDesc ⇜ ![X, U, W, #0]))

lemma rew_descF {n m : ℕ} (ω : Rew LAct Empty n Empty m) (X T U W : Semiterm LAct Empty (n + 1)) :
    ω ▹ descF X T U W = descF (ω.q X) (ω.q T) (ω.q U) (ω.q W) := by
  unfold descF
  rw [Rewriting.app_exs, LogicalConnective.HomClass.map_and, Semiformula.rew_rel]
  unfold Rewriting.subst
  rw [← TransitiveRewriting.comp_app, comp_subst_eq]
  have h1 : (fun i ↦ ω.q (![#0, T] i)) = ![#0, ω.q T] := by funext i; fin_cases i <;> simp
  have h2 : (fun i ↦ ω.q (![X, U, W, #0] i)) = ![ω.q X, ω.q U, ω.q W, #0] := by
    funext i; fin_cases i <;> simp
  rw [h1, h2]

lemma lMap_swap_descF {n : ℕ} (X T U W : Semiterm LAct Empty (n + 1)) :
    Semiformula.lMap swap (descF X T U W) =
    descF (Semiterm.lMap swap X) (Semiterm.lMap swap T) (Semiterm.lMap swap U) (Semiterm.lMap swap W) := by
  unfold descF
  rw [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_rel, Semiformula.lMap_subst,
    lMap_swap_relDesc]
  have h1 : (Semiterm.lMap swap ∘ ![#0, T]) = ![#0, Semiterm.lMap swap T] := by
    funext i; fin_cases i <;> simp
  have h2 : (Semiterm.lMap swap ∘ ![X, U, W, #0]) =
      ![Semiterm.lMap swap X, Semiterm.lMap swap U, Semiterm.lMap swap W, #0] := by
    funext i; fin_cases i <;> simp
  rw [h1, h2]
  rfl

/-- The description of the program with code `c` (a closed sentence in `#0`, in the frame
context `#1..#6`). -/
noncomputable def closedDesc (c : ℕ) : Semisentence LAct 7 :=
  descF #1 (cl (canonicalMeta c)) (cl (revalueUMeta c)) (cl (revalueWMeta c))

/-- The description of `p`, whose code is `c`: the me-triple for `.self`, the opp-triple for
`.opp`, the canonical description of `c` otherwise. -/
noncomputable def progAux (p : PD.Prog) (c : ℕ) : Semisentence LAct 7 :=
  if p = .self then descF #1 #2 #3 #4 else if p = .opp then descF #1 #5 #6 #7 else closedDesc c

/-- The action code: `C ↦ 0`, `D ↦ 1`. -/
def actCode : PD.Action → ℕ
  | .C => 0
  | .D => 1

lemma actCode_swap (a : PD.Action) : actCode a.swap = swapAction (actCode a) := by
  cases a <;> simp [actCode, PD.Action.swap, revalueAction]

lemma actCode_le_one (a : PD.Action) : actCode a ≤ 1 := by cases a <;> simp [actCode]

/-! ### The pronoun term `pBotTerm`, and the thirteen-variable descriptions

A system member's guard names its partner through the pronoun `.bot (.selfIdx j)` (`Tau/Spec.lean`,
`sysGo`: the ONLY pronoun shapes a compiled member carries are `.selfIdx j` under one `.bot`, `j ∈ {0, 1}`).
The thirteen-variable template reads member `j` from the slots `#7+3j #8+3j #9+3j` (`descriptionsSys`,
`ArithS.Agents.Guard`) exactly as `.self`/`.opp` are read from `#0..#5`, and reads `.bot (.selfIdx j)` as the
triple `(pBotTerm x_j, u_j, w_j)`: `pBot` commutes with `revalue` (`revalue_bot`), with `canonical`
(`canonical_pBot`) and fixes the re-valuation terms (`revalueU_pBot`/`revalueW_pBot`), so the description of
`pBot x` is the description of `x` with the code term wrapped by the TERM `pBotTerm t = (3̂ + t)·(3̂ + t) + t + 1`
(the polynomial pairing of `pBot`, `codeTerm_bot`, written as a term in the slot variable — the move of
`TBD(#6)` in `Cells/JustSlot.lean`). -/

/-- The term of `pBot` on term codes: `ppairTerm 3̂ t + 1` as a term in `t`. -/
noncomputable def pBotTerm {n : ℕ} (t : Semiterm LAct Empty n) : Semiterm LAct Empty n :=
  ‘(!!(cl (numTB 3)) + !!t) * (!!(cl (numTB 3)) + !!t) + !!t + 1’

lemma rew_pBotTerm {n m : ℕ} (ω : Rew LAct Empty n Empty m) (t : Semiterm LAct Empty n) :
    ω (pBotTerm t) = pBotTerm (ω t) := by
  unfold pBotTerm
  simp [rew_cl]

lemma lMap_emb_add {n : ℕ} (s t : Semiterm ℒₒᵣ Empty n) :
    Semiterm.lMap emb (‘!!s + !!t’ : Semiterm ℒₒᵣ Empty n) =
      (‘!!(Semiterm.lMap emb s) + !!(Semiterm.lMap emb t)’ : Semiterm LAct Empty n) := by
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func, Semiterm.lMap_func]
  congr 1
  funext i; fin_cases i <;> simp

lemma lMap_emb_mul {n : ℕ} (s t : Semiterm ℒₒᵣ Empty n) :
    Semiterm.lMap emb (‘!!s * !!t’ : Semiterm ℒₒᵣ Empty n) =
      (‘!!(Semiterm.lMap emb s) * !!(Semiterm.lMap emb t)’ : Semiterm LAct Empty n) := by
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Mul.term_eq, Rew.func, Semiterm.lMap_func]
  congr 1
  funext i; fin_cases i <;> simp

lemma lMap_emb_one {n : ℕ} : Semiterm.lMap emb (‘1’ : Semiterm ℒₒᵣ Empty n) = (‘1’ : Semiterm LAct Empty n) := by
  show Semiterm.lMap emb (Semiterm.Operator.const (Semiterm.Operator.numeral ℒₒᵣ 1)) =
    Semiterm.Operator.const (Semiterm.Operator.numeral LAct 1)
  rw [Semiterm.Operator.numeral_one, Semiterm.Operator.numeral_one]
  simp only [Semiterm.Operator.const, Semiterm.Operator.operator, Semiterm.Operator.One.term_eq, Rew.func,
    Semiterm.lMap_func]
  congr 1
  funext i; exact i.elim0

lemma cl_add {n : ℕ} (s t : ClosedSemiterm LAct 0) :
    (cl (‘!!s + !!t’ : ClosedSemiterm LAct 0) : Semiterm LAct Empty n) = ‘!!(cl s) + !!(cl t)’ := by
  unfold cl; simp
lemma cl_mul {n : ℕ} (s t : ClosedSemiterm LAct 0) :
    (cl (‘!!s * !!t’ : ClosedSemiterm LAct 0) : Semiterm LAct Empty n) = ‘!!(cl s) * !!(cl t)’ := by
  unfold cl; simp
lemma cl_one {n : ℕ} : (cl (‘1’ : ClosedSemiterm LAct 0) : Semiterm LAct Empty n) = ‘1’ := by
  unfold cl; simp

/-- `pBotTerm` on a closed meta term is the meta term of `pBot` (`codeTermMeta_bot`'s shape). -/
lemma pBotTerm_cl {n : ℕ} (s : ClosedSemiterm ℒₒᵣ 0) :
    (pBotTerm (cl (Semiterm.lMap emb s)) : Semiterm LAct Empty n) =
      cl (Semiterm.lMap emb (succTT (ppairTermMeta (binNumeralMeta 3) s))) := by
  rw [succTT_eq, ppairTermMeta_eq, lMap_emb_add, lMap_emb_add, lMap_emb_mul, lMap_emb_add, lMap_emb_one,
    cl_add, cl_add, cl_mul, cl_add, cl_one]
  rfl

lemma canonicalMeta_pBot (c : ℕ) :
    canonicalMeta (pBot c) = Semiterm.lMap emb (succTT (ppairTermMeta (binNumeralMeta 3) (codeTermMeta (canonical c)))) := by
  unfold canonicalMeta
  rw [canonical_pBot, codeTermMeta_bot]

/-- **The description of `pBot c` is `pBotTerm` of the description of `c`.** -/
lemma pBotTerm_canonicalMeta {n : ℕ} (c : ℕ) :
    (pBotTerm (cl (canonicalMeta c)) : Semiterm LAct Empty n) = cl (canonicalMeta (pBot c)) := by
  rw [canonicalMeta_pBot]
  exact pBotTerm_cl _

lemma revalueUMeta_pBot (c : ℕ) : revalueUMeta (pBot c) = revalueUMeta c := by
  unfold revalueUMeta
  rw [transposeCode_pBot]
  simp only [pBot_lt_pBot_iff]

lemma revalueWMeta_pBot (c : ℕ) : revalueWMeta (pBot c) = revalueWMeta c := by
  unfold revalueWMeta
  rw [transposeCode_pBot]
  simp only [pBot_lt_pBot_iff]

/-- The description of the program with code `c`, in the thirteen-variable frame (`#1..#13`). -/
noncomputable def closedDesc13 (c : ℕ) : Semisentence LAct 14 :=
  descF #1 (cl (canonicalMeta c)) (cl (revalueUMeta c)) (cl (revalueWMeta c))

/-! ### Budget abstraction: the description of a closed program at the node's budget (2026-10-01)

Route (c) made generic (decision (A) of `SPRIME_SOURCE_OF_TRUTH.md` §3). A closed program named inside a
template is described by the abstracted term `codeTermMetaAbs k₀` (`ArithS.Agents.CodeTermAbs`): every
`pSearch k₀ …` budget leaf is the budget slot `#6` of the frame (`#8` in the context of `descF`, where `#0` is
the description's witness and `#1` the program variable). The evaluator fills `#6` with the node's budget
(`guardCodeB`), and the instantiation identity `canonicalSlot_numTB` says the sentence consulted is the one the
unabstracted template consulted — so the stored template of `JustBot k` (frozen snapshot `DupocBot k`) and of
every tau instance naming a budget-carrying hypothesis instance is a CONSTANT, its code a short numeral, and
`Critch's (b)` holds for it (the obstruction of `Tau/NeverFits.lean` dissolves). `canonicalSlot none` is the
verbatim description (today's coding), `canonicalSlot (some k₀)` the abstracted one; on a code without a
`pSearch k₀` node outside a system the two coincide (`canonicalSlot_of_noSearchAt`). -/

/-- The abstracted description term of the code `c` at the node budget `k₀`, with the budget variable `b`. -/
noncomputable def canonicalAbs {n : ℕ} (k₀ c : ℕ) (b : Semiterm LAct Empty n) : Semiterm LAct Empty n :=
  Rew.subst ![b] (Semiterm.lMap emb (codeTermMetaAbs k₀ (canonical c)))

/-- The description term of a closed program: verbatim (`none`) or abstracted at the node budget (`some k₀`),
the budget written as the term `b`. -/
noncomputable def canonicalSlot {n : ℕ} : Option ℕ → ℕ → Semiterm LAct Empty n → Semiterm LAct Empty n
  | none, c, _ => cl (canonicalMeta c)
  | some k₀, c, b => canonicalAbs k₀ c b

lemma canonicalSlot_none {n : ℕ} (c : ℕ) (b : Semiterm LAct Empty n) : canonicalSlot none c b = cl (canonicalMeta c) := rfl
lemma canonicalSlot_some {n : ℕ} (k₀ c : ℕ) (b : Semiterm LAct Empty n) : canonicalSlot (some k₀) c b = canonicalAbs k₀ c b := rfl

lemma rew_canonicalAbs {n m : ℕ} (ω : Rew LAct Empty n Empty m) (k₀ c : ℕ) (b : Semiterm LAct Empty n) :
    ω (canonicalAbs k₀ c b) = canonicalAbs k₀ c (ω b) := by
  unfold canonicalAbs
  have e : (fun i ↦ ω (![b] i)) = ![ω b] := by funext i; fin_cases i; rfl
  rw [← Rew.comp_app, comp_subst_eq, e]

lemma rew_canonicalSlot {n m : ℕ} (ω : Rew LAct Empty n Empty m) (k₀ : Option ℕ) (c : ℕ) (b : Semiterm LAct Empty n) :
    ω (canonicalSlot k₀ c b) = canonicalSlot k₀ c (ω b) := by
  cases k₀ with
  | none => exact rew_cl ω _
  | some k => exact rew_canonicalAbs ω k c b

lemma lMap_swap_canonicalAbs {n : ℕ} (k₀ c : ℕ) (b : Semiterm LAct Empty n) :
    Semiterm.lMap swap (canonicalAbs k₀ c b) = canonicalAbs k₀ (transposeCode c) (Semiterm.lMap swap b) := by
  unfold canonicalAbs Rew.subst
  rw [Semiterm.lMap_bind, term_lMap_swap_emb, canonical_transposeCode]
  have e1 : Semiterm.lMap swap ∘ ![b] = ![Semiterm.lMap swap b] := by funext i; fin_cases i; rfl
  have e2 : Semiterm.lMap swap ∘ (Semiterm.fvar : Empty → Semiterm LAct Empty n) = Semiterm.fvar := by
    funext x; exact x.elim
  rw [e1, e2]

lemma lMap_swap_canonicalSlot {n : ℕ} (k₀ : Option ℕ) (c : ℕ) (b : Semiterm LAct Empty n) :
    Semiterm.lMap swap (canonicalSlot k₀ c b) = canonicalSlot k₀ (transposeCode c) (Semiterm.lMap swap b) := by
  cases k₀ with
  | none => rw [canonicalSlot_none, canonicalSlot_none, lMap_swap_cl, lMap_swap_canonicalMeta]
  | some k => exact lMap_swap_canonicalAbs k c b

/-- A closed term's shift, with anything substituted for its one variable: the closed term, cast. -/
lemma subst_bShift_cl {n : ℕ} (b : Semiterm LAct Empty n) :
    ∀ t : ClosedSemiterm LAct 0, Rew.subst ![b] (Rew.bShift t) = cl t
  | #x => x.elim0
  | &x => x.elim
  | .func f v => by
    show Rew.subst ![b] (Rew.bShift (Semiterm.func f v)) = Rew.castLE _ (Semiterm.func f v)
    rw [Rew.func, Rew.func, Rew.func]
    congr 1; funext i; exact subst_bShift_cl b (v i)

/-- A one-variable substitution by a cast closed term is the cast of the substitution. -/
lemma subst_cl_eq {n : ℕ} (u : ClosedSemiterm LAct 0) (X : Semiterm LAct Empty 1) :
    (cl (Rew.subst ![u] X) : Semiterm LAct Empty n) = Rew.subst ![cl u] X := by
  unfold cl
  have e : (fun i ↦ (Rew.castLE (Nat.zero_le n) : Rew LAct Empty 0 Empty n) (![u] i)) =
      ![(Rew.castLE (Nat.zero_le n) : Rew LAct Empty 0 Empty n) u] := by funext i; fin_cases i; rfl
  rw [← Rew.comp_app, comp_subst_eq, e]

/-- **The instantiation identity**: the abstracted description with the node's own budget in the slot IS the
verbatim description. -/
lemma canonicalAbs_numTB {n : ℕ} (k c : ℕ) :
    (canonicalAbs k c (cl (numTB k)) : Semiterm LAct Empty n) = cl (canonicalMeta c) := by
  unfold canonicalAbs
  have h' : Rew.subst ![numTB k] (Semiterm.lMap emb (codeTermMetaAbs k (canonical c))) = canonicalMeta c := by
    rw [show numTB k = Semiterm.lMap emb (binNumeralMeta k) from rfl, ← term_lMap_subst₁, subst_codeTermMetaAbs]; rfl
  rw [← h']
  exact (subst_cl_eq _ _).symm

lemma canonicalSlot_numTB {n : ℕ} (k c : ℕ) :
    (canonicalSlot (some k) c (cl (numTB k)) : Semiterm LAct Empty n) = cl (canonicalMeta c) := canonicalAbs_numTB k c

/-- On a code without a `pSearch k₀` node the abstraction is the verbatim description. -/
lemma canonicalAbs_of_noSearchAt {n : ℕ} {k₀ c : ℕ} (h : NoSearchAt k₀ (canonical c)) (b : Semiterm LAct Empty n) :
    canonicalAbs k₀ c b = cl (canonicalMeta c) := by
  unfold canonicalAbs
  rw [codeTermMetaAbs_of_noSearchAt h, Semiterm.lMap_bShift, subst_bShift_cl]; rfl

lemma canonicalSlot_of_noSearchAt {n : ℕ} {k₀ c : ℕ} (h : NoSearchAt k₀ (canonical c)) (b : Semiterm LAct Empty n) :
    canonicalSlot (some k₀) c b = cl (canonicalMeta c) := canonicalAbs_of_noSearchAt h b

/-- A system is described verbatim at every node budget (`codeTermMetaAbs_sys`). -/
lemma canonicalSlot_of_sys {n : ℕ} (k₀ : Option ℕ) (D j : ℕ) (b : Semiterm LAct Empty n) :
    canonicalSlot k₀ (pSys D j) b = cl (canonicalMeta (pSys D j)) := by
  cases k₀ with
  | none => rfl
  | some k => exact canonicalSlot_of_noSearchAt (NoSearchAt.sys k D j).canonical b

/-- The description of the program with code `c` in the thirteen-variable frame, the budget slot `#6` (here
`#8`) standing for the node budget `k₀` inside the description when `k₀ = some _`. -/
noncomputable def closedDescAt (k₀ : Option ℕ) (c : ℕ) : Semisentence LAct 14 :=
  descF #1 (canonicalSlot k₀ c #8) (cl (revalueUMeta c)) (cl (revalueWMeta c))

lemma closedDescAt_none (c : ℕ) : closedDescAt none c = closedDesc13 c := rfl
lemma closedDescAt_of_noSearchAt {k₀ c : ℕ} (h : NoSearchAt k₀ (canonical c)) : closedDescAt (some k₀) c = closedDesc13 c := by
  unfold closedDescAt closedDesc13; rw [canonicalSlot_of_noSearchAt h]

/-- The four pronoun shapes `progAuxAt` reads through the member slots. -/
def pronounP : PD.Prog → Bool
  | .selfIdx 0 => true
  | .selfIdx 1 => true
  | .bot (.selfIdx 0) => true
  | .bot (.selfIdx 1) => true
  | _ => false

/-- The description of `p` (code `c`) in the thirteen-variable frame at the node budget `k₀`: the me-triple for
`.self` (`#2 #3 #4`), the opp-triple for `.opp` (`#5 #6 #7`), member `j`'s triple for the pronoun `.selfIdx j`
(`#(9+3j) #(10+3j) #(11+3j)`, the frame slots `#7+3j..` shifted by the program variable `#1`), the same
triple with `pBotTerm` on its code term for `.bot (.selfIdx j)`, and the closed description of `c` at `k₀`
otherwise. A pronoun nested deeper (never emitted by `Tau/Spec.lean`) and a member index `≥ 2` (the
roster's systems have two members) fall to the closed description of the dangling code. -/
noncomputable def progAuxAt (k₀ : Option ℕ) (p : PD.Prog) (c : ℕ) : Semisentence LAct 14 :=
  match p with
  | .self => descF #1 #2 #3 #4
  | .opp => descF #1 #5 #6 #7
  | .selfIdx 0 => descF #1 #9 #10 #11
  | .selfIdx 1 => descF #1 #12 #13 #14
  | .bot (.selfIdx 0) => descF #1 (pBotTerm #9) #10 #11
  | .bot (.selfIdx 1) => descF #1 (pBotTerm #12) #13 #14
  | _ => closedDescAt k₀ c

/-- The unabstracted description (today's coding): `progAuxAt none`. -/
noncomputable def progAux13 (p : PD.Prog) (c : ℕ) : Semisentence LAct 14 := progAuxAt none p c

lemma progAux13_def (p : PD.Prog) (c : ℕ) : progAux13 p c = progAuxAt none p c := rfl

lemma progAuxAt_self (k₀ : Option ℕ) (c : ℕ) : progAuxAt k₀ .self c = descF #1 #2 #3 #4 := rfl
lemma progAuxAt_opp (k₀ : Option ℕ) (c : ℕ) : progAuxAt k₀ .opp c = descF #1 #5 #6 #7 := rfl
lemma progAuxAt_selfIdx0 (k₀ : Option ℕ) (c : ℕ) : progAuxAt k₀ (.selfIdx 0) c = descF #1 #9 #10 #11 := rfl
lemma progAuxAt_selfIdx1 (k₀ : Option ℕ) (c : ℕ) : progAuxAt k₀ (.selfIdx 1) c = descF #1 #12 #13 #14 := rfl
lemma progAuxAt_botSelfIdx0 (k₀ : Option ℕ) (c : ℕ) : progAuxAt k₀ (.bot (.selfIdx 0)) c = descF #1 (pBotTerm #9) #10 #11 := rfl
lemma progAuxAt_botSelfIdx1 (k₀ : Option ℕ) (c : ℕ) : progAuxAt k₀ (.bot (.selfIdx 1)) c = descF #1 (pBotTerm #12) #13 #14 := rfl

lemma progAux13_self (c : ℕ) : progAux13 .self c = descF #1 #2 #3 #4 := rfl
lemma progAux13_opp (c : ℕ) : progAux13 .opp c = descF #1 #5 #6 #7 := rfl
lemma progAux13_selfIdx0 (c : ℕ) : progAux13 (.selfIdx 0) c = descF #1 #9 #10 #11 := rfl
lemma progAux13_selfIdx1 (c : ℕ) : progAux13 (.selfIdx 1) c = descF #1 #12 #13 #14 := rfl
lemma progAux13_botSelfIdx0 (c : ℕ) : progAux13 (.bot (.selfIdx 0)) c = descF #1 (pBotTerm #9) #10 #11 := rfl
lemma progAux13_botSelfIdx1 (c : ℕ) : progAux13 (.bot (.selfIdx 1)) c = descF #1 (pBotTerm #12) #13 #14 := rfl

lemma progAuxAt_of_ne (k₀ : Option ℕ) {p : PD.Prog} (h1 : p ≠ .self) (h2 : p ≠ .opp) (h3 : pronounP p = false) (c : ℕ) :
    progAuxAt k₀ p c = closedDescAt k₀ c := by
  cases p
  case self => exact absurd rfl h1
  case opp => exact absurd rfl h2
  case selfIdx j =>
    rcases j with _ | _ | j
    · simp [pronounP] at h3
    · simp [pronounP] at h3
    · rfl
  case bot q =>
    cases q
    case selfIdx j =>
      rcases j with _ | _ | j
      · simp [pronounP] at h3
      · simp [pronounP] at h3
      · rfl
    all_goals rfl
  all_goals rfl

lemma progAux13_of_ne {p : PD.Prog} (h1 : p ≠ .self) (h2 : p ≠ .opp) (h3 : pronounP p = false) (c : ℕ) :
    progAux13 p c = closedDesc13 c := progAuxAt_of_ne none h1 h2 h3 c

lemma pronounP_cases {p : PD.Prog} (h : pronounP p = true) :
    p = .selfIdx 0 ∨ p = .selfIdx 1 ∨ p = .bot (.selfIdx 0) ∨ p = .bot (.selfIdx 1) := by
  cases p
  case selfIdx j =>
    rcases j with _ | _ | j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · simp [pronounP] at h
  case bot q =>
    cases q
    case selfIdx j =>
      rcases j with _ | _ | j
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · simp [pronounP] at h
    all_goals simp [pronounP] at h
  all_goals simp [pronounP] at h

/-! ### The translation -/

mutual
  /-- The program code. -/
  noncomputable def progCode : PD.Prog → ℕ
    | .const a => pConst (actCode a)
    | .self => pSelf
    | .opp => pOpp
    | .bot p => pBot (progCode p)
    | .sim p q => pSim (progCode p) (progCode q)
    | .ite b a p q => pIte (progCode b) (actCode a) (progCode p) (progCode q)
    | .search k φ p q => pSearch k (⌜templateAt φ (some k)⌝ : ℕ) (progCode p) (progCode q)
    | .tvote v θ p q => pTvote (voteListCode v) θ (progCode p) (progCode q)
    | .sys defs i => pSys (progListCode defs) i
    | .selfIdx j => pSelfIdx j
  /-- The code of a member list: `pNil`/`pCons`. -/
  noncomputable def progListCode : PD.ProgList → ℕ
    | .nil => pNil
    | .cons p rest => pCons (progCode p) (progListCode rest)
  /-- The code of a vote list: an entry `(w, I)` is `ppair w (progCode I)`. -/
  noncomputable def voteListCode : PD.VoteList → ℕ
    | .nil => pNil
    | .cons w I rest => pCons (ppair w (progCode I)) (voteListCode rest)
  /-- The thirteen-variable template of a formula AT THE NODE BUDGET `k₀`: the six-variable template's
  clauses index for index, in the frame `#0..#12` (me-triple, opp-triple, budget slot, the two member
  triples), with the pronoun reading of `progAuxAt` and every closed program described with the budget `k₀`
  abstracted into the slot `#6` (`closedDescAt`). `none` abstracts nothing (`template13`, today's coding).
  The code constant a `.box` carries is the UNABSTRACTED template code of its body (box guards are outside
  the zoo's fragment: LegibleBot/OptimBot, `Agents/FitBox.lean`). -/
  noncomputable def templateAt : PD.Formula → Option ℕ → Semisentence LAct 13
    | .plays p q a, k₀ =>
        ∃¹ (∃¹ (∃¹ ((progAuxAt k₀ p (progCode p) ⇜ ![#2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14, #15]) ⋏
          ((progAuxAt k₀ q (progCode q) ⇜ ![#1, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14, #15]) ⋏
            (evalG ⇜ ![#0, #2, #1, #2, cl (actT (actCode a))])))))
    | .impl φ ψ, k₀ => templateAt φ k₀ 🡒 templateAt ψ k₀
    | .neg φ, k₀ => ∼ templateAt φ k₀
    | .box k ψ, k₀ =>
        ∃¹ (∃¹ ((progAuxAt k₀ .self 0 ⇜ ![#1, #2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14]) ⋏
          ((progAuxAt k₀ .opp 0 ⇜ ![#0, #2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14]) ⋏
            (∃¹ ((guardCodeG ⇜ ![#0, cl (numTB (⌜templateAt ψ none⌝ : ℕ)), #2, #1]) ⋏
              (lenProvG ⇜ ![cl (numTB k), #0]))))))
    | .eq p q, k₀ =>
        ∃¹ (∃¹ ((progAuxAt k₀ p (progCode p) ⇜ ![#1, #2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14]) ⋏
          ((closedDescAt k₀ (progCode q) ⇜ ![#0, #2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14]) ⋏
            Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#1, #0])))
    | .diag _ _, _ => ⊥
end

/-- The UNABSTRACTED thirteen-variable template: `templateAt φ none` — today's coding, kept by name and by value
(the reading every statement about `templateCode` rests on). -/
noncomputable def template13 (φ : PD.Formula) : Semisentence LAct 13 := templateAt φ none

lemma template13_def (φ : PD.Formula) : template13 φ = templateAt φ none := rfl

/-- The unabstracted template code: `⌜template13 φ⌝`. On the `noSelfIdx` fragment it is the code of the
six-variable `template` (`templateCode_eq_quote_template`); on a formula without a budget snapshot it is what
`pSearch` stores (`templateCodeAt_eq_templateCode`). -/
noncomputable def templateCode (φ : PD.Formula) : ℕ := ⌜template13 φ⌝

/-- **The stored template code**: the template of `φ` at the node budget `k`, every closed program inside it
described with the budget `k` abstracted into the slot `#6`. `progCode (.search k φ p q)` stores it. -/
noncomputable def templateCodeAt (φ : PD.Formula) (k : ℕ) : ℕ := ⌜templateAt φ (some k)⌝

/-- The six-variable template of a formula (the original translation, kept as the reading every
`Cells/` file works with). Its body is the pre-pronoun one, except that the code constant a `.box`
carries is `templateCode ψ` — the code `pSearch` stores — which is `⌜template ψ⌝` whenever `ψ` mentions
no pronoun (the bridge), i.e. on every box the zoo carries. -/
noncomputable def template : PD.Formula → Semisentence LAct 6
  | .plays p q a =>
      ∃¹ (∃¹ (∃¹ ((progAux p (progCode p) ⇜ ![#2, #3, #4, #5, #6, #7, #8]) ⋏
        ((progAux q (progCode q) ⇜ ![#1, #3, #4, #5, #6, #7, #8]) ⋏
          (evalG ⇜ ![#0, #2, #1, #2, cl (actT (actCode a))])))))
  | .impl φ ψ => template φ 🡒 template ψ
  | .neg φ => ∼ template φ
  | .box k ψ =>
      ∃¹ (∃¹ ((progAux .self 0 ⇜ ![#1, #2, #3, #4, #5, #6, #7]) ⋏
        ((progAux .opp 0 ⇜ ![#0, #2, #3, #4, #5, #6, #7]) ⋏
          (∃¹ ((guardCodeG ⇜ ![#0, cl (numTB (templateCode ψ)), #2, #1]) ⋏
            (lenProvG ⇜ ![cl (numTB k), #0]))))))
  | .eq p q =>
      ∃¹ (∃¹ ((progAux p (progCode p) ⇜ ![#1, #2, #3, #4, #5, #6, #7]) ⋏
        ((closedDesc (progCode q) ⇜ ![#0, #2, #3, #4, #5, #6, #7]) ⋏
          Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#1, #0])))
  | .diag _ _ => ⊥

/-- The description of `p` in the frame. -/
noncomputable def progGraph (p : PD.Prog) : Semisentence LAct 7 := progAux p (progCode p)

/-- The description of `p` in the thirteen-variable frame (unabstracted). -/
noncomputable def progGraph13 (p : PD.Prog) : Semisentence LAct 14 := progAux13 p (progCode p)

/-- The description of `p` in the thirteen-variable frame at the node budget `k₀`. -/
noncomputable def progGraphAt (k₀ : Option ℕ) (p : PD.Prog) : Semisentence LAct 14 := progAuxAt k₀ p (progCode p)

lemma progGraph13_def (p : PD.Prog) : progGraph13 p = progGraphAt none p := rfl

@[simp] lemma progCode_const (a) : progCode (.const a) = pConst (actCode a) := by rw [progCode]
@[simp] lemma progCode_self : progCode .self = pSelf := by rw [progCode]
@[simp] lemma progCode_opp : progCode .opp = pOpp := by rw [progCode]
@[simp] lemma progCode_bot (p) : progCode (.bot p) = pBot (progCode p) := by rw [progCode]
@[simp] lemma progCode_sim (p q) : progCode (.sim p q) = pSim (progCode p) (progCode q) := by rw [progCode]
@[simp] lemma progCode_ite (b a p q) : progCode (.ite b a p q) = pIte (progCode b) (actCode a) (progCode p) (progCode q) := by
  rw [progCode]
@[simp] lemma progCode_search (k φ p q) : progCode (.search k φ p q) = pSearch k (templateCodeAt φ k) (progCode p) (progCode q) := by
  rw [progCode]; rfl
@[simp] lemma progCode_tvote (v θ p q) :
    progCode (.tvote v θ p q) = pTvote (voteListCode v) θ (progCode p) (progCode q) := by rw [progCode]
@[simp] lemma progCode_sys (defs i) : progCode (.sys defs i) = pSys (progListCode defs) i := by rw [progCode]
@[simp] lemma progCode_selfIdx (j) : progCode (.selfIdx j) = pSelfIdx j := by rw [progCode]
@[simp] lemma progListCode_nil : progListCode .nil = pNil := by rw [progListCode]
@[simp] lemma progListCode_cons (p rest) : progListCode (.cons p rest) = pCons (progCode p) (progListCode rest) := by
  rw [progListCode]
@[simp] lemma voteListCode_nil : voteListCode .nil = pNil := by rw [voteListCode]
@[simp] lemma voteListCode_cons (w I rest) :
    voteListCode (.cons w I rest) = pCons (ppair w (progCode I)) (voteListCode rest) := by rw [voteListCode]

/-- Every program code is a shape (the tau constructors included, since 2026-09-30). -/
theorem isShape_progCode : ∀ p : PD.Prog, IsShape (progCode p)
  | .const a => by rw [progCode_const]; exact IsShape.const _
  | .self => by rw [progCode_self]; exact IsShape.self
  | .opp => by rw [progCode_opp]; exact IsShape.opp
  | .bot p => by rw [progCode_bot]; exact IsShape.bot _
  | .sim p q => by rw [progCode_sim]; exact IsShape.sim _ _
  | .ite b a p q => by rw [progCode_ite]; exact IsShape.ite _ _ _ _
  | .search k φ p q => by rw [progCode_search]; exact IsShape.search _ _ _ _
  | .tvote v θ p q => by rw [progCode_tvote]; exact IsShape.tvote _ _ _ _
  | .sys defs i => by rw [progCode_sys]; exact IsShape.sys _ _
  | .selfIdx j => by rw [progCode_selfIdx]; exact IsShape.selfIdx _

/-- No program has the code `0` (the former code of the tau constructors). -/
theorem progCode_ne_zero (p : PD.Prog) : progCode p ≠ 0 := fun h ↦
  not_isShape_zero (V := ℕ) (h ▸ isShape_progCode p)

/-- Member lookup on codes is the engine's `ProgList.get?`: found members. -/
theorem listGet_progListCode_some : ∀ (defs : PD.ProgList) (i : ℕ) (p : PD.Prog),
    defs.get? i = some p → listGet (progListCode defs) i = progCode p + 1
  | .nil, _, _, h => by simp [PD.ProgList.get?] at h
  | .cons q _, 0, p, h => by
    simp only [PD.ProgList.get?, Option.some.injEq] at h
    rw [h, progListCode_cons, listGet_cons_zero]
  | .cons _ rest, n + 1, p, h => by
    simp only [PD.ProgList.get?] at h
    rw [progListCode_cons, listGet_cons_succ, listGet_progListCode_some rest n p h]

/-- Member lookup on codes is the engine's `ProgList.get?`: out-of-range indices. -/
theorem listGet_progListCode_none : ∀ (defs : PD.ProgList) (i : ℕ),
    defs.get? i = none → listGet (progListCode defs) i = 0
  | .nil, _, _ => by rw [progListCode_nil, listGet_nil]
  | .cons _ _, 0, h => by simp [PD.ProgList.get?] at h
  | .cons _ rest, n + 1, h => by
    simp only [PD.ProgList.get?] at h
    rw [progListCode_cons, listGet_cons_succ, listGet_progListCode_none rest n h]

lemma templateAt_plays (k₀ p q a) : templateAt (.plays p q a) k₀ =
    ∃¹ (∃¹ (∃¹ ((progGraphAt k₀ p ⇜ ![#2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14, #15]) ⋏
      ((progGraphAt k₀ q ⇜ ![#1, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14, #15]) ⋏
        (evalG ⇜ ![#0, #2, #1, #2, cl (actT (actCode a))]))))) := by
  rw [templateAt]; rfl
lemma templateAt_impl (k₀ φ ψ) : templateAt (.impl φ ψ) k₀ = templateAt φ k₀ 🡒 templateAt ψ k₀ := by rw [templateAt]
lemma templateAt_neg (k₀ φ) : templateAt (.neg φ) k₀ = ∼ templateAt φ k₀ := by rw [templateAt]
lemma templateAt_box (k₀ k ψ) : templateAt (.box k ψ) k₀ =
    ∃¹ (∃¹ ((progAuxAt k₀ .self 0 ⇜ ![#1, #2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14]) ⋏
      ((progAuxAt k₀ .opp 0 ⇜ ![#0, #2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14]) ⋏
        (∃¹ ((guardCodeG ⇜ ![#0, cl (numTB (templateCode ψ)), #2, #1]) ⋏
          (lenProvG ⇜ ![cl (numTB k), #0])))))) := by
  rw [templateAt]; rfl
lemma templateAt_eq (k₀ p q) : templateAt (.eq p q) k₀ =
    ∃¹ (∃¹ ((progGraphAt k₀ p ⇜ ![#1, #2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14]) ⋏
      ((closedDescAt k₀ (progCode q) ⇜ ![#0, #2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14]) ⋏
        Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#1, #0]))) := by
  rw [templateAt]; rfl
lemma templateAt_diag (k₀ g φ) : templateAt (.diag g φ) k₀ = ⊥ := by rw [templateAt]

lemma template13_plays (p q a) : template13 (.plays p q a) =
    ∃¹ (∃¹ (∃¹ ((progGraph13 p ⇜ ![#2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14, #15]) ⋏
      ((progGraph13 q ⇜ ![#1, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14, #15]) ⋏
        (evalG ⇜ ![#0, #2, #1, #2, cl (actT (actCode a))]))))) := templateAt_plays none p q a
lemma template13_impl (φ ψ) : template13 (.impl φ ψ) = template13 φ 🡒 template13 ψ := templateAt_impl none φ ψ
lemma template13_neg (φ) : template13 (.neg φ) = ∼ template13 φ := templateAt_neg none φ
lemma template13_box (k ψ) : template13 (.box k ψ) =
    ∃¹ (∃¹ ((progAux13 .self 0 ⇜ ![#1, #2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14]) ⋏
      ((progAux13 .opp 0 ⇜ ![#0, #2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14]) ⋏
        (∃¹ ((guardCodeG ⇜ ![#0, cl (numTB (templateCode ψ)), #2, #1]) ⋏
          (lenProvG ⇜ ![cl (numTB k), #0])))))) := templateAt_box none k ψ
lemma template13_eq (p q) : template13 (.eq p q) =
    ∃¹ (∃¹ ((progGraph13 p ⇜ ![#1, #2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14]) ⋏
      ((closedDesc13 (progCode q) ⇜ ![#0, #2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14]) ⋏
        Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#1, #0]))) := templateAt_eq none p q
lemma template13_diag (g φ) : template13 (.diag g φ) = ⊥ := templateAt_diag none g φ

lemma template_plays (p q a) : template (.plays p q a) =
    ∃¹ (∃¹ (∃¹ ((progGraph p ⇜ ![#2, #3, #4, #5, #6, #7, #8]) ⋏
      ((progGraph q ⇜ ![#1, #3, #4, #5, #6, #7, #8]) ⋏
        (evalG ⇜ ![#0, #2, #1, #2, cl (actT (actCode a))]))))) := by
  rw [template]; rfl
lemma template_impl (φ ψ) : template (.impl φ ψ) = template φ 🡒 template ψ := by rw [template]
lemma template_neg (φ) : template (.neg φ) = ∼ template φ := by rw [template]
lemma template_box (k ψ) : template (.box k ψ) =
    ∃¹ (∃¹ ((progAux .self 0 ⇜ ![#1, #2, #3, #4, #5, #6, #7]) ⋏
      ((progAux .opp 0 ⇜ ![#0, #2, #3, #4, #5, #6, #7]) ⋏
        (∃¹ ((guardCodeG ⇜ ![#0, cl (numTB (templateCode ψ)), #2, #1]) ⋏
          (lenProvG ⇜ ![cl (numTB k), #0])))))) := by
  rw [template]
lemma template_eq (p q) : template (.eq p q) =
    ∃¹ (∃¹ ((progGraph p ⇜ ![#1, #2, #3, #4, #5, #6, #7]) ⋏
      ((closedDesc (progCode q) ⇜ ![#0, #2, #3, #4, #5, #6, #7]) ⋏
        Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#1, #0]))) := by
  rw [template]; rfl
lemma template_diag (g φ) : template (.diag g φ) = ⊥ := by rw [template]

/-- The template code is a thirteen-variable formula code (every formula). -/
lemma isSemiformula_templateCode13 (φ : PD.Formula) : IsSemiformula LAct 13 (templateCode φ) := by
  have := Semiformula.quote_isSemiformula (V := ℕ) (Rewriting.emb (template13 φ) : Semiproposition LAct 13)
  rw [natCast_nat] at this
  exact this

/-- The stored template code is a thirteen-variable formula code (every formula, every budget). -/
lemma isSemiformula_templateCodeAt13 (φ : PD.Formula) (k : ℕ) : IsSemiformula LAct 13 (templateCodeAt φ k) := by
  have := Semiformula.quote_isSemiformula (V := ℕ) (Rewriting.emb (templateAt φ (some k)) : Semiproposition LAct 13)
  rw [natCast_nat] at this
  exact this

/-! ### Side conditions -/

/-- No tau constructor (`.tvote`/`.sys`/`.selfIdx`). -/
def noTauP : PD.Prog → Bool
  | .const _ => true
  | .self => true
  | .opp => true
  | .bot p => noTauP p
  | .sim p q => noTauP p && noTauP q
  | .ite b _ p q => noTauP b && noTauP p && noTauP q
  | .search _ _ p q => noTauP p && noTauP q
  | .tvote _ _ _ _ => false
  | .sys _ _ => false
  | .selfIdx _ => false

theorem noTauP_subst : ∀ (p me opp : PD.Prog), noTauP p = true → noTauP me = true → noTauP opp = true →
    noTauP (p.subst me opp) = true
  | .const _, _, _, _, _, _ => rfl
  | .self, _, _, _, hme, _ => hme
  | .opp, _, _, _, _, hopp => hopp
  | .bot _, _, _, h, _, _ => h
  | .sim p q, me, opp, h, hme, hopp => by
    simp only [noTauP, Bool.and_eq_true] at h
    simp only [PD.Prog.subst, noTauP, noTauP_subst p me opp h.1 hme hopp, noTauP_subst q me opp h.2 hme hopp,
      Bool.and_self]
  | .ite b _ p q, me, opp, h, hme, hopp => by
    simp only [noTauP, Bool.and_eq_true] at h
    simp only [PD.Prog.subst, noTauP, noTauP_subst b me opp h.1.1 hme hopp, noTauP_subst p me opp h.1.2 hme hopp,
      noTauP_subst q me opp h.2 hme hopp, Bool.and_self]
  | .search _ _ p q, me, opp, h, hme, hopp => by
    simp only [noTauP, Bool.and_eq_true] at h
    simp only [PD.Prog.subst, noTauP, noTauP_subst p me opp h.1 hme hopp, noTauP_subst q me opp h.2 hme hopp,
      Bool.and_self]
  | .tvote _ _ _ _, _, _, h, _, _ => by simp [noTauP] at h
  | .sys _ _, _, _, h, _, _ => by simp [noTauP] at h
  | .selfIdx _, _, _, h, _, _ => by simp [noTauP] at h

/-- No `.diag`. -/
def noDiag : PD.Formula → Bool
  | .plays _ _ _ => true
  | .impl φ ψ => noDiag φ && noDiag ψ
  | .neg φ => noDiag φ
  | .box _ φ => noDiag φ
  | .eq _ _ => true
  | .diag _ _ => false

mutual
  /-- No placeholder at a `subst`-visible position: `subst` fixes the program (`subst_of_closedP`). -/
  def closedP : PD.Prog → Bool
    | .const _ => true
    | .self => false
    | .opp => false
    | .bot _ => true
    | .sim p q => closedP p && closedP q
    | .ite b _ p q => closedP b && closedP p && closedP q
    | .search _ φ p q => closedF φ && closedP p && closedP q
    | .tvote _ _ p q => closedP p && closedP q
    | .sys _ _ => true
    | .selfIdx _ => true
  def closedF : PD.Formula → Bool
    | .plays p q _ => closedP p && closedP q
    | .impl φ ψ => closedF φ && closedF ψ
    | .neg φ => closedF φ
    | .box _ φ => closedF φ
    | .eq p _ => closedP p
    | .diag _ _ => true
end

mutual
  theorem subst_of_closedP : ∀ (p me opp : PD.Prog), closedP p = true → p.subst me opp = p
    | .const _, _, _, _ => rfl
    | .self, _, _, h => by simp [closedP] at h
    | .opp, _, _, h => by simp [closedP] at h
    | .bot _, _, _, _ => rfl
    | .sim p q, me, opp, h => by
      simp only [closedP, Bool.and_eq_true] at h
      simp only [PD.Prog.subst, subst_of_closedP p me opp h.1, subst_of_closedP q me opp h.2]
    | .ite b _ p q, me, opp, h => by
      simp only [closedP, Bool.and_eq_true] at h
      simp only [PD.Prog.subst, subst_of_closedP b me opp h.1.1, subst_of_closedP p me opp h.1.2,
        subst_of_closedP q me opp h.2]
    | .search _ φ p q, me, opp, h => by
      simp only [closedP, Bool.and_eq_true] at h
      simp only [PD.Prog.subst, subst_of_closedF φ me opp h.1.1, subst_of_closedP p me opp h.1.2,
        subst_of_closedP q me opp h.2]
    | .tvote _ _ p q, me, opp, h => by
      simp only [closedP, Bool.and_eq_true] at h
      simp only [PD.Prog.subst, subst_of_closedP p me opp h.1, subst_of_closedP q me opp h.2]
    | .sys _ _, _, _, _ => rfl
    | .selfIdx _, _, _, _ => rfl
  theorem subst_of_closedF : ∀ (φ : PD.Formula) (me opp : PD.Prog), closedF φ = true → φ.subst me opp = φ
    | .plays p q _, me, opp, h => by
      simp only [closedF, Bool.and_eq_true] at h
      simp only [PD.Formula.subst, subst_of_closedP p me opp h.1, subst_of_closedP q me opp h.2]
    | .impl φ ψ, me, opp, h => by
      simp only [closedF, Bool.and_eq_true] at h
      simp only [PD.Formula.subst, subst_of_closedF φ me opp h.1, subst_of_closedF ψ me opp h.2]
    | .neg φ, me, opp, h => by
      simp only [closedF] at h
      simp only [PD.Formula.subst, subst_of_closedF φ me opp h]
    | .box _ φ, me, opp, h => by
      simp only [closedF] at h
      simp only [PD.Formula.subst, subst_of_closedF φ me opp h]
    | .eq p _, me, opp, h => by
      simp only [closedF] at h
      simp only [PD.Formula.subst, subst_of_closedP p me opp h]
    | .diag _ _, _, _, _ => rfl
end

/-- A program allowed inside an atom of a template: a placeholder or a closed program. -/
def atomicP (p : PD.Prog) : Bool := (p == .self) || (p == .opp) || closedP p

mutual
  /-- The search-bot fragment (programs): no tau constructor, every template in `fragF`. -/
  def fragP : PD.Prog → Bool
    | .const _ => true
    | .self => true
    | .opp => true
    | .bot p => fragP p
    | .sim p q => fragP p && fragP q
    | .ite b _ p q => fragP b && fragP p && fragP q
    | .search _ φ p q => fragF φ && fragP p && fragP q
    | .tvote _ _ _ _ => false
    | .sys _ _ => false
    | .selfIdx _ => false
  /-- The search-bot fragment (formulas): atoms over placeholders or closed fragment programs,
  `.impl`/`.neg`, no `.box`; `.diag` is harmless (frozen, translated to `⊥`). -/
  def fragF : PD.Formula → Bool
    | .plays p q _ => atomicP p && fragP p && atomicP q && fragP q
    | .impl φ ψ => fragF φ && fragF ψ
    | .neg φ => fragF φ
    | .box _ _ => false
    | .eq p q => atomicP p && fragP p && fragP q
    | .diag _ _ => true
end

/-! ### The tau-search-free fragment (Phase 2, 2026-09-30)

Programs built from every constructor BUT `.search`, hereditarily through vote entries and system
members. On it the code-level `substCode` and `sysCloseCode` are the engine's `subst` and `sysClose`
with NO side condition on the players (no template is ever instantiated), and the evaluator runs in
lockstep with the engine's `eval` at the same fuel (`ArithS.Eval.TauCheck`). -/

mutual
  /-- No `.search` node anywhere (entries and members included). -/
  def tauSearchFreeP : PD.Prog → Bool
    | .const _ => true
    | .self => true
    | .opp => true
    | .bot p => tauSearchFreeP p
    | .sim p q => tauSearchFreeP p && tauSearchFreeP q
    | .ite b _ p q => tauSearchFreeP b && tauSearchFreeP p && tauSearchFreeP q
    | .search _ _ _ _ => false
    | .tvote v _ p q => tauSearchFreeV v && tauSearchFreeP p && tauSearchFreeP q
    | .sys defs _ => tauSearchFreeL defs
    | .selfIdx _ => true
  def tauSearchFreeL : PD.ProgList → Bool
    | .nil => true
    | .cons p rest => tauSearchFreeP p && tauSearchFreeL rest
  def tauSearchFreeV : PD.VoteList → Bool
    | .nil => true
    | .cons _ I rest => tauSearchFreeP I && tauSearchFreeV rest
end

theorem tauSearchFreeP_subst : ∀ (p me opp : PD.Prog), tauSearchFreeP p = true → tauSearchFreeP me = true →
    tauSearchFreeP opp = true → tauSearchFreeP (p.subst me opp) = true
  | .const _, _, _, _, _, _ => rfl
  | .self, _, _, _, hme, _ => hme
  | .opp, _, _, _, _, hopp => hopp
  | .bot _, _, _, h, _, _ => h
  | .sim p q, me, opp, h, hme, hopp => by
    simp only [tauSearchFreeP, Bool.and_eq_true] at h
    simp only [PD.Prog.subst, tauSearchFreeP, tauSearchFreeP_subst p me opp h.1 hme hopp,
      tauSearchFreeP_subst q me opp h.2 hme hopp, Bool.and_self]
  | .ite b _ p q, me, opp, h, hme, hopp => by
    simp only [tauSearchFreeP, Bool.and_eq_true] at h
    simp only [PD.Prog.subst, tauSearchFreeP, tauSearchFreeP_subst b me opp h.1.1 hme hopp,
      tauSearchFreeP_subst p me opp h.1.2 hme hopp, tauSearchFreeP_subst q me opp h.2 hme hopp, Bool.and_self]
  | .search _ _ _ _, _, _, h, _, _ => by simp [tauSearchFreeP] at h
  | .tvote v _ p q, me, opp, h, hme, hopp => by
    simp only [tauSearchFreeP, Bool.and_eq_true] at h
    simp only [PD.Prog.subst, tauSearchFreeP, h.1.1, tauSearchFreeP_subst p me opp h.1.2 hme hopp,
      tauSearchFreeP_subst q me opp h.2 hme hopp, Bool.and_self]
  | .sys _ _, _, _, h, _, _ => h
  | .selfIdx _, _, _, _, _, _ => rfl

theorem tauSearchFreeP_sysClose : ∀ (p : PD.Prog) (defs : PD.ProgList), tauSearchFreeP p = true →
    tauSearchFreeL defs = true → tauSearchFreeP (p.sysClose defs) = true
  | .const _, _, _, _ => rfl
  | .self, _, _, _ => rfl
  | .opp, _, _, _ => rfl
  | .bot p, defs, h, hd => tauSearchFreeP_sysClose p defs h hd
  | .sim p q, defs, h, hd => by
    simp only [tauSearchFreeP, Bool.and_eq_true] at h
    simp only [PD.Prog.sysClose, tauSearchFreeP, tauSearchFreeP_sysClose p defs h.1 hd,
      tauSearchFreeP_sysClose q defs h.2 hd, Bool.and_self]
  | .ite b _ p q, defs, h, hd => by
    simp only [tauSearchFreeP, Bool.and_eq_true] at h
    simp only [PD.Prog.sysClose, tauSearchFreeP, tauSearchFreeP_sysClose b defs h.1.1 hd,
      tauSearchFreeP_sysClose p defs h.1.2 hd, tauSearchFreeP_sysClose q defs h.2 hd, Bool.and_self]
  | .search _ _ _ _, _, h, _ => by simp [tauSearchFreeP] at h
  | .tvote v _ p q, defs, h, hd => by
    simp only [tauSearchFreeP, Bool.and_eq_true] at h
    simp only [PD.Prog.sysClose, tauSearchFreeP, h.1.1, tauSearchFreeP_sysClose p defs h.1.2 hd,
      tauSearchFreeP_sysClose q defs h.2 hd, Bool.and_self]
  | .sys _ _, _, h, _ => h
  | .selfIdx _, _, _, hd => hd

theorem tauSearchFreeP_of_get? : ∀ (defs : PD.ProgList) (i : ℕ) (p : PD.Prog), tauSearchFreeL defs = true →
    defs.get? i = some p → tauSearchFreeP p = true
  | .nil, _, _, _, h => by simp [PD.ProgList.get?] at h
  | .cons q _, 0, p, hd, h => by
    simp only [PD.ProgList.get?, Option.some.injEq] at h
    simp only [tauSearchFreeL, Bool.and_eq_true] at hd
    exact h ▸ hd.1
  | .cons _ rest, n + 1, p, hd, h => by
    simp only [PD.ProgList.get?] at h
    simp only [tauSearchFreeL, Bool.and_eq_true] at hd
    exact tauSearchFreeP_of_get? rest n p hd.2 h

/-- **The substitution equation on the tau-search-free fragment**: no template is instantiated, so it
holds with NO condition on the players (compare `progCode_subst`, which needs proper players for its
templates). -/
theorem progCode_subst_tauSearchFree (me opp : PD.Prog) :
    ∀ p : PD.Prog, tauSearchFreeP p = true →
      progCode (p.subst me opp) = substCode (progCode me) (progCode opp) (progCode p)
  | .const _, _ => by simp [PD.Prog.subst]
  | .self, _ => by simp [PD.Prog.subst]
  | .opp, _ => by simp [PD.Prog.subst]
  | .bot _, _ => by simp [PD.Prog.subst]
  | .sim p q, h => by
    simp only [tauSearchFreeP, Bool.and_eq_true] at h
    simp [PD.Prog.subst, progCode_subst_tauSearchFree me opp p h.1, progCode_subst_tauSearchFree me opp q h.2]
  | .ite b _ p q, h => by
    simp only [tauSearchFreeP, Bool.and_eq_true] at h
    simp [PD.Prog.subst, progCode_subst_tauSearchFree me opp b h.1.1, progCode_subst_tauSearchFree me opp p h.1.2,
      progCode_subst_tauSearchFree me opp q h.2]
  | .search _ _ _ _, h => by simp [tauSearchFreeP] at h
  | .tvote v _ p q, h => by
    simp only [tauSearchFreeP, Bool.and_eq_true] at h
    simp [PD.Prog.subst, progCode_subst_tauSearchFree me opp p h.1.2, progCode_subst_tauSearchFree me opp q h.2]
  | .sys _ _, _ => by simp [PD.Prog.subst]
  | .selfIdx _, _ => by simp [PD.Prog.subst]

/-- **The system-closer equation on the tau-search-free fragment**: `sysCloseCode` is the engine's
`Prog.sysClose` on codes (no template to close). -/
theorem progCode_sysClose_tauSearchFree (defs : PD.ProgList) :
    ∀ p : PD.Prog, tauSearchFreeP p = true →
      progCode (p.sysClose defs) = sysCloseCode (progListCode defs) (progCode p)
  | .const _, _ => by simp [PD.Prog.sysClose]
  | .self, _ => by simp [PD.Prog.sysClose]
  | .opp, _ => by simp [PD.Prog.sysClose]
  | .bot p, h => by simp [PD.Prog.sysClose, progCode_sysClose_tauSearchFree defs p h]
  | .sim p q, h => by
    simp only [tauSearchFreeP, Bool.and_eq_true] at h
    simp [PD.Prog.sysClose, progCode_sysClose_tauSearchFree defs p h.1, progCode_sysClose_tauSearchFree defs q h.2]
  | .ite b _ p q, h => by
    simp only [tauSearchFreeP, Bool.and_eq_true] at h
    simp [PD.Prog.sysClose, progCode_sysClose_tauSearchFree defs b h.1.1, progCode_sysClose_tauSearchFree defs p h.1.2,
      progCode_sysClose_tauSearchFree defs q h.2]
  | .search _ _ _ _, h => by simp [tauSearchFreeP] at h
  | .tvote v _ p q, h => by
    simp only [tauSearchFreeP, Bool.and_eq_true] at h
    simp [PD.Prog.sysClose, progCode_sysClose_tauSearchFree defs p h.1.2, progCode_sysClose_tauSearchFree defs q h.2]
  | .sys _ _, _ => by simp [PD.Prog.sysClose]
  | .selfIdx _, _ => by simp [PD.Prog.sysClose]

/-! ### The `noSelfIdx` fragment and the bridge `templateCode φ = ⌜template φ⌝`

`noSelfIdxP`/`noSelfIdxF`: no dangling pronoun `.selfIdx` anywhere (a `.sys` is a binder — its members'
pronouns are its own). True of every base bot and of every non-member compiled tau instance. On this
fragment the two translations agree: `template13 φ` is the six-variable `template φ` cast into thirteen
variables (`template13_eq_castLE`), and the code of a cast formula is the code of the formula
(`quote_castLE₆`), so `templateCode φ = ⌜template φ⌝` (`templateCode_eq_quote_template`) — the bridge every
`Cells/` statement about `templateCode` rests on. -/

mutual
  /-- No dangling pronoun (`.sys` binds its members' pronouns; vote entries are closed instances). -/
  def noSelfIdxP : PD.Prog → Bool
    | .const _ => true
    | .self => true
    | .opp => true
    | .bot p => noSelfIdxP p
    | .sim p q => noSelfIdxP p && noSelfIdxP q
    | .ite b _ p q => noSelfIdxP b && noSelfIdxP p && noSelfIdxP q
    | .search _ φ p q => noSelfIdxF φ && noSelfIdxP p && noSelfIdxP q
    | .tvote _ _ p q => noSelfIdxP p && noSelfIdxP q
    | .sys _ _ => true
    | .selfIdx _ => false
  def noSelfIdxF : PD.Formula → Bool
    | .plays p q _ => noSelfIdxP p && noSelfIdxP q
    | .impl φ ψ => noSelfIdxF φ && noSelfIdxF ψ
    | .neg φ => noSelfIdxF φ
    | .box _ φ => noSelfIdxF φ
    | .eq p q => noSelfIdxP p && noSelfIdxP q
    | .diag _ _ => true
end

mutual
  theorem noSelfIdxP_of_fragP : ∀ p : PD.Prog, fragP p = true → noSelfIdxP p = true
    | .const _, _ => rfl
    | .self, _ => rfl
    | .opp, _ => rfl
    | .bot p, h => noSelfIdxP_of_fragP p h
    | .sim p q, h => by
      simp only [fragP, Bool.and_eq_true] at h
      simp only [noSelfIdxP, noSelfIdxP_of_fragP p h.1, noSelfIdxP_of_fragP q h.2, Bool.and_self]
    | .ite b _ p q, h => by
      simp only [fragP, Bool.and_eq_true] at h
      simp only [noSelfIdxP, noSelfIdxP_of_fragP b h.1.1, noSelfIdxP_of_fragP p h.1.2, noSelfIdxP_of_fragP q h.2,
        Bool.and_self]
    | .search _ φ p q, h => by
      simp only [fragP, Bool.and_eq_true] at h
      simp only [noSelfIdxP, noSelfIdxF_of_fragF φ h.1.1, noSelfIdxP_of_fragP p h.1.2, noSelfIdxP_of_fragP q h.2,
        Bool.and_self]
    | .tvote _ _ _ _, h => by simp [fragP] at h
    | .sys _ _, h => by simp [fragP] at h
    | .selfIdx _, h => by simp [fragP] at h
  theorem noSelfIdxF_of_fragF : ∀ φ : PD.Formula, fragF φ = true → noSelfIdxF φ = true
    | .plays p q _, h => by
      simp only [fragF, Bool.and_eq_true] at h
      simp only [noSelfIdxF, noSelfIdxP_of_fragP p h.1.1.2, noSelfIdxP_of_fragP q h.2, Bool.and_self]
    | .impl φ ψ, h => by
      simp only [fragF, Bool.and_eq_true] at h
      simp only [noSelfIdxF, noSelfIdxF_of_fragF φ h.1, noSelfIdxF_of_fragF ψ h.2, Bool.and_self]
    | .neg φ, h => noSelfIdxF_of_fragF φ h
    | .box _ _, h => by simp [fragF] at h
    | .eq p q, h => by
      simp only [fragF, Bool.and_eq_true] at h
      simp only [noSelfIdxF, noSelfIdxP_of_fragP p h.1.2, noSelfIdxP_of_fragP q h.2, Bool.and_self]
    | .diag _ _, _ => rfl
end


mutual
  theorem noSelfIdxP_subst : ∀ (p me opp : PD.Prog), noSelfIdxP p = true → noSelfIdxP me = true →
      noSelfIdxP opp = true → noSelfIdxP (p.subst me opp) = true
    | .const _, _, _, _, _, _ => rfl
    | .self, _, _, _, hme, _ => hme
    | .opp, _, _, _, _, hopp => hopp
    | .bot _, _, _, h, _, _ => h
    | .sim p q, me, opp, h, hme, hopp => by
      simp only [noSelfIdxP, Bool.and_eq_true] at h
      simp only [PD.Prog.subst, noSelfIdxP, noSelfIdxP_subst p me opp h.1 hme hopp,
        noSelfIdxP_subst q me opp h.2 hme hopp, Bool.and_self]
    | .ite b _ p q, me, opp, h, hme, hopp => by
      simp only [noSelfIdxP, Bool.and_eq_true] at h
      simp only [PD.Prog.subst, noSelfIdxP, noSelfIdxP_subst b me opp h.1.1 hme hopp,
        noSelfIdxP_subst p me opp h.1.2 hme hopp, noSelfIdxP_subst q me opp h.2 hme hopp, Bool.and_self]
    | .search _ φ p q, me, opp, h, hme, hopp => by
      simp only [noSelfIdxP, Bool.and_eq_true] at h
      simp only [PD.Prog.subst, noSelfIdxP, noSelfIdxF_subst φ me opp h.1.1 hme hopp,
        noSelfIdxP_subst p me opp h.1.2 hme hopp, noSelfIdxP_subst q me opp h.2 hme hopp, Bool.and_self]
    | .tvote _ _ p q, me, opp, h, hme, hopp => by
      simp only [noSelfIdxP, Bool.and_eq_true] at h
      simp only [PD.Prog.subst, noSelfIdxP, noSelfIdxP_subst p me opp h.1 hme hopp,
        noSelfIdxP_subst q me opp h.2 hme hopp, Bool.and_self]
    | .sys _ _, _, _, _, _, _ => rfl
    | .selfIdx _, _, _, h, _, _ => by simp [noSelfIdxP] at h
  theorem noSelfIdxF_subst : ∀ (φ : PD.Formula) (me opp : PD.Prog), noSelfIdxF φ = true → noSelfIdxP me = true →
      noSelfIdxP opp = true → noSelfIdxF (φ.subst me opp) = true
    | .plays p q _, me, opp, h, hme, hopp => by
      simp only [noSelfIdxF, Bool.and_eq_true] at h
      show (noSelfIdxP (p.subst me opp) && noSelfIdxP (q.subst me opp)) = true
      rw [noSelfIdxP_subst p me opp h.1 hme hopp, noSelfIdxP_subst q me opp h.2 hme hopp]; rfl
    | .impl φ ψ, me, opp, h, hme, hopp => by
      simp only [noSelfIdxF, Bool.and_eq_true] at h
      simp only [PD.Formula.subst, noSelfIdxF, noSelfIdxF_subst φ me opp h.1 hme hopp,
        noSelfIdxF_subst ψ me opp h.2 hme hopp, Bool.and_self]
    | .neg φ, me, opp, h, hme, hopp => by
      simp only [noSelfIdxF] at h
      simp only [PD.Formula.subst, noSelfIdxF, noSelfIdxF_subst φ me opp h hme hopp]
    | .box _ φ, me, opp, h, hme, hopp => by
      simp only [noSelfIdxF] at h
      simp only [PD.Formula.subst, noSelfIdxF, noSelfIdxF_subst φ me opp h hme hopp]
    | .eq p q, me, opp, h, hme, hopp => by
      simp only [noSelfIdxF, Bool.and_eq_true] at h
      show (noSelfIdxP (p.subst me opp) && noSelfIdxP q) = true
      rw [noSelfIdxP_subst p me opp h.1 hme hopp, h.2]; rfl
    | .diag _ _, _, _, _, _, _ => rfl
end

mutual
  theorem noSelfIdxP_transpose : ∀ p : PD.Prog, noSelfIdxP p.transpose = noSelfIdxP p
    | .const _ => rfl
    | .self => rfl
    | .opp => rfl
    | .bot p => noSelfIdxP_transpose p
    | .sim p q => by simp only [PD.Prog.transpose, noSelfIdxP, noSelfIdxP_transpose p, noSelfIdxP_transpose q]
    | .ite b _ p q => by
      simp only [PD.Prog.transpose, noSelfIdxP, noSelfIdxP_transpose b, noSelfIdxP_transpose p, noSelfIdxP_transpose q]
    | .search _ φ p q => by
      simp only [PD.Prog.transpose, noSelfIdxP, noSelfIdxF_transpose φ, noSelfIdxP_transpose p, noSelfIdxP_transpose q]
    | .tvote _ _ p q => by simp only [PD.Prog.transpose, noSelfIdxP, noSelfIdxP_transpose p, noSelfIdxP_transpose q]
    | .sys _ _ => rfl
    | .selfIdx _ => rfl
  theorem noSelfIdxF_transpose : ∀ φ : PD.Formula, noSelfIdxF φ.transpose = noSelfIdxF φ
    | .plays p q _ => by simp only [PD.Formula.transpose, noSelfIdxF, noSelfIdxP_transpose p, noSelfIdxP_transpose q]
    | .impl φ ψ => by simp only [PD.Formula.transpose, noSelfIdxF, noSelfIdxF_transpose φ, noSelfIdxF_transpose ψ]
    | .neg φ => noSelfIdxF_transpose φ
    | .box _ φ => noSelfIdxF_transpose φ
    | .eq p q => by simp only [PD.Formula.transpose, noSelfIdxF, noSelfIdxP_transpose p, noSelfIdxP_transpose q]
    | .diag _ _ => rfl
end

lemma noSelfIdxP_ne_selfIdx {p : PD.Prog} (h : noSelfIdxP p = true) (j : ℕ) : p ≠ .selfIdx j := by
  rintro rfl; simp [noSelfIdxP] at h

lemma pronounP_eq_false_of_noSelfIdxP {p : PD.Prog} (h : noSelfIdxP p = true) : pronounP p = false := by
  cases p
  case selfIdx j => simp [noSelfIdxP] at h
  case bot q =>
    cases q
    case selfIdx j => simp [noSelfIdxP] at h
    all_goals rfl
  all_goals rfl

/-! ### The budget-snapshot predicates and the bridge `templateCodeAt φ k = templateCode φ`

`searchFreeP p`: no `.search` node at a described position of `p` (a `.sys` is a leaf, a `.tvote` is excluded —
a vote never sits inside a template). On such a program the abstracted description is the verbatim one
(`noSearchAt_progCode`, `closedDescAt_progCode_eq`). `noBudgetSnapshotF φ`: every closed program an atom of `φ`
describes is `searchFreeP` — then `templateAt φ (some k) = templateAt φ none` for every `k`
(`templateAt_some_eq_none`), i.e. the stored template is today's `templateCode φ`
(`templateCodeAt_eq_templateCode`): true of every base guard but JustBot's (`.bot (DupocBot k)`) and
CupodTrollBot's (`.eq .opp (CupodBot k)`), and of every tau guard naming a budget-free hypothesis instance. -/

/-- No `.search` node at a described position (`.sys` a leaf; `.tvote` excluded). -/
def searchFreeP : PD.Prog → Bool
  | .const _ => true
  | .self => true
  | .opp => true
  | .bot p => searchFreeP p
  | .sim p q => searchFreeP p && searchFreeP q
  | .ite b _ p q => searchFreeP b && searchFreeP p && searchFreeP q
  | .search _ _ _ _ => false
  | .tvote _ _ _ _ => false
  | .sys _ _ => true
  | .selfIdx _ => true

/-- No closed sub-program at a described position of `φ` contains a `.search` (a `.box` body is stored
unabstracted, so it never matters here). -/
def noBudgetSnapshotF : PD.Formula → Bool
  | .plays p q _ => searchFreeP p && searchFreeP q
  | .impl φ ψ => noBudgetSnapshotF φ && noBudgetSnapshotF ψ
  | .neg φ => noBudgetSnapshotF φ
  | .box _ _ => true
  | .eq p q => searchFreeP p && searchFreeP q
  | .diag _ _ => true

mutual
  /-- Every stored template of `p` is unabstracted (`noBudgetSnapshotF` on every search guard). -/
  def noBudgetSnapshotP : PD.Prog → Bool
    | .const _ => true
    | .self => true
    | .opp => true
    | .bot p => noBudgetSnapshotP p
    | .sim p q => noBudgetSnapshotP p && noBudgetSnapshotP q
    | .ite b _ p q => noBudgetSnapshotP b && noBudgetSnapshotP p && noBudgetSnapshotP q
    | .search _ φ p q => noBudgetSnapshotF φ && noBudgetSnapshotP p && noBudgetSnapshotP q
    | .tvote v _ p q => noBudgetSnapshotV v && noBudgetSnapshotP p && noBudgetSnapshotP q
    | .sys defs _ => noBudgetSnapshotL defs
    | .selfIdx _ => true
  def noBudgetSnapshotL : PD.ProgList → Bool
    | .nil => true
    | .cons p rest => noBudgetSnapshotP p && noBudgetSnapshotL rest
  def noBudgetSnapshotV : PD.VoteList → Bool
    | .nil => true
    | .cons _ I rest => noBudgetSnapshotP I && noBudgetSnapshotV rest
end

/-- A `searchFreeP` program's code has no `pSearch` node at a descent position. -/
theorem noSearchAt_progCode : ∀ p : PD.Prog, searchFreeP p = true → ∀ k₀ : ℕ, NoSearchAt k₀ (progCode p)
  | .const a, _, k₀ => by rw [progCode_const]; exact .const _ _
  | .self, _, k₀ => by rw [progCode_self]; exact .self _
  | .opp, _, k₀ => by rw [progCode_opp]; exact .opp _
  | .bot p, h, k₀ => by rw [progCode_bot]; exact .bot _ (noSearchAt_progCode p h k₀)
  | .sim p q, h, k₀ => by
    simp only [searchFreeP, Bool.and_eq_true] at h
    rw [progCode_sim]; exact .sim _ _ (noSearchAt_progCode p h.1 k₀) (noSearchAt_progCode q h.2 k₀)
  | .ite b _ p q, h, k₀ => by
    simp only [searchFreeP, Bool.and_eq_true] at h
    rw [progCode_ite]
    exact .ite _ _ _ _ (noSearchAt_progCode b h.1.1 k₀) (noSearchAt_progCode p h.1.2 k₀) (noSearchAt_progCode q h.2 k₀)
  | .search _ _ _ _, h, _ => by simp [searchFreeP] at h
  | .tvote _ _ _ _, h, _ => by simp [searchFreeP] at h
  | .sys _ _, _, k₀ => by rw [progCode_sys]; exact .sys _ _ _
  | .selfIdx _, _, k₀ => by rw [progCode_selfIdx]; exact .selfIdx _ _

lemma canonicalSlot_progCode_eq {n : ℕ} {p : PD.Prog} (hp : searchFreeP p = true) (k₀ : Option ℕ) (b : Semiterm LAct Empty n) :
    canonicalSlot k₀ (progCode p) b = cl (canonicalMeta (progCode p)) := by
  cases k₀ with
  | none => rfl
  | some k => exact canonicalSlot_of_noSearchAt (noSearchAt_progCode p hp k).canonical b

lemma closedDescAt_progCode_eq {p : PD.Prog} (hp : searchFreeP p = true) (k₀ : Option ℕ) :
    closedDescAt k₀ (progCode p) = closedDesc13 (progCode p) := by
  unfold closedDescAt closedDesc13; rw [canonicalSlot_progCode_eq hp]

lemma progGraphAt_some_eq_none {p : PD.Prog} (hp : searchFreeP p = true) (k : ℕ) :
    progGraphAt (some k) p = progGraphAt none p := by
  unfold progGraphAt
  by_cases h1 : p = .self
  · subst h1; rfl
  by_cases h2 : p = .opp
  · subst h2; rfl
  by_cases h3 : pronounP p = true
  · rcases pronounP_cases h3 with rfl | rfl | rfl | rfl <;> rfl
  · rw [progAuxAt_of_ne _ h1 h2 (Bool.eq_false_iff.mpr h3), progAuxAt_of_ne _ h1 h2 (Bool.eq_false_iff.mpr h3),
      closedDescAt_progCode_eq hp, closedDescAt_progCode_eq hp]

/-- **The bridge, meta level**: a template without a budget snapshot is the same at every node budget. -/
theorem templateAt_some_eq_none : ∀ φ : PD.Formula, noBudgetSnapshotF φ = true → ∀ k : ℕ,
    templateAt φ (some k) = templateAt φ none
  | .plays p q a, h, k => by
    simp only [noBudgetSnapshotF, Bool.and_eq_true] at h
    rw [templateAt_plays, templateAt_plays, progGraphAt_some_eq_none h.1, progGraphAt_some_eq_none h.2]
  | .impl φ ψ, h, k => by
    simp only [noBudgetSnapshotF, Bool.and_eq_true] at h
    rw [templateAt_impl, templateAt_impl, templateAt_some_eq_none φ h.1 k, templateAt_some_eq_none ψ h.2 k]
  | .neg φ, h, k => by
    simp only [noBudgetSnapshotF] at h
    rw [templateAt_neg, templateAt_neg, templateAt_some_eq_none φ h k]
  | .box _ _, _, k => by simp only [templateAt_box, progAuxAt_self, progAuxAt_opp]
  | .eq p q, h, k => by
    simp only [noBudgetSnapshotF, Bool.and_eq_true] at h
    rw [templateAt_eq, templateAt_eq, progGraphAt_some_eq_none h.1, closedDescAt_progCode_eq h.2,
      closedDescAt_progCode_eq h.2]
  | .diag _ _, _, k => by rw [templateAt_diag, templateAt_diag]

/-- Discharges `noBudgetSnapshotF φ = true` on a concrete formula (by computation) or by assumption. -/
macro "noSnap_tac" : tactic =>
  `(tactic| first
      | assumption
      | rfl
      | decide
      | (simp only [noBudgetSnapshotF, searchFreeP, Bool.and_true, Bool.true_and, Bool.and_self]
         first | rfl | decide | assumption))

/-- **The bridge**: on a formula without a budget snapshot the stored template code is today's `templateCode φ`.
Every statement about the base zoo's templates reads through this equation. -/
theorem templateCodeAt_eq_templateCode (φ : PD.Formula) (k : ℕ) (h : noBudgetSnapshotF φ = true := by noSnap_tac) :
    templateCodeAt φ k = templateCode φ := by
  unfold templateCodeAt templateCode template13
  rw [templateAt_some_eq_none φ h k]

/-- `progCode_search` on a snapshot-free guard: the stored template is `templateCode φ`. -/
lemma progCode_search_noSnap (k : ℕ) (φ : PD.Formula) (p q : PD.Prog) (h : noBudgetSnapshotF φ = true := by noSnap_tac) :
    progCode (.search k φ p q) = pSearch k (templateCode φ) (progCode p) (progCode q) := by
  rw [progCode_search, templateCodeAt_eq_templateCode φ k h]

/-! ### The description lemma (Lemma A) -/

lemma progAux_self (c : ℕ) : progAux .self c = descF #1 #2 #3 #4 := by simp [progAux]
lemma progAux_opp (c : ℕ) : progAux .opp c = descF #1 #5 #6 #7 := by simp [progAux]
lemma progAux_of_ne {p : PD.Prog} (h1 : p ≠ .self) (h2 : p ≠ .opp) (c : ℕ) : progAux p c = closedDesc c := by
  simp [progAux, h1, h2]

lemma closedP_ne_self {p : PD.Prog} (h : closedP p = true) : p ≠ .self := by
  rintro rfl; simp [closedP] at h
lemma closedP_ne_opp {p : PD.Prog} (h : closedP p = true) : p ≠ .opp := by
  rintro rfl; simp [closedP] at h

lemma closedDesc_subst {m : ℕ} (c : ℕ) (w : Fin 7 → Semiterm LAct Empty m) :
    closedDesc c ⇜ w = descF (Rew.bShift (w 0)) (cl (canonicalMeta c)) (cl (revalueUMeta c)) (cl (revalueWMeta c)) := by
  unfold closedDesc Rewriting.subst
  rw [rew_descF]
  simp only [rew_cl]
  rfl

/-- **Lemma A**: substituting the frame descriptions into the description of an atomic
program gives the description of the substituted program. -/
lemma progAux_subst {m : ℕ} {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp) (hopp : opp ≠ .self ∧ opp ≠ .opp)
    {p : PD.Prog} (hp : atomicP p = true) (w w' : Fin 7 → Semiterm LAct Empty m)
    (h0 : w 0 = w' 0)
    (h1 : w 1 = cl (canonicalMeta (progCode me))) (h2 : w 2 = cl (revalueUMeta (progCode me))) (h3 : w 3 = cl (revalueWMeta (progCode me)))
    (h4 : w 4 = cl (canonicalMeta (progCode opp))) (h5 : w 5 = cl (revalueUMeta (progCode opp))) (h6 : w 6 = cl (revalueWMeta (progCode opp))) :
    progAux p (progCode p) ⇜ w = progAux (p.subst me opp) (progCode (p.subst me opp)) ⇜ w' := by
  simp only [atomicP, Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with (rfl | rfl) | hc
  · rw [progAux_self, PD.Prog.subst, progAux_of_ne hme.1 hme.2, closedDesc_subst]
    unfold Rewriting.subst
    rw [rew_descF]
    show descF (Rew.bShift (w 0)) (Rew.bShift (w 1)) (Rew.bShift (w 2)) (Rew.bShift (w 3)) = _
    rw [h0, h1, h2, h3, rew_cl, rew_cl, rew_cl]
  · rw [progAux_opp, PD.Prog.subst, progAux_of_ne hopp.1 hopp.2, closedDesc_subst]
    unfold Rewriting.subst
    rw [rew_descF]
    show descF (Rew.bShift (w 0)) (Rew.bShift (w 4)) (Rew.bShift (w 5)) (Rew.bShift (w 6)) = _
    rw [h0, h4, h5, h6, rew_cl, rew_cl, rew_cl]
  · rw [subst_of_closedP p me opp hc, progAux_of_ne (closedP_ne_self hc) (closedP_ne_opp hc),
      closedDesc_subst, closedDesc_subst, h0]

/-! ### The substitution equation -/

lemma rew_subst_eq {n m k : ℕ} (ω : Rew LAct Empty m Empty k) (v : Fin n → Semiterm LAct Empty m)
    (φ : Semisentence LAct n) : ω ▹ (φ ⇜ v) = φ ⇜ (fun i ↦ ω (v i)) := by
  unfold Rewriting.subst
  rw [← TransitiveRewriting.comp_app, comp_subst_eq]

/-- The closed description terms of the players' codes, in the six-variable context. -/
noncomputable def descTerms6 (me opp : PD.Prog) : Fin 6 → Semiterm LAct Empty 6 :=
  fun i ↦ cl (descriptionTerms (progCode me) (progCode opp) i)

/-- **The meta substitution equation** (the heart of step (c)): on the fragment, the
template of a substituted formula IS the template with the closed descriptions of the
players substituted for the frame variables. -/
theorem template_subst {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp) (hopp : opp ≠ .self ∧ opp ≠ .opp) :
    ∀ ψ : PD.Formula, fragF ψ = true → template (ψ.subst me opp) = template ψ ⇜ descTerms6 me opp
  | .plays p q a, h => by
    simp only [fragF, Bool.and_eq_true] at h
    rw [PD.Formula.subst, template_plays, template_plays]
    unfold progGraph
    simp only [Rewriting.app_exs, Rew.q_subst, LogicalConnective.HomClass.map_and, rew_subst_eq]
    congr 4
    · refine (progAux_subst hme hopp h.1.1.1 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_).symm
      · rfl
      all_goals (show Rew.bShift (Rew.bShift (Rew.bShift (cl _))) = _; rw [rew_cl, rew_cl, rew_cl]; try rfl)
    · congr 1
      · refine (progAux_subst hme hopp h.1.2 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_).symm
        · rfl
        all_goals (show Rew.bShift (Rew.bShift (Rew.bShift (cl _))) = _; rw [rew_cl, rew_cl, rew_cl]; try rfl)
      · congr 1
        funext i
        fin_cases i
        · rfl
        · rfl
        · rfl
        · rfl
        · exact (rew_cl _ _).symm
  | .impl φ ψ, h => by
    simp only [fragF, Bool.and_eq_true] at h
    rw [PD.Formula.subst, template_impl, template_impl, template_subst hme hopp φ h.1, template_subst hme hopp ψ h.2]
    unfold Rewriting.subst
    rw [LogicalConnective.HomClass.map_imply]
  | .neg φ, h => by
    simp only [fragF] at h
    rw [PD.Formula.subst, template_neg, template_neg, template_subst hme hopp φ h]
    unfold Rewriting.subst
    rw [LogicalConnective.HomClass.map_neg]
  | .box _ _, h => by simp [fragF] at h
  | .eq p q, h => by
    simp only [fragF, Bool.and_eq_true] at h
    rw [PD.Formula.subst, template_eq, template_eq]
    unfold progGraph
    simp only [Rewriting.app_exs, Rew.q_subst, LogicalConnective.HomClass.map_and, rew_subst_eq]
    congr 3
    · refine (progAux_subst hme hopp h.1.1 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_).symm
      · rfl
      all_goals (show Rew.bShift (Rew.bShift (cl _)) = _; rw [rew_cl, rew_cl]; try rfl)
    · congr 1
      · rw [closedDesc_subst, closedDesc_subst]; rfl
      · rw [Semiformula.rew_rel]
        congr 1
        funext i
        fin_cases i <;> rfl
  | .diag _ _, _ => by
    simp only [PD.Formula.subst, template_diag]
    unfold Rewriting.subst
    rw [LogicalConnective.HomClass.map_bot]

/-- Codes do not see the context: substituting closed terms at six variables or at zero
gives the same code. -/
lemma quote_subst_cl (σ : Semisentence LAct 6) (w : Fin 6 → ClosedSemiterm LAct 0) :
    (⌜σ ⇜ (fun i ↦ (cl (w i) : Semiterm LAct Empty 6))⌝ : ℕ) = ⌜σ ⇜ w⌝ := by
  rw [Sentence.quote_def, Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe,
    Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs,
    Bootstrapping.Semiformula.val_substs]
  congr 1
  unfold SemitermVec.val
  exact matrixToVec_congr (fun i ↦ quote_emb_cl (w i))

/-! #### The bridge: on the `noSelfIdx` fragment the thirteen-variable template is the six-variable one, cast -/

lemma closedDescAt_subst {m : ℕ} (k₀ : Option ℕ) (c : ℕ) (w : Fin 14 → Semiterm LAct Empty m) :
    closedDescAt k₀ c ⇜ w =
      descF (Rew.bShift (w 0)) (canonicalSlot k₀ c (Rew.bShift (w 7))) (cl (revalueUMeta c)) (cl (revalueWMeta c)) := by
  unfold closedDescAt Rewriting.subst
  rw [rew_descF, rew_canonicalSlot]
  simp only [rew_cl]
  rfl

lemma closedDesc13_subst {m : ℕ} (c : ℕ) (w : Fin 14 → Semiterm LAct Empty m) :
    closedDesc13 c ⇜ w = descF (Rew.bShift (w 0)) (cl (canonicalMeta c)) (cl (revalueUMeta c)) (cl (revalueWMeta c)) :=
  closedDescAt_subst none c w

/-- Substituting into a cast formula reads the substitution through the cast. -/
lemma subst_castLE {n m k : ℕ} (h : n ≤ m) (A : Semisentence LAct n) (w : Fin m → Semiterm LAct Empty k) :
    (Rew.castLE h ▹ A : Semisentence LAct m) ⇜ w = A ⇜ (fun i ↦ w (Fin.castLE h i)) := by
  unfold Rewriting.subst
  rw [← TransitiveRewriting.comp_app]
  have hc : (Rew.subst w).comp (Rew.castLE h) = Rew.subst (fun i ↦ w (Fin.castLE h i)) := by
    ext x
    · simp [Rew.comp_app]
    · exact x.elim
  rw [hc]

lemma progAux13_eq_castLE {p : PD.Prog} (hp : noSelfIdxP p = true) (c : ℕ) :
    progAux13 p c = Rew.castLE (by norm_num : 7 ≤ 14) ▹ progAux p c := by
  by_cases h1 : p = .self
  · subst h1
    rw [progAux13_self, progAux_self, rew_descF]
    simp only [Rew.q_castLE, Rew.castLe_bvar]
    rfl
  by_cases h2 : p = .opp
  · subst h2
    rw [progAux13_opp, progAux_opp, rew_descF]
    simp only [Rew.q_castLE, Rew.castLe_bvar]
    rfl
  rw [progAux13_of_ne h1 h2 (pronounP_eq_false_of_noSelfIdxP hp), progAux_of_ne h1 h2]
  unfold closedDesc13 closedDesc
  rw [rew_descF]
  simp only [Rew.q_castLE, Rew.castLe_bvar, rew_cl]
  rfl

/-- **The bridge, meta level**: on the `noSelfIdx` fragment `template13` is `template` cast into thirteen
variables (every clause index for index; the pronoun clauses of `progAux13` are never reached). -/
theorem template13_eq_castLE : ∀ φ : PD.Formula, noSelfIdxF φ = true →
    template13 φ = Rew.castLE (by norm_num : 6 ≤ 13) ▹ template φ
  | .plays p q a, h => by
    simp only [noSelfIdxF, Bool.and_eq_true] at h
    rw [template13_plays, template_plays]
    unfold progGraph13 progGraph
    simp only [Rewriting.app_exs, Rew.q_castLE, LogicalConnective.HomClass.map_and, rew_subst_eq]
    rw [progAux13_eq_castLE h.1, progAux13_eq_castLE h.2, subst_castLE, subst_castLE]
    congr 4
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1
      · congr 1; funext i; fin_cases i <;> rfl
      · congr 1
        funext i
        fin_cases i
        · rfl
        · rfl
        · rfl
        · rfl
        · exact (rew_cl _ _).symm
  | .impl φ ψ, h => by
    simp only [noSelfIdxF, Bool.and_eq_true] at h
    rw [template13_impl, template_impl, LogicalConnective.HomClass.map_imply, template13_eq_castLE φ h.1,
      template13_eq_castLE ψ h.2]
  | .neg φ, h => by
    simp only [noSelfIdxF] at h
    rw [template13_neg, template_neg, LogicalConnective.HomClass.map_neg, template13_eq_castLE φ h]
  | .box k ψ, _ => by
    rw [template13_box, template_box]
    simp only [Rewriting.app_exs, Rew.q_castLE, LogicalConnective.HomClass.map_and, rew_subst_eq]
    rw [progAux13_eq_castLE (p := .self) rfl, progAux13_eq_castLE (p := .opp) rfl, subst_castLE, subst_castLE]
    congr 3
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1
      · congr 1; funext i; fin_cases i <;> rfl
      · congr 2
        · congr 1
          funext i
          fin_cases i
          · rfl
          · exact (rew_cl _ _).symm
          · rfl
          · rfl
        · congr 1
          funext i
          fin_cases i
          · exact (rew_cl _ _).symm
          · rfl
  | .eq p q, h => by
    simp only [noSelfIdxF, Bool.and_eq_true] at h
    rw [template13_eq, template_eq]
    unfold progGraph13 progGraph
    simp only [Rewriting.app_exs, Rew.q_castLE, LogicalConnective.HomClass.map_and, rew_subst_eq]
    rw [progAux13_eq_castLE h.1, subst_castLE]
    congr 3
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1
      · rw [closedDesc13_subst, closedDesc_subst]; rfl
      · rw [Semiformula.rew_rel]
        congr 1
        funext i
        fin_cases i <;> rfl
  | .diag _ _, _ => by
    rw [template13_diag, template_diag, LogicalConnective.HomClass.map_bot]

/-- The code of a substituted semisentence, at any arity: `subst` of the codes of the substituted terms. -/
lemma quote_subst_gen {k n : ℕ} (σ : Semisentence LAct k) (w : Fin k → Semiterm LAct Empty n) :
    (⌜(σ ⇜ w : Semisentence LAct n)⌝ : ℕ) =
      subst LAct (SemitermVec.val (fun i ↦ (⌜(Rew.emb (w i) : SyntacticSemiterm LAct n)⌝ : Bootstrapping.Semiterm ℕ LAct n)))
        (⌜σ⌝ : ℕ) := by
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]

/-- **Codes do not see the arity**: the code of a six-variable formula cast into thirteen variables is its code
(the cast is the substitution of the variables by themselves, `subst_eq_self_of_le`). -/
theorem quote_castLE₆ (σ : Semisentence LAct 6) :
    (⌜(Rew.castLE (by norm_num : 6 ≤ 13) ▹ σ : Semisentence LAct 13)⌝ : ℕ) = ⌜σ⌝ := by
  have h613 : (6 : ℕ) ≤ 13 := by norm_num
  have hc : (Rew.castLE h613 : Rew LAct Empty 6 Empty 13) =
      Rew.subst (fun i ↦ (#(Fin.castLE h613 i) : Semiterm LAct Empty 13)) := by
    ext x <;> first | exact x.elim | rfl | simp
  rw [hc]
  change (⌜(σ ⇜ (fun i ↦ (#(Fin.castLE h613 i) : Semiterm LAct Empty 13)) : Semisentence LAct 13)⌝ : ℕ) = _
  rw [quote_subst_gen]
  have hv : (fun i : Fin 6 ↦ (⌜(Rew.emb (#(Fin.castLE h613 i) : Semiterm LAct Empty 13) : SyntacticSemiterm LAct 13)⌝ :
      Bootstrapping.Semiterm ℕ LAct 13)) =
      ![⌜(#0 : SyntacticSemiterm LAct 13)⌝, ⌜(#1 : SyntacticSemiterm LAct 13)⌝, ⌜(#2 : SyntacticSemiterm LAct 13)⌝,
        ⌜(#3 : SyntacticSemiterm LAct 13)⌝, ⌜(#4 : SyntacticSemiterm LAct 13)⌝, ⌜(#5 : SyntacticSemiterm LAct 13)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil]
  have hid : ((⌜(#0 : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13).val ∷
      (⌜(#1 : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13).val ∷
      (⌜(#2 : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13).val ∷
      (⌜(#3 : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13).val ∷
      (⌜(#4 : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13).val ∷
      (⌜(#5 : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13).val ∷ (0 : ℕ)) = idVec6 := rfl
  rw [hid]
  have hlt : (6 : ℕ) < 13 := by norm_num
  have hvec := idVec6_semitermVec (V := ℕ) (n := 13) (le_def.mpr (Or.inr hlt))
  exact subst_eq_self_of_le (isSemiformula_quote₆ σ) (by rw [hvec.lh]; exact hvec.isUTerm)
    (le_def.mpr (Or.inl hvec.lh.symm)) nth_idVec6

/-- **The bridge**: on the `noSelfIdx` fragment the stored template code is the code of the six-variable
template — every `Cells/` statement about `templateCode` reads through this equation. -/
theorem templateCode_eq_quote_template (φ : PD.Formula) (h : noSelfIdxF φ = true) : templateCode φ = ⌜template φ⌝ := by
  unfold templateCode
  rw [template13_eq_castLE φ h]
  exact quote_castLE₆ _

/-- Discharges the side condition `noSelfIdxF φ = true` (or `noSelfIdxP p = true`) of the bridge: by
assumption, by computation on a concrete formula, or from a `fragF`/`fragP` hypothesis (also under one
layer of `.plays`/`.eq`/`.neg`/`.bot` structure). -/
macro "noSelfIdx_tac" : tactic =>
  `(tactic| first
      | assumption
      | rfl
      | decide
      | exact noSelfIdxF_of_fragF _ ‹_›
      | exact noSelfIdxP_of_fragP _ ‹_›
      | (simp only [noSelfIdxF, noSelfIdxP, Bool.and_true, Bool.true_and, Bool.and_self, Bool.and_eq_true]
         first
           | assumption
           | rfl
           | exact noSelfIdxP_of_fragP _ ‹_›
           | exact noSelfIdxF_of_fragF _ ‹_›
           | exact ⟨noSelfIdxP_of_fragP _ ‹_›, noSelfIdxP_of_fragP _ ‹_›⟩
           | exact ⟨by assumption, noSelfIdxP_of_fragP _ ‹_›⟩
           | exact ⟨noSelfIdxP_of_fragP _ ‹_›, by assumption⟩))

/-- The template code is a six-variable formula code — on the `noSelfIdx` fragment (a member's guard reads
the member slots and is thirteen-variable, `isSemiformula_templateCode13`). -/
lemma isSemiformula_templateCode (φ : PD.Formula) (h : noSelfIdxF φ = true := by noSelfIdx_tac) :
    IsSemiformula LAct 6 (templateCode φ) := by
  rw [templateCode_eq_quote_template φ h]
  exact isSemiformula_quote₆ _

/-- The sentence "`φ` at the players `me`, `opp`": the template filled with the closed
descriptions of their codes — the atom realization T2-AGENT uses. -/
noncomputable def sentenceAt (me opp : PD.Prog) (φ : PD.Formula) : Sentence LAct :=
  template φ ⇜ descriptionTerms (progCode me) (progCode opp)

/-- The code of `sentenceAt` is the guard code of the template code (the `quote_guardSentence`
argument), on the `noSelfIdx` fragment (a member's guard is read through the member slots, which the
six-slot `guardCode` does not fill). -/
theorem quote_sentenceAt (me opp : PD.Prog) (φ : PD.Formula) (h : noSelfIdxF φ = true := by noSelfIdx_tac) :
    (⌜sentenceAt me opp φ⌝ : ℕ) = guardCode (templateCode φ) (progCode me) (progCode opp) := by
  rw [templateCode_eq_quote_template φ h]
  unfold sentenceAt guardCode
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1
  exact semitermVec_val_descriptionTerms _ _

/-! ### The seven-variable reading of a pronoun-free template, and the instantiation lemma

On the `noSelfIdx` fragment `templateAt φ k₀` never reads the member slots, so it is the cast of a SEVEN-variable
formula `template7At φ k₀` (frame `#0..#5`, budget `#6`) — `templateAt_eq_castLE₇`, `quote_castLE₇` — and the
stored code is a seven-variable template (`isSemiformula_templateCodeAt₇`): `substTemplate`'s middle case
(`guardCodeSlot`) is what instantiates it inside a simulated program. The instantiation lemma
`template7At_budget` — with the node's own budget in slot `#6`, the abstracted template IS the unabstracted one
(`canonicalSlot_numTB`) — gives **`guardCodeB_templateCodeAt`**: the sentence the evaluator consults on the
stored template is `guardCode (templateCode φ) me opp`, the pre-abstraction guard, in every frame
(`EvalGraph.search_iff_at`). The evaluator's behaviour is unchanged by the abstraction; only the stored numerals
shrink. -/

/-- The closed description in the seven-variable frame (`#1..#7`, budget `#8` inside `descF`). -/
noncomputable def closedDesc7At (k₀ : Option ℕ) (c : ℕ) : Semisentence LAct 8 :=
  descF #1 (canonicalSlot k₀ c #8) (cl (revalueUMeta c)) (cl (revalueWMeta c))

/-- The description of `p` in the seven-variable frame: the me-triple, the opp-triple, or the closed description. -/
noncomputable def progAux7At (k₀ : Option ℕ) (p : PD.Prog) (c : ℕ) : Semisentence LAct 8 :=
  if p = .self then descF #1 #2 #3 #4 else if p = .opp then descF #1 #5 #6 #7 else closedDesc7At k₀ c

lemma progAux7At_self (k₀ : Option ℕ) (c : ℕ) : progAux7At k₀ .self c = descF #1 #2 #3 #4 := by simp [progAux7At]
lemma progAux7At_opp (k₀ : Option ℕ) (c : ℕ) : progAux7At k₀ .opp c = descF #1 #5 #6 #7 := by simp [progAux7At]
lemma progAux7At_of_ne (k₀ : Option ℕ) {p : PD.Prog} (h1 : p ≠ .self) (h2 : p ≠ .opp) (c : ℕ) :
    progAux7At k₀ p c = closedDesc7At k₀ c := by simp [progAux7At, h1, h2]

/-- The seven-variable template at the node budget `k₀`. -/
noncomputable def template7At : PD.Formula → Option ℕ → Semisentence LAct 7
  | .plays p q a, k₀ =>
      ∃¹ (∃¹ (∃¹ ((progAux7At k₀ p (progCode p) ⇜ ![#2, #3, #4, #5, #6, #7, #8, #9]) ⋏
        ((progAux7At k₀ q (progCode q) ⇜ ![#1, #3, #4, #5, #6, #7, #8, #9]) ⋏
          (evalG ⇜ ![#0, #2, #1, #2, cl (actT (actCode a))])))))
  | .impl φ ψ, k₀ => template7At φ k₀ 🡒 template7At ψ k₀
  | .neg φ, k₀ => ∼ template7At φ k₀
  | .box k ψ, k₀ =>
      ∃¹ (∃¹ ((progAux7At k₀ .self 0 ⇜ ![#1, #2, #3, #4, #5, #6, #7, #8]) ⋏
        ((progAux7At k₀ .opp 0 ⇜ ![#0, #2, #3, #4, #5, #6, #7, #8]) ⋏
          (∃¹ ((guardCodeG ⇜ ![#0, cl (numTB (templateCode ψ)), #2, #1]) ⋏
            (lenProvG ⇜ ![cl (numTB k), #0]))))))
  | .eq p q, k₀ =>
      ∃¹ (∃¹ ((progAux7At k₀ p (progCode p) ⇜ ![#1, #2, #3, #4, #5, #6, #7, #8]) ⋏
        ((closedDesc7At k₀ (progCode q) ⇜ ![#0, #2, #3, #4, #5, #6, #7, #8]) ⋏
          Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#1, #0])))
  | .diag _ _, _ => ⊥

lemma template7At_plays (k₀ p q a) : template7At (.plays p q a) k₀ =
    ∃¹ (∃¹ (∃¹ ((progAux7At k₀ p (progCode p) ⇜ ![#2, #3, #4, #5, #6, #7, #8, #9]) ⋏
      ((progAux7At k₀ q (progCode q) ⇜ ![#1, #3, #4, #5, #6, #7, #8, #9]) ⋏
        (evalG ⇜ ![#0, #2, #1, #2, cl (actT (actCode a))]))))) := by rw [template7At]
lemma template7At_impl (k₀ φ ψ) : template7At (.impl φ ψ) k₀ = template7At φ k₀ 🡒 template7At ψ k₀ := by rw [template7At]
lemma template7At_neg (k₀ φ) : template7At (.neg φ) k₀ = ∼ template7At φ k₀ := by rw [template7At]
lemma template7At_box (k₀ k ψ) : template7At (.box k ψ) k₀ =
    ∃¹ (∃¹ ((progAux7At k₀ .self 0 ⇜ ![#1, #2, #3, #4, #5, #6, #7, #8]) ⋏
      ((progAux7At k₀ .opp 0 ⇜ ![#0, #2, #3, #4, #5, #6, #7, #8]) ⋏
        (∃¹ ((guardCodeG ⇜ ![#0, cl (numTB (templateCode ψ)), #2, #1]) ⋏
          (lenProvG ⇜ ![cl (numTB k), #0])))))) := by rw [template7At]
lemma template7At_eq (k₀ p q) : template7At (.eq p q) k₀ =
    ∃¹ (∃¹ ((progAux7At k₀ p (progCode p) ⇜ ![#1, #2, #3, #4, #5, #6, #7, #8]) ⋏
      ((closedDesc7At k₀ (progCode q) ⇜ ![#0, #2, #3, #4, #5, #6, #7, #8]) ⋏
        Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#1, #0]))) := by rw [template7At]
lemma template7At_diag (k₀ g φ) : template7At (.diag g φ) k₀ = ⊥ := by rw [template7At]

lemma closedDesc7At_subst {m : ℕ} (k₀ : Option ℕ) (c : ℕ) (w : Fin 8 → Semiterm LAct Empty m) :
    closedDesc7At k₀ c ⇜ w =
      descF (Rew.bShift (w 0)) (canonicalSlot k₀ c (Rew.bShift (w 7))) (cl (revalueUMeta c)) (cl (revalueWMeta c)) := by
  unfold closedDesc7At Rewriting.subst
  rw [rew_descF, rew_canonicalSlot]
  simp only [rew_cl]
  rfl

lemma progAuxAt_eq_castLE₇ (k₀ : Option ℕ) {p : PD.Prog} (hp : noSelfIdxP p = true) (c : ℕ) :
    progAuxAt k₀ p c = Rew.castLE (by norm_num : 8 ≤ 14) ▹ progAux7At k₀ p c := by
  by_cases h1 : p = .self
  · subst h1
    rw [progAuxAt_self, progAux7At_self, rew_descF]
    simp only [Rew.q_castLE, Rew.castLe_bvar]
    rfl
  by_cases h2 : p = .opp
  · subst h2
    rw [progAuxAt_opp, progAux7At_opp, rew_descF]
    simp only [Rew.q_castLE, Rew.castLe_bvar]
    rfl
  rw [progAuxAt_of_ne _ h1 h2 (pronounP_eq_false_of_noSelfIdxP hp), progAux7At_of_ne _ h1 h2]
  unfold closedDescAt closedDesc7At
  rw [rew_descF, rew_canonicalSlot]
  simp only [Rew.q_castLE, Rew.castLe_bvar, rew_cl]
  rfl

/-- **The seven-variable reading**: on the `noSelfIdx` fragment `templateAt φ k₀` is `template7At φ k₀` cast. -/
theorem templateAt_eq_castLE₇ : ∀ (k₀ : Option ℕ) (φ : PD.Formula), noSelfIdxF φ = true →
    templateAt φ k₀ = Rew.castLE (by norm_num : 7 ≤ 13) ▹ template7At φ k₀
  | k₀, .plays p q a, h => by
    simp only [noSelfIdxF, Bool.and_eq_true] at h
    rw [templateAt_plays, template7At_plays]
    unfold progGraphAt
    simp only [Rewriting.app_exs, Rew.q_castLE, LogicalConnective.HomClass.map_and, rew_subst_eq]
    rw [progAuxAt_eq_castLE₇ _ h.1, progAuxAt_eq_castLE₇ _ h.2, subst_castLE, subst_castLE]
    congr 4
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1
      · congr 1; funext i; fin_cases i <;> rfl
      · congr 1
        funext i
        fin_cases i
        · rfl
        · rfl
        · rfl
        · rfl
        · exact (rew_cl _ _).symm
  | k₀, .impl φ ψ, h => by
    simp only [noSelfIdxF, Bool.and_eq_true] at h
    rw [templateAt_impl, template7At_impl, LogicalConnective.HomClass.map_imply, templateAt_eq_castLE₇ k₀ φ h.1,
      templateAt_eq_castLE₇ k₀ ψ h.2]
  | k₀, .neg φ, h => by
    simp only [noSelfIdxF] at h
    rw [templateAt_neg, template7At_neg, LogicalConnective.HomClass.map_neg, templateAt_eq_castLE₇ k₀ φ h]
  | k₀, .box k ψ, _ => by
    rw [templateAt_box, template7At_box]
    simp only [Rewriting.app_exs, Rew.q_castLE, LogicalConnective.HomClass.map_and, rew_subst_eq]
    rw [progAuxAt_eq_castLE₇ _ (p := .self) rfl, progAuxAt_eq_castLE₇ _ (p := .opp) rfl, subst_castLE, subst_castLE]
    congr 3
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1
      · congr 1; funext i; fin_cases i <;> rfl
      · congr 2
        · congr 1
          funext i
          fin_cases i
          · rfl
          · exact (rew_cl _ _).symm
          · rfl
          · rfl
        · congr 1
          funext i
          fin_cases i
          · exact (rew_cl _ _).symm
          · rfl
  | k₀, .eq p q, h => by
    simp only [noSelfIdxF, Bool.and_eq_true] at h
    rw [templateAt_eq, template7At_eq]
    unfold progGraphAt
    simp only [Rewriting.app_exs, Rew.q_castLE, LogicalConnective.HomClass.map_and, rew_subst_eq]
    rw [progAuxAt_eq_castLE₇ _ h.1, subst_castLE]
    congr 3
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1
      · rw [closedDescAt_subst, closedDesc7At_subst]; rfl
      · rw [Semiformula.rew_rel]
        congr 1
        funext i
        fin_cases i <;> rfl
  | k₀, .diag _ _, _ => by
    rw [templateAt_diag, template7At_diag, LogicalConnective.HomClass.map_bot]

/-- The code of a closed seven-variable semisentence is a seven-variable template. -/
lemma isSemiformula_quote₇ {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (φ : Semisentence LAct 7) :
    IsSemiformula LAct 7 (⌜φ⌝ : V) := by
  simpa using Sentence.quote_isSemiformula (V := V) φ

/-- **Codes do not see the arity, seven to thirteen.** -/
theorem quote_castLE₇ (σ : Semisentence LAct 7) :
    (⌜(Rew.castLE (by norm_num : 7 ≤ 13) ▹ σ : Semisentence LAct 13)⌝ : ℕ) = ⌜σ⌝ := by
  have h713 : (7 : ℕ) ≤ 13 := by norm_num
  have hc : (Rew.castLE h713 : Rew LAct Empty 7 Empty 13) =
      Rew.subst (fun i ↦ (#(Fin.castLE h713 i) : Semiterm LAct Empty 13)) := by
    ext x <;> first | exact x.elim | rfl | simp
  rw [hc]
  change (⌜(σ ⇜ (fun i ↦ (#(Fin.castLE h713 i) : Semiterm LAct Empty 13)) : Semisentence LAct 13)⌝ : ℕ) = _
  rw [quote_subst_gen]
  have hv : (fun i : Fin 7 ↦ (⌜(Rew.emb (#(Fin.castLE h713 i) : Semiterm LAct Empty 13) : SyntacticSemiterm LAct 13)⌝ :
      Bootstrapping.Semiterm ℕ LAct 13)) =
      ![⌜(#0 : SyntacticSemiterm LAct 13)⌝, ⌜(#1 : SyntacticSemiterm LAct 13)⌝, ⌜(#2 : SyntacticSemiterm LAct 13)⌝,
        ⌜(#3 : SyntacticSemiterm LAct 13)⌝, ⌜(#4 : SyntacticSemiterm LAct 13)⌝, ⌜(#5 : SyntacticSemiterm LAct 13)⌝,
        ⌜(#6 : SyntacticSemiterm LAct 13)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil]
  have hid : ((⌜(#0 : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13).val ∷
      (⌜(#1 : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13).val ∷
      (⌜(#2 : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13).val ∷
      (⌜(#3 : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13).val ∷
      (⌜(#4 : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13).val ∷
      (⌜(#5 : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13).val ∷
      (⌜(#6 : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13).val ∷ (0 : ℕ)) = idVec7 := rfl
  rw [hid]
  have hlt : (7 : ℕ) < 13 := by norm_num
  have hvec := idVec7_semitermVec (V := ℕ) (n := 13) (le_def.mpr (Or.inr hlt))
  exact subst_eq_self_of_le (isSemiformula_quote₇ σ) (by rw [hvec.lh]; exact hvec.isUTerm)
    (le_def.mpr (Or.inl hvec.lh.symm)) nth_idVec7

/-- The stored template code is the code of the seven-variable template (`noSelfIdx` fragment). -/
theorem templateCodeAt_eq_quote_template7 (φ : PD.Formula) (k : ℕ) (h : noSelfIdxF φ = true := by noSelfIdx_tac) :
    templateCodeAt φ k = ⌜template7At φ (some k)⌝ := by
  unfold templateCodeAt
  rw [templateAt_eq_castLE₇ _ φ h]
  exact quote_castLE₇ _

theorem templateCode_eq_quote_template7 (φ : PD.Formula) (h : noSelfIdxF φ = true := by noSelfIdx_tac) :
    templateCode φ = ⌜template7At φ none⌝ := by
  unfold templateCode template13
  rw [templateAt_eq_castLE₇ _ φ h]
  exact quote_castLE₇ _

/-- The stored template code is a seven-variable template (`noSelfIdx` fragment). -/
lemma isSemiformula_templateCodeAt₇ (φ : PD.Formula) (k : ℕ) (h : noSelfIdxF φ = true := by noSelfIdx_tac) :
    IsSemiformula LAct 7 (templateCodeAt φ k) := by
  rw [templateCodeAt_eq_quote_template7 φ k h]
  exact isSemiformula_quote₇ _

/-! #### The instantiation lemma -/

lemma progAux7At_budget {m : ℕ} (k : ℕ) (p : PD.Prog) (c : ℕ) (w : Fin 8 → Semiterm LAct Empty m)
    (hw : w 7 = cl (numTB k)) :
    progAux7At (some k) p c ⇜ w = progAux7At none p c ⇜ w := by
  by_cases h1 : p = .self
  · subst h1; rw [progAux7At_self, progAux7At_self]
  by_cases h2 : p = .opp
  · subst h2; rw [progAux7At_opp, progAux7At_opp]
  rw [progAux7At_of_ne _ h1 h2, progAux7At_of_ne _ h1 h2, closedDesc7At_subst, closedDesc7At_subst, hw, rew_cl,
    canonicalSlot_numTB, canonicalSlot_none]

/-- **The instantiation lemma**: with the node's own budget in slot `#6`, the abstracted template is the
unabstracted one. -/
theorem template7At_budget (k : ℕ) : ∀ (φ : PD.Formula) {m : ℕ} (v : Fin 7 → Semiterm LAct Empty m),
    v 6 = cl (numTB k) → template7At φ (some k) ⇜ v = template7At φ none ⇜ v
  | .plays p q a, m, v, hv => by
    rw [template7At_plays, template7At_plays]
    simp only [Rewriting.app_exs, Rew.q_subst, LogicalConnective.HomClass.map_and, rew_subst_eq]
    congr 4
    · exact progAux7At_budget k p _ _
        (by show Rew.bShift (Rew.bShift (Rew.bShift (v 6))) = _; rw [hv, rew_cl, rew_cl, rew_cl])
    · congr 1
      exact progAux7At_budget k q _ _
        (by show Rew.bShift (Rew.bShift (Rew.bShift (v 6))) = _; rw [hv, rew_cl, rew_cl, rew_cl])
  | .impl φ ψ, m, v, hv => by
    rw [template7At_impl, template7At_impl]
    have h1 := template7At_budget k φ v hv
    have h2 := template7At_budget k ψ v hv
    unfold Rewriting.subst at h1 h2 ⊢
    rw [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_imply, h1, h2]
  | .neg φ, m, v, hv => by
    rw [template7At_neg, template7At_neg]
    have h1 := template7At_budget k φ v hv
    unfold Rewriting.subst at h1 ⊢
    rw [LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_neg, h1]
  | .box _ _, m, v, _ => by simp only [template7At_box, progAux7At_self, progAux7At_opp]
  | .eq p q, m, v, hv => by
    rw [template7At_eq, template7At_eq]
    simp only [Rewriting.app_exs, Rew.q_subst, LogicalConnective.HomClass.map_and, rew_subst_eq]
    congr 3
    · exact progAux7At_budget k p _ _
        (by show Rew.bShift (Rew.bShift (v 6)) = _; rw [hv, rew_cl, rew_cl])
    · congr 1
      rw [closedDesc7At_subst, closedDesc7At_subst]
      show descF _ (canonicalSlot (some k) _ (Rew.bShift (Rew.bShift (Rew.bShift (v 6))))) _ _ =
        descF _ (canonicalSlot none _ (Rew.bShift (Rew.bShift (Rew.bShift (v 6))))) _ _
      rw [hv, rew_cl, rew_cl, rew_cl, canonicalSlot_numTB, canonicalSlot_none]
  | .diag _ _, m, v, _ => by rw [template7At_diag, template7At_diag]

/-- A closed term cast to zero bound variables is itself. -/
lemma cl_zero : ∀ t : ClosedSemiterm LAct 0, (cl t : Semiterm LAct Empty 0) = t
  | #x => x.elim0
  | &x => x.elim
  | .func f v => by
    show Rew.castLE _ (Semiterm.func f v) = Semiterm.func f v
    rw [Rew.func]
    congr 1
    funext i
    exact cl_zero (v i)

lemma quote_lMap_emb_binNumeralMeta (k : ℕ) : (⌜Semiterm.lMap emb (binNumeralMeta k)⌝ : ℕ) = binNumeral k := by
  rw [Semiterm.empty_quote_def, term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def,
    quote_binNumeralMeta_nat]

lemma quote_numTB (k : ℕ) : (⌜numTB k⌝ : ℕ) = binNumeral k := quote_lMap_emb_binNumeralMeta k

/-- The seven closed terms the evaluator substitutes: the descriptions of the players and the node budget. -/
noncomputable def descriptionTermsB (me opp k : ℕ) : Fin 7 → ClosedSemiterm LAct 0 :=
  ![canonicalMeta me, revalueUMeta me, revalueWMeta me, canonicalMeta opp, revalueUMeta opp, revalueWMeta opp, numTB k]

lemma semitermVec_val_descriptionTermsB (me opp k : ℕ) :
    SemitermVec.val (fun i ↦ (⌜(Rew.emb (descriptionTermsB me opp k i) : SyntacticSemiterm LAct 0)⌝ :
      Bootstrapping.Semiterm ℕ LAct 0)) = descriptionsB me opp k := by
  have hv : (fun i ↦ (⌜(Rew.emb (descriptionTermsB me opp k i) : SyntacticSemiterm LAct 0)⌝ :
      Bootstrapping.Semiterm ℕ LAct 0)) =
      ![⌜(Rew.emb (canonicalMeta me) : SyntacticSemiterm LAct 0)⌝, ⌜(Rew.emb (revalueUMeta me) : SyntacticSemiterm LAct 0)⌝,
        ⌜(Rew.emb (revalueWMeta me) : SyntacticSemiterm LAct 0)⌝, ⌜(Rew.emb (canonicalMeta opp) : SyntacticSemiterm LAct 0)⌝,
        ⌜(Rew.emb (revalueUMeta opp) : SyntacticSemiterm LAct 0)⌝, ⌜(Rew.emb (revalueWMeta opp) : SyntacticSemiterm LAct 0)⌝,
        ⌜(Rew.emb (numTB k) : SyntacticSemiterm LAct 0)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil, typed_val_emb, quote_canonicalMeta, quote_revalueUMeta,
    quote_revalueWMeta, quote_numTB]
  rfl

/-- `guardCodeB` on the code of a seven-variable sentence is the code of its instance. -/
theorem guardCodeB_quote₇ (σ : Semisentence LAct 7) (me opp k : ℕ) :
    guardCodeB (⌜σ⌝ : ℕ) me opp k = ⌜σ ⇜ descriptionTermsB me opp k⌝ := by
  unfold guardCodeB
  rw [quote_subst_gen, semitermVec_val_descriptionTermsB]

/-- **The evaluator's behaviour is unchanged by the abstraction**: the sentence consulted on the stored
template at the node's budget is the guard of the unabstracted template. -/
theorem guardCodeB_templateCodeAt (φ : PD.Formula) (me opp k : ℕ) (h : noSelfIdxF φ = true := by noSelfIdx_tac) :
    guardCodeB (templateCodeAt φ k) me opp k = guardCode (templateCode φ) me opp := by
  rw [templateCodeAt_eq_quote_template7 φ k h, guardCodeB_quote₇,
    template7At_budget k φ (descriptionTermsB me opp k) (cl_zero _).symm, ← guardCodeB_quote₇,
    ← templateCode_eq_quote_template7 φ h, guardCodeB_of_template (isSemiformula_templateCode φ h)]

/-- **The search clause on a stored template**: the pre-abstraction reading, in every frame. -/
theorem EvalGraph.search_iff_at {n me opp k p q a : ℕ} (φ : PD.Formula) (h : noSelfIdxF φ = true := by noSelfIdx_tac) :
    EvalGraph (n + 1) me opp (pSearch k (templateCodeAt φ k) p q) a ↔
    ((LenBox TAct k (guardCode (templateCode φ) me opp) ∧ EvalGraph n me opp p a) ∨
     (¬LenBox TAct k (guardCode (templateCode φ) me opp) ∧ EvalGraph n me opp q a)) := by
  rw [EvalGraph.search_iff, guardCodeB_templateCodeAt φ me opp k h]

/-! #### Substitution on the seven-variable reading -/

/-- The seven substitution terms of a simulated program's frame: the players' closed descriptions in
`#0..#5`, the budget slot kept. -/
noncomputable def descTerms7 (me opp : PD.Prog) : Fin 7 → Semiterm LAct Empty 7 :=
  ![cl (canonicalMeta (progCode me)), cl (revalueUMeta (progCode me)), cl (revalueWMeta (progCode me)),
    cl (canonicalMeta (progCode opp)), cl (revalueUMeta (progCode opp)), cl (revalueWMeta (progCode opp)), #6]

/-- **Lemma A, seven variables**: substituting the frame descriptions into the description of an atomic program
gives the description of the substituted program — the player's description being abstracted on the right,
the equation needs a search-free player (`searchFreeP`) wherever the atom is that player. -/
lemma progAux7At_subst {m : ℕ} (k₀ : Option ℕ) {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp)
    (hopp : opp ≠ .self ∧ opp ≠ .opp) {p : PD.Prog} (hp : atomicP p = true)
    (hme' : p = .self → searchFreeP me = true) (hopp' : p = .opp → searchFreeP opp = true)
    (w w' : Fin 8 → Semiterm LAct Empty m)
    (h0 : w 0 = w' 0)
    (h1 : w 1 = cl (canonicalMeta (progCode me))) (h2 : w 2 = cl (revalueUMeta (progCode me))) (h3 : w 3 = cl (revalueWMeta (progCode me)))
    (h4 : w 4 = cl (canonicalMeta (progCode opp))) (h5 : w 5 = cl (revalueUMeta (progCode opp))) (h6 : w 6 = cl (revalueWMeta (progCode opp)))
    (h7 : w 7 = w' 7) :
    progAux7At k₀ p (progCode p) ⇜ w = progAux7At k₀ (p.subst me opp) (progCode (p.subst me opp)) ⇜ w' := by
  simp only [atomicP, Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with (rfl | rfl) | hc
  · rw [progAux7At_self, PD.Prog.subst, progAux7At_of_ne _ hme.1 hme.2, closedDesc7At_subst,
      canonicalSlot_progCode_eq (hme' rfl)]
    unfold Rewriting.subst
    rw [rew_descF]
    show descF (Rew.bShift (w 0)) (Rew.bShift (w 1)) (Rew.bShift (w 2)) (Rew.bShift (w 3)) = _
    rw [h0, h1, h2, h3, rew_cl, rew_cl, rew_cl]
  · rw [progAux7At_opp, PD.Prog.subst, progAux7At_of_ne _ hopp.1 hopp.2, closedDesc7At_subst,
      canonicalSlot_progCode_eq (hopp' rfl)]
    unfold Rewriting.subst
    rw [rew_descF]
    show descF (Rew.bShift (w 0)) (Rew.bShift (w 4)) (Rew.bShift (w 5)) (Rew.bShift (w 6)) = _
    rw [h0, h4, h5, h6, rew_cl, rew_cl, rew_cl]
  · rw [subst_of_closedP p me opp hc, progAux7At_of_ne _ (closedP_ne_self hc) (closedP_ne_opp hc),
      closedDesc7At_subst, closedDesc7At_subst, h0, h7]

lemma closedF_or_left {φ ψ : PD.Formula} {R : Prop} (h : closedF (.impl φ ψ) = true ∨ R) : closedF φ = true ∨ R :=
  h.imp_left (fun h' ↦ by simp only [closedF, Bool.and_eq_true] at h'; exact h'.1)
lemma closedF_or_right {φ ψ : PD.Formula} {R : Prop} (h : closedF (.impl φ ψ) = true ∨ R) : closedF ψ = true ∨ R :=
  h.imp_left (fun h' ↦ by simp only [closedF, Bool.and_eq_true] at h'; exact h'.2)
lemma closedF_or_neg {φ : PD.Formula} {R : Prop} (h : closedF (.neg φ) = true ∨ R) : closedF φ = true ∨ R :=
  h.imp_left (fun h' ↦ by simpa only [closedF] using h')
lemma closedF_plays_self {q : PD.Prog} {a : PD.Action} {R : Prop} (h : closedF (.plays .self q a) = true ∨ R) : R :=
  h.resolve_left (by simp [closedF, closedP])
lemma closedF_plays_opp {q : PD.Prog} {a : PD.Action} {R : Prop} (h : closedF (.plays .opp q a) = true ∨ R) : R :=
  h.resolve_left (by simp [closedF, closedP])
lemma closedF_plays_self' {p : PD.Prog} {a : PD.Action} {R : Prop} (h : closedF (.plays p .self a) = true ∨ R) : R :=
  h.resolve_left (by simp [closedF, closedP])
lemma closedF_plays_opp' {p : PD.Prog} {a : PD.Action} {R : Prop} (h : closedF (.plays p .opp a) = true ∨ R) : R :=
  h.resolve_left (by simp [closedF, closedP])
lemma closedF_eq_self {q : PD.Prog} {R : Prop} (h : closedF (.eq .self q) = true ∨ R) : R :=
  h.resolve_left (by simp [closedF, closedP])
lemma closedF_eq_opp {q : PD.Prog} {R : Prop} (h : closedF (.eq .opp q) = true ∨ R) : R :=
  h.resolve_left (by simp [closedF, closedP])

/-- **The meta substitution equation on the seven-variable reading**: on the fragment, with players whose
descriptions the abstraction does not touch (search-free) — or on a CLOSED formula, for any players. -/
theorem template7At_subst {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp) (hopp : opp ≠ .self ∧ opp ≠ .opp)
    (k₀ : Option ℕ) :
    ∀ ψ : PD.Formula, fragF ψ = true → (closedF ψ = true ∨ searchFreeP me = true) →
      (closedF ψ = true ∨ searchFreeP opp = true) →
      template7At (ψ.subst me opp) k₀ = template7At ψ k₀ ⇜ descTerms7 me opp
  | .plays p q a, h, hm, ho => by
    simp only [fragF, Bool.and_eq_true] at h
    rw [PD.Formula.subst, template7At_plays, template7At_plays]
    simp only [Rewriting.app_exs, Rew.q_subst, LogicalConnective.HomClass.map_and, rew_subst_eq]
    congr 4
    · refine (progAux7At_subst k₀ hme hopp h.1.1.1 (fun hs ↦ ?_) (fun hs ↦ ?_) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).symm
      · subst hs; exact closedF_plays_self hm
      · subst hs; exact closedF_plays_opp ho
      · rfl
      all_goals (first
        | (show Rew.bShift (Rew.bShift (Rew.bShift (cl _))) = _; rw [rew_cl, rew_cl, rew_cl]; try rfl)
        | rfl)
    · congr 1
      · refine (progAux7At_subst k₀ hme hopp h.1.2 (fun hs ↦ ?_) (fun hs ↦ ?_) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).symm
        · subst hs; exact closedF_plays_self' hm
        · subst hs; exact closedF_plays_opp' ho
        · rfl
        all_goals (first
          | (show Rew.bShift (Rew.bShift (Rew.bShift (cl _))) = _; rw [rew_cl, rew_cl, rew_cl]; try rfl)
          | rfl)
      · congr 1
        funext i
        fin_cases i
        · rfl
        · rfl
        · rfl
        · rfl
        · exact (rew_cl _ _).symm
  | .impl φ ψ, h, hm, ho => by
    simp only [fragF, Bool.and_eq_true] at h
    rw [PD.Formula.subst, template7At_impl, template7At_impl,
      template7At_subst hme hopp k₀ φ h.1 (closedF_or_left hm) (closedF_or_left ho),
      template7At_subst hme hopp k₀ ψ h.2 (closedF_or_right hm) (closedF_or_right ho)]
    unfold Rewriting.subst
    rw [LogicalConnective.HomClass.map_imply]
  | .neg φ, h, hm, ho => by
    simp only [fragF] at h
    rw [PD.Formula.subst, template7At_neg, template7At_neg,
      template7At_subst hme hopp k₀ φ h (closedF_or_neg hm) (closedF_or_neg ho)]
    unfold Rewriting.subst
    rw [LogicalConnective.HomClass.map_neg]
  | .box _ _, h, _, _ => by simp [fragF] at h
  | .eq p q, h, hm, ho => by
    simp only [fragF, Bool.and_eq_true] at h
    rw [PD.Formula.subst, template7At_eq, template7At_eq]
    simp only [Rewriting.app_exs, Rew.q_subst, LogicalConnective.HomClass.map_and, rew_subst_eq]
    congr 3
    · refine (progAux7At_subst k₀ hme hopp h.1.1 (fun hs ↦ ?_) (fun hs ↦ ?_) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).symm
      · subst hs; exact closedF_eq_self hm
      · subst hs; exact closedF_eq_opp ho
      · rfl
      all_goals (first
        | (show Rew.bShift (Rew.bShift (cl _)) = _; rw [rew_cl, rew_cl]; try rfl)
        | rfl)
    · congr 1
      · rw [closedDesc7At_subst, closedDesc7At_subst]; rfl
      · rw [Semiformula.rew_rel]
        congr 1
        funext i
        fin_cases i <;> rfl
  | .diag _ _, _, _, _ => by
    simp only [PD.Formula.subst, template7At_diag]
    unfold Rewriting.subst
    rw [LogicalConnective.HomClass.map_bot]

lemma quote_emb_bvar7_six : (⌜(Rew.emb (#6 : Semiterm LAct Empty 7) : SyntacticSemiterm LAct 7)⌝ : ℕ) = ^#6 := by
  simp [Rew.emb]

/-- The codes of `descTerms7` form the kept-slot vector `descriptionsSlot`. -/
lemma semitermVec_val_descTerms7 (me opp : PD.Prog) :
    SemitermVec.val (fun i ↦ (⌜(Rew.emb (descTerms7 me opp i) : SyntacticSemiterm LAct 7)⌝ : Bootstrapping.Semiterm ℕ LAct 7)) =
      descriptionsSlot (progCode me) (progCode opp) := by
  have e : ∀ t : Semiterm LAct Empty 7,
      ((⌜(Rew.emb t : SyntacticSemiterm LAct 7)⌝ : Bootstrapping.Semiterm ℕ LAct 7)).val =
        (⌜(Rew.emb t : SyntacticSemiterm LAct 7)⌝ : ℕ) := fun _ ↦ rfl
  have hv : (fun i ↦ (⌜(Rew.emb (descTerms7 me opp i) : SyntacticSemiterm LAct 7)⌝ : Bootstrapping.Semiterm ℕ LAct 7)) =
      ![⌜(Rew.emb (cl (canonicalMeta (progCode me))) : SyntacticSemiterm LAct 7)⌝,
        ⌜(Rew.emb (cl (revalueUMeta (progCode me))) : SyntacticSemiterm LAct 7)⌝,
        ⌜(Rew.emb (cl (revalueWMeta (progCode me))) : SyntacticSemiterm LAct 7)⌝,
        ⌜(Rew.emb (cl (canonicalMeta (progCode opp))) : SyntacticSemiterm LAct 7)⌝,
        ⌜(Rew.emb (cl (revalueUMeta (progCode opp))) : SyntacticSemiterm LAct 7)⌝,
        ⌜(Rew.emb (cl (revalueWMeta (progCode opp))) : SyntacticSemiterm LAct 7)⌝,
        ⌜(Rew.emb (#6 : Semiterm LAct Empty 7) : SyntacticSemiterm LAct 7)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil, e]
  simp only [quote_emb_cl, quote_emb_bvar7_six]
  simp only [← Semiterm.empty_quote_def, quote_canonicalMeta, quote_revalueUMeta, quote_revalueWMeta]
  rfl

/-- **The stored template code equation**: on the fragment, the stored template of a substituted formula is the
stored template of the formula instantiated by `substTemplate` (= `guardCodeSlot`: the players' descriptions
in `#0..#5`, the budget slot kept for the running node) — for search-free players, or for a closed formula. -/
theorem templateCodeAt_subst {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp) (hopp : opp ≠ .self ∧ opp ≠ .opp)
    (hme' : noSelfIdxP me = true) (hopp' : noSelfIdxP opp = true)
    (ψ : PD.Formula) (h : fragF ψ = true) (hm : closedF ψ = true ∨ searchFreeP me = true)
    (ho : closedF ψ = true ∨ searchFreeP opp = true) (k : ℕ) :
    templateCodeAt (ψ.subst me opp) k = substTemplate (progCode me) (progCode opp) (templateCodeAt ψ k) := by
  have hψ := noSelfIdxF_of_fragF ψ h
  rw [substTemplate_eq_guardCodeSlot (isSemiformula_templateCodeAt₇ ψ k hψ),
    templateCodeAt_eq_quote_template7 _ k (noSelfIdxF_subst ψ me opp hψ hme' hopp'),
    template7At_subst hme hopp (some k) ψ h hm ho, quote_subst_gen, semitermVec_val_descTerms7,
    templateCodeAt_eq_quote_template7 ψ k hψ]
  rfl

/-- **The template code equation**: on the fragment, the template code of a substituted
formula is the stored template instantiated by `substTemplate` (= `guardCode`) with the players'
codes — exactly what `substCode` does at a search node. -/
theorem templateCode_subst {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp) (hopp : opp ≠ .self ∧ opp ≠ .opp)
    (hme' : noSelfIdxP me = true) (hopp' : noSelfIdxP opp = true)
    (ψ : PD.Formula) (h : fragF ψ = true) :
    templateCode (ψ.subst me opp) = substTemplate (progCode me) (progCode opp) (templateCode ψ) := by
  have hψ := noSelfIdxF_of_fragF ψ h
  rw [substTemplate_of_template (isSemiformula_templateCode ψ hψ), ← quote_sentenceAt me opp ψ hψ,
    templateCode_eq_quote_template _ (noSelfIdxF_subst ψ me opp hψ hme' hopp')]
  unfold sentenceAt
  rw [template_subst hme hopp ψ h]
  exact quote_subst_cl _ _

/-- **The program code equation**: on the fragment, the code of a substituted program is the
code-level substitution of the players' codes — for SEARCH-FREE players (`searchFreeP`): a budget-carrying
player substituted into a stored template is described abstractly by the engine's `subst` and verbatim by
`substCode`, two codes for one sentence (`progCode_subst_closed` covers closed bodies for any players). -/
theorem progCode_subst {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp) (hopp : opp ≠ .self ∧ opp ≠ .opp)
    (hme' : noSelfIdxP me = true) (hopp' : noSelfIdxP opp = true)
    (hsm : searchFreeP me = true) (hso : searchFreeP opp = true) :
    ∀ p : PD.Prog, fragP p = true → progCode (p.subst me opp) = substCode (progCode me) (progCode opp) (progCode p)
  | .const _, _ => by simp [PD.Prog.subst]
  | .self, _ => by simp [PD.Prog.subst]
  | .opp, _ => by simp [PD.Prog.subst]
  | .bot _, _ => by simp [PD.Prog.subst]
  | .sim p q, h => by
    simp only [fragP, Bool.and_eq_true] at h
    simp [PD.Prog.subst, progCode_subst hme hopp hme' hopp' hsm hso p h.1, progCode_subst hme hopp hme' hopp' hsm hso q h.2]
  | .ite b _ p q, h => by
    simp only [fragP, Bool.and_eq_true] at h
    simp [PD.Prog.subst, progCode_subst hme hopp hme' hopp' hsm hso b h.1.1, progCode_subst hme hopp hme' hopp' hsm hso p h.1.2,
      progCode_subst hme hopp hme' hopp' hsm hso q h.2]
  | .search k φ p q, h => by
    simp only [fragP, Bool.and_eq_true] at h
    simp [PD.Prog.subst, progCode_subst hme hopp hme' hopp' hsm hso p h.1.2, progCode_subst hme hopp hme' hopp' hsm hso q h.2,
      templateCodeAt_subst hme hopp hme' hopp' φ h.1.1 (Or.inr hsm) (Or.inr hso) k]
  | .tvote _ _ _ _, h => by simp [fragP] at h
  | .sys _ _, h => by simp [fragP] at h
  | .selfIdx _, h => by simp [fragP] at h

/-- The program code equation on a CLOSED body (any proper players): `substCode` fixes it, as `subst` does. -/
theorem progCode_subst_closed {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp) (hopp : opp ≠ .self ∧ opp ≠ .opp)
    (hme' : noSelfIdxP me = true) (hopp' : noSelfIdxP opp = true) :
    ∀ p : PD.Prog, fragP p = true → closedP p = true →
      progCode (p.subst me opp) = substCode (progCode me) (progCode opp) (progCode p)
  | .const _, _, _ => by simp [PD.Prog.subst]
  | .self, _, hc => by simp [closedP] at hc
  | .opp, _, hc => by simp [closedP] at hc
  | .bot _, _, _ => by simp [PD.Prog.subst]
  | .sim p q, h, hc => by
    simp only [fragP, Bool.and_eq_true] at h
    simp only [closedP, Bool.and_eq_true] at hc
    simp [PD.Prog.subst, progCode_subst_closed hme hopp hme' hopp' p h.1 hc.1, progCode_subst_closed hme hopp hme' hopp' q h.2 hc.2]
  | .ite b _ p q, h, hc => by
    simp only [fragP, Bool.and_eq_true] at h
    simp only [closedP, Bool.and_eq_true] at hc
    simp [PD.Prog.subst, progCode_subst_closed hme hopp hme' hopp' b h.1.1 hc.1.1,
      progCode_subst_closed hme hopp hme' hopp' p h.1.2 hc.1.2, progCode_subst_closed hme hopp hme' hopp' q h.2 hc.2]
  | .search k φ p q, h, hc => by
    simp only [fragP, Bool.and_eq_true] at h
    simp only [closedP, Bool.and_eq_true] at hc
    simp [PD.Prog.subst, progCode_subst_closed hme hopp hme' hopp' p h.1.2 hc.1.2,
      progCode_subst_closed hme hopp hme' hopp' q h.2 hc.2,
      templateCodeAt_subst hme hopp hme' hopp' φ h.1.1 (Or.inl hc.1.1) (Or.inl hc.1.1) k]
  | .tvote _ _ _ _, h, _ => by simp [fragP] at h
  | .sys _ _, h, _ => by simp [fragP] at h
  | .selfIdx _, h, _ => by simp [fragP] at h

/-- The program code equation on an ATOMIC body — a placeholder or a closed program, the arguments of a `.sim`
in a modest program — for any proper players. -/
theorem progCode_subst_atomic {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp) (hopp : opp ≠ .self ∧ opp ≠ .opp)
    (hme' : noSelfIdxP me = true) (hopp' : noSelfIdxP opp = true) (p : PD.Prog) (hp : fragP p = true)
    (ha : atomicP p = true) : progCode (p.subst me opp) = substCode (progCode me) (progCode opp) (progCode p) := by
  simp only [atomicP, Bool.or_eq_true, beq_iff_eq] at ha
  rcases ha with (rfl | rfl) | hc
  · simp [PD.Prog.subst]
  · simp [PD.Prog.subst]
  · exact progCode_subst_closed hme hopp hme' hopp' p hp hc

/-! ### τ -/

lemma transpose_ne_self {p : PD.Prog} (h : p ≠ .self) : p.transpose ≠ .self := by
  cases p <;> simp_all [PD.Prog.transpose]
lemma transpose_ne_opp {p : PD.Prog} (h : p ≠ .opp) : p.transpose ≠ .opp := by
  cases p <;> simp_all [PD.Prog.transpose]

lemma lMap_swap_closedDesc (c : ℕ) : Semiformula.lMap swap (closedDesc c) = closedDesc (transposeCode c) := by
  unfold closedDesc
  rw [lMap_swap_descF, lMap_swap_cl, lMap_swap_cl, lMap_swap_cl, lMap_swap_canonicalMeta, lMap_swap_revalueUMeta, lMap_swap_revalueWMeta]
  rfl

lemma lMap_swap_closedDescAt (k₀ : Option ℕ) (c : ℕ) :
    Semiformula.lMap swap (closedDescAt k₀ c) = closedDescAt k₀ (transposeCode c) := by
  unfold closedDescAt
  rw [lMap_swap_descF, lMap_swap_canonicalSlot, lMap_swap_cl, lMap_swap_cl, lMap_swap_revalueUMeta, lMap_swap_revalueWMeta]
  rfl

lemma lMap_swap_closedDesc13 (c : ℕ) : Semiformula.lMap swap (closedDesc13 c) = closedDesc13 (transposeCode c) :=
  lMap_swap_closedDescAt none c

lemma lMap_swap_progAux {p : PD.Prog} (h : transposeCode (progCode p) = progCode p.transpose) :
    Semiformula.lMap swap (progAux p (progCode p)) = progAux p.transpose (progCode p.transpose) := by
  by_cases h1 : p = .self
  · subst h1
    rw [show PD.Prog.transpose .self = .self from rfl]
    simp only [progAux_self]
    rw [lMap_swap_descF]; rfl
  by_cases h2 : p = .opp
  · subst h2
    rw [show PD.Prog.transpose .opp = .opp from rfl]
    simp only [progAux_opp]
    rw [lMap_swap_descF]; rfl
  rw [progAux_of_ne h1 h2, progAux_of_ne (transpose_ne_self h1) (transpose_ne_opp h2), lMap_swap_closedDesc, h]

lemma pronounP_transpose (p : PD.Prog) : pronounP p.transpose = pronounP p := by
  cases p
  case selfIdx j => rfl
  case bot q => cases q <;> rfl
  all_goals rfl

/-- τ on the thirteen-variable description of a pronoun-free program (its code transposes). -/
lemma lMap_swap_progAuxAt (k₀ : Option ℕ) {p : PD.Prog} (hp : noSelfIdxP p = true)
    (h : transposeCode (progCode p) = progCode p.transpose) :
    Semiformula.lMap swap (progAuxAt k₀ p (progCode p)) = progAuxAt k₀ p.transpose (progCode p.transpose) := by
  by_cases h1 : p = .self
  · subst h1
    rw [show PD.Prog.transpose .self = .self from rfl, progAuxAt_self, lMap_swap_descF]; rfl
  by_cases h2 : p = .opp
  · subst h2
    rw [show PD.Prog.transpose .opp = .opp from rfl, progAuxAt_opp, lMap_swap_descF]; rfl
  rw [progAuxAt_of_ne _ h1 h2 (pronounP_eq_false_of_noSelfIdxP hp),
    progAuxAt_of_ne _ (transpose_ne_self h1) (transpose_ne_opp h2)
      (by rw [pronounP_transpose]; exact pronounP_eq_false_of_noSelfIdxP hp),
    lMap_swap_closedDescAt, h]

mutual
  /-- **τ on the stored templates**: the transposition of the template at the node budget is the template of the
  transposed formula at the same budget (fragment; the abstraction commutes with τ since `canonical` is
  τ-invariant). -/
  theorem lMap_swap_templateAt : ∀ (k₀ : Option ℕ) (φ : PD.Formula), fragF φ = true →
      Semiformula.lMap swap (templateAt φ k₀) = templateAt φ.transpose k₀
    | k₀, .plays p q a, h => by
      simp only [fragF, Bool.and_eq_true] at h
      rw [PD.Formula.transpose, templateAt_plays, templateAt_plays]
      unfold progGraphAt
      simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
        lMap_swap_evalG, lMap_swap_progAuxAt k₀ (noSelfIdxP_of_fragP p h.1.1.2) (transposeCode_progCode p h.1.1.2),
        lMap_swap_progAuxAt k₀ (noSelfIdxP_of_fragP q h.2) (transposeCode_progCode q h.2)]
      congr 4
      · congr 1; funext i; fin_cases i <;> rfl
      · congr 1
        · congr 1; funext i; fin_cases i <;> rfl
        · congr 1
          funext i
          fin_cases i
          · rfl
          · rfl
          · rfl
          · rfl
          · show Semiterm.lMap swap (cl (actT (actCode a))) = cl (actT (actCode a.swap))
            rw [lMap_swap_cl, lMap_swap_actT, actCode_swap]
    | k₀, .impl φ ψ, h => by
      simp only [fragF, Bool.and_eq_true] at h
      rw [PD.Formula.transpose, templateAt_impl, templateAt_impl, LogicalConnective.HomClass.map_imply,
        lMap_swap_templateAt k₀ φ h.1, lMap_swap_templateAt k₀ ψ h.2]
    | k₀, .neg φ, h => by
      simp only [fragF] at h
      rw [PD.Formula.transpose, templateAt_neg, templateAt_neg, LogicalConnective.HomClass.map_neg,
        lMap_swap_templateAt k₀ φ h]
    | _, .box _ _, h => by simp [fragF] at h
    | k₀, .eq p q, h => by
      simp only [fragF, Bool.and_eq_true] at h
      rw [PD.Formula.transpose, templateAt_eq, templateAt_eq]
      unfold progGraphAt
      simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
        lMap_swap_progAuxAt k₀ (noSelfIdxP_of_fragP p h.1.2) (transposeCode_progCode p h.1.2), lMap_swap_closedDescAt,
        transposeCode_progCode q h.2, Semiformula.lMap_rel]
      congr 3
      · congr 1; funext i; fin_cases i <;> rfl
      · congr 1
        · congr 1; funext i; fin_cases i <;> rfl
        · show FirstOrder.Semiformula.rel _ (Semiterm.lMap swap ∘ ![#1, #0]) = _
          congr 1; funext i; fin_cases i <;> rfl
    | k₀, .diag _ _, _ => by
      rw [PD.Formula.transpose, templateAt_diag, templateAt_diag, LogicalConnective.HomClass.map_bot]
  /-- **τ on program codes**: the code-level transposition of a program's code is the code of
  the engine's transposed program (fragment). -/
  theorem transposeCode_progCode : ∀ p : PD.Prog, fragP p = true → transposeCode (progCode p) = progCode p.transpose
    | .const a, _ => by simp [PD.Prog.transpose, transposeCode, actCode_swap]
    | .self, _ => by simp [PD.Prog.transpose, transposeCode]
    | .opp, _ => by simp [PD.Prog.transpose, transposeCode]
    | .bot p, h => by
      simp only [fragP] at h
      simp [PD.Prog.transpose, transposeCode, transposeCode_progCode p h]
    | .sim p q, h => by
      simp only [fragP, Bool.and_eq_true] at h
      simp [PD.Prog.transpose, transposeCode, transposeCode_progCode p h.1, transposeCode_progCode q h.2]
    | .ite b a p q, h => by
      simp only [fragP, Bool.and_eq_true] at h
      simp [PD.Prog.transpose, transposeCode, transposeCode_progCode b h.1.1, transposeCode_progCode p h.1.2, transposeCode_progCode q h.2,
        actCode_swap]
    | .search k φ p q, h => by
      simp only [fragP, Bool.and_eq_true] at h
      simp only [PD.Prog.transpose, progCode_search, transposeCode, revalue_search, transposeCode_progCode p h.1.2,
        transposeCode_progCode q h.2]
      unfold templateCodeAt
      rw [revalueTemplate_quote_sentence, lMap_swap_templateAt (some k) φ h.1.1]
    | .tvote _ _ _ _, h => by simp [fragP] at h
    | .sys _ _, h => by simp [fragP] at h
    | .selfIdx _, h => by simp [fragP] at h
end

/-- **τ on the six-variable templates**: the transposition of the template is the template of the transposed
formula (fragment). -/
theorem lMap_swap_template : ∀ φ : PD.Formula, fragF φ = true →
    Semiformula.lMap swap (template φ) = template φ.transpose
  | .plays p q a, h => by
    simp only [fragF, Bool.and_eq_true] at h
    rw [PD.Formula.transpose, template_plays, template_plays]
    unfold progGraph
    simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
      lMap_swap_evalG, lMap_swap_progAux (transposeCode_progCode p h.1.1.2), lMap_swap_progAux (transposeCode_progCode q h.2)]
    congr 4
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1
      · congr 1; funext i; fin_cases i <;> rfl
      · congr 1
        funext i
        fin_cases i
        · rfl
        · rfl
        · rfl
        · rfl
        · show Semiterm.lMap swap (cl (actT (actCode a))) = cl (actT (actCode a.swap))
          rw [lMap_swap_cl, lMap_swap_actT, actCode_swap]
  | .impl φ ψ, h => by
    simp only [fragF, Bool.and_eq_true] at h
    rw [PD.Formula.transpose, template_impl, template_impl, LogicalConnective.HomClass.map_imply,
      lMap_swap_template φ h.1, lMap_swap_template ψ h.2]
  | .neg φ, h => by
    simp only [fragF] at h
    rw [PD.Formula.transpose, template_neg, template_neg, LogicalConnective.HomClass.map_neg, lMap_swap_template φ h]
  | .box _ _, h => by simp [fragF] at h
  | .eq p q, h => by
    simp only [fragF, Bool.and_eq_true] at h
    rw [PD.Formula.transpose, template_eq, template_eq]
    unfold progGraph
    simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
      lMap_swap_progAux (transposeCode_progCode p h.1.2), lMap_swap_closedDesc, transposeCode_progCode q h.2,
      Semiformula.lMap_rel]
    congr 3
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1
      · congr 1; funext i; fin_cases i <;> rfl
      · show FirstOrder.Semiformula.rel _ (Semiterm.lMap swap ∘ ![#1, #0]) = _
        congr 1; funext i; fin_cases i <;> rfl
  | .diag _ _, _ => by
    rw [PD.Formula.transpose, template_diag, template_diag, LogicalConnective.HomClass.map_bot]

/-- **τ on template codes** (fragment). -/
theorem revalueTemplate_templateCode (φ : PD.Formula) (h : fragF φ = true) :
    revalueTemplate 1 0 (templateCode φ) = templateCode φ.transpose := by
  unfold templateCode template13
  rw [revalueTemplate_quote_sentence, lMap_swap_templateAt none φ h]

/-- **τ on the stored template codes** (fragment). -/
theorem revalueTemplate_templateCodeAt (φ : PD.Formula) (k : ℕ) (h : fragF φ = true) :
    revalueTemplate 1 0 (templateCodeAt φ k) = templateCodeAt φ.transpose k := by
  unfold templateCodeAt
  rw [revalueTemplate_quote_sentence, lMap_swap_templateAt (some k) φ h]

/-! ### Sanity: the engine's `DupocBot`

`progCode (DupocBot k)` is a searcher of budget `k` on the template of `.plays .opp .self .C` with
the constant branches `C`/`D`; it is in the fragment. Its stored template is NOT literally
`⌜guardTemplate 0⌝` (the hand-written template of `ArithS.RedCell`): `template` quantifies the two
program codes and the fuel in the order `x y n` and describes each player through the
uniform shape `descF`, whereas `guardTemplate7` reconstructs `me`/`opp` and then quantifies the fuel.
The two guard sentences say the same thing (both are "opp plays `C` against me"); `Dupoc k`
and `progCode (DupocBot k)` are two different searchers with provably equivalent guards, not one
code. -/
theorem progCode_DupocBot (k : ℕ) :
    progCode (PD.Bots.DupocBot k) = pSearch k (templateCode (.plays .opp .self .C)) (pConst 0) (pConst 1) := by
  rw [PD.Bots.DupocBot, progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

theorem noBudgetSnapshotP_DupocBot (k : ℕ) : noBudgetSnapshotP (PD.Bots.DupocBot k) = true := rfl

theorem fragP_DupocBot (k : ℕ) : fragP (PD.Bots.DupocBot k) = true := rfl
theorem noSelfIdxP_DupocBot (k : ℕ) : noSelfIdxP (PD.Bots.DupocBot k) = true := rfl

theorem transposeCode_progCode_DupocBot (k : ℕ) :
    transposeCode (progCode (PD.Bots.DupocBot k)) = progCode (PD.Bots.DupocBot k).transpose :=
  transposeCode_progCode _ (fragP_DupocBot k)

end ArithS
