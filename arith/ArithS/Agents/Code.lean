import ArithS.Agents.Template
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
  search-bot fragment only. **What is NOT here (the open item of §2.5 of the phase note):** `template`
  keeps its six variables, so the pronoun `.selfIdx j` inside a member's guard is described LITERALLY —
  `progAux (.selfIdx j) _ = closedDesc (pSelfIdx j)`, the dangling code — and not through member slots
  `#7+3j..`; `sysCloseTemplate` (which fills those slots) is the identity on every compiled template. The
  pronoun reading requires widening the arity of `template`, `progAux`, `closedDesc` and `sentenceAt`.

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

**Reading guide.** Definition: `actCode`, `progCode` and `template` (§The translation) — the bridge from the engine's `Prog`/`Formula` to codes and templates; `sentenceAt` is the closed guard sentence of a pair. Facts: the description lemma, the substitution equation (`progCode_subst`), τ, and the sanity checks on the engine's `DupocBot`. §The Σ₁ graphs over `LAct` and §The description shape are plumbing for the translation — skip on first reading. At ℕ: `progCode_subst` (`ArithS.Readings`).
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
    | .search k φ p q => pSearch k (⌜template φ⌝ : ℕ) (progCode p) (progCode q)
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
  /-- The six-variable template of a formula. -/
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
            (∃¹ ((guardCodeG ⇜ ![#0, cl (numTB (⌜template ψ⌝ : ℕ)), #2, #1]) ⋏
              (lenProvG ⇜ ![cl (numTB k), #0]))))))
    | .eq p q =>
        ∃¹ (∃¹ ((progAux p (progCode p) ⇜ ![#1, #2, #3, #4, #5, #6, #7]) ⋏
          ((closedDesc (progCode q) ⇜ ![#0, #2, #3, #4, #5, #6, #7]) ⋏
            Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#1, #0])))
    | .diag _ _ => ⊥
end

/-- The template code. -/
noncomputable def templateCode (φ : PD.Formula) : ℕ := ⌜template φ⌝

/-- The description of `p` in the frame. -/
noncomputable def progGraph (p : PD.Prog) : Semisentence LAct 7 := progAux p (progCode p)

@[simp] lemma progCode_const (a) : progCode (.const a) = pConst (actCode a) := by rw [progCode]
@[simp] lemma progCode_self : progCode .self = pSelf := by rw [progCode]
@[simp] lemma progCode_opp : progCode .opp = pOpp := by rw [progCode]
@[simp] lemma progCode_bot (p) : progCode (.bot p) = pBot (progCode p) := by rw [progCode]
@[simp] lemma progCode_sim (p q) : progCode (.sim p q) = pSim (progCode p) (progCode q) := by rw [progCode]
@[simp] lemma progCode_ite (b a p q) : progCode (.ite b a p q) = pIte (progCode b) (actCode a) (progCode p) (progCode q) := by
  rw [progCode]
@[simp] lemma progCode_search (k φ p q) : progCode (.search k φ p q) = pSearch k (templateCode φ) (progCode p) (progCode q) := by
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
  rw [template]; rfl
lemma template_eq (p q) : template (.eq p q) =
    ∃¹ (∃¹ ((progGraph p ⇜ ![#1, #2, #3, #4, #5, #6, #7]) ⋏
      ((closedDesc (progCode q) ⇜ ![#0, #2, #3, #4, #5, #6, #7]) ⋏
        Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#1, #0]))) := by
  rw [template]; rfl
lemma template_diag (g φ) : template (.diag g φ) = ⊥ := by rw [template]

/-- The template code is a six-variable formula code. -/
lemma isSemiformula_templateCode (φ : PD.Formula) : IsSemiformula LAct 6 (templateCode φ) := by
  have := Semiformula.quote_isSemiformula (V := ℕ) (Rewriting.emb (template φ) : Semiproposition LAct 6)
  rw [natCast_nat] at this
  exact this

/-- The sentence "`φ` at the players `me`, `opp`": the template filled with the closed
descriptions of their codes — the atom realization T2-AGENT uses. -/
noncomputable def sentenceAt (me opp : PD.Prog) (φ : PD.Formula) : Sentence LAct :=
  template φ ⇜ descriptionTerms (progCode me) (progCode opp)

/-- The code of `sentenceAt` is the guard code of the template code (the `quote_guardSentence`
argument, for every formula). -/
theorem quote_sentenceAt (me opp : PD.Prog) (φ : PD.Formula) :
    (⌜sentenceAt me opp φ⌝ : ℕ) = guardCode (templateCode φ) (progCode me) (progCode opp) := by
  unfold sentenceAt guardCode templateCode
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1
  exact semitermVec_val_descriptionTerms _ _

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

/-- **The template code equation**: on the fragment, the template code of a substituted
formula is the stored template instantiated by `substTemplate` (= `guardCode`) with the players'
codes — exactly what `substCode` does at a search node. -/
theorem templateCode_subst {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp) (hopp : opp ≠ .self ∧ opp ≠ .opp)
    (ψ : PD.Formula) (h : fragF ψ = true) :
    templateCode (ψ.subst me opp) = substTemplate (progCode me) (progCode opp) (templateCode ψ) := by
  rw [substTemplate_of_template (isSemiformula_templateCode ψ), ← quote_sentenceAt]
  unfold templateCode sentenceAt
  rw [template_subst hme hopp ψ h]
  exact quote_subst_cl _ _

/-- **The program code equation**: on the fragment, the code of a substituted program is the
code-level substitution of the players' codes. -/
theorem progCode_subst {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp) (hopp : opp ≠ .self ∧ opp ≠ .opp) :
    ∀ p : PD.Prog, fragP p = true → progCode (p.subst me opp) = substCode (progCode me) (progCode opp) (progCode p)
  | .const _, _ => by simp [PD.Prog.subst]
  | .self, _ => by simp [PD.Prog.subst]
  | .opp, _ => by simp [PD.Prog.subst]
  | .bot _, _ => by simp [PD.Prog.subst]
  | .sim p q, h => by
    simp only [fragP, Bool.and_eq_true] at h
    simp [PD.Prog.subst, progCode_subst hme hopp p h.1, progCode_subst hme hopp q h.2]
  | .ite b _ p q, h => by
    simp only [fragP, Bool.and_eq_true] at h
    simp [PD.Prog.subst, progCode_subst hme hopp b h.1.1, progCode_subst hme hopp p h.1.2, progCode_subst hme hopp q h.2]
  | .search _ φ p q, h => by
    simp only [fragP, Bool.and_eq_true] at h
    simp [PD.Prog.subst, progCode_subst hme hopp p h.1.2, progCode_subst hme hopp q h.2, templateCode_subst hme hopp φ h.1.1]
  | .tvote _ _ _ _, h => by simp [fragP] at h
  | .sys _ _, h => by simp [fragP] at h
  | .selfIdx _, h => by simp [fragP] at h

/-! ### τ -/

lemma transpose_ne_self {p : PD.Prog} (h : p ≠ .self) : p.transpose ≠ .self := by
  cases p <;> simp_all [PD.Prog.transpose]
lemma transpose_ne_opp {p : PD.Prog} (h : p ≠ .opp) : p.transpose ≠ .opp := by
  cases p <;> simp_all [PD.Prog.transpose]

lemma lMap_swap_closedDesc (c : ℕ) : Semiformula.lMap swap (closedDesc c) = closedDesc (transposeCode c) := by
  unfold closedDesc
  rw [lMap_swap_descF, lMap_swap_cl, lMap_swap_cl, lMap_swap_cl, lMap_swap_canonicalMeta, lMap_swap_revalueUMeta, lMap_swap_revalueWMeta]
  rfl

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

mutual
  /-- **τ on templates**: the transposition of the template is the template of the transposed
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
      unfold templateCode
      rw [revalueTemplate_quote_sentence, lMap_swap_template φ h.1.1]
    | .tvote _ _ _ _, h => by simp [fragP] at h
    | .sys _ _, h => by simp [fragP] at h
    | .selfIdx _, h => by simp [fragP] at h
end

/-- **τ on template codes** (fragment). -/
theorem revalueTemplate_templateCode (φ : PD.Formula) (h : fragF φ = true) :
    revalueTemplate 1 0 (templateCode φ) = templateCode φ.transpose := by
  unfold templateCode
  rw [revalueTemplate_quote_sentence, lMap_swap_template φ h]

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
  simp [PD.Bots.DupocBot, actCode]

theorem fragP_DupocBot (k : ℕ) : fragP (PD.Bots.DupocBot k) = true := rfl

theorem transposeCode_progCode_DupocBot (k : ℕ) :
    transposeCode (progCode (PD.Bots.DupocBot k)) = progCode (PD.Bots.DupocBot k).transpose :=
  transposeCode_progCode _ (fragP_DupocBot k)

end ArithS
