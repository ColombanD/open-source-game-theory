import ArithS.Template
import ArithS.SimTest
import PrisonersDilemma.Base.Transpose
import PrisonersDilemma.Bots.DupocBot

/-!
# ArithS.Code — the code translation of the engine's programs and formulas (roadmap M3, step (c))

`pcode : PD.Prog → ℕ` sends an engine program to its HFS pair-code (`ArithS.Prog`), and
`tmpl : PD.Formula → Semisentence LAct 6` sends an engine formula to a SIX-VARIABLE
TEMPLATE over `LAct` — the me-triple `x₁ u₁ w₁` in `#0 #1 #2`, the opp-triple `x₂ u₂ w₂`
in `#3 #4 #5` (`ArithS.Guard`): the placeholders `.self`/`.opp` of the formula are read as
"the program described by the me- or opp-triple", every other program as the CANONICAL
DESCRIPTION of its own code (`dnumT`/`dUT`/`dWT` of `ArithS.Template`, binary numerals —
no unary numeral of a code appears anywhere). `tcode φ := ⌜tmpl φ⌝` is the template code
stored by `pSearch`; the two are mutually recursive exactly as `Prog`/`Formula` are.

* `.plays p q a ↦ ∃ x y n, D_p(x) ∧ D_q(y) ∧ EvalGraph n x y x c_a` — the engine's
  `play fuel p q = eval fuel p q p` (`Dynamics.play`); a description `D_p(x)` is
  `∃ d, d = T_p ∧ x = relabel U_p W_p d` (`descF`), with `(T, U, W)` the frame variables
  for a placeholder and the closed description terms of `pcode p` otherwise;
* `.impl`/`.neg` are `🡒`/`∼`; `.eq p q ↦ ∃ x y, D_p(x) ∧ D̂_q(y) ∧ x = y` with the frozen
  literal `q` always described by its code;
* `.box k ψ ↦ ∃ me opp, (me, opp reconstructed from the triples) ∧ ∃ g, guardCodeGraph g
  ⌜tmpl ψ⌝ me opp ∧ LenProvableV TAct k g` — "the instance of `ψ` at the current players
  has a `TAct`-proof of length `≤ k`" (the constant `⌜tmpl ψ⌝` is a binary numeral);
* `.diag ↦ ⊥`: the engine's `.diag` is a meta-level fixpoint sentence with no bounded
  reading here (T2-CORE reads it as Foundation's `fixedpoint`, budget erased) — recorded by
  the side condition `noDiag`; `.tvote`/`.sys`/`.selfIdx` (the tau constructors) map to the
  non-shape code `0` — side condition `noTauP`, closed under `Prog.subst`.

## The code equations (`pcode_subst`, `tcode_subst`)

`pcode (p.subst me opp) = psubst (pcode me) (pcode opp) (pcode p)` and
`tcode (ψ.subst me opp) = gsubst (pcode me) (pcode opp) (tcode ψ)` — proved on the
SEARCH-BOT FRAGMENT `fragP`/`fragF`: the atoms `.plays P Q a` / `.eq P Q` have `P, Q` a
placeholder or a CLOSED program (`closedP`: no placeholder at a `subst`-visible position), no
`.box` occurs inside a template, no tau constructor, and the players `me`, `opp` are not bare
placeholders. The heart is the meta equation `tmpl_subst`: `tmpl (ψ.subst me opp) = tmpl ψ ⇜
(the closed description terms of `pcode me`, `pcode opp`)`, which holds LITERALLY because
after substitution the frame variables are unused and every description has the uniform
shape `descF`.

WHY `.box` IS EXCLUDED (an honest boundary, not a gap in the proof): the translated box
carries the CODE of its body as a numeral constant, and codes are not compositional under
substitution — `tmpl (.box k (ψ.subst me opp))` mentions `⌜tmpl (ψ.subst me opp)⌝` while
`tmpl (.box k ψ) ⇜ desc` mentions `⌜tmpl ψ⌝` and the descriptions: two sentences that are
PA-provably equivalent (both say that the same instantiated sentence is provable) but not
identical, and length-bounded provability is not invariant under provable equivalence. This
is the same phenomenon as `□A(x)` vs `Prov(sub(⌜A⌝, x))` in provability logic. The zoo's
templates are box-free except LegibleBot/OptimBot (their two-budget box guards), which are
outside the fragment.

## τ (`swapcode_pcode`, `relabelTemplate_tcode`)

On the same fragment the code-level transposition of `ArithS.Prog` is the code of the
engine's `Prog.transpose`/`Formula.transpose` (`Base/Transpose`): `lMap swap (tmpl φ) =
tmpl φ.transpose` (`lMap_swap_tmpl`), then `relabelTemplate_quote_sentence`. The box is
excluded here for the same reason (its code constant is not re-valued by `swap`).
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

lemma tlen_emb_cl {n : ℕ} (t : ClosedSemiterm LAct 0) :
    tlen (Rew.emb (cl t) : SyntacticSemiterm LAct n) = tlen (Rew.emb t : SyntacticSemiterm LAct 0) := by
  induction t with
  | bvar x => exact x.elim0
  | fvar x => exact x.elim
  | func f v ih =>
    show tlen (Rew.emb (Rew.castLE _ (Semiterm.func f v)) : SyntacticSemiterm LAct n) = _
    rw [Rew.func, Rew.func, Rew.func, tlen_func, tlen_func]
    congr 1
    exact Finset.sum_congr rfl (fun i _ ↦ ih i)

lemma comp_subst_eq {n m k : ℕ} (ω : Rew LAct Empty m Empty k) (v : Fin n → Semiterm LAct Empty m) :
    ω.comp (Rew.subst v) = Rew.subst (fun i ↦ ω (v i)) := by
  ext x
  · simp [Rew.comp_app]
  · exact x.elim

/-- The binary numeral of a code, as an `LAct`-term. -/
noncomputable def numTB (c : ℕ) : ClosedSemiterm LAct 0 := Semiterm.lMap emb (bnumT c)

/-! ### The Σ₁ graphs over `LAct` -/

/-- `#0 = relabel #1 #2 #3` (`relabelDef`, argument order `y u w x`). -/
noncomputable def relDesc : Semisentence LAct 4 := Semiformula.lMap emb relabelDef.val
/-- `EvalGraph #0 #1 #2 #3 #4` (`n me opp p a`). -/
noncomputable def evalG : Semisentence LAct 5 := Semiformula.lMap emb evalGraphDef.val
/-- `#0 = guardCode #1 #2 #3` (`y g me opp`). -/
noncomputable def guardCodeG : Semisentence LAct 4 := Semiformula.lMap emb guardCodeGraph.val
/-- `LenProvableV TAct #0 #1` (`k φ`), the Σ₁ side. -/
noncomputable def lenProvG : Semisentence LAct 2 := Semiformula.lMap emb (lenProvableV TAct).sigma.val

lemma lMap_swap_relDesc : Semiformula.lMap swap relDesc = relDesc := lMap_swap_emb _
lemma lMap_swap_evalG : Semiformula.lMap swap evalG = evalG := lMap_swap_emb _
lemma lMap_swap_guardCodeG : Semiformula.lMap swap guardCodeG = guardCodeG := lMap_swap_emb _
lemma lMap_swap_lenProvG : Semiformula.lMap swap lenProvG = lenProvG := lMap_swap_emb _

/-! ### The description shape -/

/-- `∃ d, d = T ∧ X = relabel U W d`: "`X` is the program with canonical numeral `T` and
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
  descF #1 (cl (dnumT c)) (cl (dUT c)) (cl (dWT c))

/-- The description of `p`, whose code is `c`: the me-triple for `.self`, the opp-triple for
`.opp`, the canonical description of `c` otherwise. -/
noncomputable def progAux (p : PD.Prog) (c : ℕ) : Semisentence LAct 7 :=
  if p = .self then descF #1 #2 #3 #4 else if p = .opp then descF #1 #5 #6 #7 else closedDesc c

/-- The action code: `C ↦ 0`, `D ↦ 1`. -/
def actCode : PD.Action → ℕ
  | .C => 0
  | .D => 1

lemma actCode_swap (a : PD.Action) : actCode a.swap = swapAct (actCode a) := by
  cases a <;> simp [actCode, PD.Action.swap, relabelAct]

lemma actCode_le_one (a : PD.Action) : actCode a ≤ 1 := by cases a <;> simp [actCode]

/-! ### The translation -/

mutual
  /-- The program code. -/
  noncomputable def pcode : PD.Prog → ℕ
    | .const a => pConst (actCode a)
    | .self => pSelf
    | .opp => pOpp
    | .bot p => pBot (pcode p)
    | .sim p q => pSim (pcode p) (pcode q)
    | .ite b a p q => pIte (pcode b) (actCode a) (pcode p) (pcode q)
    | .search k φ p q => pSearch k (⌜tmpl φ⌝ : ℕ) (pcode p) (pcode q)
    | .tvote _ _ _ _ => 0
    | .sys _ _ => 0
    | .selfIdx _ => 0
  /-- The six-variable template of a formula. -/
  noncomputable def tmpl : PD.Formula → Semisentence LAct 6
    | .plays p q a =>
        ∃¹ (∃¹ (∃¹ ((progAux p (pcode p) ⇜ ![#2, #3, #4, #5, #6, #7, #8]) ⋏
          ((progAux q (pcode q) ⇜ ![#1, #3, #4, #5, #6, #7, #8]) ⋏
            (evalG ⇜ ![#0, #2, #1, #2, cl (actT (actCode a))])))))
    | .impl φ ψ => tmpl φ 🡒 tmpl ψ
    | .neg φ => ∼ tmpl φ
    | .box k ψ =>
        ∃¹ (∃¹ ((progAux .self 0 ⇜ ![#1, #2, #3, #4, #5, #6, #7]) ⋏
          ((progAux .opp 0 ⇜ ![#0, #2, #3, #4, #5, #6, #7]) ⋏
            (∃¹ ((guardCodeG ⇜ ![#0, cl (numTB (⌜tmpl ψ⌝ : ℕ)), #2, #1]) ⋏
              (lenProvG ⇜ ![cl (numTB k), #0]))))))
    | .eq p q =>
        ∃¹ (∃¹ ((progAux p (pcode p) ⇜ ![#1, #2, #3, #4, #5, #6, #7]) ⋏
          ((closedDesc (pcode q) ⇜ ![#0, #2, #3, #4, #5, #6, #7]) ⋏
            Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#1, #0])))
    | .diag _ _ => ⊥
end

/-- The template code. -/
noncomputable def tcode (φ : PD.Formula) : ℕ := ⌜tmpl φ⌝

/-- The description of `p` in the frame. -/
noncomputable def progGraph (p : PD.Prog) : Semisentence LAct 7 := progAux p (pcode p)

@[simp] lemma pcode_const (a) : pcode (.const a) = pConst (actCode a) := by rw [pcode]
@[simp] lemma pcode_self : pcode .self = pSelf := by rw [pcode]
@[simp] lemma pcode_opp : pcode .opp = pOpp := by rw [pcode]
@[simp] lemma pcode_bot (p) : pcode (.bot p) = pBot (pcode p) := by rw [pcode]
@[simp] lemma pcode_sim (p q) : pcode (.sim p q) = pSim (pcode p) (pcode q) := by rw [pcode]
@[simp] lemma pcode_ite (b a p q) : pcode (.ite b a p q) = pIte (pcode b) (actCode a) (pcode p) (pcode q) := by
  rw [pcode]
@[simp] lemma pcode_search (k φ p q) : pcode (.search k φ p q) = pSearch k (tcode φ) (pcode p) (pcode q) := by
  rw [pcode]; rfl
@[simp] lemma pcode_tvote (v θ p q) : pcode (.tvote v θ p q) = 0 := by rw [pcode]
@[simp] lemma pcode_sys (defs i) : pcode (.sys defs i) = 0 := by rw [pcode]
@[simp] lemma pcode_selfIdx (j) : pcode (.selfIdx j) = 0 := by rw [pcode]

lemma tmpl_plays (p q a) : tmpl (.plays p q a) =
    ∃¹ (∃¹ (∃¹ ((progGraph p ⇜ ![#2, #3, #4, #5, #6, #7, #8]) ⋏
      ((progGraph q ⇜ ![#1, #3, #4, #5, #6, #7, #8]) ⋏
        (evalG ⇜ ![#0, #2, #1, #2, cl (actT (actCode a))]))))) := by
  rw [tmpl]; rfl
lemma tmpl_impl (φ ψ) : tmpl (.impl φ ψ) = tmpl φ 🡒 tmpl ψ := by rw [tmpl]
lemma tmpl_neg (φ) : tmpl (.neg φ) = ∼ tmpl φ := by rw [tmpl]
lemma tmpl_box (k ψ) : tmpl (.box k ψ) =
    ∃¹ (∃¹ ((progAux .self 0 ⇜ ![#1, #2, #3, #4, #5, #6, #7]) ⋏
      ((progAux .opp 0 ⇜ ![#0, #2, #3, #4, #5, #6, #7]) ⋏
        (∃¹ ((guardCodeG ⇜ ![#0, cl (numTB (tcode ψ)), #2, #1]) ⋏
          (lenProvG ⇜ ![cl (numTB k), #0])))))) := by
  rw [tmpl]; rfl
lemma tmpl_eq (p q) : tmpl (.eq p q) =
    ∃¹ (∃¹ ((progGraph p ⇜ ![#1, #2, #3, #4, #5, #6, #7]) ⋏
      ((closedDesc (pcode q) ⇜ ![#0, #2, #3, #4, #5, #6, #7]) ⋏
        Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#1, #0]))) := by
  rw [tmpl]; rfl
lemma tmpl_diag (g φ) : tmpl (.diag g φ) = ⊥ := by rw [tmpl]

/-- The template code is a six-variable formula code. -/
lemma isSemiformula_tcode (φ : PD.Formula) : IsSemiformula LAct 6 (tcode φ) := by
  have := Semiformula.quote_isSemiformula (V := ℕ) (Rewriting.emb (tmpl φ) : Semiproposition LAct 6)
  rw [natCast_nat] at this
  exact this

/-- The sentence "`φ` at the players `me`, `opp`": the template filled with the closed
descriptions of their codes — the atom realization T2-AGENT uses. -/
noncomputable def trAt (me opp : PD.Prog) (φ : PD.Formula) : Sentence LAct :=
  tmpl φ ⇜ descTerms (pcode me) (pcode opp)

/-- The code of `trAt` is the guard code of the template code (the `quote_guardSentenceA`
argument, for every formula). -/
theorem quote_trAt (me opp : PD.Prog) (φ : PD.Formula) :
    (⌜trAt me opp φ⌝ : ℕ) = guardCode (tcode φ) (pcode me) (pcode opp) := by
  unfold trAt guardCode tcode
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1
  exact semitermVec_val_descTerms _ _

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
    closedDesc c ⇜ w = descF (Rew.bShift (w 0)) (cl (dnumT c)) (cl (dUT c)) (cl (dWT c)) := by
  unfold closedDesc Rewriting.subst
  rw [rew_descF]
  simp only [rew_cl]
  rfl

/-- **Lemma A**: substituting the frame descriptions into the description of an atomic
program gives the description of the substituted program. -/
lemma progAux_subst {m : ℕ} {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp) (hopp : opp ≠ .self ∧ opp ≠ .opp)
    {p : PD.Prog} (hp : atomicP p = true) (w w' : Fin 7 → Semiterm LAct Empty m)
    (h0 : w 0 = w' 0)
    (h1 : w 1 = cl (dnumT (pcode me))) (h2 : w 2 = cl (dUT (pcode me))) (h3 : w 3 = cl (dWT (pcode me)))
    (h4 : w 4 = cl (dnumT (pcode opp))) (h5 : w 5 = cl (dUT (pcode opp))) (h6 : w 6 = cl (dWT (pcode opp))) :
    progAux p (pcode p) ⇜ w = progAux (p.subst me opp) (pcode (p.subst me opp)) ⇜ w' := by
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
  fun i ↦ cl (descTerms (pcode me) (pcode opp) i)

/-- **The meta substitution equation** (the heart of step (c)): on the fragment, the
template of a substituted formula IS the template with the closed descriptions of the
players substituted for the frame variables. -/
theorem tmpl_subst {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp) (hopp : opp ≠ .self ∧ opp ≠ .opp) :
    ∀ ψ : PD.Formula, fragF ψ = true → tmpl (ψ.subst me opp) = tmpl ψ ⇜ descTerms6 me opp
  | .plays p q a, h => by
    simp only [fragF, Bool.and_eq_true] at h
    rw [PD.Formula.subst, tmpl_plays, tmpl_plays]
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
    rw [PD.Formula.subst, tmpl_impl, tmpl_impl, tmpl_subst hme hopp φ h.1, tmpl_subst hme hopp ψ h.2]
    unfold Rewriting.subst
    rw [LogicalConnective.HomClass.map_imply]
  | .neg φ, h => by
    simp only [fragF] at h
    rw [PD.Formula.subst, tmpl_neg, tmpl_neg, tmpl_subst hme hopp φ h]
    unfold Rewriting.subst
    rw [LogicalConnective.HomClass.map_neg]
  | .box _ _, h => by simp [fragF] at h
  | .eq p q, h => by
    simp only [fragF, Bool.and_eq_true] at h
    rw [PD.Formula.subst, tmpl_eq, tmpl_eq]
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
    simp only [PD.Formula.subst, tmpl_diag]
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
formula is the stored template instantiated by `gsubst` (= `guardCode`) with the players'
codes — exactly what `psubst` does at a search node. -/
theorem tcode_subst {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp) (hopp : opp ≠ .self ∧ opp ≠ .opp)
    (ψ : PD.Formula) (h : fragF ψ = true) :
    tcode (ψ.subst me opp) = gsubst (pcode me) (pcode opp) (tcode ψ) := by
  rw [gsubst_of_template (isSemiformula_tcode ψ), ← quote_trAt]
  unfold tcode trAt
  rw [tmpl_subst hme hopp ψ h]
  exact quote_subst_cl _ _

/-- **The program code equation**: on the fragment, the code of a substituted program is the
code-level substitution of the players' codes. -/
theorem pcode_subst {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp) (hopp : opp ≠ .self ∧ opp ≠ .opp) :
    ∀ p : PD.Prog, fragP p = true → pcode (p.subst me opp) = psubst (pcode me) (pcode opp) (pcode p)
  | .const _, _ => by simp [PD.Prog.subst]
  | .self, _ => by simp [PD.Prog.subst]
  | .opp, _ => by simp [PD.Prog.subst]
  | .bot _, _ => by simp [PD.Prog.subst]
  | .sim p q, h => by
    simp only [fragP, Bool.and_eq_true] at h
    simp [PD.Prog.subst, pcode_subst hme hopp p h.1, pcode_subst hme hopp q h.2]
  | .ite b _ p q, h => by
    simp only [fragP, Bool.and_eq_true] at h
    simp [PD.Prog.subst, pcode_subst hme hopp b h.1.1, pcode_subst hme hopp p h.1.2, pcode_subst hme hopp q h.2]
  | .search _ φ p q, h => by
    simp only [fragP, Bool.and_eq_true] at h
    simp [PD.Prog.subst, pcode_subst hme hopp p h.1.2, pcode_subst hme hopp q h.2, tcode_subst hme hopp φ h.1.1]
  | .tvote _ _ _ _, h => by simp [fragP] at h
  | .sys _ _, h => by simp [fragP] at h
  | .selfIdx _, h => by simp [fragP] at h

/-! ### τ -/

lemma transpose_ne_self {p : PD.Prog} (h : p ≠ .self) : p.transpose ≠ .self := by
  cases p <;> simp_all [PD.Prog.transpose]
lemma transpose_ne_opp {p : PD.Prog} (h : p ≠ .opp) : p.transpose ≠ .opp := by
  cases p <;> simp_all [PD.Prog.transpose]

lemma lMap_swap_closedDesc (c : ℕ) : Semiformula.lMap swap (closedDesc c) = closedDesc (swapcode c) := by
  unfold closedDesc
  rw [lMap_swap_descF, lMap_swap_cl, lMap_swap_cl, lMap_swap_cl, lMap_swap_dnumT, lMap_swap_dUT, lMap_swap_dWT]
  rfl

lemma lMap_swap_progAux {p : PD.Prog} (h : swapcode (pcode p) = pcode p.transpose) :
    Semiformula.lMap swap (progAux p (pcode p)) = progAux p.transpose (pcode p.transpose) := by
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
  theorem lMap_swap_tmpl : ∀ φ : PD.Formula, fragF φ = true →
      Semiformula.lMap swap (tmpl φ) = tmpl φ.transpose
    | .plays p q a, h => by
      simp only [fragF, Bool.and_eq_true] at h
      rw [PD.Formula.transpose, tmpl_plays, tmpl_plays]
      unfold progGraph
      simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
        lMap_swap_evalG, lMap_swap_progAux (swapcode_pcode p h.1.1.2), lMap_swap_progAux (swapcode_pcode q h.2)]
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
      rw [PD.Formula.transpose, tmpl_impl, tmpl_impl, LogicalConnective.HomClass.map_imply,
        lMap_swap_tmpl φ h.1, lMap_swap_tmpl ψ h.2]
    | .neg φ, h => by
      simp only [fragF] at h
      rw [PD.Formula.transpose, tmpl_neg, tmpl_neg, LogicalConnective.HomClass.map_neg, lMap_swap_tmpl φ h]
    | .box _ _, h => by simp [fragF] at h
    | .eq p q, h => by
      simp only [fragF, Bool.and_eq_true] at h
      rw [PD.Formula.transpose, tmpl_eq, tmpl_eq]
      unfold progGraph
      simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
        lMap_swap_progAux (swapcode_pcode p h.1.2), lMap_swap_closedDesc, swapcode_pcode q h.2,
        Semiformula.lMap_rel]
      congr 3
      · congr 1; funext i; fin_cases i <;> rfl
      · congr 1
        · congr 1; funext i; fin_cases i <;> rfl
        · show FirstOrder.Semiformula.rel _ (Semiterm.lMap swap ∘ ![#1, #0]) = _
          congr 1; funext i; fin_cases i <;> rfl
    | .diag _ _, _ => by
      rw [PD.Formula.transpose, tmpl_diag, tmpl_diag, LogicalConnective.HomClass.map_bot]
  /-- **τ on program codes**: the code-level transposition of a program's code is the code of
  the engine's transposed program (fragment). -/
  theorem swapcode_pcode : ∀ p : PD.Prog, fragP p = true → swapcode (pcode p) = pcode p.transpose
    | .const a, _ => by simp [PD.Prog.transpose, swapcode, actCode_swap]
    | .self, _ => by simp [PD.Prog.transpose, swapcode]
    | .opp, _ => by simp [PD.Prog.transpose, swapcode]
    | .bot p, h => by
      simp only [fragP] at h
      simp [PD.Prog.transpose, swapcode, swapcode_pcode p h]
    | .sim p q, h => by
      simp only [fragP, Bool.and_eq_true] at h
      simp [PD.Prog.transpose, swapcode, swapcode_pcode p h.1, swapcode_pcode q h.2]
    | .ite b a p q, h => by
      simp only [fragP, Bool.and_eq_true] at h
      simp [PD.Prog.transpose, swapcode, swapcode_pcode b h.1.1, swapcode_pcode p h.1.2, swapcode_pcode q h.2,
        actCode_swap]
    | .search k φ p q, h => by
      simp only [fragP, Bool.and_eq_true] at h
      simp only [PD.Prog.transpose, pcode_search, swapcode, relabel_search, swapcode_pcode p h.1.2,
        swapcode_pcode q h.2]
      unfold tcode
      rw [relabelTemplate_quote_sentence, lMap_swap_tmpl φ h.1.1]
    | .tvote _ _ _ _, h => by simp [fragP] at h
    | .sys _ _, h => by simp [fragP] at h
    | .selfIdx _, h => by simp [fragP] at h
end

/-- **τ on template codes** (fragment). -/
theorem relabelTemplate_tcode (φ : PD.Formula) (h : fragF φ = true) :
    relabelTemplate 1 0 (tcode φ) = tcode φ.transpose := by
  unfold tcode
  rw [relabelTemplate_quote_sentence, lMap_swap_tmpl φ h]

/-! ### Sanity: the engine's `DupocBot`

`pcode (DupocBot k)` is a searcher of budget `k` on the template of `.plays .opp .self .C` with
the constant branches `C`/`D`; it is in the fragment. Its stored template is NOT literally
`⌜GtmplA 0⌝` (the hand-written template of `ArithS.RedCell`): `tmpl` quantifies the two
program codes and the fuel in the order `x y n` and describes each player through the
uniform shape `descF`, whereas `Gtmpl` reconstructs `me`/`opp` and then quantifies the fuel.
The two guard sentences say the same thing (both are "opp plays `C` against me"); `Dupoc k`
and `pcode (DupocBot k)` are two different searchers with provably equivalent guards, not one
code. -/
theorem pcode_DupocBot (k : ℕ) :
    pcode (PD.Bots.DupocBot k) = pSearch k (tcode (.plays .opp .self .C)) (pConst 0) (pConst 1) := by
  simp [PD.Bots.DupocBot, actCode]

theorem fragP_DupocBot (k : ℕ) : fragP (PD.Bots.DupocBot k) = true := rfl

theorem swapcode_pcode_DupocBot (k : ℕ) :
    swapcode (pcode (PD.Bots.DupocBot k)) = pcode (PD.Bots.DupocBot k).transpose :=
  swapcode_pcode _ (fragP_DupocBot k)

end ArithS
