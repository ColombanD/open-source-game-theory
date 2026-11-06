import ArithS.Agents.CodeTerm
import ArithS.Agents.Guard

/-!
# ArithS.Agents.CodeTermAbs — the description of a closed program with the node's budget ABSTRACTED

Route (c) made generic (Phase 2c of `SPRIME_SOURCE_OF_TRUTH.md`, decision (A), 2026-10-01). A stored template
describes a closed program by the structural term of its code (`codeTermMeta`, `ArithS.Agents.CodeTerm`). When
that program carries the searching node's OWN budget `k₀` — JustBot's frozen snapshot `DupocBot k`, a tau
hypothesis instance `.search k …` named inside a guard — the description written as a closed numeral makes the
template code `k₀`-dependent (`ROUTE_B_SCOPE.md` §7, the budget-snapshot obstruction of `Tau/NeverFits.lean`).
Here the description is a ONE-VARIABLE term instead: `codeTermMetaAbs k₀ x : Semiterm ℒₒᵣ Empty 1` is
`codeTermMeta x` with every `pSearch k₀ …` budget leaf written as the variable `#0`; the template puts the budget
slot `#6` there, and the evaluator fills `#6` with the node's budget (`guardCodeB`), so the sentence consulted at
run time is unchanged — the syntactic instantiation identity `subst_codeTermMetaAbs`:

  `Rew.subst ![binNumeralMeta k₀] (codeTermMetaAbs k₀ x) = codeTermMeta x`.

The recursion descends through `pBot`, `pSim`, `pIte`, `pSearch` (branches and the budget), `pTvote`, the
list `pCons` and — since Phase 2d (decision (α), 2026-10-02) — a SYSTEM `pSys d i` (the member list abstracted
member by member through the `pCons` clause, the index a numeral leaf); every other code — the leaves
`pConst`/`pSelf`/`pOpp`/`pSelfIdx` and a non-program — is described verbatim (`Rew.bShift (codeTermMeta x)`).
Phase 2c kept a system opaque so that the member-slot equation `templateAt_sysClose`
(`Agents/SysTemplate.lean`) stayed literal against the VERBATIM closer `sysCloseTemplate`; but a paper-zoo guard
DOES name a closed system with a `.search k` member (`inst dimcid ebot`: τ(EBot)'s third watch at DIMCID names
`inst dimcid mirror = .sys [dim 1, mm 0] 0`), and a verbatim system puts `binNumeral k` back inside that stored
template (`Tau/NeverFitsSys.lean`). The closer now takes the node's budget and fills the member slots with the
code-level twin of this abstraction (`codeTermAbs`, `sysCloseTemplateAt`, `ArithS.Agents.CodeTermSlot`/`Guard`),
so both sides of the member equation are abstract.

* `Desc x` — the seven descent shapes; `budgetT1 k₀ k` — the budget leaf (`#0` at `k = k₀`, the numeral else);
* `CodeTermMetaAbsGraph k₀` (inductive, with inversion lemmas) and the function `codeTermMetaAbs k₀`;
* the equations `codeTermMetaAbs_bot … _cons`, `_leaf`, `_const`, `_self`, `_opp`, `_sys`, `_selfIdx`,
  `_of_not_shape`;
* **`subst_codeTermMetaAbs`** (the instantiation identity) and its V-valued corollary in `Eval/Det.lean`;
* §8 **`quote_emb_codeTermMetaAbs`** (the code equation, every model): the code of the abstracted term is the
  internal `codeTermAbs k₀ ^#0 x` (`ArithS.Agents.CodeTermSlot`);
* **`NoSearchAt k₀ x`** ("no `pSearch k₀` node at a descent position", systems included) with `codeTermMetaAbs_of_noSearchAt :
  codeTermMetaAbs k₀ x = Rew.bShift (codeTermMeta x)` — the bridge to the unabstracted description — closed
  under `transposeCode` and `canonical`;
* the length bound `termLenMeta_emb_codeTermMetaAbs_le`: the abstracted term is never longer than the verbatim
  one (`#0` has length `1`), with the per-shape equations (`termLenMeta_emb_codeTermMetaAbs_search`: the budget
  slot contributes `6 · 1` instead of `6 · |binNumeralMeta k₀|`) from which the `k₀`-independence of a family's
  description follows once its canonical orientation is fixed (`Agents/Instance.lean`'s method).

The one-variable term combinators `ppairT1`/`succT1`/`searchT1` and the substitution lemmas on them moved here
from `Agents/Instance.lean` (2026-10-01; same names).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

/-! ### 1. One-variable term combinators (from `Agents/Instance.lean`) -/

section oneVariable

/-- The one-variable pairing term (bound variables allowed). -/
noncomputable def ppairT1 (s t : Semiterm ℒₒᵣ Empty 1) : Semiterm ℒₒᵣ Empty 1 :=
  Semiterm.func Language.ORing.Func.add
    ![Semiterm.func Language.ORing.Func.mul
      ![Semiterm.func Language.ORing.Func.add ![s, t], Semiterm.func Language.ORing.Func.add ![s, t]], t]

/-- The meta numeral `1` as a closed term. -/
noncomputable def oneTT : ClosedSemiterm ℒₒᵣ 0 := ‘1’

/-- The one-variable successor term. -/
noncomputable def succT1 (t : Semiterm ℒₒᵣ Empty 1) : Semiterm ℒₒᵣ Empty 1 :=
  Semiterm.func Language.ORing.Func.add ![t, Rew.bShift oneTT]

lemma ppairTermMeta_func (s t : ClosedSemiterm ℒₒᵣ 0) :
    ppairTermMeta s t = Semiterm.func Language.ORing.Func.add
      ![Semiterm.func Language.ORing.Func.mul
        ![Semiterm.func Language.ORing.Func.add ![s, t], Semiterm.func Language.ORing.Func.add ![s, t]], t] := rfl

lemma succTT_func (t : ClosedSemiterm ℒₒᵣ 0) :
    succTT t = Semiterm.func Language.ORing.Func.add ![t, oneTT] := rfl

lemma subst_func₂ (v : Fin 1 → ClosedSemiterm ℒₒᵣ 0) (f : (ℒₒᵣ).Func 2) (s t : Semiterm ℒₒᵣ Empty 1) :
    Rew.subst v (Semiterm.func f ![s, t]) = Semiterm.func f ![Rew.subst v s, Rew.subst v t] := by
  rw [Rew.func]; congr 1; funext i; fin_cases i <;> rfl

lemma subst_bShift₁ (u : ClosedSemiterm ℒₒᵣ 0) (t : ClosedSemiterm ℒₒᵣ 0) :
    Rew.subst ![u] (Rew.bShift t) = t := by
  rw [← Rew.comp_app, Rew.subst_comp_bShift_eq_id]; rfl

lemma subst_ppairT1 (u : ClosedSemiterm ℒₒᵣ 0) (s t : Semiterm ℒₒᵣ Empty 1) :
    Rew.subst ![u] (ppairT1 s t) = ppairTermMeta (Rew.subst ![u] s) (Rew.subst ![u] t) := by
  rw [ppairT1, ppairTermMeta_func, subst_func₂, subst_func₂, subst_func₂]

lemma subst_succT1 (u : ClosedSemiterm ℒₒᵣ 0) (t : Semiterm ℒₒᵣ Empty 1) :
    Rew.subst ![u] (succT1 t) = succTT (Rew.subst ![u] t) := by
  rw [succT1, succTT_func, subst_func₂, subst_bShift₁]

/-- The one-variable structural term of the searcher `pSearch · g p q`. -/
noncomputable def searchT1 (g p q : ℕ) : Semiterm ℒₒᵣ Empty 1 :=
  succT1 (ppairT1 (Rew.bShift (binNumeralMeta 6)) (ppairT1 #0
    (Rew.bShift (ppairTermMeta (binNumeralMeta g) (ppairTermMeta (codeTermMeta p) (codeTermMeta q))))))

/-- **The structural term of a searcher is the `k`-instance of `searchT1`.** -/
theorem codeTermMeta_search_eq_subst (k g p q : ℕ) :
    codeTermMeta (pSearch k g p q) = Rew.subst ![binNumeralMeta k] (searchT1 g p q) := by
  rw [codeTermMeta_search, searchT1, subst_succT1, subst_ppairT1, subst_ppairT1, subst_bShift₁, subst_bShift₁,
    Rew.subst_bvar]
  rfl

/-- `lMap` commutes with a one-variable substitution. -/
lemma term_lMap_subst₁ (b : ClosedSemiterm ℒₒᵣ 0) (T : Semiterm ℒₒᵣ Empty 1) :
    Semiterm.lMap emb (Rew.subst ![b] T) = Rew.subst ![Semiterm.lMap emb b] (Semiterm.lMap emb T) := by
  unfold Rew.subst
  rw [Semiterm.lMap_bind]
  have e1 : Semiterm.lMap emb ∘ ![b] = ![Semiterm.lMap emb b] := by funext i; fin_cases i; rfl
  have e2 : Semiterm.lMap emb ∘ (Semiterm.fvar : Empty → Semiterm ℒₒᵣ Empty 0) = Semiterm.fvar := by
    funext x; exact x.elim
  rw [e1, e2]

/-- `bShift` of a closed `ppairTermMeta` is the one-variable pairing of the shifts. -/
lemma bShift_ppairTermMeta (s t : ClosedSemiterm ℒₒᵣ 0) :
    (Rew.bShift (ppairTermMeta s t) : Semiterm ℒₒᵣ Empty 1) = ppairT1 (Rew.bShift s) (Rew.bShift t) := by
  rw [ppairTermMeta_func, ppairT1, Rew.func]
  congr 1; funext i; fin_cases i
  · change Rew.bShift (Semiterm.func Language.ORing.Func.mul
      ![Semiterm.func Language.ORing.Func.add ![s, t], Semiterm.func Language.ORing.Func.add ![s, t]]) = _
    rw [Rew.func]; congr 1; funext j; fin_cases j <;>
      (change Rew.bShift (Semiterm.func Language.ORing.Func.add ![s, t]) = _
       rw [Rew.func]; congr 1; funext l; fin_cases l <;> rfl)
  · rfl

/-- `bShift` of a closed `succTT` is the one-variable successor of the shift. -/
lemma bShift_succTT (t : ClosedSemiterm ℒₒᵣ 0) :
    (Rew.bShift (succTT t) : Semiterm ℒₒᵣ Empty 1) = succT1 (Rew.bShift t) := by
  rw [succTT_func, succT1, Rew.func]
  congr 1; funext i; fin_cases i <;> rfl

end oneVariable

/-! ### 2. The descent shapes and the budget leaf -/

/-- The seven shapes the abstraction descends into: `pBot`, `pSim`, `pIte`, `pSearch`, `pTvote`, `pCons`, and
(since Phase 2d) a system `pSys d i`. Every other code (the leaves `pConst`/`pSelf`/`pOpp`/`pSelfIdx`, a
non-program) is described verbatim. -/
def Desc (x : ℕ) : Prop :=
  (∃ p, x = pBot p) ∨ (∃ p q, x = pSim p q) ∨ (∃ b a p q, x = pIte b a p q) ∨
  (∃ k g p q, x = pSearch k g p q) ∨ (∃ v θ p q, x = pTvote v θ p q) ∨ (∃ e r, x = pCons e r) ∨
  (∃ d i, x = pSys d i)

lemma Desc.isShape {x : ℕ} (h : Desc x) : IsShape x := by
  rcases h with ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ | ⟨v, θ, p, q, rfl⟩ | ⟨e, r, rfl⟩ |
    ⟨d, i, rfl⟩
  · exact IsShape.bot _
  · exact IsShape.sim _ _
  · exact IsShape.ite _ _ _ _
  · exact IsShape.search _ _ _ _
  · exact IsShape.tvote _ _ _ _
  · exact IsShape.cons _ _
  · exact IsShape.sys _ _

lemma not_desc_of_not_shape {x : ℕ} (h : ¬IsShape x) : ¬Desc x := fun hd ↦ h hd.isShape

section descLeaves

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch pTvote pSys pSelfIdx pCons Desc

lemma not_desc_const (a : ℕ) : ¬Desc (pConst a) := by simp
lemma not_desc_self : ¬Desc pSelf := by simp
lemma not_desc_opp : ¬Desc pOpp := by simp
lemma not_desc_selfIdx (j : ℕ) : ¬Desc (pSelfIdx j) := by simp

end descLeaves

/-- The budget leaf: the variable `#0` at the abstracted budget, the binary numeral otherwise. -/
noncomputable def budgetT1 (k₀ k : ℕ) : Semiterm ℒₒᵣ Empty 1 :=
  if k = k₀ then #0 else Rew.bShift (binNumeralMeta k)

lemma budgetT1_self (k₀ : ℕ) : budgetT1 k₀ k₀ = #0 := by simp [budgetT1]
lemma budgetT1_of_ne {k₀ k : ℕ} (h : k ≠ k₀) : budgetT1 k₀ k = Rew.bShift (binNumeralMeta k) := by
  simp [budgetT1, h]

/-- Filling the budget variable with the abstracted budget recovers the numeral. -/
lemma subst_budgetT1 (k₀ k : ℕ) : Rew.subst ![binNumeralMeta k₀] (budgetT1 k₀ k) = binNumeralMeta k := by
  unfold budgetT1
  split_ifs with h
  · subst h; simp
  · exact subst_bShift₁ _ _

/-! ### 3. The graph of the abstracting recursion -/

/-- `CodeTermMetaAbsGraph k₀ x t`: `t` is the structural term of `x` with every budget `k₀` written as `#0`. -/
inductive CodeTermMetaAbsGraph (k₀ : ℕ) : ℕ → Semiterm ℒₒᵣ Empty 1 → Prop
  | bot (x p : ℕ) (t tp : Semiterm ℒₒᵣ Empty 1) (hx : x = pBot p) (hp : CodeTermMetaAbsGraph k₀ p tp)
      (ht : t = succT1 (ppairT1 (Rew.bShift (binNumeralMeta 3)) tp)) : CodeTermMetaAbsGraph k₀ x t
  | sim (x p q : ℕ) (t tp tq : Semiterm ℒₒᵣ Empty 1) (hx : x = pSim p q)
      (hp : CodeTermMetaAbsGraph k₀ p tp) (hq : CodeTermMetaAbsGraph k₀ q tq)
      (ht : t = succT1 (ppairT1 (Rew.bShift (binNumeralMeta 4)) (ppairT1 tp tq))) : CodeTermMetaAbsGraph k₀ x t
  | ite (x b a p q : ℕ) (t tb tp tq : Semiterm ℒₒᵣ Empty 1) (hx : x = pIte b a p q)
      (hb : CodeTermMetaAbsGraph k₀ b tb) (hp : CodeTermMetaAbsGraph k₀ p tp) (hq : CodeTermMetaAbsGraph k₀ q tq)
      (ht : t = succT1 (ppairT1 (Rew.bShift (binNumeralMeta 5))
        (ppairT1 tb (ppairT1 (Rew.bShift (binNumeralMeta a)) (ppairT1 tp tq))))) :
      CodeTermMetaAbsGraph k₀ x t
  | search (x k g p q : ℕ) (t tp tq : Semiterm ℒₒᵣ Empty 1) (hx : x = pSearch k g p q)
      (hp : CodeTermMetaAbsGraph k₀ p tp) (hq : CodeTermMetaAbsGraph k₀ q tq)
      (ht : t = succT1 (ppairT1 (Rew.bShift (binNumeralMeta 6))
        (ppairT1 (budgetT1 k₀ k) (ppairT1 (Rew.bShift (binNumeralMeta g)) (ppairT1 tp tq))))) :
      CodeTermMetaAbsGraph k₀ x t
  | tvote (x v θ p q : ℕ) (t tv tp tq : Semiterm ℒₒᵣ Empty 1) (hx : x = pTvote v θ p q)
      (hv : CodeTermMetaAbsGraph k₀ v tv) (hp : CodeTermMetaAbsGraph k₀ p tp) (hq : CodeTermMetaAbsGraph k₀ q tq)
      (ht : t = succT1 (ppairT1 (Rew.bShift (binNumeralMeta 7))
        (ppairT1 tv (ppairT1 (Rew.bShift (binNumeralMeta θ)) (ppairT1 tp tq))))) :
      CodeTermMetaAbsGraph k₀ x t
  | cons (x e r : ℕ) (t te tr : Semiterm ℒₒᵣ Empty 1) (hx : x = pCons e r)
      (he : CodeTermMetaAbsGraph k₀ e te) (hr : CodeTermMetaAbsGraph k₀ r tr)
      (ht : t = succT1 (ppairT1 (Rew.bShift (binNumeralMeta 10)) (ppairT1 te tr))) : CodeTermMetaAbsGraph k₀ x t
  | sys (x d i : ℕ) (t td : Semiterm ℒₒᵣ Empty 1) (hx : x = pSys d i) (hd : CodeTermMetaAbsGraph k₀ d td)
      (ht : t = succT1 (ppairT1 (Rew.bShift (binNumeralMeta 8)) (ppairT1 td (Rew.bShift (binNumeralMeta i))))) :
      CodeTermMetaAbsGraph k₀ x t
  | leaf (x : ℕ) (t : Semiterm ℒₒᵣ Empty 1) (hx : ¬Desc x) (ht : t = Rew.bShift (codeTermMeta x)) :
      CodeTermMetaAbsGraph k₀ x t

section inversion

variable {k₀ : ℕ}

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch pTvote pSys pSelfIdx pCons Desc

lemma CodeTermMetaAbsGraph.bot_iff {p : ℕ} {t : Semiterm ℒₒᵣ Empty 1} :
    CodeTermMetaAbsGraph k₀ (pBot p) t ↔
    ∃ tp, CodeTermMetaAbsGraph k₀ p tp ∧ t = succT1 (ppairT1 (Rew.bShift (binNumeralMeta 3)) tp) := by
  constructor
  · intro h; cases h <;> simp_all <;>
      first | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩
  · rintro ⟨tp, hp, rfl⟩; exact .bot _ _ _ _ rfl hp rfl

lemma CodeTermMetaAbsGraph.sim_iff {p q : ℕ} {t : Semiterm ℒₒᵣ Empty 1} :
    CodeTermMetaAbsGraph k₀ (pSim p q) t ↔
    ∃ tp tq, CodeTermMetaAbsGraph k₀ p tp ∧ CodeTermMetaAbsGraph k₀ q tq ∧
      t = succT1 (ppairT1 (Rew.bShift (binNumeralMeta 4)) (ppairT1 tp tq)) := by
  constructor
  · intro h; cases h <;> simp_all <;>
      first | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩
  · rintro ⟨tp, tq, hp, hq, rfl⟩; exact .sim _ _ _ _ _ _ rfl hp hq rfl

lemma CodeTermMetaAbsGraph.ite_iff {b a p q : ℕ} {t : Semiterm ℒₒᵣ Empty 1} :
    CodeTermMetaAbsGraph k₀ (pIte b a p q) t ↔
    ∃ tb tp tq, CodeTermMetaAbsGraph k₀ b tb ∧ CodeTermMetaAbsGraph k₀ p tp ∧ CodeTermMetaAbsGraph k₀ q tq ∧
      t = succT1 (ppairT1 (Rew.bShift (binNumeralMeta 5))
        (ppairT1 tb (ppairT1 (Rew.bShift (binNumeralMeta a)) (ppairT1 tp tq)))) := by
  constructor
  · intro h; cases h <;> simp_all <;>
      first | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩
  · rintro ⟨tb, tp, tq, hb, hp, hq, rfl⟩; exact .ite _ _ _ _ _ _ _ _ _ rfl hb hp hq rfl

lemma CodeTermMetaAbsGraph.search_iff {k g p q : ℕ} {t : Semiterm ℒₒᵣ Empty 1} :
    CodeTermMetaAbsGraph k₀ (pSearch k g p q) t ↔
    ∃ tp tq, CodeTermMetaAbsGraph k₀ p tp ∧ CodeTermMetaAbsGraph k₀ q tq ∧
      t = succT1 (ppairT1 (Rew.bShift (binNumeralMeta 6))
        (ppairT1 (budgetT1 k₀ k) (ppairT1 (Rew.bShift (binNumeralMeta g)) (ppairT1 tp tq)))) := by
  constructor
  · intro h; cases h <;> simp_all <;>
      first | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩
  · rintro ⟨tp, tq, hp, hq, rfl⟩; exact .search _ _ _ _ _ _ _ _ rfl hp hq rfl

lemma CodeTermMetaAbsGraph.tvote_iff {v θ p q : ℕ} {t : Semiterm ℒₒᵣ Empty 1} :
    CodeTermMetaAbsGraph k₀ (pTvote v θ p q) t ↔
    ∃ tv tp tq, CodeTermMetaAbsGraph k₀ v tv ∧ CodeTermMetaAbsGraph k₀ p tp ∧ CodeTermMetaAbsGraph k₀ q tq ∧
      t = succT1 (ppairT1 (Rew.bShift (binNumeralMeta 7))
        (ppairT1 tv (ppairT1 (Rew.bShift (binNumeralMeta θ)) (ppairT1 tp tq)))) := by
  constructor
  · intro h; cases h <;> simp_all <;>
      first | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩
  · rintro ⟨tv, tp, tq, hv, hp, hq, rfl⟩; exact .tvote _ _ _ _ _ _ _ _ _ rfl hv hp hq rfl

lemma CodeTermMetaAbsGraph.cons_iff {e r : ℕ} {t : Semiterm ℒₒᵣ Empty 1} :
    CodeTermMetaAbsGraph k₀ (pCons e r) t ↔
    ∃ te tr, CodeTermMetaAbsGraph k₀ e te ∧ CodeTermMetaAbsGraph k₀ r tr ∧
      t = succT1 (ppairT1 (Rew.bShift (binNumeralMeta 10)) (ppairT1 te tr)) := by
  constructor
  · intro h; cases h <;> simp_all <;>
      first | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩
  · rintro ⟨te, tr, he, hr, rfl⟩; exact .cons _ _ _ _ _ _ rfl he hr rfl

lemma CodeTermMetaAbsGraph.sys_iff {d i : ℕ} {t : Semiterm ℒₒᵣ Empty 1} :
    CodeTermMetaAbsGraph k₀ (pSys d i) t ↔
    ∃ td, CodeTermMetaAbsGraph k₀ d td ∧
      t = succT1 (ppairT1 (Rew.bShift (binNumeralMeta 8)) (ppairT1 td (Rew.bShift (binNumeralMeta i)))) := by
  constructor
  · intro h; cases h <;> simp_all <;>
      first | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩
  · rintro ⟨td, hd, rfl⟩; exact .sys _ _ _ _ _ rfl hd rfl

lemma CodeTermMetaAbsGraph.leaf_iff {x : ℕ} {t : Semiterm ℒₒᵣ Empty 1} (hx : ¬Desc x) :
    CodeTermMetaAbsGraph k₀ x t ↔ t = Rew.bShift (codeTermMeta x) := by
  constructor
  · intro h; cases h <;> simp_all
  · rintro rfl; exact .leaf _ _ hx rfl

end inversion

lemma codeTermMetaAbsGraph_exists (k₀ x : ℕ) : ∃ t, CodeTermMetaAbsGraph k₀ x t := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : Desc x
    · rcases hx with ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ | ⟨v, θ, p, q, rfl⟩ | ⟨e, r, rfl⟩ |
        ⟨d, i, rfl⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp)
        exact ⟨_, CodeTermMetaAbsGraph.bot_iff.mpr ⟨tp, hp, rfl⟩⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp); obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, CodeTermMetaAbsGraph.sim_iff.mpr ⟨tp, tq, hp, hq, rfl⟩⟩
      · obtain ⟨tb, hb⟩ := ih b (by simp); obtain ⟨tp, hp⟩ := ih p (by simp)
        obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, CodeTermMetaAbsGraph.ite_iff.mpr ⟨tb, tp, tq, hb, hp, hq, rfl⟩⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp); obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, CodeTermMetaAbsGraph.search_iff.mpr ⟨tp, tq, hp, hq, rfl⟩⟩
      · obtain ⟨tv, hv⟩ := ih v (by simp); obtain ⟨tp, hp⟩ := ih p (by simp)
        obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, CodeTermMetaAbsGraph.tvote_iff.mpr ⟨tv, tp, tq, hv, hp, hq, rfl⟩⟩
      · obtain ⟨te, he⟩ := ih e (by simp); obtain ⟨tr, hr⟩ := ih r (by simp)
        exact ⟨_, CodeTermMetaAbsGraph.cons_iff.mpr ⟨te, tr, he, hr, rfl⟩⟩
      · obtain ⟨td, hd⟩ := ih d (by simp)
        exact ⟨_, CodeTermMetaAbsGraph.sys_iff.mpr ⟨td, hd, rfl⟩⟩
    · exact ⟨_, (CodeTermMetaAbsGraph.leaf_iff hx).mpr rfl⟩

lemma codeTermMetaAbsGraph_unique (k₀ x : ℕ) :
    ∀ t₁ t₂, CodeTermMetaAbsGraph k₀ x t₁ → CodeTermMetaAbsGraph k₀ x t₂ → t₁ = t₂ := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro t₁ t₂ h₁ h₂
    by_cases hx : Desc x
    · rcases hx with ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ | ⟨v, θ, p, q, rfl⟩ | ⟨e, r, rfl⟩ |
        ⟨d, i, rfl⟩
      · rcases CodeTermMetaAbsGraph.bot_iff.mp h₁ with ⟨p₁, hp₁, rfl⟩
        rcases CodeTermMetaAbsGraph.bot_iff.mp h₂ with ⟨p₂, hp₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂]
      · rcases CodeTermMetaAbsGraph.sim_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases CodeTermMetaAbsGraph.sim_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases CodeTermMetaAbsGraph.ite_iff.mp h₁ with ⟨b₁, p₁, q₁, hb₁, hp₁, hq₁, rfl⟩
        rcases CodeTermMetaAbsGraph.ite_iff.mp h₂ with ⟨b₂, p₂, q₂, hb₂, hp₂, hq₂, rfl⟩
        rw [ih b (by simp) _ _ hb₁ hb₂, ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases CodeTermMetaAbsGraph.search_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases CodeTermMetaAbsGraph.search_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases CodeTermMetaAbsGraph.tvote_iff.mp h₁ with ⟨v₁, p₁, q₁, hv₁, hp₁, hq₁, rfl⟩
        rcases CodeTermMetaAbsGraph.tvote_iff.mp h₂ with ⟨v₂, p₂, q₂, hv₂, hp₂, hq₂, rfl⟩
        rw [ih v (by simp) _ _ hv₁ hv₂, ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases CodeTermMetaAbsGraph.cons_iff.mp h₁ with ⟨e₁, r₁, he₁, hr₁, rfl⟩
        rcases CodeTermMetaAbsGraph.cons_iff.mp h₂ with ⟨e₂, r₂, he₂, hr₂, rfl⟩
        rw [ih e (by simp) _ _ he₁ he₂, ih r (by simp) _ _ hr₁ hr₂]
      · rcases CodeTermMetaAbsGraph.sys_iff.mp h₁ with ⟨d₁, hd₁, rfl⟩
        rcases CodeTermMetaAbsGraph.sys_iff.mp h₂ with ⟨d₂, hd₂, rfl⟩
        rw [ih d (by simp) _ _ hd₁ hd₂]
    · rw [CodeTermMetaAbsGraph.leaf_iff hx] at h₁ h₂; rw [h₁, h₂]

lemma codeTermMetaAbsGraph_existsUnique (k₀ x : ℕ) : ∃! t, CodeTermMetaAbsGraph k₀ x t := by
  rcases codeTermMetaAbsGraph_exists k₀ x with ⟨t, ht⟩
  exact ExistsUnique.intro t ht (fun t' h' ↦ codeTermMetaAbsGraph_unique k₀ x t' t h' ht)

/-- **The abstracted structural term**: `codeTermMeta x` with every `pSearch k₀ …` budget written as `#0`. -/
noncomputable def codeTermMetaAbs (k₀ x : ℕ) : Semiterm ℒₒᵣ Empty 1 :=
  Classical.choose (codeTermMetaAbsGraph_existsUnique k₀ x).exists

lemma codeTermMetaAbs_graph (k₀ x : ℕ) : CodeTermMetaAbsGraph k₀ x (codeTermMetaAbs k₀ x) :=
  Classical.choose_spec (codeTermMetaAbsGraph_existsUnique k₀ x).exists

lemma codeTermMetaAbs_eq_of_graph {k₀ x : ℕ} {t : Semiterm ℒₒᵣ Empty 1} (h : CodeTermMetaAbsGraph k₀ x t) :
    codeTermMetaAbs k₀ x = t :=
  codeTermMetaAbsGraph_unique k₀ x _ _ (codeTermMetaAbs_graph k₀ x) h

/-! ### 4. The equations -/

lemma codeTermMetaAbs_bot (k₀ p : ℕ) :
    codeTermMetaAbs k₀ (pBot p) = succT1 (ppairT1 (Rew.bShift (binNumeralMeta 3)) (codeTermMetaAbs k₀ p)) :=
  codeTermMetaAbs_eq_of_graph (CodeTermMetaAbsGraph.bot_iff.mpr ⟨_, codeTermMetaAbs_graph k₀ p, rfl⟩)
lemma codeTermMetaAbs_sim (k₀ p q : ℕ) :
    codeTermMetaAbs k₀ (pSim p q) =
      succT1 (ppairT1 (Rew.bShift (binNumeralMeta 4)) (ppairT1 (codeTermMetaAbs k₀ p) (codeTermMetaAbs k₀ q))) :=
  codeTermMetaAbs_eq_of_graph (CodeTermMetaAbsGraph.sim_iff.mpr
    ⟨_, _, codeTermMetaAbs_graph k₀ p, codeTermMetaAbs_graph k₀ q, rfl⟩)
lemma codeTermMetaAbs_ite (k₀ b a p q : ℕ) :
    codeTermMetaAbs k₀ (pIte b a p q) =
      succT1 (ppairT1 (Rew.bShift (binNumeralMeta 5)) (ppairT1 (codeTermMetaAbs k₀ b)
        (ppairT1 (Rew.bShift (binNumeralMeta a)) (ppairT1 (codeTermMetaAbs k₀ p) (codeTermMetaAbs k₀ q))))) :=
  codeTermMetaAbs_eq_of_graph (CodeTermMetaAbsGraph.ite_iff.mpr
    ⟨_, _, _, codeTermMetaAbs_graph k₀ b, codeTermMetaAbs_graph k₀ p, codeTermMetaAbs_graph k₀ q, rfl⟩)
lemma codeTermMetaAbs_search (k₀ k g p q : ℕ) :
    codeTermMetaAbs k₀ (pSearch k g p q) =
      succT1 (ppairT1 (Rew.bShift (binNumeralMeta 6)) (ppairT1 (budgetT1 k₀ k)
        (ppairT1 (Rew.bShift (binNumeralMeta g)) (ppairT1 (codeTermMetaAbs k₀ p) (codeTermMetaAbs k₀ q))))) :=
  codeTermMetaAbs_eq_of_graph (CodeTermMetaAbsGraph.search_iff.mpr
    ⟨_, _, codeTermMetaAbs_graph k₀ p, codeTermMetaAbs_graph k₀ q, rfl⟩)
lemma codeTermMetaAbs_tvote (k₀ v θ p q : ℕ) :
    codeTermMetaAbs k₀ (pTvote v θ p q) =
      succT1 (ppairT1 (Rew.bShift (binNumeralMeta 7)) (ppairT1 (codeTermMetaAbs k₀ v)
        (ppairT1 (Rew.bShift (binNumeralMeta θ)) (ppairT1 (codeTermMetaAbs k₀ p) (codeTermMetaAbs k₀ q))))) :=
  codeTermMetaAbs_eq_of_graph (CodeTermMetaAbsGraph.tvote_iff.mpr
    ⟨_, _, _, codeTermMetaAbs_graph k₀ v, codeTermMetaAbs_graph k₀ p, codeTermMetaAbs_graph k₀ q, rfl⟩)
lemma codeTermMetaAbs_cons (k₀ e r : ℕ) :
    codeTermMetaAbs k₀ (pCons e r) =
      succT1 (ppairT1 (Rew.bShift (binNumeralMeta 10)) (ppairT1 (codeTermMetaAbs k₀ e) (codeTermMetaAbs k₀ r))) :=
  codeTermMetaAbs_eq_of_graph (CodeTermMetaAbsGraph.cons_iff.mpr
    ⟨_, _, codeTermMetaAbs_graph k₀ e, codeTermMetaAbs_graph k₀ r, rfl⟩)
/-- A code the abstraction does not descend into is described verbatim. -/
lemma codeTermMetaAbs_leaf {x : ℕ} (hx : ¬Desc x) (k₀ : ℕ) : codeTermMetaAbs k₀ x = Rew.bShift (codeTermMeta x) :=
  codeTermMetaAbs_eq_of_graph ((CodeTermMetaAbsGraph.leaf_iff hx).mpr rfl)

lemma codeTermMetaAbs_const (k₀ a : ℕ) : codeTermMetaAbs k₀ (pConst a) = Rew.bShift (codeTermMeta (pConst a)) :=
  codeTermMetaAbs_leaf (not_desc_const a) k₀
lemma codeTermMetaAbs_self (k₀ : ℕ) : codeTermMetaAbs k₀ pSelf = Rew.bShift (codeTermMeta pSelf) :=
  codeTermMetaAbs_leaf not_desc_self k₀
lemma codeTermMetaAbs_opp (k₀ : ℕ) : codeTermMetaAbs k₀ pOpp = Rew.bShift (codeTermMeta pOpp) :=
  codeTermMetaAbs_leaf not_desc_opp k₀
/-- **The abstraction descends into a system** (Phase 2d): the member list is abstracted member by member
(through `codeTermMetaAbs_cons`), the index is a numeral leaf. -/
lemma codeTermMetaAbs_sys (k₀ d i : ℕ) :
    codeTermMetaAbs k₀ (pSys d i) =
      succT1 (ppairT1 (Rew.bShift (binNumeralMeta 8)) (ppairT1 (codeTermMetaAbs k₀ d) (Rew.bShift (binNumeralMeta i)))) :=
  codeTermMetaAbs_eq_of_graph (CodeTermMetaAbsGraph.sys_iff.mpr ⟨_, codeTermMetaAbs_graph k₀ d, rfl⟩)
lemma codeTermMetaAbs_nil (k₀ : ℕ) : codeTermMetaAbs k₀ pNil = Rew.bShift (binNumeralMeta 0) := by
  rw [codeTermMetaAbs_leaf (not_desc_of_not_shape not_isShape_zero), codeTermMeta_of_not_shape not_isShape_zero]
lemma codeTermMetaAbs_selfIdx (k₀ j : ℕ) : codeTermMetaAbs k₀ (pSelfIdx j) = Rew.bShift (codeTermMeta (pSelfIdx j)) :=
  codeTermMetaAbs_leaf (not_desc_selfIdx j) k₀
lemma codeTermMetaAbs_of_not_shape {x : ℕ} (hx : ¬IsShape x) (k₀ : ℕ) :
    codeTermMetaAbs k₀ x = Rew.bShift (binNumeralMeta x) := by
  rw [codeTermMetaAbs_leaf (not_desc_of_not_shape hx), codeTermMeta_of_not_shape hx]

/-! ### 5. The instantiation identity -/

/-- **Filling the budget variable with the abstracted budget recovers the verbatim structural term.** The
sentence a template consults after `guardCodeB` fills `#6` is therefore the one the unabstracted template
consulted. -/
theorem subst_codeTermMetaAbs (k₀ x : ℕ) :
    Rew.subst ![binNumeralMeta k₀] (codeTermMetaAbs k₀ x) = codeTermMeta x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : Desc x
    · rcases hx with ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ | ⟨v, θ, p, q, rfl⟩ | ⟨e, r, rfl⟩ |
        ⟨d, i, rfl⟩
      · rw [codeTermMetaAbs_bot, subst_succT1, subst_ppairT1, subst_bShift₁, ih p (by simp), codeTermMeta_bot]
      · rw [codeTermMetaAbs_sim, subst_succT1, subst_ppairT1, subst_ppairT1, subst_bShift₁, ih p (by simp),
          ih q (by simp), codeTermMeta_sim]
      · rw [codeTermMetaAbs_ite, subst_succT1, subst_ppairT1, subst_ppairT1, subst_ppairT1, subst_ppairT1,
          subst_bShift₁, subst_bShift₁, ih b (by simp), ih p (by simp), ih q (by simp), codeTermMeta_ite]
      · rw [codeTermMetaAbs_search, subst_succT1, subst_ppairT1, subst_ppairT1, subst_ppairT1, subst_ppairT1,
          subst_bShift₁, subst_bShift₁, subst_budgetT1, ih p (by simp), ih q (by simp), codeTermMeta_search]
      · rw [codeTermMetaAbs_tvote, subst_succT1, subst_ppairT1, subst_ppairT1, subst_ppairT1, subst_ppairT1,
          subst_bShift₁, subst_bShift₁, ih v (by simp), ih p (by simp), ih q (by simp), codeTermMeta_tvote]
      · rw [codeTermMetaAbs_cons, subst_succT1, subst_ppairT1, subst_ppairT1, subst_bShift₁, ih e (by simp),
          ih r (by simp), codeTermMeta_cons]
      · rw [codeTermMetaAbs_sys, subst_succT1, subst_ppairT1, subst_ppairT1, subst_bShift₁, subst_bShift₁,
          ih d (by simp), codeTermMeta_sys]
    · rw [codeTermMetaAbs_leaf hx, subst_bShift₁]

/-! ### 6. Codes without a `pSearch k₀` node: the abstraction is the verbatim term, shifted -/

/-- `NoSearchAt k₀ x`: no `pSearch k₀ …` node at a descent position of `x` (a system's member list is a descent
position since Phase 2d: a system with a `.search k₀` member is NOT `NoSearchAt k₀`). -/
inductive NoSearchAt (k₀ : ℕ) : ℕ → Prop
  | bot (p : ℕ) : NoSearchAt k₀ p → NoSearchAt k₀ (pBot p)
  | sim (p q : ℕ) : NoSearchAt k₀ p → NoSearchAt k₀ q → NoSearchAt k₀ (pSim p q)
  | ite (b a p q : ℕ) : NoSearchAt k₀ b → NoSearchAt k₀ p → NoSearchAt k₀ q → NoSearchAt k₀ (pIte b a p q)
  | search (k g p q : ℕ) (hk : k ≠ k₀) : NoSearchAt k₀ p → NoSearchAt k₀ q → NoSearchAt k₀ (pSearch k g p q)
  | tvote (v θ p q : ℕ) : NoSearchAt k₀ v → NoSearchAt k₀ p → NoSearchAt k₀ q → NoSearchAt k₀ (pTvote v θ p q)
  | cons (e r : ℕ) : NoSearchAt k₀ e → NoSearchAt k₀ r → NoSearchAt k₀ (pCons e r)
  | sys (d i : ℕ) : NoSearchAt k₀ d → NoSearchAt k₀ (pSys d i)
  | leaf (x : ℕ) (hx : ¬Desc x) : NoSearchAt k₀ x

lemma NoSearchAt.const (k₀ a : ℕ) : NoSearchAt k₀ (pConst a) := .leaf _ (not_desc_const a)
lemma NoSearchAt.self (k₀ : ℕ) : NoSearchAt k₀ pSelf := .leaf _ not_desc_self
lemma NoSearchAt.opp (k₀ : ℕ) : NoSearchAt k₀ pOpp := .leaf _ not_desc_opp
lemma NoSearchAt.nil (k₀ : ℕ) : NoSearchAt k₀ pNil := .leaf _ (not_desc_of_not_shape not_isShape_zero)
lemma NoSearchAt.selfIdx (k₀ j : ℕ) : NoSearchAt k₀ (pSelfIdx j) := .leaf _ (not_desc_selfIdx j)
lemma NoSearchAt.of_not_shape {x : ℕ} (hx : ¬IsShape x) (k₀ : ℕ) : NoSearchAt k₀ x :=
  .leaf _ (not_desc_of_not_shape hx)

/-- **On a code without a `pSearch k₀` node the abstraction is the verbatim description** (shifted into the
one-variable context): the bridge from `closedDescAt` to `closedDesc13` (`Agents/Code.lean`). -/
theorem codeTermMetaAbs_of_noSearchAt {k₀ x : ℕ} (h : NoSearchAt k₀ x) :
    codeTermMetaAbs k₀ x = Rew.bShift (codeTermMeta x) := by
  induction h with
  | bot p _ ih => rw [codeTermMetaAbs_bot, ih, codeTermMeta_bot, bShift_succTT, bShift_ppairTermMeta]
  | sim p q _ _ ihp ihq =>
    rw [codeTermMetaAbs_sim, ihp, ihq, codeTermMeta_sim, bShift_succTT, bShift_ppairTermMeta, bShift_ppairTermMeta]
  | ite b a p q _ _ _ ihb ihp ihq =>
    rw [codeTermMetaAbs_ite, ihb, ihp, ihq, codeTermMeta_ite, bShift_succTT, bShift_ppairTermMeta,
      bShift_ppairTermMeta, bShift_ppairTermMeta, bShift_ppairTermMeta]
  | search k g p q hk _ _ ihp ihq =>
    rw [codeTermMetaAbs_search, ihp, ihq, budgetT1_of_ne hk, codeTermMeta_search, bShift_succTT,
      bShift_ppairTermMeta, bShift_ppairTermMeta, bShift_ppairTermMeta, bShift_ppairTermMeta]
  | tvote v θ p q _ _ _ ihv ihp ihq =>
    rw [codeTermMetaAbs_tvote, ihv, ihp, ihq, codeTermMeta_tvote, bShift_succTT, bShift_ppairTermMeta,
      bShift_ppairTermMeta, bShift_ppairTermMeta, bShift_ppairTermMeta]
  | cons e r _ _ ihe ihr =>
    rw [codeTermMetaAbs_cons, ihe, ihr, codeTermMeta_cons, bShift_succTT, bShift_ppairTermMeta, bShift_ppairTermMeta]
  | sys d i _ ihd =>
    rw [codeTermMetaAbs_sys, ihd, codeTermMeta_sys, bShift_succTT, bShift_ppairTermMeta, bShift_ppairTermMeta]
  | leaf x hx => exact codeTermMetaAbs_leaf hx k₀

section transpose

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch pTvote pSys pSelfIdx pCons Desc

/-- A code the abstraction does not descend into transposes to one it does not descend into. -/
lemma not_desc_transposeCode {x : ℕ} (hx : ¬Desc x) : ¬Desc (transposeCode x) := by
  by_cases hs : IsShape x
  · rcases hs with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ |
        ⟨v, θ, p, q, rfl⟩ | ⟨d, i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩
    · rw [transposeCode, revalue_const]; exact not_desc_const _
    · rw [transposeCode, revalue_self]; exact not_desc_self
    · rw [transposeCode, revalue_opp]; exact not_desc_opp
    · exact absurd (Or.inl ⟨p, rfl⟩) hx
    · exact absurd (Or.inr (Or.inl ⟨p, q, rfl⟩)) hx
    · exact absurd (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, rfl⟩))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, rfl⟩)))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, θ, p, q, rfl⟩))))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨d, i, rfl⟩)))))) hx
    · rw [transposeCode, revalue_selfIdx]; exact not_desc_selfIdx _
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, r, rfl⟩)))))) hx
  · rw [transposeCode, revalue_of_not_shape hs]; exact hx

end transpose

/-- `NoSearchAt` is closed under τ on codes (budgets are not re-valued). -/
theorem NoSearchAt.transpose {k₀ x : ℕ} (h : NoSearchAt k₀ x) : NoSearchAt k₀ (transposeCode x) := by
  induction h with
  | bot p _ ih => rw [transposeCode, revalue_bot]; exact .bot _ ih
  | sim p q _ _ ihp ihq => rw [transposeCode, revalue_sim]; exact .sim _ _ ihp ihq
  | ite b a p q _ _ _ ihb ihp ihq => rw [transposeCode, revalue_ite]; exact .ite _ _ _ _ ihb ihp ihq
  | search k g p q hk _ _ ihp ihq => rw [transposeCode, revalue_search]; exact .search _ _ _ _ hk ihp ihq
  | tvote v θ p q _ _ _ ihv ihp ihq =>
    rw [transposeCode, revalue_tvote]; exact .tvote _ _ _ _ (by rwa [transposeCode] at ihv) ihp ihq
  | cons e r _ _ ihe ihr => rw [transposeCode, revalue_cons]; exact .cons _ _ ihe ihr
  | sys d i _ ihd => rw [transposeCode, revalue_sys]; exact .sys _ _ ihd
  | leaf x hx => exact .leaf _ (not_desc_transposeCode hx)

/-- `NoSearchAt` is closed under `canonical` (the orbit's minimum is `x` or its transposition). -/
theorem NoSearchAt.canonical {k₀ x : ℕ} (h : NoSearchAt k₀ x) : NoSearchAt k₀ (canonical x) := by
  unfold ArithS.canonical
  split_ifs
  · exact h
  · exact h.transpose

/-! ### 7. Lengths: the abstracted term is never longer than the verbatim one -/

section length

/-- Every term has at least one symbol. -/
lemma one_le_termLenMeta {n : ℕ} : ∀ t : SyntacticSemiterm ℒₒᵣ n, 1 ≤ termLenMeta t
  | #x => by simp
  | &x => by simp
  | .func f v => by rw [termLenMeta_func]; omega

/-- Shifting a closed term does not change its length (no variable to re-index). -/
lemma termLenMeta_emb_bShift₀ : ∀ t : ClosedSemiterm ℒₒᵣ 0,
    termLenMeta (Rew.emb (Rew.bShift t) : SyntacticSemiterm ℒₒᵣ 1) = termLenMeta (Rew.emb t : SyntacticSemiterm ℒₒᵣ 0)
  | #x => x.elim0
  | &x => x.elim
  | .func f v => by
    rw [Rew.func, Rew.func, Rew.func, termLenMeta_func, termLenMeta_func]
    congr 1
    exact Finset.sum_congr rfl (fun i _ ↦ termLenMeta_emb_bShift₀ (v i))

lemma termLenMeta_emb_func₂ (f : (ℒₒᵣ).Func 2) (s t : Semiterm ℒₒᵣ Empty 1) :
    termLenMeta (Rew.emb (Semiterm.func f ![s, t]) : SyntacticSemiterm ℒₒᵣ 1) =
      termLenMeta (Rew.emb s : SyntacticSemiterm ℒₒᵣ 1) + termLenMeta (Rew.emb t : SyntacticSemiterm ℒₒᵣ 1) + 1 := by
  rw [Rew.func, termLenMeta_func]
  have e : (fun i ↦ termLenMeta ((Rew.emb ∘ ![s, t]) i)) =
      ![termLenMeta (Rew.emb s : SyntacticSemiterm ℒₒᵣ 1), termLenMeta (Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)] := by
    funext i; fin_cases i <;> rfl
  rw [e, Fin.sum_univ_two]
  rfl

lemma termLenMeta_emb_ppairT1 (s t : Semiterm ℒₒᵣ Empty 1) :
    termLenMeta (Rew.emb (ppairT1 s t) : SyntacticSemiterm ℒₒᵣ 1) =
      2 * termLenMeta (Rew.emb s : SyntacticSemiterm ℒₒᵣ 1) + 3 * termLenMeta (Rew.emb t : SyntacticSemiterm ℒₒᵣ 1) + 4 := by
  rw [ppairT1, termLenMeta_emb_func₂, termLenMeta_emb_func₂, termLenMeta_emb_func₂]; omega

lemma termLenMeta_emb_oneTT : termLenMeta (Rew.emb oneTT : SyntacticSemiterm ℒₒᵣ 0) = 1 := termLenMeta_emb_closed_one

lemma termLenMeta_emb_succT1 (t : Semiterm ℒₒᵣ Empty 1) :
    termLenMeta (Rew.emb (succT1 t) : SyntacticSemiterm ℒₒᵣ 1) = termLenMeta (Rew.emb t : SyntacticSemiterm ℒₒᵣ 1) + 2 := by
  rw [succT1, termLenMeta_emb_func₂, termLenMeta_emb_bShift₀, termLenMeta_emb_oneTT]

lemma termLenMeta_emb_bvar_zero : termLenMeta (Rew.emb (#0 : Semiterm ℒₒᵣ Empty 1) : SyntacticSemiterm ℒₒᵣ 1) = 1 := by
  simp [Rew.emb]

/-- The budget leaf is never longer than the numeral it stands for. -/
lemma termLenMeta_emb_budgetT1_le (k₀ k : ℕ) :
    termLenMeta (Rew.emb (budgetT1 k₀ k) : SyntacticSemiterm ℒₒᵣ 1) ≤
      termLenMeta (Rew.emb (binNumeralMeta k) : SyntacticSemiterm ℒₒᵣ 0) := by
  unfold budgetT1
  split_ifs
  · rw [termLenMeta_emb_bvar_zero]; exact one_le_termLenMeta _
  · rw [termLenMeta_emb_bShift₀]

/-- The budget slot of an abstracted searcher costs ONE symbol. -/
lemma termLenMeta_emb_budgetT1_self (k₀ : ℕ) :
    termLenMeta (Rew.emb (budgetT1 k₀ k₀) : SyntacticSemiterm ℒₒᵣ 1) = 1 := by
  rw [budgetT1_self]; exact termLenMeta_emb_bvar_zero

/-- The searcher's abstracted term: the `pSearch` shape with the budget leaf in the budget's place. -/
lemma termLenMeta_emb_codeTermMetaAbs_search (k₀ k g p q : ℕ) :
    termLenMeta (Rew.emb (codeTermMetaAbs k₀ (pSearch k g p q)) : SyntacticSemiterm ℒₒᵣ 1) =
      2 * termLenMeta (Rew.emb (binNumeralMeta 6) : SyntacticSemiterm ℒₒᵣ 0) +
        6 * termLenMeta (Rew.emb (budgetT1 k₀ k) : SyntacticSemiterm ℒₒᵣ 1) +
        18 * termLenMeta (Rew.emb (binNumeralMeta g) : SyntacticSemiterm ℒₒᵣ 0) +
        54 * termLenMeta (Rew.emb (codeTermMetaAbs k₀ p) : SyntacticSemiterm ℒₒᵣ 1) +
        81 * termLenMeta (Rew.emb (codeTermMetaAbs k₀ q) : SyntacticSemiterm ℒₒᵣ 1) + 162 := by
  rw [codeTermMetaAbs_search, termLenMeta_emb_succT1, termLenMeta_emb_ppairT1, termLenMeta_emb_ppairT1,
    termLenMeta_emb_ppairT1, termLenMeta_emb_ppairT1, termLenMeta_emb_bShift₀, termLenMeta_emb_bShift₀]
  ring

/-- **The abstracted description is never longer than the verbatim one.** -/
theorem termLenMeta_emb_codeTermMetaAbs_le (k₀ x : ℕ) :
    termLenMeta (Rew.emb (codeTermMetaAbs k₀ x) : SyntacticSemiterm ℒₒᵣ 1) ≤
      termLenMeta (Rew.emb (codeTermMeta x) : SyntacticSemiterm ℒₒᵣ 0) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : Desc x
    · rcases hx with ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ | ⟨v, θ, p, q, rfl⟩ | ⟨e, r, rfl⟩ |
        ⟨d, i, rfl⟩
      · have := ih p (by simp)
        rw [codeTermMetaAbs_bot, termLenMeta_emb_succT1, termLenMeta_emb_ppairT1, termLenMeta_emb_bShift₀,
          termLenMeta_emb_codeTermMeta_bot]
        omega
      · have hp := ih p (by simp); have hq := ih q (by simp)
        rw [codeTermMetaAbs_sim, termLenMeta_emb_succT1, termLenMeta_emb_ppairT1, termLenMeta_emb_ppairT1,
          termLenMeta_emb_bShift₀, termLenMeta_emb_codeTermMeta_sim]
        omega
      · have hb := ih b (by simp); have hp := ih p (by simp); have hq := ih q (by simp)
        rw [codeTermMetaAbs_ite, termLenMeta_emb_succT1, termLenMeta_emb_ppairT1, termLenMeta_emb_ppairT1,
          termLenMeta_emb_ppairT1, termLenMeta_emb_ppairT1, termLenMeta_emb_bShift₀, termLenMeta_emb_bShift₀,
          termLenMeta_emb_codeTermMeta_ite]
        omega
      · have hp := ih p (by simp); have hq := ih q (by simp)
        have hk := termLenMeta_emb_budgetT1_le k₀ k
        rw [termLenMeta_emb_codeTermMetaAbs_search, termLenMeta_emb_codeTermMeta_search]
        omega
      · have hv := ih v (by simp); have hp := ih p (by simp); have hq := ih q (by simp)
        rw [codeTermMetaAbs_tvote, termLenMeta_emb_succT1, termLenMeta_emb_ppairT1, termLenMeta_emb_ppairT1,
          termLenMeta_emb_ppairT1, termLenMeta_emb_ppairT1, termLenMeta_emb_bShift₀, termLenMeta_emb_bShift₀,
          termLenMeta_emb_codeTermMeta_tvote]
        omega
      · have he := ih e (by simp); have hr := ih r (by simp)
        rw [codeTermMetaAbs_cons, termLenMeta_emb_succT1, termLenMeta_emb_ppairT1, termLenMeta_emb_ppairT1,
          termLenMeta_emb_bShift₀, termLenMeta_emb_codeTermMeta_cons]
        omega
      · have hd := ih d (by simp)
        rw [codeTermMetaAbs_sys, termLenMeta_emb_succT1, termLenMeta_emb_ppairT1, termLenMeta_emb_ppairT1,
          termLenMeta_emb_bShift₀, termLenMeta_emb_bShift₀, termLenMeta_emb_codeTermMeta_sys]
        omega
    · rw [codeTermMetaAbs_leaf hx, termLenMeta_emb_bShift₀]

end length

/-! ### 8. The code equation: the code of the abstracted term is the internal `codeTermAbs` (Phase 2d)

The code-level twin `codeTermAbs k₀ s x` (`ArithS.Agents.CodeTermSlot`) is `codeTerm x` with the budget leaf
`pSearch k₀` written as the term code `s`. With the slot `^#0` it is the code of `codeTermMetaAbs k₀ x`, in
every model — the equation the member-slot identity `templateCodeAt_sysClose` (`Agents/SysTemplate.lean`) rests
on. (The quote lemmas for the one-variable combinators moved here from `Agents/InstanceV.lean`, same names.) -/

section codeEquation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The code of `#0` (one bound variable). -/
lemma quote_emb_bvar_zero : (⌜(Rew.emb (#0 : Semiterm ℒₒᵣ Empty 1) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = ^#0 := by
  simp [Rew.emb]

/-- The code of a shifted closed term is the code of the term. -/
lemma quote_emb_bShift {L : Language} [L.Encodable] [L.LORDefinable] :
    ∀ t : ClosedSemiterm L 0,
      (⌜(Rew.emb (Rew.bShift t) : SyntacticSemiterm L 1)⌝ : V) = ⌜(Rew.emb t : SyntacticSemiterm L 0)⌝
  | #x => x.elim0
  | &x => x.elim
  | .func f v => by
    rw [Rew.func, Rew.func, Rew.func, Semiterm.quote_func, Semiterm.quote_func]
    congr 1
    unfold SemitermVec.val
    exact matrixToVec_congr (fun i ↦ quote_emb_bShift (v i))

lemma quote_emb_add (s t : Semiterm ℒₒᵣ Empty 1) :
    (⌜(Rew.emb (Semiterm.func Language.ORing.Func.add ![s, t]) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
    (⌜(Rew.emb s : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) ^+ ⌜(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)⌝ := by
  rw [Rew.func]
  have e : (Semiterm.func Language.ORing.Func.add (⇑Rew.emb ∘ ![s, t]) : SyntacticSemiterm ℒₒᵣ 1) =
      ‘!!(Rew.emb s : SyntacticSemiterm ℒₒᵣ 1) + !!(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)’ := by
    congr 1; funext i; fin_cases i <;> rfl
  rw [e, Semiterm.quote_def, Semiterm.typed_quote_add]; rfl

lemma quote_emb_mul (s t : Semiterm ℒₒᵣ Empty 1) :
    (⌜(Rew.emb (Semiterm.func Language.ORing.Func.mul ![s, t]) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
    (⌜(Rew.emb s : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) ^* ⌜(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)⌝ := by
  rw [Rew.func]
  have e : (Semiterm.func Language.ORing.Func.mul (⇑Rew.emb ∘ ![s, t]) : SyntacticSemiterm ℒₒᵣ 1) =
      ‘!!(Rew.emb s : SyntacticSemiterm ℒₒᵣ 1) * !!(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)’ := by
    congr 1; funext i; fin_cases i <;> rfl
  rw [e, Semiterm.quote_def, Semiterm.typed_quote_mul]; rfl

lemma quote_emb_ppairT1 (s t : Semiterm ℒₒᵣ Empty 1) :
    (⌜(Rew.emb (ppairT1 s t) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
    ppairTerm (⌜(Rew.emb s : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) ⌜(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)⌝ := by
  rw [ppairT1, quote_emb_add, quote_emb_mul, quote_emb_add]; rfl

lemma quote_emb_oneTT : (⌜(Rew.emb oneTT : SyntacticSemiterm ℒₒᵣ 0)⌝ : V) = 𝟏 := by
  rw [← Semiterm.empty_quote_def]; exact quote_closed_one

lemma quote_emb_succT1 (t : Semiterm ℒₒᵣ Empty 1) :
    (⌜(Rew.emb (succT1 t) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
    (⌜(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) ^+ 𝟏 := by
  rw [succT1, quote_emb_add, quote_emb_bShift, quote_emb_oneTT]

/-- A non-shape stays a non-shape in every model (`IsShape` is Σ₀). -/
lemma not_isShape_cast {x : ℕ} (hx : ¬IsShape x) : ¬IsShape (x : V) := by
  have h := Defined.shigmaZero_absolute V (IsShape.defined (V := ℕ)) (IsShape.defined (V := V)) ![x]
  intro h'
  exact hx (h.mpr (by simpa using h'))

/-- The code of the budget leaf: the slot `^#0` at the abstracted budget, the numeral otherwise. -/
lemma quote_emb_budgetT1 (k₀ k : ℕ) :
    (⌜(Rew.emb (budgetT1 k₀ k) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = budgetLeaf (k₀ : V) (^#0) (k : V) := by
  by_cases h : k = k₀
  · subst h; rw [budgetT1_self, budgetLeaf_self, quote_emb_bvar_zero]
  · rw [budgetT1_of_ne h, budgetLeaf_of_ne (fun h' ↦ h (Nat.cast_injective h')), quote_emb_bShift,
      ← Semiterm.empty_quote_def, quote_binNumeralMeta]

/-- **The code equation** (Phase 2d): the code of the abstracted structural term is the internal `codeTermAbs`
with the slot `^#0`, in every model. -/
theorem quote_emb_codeTermMetaAbs (k₀ x : ℕ) :
    (⌜(Rew.emb (codeTermMetaAbs k₀ x) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTermAbs (k₀ : V) (^#0) (x : V) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    have hbn : ∀ n : ℕ, (⌜(Rew.emb (Rew.bShift (binNumeralMeta n)) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = binNumeral (n : V) := by
      intro n; rw [quote_emb_bShift, ← Semiterm.empty_quote_def, quote_binNumeralMeta]
    have hleaf : ∀ y : ℕ, (⌜(Rew.emb (Rew.bShift (codeTermMeta y)) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (y : V) := by
      intro y; rw [quote_emb_bShift, ← Semiterm.empty_quote_def, quote_codeTermMeta]
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ |
        ⟨v, θ, p, q, rfl⟩ | ⟨d, i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩
      · rw [codeTermMetaAbs_const, hleaf, cast_pConst, codeTerm_const, codeTermAbs_const]
      · rw [codeTermMetaAbs_self, hleaf, cast_pSelf, codeTerm_self, codeTermAbs_self]
      · rw [codeTermMetaAbs_opp, hleaf, cast_pOpp, codeTerm_opp, codeTermAbs_opp]
      · rw [codeTermMetaAbs_bot, quote_emb_succT1, quote_emb_ppairT1, hbn, ih p (by simp), cast_pBot, codeTermAbs_bot]
        push_cast; rfl
      · rw [codeTermMetaAbs_sim, quote_emb_succT1, quote_emb_ppairT1, quote_emb_ppairT1, hbn, ih p (by simp),
          ih q (by simp), cast_pSim, codeTermAbs_sim]
        push_cast; rfl
      · rw [codeTermMetaAbs_ite, quote_emb_succT1, quote_emb_ppairT1, quote_emb_ppairT1, quote_emb_ppairT1,
          quote_emb_ppairT1, hbn, hbn, ih b (by simp), ih p (by simp), ih q (by simp), cast_pIte, codeTermAbs_ite]
        push_cast; rfl
      · rw [codeTermMetaAbs_search, quote_emb_succT1, quote_emb_ppairT1, quote_emb_ppairT1, quote_emb_ppairT1,
          quote_emb_ppairT1, hbn, hbn, quote_emb_budgetT1, ih p (by simp), ih q (by simp), cast_pSearch,
          codeTermAbs_search]
        push_cast; rfl
      · rw [codeTermMetaAbs_tvote, quote_emb_succT1, quote_emb_ppairT1, quote_emb_ppairT1, quote_emb_ppairT1,
          quote_emb_ppairT1, hbn, hbn, ih v (by simp), ih p (by simp), ih q (by simp), cast_pTvote, codeTermAbs_tvote]
        push_cast; rfl
      · rw [codeTermMetaAbs_sys, quote_emb_succT1, quote_emb_ppairT1, quote_emb_ppairT1, hbn, hbn, ih d (by simp),
          cast_pSys, codeTermAbs_sys]
        push_cast; rfl
      · rw [codeTermMetaAbs_selfIdx, hleaf, cast_pSelfIdx, codeTerm_selfIdx, codeTermAbs_selfIdx]
      · rw [codeTermMetaAbs_cons, quote_emb_succT1, quote_emb_ppairT1, quote_emb_ppairT1, hbn, ih e (by simp),
          ih r (by simp), cast_pCons, codeTermAbs_cons]
        push_cast; rfl
    · rw [codeTermMetaAbs_of_not_shape hx, hbn, codeTermAbs_of_not_shape (not_isShape_cast hx)]

/-- The code equation in `ℕ`. -/
theorem quote_emb_codeTermMetaAbs_nat (k₀ x : ℕ) :
    (⌜(Rew.emb (codeTermMetaAbs k₀ x) : SyntacticSemiterm ℒₒᵣ 1)⌝ : ℕ) = codeTermAbs k₀ (^#0) x := by
  rw [quote_emb_codeTermMetaAbs]; simp

end codeEquation

end ArithS
