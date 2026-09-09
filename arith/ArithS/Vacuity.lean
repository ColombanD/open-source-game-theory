import ArithS.RedCell

/-!
# ArithS.Vacuity — under UNARY numerals no bounded search can ever succeed

Critch fixes his proof system `S` only up to four assumptions (Appendix B of `critch22`);
assumption **(b)** is that `S` "writes `k` in `O(lg k)` characters". This file proves that
the CURRENT length measure of the package violates (b) so badly that the bounded proof
search of every agent is vacuous:

* a search node `pSearch k g a p q` stores its budget `k` inside its own pair-code, so the
  code — and the canonical numeral `dnum me` by which the guard sentence names the searcher
  (`ArithS.Guard`) — is at least `k` (`le_dnum_pSearch`);
* numerals are counted in UNARY by `tlen`/`termLen` (`tlen_numeral : n ≤ tlen ↑n`);
* the guard template mentions the searcher's numeral (`Gtmpl_not_inert`: replacing that one
  term changes the truth value of the instance), so every instance of the template is
  longer than the numeral it carries (`tlen_lt_flen_Gtmpl_subst`), hence longer than `k`
  (`budget_lt_flen_guardSentence`);
* a derivation is at least as long as any formula of its conclusion (`flen_le_mlen`), so a
  proof of length `≤ k` can only prove sentences of length `≤ k`
  (`flen_le_of_lenProvable`).

Together: **the guard is never found at any budget** (`search_never_found`,
`guard_never_found_Dupoc`, `guard_never_found_Cupod`), every search node always takes its
else-branch (`search_always_else`), `Dupoc k` always defects and `Cupod k` always cooperates,
against EVERY opponent (`Dupoc_always_defects`, `Cupod_always_cooperates`).

Consequences for the roadmap. `red_cell` (`ArithS.RedCell`) remains correct and
coding-independent — its proof uses only soundness, τ-symmetry and determinism, and the
value `(D, C)` is what these theorems give as well — but the MODEL is degenerate: no Löbian
cooperation can appear while the guard costs `≥ 2k` characters against a budget of `k`.
The planned fix is a logarithmic-cost numeral clause in `termLen` (so that `tlen ↑n ~ lg n`
and a guard costs `O(lg k)`, which is exactly what (b) demands); until it lands, every
positive outcome theorem about search agents in this package would be vacuously false.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

/-! ### `flen` on the connectives (definitional equations, for `rw`) -/

section flenEqns

variable {L : Language} {n : ℕ}

@[simp] lemma flen_rel {k : ℕ} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    flen (Semiformula.rel R v) = (∑ i, tlen (v i)) + 1 := rfl
@[simp] lemma flen_nrel {k : ℕ} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    flen (Semiformula.nrel R v) = (∑ i, tlen (v i)) + 1 := rfl
@[simp] lemma flen_verum : flen (⊤ : Semiproposition L n) = 1 := rfl
@[simp] lemma flen_falsum : flen (⊥ : Semiproposition L n) = 1 := rfl
@[simp] lemma flen_and (φ ψ : Semiproposition L n) : flen (φ ⋏ ψ) = flen φ + flen ψ + 1 := rfl
@[simp] lemma flen_or (φ ψ : Semiproposition L n) : flen (φ ⋎ ψ) = flen φ + flen ψ + 1 := rfl
@[simp] lemma flen_all (φ : Semiproposition L (n + 1)) : flen (∀¹ φ) = flen φ + 1 := rfl
@[simp] lemma flen_exs (φ : Semiproposition L (n + 1)) : flen (∃¹ φ) = flen φ + 1 := rfl

end flenEqns

/-! ### 1. A derivation is at least as long as every formula of its conclusion -/

section derivation

variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

/-- A derivation is at least as long as any formula of its conclusion (every node of `mlen`
charges its whole conclusion sequent: `sqlen_le_mlen`, `ArithS.Proper`). -/
lemma flen_le_mlen {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) {σ : Proposition L} (h : σ ∈ Γ) :
    flen σ ≤ mlen d :=
  le_trans (flen_le_sqlen h) (sqlen_le_mlen d)

end derivation

/-! ### 2. A proof of length `≤ k` only proves sentences of length `≤ k` -/

/-- Length-bounded provability bounds the length of the sentence proved. -/
theorem flen_le_of_lenProvable {σ : Sentence LAct} {k : ℕ}
    (h : LenProvable (fbound : ℕ → ℕ) k TAct (⌜σ⌝ : ℕ)) : flen (σ : Proposition LAct) ≤ k := by
  rcases h with ⟨d, _, hd, hk⟩
  have e : (ORingStructure.numeral k : ℕ) = k := by simp
  rw [Sentence.quote_def] at hd
  obtain ⟨b, rfl⟩ := Proof.sound' hd
  rw [dlen_quote, e] at hk
  have hk' : mlen b ≤ k := by
    rcases le_def.mp hk with h | h
    · exact Nat.le_of_eq h
    · exact Nat.le_of_lt h
  exact le_trans (flen_le_mlen b (Finset.mem_singleton_self _)) hk'

/-! ### 3a. Numerals are counted in unary -/

section numeral

lemma tlen_add_operator {m : ℕ} (v : Fin 2 → SyntacticSemiterm ℒₒᵣ m) :
    tlen (Semiterm.Operator.Add.add.operator v) = tlen (v 0) + tlen (v 1) + 1 := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Fin.sum_univ_two]

lemma tlen_one_operator {m : ℕ} :
    tlen ((Semiterm.Operator.One.one : Semiterm.Const ℒₒᵣ).operator ![] : SyntacticSemiterm ℒₒᵣ m) = 1 := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.One.term_eq]

lemma numeral_operator_add_two {m : ℕ} (k : ℕ) :
    ((Semiterm.Operator.numeral ℒₒᵣ (k + 2)).operator ![] : SyntacticSemiterm ℒₒᵣ m) =
    Semiterm.Operator.Add.add.operator
      ![(Semiterm.Operator.numeral ℒₒᵣ (k + 1)).operator ![], (Semiterm.Operator.One.one).operator ![]] := by
  rw [Semiterm.Operator.numeral_add_two, Semiterm.Operator.operator_comp]
  congr 1
  funext i; fin_cases i <;> rfl

/-- The unary count: the numeral `k` has at least `k` symbols (exactly `2k - 1` for `k ≥ 1`). -/
theorem tlen_numeral_operator {m : ℕ} :
    ∀ k : ℕ, k ≤ tlen ((Semiterm.Operator.numeral ℒₒᵣ k).operator ![] : SyntacticSemiterm ℒₒᵣ m)
  | 0 => Nat.zero_le _
  | 1 => by rw [Semiterm.Operator.numeral_one, tlen_one_operator]
  | k + 2 => by
    rw [numeral_operator_add_two, tlen_add_operator]
    have := tlen_numeral_operator (m := m) (k + 1)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega

/-- `n ≤ tlen ↑n`: under the unary measure a numeral is as long as its value. -/
theorem tlen_numeral (k : ℕ) : k ≤ tlen (↑k : SyntacticSemiterm ℒₒᵣ 0) := tlen_numeral_operator k

theorem tlen_emb_numeral (k : ℕ) :
    k ≤ tlen (Rew.emb (↑k : ClosedSemiterm ℒₒᵣ 0) : SyntacticSemiterm ℒₒᵣ 0) := by
  have e : (Rew.emb (↑k : ClosedSemiterm ℒₒᵣ 0) : SyntacticSemiterm ℒₒᵣ 0) = ↑k := by simp
  rw [e]
  exact tlen_numeral k

/-- The `LAct` numeral term of the descriptions (`ArithS.Template`) is as long as its value. -/
theorem tlen_emb_numT (k : ℕ) : k ≤ tlen (Rew.emb (numT k) : SyntacticSemiterm LAct 0) := by
  unfold numT
  rw [term_emb_lMap_emb, tlen_lMap]
  exact tlen_emb_numeral k

end numeral

/-! ### 3b. A substituted term is shorter than the result, unless the variable is inert

`TInert i t` / `FInert i φ`: two rewriters that agree on every variable except `#i` agree on
`t` / `φ` — the substitution-invariant way of saying "`#i` does not occur". The dichotomy
lemmas say: either `#i` is inert, or its image contributes its full length to the image of
the term/formula. -/

section occurrence

variable {L : Language} [L.Encodable] [L.LORDefinable] {ξ : Type*}

/-- `#i` is inert in the term `t`. -/
def TInert {n : ℕ} (i : Fin n) (t : Semiterm L ξ n) : Prop :=
  ∀ ⦃m : ℕ⦄ (ω₁ ω₂ : Rew L ξ n ℕ m),
    (∀ j, j ≠ i → ω₁ #j = ω₂ #j) → (∀ x, ω₁ &x = ω₂ &x) → ω₁ t = ω₂ t

/-- `#i` is inert in the formula `φ`. -/
def FInert {n : ℕ} (i : Fin n) (φ : Semiformula L ξ n) : Prop :=
  ∀ ⦃m : ℕ⦄ (ω₁ ω₂ : Rew L ξ n ℕ m),
    (∀ j, j ≠ i → ω₁ #j = ω₂ #j) → (∀ x, ω₁ &x = ω₂ &x) → ω₁ ▹ φ = ω₂ ▹ φ

lemma tlen_le_bShift {n : ℕ} : ∀ t : SyntacticSemiterm L n, tlen t ≤ tlen (Rew.bShift t)
  | #x => by simp only [Rew.bShift_bvar, tlen_bvar, Fin.val_succ]; omega
  | &x => by simp
  | .func f v => by
    rw [Rew.func, tlen_func, tlen_func]
    exact Nat.add_le_add_right (Finset.sum_le_sum fun j _ ↦ tlen_le_bShift (v j)) 1

theorem tlen_le_of_rew_or_inert {n m : ℕ} (i : Fin n) (ω : Rew L ξ n ℕ m) :
    ∀ t : Semiterm L ξ n, tlen (ω #i) ≤ tlen (ω t) ∨ TInert i t
  | #x => by
    by_cases hx : x = i
    · subst hx; exact Or.inl le_rfl
    · exact Or.inr fun _ ω₁ ω₂ hb _ ↦ hb x hx
  | &x => Or.inr fun _ ω₁ ω₂ _ hf ↦ hf x
  | .func f v => by
    by_cases h : ∃ j, tlen (ω #i) ≤ tlen (ω (v j))
    · rcases h with ⟨j, hj⟩
      left
      rw [Rew.func, tlen_func]
      exact le_trans hj (le_trans
        (Finset.single_le_sum (f := fun j ↦ tlen ((ω ∘ v) j)) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j))
        (Nat.le_add_right _ 1))
    · right
      intro m ω₁ ω₂ hb hf
      rw [Rew.func, Rew.func]
      congr 1
      funext j
      rcases tlen_le_of_rew_or_inert i ω (v j) with hj | hj
      · exact absurd hj (not_exists.mp h j)
      · exact hj ω₁ ω₂ hb hf

theorem tlen_lt_flen_of_rew_or_inert {n : ℕ} (φ : Semiformula L ξ n) :
    ∀ {m : ℕ} (i : Fin n) (ω : Rew L ξ n ℕ m), tlen (ω #i) < flen (ω ▹ φ) ∨ FInert i φ := by
  induction φ with
  | verum =>
    intro m i ω
    right
    intro m ω₁ ω₂ _ _
    show ω₁ ▹ (⊤ : Semiformula L ξ _) = ω₂ ▹ ⊤
    rw [LogicalConnective.HomClass.map_top, LogicalConnective.HomClass.map_top]
  | falsum =>
    intro m i ω
    right
    intro m ω₁ ω₂ _ _
    show ω₁ ▹ (⊥ : Semiformula L ξ _) = ω₂ ▹ ⊥
    rw [LogicalConnective.HomClass.map_bot, LogicalConnective.HomClass.map_bot]
  | rel R v =>
    intro m i ω
    rw [Semiformula.rew_rel, flen_rel]
    by_cases h : ∃ j, tlen (ω #i) ≤ tlen (ω (v j))
    · rcases h with ⟨j, hj⟩
      exact Or.inl (Nat.lt_succ_of_le (le_trans hj
        (Finset.single_le_sum (f := fun j ↦ tlen (ω (v j))) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j))))
    · right
      intro m ω₁ ω₂ hb hf
      rw [Semiformula.rew_rel, Semiformula.rew_rel]
      congr 1
      funext j
      rcases tlen_le_of_rew_or_inert i ω (v j) with hj | hj
      · exact absurd hj (not_exists.mp h j)
      · exact hj ω₁ ω₂ hb hf
  | nrel R v =>
    intro m i ω
    rw [Semiformula.rew_nrel, flen_nrel]
    by_cases h : ∃ j, tlen (ω #i) ≤ tlen (ω (v j))
    · rcases h with ⟨j, hj⟩
      exact Or.inl (Nat.lt_succ_of_le (le_trans hj
        (Finset.single_le_sum (f := fun j ↦ tlen (ω (v j))) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j))))
    · right
      intro m ω₁ ω₂ hb hf
      rw [Semiformula.rew_nrel, Semiformula.rew_nrel]
      congr 1
      funext j
      rcases tlen_le_of_rew_or_inert i ω (v j) with hj | hj
      · exact absurd hj (not_exists.mp h j)
      · exact hj ω₁ ω₂ hb hf
  | and φ ψ ihφ ihψ =>
    intro m i ω
    show tlen (ω #i) < flen (ω ▹ (φ ⋏ ψ)) ∨ FInert i (φ ⋏ ψ)
    rw [LogicalConnective.HomClass.map_and, flen_and]
    rcases ihφ i ω with h | h
    · exact Or.inl (by omega)
    rcases ihψ i ω with h' | h'
    · exact Or.inl (by omega)
    right
    intro m ω₁ ω₂ hb hf
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and,
      h ω₁ ω₂ hb hf, h' ω₁ ω₂ hb hf]
  | or φ ψ ihφ ihψ =>
    intro m i ω
    show tlen (ω #i) < flen (ω ▹ (φ ⋎ ψ)) ∨ FInert i (φ ⋎ ψ)
    rw [LogicalConnective.HomClass.map_or, flen_or]
    rcases ihφ i ω with h | h
    · exact Or.inl (by omega)
    rcases ihψ i ω with h' | h'
    · exact Or.inl (by omega)
    right
    intro m ω₁ ω₂ hb hf
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or,
      h ω₁ ω₂ hb hf, h' ω₁ ω₂ hb hf]
  | all φ ih =>
    intro m i ω
    show tlen (ω #i) < flen (ω ▹ (∀¹ φ)) ∨ FInert i (∀¹ φ)
    rw [Rewriting.app_all, flen_all]
    rcases ih i.succ ω.q with h | h
    · left
      rw [Rew.q_bvar_succ] at h
      exact lt_of_le_of_lt (tlen_le_bShift _) (Nat.lt_succ_of_lt h)
    · right
      intro m ω₁ ω₂ hb hf
      rw [Rewriting.app_all, Rewriting.app_all]
      congr 1
      apply h ω₁.q ω₂.q
      · intro j hj
        cases j using Fin.cases with
        | zero => simp
        | succ j => rw [Rew.q_bvar_succ, Rew.q_bvar_succ, hb j (fun e ↦ hj (by rw [e]))]
      · intro x
        rw [Rew.q_fvar, Rew.q_fvar, hf x]
  | exs φ ih =>
    intro m i ω
    show tlen (ω #i) < flen (ω ▹ (∃¹ φ)) ∨ FInert i (∃¹ φ)
    rw [Rewriting.app_exs, flen_exs]
    rcases ih i.succ ω.q with h | h
    · left
      rw [Rew.q_bvar_succ] at h
      exact lt_of_le_of_lt (tlen_le_bShift _) (Nat.lt_succ_of_lt h)
    · right
      intro m ω₁ ω₂ hb hf
      rw [Rewriting.app_exs, Rewriting.app_exs]
      congr 1
      apply h ω₁.q ω₂.q
      · intro j hj
        cases j using Fin.cases with
        | zero => simp
        | succ j => rw [Rew.q_bvar_succ, Rew.q_bvar_succ, hb j (fun e ↦ hj (by rw [e]))]
      · intro x
        rw [Rew.q_fvar, Rew.q_fvar, hf x]

end occurrence

/-! ### 3c. The guard template mentions the searcher's numeral

Its first variable `x₁` is NOT inert: the instance for `me = pConst 2` against `pOpp` is
false ("`pOpp` plays `C` against `pConst 2`" — it plays `2`), and replacing only the
numeral of `me` by that of `pConst 0` makes it true. So every instance of `Gtmpl` is longer
than the numeral term it carries in position `0`. -/

/-- The truth of an arbitrary instance of the template (generalizes `models_guardSentence_iff`). -/
theorem models_Gtmpl_subst_iff (w : Fin 7 → ClosedSemiterm LAct 0) :
    ℕ↓[LAct] ⊧ (Gtmpl ⇜ w) ↔
    ∃ n, EvalGraph n
      (relabel ((w 4).val (s := stdAct) ![] Empty.elim) ((w 5).val (s := stdAct) ![] Empty.elim)
        ((w 3).val (s := stdAct) ![] Empty.elim))
      (relabel ((w 1).val (s := stdAct) ![] Empty.elim) ((w 2).val (s := stdAct) ![] Empty.elim)
        ((w 0).val (s := stdAct) ![] Empty.elim))
      (relabel ((w 4).val (s := stdAct) ![] Empty.elim) ((w 5).val (s := stdAct) ![] Empty.elim)
        ((w 3).val (s := stdAct) ![] Empty.elim))
      ((w 6).val (s := stdAct) ![] Empty.elim) := by
  rw [models_iff]
  unfold Gtmpl Semiformula.Realize
  rw [Semiformula.eval_substs, Semiformula.eval_lMap, stdAct_lMap_emb]
  exact eval_gtmpl (V := ℕ) _

/-- The probe: the descriptions of `(pConst 2, pOpp, C)`. -/
noncomputable def probeW : Fin 7 → ClosedSemiterm LAct 0 := descTerms (pConst 2) pOpp 0

/-- The probe with the searcher's numeral replaced by that of `pConst 0`. -/
noncomputable def probeW' : Fin 7 → ClosedSemiterm LAct 0 := Function.update probeW 0 (numT (pConst 0))

lemma probeW'_ne (j : Fin 7) (hj : j ≠ 0) : probeW' j = probeW j := Function.update_of_ne hj _ _
lemma probeW'_zero : probeW' 0 = numT (pConst 0) := Function.update_self _ _ _

lemma swapcode_pConst_two : swapcode (pConst 2 : ℕ) = pConst 2 := by
  simp only [swapcode, relabel_const]; congr 1; simp [relabelAct]

lemma val_dUT_pConst_two : (dUT (pConst 2)).val (s := stdAct) ![] Empty.elim = 0 := by
  unfold dUT
  rw [swapcode_pConst_two, if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _)]
  exact val_numT 0

lemma val_dWT_pConst_two : (dWT (pConst 2)).val (s := stdAct) ![] Empty.elim = 1 := by
  unfold dWT
  rw [swapcode_pConst_two, if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _)]
  exact val_numT 1

lemma probeW'_opp :
    relabel ((probeW' 4).val (s := stdAct) ![] Empty.elim) ((probeW' 5).val (s := stdAct) ![] Empty.elim)
      ((probeW' 3).val (s := stdAct) ![] Empty.elim) = pOpp := by
  rw [probeW'_ne 4 (by decide), probeW'_ne 5 (by decide), probeW'_ne 3 (by decide)]
  change relabel ((dUT pOpp).val (s := stdAct) ![] Empty.elim) ((dWT pOpp).val (s := stdAct) ![] Empty.elim)
    ((dnumT pOpp).val (s := stdAct) ![] Empty.elim) = pOpp
  rw [val_dnumT]
  exact relabel_val_desc pOpp

lemma probeW'_me :
    relabel ((probeW' 1).val (s := stdAct) ![] Empty.elim) ((probeW' 2).val (s := stdAct) ![] Empty.elim)
      ((probeW' 0).val (s := stdAct) ![] Empty.elim) = pConst 0 := by
  rw [probeW'_ne 1 (by decide), probeW'_ne 2 (by decide), probeW'_zero]
  change relabel ((dUT (pConst 2)).val (s := stdAct) ![] Empty.elim)
    ((dWT (pConst 2)).val (s := stdAct) ![] Empty.elim) ((numT (pConst 0)).val (s := stdAct) ![] Empty.elim) = pConst 0
  rw [val_dUT_pConst_two, val_dWT_pConst_two, val_numT]
  exact relabel_zero_one _

lemma probeW'_act : (probeW' 6).val (s := stdAct) ![] Empty.elim = 0 := by
  rw [probeW'_ne 6 (by decide)]
  exact val_actT 0

/-- The modified probe is TRUE: `pOpp` plays `C` against `pConst 0`. -/
theorem models_Gtmpl_probeW' : ℕ↓[LAct] ⊧ (Gtmpl ⇜ probeW') := by
  rw [models_Gtmpl_subst_iff, probeW'_opp, probeW'_me, probeW'_act]
  refine ⟨2, ?_⟩
  show EvalGraph (1 + 1) pOpp (pConst 0) pOpp 0
  rw [EvalGraph.opp_iff]
  exact (EvalGraph.const_iff (n := 0)).mpr rfl

/-- The probe is FALSE: `pOpp` plays `2`, not `C`, against `pConst 2`. -/
theorem not_models_Gtmpl_probeW : ¬ ℕ↓[LAct] ⊧ (Gtmpl ⇜ probeW) := by
  change ¬ ℕ↓[LAct] ⊧ guardSentence (pConst 2) pOpp 0
  rw [models_guardSentence_iff]
  rintro ⟨n, hn⟩
  have h2 : EvalGraph 2 pOpp (pConst 2) pOpp 2 := by
    show EvalGraph (1 + 1) pOpp (pConst 2) pOpp 2
    rw [EvalGraph.opp_iff]
    exact (EvalGraph.const_iff (n := 0)).mpr rfl
  exact absurd (EvalGraph.unique' hn h2) (by decide)

/-- The template's first variable (the searcher's numeral) is not inert. -/
theorem Gtmpl_not_inert : ¬ FInert (0 : Fin 7) (Rewriting.emb Gtmpl : Semiproposition LAct 7) := by
  intro h
  have e : Gtmpl ⇜ probeW = Gtmpl ⇜ probeW' :=
    (Semiformula.coe_inj _ _).mp
      ((Semiformula.coe_subst_eq_subst_coe Gtmpl probeW).trans
        ((h (Rew.subst fun i ↦ (Rew.emb (probeW i) : SyntacticSemiterm LAct 0))
            (Rew.subst fun i ↦ (Rew.emb (probeW' i) : SyntacticSemiterm LAct 0))
            (fun j hj ↦ by simp [probeW'_ne j hj]) (fun x ↦ by simp)).trans
          (Semiformula.coe_subst_eq_subst_coe Gtmpl probeW').symm))
  exact not_models_Gtmpl_probeW (e ▸ models_Gtmpl_probeW')

/-- **Every instance of the guard template is longer than its first description term.** -/
theorem tlen_lt_flen_Gtmpl_subst (w : Fin 7 → ClosedSemiterm LAct 0) :
    tlen (Rew.emb (w 0) : SyntacticSemiterm LAct 0) < flen (Rewriting.emb (Gtmpl ⇜ w) : Proposition LAct) := by
  rw [Semiformula.coe_subst_eq_subst_coe]
  rcases tlen_lt_flen_of_rew_or_inert (Rewriting.emb Gtmpl : Semiproposition LAct 7) 0
    (Rew.subst fun i ↦ (Rew.emb (w i) : SyntacticSemiterm LAct 0)) with h | h
  · simpa using h
  · exact absurd h Gtmpl_not_inert

/-! ### 4. The budget is below the searcher's canonical numeral -/

lemma le_dnum_of_le {k x : ℕ} (h₁ : k ≤ x) (h₂ : k ≤ swapcode x) : k ≤ dnum x := by
  unfold dnum
  split_ifs <;> assumption

/-- A search node's budget is a component of its pair-code, and of its transposition's. -/
theorem le_dnum_pSearch (k g a p q : ℕ) : k ≤ dnum (pSearch k g a p q) :=
  le_dnum_of_le (Nat.le_of_lt (k_lt_pSearch _ _ _ _ _)) (by
    simp only [swapcode, relabel_search]
    exact Nat.le_of_lt (k_lt_pSearch _ _ _ _ _))

theorem le_dnum_Dupoc (k : ℕ) : k ≤ dnum (Dupoc k) := le_dnum_pSearch _ _ _ _ _
theorem le_dnum_Cupod (k : ℕ) : k ≤ dnum (Cupod k) := le_dnum_pSearch _ _ _ _ _

/-! ### 5. The theorems -/

/-- **The guard of a searcher of budget `k` is longer than `k`**, for any program `me` whose
canonical numeral is at least `k` — in particular for every search node of budget `k`. -/
theorem budget_lt_flen_guardSentence {k me : ℕ} (hk : k ≤ dnum me) (opp a : ℕ) :
    k < flen (Rewriting.emb (guardSentence me opp a) : Proposition LAct) := by
  have h2 : tlen (Rew.emb (dnumT me) : SyntacticSemiterm LAct 0) <
      flen (Rewriting.emb (guardSentence me opp a) : Proposition LAct) :=
    tlen_lt_flen_Gtmpl_subst (descTerms me opp a)
  have h3 : dnum me ≤ tlen (Rew.emb (dnumT me) : SyntacticSemiterm LAct 0) := tlen_emb_numT _
  omega

/-- **No bounded search ever succeeds** (for any searcher whose canonical numeral is at least
its budget): the guard sentence is longer than the budget, and a proof is at least as long
as its conclusion. -/
theorem guard_never_found_of_le {k me : ℕ} (hk : k ≤ dnum me) (opp a : ℕ) :
    ¬ LenProvableV TAct k (guardCode (⌜Gtmpl⌝ : ℕ) me opp a) := by
  intro h
  rw [← quote_guardSentence, lenProvableV_nat] at h
  have h1 : flen (Rewriting.emb (guardSentence me opp a) : Proposition LAct) ≤ k :=
    flen_le_of_lenProvable h
  have h2 := budget_lt_flen_guardSentence hk opp a
  omega

/-- Every search node of the restricted template fails its own search, at every budget. -/
theorem search_never_found (k a p q opp a' : ℕ) :
    ¬ LenProvableV TAct k (guardCode (⌜Gtmpl⌝ : ℕ) (pSearch k (⌜Gtmpl⌝ : ℕ) a p q) opp a') :=
  guard_never_found_of_le (le_dnum_pSearch _ _ _ _ _) opp a'

/-- Hence every search node always takes its else-branch. -/
theorem search_always_else (k a p q opp x n : ℕ) :
    EvalGraph (n + 1) (pSearch k (⌜Gtmpl⌝ : ℕ) a p q) opp (pSearch k (⌜Gtmpl⌝ : ℕ) a p q) x ↔
    EvalGraph n (pSearch k (⌜Gtmpl⌝ : ℕ) a p q) opp q x := by
  rw [EvalGraph.search_iff]
  have hg := search_never_found k a p q opp a
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact absurd h hg
    · exact h
  · intro h
    exact Or.inr ⟨hg, h⟩

theorem guard_never_found_Dupoc (k opp a : ℕ) :
    ¬ LenProvableV TAct k (guardCode (⌜Gtmpl⌝ : ℕ) (Dupoc k) opp a) :=
  guard_never_found_of_le (le_dnum_Dupoc k) opp a

theorem guard_never_found_Cupod (k opp a : ℕ) :
    ¬ LenProvableV TAct k (guardCode (⌜Gtmpl⌝ : ℕ) (Cupod k) opp a) :=
  guard_never_found_of_le (le_dnum_Cupod k) opp a

/-- **`Dupoc k` defects against every opponent** (fuel `2` suffices). -/
theorem Dupoc_always_defects (k opp : ℕ) : EvalGraph 2 (Dupoc k) opp (Dupoc k) 1 := by
  show EvalGraph (1 + 1) (Dupoc k) opp (pSearch k (⌜Gtmpl⌝ : ℕ) 0 (pConst 0) (pConst 1)) 1
  rw [EvalGraph.search_iff]
  exact Or.inr ⟨guard_never_found_Dupoc k opp 0, (EvalGraph.const_iff (n := 0)).mpr rfl⟩

/-- **`Cupod k` cooperates with every opponent** (fuel `2` suffices). -/
theorem Cupod_always_cooperates (k opp : ℕ) : EvalGraph 2 (Cupod k) opp (Cupod k) 0 := by
  show EvalGraph (1 + 1) (Cupod k) opp (pSearch k (⌜Gtmpl⌝ : ℕ) 1 (pConst 1) (pConst 0)) 0
  rw [EvalGraph.search_iff]
  exact Or.inr ⟨guard_never_found_Cupod k opp 1, (EvalGraph.const_iff (n := 0)).mpr rfl⟩

/-- No other action at any fuel: `Dupoc k` is extensionally `DefectBot`. -/
theorem Dupoc_defects_unique {k opp n a : ℕ} (h : EvalGraph n (Dupoc k) opp (Dupoc k) a) : a = 1 :=
  EvalGraph.unique' h (Dupoc_always_defects k opp)

/-- No other action at any fuel: `Cupod k` is extensionally `CooperateBot`. -/
theorem Cupod_cooperates_unique {k opp n a : ℕ} (h : EvalGraph n (Cupod k) opp (Cupod k) a) : a = 0 :=
  EvalGraph.unique' h (Cupod_always_cooperates k opp)

end ArithS
