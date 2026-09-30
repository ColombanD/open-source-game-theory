import ArithS.Box.Bew
import Mathlib.Algebra.BigOperators.Fin

/-!
# ArithS.MetaLength — the code-level length agrees with the meta-level symbol count

`termLenMeta`/`formulaLenMeta` are the symbol counts on Foundation's META syntax (`SyntacticSemiterm`,
`Semiproposition`), defined by structural recursion; `termLen_quote`/`formulaLen_quote`
say the Σ₁ functions of `ArithS.Length` compute exactly them on Gödel codes, in EVERY
model `V`. This is the bridge both the properness estimate (M1) and the τ-transposition
argument (M2, `len ∘ τ = len` is proved on the meta side) run through. Sequents and
derivations follow in the second half of the file.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ### Terms -/

/-- Symbol count of a syntactic term: a variable of index `i` counts `i + 1`, a function
symbol `1`. -/
def termLenMeta {n : ℕ} : SyntacticSemiterm L n → ℕ
  | #x => x + 1
  | &x => x + 1
  | FirstOrder.Semiterm.func _ v => (∑ i, termLenMeta (v i)) + 1

@[simp] lemma termLenMeta_bvar {n : ℕ} (x : Fin n) : termLenMeta (#x : SyntacticSemiterm L n) = x + 1 := by
  simp [termLenMeta]
@[simp] lemma termLenMeta_fvar {n : ℕ} (x : ℕ) : termLenMeta (&x : SyntacticSemiterm L n) = x + 1 := by
  simp [termLenMeta]
@[simp] lemma termLenMeta_func {n k : ℕ} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    termLenMeta (FirstOrder.Semiterm.func f v) = (∑ i, termLenMeta (v i)) + 1 := by simp [termLenMeta]

lemma listSum_termLenVec {k n : ℕ} (w : SemitermVec V L k n) :
    listSum (termLenVec L ↑k w.val) = ∑ i, termLen L (w i).val := by
  induction k with
  | zero =>
    rw [SemitermVec.val_nil, Nat.cast_zero, termLenVec_nil, listSum_nil]
    simp
  | succ k ih =>
    rw [SemitermVec.val_succ, Nat.cast_succ,
      termLenVec_cons (Semiterm.isUTerm _) (SemitermVec.isUTermVec _), listSum_adjoin,
      ih, Fin.sum_univ_succ]
    rfl

theorem termLen_quote {n : ℕ} (t : SyntacticSemiterm L n) :
    termLen L (⌜t⌝ : V) = ↑(termLenMeta t) := by
  induction t with
  | bvar x => simp
  | fvar x => simp
  | func f v ih =>
    rw [Semiterm.quote_func, termLen_func (by simp) (SemitermVec.isUTermVec _),
      listSum_termLenVec, termLenMeta_func]
    push_cast
    congr 1
    exact Finset.sum_congr rfl (fun i _ ↦ ih i)

/-! ### Formulas -/

/-- Symbol count of a syntactic formula. -/
def formulaLenMeta {n : ℕ} : Semiproposition L n → ℕ
  | .rel _ v => (∑ i, termLenMeta (v i)) + 1
  | .nrel _ v => (∑ i, termLenMeta (v i)) + 1
  | .verum => 1
  | .falsum => 1
  | .and φ ψ => formulaLenMeta φ + formulaLenMeta ψ + 1
  | .or φ ψ => formulaLenMeta φ + formulaLenMeta ψ + 1
  | .all φ => formulaLenMeta φ + 1
  | .exs φ => formulaLenMeta φ + 1

theorem formulaLen_quote {n : ℕ} (φ : Semiproposition L n) :
    formulaLen L (⌜φ⌝ : V) = ↑(formulaLenMeta φ) := by
  induction φ with
  | rel R v =>
    rw [Semiformula.quote_rel, formulaLen_rel (by simp) (SemitermVec.isUTermVec _),
      listSum_termLenVec]
    simp only [formulaLenMeta]
    push_cast
    congr 1
    exact Finset.sum_congr rfl (fun i _ ↦ termLen_quote (v i))
  | nrel R v =>
    rw [Semiformula.quote_nrel, formulaLen_nrel (by simp) (SemitermVec.isUTermVec _),
      listSum_termLenVec]
    simp only [formulaLenMeta]
    push_cast
    congr 1
    exact Finset.sum_congr rfl (fun i _ ↦ termLen_quote (v i))
  | verum =>
    change formulaLen L ⌜(⊤ : Semiproposition L _)⌝ = ((1 : ℕ) : V)
    simp
  | falsum =>
    change formulaLen L ⌜(⊥ : Semiproposition L _)⌝ = ((1 : ℕ) : V)
    simp
  | and φ ψ ihφ ihψ =>
    change formulaLen L ⌜φ ⋏ ψ⌝ = ((formulaLenMeta φ + formulaLenMeta ψ + 1 : ℕ) : V)
    rw [Semiformula.quote_and, formulaLen_and (Semiformula.quote_isSemiformula _).isUFormula (Semiformula.quote_isSemiformula _).isUFormula, ihφ, ihψ]; push_cast; rfl
  | or φ ψ ihφ ihψ =>
    change formulaLen L ⌜φ ⋎ ψ⌝ = ((formulaLenMeta φ + formulaLenMeta ψ + 1 : ℕ) : V)
    rw [Semiformula.quote_or, formulaLen_or (Semiformula.quote_isSemiformula _).isUFormula (Semiformula.quote_isSemiformula _).isUFormula, ihφ, ihψ]; push_cast; rfl
  | all φ ih =>
    change formulaLen L ⌜∀¹ φ⌝ = ((formulaLenMeta φ + 1 : ℕ) : V)
    rw [Semiformula.quote_all, formulaLen_all (Semiformula.quote_isSemiformula _).isUFormula, ih]; push_cast; rfl
  | exs φ ih =>
    change formulaLen L ⌜∃¹ φ⌝ = ((formulaLenMeta φ + 1 : ℕ) : V)
    rw [Semiformula.quote_ex, formulaLen_exs (Semiformula.quote_isSemiformula _).isUFormula, ih]; push_cast; rfl

/-! ### Sequents (at `V = ℕ`) -/

section sequent

variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]

open Classical

/-- The partial sums stabilise once the index passes the set (all members are below it). -/
lemma sequentLenAux_eq_of_le {s i : ℕ} (h : s ≤ i) : sequentLenAux L s i = sequentLen L s := by
  induction i with
  | zero =>
    have : s = 0 := Nat.le_zero.mp h
    subst this; rfl
  | succ i ih =>
    rcases Nat.lt_or_ge i s with hi | hi
    · have : s = i + 1 := le_antisymm h hi
      subst this; rfl
    · have hnot : i ∉ s := fun hm ↦ absurd (lt_of_mem hm) (not_lt.mpr hi)
      rw [sequentLenAux_succ_of_not_mem hnot, ih hi]

lemma sequentLenAux_insert_of_not_mem {x s : ℕ} (hx : x ∉ s) (i : ℕ) :
    sequentLenAux L (insert x s) i = sequentLenAux L s i + (if x < i then formulaLen L x else 0) := by
  induction i with
  | zero => simp
  | succ i ih =>
    by_cases hix : i = x
    · subst hix
      rw [sequentLenAux_succ_of_mem (by simp), sequentLenAux_succ_of_not_mem hx, ih]
      simp
    · have e : (i ∈ insert x s) ↔ i ∈ s := by simp [hix]
      by_cases his : i ∈ s
      · rw [sequentLenAux_succ_of_mem (e.mpr his), sequentLenAux_succ_of_mem his, ih]
        have : (x < i + 1) ↔ x < i := by omega
        simp only [this]; split_ifs <;> omega
      · rw [sequentLenAux_succ_of_not_mem (fun h ↦ his (e.mp h)), sequentLenAux_succ_of_not_mem his, ih]
        have : (x < i + 1) ↔ x < i := by omega
        simp only [this]

lemma sequentLen_insert_of_not_mem {x s : ℕ} (hx : x ∉ s) :
    sequentLen L (insert x s) = sequentLen L s + formulaLen L x := by
  have h1 : sequentLen L (insert x s) = sequentLenAux L (insert x s) (insert x s + s + x + 1) :=
    (sequentLenAux_eq_of_le (by omega)).symm
  have h2 : sequentLen L s = sequentLenAux L s (insert x s + s + x + 1) :=
    (sequentLenAux_eq_of_le (by omega)).symm
  rw [h1, h2, sequentLenAux_insert_of_not_mem hx]
  simp [show x < insert x s + s + x + 1 by omega]

/-- The code-level sequent length is the sum of the meta symbol counts. -/
theorem sequentLen_quote (Γ : Finset (Proposition L)) : sequentLen L (⌜Γ⌝ : ℕ) = ∑ φ ∈ Γ, formulaLenMeta φ := by
  induction Γ using Finset.induction with
  | empty => simp [Derivation2.Sequent.quote_empty, emptyset_def, sequentLen]
  | insert a Γ ha ih =>
    rw [Derivation2.Sequent.quote_insert,
      sequentLen_insert_of_not_mem (by simpa [Derivation2.Sequent.mem_quote_iff] using ha),
      ih, Finset.sum_insert ha, formulaLen_quote]
    simp; omega

end sequent

/-! ### Derivations (at `V = ℕ`) -/

section derivation

variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

/-- Symbol count of a sequent. -/
abbrev sequentLenMeta (Γ : Finset (Proposition L)) : ℕ := ∑ φ ∈ Γ, formulaLenMeta φ

/-- Symbol count of a meta-level derivation: the sum over its nodes of `1 + ` the node's
sequent, plus the witness term of each `∃`-introduction — the meta twin of `proofLen`. -/
def proofLenMeta : {Γ : Finset (Proposition L)} → T ⟹₂ Γ → ℕ
  | Γ, .closed _ _ _ _ => sequentLenMeta Γ + 1
  | Γ, .axm _ _ _ => sequentLenMeta Γ + 1
  | Γ, .verum _ => sequentLenMeta Γ + 1
  | Γ, .and _ d₁ d₂ => sequentLenMeta Γ + proofLenMeta d₁ + proofLenMeta d₂ + 1
  | Γ, .or _ d => sequentLenMeta Γ + proofLenMeta d + 1
  | Γ, .all _ d => sequentLenMeta Γ + proofLenMeta d + 1
  | Γ, .exs _ t d => sequentLenMeta Γ + termLenMeta t + proofLenMeta d + 1
  | Γ, .wk d _ => sequentLenMeta Γ + proofLenMeta d + 1
  | _, .shift (Γ := Γ) d => sequentLenMeta (Γ.image Rewriting.shift) + proofLenMeta d + 1
  | Γ, .cut d₁ d₂ => sequentLenMeta Γ + proofLenMeta d₁ + proofLenMeta d₂ + 1

/-- The code of a meta derivation is an internal derivation. -/
lemma derivation_quote {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : Derivation T (⌜d⌝ : ℕ) :=
  (Derivation2.typedQuote ℕ d).derivationOf.2

/-- **The bridge**: the Σ₁ length function computes the meta symbol count on codes. -/
theorem proofLen_quote {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : proofLen T (⌜d⌝ : ℕ) = proofLenMeta d := by
  induction d with
  | closed Γ φ h hn =>
    apply proofLen_eq_of_graph (derivation_quote _)
    rw [Derivation2.quote_closed]
    exact ProofLenGraph.axL_iff.mpr (by simp [proofLenMeta, sequentLen_quote])
  | axm σ hT hΓ =>
    apply proofLen_eq_of_graph (derivation_quote _)
    rw [Derivation2.quote_axm]
    exact ProofLenGraph.axm_iff.mpr (by simp [proofLenMeta, sequentLen_quote])
  | verum h =>
    apply proofLen_eq_of_graph (derivation_quote _)
    rw [Derivation2.quote_verum]
    exact ProofLenGraph.verumIntro_iff.mpr (by simp [proofLenMeta, sequentLen_quote])
  | and h d₁ d₂ ih₁ ih₂ =>
    apply proofLen_eq_of_graph (derivation_quote _)
    rw [Derivation2.quote_and]
    exact ProofLenGraph.andIntro_iff.mpr ⟨_, _, ih₁ ▸ proofLen_graph (derivation_quote d₁),
      ih₂ ▸ proofLen_graph (derivation_quote d₂), by simp [proofLenMeta, sequentLen_quote]⟩
  | or h d ih =>
    apply proofLen_eq_of_graph (derivation_quote _)
    rw [Derivation2.quote_or]
    exact ProofLenGraph.orIntro_iff.mpr ⟨_, ih ▸ proofLen_graph (derivation_quote d),
      by simp [proofLenMeta, sequentLen_quote]⟩
  | all h d ih =>
    apply proofLen_eq_of_graph (derivation_quote _)
    rw [Derivation2.quote_all]
    exact ProofLenGraph.allIntro_iff.mpr ⟨_, ih ▸ proofLen_graph (derivation_quote d),
      by simp [proofLenMeta, sequentLen_quote]⟩
  | exs h t d ih =>
    apply proofLen_eq_of_graph (derivation_quote _)
    rw [Derivation2.quote_exs]
    exact ProofLenGraph.exsIntro_iff.mpr ⟨_, ih ▸ proofLen_graph (derivation_quote d),
      by simp [proofLenMeta, sequentLen_quote, termLen_quote]⟩
  | wk d ss ih =>
    apply proofLen_eq_of_graph (derivation_quote _)
    rw [Derivation2.quote_wk]
    exact ProofLenGraph.wkRule_iff.mpr ⟨_, ih ▸ proofLen_graph (derivation_quote d),
      by simp [proofLenMeta, sequentLen_quote]⟩
  | shift d ih =>
    apply proofLen_eq_of_graph (derivation_quote _)
    rw [Derivation2.quote_shift]
    exact ProofLenGraph.shiftRule_iff.mpr ⟨_, ih ▸ proofLen_graph (derivation_quote d),
      by simp [proofLenMeta, sequentLen_quote]⟩
  | cut d₁ d₂ ih₁ ih₂ =>
    apply proofLen_eq_of_graph (derivation_quote _)
    rw [Derivation2.quote_cut]
    exact ProofLenGraph.cutRule_iff.mpr ⟨_, _, ih₁ ▸ proofLen_graph (derivation_quote d₁),
      ih₂ ▸ proofLen_graph (derivation_quote d₂), by simp [proofLenMeta, sequentLen_quote]⟩

end derivation

end ArithS
