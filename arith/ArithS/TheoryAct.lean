import ArithS.LangAct
import Foundation.FirstOrder.Incompleteness.Definability
import Mathlib.Tactic.FinCases

/-!
# ArithS.TheoryAct — the theory `TAct = PA + {c_C ≠ c_D, c_D ≠ c_C}` over `LAct`

Roadmap §2.4. `PA` is transported along the inclusion `emb : ℒₒᵣ →ᵥ LAct`; the two
inequality axioms are stated in BOTH orientations so that the axiom set is literally closed
under `swap` (closure up to a one-line derivation would cost `k` vs `k + c`, and the red
cell needs an exact iff). `TAct` is Δ₁-axiomatized: since the encoding of `LAct` keeps the
`ℒₒᵣ` codes, an `ℒₒᵣ`-formula has the same code in both languages
(`quote_lMap_emb`), so PA's own Δ₁ class, conjoined with "is an `ℒₒᵣ`-formula", defines the
transported axioms. The standard model interprets `c_C ↦ 0`, `c_D ↦ 1`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open LAct

/-! ### The standard structure on ℕ -/

/-- `ℕ` as an `LAct`-structure: arithmetic as usual, `c_C ↦ 0`, `c_D ↦ 1`. -/
instance stdAct : Structure LAct ℕ where
  func _ f := match f with
    | Sum.inl f => (standardModel ℕ).func f
    | Sum.inr (Language.Constant.Func.const Act.C) => fun _ ↦ 0
    | Sum.inr (Language.Constant.Func.const Act.D) => fun _ ↦ 1
  rel _ r := match r with
    | Sum.inl r => (standardModel ℕ).rel r
    | Sum.inr e => PEmpty.elim e

lemma stdAct_lMap_emb : Structure.lMap emb stdAct = standardModel ℕ := by
  ext <;> rfl

/-- Truth of a transported `ℒₒᵣ`-sentence in `ℕ` is its truth in `ℕ`. -/
lemma models_lMap_emb (σ : Sentence ℒₒᵣ) :
    ℕ↓[LAct] ⊧ Semiformula.lMap emb σ ↔ ℕ↓[ℒₒᵣ] ⊧ σ := by
  have := Semiformula.models_lMap (s₂ := stdAct) (Φ := emb) (σ := σ) (M := ℕ)
  rw [stdAct_lMap_emb] at this
  exact this

/-! ### The theory -/

/-- The constant term `c_a`. -/
def cterm (a : Act) {ξ : Type*} {n : ℕ} : Semiterm LAct ξ n := Semiterm.func (const a) ![]

/-- `c_C ≠ c_D`. -/
def axNe : Sentence LAct := Semiformula.nrel Language.Eq.eq ![cterm Act.C, cterm Act.D]

/-- `c_D ≠ c_C`. -/
def axNe' : Sentence LAct := Semiformula.nrel Language.Eq.eq ![cterm Act.D, cterm Act.C]

/-- `TAct := PA ∪ {c_C ≠ c_D, c_D ≠ c_C}` over `LAct`. -/
abbrev TAct : Theory LAct := insert axNe (insert axNe' (Theory.lMap emb 𝗣𝗔))

/-! ### Codes agree along the embedding -/

section codes

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma quote_func_emb {k : ℕ} (f : Language.Func ℒₒᵣ k) : (⌜emb.func f⌝ : V) = (⌜f⌝ : V) := rfl
lemma quote_rel_emb {k : ℕ} (r : Language.Rel ℒₒᵣ k) : (⌜emb.rel r⌝ : V) = (⌜r⌝ : V) := rfl

lemma matrixToVec_congr {k : ℕ} {w₁ w₂ : Fin k → V} (h : ∀ i, w₁ i = w₂ i) :
    matrixToVec w₁ = matrixToVec w₂ := by
  rw [funext h]

/-- The code of `lMap emb t` is the code of `t`. -/
theorem quote_term_lMap_emb {n : ℕ} (t : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiterm.lMap emb t⌝ : V) = ⌜t⌝ := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih =>
    rw [Semiterm.lMap_func, Semiterm.quote_func, Semiterm.quote_func]
    congr 1 <;> first
      | rfl
      | (unfold SemitermVec.val; exact matrixToVec_congr (fun i ↦ ih i))

/-- The code of `lMap emb φ` is the code of `φ`. -/
theorem quote_lMap_emb {n : ℕ} (φ : Semiproposition ℒₒᵣ n) :
    (⌜Semiformula.lMap emb φ⌝ : V) = ⌜φ⌝ := by
  induction φ with
  | rel R v =>
    rw [Semiformula.lMap_rel, Semiformula.quote_rel, Semiformula.quote_rel]
    congr 1 <;> first
      | rfl
      | (unfold SemitermVec.val; exact matrixToVec_congr (fun i ↦ quote_term_lMap_emb (v i)))
  | nrel R v =>
    rw [Semiformula.lMap_nrel, Semiformula.quote_nrel, Semiformula.quote_nrel]
    congr 1 <;> first
      | rfl
      | (unfold SemitermVec.val; exact matrixToVec_congr (fun i ↦ quote_term_lMap_emb (v i)))
  | verum =>
    change (⌜Semiformula.lMap emb (⊤ : Semiproposition ℒₒᵣ _)⌝ : V) = ⌜(⊤ : Semiproposition ℒₒᵣ _)⌝
    rw [LogicalConnective.HomClass.map_top]; rfl
  | falsum =>
    change (⌜Semiformula.lMap emb (⊥ : Semiproposition ℒₒᵣ _)⌝ : V) = ⌜(⊥ : Semiproposition ℒₒᵣ _)⌝
    rw [LogicalConnective.HomClass.map_bot]; rfl
  | and φ ψ ihφ ihψ =>
    change (⌜Semiformula.lMap emb (φ ⋏ ψ)⌝ : V) = ⌜φ ⋏ ψ⌝
    rw [LogicalConnective.HomClass.map_and, Semiformula.quote_and, Semiformula.quote_and, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    change (⌜Semiformula.lMap emb (φ ⋎ ψ)⌝ : V) = ⌜φ ⋎ ψ⌝
    rw [LogicalConnective.HomClass.map_or, Semiformula.quote_or, Semiformula.quote_or, ihφ, ihψ]
  | all φ ih =>
    change (⌜Semiformula.lMap emb (∀¹ φ)⌝ : V) = ⌜∀¹ φ⌝
    rw [Semiformula.lMap_all, Semiformula.quote_all, Semiformula.quote_all, ih]
  | exs φ ih =>
    change (⌜Semiformula.lMap emb (∃¹ φ)⌝ : V) = ⌜∃¹ φ⌝
    rw [Semiformula.lMap_exs, Semiformula.quote_ex, Semiformula.quote_ex, ih]

/-- Sentences: the same, through the sentence-to-proposition coercion. -/
theorem quote_sentence_lMap_emb (σ : Sentence ℒₒᵣ) :
    (⌜Semiformula.lMap emb σ⌝ : V) = ⌜σ⌝ := by
  rw [Sentence.quote_def, Sentence.quote_def, ← Semiformula.lMap_emb, quote_lMap_emb]

end codes

/-! ### `TAct` is Δ₁-axiomatized -/

section delta1

open Arithmetic.HierarchySymbol.Semiformula

/-- "`p` is the code of an `ℒₒᵣ`-formula", as a Δ₁ semisentence. -/
noncomputable def isFormulaOR : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “p. !(isSemiformula ℒₒᵣ).sigma 0 p”)
  (.mkPi “p. !(isSemiformula ℒₒᵣ).pi 0 p”)

lemma isFormulaOR_properOn (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    isFormulaOR.ProperOn V := by
  intro v
  simp [isFormulaOR, HierarchySymbol.Semiformula.val_sigma,
    (IsSemiformula.defined (L := ℒₒᵣ) (V := V)).proper.iff']

lemma eval_isFormulaOR {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (p : V) :
    V ⊧/![p] isFormulaOR.val ↔ IsSemiformula ℒₒᵣ 0 p := by
  simp [isFormulaOR, HierarchySymbol.Semiformula.val_sigma,
    (IsSemiformula.defined (L := ℒₒᵣ) (V := V)).df]

/-- PA transported to `LAct` is Δ₁: its axioms are exactly the `ℒₒᵣ`-formula codes that PA's
own Δ₁ class accepts, because the codes agree along `emb`. -/
noncomputable instance embPA_delta1 : (Theory.lMap emb 𝗣𝗔).Δ₁ where
  ch := isFormulaOR ⋏ Theory.Δ₁ch 𝗣𝗔
  mem_iff {φ} := by
    rw [val_and]
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq, eval_isFormulaOR]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨ψ, hψ⟩ := IsSemiformula.sound (L := ℒₒᵣ) h1
      rw [← hψ] at h2
      obtain ⟨σ, hσ, rfl⟩ := (Δ₁Class.mem_iff'_s (V := ℕ) (T := 𝗣𝗔)).mp h2
      refine ⟨Semiformula.lMap emb σ, ⟨σ, hσ, rfl⟩, ?_⟩
      apply (Semiformula.quote_inj_iff (V := ℕ)).mp
      rw [← hψ, ← Semiformula.lMap_emb, quote_lMap_emb]
    · rintro ⟨σ, ⟨σ₀, hσ₀, rfl⟩, rfl⟩
      have e : (⌜(Semiformula.lMap emb σ₀ : Sentence LAct)⌝ : ℕ) = ⌜(σ₀ : Proposition ℒₒᵣ)⌝ :=
        quote_sentence_lMap_emb σ₀
      change IsSemiformula ℒₒᵣ 0 (⌜(Semiformula.lMap emb σ₀ : Sentence LAct)⌝ : ℕ) ∧
        ℕ ⊧/![(⌜(Semiformula.lMap emb σ₀ : Sentence LAct)⌝ : ℕ)] (Theory.Δ₁ch 𝗣𝗔).val
      rw [e]
      exact ⟨by simp, (Δ₁Class.mem_iff'_s (V := ℕ) (T := 𝗣𝗔)).mpr ⟨σ₀, hσ₀, rfl⟩⟩
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦
    ProperOn.and (isFormulaOR_properOn V) (by simp)

noncomputable instance : TAct.Δ₁ := inferInstance

end delta1

/-! ### `TAct` is closed under the transposition -/

section closure

lemma term_lMap_swap_emb {n : ℕ} {ξ : Type*} (t : Semiterm ℒₒᵣ ξ n) :
    Semiterm.lMap swap (Semiterm.lMap emb t) = Semiterm.lMap emb t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih => simp [Semiterm.lMap_func, Function.comp_def, ih, swap_emb]

lemma lMap_swap_emb {n : ℕ} {ξ : Type*} (φ : Semiformula ℒₒᵣ ξ n) :
    Semiformula.lMap swap (Semiformula.lMap emb φ) = Semiformula.lMap emb φ := by
  induction φ with
  | rel R v => simp [Semiformula.lMap_rel, Function.comp_def, term_lMap_swap_emb]
  | nrel R v => simp [Semiformula.lMap_nrel, Function.comp_def, term_lMap_swap_emb]
  | verum =>
    change Semiformula.lMap swap (Semiformula.lMap emb ⊤) = Semiformula.lMap emb ⊤
    simp
  | falsum =>
    change Semiformula.lMap swap (Semiformula.lMap emb ⊥) = Semiformula.lMap emb ⊥
    simp
  | and φ ψ ihφ ihψ =>
    change Semiformula.lMap swap (Semiformula.lMap emb (φ ⋏ ψ)) = Semiformula.lMap emb (φ ⋏ ψ)
    simp [ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    change Semiformula.lMap swap (Semiformula.lMap emb (φ ⋎ ψ)) = Semiformula.lMap emb (φ ⋎ ψ)
    simp [ihφ, ihψ]
  | all φ ih =>
    change Semiformula.lMap swap (Semiformula.lMap emb (∀¹ φ)) = Semiformula.lMap emb (∀¹ φ)
    simp [ih]
  | exs φ ih =>
    change Semiformula.lMap swap (Semiformula.lMap emb (∃¹ φ)) = Semiformula.lMap emb (∃¹ φ)
    simp [ih]

lemma lMap_swap_cterm_C {ξ : Type*} {n : ℕ} :
    Semiterm.lMap swap (cterm Act.C : Semiterm LAct ξ n) = cterm Act.D := by
  unfold cterm
  rw [Semiterm.lMap_func, swap_C]
  congr 1
  funext i; exact i.elim0

lemma lMap_swap_cterm_D {ξ : Type*} {n : ℕ} :
    Semiterm.lMap swap (cterm Act.D : Semiterm LAct ξ n) = cterm Act.C := by
  unfold cterm
  rw [Semiterm.lMap_func, swap_D]
  congr 1
  funext i; exact i.elim0

lemma lMap_swap_axNe : Semiformula.lMap swap axNe = axNe' := by
  unfold axNe axNe'
  rw [Semiformula.lMap_nrel]
  congr 1
  funext i; fin_cases i <;> simp [lMap_swap_cterm_C, lMap_swap_cterm_D]

lemma lMap_swap_axNe' : Semiformula.lMap swap axNe' = axNe := by
  unfold axNe axNe'
  rw [Semiformula.lMap_nrel]
  congr 1
  funext i; fin_cases i <;> simp [lMap_swap_cterm_C, lMap_swap_cterm_D]

/-- The axiom set of `TAct` is literally closed under the transposition. -/
theorem lMap_swap_mem_TAct {σ : Sentence LAct} (h : σ ∈ TAct) : Semiformula.lMap swap σ ∈ TAct := by
  rcases h with rfl | rfl | ⟨σ₀, hσ₀, rfl⟩
  · rw [lMap_swap_axNe]; exact Or.inr (Or.inl rfl)
  · rw [lMap_swap_axNe']; exact Or.inl rfl
  · rw [lMap_swap_emb]; exact Or.inr (Or.inr ⟨σ₀, hσ₀, rfl⟩)

end closure

end ArithS
