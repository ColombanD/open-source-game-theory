import ArithS.Theory.LangAct
import Foundation.FirstOrder.Incompleteness.Definability
import Mathlib.Tactic.FinCases

/-!
# ArithS.TheoryAct — the theory `TAct = PA + {(c_C, c_D) ∈ {(0,1), (1,0)}} + {c_C ≠ c_D}` over `LAct`

Roadmap §2.4. `PA` is transported along the inclusion `emb : ℒₒᵣ →ᵥ LAct`. The action axioms:

* **`actionAxiom : (c_C = 0 ∧ c_D = 1) ∨ (c_C = 1 ∧ c_D = 0)`** (U0b) — the action
  constants ARE the two action values, in one of the two orders. Without it (with only
  `c_C ≠ c_D`, the theory before U0b) a model of `TAct` may read `c_C ↦ 5, c_D ↦ 7`; the guard
  sentences of the search bots feed the constants as action VALUES into `revalue` (only
  meaningful on `{0, 1}`), so in such a model the described program is garbage, its search finds
  nothing, and every guard sentence is FALSE there: `TAct ⊬ guard` for every `k`, and no Löbian
  cell could ever be proved in the arithmetized `S'` (the model-class finding of
  `ArithS/Transparency.lean`: the truth equations hold only in the standard readings). With
  `actionAxiom`, every real-equality model of `TAct` reads the constants as `(0, 1)` or `(1, 0)` —
  `structure_eq_of_actionAxiom`: the structure IS `stdReading M` or `swappedReading M`.
* `constNe : c_C ≠ c_D` (implied by `actionAxiom` over PA; kept — the downstream membership chains
  expect it and it costs nothing).

Every axiom is stated in BOTH orientations (`actionAxiom'`, `constNe'`) so that the axiom set is
literally closed under `swap` (closure up to a one-line derivation would cost `k` vs `k + c`,
and the red cell needs an exact iff). `TAct` is Δ₁-axiomatized: since the encoding of `LAct`
keeps the `ℒₒᵣ` codes, an `ℒₒᵣ`-formula has the same code in both languages
(`quote_lMap_emb`), so PA's own Δ₁ class, conjoined with "is an `ℒₒᵣ`-formula", defines the
transported axioms; the four action sentences are `insert`ed (Foundation's `Theory.Δ₁.insert`,
two short closed codes each). The standard model interprets `c_C ↦ 0`, `c_D ↦ 1`.

**Reading guide.** Definition: §The standard structure on ℕ and §The theory (`actionAxiom`, `constNe`, `TAct`) — the first hundred lines. Foundation plumbing: §Codes agree along the embedding and §`TAct` is Δ₁-axiomatized — skip on first reading. Facts: §closed under the transposition, and §The standard readings (`stdReading`/`swappedReading`, `structure_eq_of_actionAxiom`) — the two readings the positive method completes over. At ℕ: `TAct_sound_nat` (`ArithS.Readings`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open LAct

/-! ### The standard structure on ℕ -/

/-- `ℕ` as an `LAct`-structure: arithmetic as usual, `c_C ↦ 0`, `c_D ↦ 1`. -/
instance stdReadingNat : Structure LAct ℕ where
  func _ f := match f with
    | Sum.inl f => (standardModel ℕ).func f
    | Sum.inr (Language.Constant.Func.const Act.C) => fun _ ↦ 0
    | Sum.inr (Language.Constant.Func.const Act.D) => fun _ ↦ 1
  rel _ r := match r with
    | Sum.inl r => (standardModel ℕ).rel r
    | Sum.inr e => PEmpty.elim e

lemma stdReadingNat_lMap_emb : Structure.lMap emb stdReadingNat = standardModel ℕ := by
  ext <;> rfl

/-- Truth of a transported `ℒₒᵣ`-sentence in `ℕ` is its truth in `ℕ`. -/
lemma models_lMap_emb (σ : Sentence ℒₒᵣ) :
    ℕ↓[LAct] ⊧ Semiformula.lMap emb σ ↔ ℕ↓[ℒₒᵣ] ⊧ σ := by
  have := Semiformula.models_lMap (s₂ := stdReadingNat) (Φ := emb) (σ := σ) (M := ℕ)
  rw [stdReadingNat_lMap_emb] at this
  exact this

/-! ### The theory -/

/-- The constant term `c_a`. -/
def cterm (a : Act) {ξ : Type*} {n : ℕ} : Semiterm LAct ξ n := Semiterm.func (const a) ![]

/-- `c_C ≠ c_D`. -/
def constNe : Sentence LAct := Semiformula.nrel Language.Eq.eq ![cterm Act.C, cterm Act.D]

/-- `c_D ≠ c_C`. -/
def constNe' : Sentence LAct := Semiformula.nrel Language.Eq.eq ![cterm Act.D, cterm Act.C]

/-- The constant term `0` of `LAct` (the `ℒₒᵣ` symbol along `emb`). -/
def zeroT {ξ : Type*} {n : ℕ} : Semiterm LAct ξ n := Semiterm.func (emb.func Language.Zero.zero) ![]

/-- The constant term `1` of `LAct` (the `ℒₒᵣ` symbol along `emb`). -/
def oneT {ξ : Type*} {n : ℕ} : Semiterm LAct ξ n := Semiterm.func (emb.func Language.One.one) ![]

/-- `t = u`, as the atomic `LAct`-formula. -/
def eqF {ξ : Type*} {n : ℕ} (t u : Semiterm LAct ξ n) : Semiformula LAct ξ n :=
  Semiformula.rel Language.Eq.eq ![t, u]

/-- **The action axiom** `(c_C = 0 ∧ c_D = 1) ∨ (c_C = 1 ∧ c_D = 0)`: the constants are the two
action values, in one of the two (τ-symmetric) orders. -/
def actionAxiom : Sentence LAct :=
  (eqF (cterm Act.C) zeroT ⋏ eqF (cterm Act.D) oneT) ⋎ (eqF (cterm Act.C) oneT ⋏ eqF (cterm Act.D) zeroT)

/-- The action axiom with the constants transposed, `(c_D = 0 ∧ c_C = 1) ∨ (c_D = 1 ∧ c_C = 0)`
— literally `Semiformula.lMap swap actionAxiom` (`lMap_swap_actionAxiom`). -/
def actionAxiom' : Sentence LAct :=
  (eqF (cterm Act.D) zeroT ⋏ eqF (cterm Act.C) oneT) ⋎ (eqF (cterm Act.D) oneT ⋏ eqF (cterm Act.C) zeroT)

/-- `TAct := PA ∪ {actionAxiom, actionAxiom', c_C ≠ c_D, c_D ≠ c_C}` over `LAct`. -/
abbrev TAct : Theory LAct :=
  insert actionAxiom (insert actionAxiom' (insert constNe (insert constNe' (Theory.lMap emb 𝗣𝗔))))

/-! The membership facts every consumer uses (never re-derive the `insert` chain downstream). -/

lemma actionAxiom_mem_TAct : actionAxiom ∈ TAct := Set.mem_insert _ _

lemma actionAxiom'_mem_TAct : actionAxiom' ∈ TAct := Set.mem_insert_of_mem _ (Set.mem_insert _ _)

lemma constNe_mem_TAct : constNe ∈ TAct :=
  Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

lemma constNe'_mem_TAct : constNe' ∈ TAct :=
  Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))

lemma lMap_emb_PA_subset_TAct : Theory.lMap emb 𝗣𝗔 ⊆ TAct := fun _ h ↦
  Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ h)))

lemma lMap_emb_mem_TAct {σ : Sentence ℒₒᵣ} (h : σ ∈ 𝗣𝗔) : Semiformula.lMap emb σ ∈ TAct :=
  lMap_emb_PA_subset_TAct ⟨σ, h, rfl⟩

/-- Case analysis on the axioms of `TAct`. -/
lemma mem_TAct_iff {σ : Sentence LAct} :
    σ ∈ TAct ↔ σ = actionAxiom ∨ σ = actionAxiom' ∨ σ = constNe ∨ σ = constNe' ∨ ∃ σ₀ ∈ 𝗣𝗔, Semiformula.lMap emb σ₀ = σ :=
  Iff.rfl

/-- `TAct` proves its own action axiom (sanity). -/
theorem tact_proves_actionAxiom : TAct ⊢ actionAxiom := Entailment.by_axm actionAxiom_mem_TAct

theorem tact_proves_actionAxiom' : TAct ⊢ actionAxiom' := Entailment.by_axm actionAxiom'_mem_TAct

/-! ### Codes agree along the embedding — Foundation plumbing, skip on first reading -/

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

/-! ### `TAct` is Δ₁-axiomatized — Foundation plumbing, skip on first reading -/

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

lemma lMap_swap_zeroT {ξ : Type*} {n : ℕ} :
    Semiterm.lMap swap (zeroT : Semiterm LAct ξ n) = zeroT := by
  unfold zeroT
  rw [Semiterm.lMap_func, swap_emb]
  congr 1
  funext i; exact i.elim0

lemma lMap_swap_oneT {ξ : Type*} {n : ℕ} :
    Semiterm.lMap swap (oneT : Semiterm LAct ξ n) = oneT := by
  unfold oneT
  rw [Semiterm.lMap_func, swap_emb]
  congr 1
  funext i; exact i.elim0

lemma lMap_swap_eqF {ξ : Type*} {n : ℕ} (t u : Semiterm LAct ξ n) :
    Semiformula.lMap swap (eqF t u) = eqF (Semiterm.lMap swap t) (Semiterm.lMap swap u) := by
  unfold eqF
  rw [Semiformula.lMap_rel, swap_rel]
  congr 1
  funext i; fin_cases i <;> rfl

/-- `actionAxiom'` IS the transposition of `actionAxiom`. -/
lemma lMap_swap_actionAxiom : Semiformula.lMap swap actionAxiom = actionAxiom' := by
  unfold actionAxiom actionAxiom'
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and, lMap_swap_eqF,
    lMap_swap_cterm_C, lMap_swap_cterm_D, lMap_swap_zeroT, lMap_swap_oneT]

lemma lMap_swap_actionAxiom' : Semiformula.lMap swap actionAxiom' = actionAxiom := by
  unfold actionAxiom actionAxiom'
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and, lMap_swap_eqF,
    lMap_swap_cterm_C, lMap_swap_cterm_D, lMap_swap_zeroT, lMap_swap_oneT]

lemma lMap_swap_constNe : Semiformula.lMap swap constNe = constNe' := by
  unfold constNe constNe'
  rw [Semiformula.lMap_nrel]
  congr 1
  funext i; fin_cases i <;> simp [lMap_swap_cterm_C, lMap_swap_cterm_D]

lemma lMap_swap_constNe' : Semiformula.lMap swap constNe' = constNe := by
  unfold constNe constNe'
  rw [Semiformula.lMap_nrel]
  congr 1
  funext i; fin_cases i <;> simp [lMap_swap_cterm_C, lMap_swap_cterm_D]

/-- The axiom set of `TAct` is literally closed under the transposition. -/
theorem lMap_swap_mem_TAct {σ : Sentence LAct} (h : σ ∈ TAct) : Semiformula.lMap swap σ ∈ TAct := by
  rcases h with rfl | rfl | rfl | rfl | ⟨σ₀, hσ₀, rfl⟩
  · rw [lMap_swap_actionAxiom]; exact actionAxiom'_mem_TAct
  · rw [lMap_swap_actionAxiom']; exact actionAxiom_mem_TAct
  · rw [lMap_swap_constNe]; exact constNe'_mem_TAct
  · rw [lMap_swap_constNe']; exact constNe_mem_TAct
  · rw [lMap_swap_emb]; exact lMap_emb_mem_TAct hσ₀

end closure

/-! ### The standard readings of the constants, and the model class of `actionAxiom` -/

section models

variable {M : Type*}

/-- `M` as an `LAct`-structure over its `ORingStructure`: arithmetic standard, `c_C ↦ 0`,
`c_D ↦ 1` (`stdReadingNat` for a general `M`; `ArithS.Det.stdReadingV` is the same structure, as the
pull-back along `inst` — `stdReadingV_eq_stdReading`). -/
@[instance_reducible] def stdReading (M : Type*) [ORingStructure M] : Structure LAct M where
  func _ f := match f with
    | Sum.inl f => (standardModel M).func f
    | Sum.inr (Language.Constant.Func.const Act.C) => fun _ ↦ 0
    | Sum.inr (Language.Constant.Func.const Act.D) => fun _ ↦ 1
  rel _ r := match r with
    | Sum.inl r => (standardModel M).rel r
    | Sum.inr e => PEmpty.elim e

/-- The transposed reading `c_C ↦ 1`, `c_D ↦ 0`: the pull-back of `stdReading M` along `swap`. -/
@[instance_reducible] def swappedReading (M : Type*) [ORingStructure M] : Structure LAct M :=
  Structure.lMap swap (stdReading M)

lemma stdReading_nat : stdReading ℕ = stdReadingNat := by
  ext <;> rfl

lemma stdReading_lMap_emb [ORingStructure M] : Structure.lMap emb (stdReading M) = standardModel M := by
  ext <;> rfl

lemma swappedReading_lMap_emb [ORingStructure M] : Structure.lMap emb (swappedReading M) = standardModel M := by
  ext <;> rfl

/-- The value of an action constant: the structure's reading of it. -/
lemma val_cterm (S : Structure LAct M) (a : Act) {n : ℕ} (e : Fin n → M) (ε : Empty → M) :
    Semiterm.val (s := S) e ε (cterm a) = S.func (const a) ![] := by
  unfold cterm
  rw [Semiterm.val_func]
  congr 1
  exact Matrix.empty_eq _

section reduct

variable [ORingStructure M] (S : Structure LAct M) (hS : Structure.lMap emb S = standardModel M)
include hS

lemma val_zeroT {n : ℕ} (e : Fin n → M) (ε : Empty → M) :
    Semiterm.val (s := S) e ε zeroT = 0 := by
  unfold zeroT
  rw [Semiterm.val_func, Matrix.empty_eq (Semiterm.val (s := S) e ε ∘ ![])]
  exact congrArg (fun s : Structure ℒₒᵣ M ↦ s.func Language.Zero.zero ![]) hS

lemma val_oneT {n : ℕ} (e : Fin n → M) (ε : Empty → M) :
    Semiterm.val (s := S) e ε oneT = 1 := by
  unfold oneT
  rw [Semiterm.val_func, Matrix.empty_eq (Semiterm.val (s := S) e ε ∘ ![])]
  exact congrArg (fun s : Structure ℒₒᵣ M ↦ s.func Language.One.one ![]) hS

/-- In a structure whose reduct is standard, `eqF` is real equality. -/
lemma eval_eqF {n : ℕ} (t u : Semiterm LAct Empty n) (e : Fin n → M) :
    Semiformula.Eval (s := S) e Empty.elim (eqF t u) ↔
      Semiterm.val (s := S) e Empty.elim t = Semiterm.val (s := S) e Empty.elim u := by
  unfold eqF
  rw [Semiformula.eval_rel]
  change (Structure.lMap emb S).rel Language.Eq.eq (fun i ↦ Semiterm.val (s := S) e Empty.elim (![t, u] i)) ↔ _
  rw [hS]
  exact Iff.rfl

/-- **The model class of the action axiom.** In an `LAct`-structure with standard reduct (in
particular with real equality), `actionAxiom` holds iff the constants read `(0, 1)` or `(1, 0)`. -/
theorem eval_actionAxiom_iff :
    Semiformula.Eval (s := S) ![] Empty.elim actionAxiom ↔
      (S.func (const Act.C) ![] = 0 ∧ S.func (const Act.D) ![] = 1) ∨
      (S.func (const Act.C) ![] = 1 ∧ S.func (const Act.D) ![] = 0) := by
  unfold actionAxiom
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.or_eq, LogicalConnective.Prop.and_eq, eval_eqF S hS, val_cterm,
    val_zeroT S hS, val_oneT S hS]

theorem eval_actionAxiom'_iff :
    Semiformula.Eval (s := S) ![] Empty.elim actionAxiom' ↔
      (S.func (const Act.D) ![] = 0 ∧ S.func (const Act.C) ![] = 1) ∨
      (S.func (const Act.D) ![] = 1 ∧ S.func (const Act.C) ![] = 0) := by
  unfold actionAxiom'
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.or_eq, LogicalConnective.Prop.and_eq, eval_eqF S hS, val_cterm,
    val_zeroT S hS, val_oneT S hS]

/-- **The structures satisfying `actionAxiom` are the two standard readings**: a structure with standard
reduct satisfying `actionAxiom` is `stdReading M` (`c_C ↦ 0, c_D ↦ 1`) or `swappedReading M` (`c_C ↦ 1, c_D ↦ 0`). -/
theorem structure_eq_of_actionAxiom (hAct : Semiformula.Eval (s := S) ![] Empty.elim actionAxiom) :
    S = stdReading M ∨ S = swappedReading M := by
  have hfun : ∀ {k : ℕ} (f : Language.Func ℒₒᵣ k) (v : Fin k → M),
      S.func (emb.func f) v = (standardModel M).func f v := fun f v ↦
    congrArg (fun s : Structure ℒₒᵣ M ↦ s.func f v) hS
  have hrel : ∀ {k : ℕ} (r : Language.Rel ℒₒᵣ k) (v : Fin k → M),
      S.rel (emb.rel r) v = (standardModel M).rel r v := fun r v ↦
    congrArg (fun s : Structure ℒₒᵣ M ↦ s.rel r v) hS
  rcases (eval_actionAxiom_iff S hS).mp hAct with ⟨hC, hD⟩ | ⟨hC, hD⟩
  · left
    refine Structure.ext ?_ ?_
    · funext k f v
      rcases f with f | ⟨(_ | _)⟩
      · exact hfun f v
      · rw [Matrix.empty_eq v]; exact hC
      · rw [Matrix.empty_eq v]; exact hD
    · funext k r v
      rcases r with r | e
      · exact hrel r v
      · exact e.elim
  · right
    refine Structure.ext ?_ ?_
    · funext k f v
      rcases f with f | ⟨(_ | _)⟩
      · exact hfun f v
      · rw [Matrix.empty_eq v]; exact hC
      · rw [Matrix.empty_eq v]; exact hD
    · funext k r v
      rcases r with r | e
      · exact hrel r v
      · exact e.elim

end reduct

lemma eval_actionAxiom_stdReading [ORingStructure M] : Semiformula.Eval (s := stdReading M) ![] Empty.elim actionAxiom :=
  (eval_actionAxiom_iff _ stdReading_lMap_emb).mpr (Or.inl ⟨rfl, rfl⟩)

lemma eval_actionAxiom'_stdReading [ORingStructure M] : Semiformula.Eval (s := stdReading M) ![] Empty.elim actionAxiom' :=
  (eval_actionAxiom'_iff _ stdReading_lMap_emb).mpr (Or.inr ⟨rfl, rfl⟩)

lemma eval_actionAxiom_swappedReading [ORingStructure M] : Semiformula.Eval (s := swappedReading M) ![] Empty.elim actionAxiom :=
  (eval_actionAxiom_iff _ swappedReading_lMap_emb).mpr (Or.inr ⟨rfl, rfl⟩)

lemma eval_actionAxiom'_swappedReading [ORingStructure M] : Semiformula.Eval (s := swappedReading M) ![] Empty.elim actionAxiom' :=
  (eval_actionAxiom'_iff _ swappedReading_lMap_emb).mpr (Or.inl ⟨rfl, rfl⟩)

/-- **`models_actionAxiom_iff`**: an `LAct`-structure (instance form) with standard reduct — in
particular with real equality — satisfies `actionAxiom` iff its constants read `(0, 1)` or `(1, 0)`. -/
theorem models_actionAxiom_iff [ORingStructure M] [Nonempty M] [Structure LAct M]
    (hS : Structure.lMap emb (inferInstance : Structure LAct M) = standardModel M) :
    M↓[LAct] ⊧ actionAxiom ↔
      (Structure.func (const Act.C) ![] = (0 : M) ∧ Structure.func (const Act.D) ![] = (1 : M)) ∨
      (Structure.func (const Act.C) ![] = (1 : M) ∧ Structure.func (const Act.D) ![] = (0 : M)) := by
  rw [models_iff]
  exact eval_actionAxiom_iff _ hS

/-- `ℕ` (with `c_C ↦ 0`, `c_D ↦ 1`) satisfies the action axiom. -/
lemma models_actionAxiom : ℕ↓[LAct] ⊧ actionAxiom := by
  rw [models_iff]
  exact (eval_actionAxiom_iff stdReadingNat stdReadingNat_lMap_emb).mpr (Or.inl ⟨rfl, rfl⟩)

lemma models_actionAxiom' : ℕ↓[LAct] ⊧ actionAxiom' := by
  rw [models_iff]
  exact (eval_actionAxiom'_iff stdReadingNat stdReadingNat_lMap_emb).mpr (Or.inr ⟨rfl, rfl⟩)

/-! ### `ℕ` is a model of `TAct` — soundness, the whole negative method of the cells -/

lemma models_constNe : ℕ↓[LAct] ⊧ constNe := by
  rw [models_iff]
  unfold constNe Semiformula.Realize
  simp [Semiformula.eval_nrel, cterm]
  change ¬((0 : ℕ) = 1)
  decide

lemma models_constNe' : ℕ↓[LAct] ⊧ constNe' := by
  rw [models_iff]
  unfold constNe' Semiformula.Realize
  simp [Semiformula.eval_nrel, cterm]
  change ¬((1 : ℕ) = 0)
  decide

instance models_TAct : ℕ↓[LAct] ⊧* TAct := by
  rw [models_theory_iff]
  intro φ hφ
  rcases hφ with rfl | rfl | rfl | rfl | ⟨σ, hσ, rfl⟩
  · exact models_actionAxiom
  · exact models_actionAxiom'
  · exact models_constNe
  · exact models_constNe'
  · rw [models_lMap_emb]
    exact Theory.models ℕ 𝗣𝗔 hσ

end models

end ArithS
