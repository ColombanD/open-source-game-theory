import ArithS.Assembly.Cell

/-!
# ArithS.Necessitation.Lib.Basic — the uniform packaging of the library `Λ`

`DESIGN_inner_necessitation.md` §3.1: the verification proof of bounded inner necessitation
uses a FINITE library of lemma-sentences `Λ = ∀ x̄, B(x̄)`, each a `TAct`-theorem whose proof
has a FIXED standard length `N_Λ`, in EVERY model of `𝗜𝚺₁` (so the fragments can cite them at
cost `O(1)`).

* `Lib σ` — "`σ` has a `TAct`-proof of some fixed standard length, in every model";
  `Lib.of_tact`/`Lib.of_pa`/`Lib.of_isigma1` (transport along `emb` + `lenDerivable_of_proof`
  + `lenDerivable_of_nat`, the `CutV`/`Prep` route); `Lib.code`, the unfolded reading.
* `quote_alls` — the code of the embedded universal closure `∀¹* B` is `qqAlls ⌜B⌝ m`;
  `Lib.univ_code` — the code-level reading a fragment instantiates at its witnesses.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

/-- **A library sentence**: the `ℒₒᵣ`-sentence `σ`, embedded into `LAct` along `emb`, has a
`TAct`-proof code of length `≤ N` for ONE standard `N`, in EVERY model of `𝗜𝚺₁`. -/
def Lib (σ : ArithmeticSentence) : Prop :=
  ∃ N : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    LenDerivable TAct (N : V) (⌜Semiformula.lMap emb σ⌝ : V)

namespace Lib

/-- Every `TAct`-theorem (embedded form) is a library sentence. -/
theorem of_tact {σ : ArithmeticSentence} (h : TAct ⊢ Semiformula.lMap emb σ) : Lib σ :=
  exists_lenDerivable_V_of_proof _ h

/-- Every `𝗣𝗔`-theorem is a library sentence (`tact_proves_lMap_emb`). -/
theorem of_pa {σ : ArithmeticSentence} (h : 𝗣𝗔 ⊢ σ) : Lib σ :=
  of_tact (tact_proves_lMap_emb h)

/-- Every `𝗜𝚺₁`-theorem is a library sentence (`𝗜𝚺₁ ⪯ 𝗣𝗔`). -/
theorem of_isigma1 {σ : ArithmeticSentence} (h : 𝗜𝚺₁ ⊢ σ) : Lib σ :=
  of_pa (Entailment.WeakerThan.pbl h)

/-- **The route every library row takes**: truth in every model of `𝗜𝚺₁` gives a `𝗣𝗔`-proof
(completeness, `Arithmetic.complete`), hence a library sentence. -/
theorem pa_proves_of_models {σ : ArithmeticSentence}
    (H : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], V↓[ℒₒᵣ] ⊧ σ) : 𝗣𝗔 ⊢ σ :=
  complete 𝗣𝗔 σ fun (V : Type) _ _ ↦
    haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    H V

theorem isigma1_proves_of_models {σ : ArithmeticSentence}
    (H : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], V↓[ℒₒᵣ] ⊧ σ) : 𝗜𝚺₁ ⊢ σ :=
  complete 𝗜𝚺₁ σ fun (V : Type) _ _ ↦ H V

theorem of_models {σ : ArithmeticSentence}
    (H : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], V↓[ℒₒᵣ] ⊧ σ) : Lib σ :=
  of_pa (pa_proves_of_models H)

/-- The code-level reading: some standard `N` bounds a proof code of `⌜σ⌝` in every model. -/
theorem code {σ : ArithmeticSentence} (h : Lib σ) :
    ∃ N : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      ∃ d, Proof TAct d (⌜Semiformula.lMap emb σ⌝ : V) ∧ dlen TAct d ≤ (N : V) := h

end Lib

/-! ### Prenex universal form: the code of `∀¹* B` -/

section alls

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The universal closure commutes with the embedding `Rewriting.emb` (`Empty` → `ℕ` free
variables). -/
lemma emb_allClosure {L : Language} {n : ℕ} (φ : Semisentence L n) :
    (Rewriting.emb (∀¹* φ : Sentence L) : Proposition L) = ∀¹* (Rewriting.emb φ : Semiproposition L n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [allClosure_succ, ih (∀¹ φ), allClosure_succ]
    simp

/-- **The code of an embedded universal closure** is `qqAlls` of the body's code. -/
theorem quote_alls {m : ℕ} (B : ArithmeticSemisentence m) :
    (⌜Semiformula.lMap emb (∀¹* B : ArithmeticSentence)⌝ : V) =
      qqAlls (⌜Semiformula.lMap emb B⌝ : V) (m : V) := by
  rw [Semiformula.lMap_allClosure, Sentence.quote_def, emb_allClosure, quote_allClosure]
  rfl

end alls

namespace Lib

/-- **The code-level reading in prenex form**: a library sentence `∀¹* B` (`m` outer universal
quantifiers over the body `B`) has, for some standard `N`, in every model, a proof code of
`qqAlls ⌜B⌝ m` of length `≤ N`. -/
theorem univ_code {m : ℕ} {B : ArithmeticSemisentence m} (h : Lib (∀¹* B)) :
    ∃ N : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      ∃ d, Proof TAct d (qqAlls (⌜Semiformula.lMap emb B⌝ : V) (m : V)) ∧ dlen TAct d ≤ (N : V) := by
  obtain ⟨N, hN⟩ := h.code
  exact ⟨N, fun V _ _ ↦ by rw [← quote_alls]; exact hN V⟩

end Lib

/-! ### Probes (deleted once settled) -/

example : (“∀ x s, x ∈ s” : ArithmeticSentence) = ∀¹* (“s x. x ∈ s” : ArithmeticSemisentence 2) := rfl
example : (“∀ x s t, x ∈ s → !bitSubsetDef s t” : ArithmeticSentence) =
    ∀¹* (“t s x. x ∈ s → !bitSubsetDef s t” : ArithmeticSemisentence 3) := rfl

end ArithS
