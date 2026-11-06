import ArithS.Length.DerivationLength

/-!
# ArithS.Bew — length-bounded provability `□_k`

`LenBoxNat f k T φ`: `φ` has a `T`-proof of length `≤ k` (and code `< f k`). This is
Foundation's `Theory.RestrictedProvable` (`Incompleteness/RestrictedProvability.lean`) with
the LENGTH conjunct `proofLen T d ≤ k` added — Critch's `□_k` (Notation 3.5 of `critch22`:
"a proof … that requires at most `k` characters of text"), with `proofLen` the structural
symbol count of `ArithS.DerivationLength`.

The code bound `d < f k` is what makes the predicate Π₁-definable (a bounded search), and
is NEVER meant to bite: the PROPERNESS lemma — every actual derivation of length `≤ k` has
code `< f k` for the chosen `f` — is a separate, meta-level (`V = ℕ`) estimate on
Foundation's coding, stated as a hypothesis here (`ProperBoundNat`) and discharged in
`ArithS.Proper` (roadmap M1). Everything below is parametric in `f`, exactly as Foundation
is parametric in its bounding function.

Contents: the predicate and its Π₁ definition; monotonicity; the Gödel sentence for `□_k`
(`lenGödel`), its truth, its provability, and the LOWER BOUND on the length of any proof
of it (`lower_bound_proofLen_proof_lenGödel`) — the length-measure twin of
`lower_bound_gödelNumber_proof_restrictedGödel`, and the M1 gate of the roadmap.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

/-- Provability by a proof of length `≤ k` (code below `f k`). -/
def LenBoxNat (f : V → V) (k : ℕ) (T : Theory L) [T.Δ₁] (φ : V) : Prop :=
  ∃ d < f (ORingStructure.numeral k), Proof T d φ ∧ proofLen T d ≤ ORingStructure.numeral k

variable (T)

noncomputable def lenBoxNat (fDef : 𝚺₁.Semisentence 2) (k : ℕ) : 𝚷₁.Semisentence 1 :=
  .mkPi “φ. ∀ E, !fDef E !k → ∃ d < E, !(proof T).pi d φ ∧ ∀ n, !(proofLenDef T) n d → n ≤ !k”

/-- The sentence `□_k σ`. -/
noncomputable abbrev lenProvabilityPred (fDef : 𝚺₁.Semisentence 2) (k : ℕ) (σ : Sentence L) :
    ArithmeticSentence := (lenBoxNat T fDef k).val/[⌜σ⌝]

variable {T}

instance LenBoxNat.defined {f : V → V} {fDef : 𝚺₁.Semisentence 2} [𝚺₁-Function₁[V] f via fDef] {k} :
    𝚷₁-Predicate[V] (LenBoxNat f k T) via (lenBoxNat T fDef k) where
  defined {φ} := by simp [lenBoxNat, LenBoxNat, proofLen_defined.iff]

lemma LenBoxNat.mono {f : V → V} (hf : Monotone f) {k k' : ℕ} (h : k ≤ k') {φ : V} :
    LenBoxNat f k T φ → LenBoxNat f k' T φ := by
  rintro ⟨d, hd, hp, hl⟩
  have hk : (ORingStructure.numeral k : V) ≤ ORingStructure.numeral k' := by
    simpa [numeral_eq_natCast] using (Nat.cast_le (α := V)).mpr h
  exact ⟨d, lt_of_lt_of_le hd (hf hk), hp, le_trans hl hk⟩

lemma LenBoxNat.provable {f : V → V} {k : ℕ} {φ : V} : LenBoxNat f k T φ → Provable T φ := by
  rintro ⟨d, _, hp, _⟩; exact ⟨d, hp⟩

/-! ### The Gödel sentence for `□_k` -/

section gödel

variable (T)

/-- "I have no `T`-proof of length `≤ k`." -/
noncomputable abbrev lenGödel (fDef : 𝚺₁.Semisentence 2) (k : ℕ) : ArithmeticSentence :=
  fixedpoint (∼(lenBoxNat T fDef k))

private noncomputable abbrev lenGödel' (fDef : 𝚺₁.Semisentence 2) (k : ℕ) : ArithmeticSentence :=
  ∼(lenBoxNat T fDef k).val/[⌜lenGödel T fDef k⌝]

variable {T}

private lemma lenGödel'_sigmaOne {fDef : 𝚺₁.Semisentence 2} {k : ℕ} :
    Hierarchy 𝚺 1 (lenGödel' T fDef k) := by definability

end gödel

end ArithS

namespace ArithS.Arithmetic

open FFL FFL.FirstOrder Arithmetic Bootstrapping ArithS
open PeanoMinus ISigma0 ISigma1

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T U : ArithmeticTheory} [T.Δ₁]
variable {fDef : 𝚺₁.Semisentence 2} {k : ℕ}

lemma def_lenGödel [𝗜𝚺₁ ⪯ U] :
    U ⊢ lenGödel T fDef k 🡘 (∼(lenBoxNat T fDef k).val)/[⌜lenGödel T fDef k⌝] := diagonal _

private lemma def_lenGödel' [𝗜𝚺₁ ⪯ U] :
    U ⊢ lenGödel' T fDef k 🡘 (∼(lenBoxNat T fDef k).val)/[⌜lenGödel T fDef k⌝] := by simp

private lemma provable_E_lenGödel_lenGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ lenGödel T fDef k 🡘 lenGödel' T fDef k := by
  apply Entailment.E_trans
  · exact def_lenGödel
  · exact Entailment.E_symm def_lenGödel'

private lemma iff_provable_lenGödel_provable_lenGödel' [𝗜𝚺₁ ⪯ U] :
    U ⊢ lenGödel T fDef k ↔ U ⊢ lenGödel' T fDef k :=
  Entailment.iff_of_E provable_E_lenGödel_lenGödel'

private lemma iff_true_lenGödel_true_lenGödel' :
    ℕ↓[ℒₒᵣ] ⊧ lenGödel T fDef k ↔ ℕ↓[ℒₒᵣ] ⊧ lenGödel' T fDef k := by
  apply Semantics.models_iff.mp
  apply models_of_provable (T := 𝗜𝚺₁) inferInstance
  apply provable_E_lenGödel_lenGödel'

lemma models_lenGödel (f : V → V) [𝚺₁-Function₁[V] f via fDef] :
    V↓[ℒₒᵣ] ⊧ lenGödel T fDef k ↔
    ∀ x : V, x < f (ORingStructure.numeral k) →
      ¬(Proof T x (⌜lenGödel T fDef k⌝) ∧ proofLen T x ≤ ORingStructure.numeral k) := by
  apply Iff.trans <| Semantics.models_iff.mp <| models_of_provable (T := 𝗜𝚺₁) inferInstance <| def_lenGödel
  simp [models_iff, LenBoxNat]

private lemma models_neg_lenGödel (f : V → V) [𝚺₁-Function₁[V] f via fDef] :
    ¬V↓[ℒₒᵣ] ⊧ lenGödel T fDef k ↔
    ∃ x : V, x < f (ORingStructure.numeral k) ∧
      Proof T x (⌜lenGödel T fDef k⌝) ∧ proofLen T x ≤ ORingStructure.numeral k := by
  simpa using (models_lenGödel f).not

variable [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- The Gödel sentence for `□_k` is true. -/
theorem true_lenGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] : ℕ↓[ℒₒᵣ] ⊧ lenGödel T fDef k := by
  by_contra hC
  obtain ⟨e, _, he, _⟩ := (models_neg_lenGödel f (k := k)).mp hC
  apply hC
  apply iff_true_lenGödel_true_lenGödel'.mpr
  apply ArithmeticTheory.soundOnHierarchy T _ _ ?_ lenGödel'_sigmaOne
  apply iff_provable_lenGödel_provable_lenGödel'.mp
  apply Arithmetic.Bootstrapping.provable_of_standard_proof (T := T) (V := ℕ) (n := e)
  simpa using he

/-- The Gödel sentence for `□_k` is provable (in `T`, by a proof that is necessarily long). -/
theorem provable_lenGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] : T ⊢ lenGödel T fDef k := by
  apply iff_provable_lenGödel_provable_lenGödel'.mpr
  apply Arithmetic.sigma_one_completeness_iff lenGödel'_sigmaOne |>.mp
  apply iff_true_lenGödel_true_lenGödel'.mp <| true_lenGödel f

/-- Every proof of the Gödel sentence for `□_k` either has code `≥ f k` or length `> k`. -/
theorem lower_bound_proof_lenGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] :
    ∀ b : T ⊢! lenGödel T fDef k, f k ≤ ⌜b⌝ ∨ k < proofLen T (⌜b⌝ : ℕ) := by
  intro b
  rcases Nat.lt_or_ge (⌜b⌝ : ℕ) (f k) with h | h
  swap
  · exact Or.inl h
  · right
    by_contra hk
    have hle : proofLen T (⌜b⌝ : ℕ) ≤ k := Nat.le_of_not_lt hk
    exact (models_lenGödel f).mp (true_lenGödel f) ⌜b⌝ (by simpa using h)
      ⟨proof_of_quote_proof b, by
        simpa [numeral_eq_natCast, le_def] using (Nat.lt_or_eq_of_le hle).symm⟩

/-- PROPERNESS of the bound `f` for the length measure at `k`: no derivation of length `≤ k`
has a code `≥ f k`. Discharged for a concrete `f` in `ArithS.Proper` (meta-level estimate
on Foundation's coding); a hypothesis here. -/
def ProperBoundNat (f : ℕ → ℕ) (k : ℕ) (T : ArithmeticTheory) [T.Δ₁] : Prop :=
  ∀ b : T ⊢! lenGödel T fDef k, proofLen T (⌜b⌝ : ℕ) ≤ k → ⌜b⌝ < f k

/-- **The M1 gate.** Under properness, every proof of the Gödel sentence for `□_k` is LONGER
than `k` — the length-measure twin of Foundation's
`lower_bound_gödelNumber_proof_restrictedGödel`. -/
theorem lower_bound_proofLen_proof_lenGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef]
    (hf : ProperBoundNat (fDef := fDef) f k T) :
    ∀ b : T ⊢! lenGödel T fDef k, k < proofLen T (⌜b⌝ : ℕ) := by
  intro b
  rcases lower_bound_proof_lenGödel f b with h | h
  · by_contra hk
    exact absurd h (not_le.mpr (hf b (not_lt.mp hk)))
  · exact h

end ArithS.Arithmetic
