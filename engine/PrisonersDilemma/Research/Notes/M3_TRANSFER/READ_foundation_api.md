# Foundation API report — pinned commit `58c76ac8b26cfda45d0d5430511750489d39b25a` (Lean v4.33.1)

Package root: `/Users/colomband/wt/arith-lake/packages/Foundation` (the `arith/.lake` symlink target). All paths below are relative to that root. Namespace root is `FFL` (not `LO`). Every declaration is quoted verbatim.

**Headline structural facts (affect design):**
- `Foundation/ProvabilityLogic/**` and `Foundation/Modal/**` are **ABSENT** at this commit. Removed in `947950e8 refactor: Remove ProvabilityLogic (#829)` (2026-07-02) and `1defcb8a refactor: Remove Modal Logic and associated superintuitionistic logic (#852)` (2026-07-22). README §"Further Results" says they now live in a separate repo `[ProvabilityLogic]` under the FFL organization. The old `Realization.lean` / `GL/Soundness.lean` are quoted in §7 from git history (`git show 947950e8^:Foundation/ProvabilityLogic/...`) for reuse-by-copy.
- Entailment: `T ⊢! φ` is the proof TYPE (`Entailment.Prf`), `T ⊢ φ` is `Nonempty (T ⊢! φ)` (`Foundation/Logic/Entailment.lean:34-53`). `Theory.Proof` (`Foundation/FirstOrder/Basic/Calculus.lean:355`) is the proof-object structure.
- `⪯` is `WeakerThan` (`Foundation/Logic/Entailment.lean:90-93`): `class WeakerThan (𝓢 : S) (𝓣 : T) : Prop where subset : theory 𝓢 ⊆ theory 𝓣`.

---

## (1) `Foundation/FirstOrder/Incompleteness/StandardProvability.lean`

Full file (111 lines):

```lean
-- :14
namespace FFL.FirstOrder.Arithmetic
open ISigma1 Bootstrapping ProvabilityAbstraction

-- :18
noncomputable instance : Diagonalization 𝗜𝚺₁ where
  fixedpoint := fixedpoint
  diag θ := diagonal θ

-- :24
variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]
local prefix:90 "□" => provabilityPred T

-- :29
theorem provable_D1 {σ} : T ⊢ σ → 𝗜𝚺₁ ⊢ □σ := fun h ↦
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by simpa [models_iff] using internalize_provability (V := V) h

-- :33
theorem provable_D2 {σ π} : 𝗜𝚺₁ ⊢ □(σ 🡒 π) 🡒 □σ 🡒 □π :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by simpa [models_iff] using modus_ponens_sentence T

-- :38
noncomputable abbrev _root_.FFL.FirstOrder.Theory.standardProvability : Provability 𝗜𝚺₁ T where
  prov := provable T
  bew_def := provable_D1

-- :44
instance : T.standardProvability.HBL2 := ⟨provable_D2⟩
-- :46
lemma standardProvability_def (σ : Sentence L) : T.standardProvability σ = provabilityPred T σ := rfl
-- :48
instance : T.standardProvability.SoundOn ℕ :=
  ⟨fun h ↦ by simpa [Arithmetic.standardProvability_def, models_iff] using h⟩

-- :55
variable {T U : ArithmeticTheory} [T.Δ₁]
local prefix:90 "□" => provabilityPred T

-- :59
lemma provable_sigma_one_complete [𝗣𝗔⁻ ⪯ T] {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    𝗜𝚺₁ ⊢ σ 🡒 □σ :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using Bootstrapping.Arithmetic.sigma_one_complete (T := T) (V := V) hσ

-- :65
theorem provable_D3 [𝗣𝗔⁻ ⪯ T] {σ : ArithmeticSentence} :
    𝗜𝚺₁ ⊢ □σ 🡒 □□σ := provable_sigma_one_complete (by simp)

-- :70
lemma provable_D2_context [𝗜𝚺₁ ⪯ U] {Γ σ π} (hσπ : Γ ⊢[U] □(σ 🡒 π)) (hσ : Γ ⊢[U] □σ) :
    Γ ⊢[U] □π := FiniteContext.of' (weakening inferInstance provable_D2) ⨀ hσπ ⨀ hσ

-- :73
lemma provable_D3_context [𝗣𝗔⁻ ⪯ T] [𝗜𝚺₁ ⪯ U] {Γ σ} (hσπ : Γ ⊢[U] □σ) :
  Γ ⊢[U] □□σ := FiniteContext.of' (weakening inferInstance provable_D3) ⨀ hσπ

-- :76
lemma provable_sound [U.SoundOnHierarchy 𝚺 1] {σ} : U ⊢ □σ → T ⊢ σ := fun h ↦ by
  have : ℕ↓[ℒₒᵣ] ⊧ provabilityPred T σ := ArithmeticTheory.SoundOn.sound (F := Arithmetic.Hierarchy 𝚺 1) h (by simp)
  simpa [models_iff] using this

-- :80
lemma provable_complete [U.SoundOnHierarchy 𝚺 1] [𝗜𝚺₁ ⪯ U] {σ} : T ⊢ σ ↔ U ⊢ □σ :=
  ⟨fun h ↦ weakening inferInstance (provable_D1 h), provable_sound⟩

-- :83
instance [𝗣𝗔⁻ ⪯ T] : T.standardProvability.HBL3 := ⟨provable_D3⟩
-- :85
instance [𝗣𝗔⁻ ⪯ T] : T.standardProvability.HBL where
-- :87
instance [T.SoundOnHierarchy 𝚺 1] : T.standardProvability.Kreisel := ⟨fun h ↦ provable_sound h⟩

-- :94
lemma provable_sigma_one_complete_of_E {σ π} [𝗜𝚺₁ ⪯ T]
  (hσ : Hierarchy 𝚺 1 σ) (hσπ : 𝗜𝚺₁ ⊢ σ 🡘 π) : 𝗜𝚺₁ ⊢ π 🡒 □π := by
  apply C_replace ?_ ?_ $ provable_sigma_one_complete (T := T) $ hσ;
  . cl_prover [hσπ];
  . apply T.standardProvability.mono';
    cl_prover [hσπ];

-- :104
lemma exists_true_but_unprovable_sentence_of_incomplete {T : ArithmeticTheory} (h : Incomplete T) :
    ∃ δ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ δ ∧ T ⊬ δ
```

NOTE: in `provable_D1`/`provable_D2` (lines 24-51) `T : Theory L` for ANY `[L.Encodable] [L.LORDefinable]` language, and the box lands in `𝗜𝚺₁`. `provable_D3`, `provable_sound`, `provable_complete` need `T U : ArithmeticTheory`. In `provable_sigma_one_complete` the hypothesis is `[𝗣𝗔⁻ ⪯ T]` (the box theory), the conclusion is in `𝗜𝚺₁`; in `_of_E` it is `[𝗜𝚺₁ ⪯ T]`.

### Underlying definitions

`Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean` (namespace `FFL.FirstOrder.Arithmetic.Bootstrapping`, `variable (T)`, `{V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`, `{L : Language} [L.Encodable] [L.LORDefinable]`, `{T : Theory L} [T.Δ₁]`):

```lean
-- :464
def Derivation : V → Prop := (construction T).Fixpoint ![]
-- :466
def DerivationOf (d s : V) : Prop := fstIdx d = s ∧ Derivation T d
-- :468
def Derivable (s : V) : Prop := ∃ d, DerivationOf T d s
-- :470
def Proof (d φ : V) : Prop := DerivationOf T d {φ}
-- :472
def Provable (φ : V) : Prop := ∃ d, Proof T d φ
-- :474
noncomputable def derivation : 𝚫₁.Semisentence 1 := (blueprint T).fixpointDefΔ₁
-- :476
noncomputable def derivationOf : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “d s. !fstIdxDef s d ∧ !(derivation T).sigma d”)
  (.mkPi “d s. !fstIdxDef s d ∧ !(derivation T).pi d”)
-- :480
noncomputable def derivable : 𝚺₁.Semisentence 1 := .mkSigma
  “Γ. ∃ d, !(derivationOf T).sigma d Γ”
-- :483
noncomputable def proof : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “d φ. ∃ s, !insertDef s φ 0 ∧ !(derivationOf T).sigma d s”)
  (.mkPi “d φ. ∀ s, !insertDef s φ 0 → !(derivationOf T).pi d s”)
-- :488
noncomputable def provable : 𝚺₁.Semisentence 1 := .mkSigma
  “φ. ∃ d, !(proof T).sigma d φ”
-- :491
noncomputable abbrev provabilityPred (σ : Sentence L) : ArithmeticSentence := (provable T).val/[⌜σ⌝]
-- :493
noncomputable def provabilityPred' (σ : Sentence L) : 𝚺₁.Sentence := .mkSigma
  “!(provable T) !!(⌜σ⌝)”
-- :497  -- Proving this by `rfl` overflows memory on Lean v4.33.1.
@[simp] lemma provabilityPred'_val (σ : Sentence L) : (provabilityPred' T σ).val = provabilityPred T σ
-- :504..
instance Derivation.defined : 𝚫₁-Predicate[V] Derivation T via derivation T := (construction T).fixpoint_definedΔ₁
instance DerivationOf.defined : 𝚫₁-Relation[V] DerivationOf T via derivationOf T
instance Derivable.defined : 𝚺₁-Predicate[V] Derivable T via derivable T
-- :525
instance Proof.defined : 𝚫₁-Relation[V] Proof T via proof T := .mk
  ⟨by intro v; simp [proof], by intro v; simp [Proof, proof, singleton_eq_insert, emptyset_def]⟩
instance Proof.definable : 𝚫₁-Relation[V] Proof T := Proof.defined.to_definable
instance Proof.definable' : Γ-[m + 1]-Relation[V] Proof T := Proof.definable.of_deltaOne
-- :532
instance Provable.defined : 𝚺₁-Predicate[V] Provable T via provable T := .mk fun v ↦ by simp [provable, Provable]
instance Provable.definable : 𝚺₁-Predicate[V] Provable T := Provable.defined.to_definable
instance Provable.definable' : 𝚺-[0 + 1]-Predicate[V] Provable T := Provable.definable
```

`Derivation.case_iff` (`:543-560`) is the internal derivation-rule case analysis (`axL, verumIntro, andIntro, orIntro, allIntro, exsIntro, wkRule, shiftRule, cutRule, axm` with `p ∈ T.Δ₁Class`); `Derivation.induction1 (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P) {d} (hd : Derivation T d) ...` (`:562-590`); constructor lemmas `Derivation.axL/verumIntro/andIntro/orIntro/allIntro/exsIntro/wkRule/...` (`:598+`).

D1/D2/D3 at the model level (`Foundation/FirstOrder/Bootstrapping/DerivabilityCondition/`):

```lean
-- D1.lean:20   (variable {V} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {L} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁])
lemma derivable_quote {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : Derivable T (⌜Γ⌝ : V)
-- D1.lean:24
theorem internalize_provability {φ} : T ⊢ φ → Provable T (⌜φ⌝ : V)
-- D1.lean:27
theorem internal_provable_of_outer_provable {φ} : T ⊢ φ → T.internalize V ⊢ ⌜φ⌝
-- D1.lean:30
@[simp] lemma Provable.complete {φ : Sentence L} : T.internalize ℕ ⊢ ⌜φ⌝ ↔ T ⊢ φ
-- D1.lean:34
@[simp] lemma provable_iff_provable {T : Theory L} [T.Δ₁] {φ : Sentence L} : Provable T (⌜φ⌝ : ℕ) ↔ T ⊢ φ

-- D2.lean:21   (variable (T : Theory L) [T.Δ₁])
theorem modus_ponens {φ ψ : Proposition L} (hφψ : Provable T (⌜φ 🡒 ψ⌝ : V)) (hφ : Provable T (⌜φ⌝ : V)) : Provable T (⌜ψ⌝ : V)
-- D2.lean:28
theorem modus_ponens_sentence {σ τ : Sentence L} (hστ : Provable T (⌜σ 🡒 τ⌝ : V)) (hσ : Provable T (⌜σ⌝ : V)) : Provable T (⌜τ⌝ : V)

-- D3.lean  namespace FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic ; variable (T : ArithmeticTheory) [Theory.Δ₁ T] [𝗣𝗔⁻ ⪯ T]
-- :44
noncomputable abbrev toNumVec (w : Fin n → V) : SemitermVec V ℒₒᵣ n k := ((𝕹 ·)⨟ w)
-- :48
theorem term_complete {n : ℕ} (t : FirstOrder.ClosedSemiterm ℒₒᵣ n) (w : Fin n → V) :
    T.internalize V ⊢ (toNumVec w ⤕ ⌜t⌝) ≐  𝕹 (t.valb w)
-- :76
theorem bold_sigma_one_complete {n} {φ : ArithmeticSemisentence n} (hp : Hierarchy 𝚺 1 φ) {w} :
    V ⊧/w φ → T.internalize V ⊢ (toNumVec w ⤔ ⌜φ⌝)
-- :152
theorem sigma_one_provable_of_models {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
     V↓[ℒₒᵣ] ⊧ σ → T.internalize V ⊢ ⌜σ⌝
-- :160  /-- Hilbert–Bernays provability condition D3 -/
theorem sigma_one_complete {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    V↓[ℒₒᵣ] ⊧ σ → Provable T (⌜σ⌝ : V)
-- :165
theorem provable_internalize {σ : ArithmeticSentence} :
    Provable T (⌜σ⌝ : V) → Provable T (⌜provabilityPred T σ⌝ : V)
```
(`⤕`/`⤔` are local infix for `Semiterm.subst`/`Semiformula.subst` on the internal typed syntax, D3.lean:33-35; `𝕹` is the internal typed numeral.)

Internal-typed bridges (`Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Typed.lean`):

```lean
-- :106
structure InternalTheory (V : Type*) (L : Language) [L.Encodable] [L.LORDefinable] where
  theory : Theory L
  Δ₁ : theory.Δ₁
-- :116
def _root_.FFL.FirstOrder.Theory.internalize (T : Theory L) [T.Δ₁] : InternalTheory V L := ⟨T, inferInstance⟩
-- :146
lemma TProvable.iff_provable {σ : Formula V L} : T ⊢ σ ↔ Provable T.theory σ.val
-- :158
lemma tprovable_iff_provable {T : Theory L} [T.Δ₁] {σ : Formula V L} : T.internalize V ⊢ σ ↔ Provable T σ.val
-- :161
lemma tprovable_tquote_iff_provable_quote {T : Theory L} [T.Δ₁] {φ : Proposition L} : T.internalize V ⊢ ⌜φ⌝ ↔ Provable T (⌜φ⌝ : V)
-- :164
lemma tprovable_tquote_iff_provable_quote_sentence {T : Theory L} [T.Δ₁] {σ : Sentence L} : T.internalize V ⊢ ⌜σ⌝ ↔ Provable T (⌜σ⌝ : V)
```

Proof-code bridges (`Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Coding.lean`):

```lean
-- :289
@[simp] lemma proof_of_quote_proof2 {φ : Sentence L} (d : T ⊢₂! (φ : Proposition L)) : Proof T (⌜d⌝ : V) ⌜φ⌝
-- :295
@[simp] lemma proof_of_quote_proof {φ : Sentence L} (b : T ⊢! φ) : Proof T (⌜b⌝ : V) ⌜φ⌝ := proof_of_quote_proof2 b.toProof2
-- :298
lemma coe_quote_proof_eq (d : T ⊢! φ) : (↑(⌜d⌝ : ℕ) : V) = ⌜d⌝
-- :391
lemma Provable.sound {φ : Sentence L} (h : Provable T (⌜φ⌝ : ℕ)) : T ⊢ φ
```
and `Foundation/FirstOrder/Incompleteness/RosserProvability.lean:55`:
```lean
lemma provable_of_standard_proof {n : ℕ} {φ : Sentence L} : Proof T (n : V) ⌜φ⌝ → T ⊢ φ
```
(proof uses `Defined.shigmaOne_absolute V (φ := proof T) ... Proof.defined Proof.defined ![n, ⌜φ⌝]` then `provable_iff_provable`).

### Classes / instances required

```lean
-- Foundation/FirstOrder/Bootstrapping/Syntax/Theory.lean:13   (variable {L : Language} [L.Encodable] [L.LORDefinable])
class Δ₁ (T : Theory L) where
  ch : 𝚫₁.Semisentence 1
  mem_iff : ∀ φ : Proposition L, ℕ ⊧/![⌜φ⌝] ch.val ↔ ∃ σ ∈ T, φ = σ
  isDelta1 : ch.ProvablyProperOn 𝗜𝚺₁
-- :19
abbrev Δ₁ch (T : Theory L) [T.Δ₁] : 𝚫₁.Semisentence 1 := Δ₁.ch T
-- :23 (variable [L.Primcodable])
class RE (T : Theory L) : Prop where re : REPred (· ∈ T)
protected class Primrec (T : Theory L) : Prop where primrec : PrimrecPred (· ∈ T)
-- :61
def _root_.FFL.FirstOrder.Theory.Δ₁Class (T : Theory L) [T.Δ₁] : Set V := { φ : V | V ⊧/![φ] T.Δ₁ch.val }
-- :86
@[simp] lemma Δ₁Class.mem_iff {φ : Sentence L} : (⌜φ⌝ : V) ∈ T.Δ₁Class ↔ φ ∈ T
-- Δ₁ constructors (:104-145):
abbrev Δ₁.add (dT : T.Δ₁) (dU : U.Δ₁) : (T ∪ U).Δ₁            -- ch := T.Δ₁ch ⋎ U.Δ₁ch
abbrev Δ₁.ofEq (dT : T.Δ₁) (h : T = U) : U.Δ₁
instance Δ₁.empty : Theory.Δ₁ (∅ : Theory L)
abbrev Δ₁.singleton (φ : Sentence L) : Theory.Δ₁ {φ}          -- ch := .ofZero (.mkSigma “x. x = ↑(Encodable.encode φ)”) _
abbrev Δ₁.ofList (l : List (Sentence L)) : Δ₁ {φ | φ ∈ l}
noncomputable abbrev Δ₁.ofFinite (T : Theory L) (h : Set.Finite T) : T.Δ₁
instance [T.Δ₁] [U.Δ₁] : (T ∪ U).Δ₁ ; instance (φ : Sentence L) : Theory.Δ₁ {φ} ; instance Δ₁.insert [d : T.Δ₁] : (insert φ T).Δ₁
```
Concrete instances: `Foundation/FirstOrder/Incompleteness/Definability.lean:640 noncomputable instance PeanoMinus.delta1 : (𝗣𝗔⁻ : ArithmeticTheory).Δ₁`; `:1070 noncomputable instance : 𝗣𝗔.Δ₁`; `:1072 noncomputable instance : 𝗜𝚺₁.Δ₁`; `:1062 instance : 𝗣𝗔.RE`; `:1064 instance : 𝗜𝚺₁.RE`. For an RE-only theory, `Foundation/FirstOrder/Bootstrapping/Syntax/CraigTrick.lean:128 def craig : Theory L := { φ | ∃ (σ : Sentence L) (s : ℕ), ℕ ⊧/![(s : ℕ), ⌜σ⌝] T.reWitness.val ∧ φ = σ.padding s}`, `:330 noncomputable instance : (T.craig).Δ₁`, `:339 instance : T.craig ⪯ T`, `:345 instance : T ⪯ T.craig`, `:352 instance : T ≊ T.craig`.

```lean
-- Foundation/FirstOrder/Arithmetic/Basic/Model.lean:109
class ArithmeticTheory.SoundOn (T : ArithmeticTheory) (F : ArithmeticSentence → Prop) where
  sound : ∀ {σ}, T ⊢ σ → F σ → ℕ↓[ℒₒᵣ] ⊧ σ
-- :116
instance [ℕ↓[ℒₒᵣ] ⊧* T] : T.SoundOn F
-- :118
lemma SoundOn.of_weakerThan (F : ArithmeticSentence → Prop) (T U : ArithmeticTheory) [U ⪯ T] [T.SoundOn F] : U.SoundOn F
-- :122
lemma consistent_of_sound [SoundOn T F] (hF : F ⊥) : Entailment.Consistent T

-- Foundation/FirstOrder/Arithmetic/Basic/Hierarchy.lean:481
abbrev ArithmeticTheory.SoundOnHierarchy (T : ArithmeticTheory) (Γ : Polarity) (k : ℕ) := T.SoundOn (Arithmetic.Hierarchy Γ k)
-- :483
lemma ArithmeticTheory.soundOnHierarchy (T : ArithmeticTheory) (Γ : Polarity) (k : ℕ) [T.SoundOnHierarchy Γ k] :
    T ⊢ σ → Arithmetic.Hierarchy Γ k σ → ℕ↓[ℒₒᵣ] ⊧ σ := SoundOn.sound
-- :486
instance (T : ArithmeticTheory) [T.SoundOnHierarchy 𝚺 1] : Entailment.Consistent T
-- Foundation/FirstOrder/Arithmetic/Schemata.lean:416,418
instance sigmaOneSound_ISigmaOne : 𝗜𝚺₁.SoundOnHierarchy 𝚺 1 := inferInstance
instance sigmaOneSound_Peano : 𝗣𝗔.SoundOnHierarchy 𝚺 1 := inferInstance
```

Subtheory instances (`Foundation/FirstOrder/Arithmetic/Schemata.lean`): `:85 instance : 𝗜𝚺₀ ⪯ 𝗜𝚺₁`; `:87 instance : 𝗜𝚺i ⪯ 𝗣𝗔`; `:98 instance : 𝗣𝗔⁻ ⪯ 𝗜𝗢𝗽𝗲𝗻`; `:100 instance : 𝗜𝗢𝗽𝗲𝗻 ⪯ 𝗜𝚺₀`; `:102 instance : 𝗜𝚺₁ ⪯ 𝗣𝗔`; `:104 instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔`; `:424 instance : 𝗣𝗔 ⪯ 𝗧𝗔`; `:426 instance (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] : 𝗥₀ ⪯ T`; `:430 [𝗜𝚺₀ ⪯ T] : 𝗣𝗔⁻ ⪯ T`; `:434 [𝗜𝚺₁ ⪯ T] : 𝗣𝗔⁻ ⪯ T`; `:438 [𝗣𝗔 ⪯ T] : 𝗣𝗔⁻ ⪯ T`. `PeanoMinus/Basic.lean:167 instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻`, `:366 instance : 𝗥₀ ⪯ 𝗣𝗔⁻`, `:405 instance : 𝗤 ⪯ 𝗣𝗔⁻`. `R0/Basic.lean:26 instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗥₀`. `TA/Basic.lean:21 instance (T : ArithmeticTheory) [ℕ↓[ℒₒᵣ] ⊧* T] : T ⪯ 𝗧𝗔`.

Arithmetic completeness wrapper used everywhere (`Foundation/FirstOrder/Arithmetic/Basic/Model.lean:78`):
```lean
lemma complete (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (φ : ArithmeticSentence) (H : ∀ (M : Type*) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T], M↓[ℒₒᵣ] ⊧ φ) : T ⊢ φ
-- :100
lemma weakerThan_of_models (T S : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ S] (H : ∀ (M : Type*) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* S], M↓[ℒₒᵣ] ⊧* T) : T ⪯ S
```
Soundness (`Foundation/FirstOrder/Basic/Soundness.lean`): `:99 theorem Proof.sound {φ : Sentence L} : T ⊢ φ → T ⊨[Struc.{v, u} L] φ`; `:128 lemma models_of_provable (hT : M↓[L] ⊧* T) {φ : Sentence L} (h : T ⊢ φ) : M↓[L] ⊧ φ`. `Semantics.lean:539 lemma models_iff : M↓[L] ⊧ σ ↔ σ.Realize M := by rfl`; `:559 lemma consequence_iff {φ} : T ⊨[Struc.{v, u} L] φ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M], M↓[L] ⊧* T → M↓[L] ⊧ φ)`; `:526 notation: max M "↓[" L "]" => Language.str M L`.

---

## (2) Löb / Second / First / Tarski / FixedPoint

`Foundation/FirstOrder/Incompleteness/Löb.lean` (22 lines):
```lean
-- :14
variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {σ : ArithmeticSentence}
-- :16
theorem löb_theorem : T ⊢ provabilityPred T σ 🡒 σ → T ⊢ σ :=
  ProvabilityAbstraction.löb_theorem (𝔅 := T.standardProvability)
-- :19
theorem formalized_löb_theorem : 𝗜𝚺₁ ⊢ provabilityPred T (provabilityPred T σ 🡒 σ) 🡒 provabilityPred T σ :=
  ProvabilityAbstraction.formalized_löb_theorem (𝔅 := T.standardProvability)
```

`Foundation/FirstOrder/Incompleteness/Second.lean`:
```lean
-- :16
variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
-- :19
theorem consistent_unprovable [Consistent T] : T ⊬ T.consistent.val := ProvabilityAbstraction.con_unprovable (𝔅 := T.standardProvability)
-- :23
theorem craig_consistent_unprovable_of_RE (T : ArithmeticTheory) [T.RE] [𝗜𝚺₁ ⪯ T] [Consistent T] : T ⊬ T.craig.consistent.val
-- :27
theorem inconsistent_unprovable [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T ⊬ ∼T.consistent.val
-- :31
theorem inconsistent_independent [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : Independent T T.consistent.val
-- :34
instance [Consistent T] : T ⪱ T ∪ T.Con
-- :39
instance [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T ⪱ T ∪ T.Incon
```
with (`Consistency.lean`): `:24 def _root_.FFL.FirstOrder.Theory.Consistent : Prop := ¬Provable T (⌜(⊥ : Sentence L)⌝ : V)`; `:36 noncomputable def _root_.FFL.FirstOrder.Theory.consistent : 𝚷₁.Sentence := .mkPi (∼provabilityPred T ⊥)`; `:61 abbrev Theory.Con : ArithmeticTheory := {T.consistent.val}`; `:63 abbrev Theory.Incon : ArithmeticTheory := {∼T.consistent.val}`; `:73 theorem consistent_eq : T.consistent = T.standardProvability.con := rfl`; `:75 @[simp] lemma standard_consistent [𝗥₀ ⪯ T] : T.Consistent ℕ ↔ Entailment.Consistent T`.

`Foundation/FirstOrder/Incompleteness/First.lean`:
```lean
-- :17
theorem incomplete (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : Incomplete T
-- proof: D φ := IsSemiformula ℒₒᵣ 1 φ ∧ Provable T (neg ℒₒᵣ <| subst ℒₒᵣ ?[numeral φ] φ); D_re by `definability` + rePred_iff_sigma1;
--        δ := codeOfREPred D; π := δ/[⌜δ⌝]; T ⊢ π ↔ T ⊢ ∼π.
-- :47
theorem exists_true_but_unprovable_sentence_of_sigma1sound (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ∃ δ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ δ ∧ T ⊬ δ
-- :59
theorem incomplete_of_RE (T : ArithmeticTheory) [T.RE] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : Incomplete T
-- :67
instance {T : ArithmeticTheory} [ℕ↓[ℒₒᵣ] ⊧* T] [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : T ⪱ 𝗧𝗔
```
There is NO declaration literally named `gödel` in First.lean; the abstract Gödel sentence is `ProvabilityAbstraction.gödel 𝔅` (§4). The "sentence with one free variable → fixpoint" mechanism:

`Foundation/FirstOrder/Bootstrapping/FixedPoint.lean` (namespace `FFL.FirstOrder.Arithmetic`, `variable {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T]` at :122):
```lean
-- :22 (namespace Bootstrapping.Arithmetic)
noncomputable def substNumeral (φ x : V) : V := subst ℒₒᵣ ?[numeral x] φ
-- :24
lemma substNumeral_app_quote (σ π : ArithmeticSemisentence 1) :
    substNumeral ⌜σ⌝ (⌜π⌝ : V) = ⌜(σ/[⌜π⌝] : ArithmeticSentence)⌝
-- :29
noncomputable def substNumerals (φ : V) (v : Fin k → V) : V := subst ℒₒᵣ (matrixToVec (fun i ↦ numeral (v i))) φ
-- :31
lemma substNumerals_app_quote (σ : ArithmeticSemisentence k) (v : Fin k → ℕ) :
    (substNumerals ⌜σ⌝ (v ·) : V) = ⌜((Rew.subst (fun i ↦ ↑(v i))) ▹ σ : ArithmeticSentence)⌝
-- :51
noncomputable def ssnum : 𝚺₁.Semisentence 3 := .mkSigma
  “y φ x. ∃ n, !numeralGraph n x ∧ ∃ v, !adjoinDef v n 0 ∧ !(substsGraph ℒₒᵣ) y v φ”
-- :54
instance substNumeral.defined : 𝚺₁-Function₂ (substNumeral : V → V → V) via ssnum
-- :126
noncomputable def diag (θ : ArithmeticSemisentence 1) : ArithmeticSemisentence 1 := “x. ∀ y, !ssnum y x x → !θ y”
-- :128
noncomputable def fixedpoint (θ : ArithmeticSemisentence 1) : ArithmeticSentence := (diag θ)/[⌜diag θ⌝]
-- :130
theorem diagonal (θ : ArithmeticSemisentence 1) :
    T ⊢ fixedpoint θ 🡘 θ/[⌜fixedpoint θ⌝]
-- :151-159  (multi)
noncomputable def multidiag (θ : ArithmeticSemisentence k) : ArithmeticSemisentence k
noncomputable def multifixedpoint (θ : Fin k → ArithmeticSemisentence k) (i : Fin k) : ArithmeticSentence := (Rew.subst fun j ↦ ⌜multidiag (θ j)⌝) ▹ (multidiag (θ i))
theorem multidiagonal (θ : Fin k → ArithmeticSemisentence k) :
    T ⊢ multifixedpoint θ i 🡘 (Rew.subst fun j ↦ ⌜multifixedpoint θ j⌝) ▹ (θ i)
-- :174-198
noncomputable def exclusiveMultifixedpoint (θ : Fin k → ArithmeticSemisentence k) (i : Fin k) : ArithmeticSentence
theorem exclusiveMultidiagonal ... ; lemma multifixedpoint_pi (h : ∀ i, Hierarchy 𝚷 (m + 1) (θ i)) : Hierarchy 𝚷 (m + 1) (multifixedpoint θ i)
-- :204-231 (parameterized)
noncomputable def parameterizedDiag (θ : ArithmeticSemisentence (k + 1)) : ArithmeticSemisentence (k + 1) := “x. ∀ y, !(ssnumParams k) y x x → !θ y ⋯”
noncomputable def parameterizedFixedpoint (θ : ArithmeticSemisentence (k + 1)) : ArithmeticSemisentence k
theorem parameterized_diagonal (θ : ArithmeticSemisentence (k + 1)) :
    T ⊢ ∀¹* (parameterizedFixedpoint θ 🡘 “!θ !!(⌜parameterizedFixedpoint θ⌝) ⋯”)
theorem parameterized_diagonal₁ (θ : ArithmeticSemisentence 2) :
    T ⊢ ∀¹ (parameterizedFixedpoint θ 🡘 θ/[⌜parameterizedFixedpoint θ⌝, #0])
```
So: a `θ : ArithmeticSemisentence 1` (one bound variable `#0`, no free vars) becomes the sentence `fixedpoint θ`, and `diagonal` gives `T ⊢ fixedpoint θ 🡘 θ/[⌜fixedpoint θ⌝]` for any `T` with `[𝗜𝚺₁ ⪯ T]`. `⌜fixedpoint θ⌝` there is the closed term `Semiterm.Operator.GödelNumber.gödelNumber'` = numeral of `Encodable.encode`.

`Foundation/FirstOrder/Incompleteness/Tarski.lean`:
```lean
-- :9
variable {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T] [Entailment.Consistent T]
-- :12
lemma not_exists_tarski_predicate : ¬∃ τ : ArithmeticSemisentence 1, ∀ σ, T ⊢ σ 🡘 τ/[⌜σ⌝]
-- :20
theorem undefinability_of_truth : ¬∃ τ : ArithmeticSemisentence 1, ∀ σ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ σ ↔ ℕ↓[ℒₒᵣ] ⊧ τ/[⌜σ⌝]
```
(Relevant to ArithS only as a negative bound: a bounded `□_k` interpretation cannot be a truth predicate.)

---

## (3) `Church.lean`, `Halting.lean`, representation bridges

`Foundation/FirstOrder/Incompleteness/Church.lean`:
```lean
-- :28
lemma computable_iff_sigma1_simulate {α β : Type*} [Primcodable α] [Primcodable β]
    {f : ℕ → ℕ} (hf : 𝚺₁-Function₁ f)
    {F : α → β} (h : ∀ a, f (Encodable.encode a) = Encodable.encode (F a)) :
    Computable F
-- :38
lemma computable₂_iff_sigma1_simulate {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : ℕ → ℕ → ℕ} (hf : 𝚺₁-Function₂ f)
    {F : α → β → γ} (h : ∀ a b, f (Encodable.encode a) (Encodable.encode b) = Encodable.encode (F a b)) :
    Computable₂ F
-- :49
variable {T : ArithmeticTheory} [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
-- :51
theorem uncomputable_theory_of_sigma1Sound : ¬ComputablePred T.theory
-- :79  (variable {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T] [Entailment.Consistent T])
theorem uncomputable_theory_of_consistent : ¬ComputablePred T.theory
-- :104
theorem undecidability_first_order_logic : ¬ComputablePred ((∅ : ArithmeticTheory).theory)
```
"simulate" is NOT a definition: `computable_iff_sigma1_simulate` is a lemma whose hypotheses are (i) `hf : 𝚺₁-Function₁ f` = `HierarchySymbol.DefinableFunction₁ 𝚺₁ f` over `V := ℕ` (Definable with parameters, NO specific formula — see §8), and (ii) `h`: `f` tracks `F` through `Encodable.encode`. Direction: definability ⇒ `Computable F` (via `computable_iff_sigma1.mpr`). The only instance needed is `[Primcodable α] [Primcodable β]` (Mathlib). It does NOT produce a formula. Usage pattern at `:55`: `computable₂_iff_sigma1_simulate (f := substNumeral (V := ℕ)) (by definability) fun σ τ ↦ by simp [←Sentence.quote_eq_encode_nat, substNumeral_app_quote]`.

Representation theorems (`Foundation/FirstOrder/Arithmetic/R0/Representation.lean`):
```lean
-- :85
lemma sigma1_re (ε : ξ → ℕ) {k} {φ : ArithmeticSemiformula ξ k} (hp : Hierarchy 𝚺 1 φ) :
    REPred fun v : List.Vector ℕ k ↦ φ.Eval v.get ε
-- :174
def code (c : Code k) : ArithmeticSemisentence (k + 1)
-- :189
@[simp] lemma code_sigma_one {k} (c : Nat.ArithPart₁.Code k) : Hierarchy 𝚺 1 (code c)
-- :241
lemma models_code {c : Code k} {f : List.Vector ℕ k →. ℕ} (hc : c.eval f) (y : ℕ) (v : Fin k → ℕ) :
    (code c).Evalb (y :> v) ↔ y ∈ f (List.Vector.ofFn v)
-- :246
noncomputable def codeOfPartrec' {k} (f : List.Vector ℕ k →. ℕ) : ArithmeticSemisentence (k + 1) :=
  code <| Classical.epsilon fun c ↦ ∀ y v, (code c).Evalb (y :> v) ↔ y ∈ f (List.Vector.ofFn v)
-- :249
lemma codeOfPartrec'_spec {k} {f : List.Vector ℕ k →. ℕ} (hf : Nat.Partrec' f) {y : ℕ} {v : Fin k → ℕ} :
    (codeOfPartrec' f).Evalb (y :> v) ↔ y ∈ f (List.Vector.ofFn v)
-- :311  (variable {M} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻])
lemma code_uniq {k} {c : Code k} {v : Fin k → M} {z z' : M} : ...  -- graph functionality in any 𝗣𝗔⁻ model
-- :324
noncomputable def codeOfREPred (p : ℕ → Prop) : ArithmeticSemisentence 1 :=
  let f : ℕ →. Unit := fun a ↦ Part.assert (p a) fun _ ↦ Part.some ()
  (codeOfPartrec' (fun v ↦ (f (v.get 0)).map fun _ ↦ 0))/[‘0’, #0]
-- :328
lemma codeOfREPred_spec {p : ℕ → Prop} (hp : REPred p) {x : ℕ} : (codeOfREPred p).Evalb ![x] ↔ p x
-- :337
variable {T : ArithmeticTheory} [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
-- :340  /-- Weak representation of a r.e. predicate -/
theorem rePred_weak_representation {p : ℕ → Prop} (hp : REPred p) {x : ℕ} :
    p x ↔ T ⊢ (codeOfREPred p)/[x]
-- :351
noncomputable def codeOfComputablePred (p : ℕ → Prop) : ArithmeticSemisentence 1 :=
  (codeOfPartrec' (fun v ↦ Part.some (if p (v.get 0) then 1 else 0)))/[‘1’, #0]
-- :354
@[simp] lemma codeOfComputablePred_sigma1 (p : ℕ → Prop) : Hierarchy 𝚺 1 (codeOfComputablePred p)
-- :376  (variable {T : ArithmeticTheory} {x : ℕ})
theorem codeOfComputablePred_provable [𝗥₀ ⪯ T] (hp : ComputablePred p) (h : p x) :
    T ⊢ (codeOfComputablePred p)/[↑x]
-- :386
theorem codeOfComputablePred_provable_neg [𝗣𝗔⁻ ⪯ T] (hp : ComputablePred p) (h : ¬p x) :
    T ⊢ ∼((codeOfComputablePred p)/[↑x])
-- :414
theorem rePred_iff_sigma1 {p : ℕ → Prop} : REPred p ↔ 𝚺₁-Predicate p
-- :426
theorem computablePred_iff_delta1 {p : ℕ → Prop} : ComputablePred p ↔ 𝚫₁-Predicate p
-- :440
theorem computable_iff_sigma1 {f : ℕ → ℕ} : Computable f ↔ 𝚺₁-Function₁ f
-- :461
theorem computable₂_iff_sigma1 {f : ℕ → ℕ → ℕ} : Computable₂ f ↔ 𝚺₁-Function₂ f
```
**Answer to "is there a version giving a Σ₁ semisentence REPRESENTING a computable function f with `f a = b ↔ ℕ ⊧ φ(a,b)` and `T ⊢ φ(a̅,b̅)` when true"**: YES, by composition, no single named lemma:
- formula: `codeOfPartrec' F` for `F : List.Vector ℕ 1 →. ℕ := fun v ↦ Part.some (f (v.get 0))`; `Hierarchy 𝚺 1` by `simp [codeOfPartrec']` (`code_sigma_one`); truth: `codeOfPartrec'_spec (Nat.Partrec'.of_part hF) : (codeOfPartrec' F).Evalb (y :> ![a]) ↔ y ∈ F ![a]`, i.e. `↔ y = f a` (this is exactly the `.mp` half of `computable_iff_sigma1` at :440-450, which packages it as `⟨.mkSigma (codeOfPartrec' F) (by simp [codeOfPartrec']), ...⟩`);
- provability when true: `sigma_one_completeness` (`R0/Basic.lean:143`, `[𝗥₀ ⪯ T]`) or `sigma_one_completeness_iff_param` (§6) applied to `(codeOfPartrec' F)/[b, a]`; uniqueness/negative side in `𝗣𝗔⁻`: `code_uniq` (:311) as used in `codeOfComputablePred_provable_neg`.

Halting.lean (`variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]`):
```lean
-- :14
lemma incomplete_of_REPred_not_ComputablePred_Nat' {P : ℕ → Prop} (hRE : REPred P) (hC : ¬ComputablePred P) :
  ∃ φ : ArithmeticSemisentence 1, ∃ a : ℕ, T ⊬ φ/[a] ∧ T ⊬ ∼φ/[a]
-- :52
lemma incomplete_of_REPred_not_ComputablePred_Nat {P : ℕ → Prop} (hRE : REPred P) (hC : ¬ComputablePred P) : Entailment.Incomplete T
-- :63
lemma _root_.REPred.iff_decoded_pred {α : Type*} [Primcodable α] {A : α → Prop} :
    REPred A ↔ REPred fun n : ℕ ↦ (Encodable.decode (α := α) n).elim False A
-- :82
lemma _root_.ComputablePred.iff_decoded_pred {α : Type*} [Primcodable α] {A : α → Prop} :
    ComputablePred A ↔ ComputablePred fun n : ℕ ↦ (Encodable.decode (α := α) n).elim False A
-- :108
lemma incomplete_of_REPred_not_ComputablePred {α : Type*} [Primcodable α] {P : α → Prop} (hRE : REPred P) (hC : ¬ComputablePred P) : Entailment.Incomplete T
-- :118
theorem incomplete_of_halting_problem : Entailment.Incomplete T
```
Note the proof at :26 shows the idiom for "provability of a numeral instance is Σ₁": `𝚺₁-Predicate fun b : ℕ ↦ Bootstrapping.Provable T (Bootstrapping.neg ℒₒᵣ <| Bootstrapping.subst ℒₒᵣ ?[Bootstrapping.Arithmetic.numeral b] ⌜φ⌝)` by `definability`, and the bridge `T ⊢ ∼φ/[a] ↔ Provable T (neg (subst ?[numeral a] ⌜φ⌝))` via `Provable.sound` / `internalize_provability (V := ℕ)` with `simp [Sentence.quote_def, Semiformula.quote_def, Rewriting.emb_subst_eq_subst_coe₁]`.

---

## (4) `ProvabilityAbstraction/`

`Basic.lean` (namespace `FFL.FirstOrder`, then `ProvabilityAbstraction`):
```lean
-- :19
abbrev Language.ReferenceableBy (L L₀ : Language) := Semiterm.Operator.GödelNumber L₀ (Sentence L)
-- :23
structure Provability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  prov : Semisentence L₀ 1
  /-- Derivability condition `D1` -/
  bew_def {σ : Sentence L} : T ⊢ σ → T₀ ⊢ prov/[⌜σ⌝]
-- :32
@[coe] def pr (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L₀ := 𝔅.prov/[⌜σ⌝]
instance : CoeFun (Provability T₀ T) (fun _ ↦ Sentence L → Sentence L₀) := ⟨pr⟩
-- :35
def con (𝔅 : Provability T₀ T) : Sentence L₀ := ∼𝔅 ⊥
-- :37
abbrev dia (𝔅 : Provability T₀ T) (φ : Sentence L) : Sentence L₀ := ∼𝔅 (∼φ)
-- :52
lemma D1 {𝔅 : Provability T₀ T} {σ : Sentence L} : T ⊢ σ → T₀ ⊢ 𝔅 σ := fun h ↦ 𝔅.bew_def h
-- :54
class HBL2 [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  D2 {σ τ : Sentence L} : T₀ ⊢ 𝔅 (σ 🡒 τ) 🡒 𝔅 σ 🡒 𝔅 τ
-- :58 variable [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T)
-- :60
class HBL3 where
  D3 {σ : Sentence L} : T₀ ⊢ 𝔅 σ 🡒 𝔅 (𝔅 σ)
-- :64
class HBL extends 𝔅.HBL2, 𝔅.HBL3
-- :66
class Mono [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  mono {σ τ : Sentence L} : T ⊢ σ 🡒 τ → T₀ ⊢ 𝔅 σ 🡒 𝔅 τ
-- :70
class Ext ... where ext {σ τ : Sentence L} : T ⊢ σ 🡘 τ → T₀ ⊢ 𝔅 σ 🡘 𝔅 τ
-- :74
class Rosser ... where Ros {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ ∼𝔅 σ
-- :84
class FormalizedCompleteOn (𝔅 : Provability T₀ T) (σ) where
  formalized_complete_on : T₀ ⊢ σ 🡒 𝔅 σ
-- :89
instance [∀ σ, 𝔅.FormalizedCompleteOn (𝔅 σ)] : 𝔅.HBL3
-- :94
class Kreisel [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T) where
  KR {σ : Sentence L} : T ⊢ 𝔅 σ → T ⊢ σ
-- :100
class SoundOn [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}
  (𝔅 : Provability T₀ T) (M : outParam Type*) [Nonempty M] [Structure L₀ M] where
  sound_on {σ : Sentence L} : M↓[L₀] ⊧ (𝔅 σ : Sentence L₀) → T ⊢ σ
-- :109
lemma syntactical_sound {T₀ T : Theory L} {𝔅 : Provability T₀ T} (M : Type*) [Nonempty M] [Structure L M] [SoundOn 𝔅 M] [M↓[L] ⊧* T₀] :
    ∀ {σ : Sentence L}, T₀ ⊢ 𝔅 σ → T ⊢ σ
-- :129
lemma bew_distribute_imply [𝔅.HBL2] (h : T₀ ⊢ 𝔅 (σ 🡒 τ)) : T₀ ⊢ 𝔅 σ 🡒 𝔅 τ := D2 ⨀ h
-- :131
instance [𝔅.HBL2] : 𝔅.Mono ; instance [𝔅.HBL2] : 𝔅.Ext
-- :134
lemma bew_distribute_and [𝔅.HBL2] [L₀.DecidableEq] : T₀ ⊢ 𝔅 (σ ⋏ τ) 🡒 𝔅 σ ⋏ 𝔅 τ
lemma bew_distribute_and' ... : T₀ ⊢ 𝔅 (σ ⋏ τ) → T₀ ⊢ 𝔅 σ ⋏ 𝔅 τ
-- :141
lemma bew_collect_and [𝔅.HBL2] [L₀.DecidableEq] [L.DecidableEq] : T₀ ⊢ 𝔅 σ ⋏ 𝔅 τ 🡒 𝔅 (σ ⋏ τ)
-- :147
lemma dia_mono [L₀.DecidableEq] [L.DecidableEq] [𝔅.Mono] (h : T ⊢ σ 🡒 τ) : T₀ ⊢ 𝔅.dia σ 🡒 𝔅.dia τ
-- :161  (variable [L.ReferenceableBy L] {T₀ T : Theory L} [T₀ ⪯ T])
lemma mono' [𝔅.Mono] (h : T₀ ⊢ σ 🡒 τ) : T₀ ⊢ 𝔅 σ 🡒 𝔅 τ
lemma ext' [𝔅.Ext] (h : T₀ ⊢ σ 🡘 τ) : T₀ ⊢ 𝔅 σ 🡘 𝔅 τ
-- :174
class Diagonalization [L.ReferenceableBy L] (T : Theory L) where
  fixedpoint : Semisentence L 1 → Sentence L
  diag (θ) : T ⊢ fixedpoint θ 🡘 θ/[⌜fixedpoint θ⌝]
-- :180 variable [L.ReferenceableBy L] {T₀ T : Theory L} [Diagonalization T₀] {𝔅 : Provability T₀ T}
-- :184
def gödel (𝔅 : Provability T₀ T) : Sentence L := fixedpoint T₀ “x. ¬!𝔅.prov x”
-- :187
lemma gödel_spec : T₀ ⊢ (gödel 𝔅) 🡘 ∼𝔅 (gödel 𝔅)
-- :191 variable [L.DecidableEq] [T₀ ⪯ T] [Consistent T]
theorem unprovable_gödel : T ⊬ (gödel 𝔅)                              -- :194
theorem unrefutable_gödel [𝔅.Kreisel] : T ⊬ ∼(gödel 𝔅)                 -- :202
theorem gödel_independent [𝔅.Kreisel] : Independent T (gödel 𝔅)        -- :209
theorem first_incompleteness [𝔅.Kreisel] : Incomplete T                -- :214
-- :222 variable [𝔅.HBL]
lemma formalized_consistent_of_existance_unprovable [L.DecidableEq] : T₀ ⊢ ∼𝔅 σ 🡒 𝔅.con   -- :225
-- :229 variable [L.DecidableEq] [T₀ ⪯ T]
theorem formalized_unprovable_gödel  : T₀ ⊢ 𝔅.con 🡒 ∼𝔅 𝐆               -- :232 (𝐆 = gödel 𝔅)
theorem gödel_iff_con : T₀ ⊢ 𝐆 🡘 𝔅.con                                 -- :239
theorem con_unprovable [Consistent T] : T ⊬ 𝔅.con                        -- :245
theorem con_unrefutable [Consistent T] [𝔅.Kreisel] : T ⊬ ∼𝔅.con         -- :251
theorem con_independent [Consistent T] [𝔅.Kreisel] : Independent T 𝔅.con -- :257
-- :267
def kreisel (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L := fixedpoint T₀ “x. !𝔅.prov x → !σ”
-- :273
lemma kreisel_spec : T₀ ⊢ (𝐊 σ) 🡘 (𝔅 (𝐊 σ) 🡒 σ)
-- :279 variable [𝔅.HBL] ; :284 variable [L.DecidableEq] [T₀ ⪯ T]
theorem löb_theorem (H : T ⊢ 𝔅 σ 🡒 σ) : T ⊢ σ                              -- :286
theorem formalized_löb_theorem : T₀ ⊢ 𝔅 (𝔅 σ 🡒 σ) 🡒 𝔅 σ                    -- :291
lemma formalized_unprovable_not_con [Consistent T] [𝔅.Kreisel] : T ⊬ 𝔅.con 🡒 ∼𝔅 (∼𝔅.con)     -- :297
lemma formalized_unrefutable_gödel [Consistent T] [𝔅.Kreisel] : T ⊬ 𝔅.con 🡒 ∼𝔅 (∼(gödel 𝔅)) -- :303
-- :319 Rosser section: variable {T₀ T : Theory L} [Diagonalization T₀] [T₀ ⪯ T] [Consistent T] {𝔅 : Provability T₀ T}
theorem unrefutable_rosser [𝔅.Rosser] : T ⊬ ∼𝐑 ; theorem rosser_independent ... ; theorem rosser_first_incompleteness ...
theorem kreisel_remark [𝔅.Rosser] : T ⊢ 𝔅.con                             -- :340
```
Standard-predicate instances: `StandardProvability.lean:18 Diagonalization 𝗜𝚺₁`, `:38 T.standardProvability : Provability 𝗜𝚺₁ T` (for ANY `T : Theory L` with `[T.Δ₁]`, `[L.Encodable] [L.LORDefinable]`), `:44 HBL2`, `:48 SoundOn ℕ`, `:83 HBL3 [𝗣𝗔⁻ ⪯ T]`, `:85 HBL [𝗣𝗔⁻ ⪯ T]`, `:87 Kreisel [T.SoundOnHierarchy 𝚺 1]`. Rosser: `RosserProvability.lean:128 noncomputable abbrev Theory.rosserProvability : Provability 𝗜𝚺₁ T` with `:132 instance : T.rosserProvability.Rosser`.

`Height.lean` (`variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L}`, `{𝔅 : Provability T₀ T}`):
```lean
-- :18
noncomputable def Provability.height (𝔅 : Provability T₀ T) : ENat := ENat.find (T ⊢ 𝔅^[·] ⊥)
-- :21
@[simp] lemma neg_iterated_prov (φ : Sentence L) : ∼(𝔅^[n] φ) = 𝔅.dia^[n] (∼φ)
-- :24
lemma boxBot_monotone [T₀ ⪯ T] [𝔅.HBL] : n ≤ m → T ⊢ 𝔅^[n] ⊥ 🡒 𝔅^[m] ⊥
-- :43
lemma iIncon_unprovable_of_sigma1_sound [𝔅.Kreisel] [Entailment.Consistent T] : ∀ n, T ⊬ 𝔅^[n] ⊥
-- :53
lemma height_eq_top_iff : 𝔅.height = ⊤ ↔ ∀ n, T ⊬ 𝔅^[n] ⊥
-- :55
lemma height_le_of_boxBot {n : ℕ} (h : T ⊢ 𝔅^[n] ⊥) : 𝔅.height ≤ n
-- :58
lemma height_lt_pos_of_boxBot (hSound : ∀ {σ}, T₀ ⊢ 𝔅 σ → T ⊢ σ) {n : ℕ} (pos : 0 < n) (h : T₀ ⊢ 𝔅^[n] ⊥) : 𝔅.height < n
-- :68
lemma height_le_iff_boxBot [T₀ ⪯ T] [𝔅.HBL] {n : ℕ} : 𝔅.height ≤ n ↔ T ⊢ 𝔅^[n] ⊥
-- :77
lemma height_eq_top_of_sound_and_consistent [𝔅.Kreisel] [Entailment.Consistent T] : 𝔅.height = ⊤
-- :81
lemma height_eq_zero_of_inconsistent (h : Entailment.Inconsistent T) : 𝔅.height = 0
-- :92
noncomputable abbrev ArithmeticTheory.height (T : ArithmeticTheory) [T.Δ₁] : ℕ∞ := T.standardProvability.height
-- :97
lemma height_eq_top_of_sigma1_sound (T : ArithmeticTheory) [T.Δ₁] [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T.height = ⊤
-- :101,:104
lemma ISigma1_height_eq_top : 𝗜𝚺₁.height = ⊤ ; lemma Peano_height_eq_top : 𝗣𝗔.height = ⊤
```

`Refutability.lean`:
```lean
-- :15
structure Refutability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  refu : Semisentence L₀ 1
  refu_def {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ refu/[⌜σ⌝]
-- :23
@[coe] def rf (𝔚 : Refutability T₀ T) (σ : Sentence L) : Sentence L₀ := 𝔚.refu/[⌜σ⌝]
-- :35
lemma R1 {𝔚 : Refutability T₀ T} {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ 𝔚 σ
-- :52
def jeroslow (𝔚 : Refutability T₀ T) : Sentence L := fixedpoint T₀ 𝔚.refu
-- :54
lemma jeroslow_def : T₀ ⊢ jeroslow 𝔚 🡘 𝔚 (jeroslow 𝔚)
-- :59
class Refutability.SoundOn (𝔚 : Refutability T₀ T) (σ : Sentence L) where
  sound_on : T ⊢ 𝔚 σ → T ⊢ ∼σ
-- :73
lemma unprovable_jeroslow [T₀ ⪯ T] [Consistent T] [𝔚.SoundOn (jeroslow 𝔚)] : T ⊬ jeroslow 𝔚
-- :90
def safe (𝔅 : Provability T₀ T) (𝔚 : Refutability T₀ T) : Semisentence L 1 := “x. ¬(!𝔅.prov x ∧ !𝔚.refu x)”
-- :93
def flon (𝔅 : Provability T₀ T) (𝔚 : Refutability T₀ T) : Sentence L := “∀ x, !(safe 𝔅 𝔚) x”
-- :107
lemma jeroslow_not_safe [𝔅.FormalizedCompleteOn 𝐉] : T ⊢ 𝐉 🡒 (𝔅 𝐉 ⋏ 𝔚 𝐉)
-- :116
lemma unprovable_flon [consis : Consistent T] [𝔅.FormalizedCompleteOn 𝐉] : T ⊬ flon 𝔅 𝔚
```
(`Jeroslow.lean:63 noncomputable abbrev standardRefutability (T : ArithmeticTheory) [T.Δ₁] : Refutability 𝗜𝚺₁ T`.)

---

## (5) `RestrictedProvability.lean` — full API

```lean
-- :19 namespace Theory
-- :21 variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
-- :22 variable {L : Language} [L.Encodable] [L.LORDefinable]
-- :24 variable {T U : Theory L} [T.Δ₁] [U.Δ₁]

-- :27  /-- Provability with restriction of proof size -/
def RestrictedProvable (f : V → V) (e : ℕ) (T : Theory L) [T.Δ₁] (φ : V) := ∃ d < f (ORingStructure.numeral e), Arithmetic.Bootstrapping.Proof T d φ

-- :29
noncomputable def restrictedProvable (fDef : 𝚺₁.Semisentence 2) (e : ℕ) : 𝚷₁.Semisentence 1 := .mkPi “φ. ∀ E, !fDef E !e → ∃ d < E, !(proof T).pi d φ”

-- :31
noncomputable abbrev restrictedProvabilityPred (fDef : 𝚺₁.Semisentence 2) (e : ℕ) (σ : Sentence L) : ArithmeticSentence := (T.restrictedProvable fDef e).val/[⌜σ⌝]

-- :33
instance RestrictedProvable.defined {f : V → V} {fDef : 𝚺₁.Semisentence 2} [𝚺₁-Function₁[V] f via fDef] {e} :
    𝚷₁-Predicate[V] (T.RestrictedProvable f e) via (T.restrictedProvable fDef e) where
  defined {φ} := by simp [Theory.restrictedProvable, Theory.RestrictedProvable];

-- :38  /-- Gödel sentence by restricted provability -/
noncomputable abbrev restrictedGödel (fDef : 𝚺₁.Semisentence 2) (e : ℕ) (T : Theory L) [T.Δ₁] : ArithmeticSentence := fixedpoint (∼(T.restrictedProvable fDef e))

-- :40
private noncomputable abbrev restrictedGödel' (fDef : 𝚺₁.Semisentence 2) (e : ℕ) (T : Theory L) [T.Δ₁] : ArithmeticSentence :=
  ∼(T.restrictedProvable fDef e).val/[⌜restrictedGödel fDef e T⌝]
-- :43
private lemma restrictedGödel'_sigmaOne {fDef : 𝚺₁.Semisentence 2} {e : ℕ} : Hierarchy 𝚺 1 (T.restrictedGödel' fDef e) := by definability;

-- :48 namespace Arithmetic
-- :50 variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
-- :51 variable {T U : ArithmeticTheory} [T.Δ₁]
-- :52 variable {fDef : 𝚺₁.Semisentence 2} {e : ℕ}

-- :54
lemma def_restrictedGödel [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel fDef e 🡘 (∼(T.restrictedProvable fDef e).val)/[⌜T.restrictedGödel fDef e⌝] := diagonal _
-- :56
private lemma def_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel' fDef e 🡘 (∼(T.restrictedProvable fDef e).val)/[⌜T.restrictedGödel fDef e⌝] := by simp;
-- :58
private lemma provable_E_restrictedGödel_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel fDef e 🡘 T.restrictedGödel' fDef e
-- :63
private lemma iff_provable_restrictedGödel_provable_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ (T.restrictedGödel fDef e) ↔ U ⊢ (T.restrictedGödel' fDef e)
-- :66
private lemma iff_true_restrictedGödel_true_restrictedGödel' : ℕ↓[ℒₒᵣ] ⊧ (T.restrictedGödel fDef e) ↔ ℕ↓[ℒₒᵣ] ⊧ (T.restrictedGödel' fDef e)
--   proof: Semantics.models_iff.mp (models_of_provable (T := 𝗜𝚺₁) inferInstance provable_E_restrictedGödel_restrictedGödel')

-- :71
lemma models_restrictedGödel (f : V → V) [𝚺₁-Function₁[V] f via fDef] :
    V↓[ℒₒᵣ] ⊧ T.restrictedGödel fDef e ↔ ∀ x : V, x < f (ORingStructure.numeral e) → ¬Arithmetic.Bootstrapping.Proof T x (⌜T.restrictedGödel fDef e⌝)
-- :76
private lemma models_neg_restrictedGödel (f : V → V) [𝚺₁-Function₁[V] f via fDef] :
    ¬V↓[ℒₒᵣ] ⊧ T.restrictedGödel fDef e ↔ ∃ x : V, x < f (ORingStructure.numeral e) ∧ Arithmetic.Bootstrapping.Proof T x (⌜T.restrictedGödel fDef e⌝)

-- :80 variable [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

-- :83  /- Gödel sentence by restricted provability is true. -/
theorem true_restrictedGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] : ℕ↓[ℒₒᵣ] ⊧ T.restrictedGödel fDef e
--   proof: by_contra; models_neg_restrictedGödel f; ArithmeticTheory.soundOnHierarchy T _ _ ?_ T.restrictedGödel'_sigmaOne;
--          Arithmetic.Bootstrapping.provable_of_standard_proof (T := T) (V := ℕ) (n := e)

-- :94  /- Gödel sentence by restricted provability is provable. -/
theorem provable_restrictedGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] : T ⊢ T.restrictedGödel fDef e
--   proof: iff_provable_...'.mpr; Arithmetic.sigma_one_completeness_iff T.restrictedGödel'_sigmaOne |>.mp; iff_true_...'.mp (true_restrictedGödel f)

-- :100  /-- Lower bound of a Gödel number of proof of restricted Gödel sentence is `f e`. -/
theorem lower_bound_gödelNumber_proof_restrictedGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] :
    ∀ b : T ⊢! T.restrictedGödel fDef e, f (ORingStructure.numeral e) ≤ ⌜b⌝
--   proof: Nat.le_of_not_lt $ (imp_not_comm.mp $ (models_restrictedGödel f).mp (true_restrictedGödel f) ⌜b⌝) $ proof_of_quote_proof b

-- :117
theorem two_pow_le_superexp {e : ℕ} (he : 1 ≤ e) : 2 ^ e ≤ Superexp.superexp e
-- :123 variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
-- :125
theorem provable_restrictedGödel_superexp {e : ℕ} : T ⊢ T.restrictedGödel superexpDef e
-- :128
theorem lower_bound_gödelNumber_proof_restrictedGödel_superexp {e : ℕ} :
    ∀ b : T ⊢! T.restrictedGödel superexpDef e, Superexp.superexp e ≤ ⌜b⌝
```
The bounding-function instance it consumes (`Foundation/FirstOrder/Arithmetic/HFS/Superexp.lean`): `:83 def _root_.FFL.FirstOrder.Arithmetic.superexpDef : 𝚺₁.Semisentence 2 := .mkSigma “y x. !iterExpDef y x x”`; `:86 instance superexp_defined : 𝚺₁-Function₁[V] Superexp.superexp via superexpDef`; `:53 lemma superexp_eq (x : V) : Superexp.superexp x = iterExp x x := rfl`. NOTE: `restrictedProvable` is `𝚷₁` (universal over the bound `E`), so `provable_restrictedGödel` goes through the private Σ₁ twin `restrictedGödel'` — the same trick `arith/ArithS/Bew.lean` copies (`lenGödel'`, `lenGödel'_sigmaOne := by definability`). The `[𝚺₁-Function₁ f via fDef]` needed by `RestrictedProvable.defined` is a `Defined` (specific formula, all `V`), NOT what `computable_iff_sigma1` yields (a parametric `Definable` over ℕ only).

---

## (6) Σ₁/Δ₁-completeness bridges on definability classes

Completeness for sentences:
```lean
-- Foundation/FirstOrder/Arithmetic/R0/Basic.lean:131  (variable {M} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗥₀])
lemma bold_sigma_one_completeness' {n} {σ : ArithmeticSemisentence n} (hσ : Hierarchy 𝚺 1 σ) {bv} :
    σ.Evalb (M := ℕ) bv → σ.Evalb (M := M) (numeral ∘ bv)
-- :141 variable {T : ArithmeticTheory} [𝗥₀ ⪯ T]
-- :143
theorem sigma_one_completeness {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) : ℕ↓[ℒₒᵣ] ⊧ σ → T ⊢ σ
-- :151
theorem sigma_one_completeness_iff [T.SoundOnHierarchy 𝚺 1] {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) : ℕ↓[ℒₒᵣ] ⊧ σ ↔ T ⊢ σ
```
Completeness with numeral parameters (`Foundation/FirstOrder/Arithmetic/Definability/Absoluteness.lean`):
```lean
-- :9
lemma nat_modelsWithParam_iff_models_substs {v : Fin k → ℕ} {φ : ArithmeticSemisentence k} :
    φ.Evalb v ↔ ℕ↓[ℒₒᵣ] ⊧ (φ ⇜ (fun i ↦ Semiterm.Operator.numeral ℒₒᵣ (v i)))
-- :13 variable (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
-- :16
lemma modelsWithParam_iff_models_substs {v : Fin k → ℕ} {φ : ArithmeticSemisentence k} :
    φ.Evalb (M := V) (Nat.cast ∘ v) ↔ V↓[ℒₒᵣ] ⊧ (φ ⇜ (fun i ↦ Semiterm.Operator.numeral ℒₒᵣ (v i)))
-- :20
lemma shigmaZero_absolute {k} (φ : 𝚺₀.Semisentence k) (v : Fin k → ℕ) : φ.val.Evalb v ↔ φ.val.Evalb (M := V) (Nat.cast ∘ v)
-- :35
lemma sigmaOne_upward_absolute {k} (φ : 𝚺₁.Semisentence k) (v : Fin k → ℕ) : φ.val.Evalb v → φ.val.Evalb (M := V) (Nat.cast ∘ v)
-- :40
lemma piOne_downward_absolute {k} (φ : 𝚷₁.Semisentence k) (v : Fin k → ℕ) : φ.val.Evalb (M := V) (Nat.cast ∘ v) → φ.val.Evalb v
-- :45
lemma deltaOne_absolute {k} (φ : 𝚫₁.Semisentence k) (properNat : φ.ProperOn ℕ) (proper : φ.ProperOn V) (v : Fin k → ℕ) :
    φ.val.Evalb v ↔ φ.val.Evalb (M := V) (Nat.cast ∘ v)
-- :51
lemma Defined.shigmaOne_absolute {k} {R : (Fin k → ℕ) → Prop} {R' : (Fin k → V) → Prop} {φ : 𝚫₁.Semisentence k}
    (hR : 𝚫₁.Defined R φ) (hR' : 𝚫₁.Defined R' φ) (v : Fin k → ℕ) : R v ↔ R' (Nat.cast ∘ v)
-- :56
lemma DefinedFunction.shigmaOne_absolute_func {k} {f : (Fin k → ℕ) → ℕ} {f' : (Fin k → V) → V} {φ : 𝚺₁.Semisentence (k + 1)}
    (hf : 𝚺₁.DefinedFunction f φ) (hf' : 𝚺₁.DefinedFunction f' φ) (v : Fin k → ℕ) : (f v : V) = f' (Nat.cast ∘ v)
-- :74
lemma models_iff_of_Delta1 {σ : 𝚫₁.Semisentence n} (hσ : σ.ProperOn ℕ) (hσV : σ.ProperOn V) {e : Fin n → ℕ} :
    σ.val.Evalb (M := V) (Nat.cast ∘ e) ↔ σ.val.Evalb e
-- :85 variable {T : ArithmeticTheory} [𝗣𝗔⁻ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
-- :89
theorem sigma_one_completeness_iff_param {σ : ArithmeticSemisentence n} (hσ : Hierarchy 𝚺 1 σ) {e : Fin n → ℕ} :
    ℕ ⊧/e σ ↔ T ⊢ (σ ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x))
-- :94
lemma models_iff_provable_of_Sigma0_param [V↓[ℒₒᵣ] ⊧* T] {σ : ArithmeticSemisentence n} (hσ : Hierarchy 𝚺 0 σ) {e : Fin n → ℕ} :
    V ⊧/(Nat.cast ∘ e) σ ↔ T ⊢ (σ ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x))
-- :102
lemma models_iff_provable_of_Delta1_param [V↓[ℒₒᵣ] ⊧* T] {σ : 𝚫₁.Semisentence n} (hσ : σ.ProperOn ℕ) (hσV : σ.ProperOn V) {e : Fin n → ℕ} :
    V ⊧/(Nat.cast ∘ e) σ.val ↔ T ⊢ (σ.val ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x))
```
**Recipe from `𝚺₁-Predicate R via φ` (over `V := ℕ`) and `R a` to `T ⊢ φ.val/[a̅]`**:
1. `Defined.iff : φ.val.Evalb v ↔ R v` (`Definability/Definable.lean:189`, simp lemma; needs the instance `[Defined R φ]` at `V := ℕ`).
2. `φ.sigma_prop : Hierarchy 𝚺 1 φ.val` (`Hierarchy.lean:89`; also `hierarchy_sigma` :117, simp).
3. `sigma_one_completeness_iff_param (T := T) φ.sigma_prop (e := ![a]) : ℕ ⊧/![a] φ.val ↔ T ⊢ (φ.val ⇜ fun x ↦ numeral ℒₒᵣ (![a] x))` — needs `[𝗣𝗔⁻ ⪯ T] [T.SoundOnHierarchy 𝚺 1]`; or one-directional `sigma_one_completeness` with `[𝗥₀ ⪯ T]` after `nat_modelsWithParam_iff_models_substs`.
4. To rewrite `φ.val ⇜ fun x ↦ numeral (![a] x)` to `φ.val/[↑a]`: `/[t]` is macro for `⇜ ![t]` (`Foundation/Syntax/Predicate/Rew.lean:887-893`), `↑a : Semiterm` is `Semiterm.numeral a := Operator.numeral L a` (`Basic/Operator.lean:695-697`, `instance : Coe ℕ (Semiterm L ξ n) := ⟨numeral⟩`); the usual `simp [Matrix.constant_eq_singleton, Matrix.fun_eq_vec_one]` closes it (see `rePred_weak_representation` :340-343 and `codeOfComputablePred_provable` :376-384 for the exact simp sets: `simp [models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton]`).
For a `𝚫₁` predicate use `Defined.iff_delta_sigma` (`Definable.lean:195`: `φ.sigma.val.Evalb v ↔ R v`) + `val_sigma` and complete the Σ₁ side; the negative side is `Defined.iff_delta_pi` + `piOne_downward_absolute` / `models_iff_of_Delta1`.

Evaluation lemmas (`Foundation/FirstOrder/Basic/Semantics/Semantics.lean`):
```lean
-- :239
abbrev Evalb [s : Structure L M] (b : Fin n → M) : Semiformula L Empty n →ˡᶜ Prop := Eval b Empty.elim
-- :242
notation:max M:90 " ⊧/" e:max => @Evalb _ M _ _ e
-- :306
lemma eval_rew {n₁ n₂ b₂ f₂} (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) : ...
-- :356
@[simp] lemma eval_substs {k} (w : Fin k → Semiterm L ξ n) (φ : Semiformula L ξ k) :
    Eval b f (φ ⇜ w) ↔ φ.Eval (Semiterm.val b f ∘ w) f
-- :372
@[simp] lemma eval_emb {f : ξ → M} (φ : Semiformula L Empty n) : Eval b f (Rewriting.emb (ξ := ξ) φ : Semiformula L ξ n) ↔ Eval b Empty.elim φ
-- :381
@[simp] lemma eval_embSubsts {ξ} {f : ξ → M} {k} (w : Fin k → Semiterm L ξ n) (σ : Semisentence L k) :
    Eval b f ((@Rew.embSubsts L ξ n k w) ▹ σ) ↔ M ⊧/(Semiterm.val b f ∘ w) σ
```
Substitution (`Foundation/Syntax/Predicate/Rew.lean`): `:853 abbrev subst [Rewriting L ξ F ξ F] (φ : F n₁) (w : Fin n₁ → Semiterm L ξ n₂) : F n₂ := Rew.subst w ▹ φ`; `:856 infix:90 " ⇜ " => FFL.FirstOrder.Rewriting.subst`; `:887-893` the `/[...]` macro (`$φ /[$terms,*] ↦ $φ ⇜ ![$terms,*]`). `Foundation/FirstOrder/Basic/Syntax/Rew.lean:240 lemma coe_subst_eq_subst_coe₁ (φ : Semisentence L 1) (t : ClosedSemiterm L n) : (↑(φ/[t]) : Semiproposition L n) = (↑φ : Semiproposition L 1)/[(↑t : Semiterm L ℕ n)]`.

Numerals: `Basic/Operator.lean:156 def numeral (L : Language) [Operator.Zero L] [Operator.One L] [Operator.Add L] : ℕ → Const L | 0 => Zero.zero | n + 1 => Add.add.foldr One.one (List.replicate n One.one)`; `Arithmetic/Basic/Misc.lean:23 def ORingStructure.numeral : ℕ → α | 0 => 0 | 1 => 1 | n + 2 => numeral (n + 1) + 1`; `:34 @[simp] lemma Nat.numeral_eq : (n : ℕ) → ORingStructure.numeral n = n`; `:138 @[simp] lemma numeral_eq_numeral : (z : ℕ) → (Semiterm.Operator.numeral L z).val ![] = (ORingStructure.numeral z : M)`; `PeanoMinus/Basic.lean:314 lemma numeral_eq_natCast_app : (n : ℕ) → (ORingStructure.numeral n : M) = n`; `:319 lemma numeral_eq_natCast : (ORingStructure.numeral : ℕ → M) = Nat.cast` (M a 𝗣𝗔⁻ model).

Hierarchy under substitution (`Arithmetic/Basic/Hierarchy.lean`): `:258 lemma rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) {φ : Semiformula L ξ₁ n₁} : Hierarchy Γ s φ → Hierarchy Γ s (ω ▹ φ)`; `:266 @[simp] lemma rew_iff {ω} {φ} : Hierarchy Γ s (ω ▹ φ) ↔ Hierarchy Γ s φ`; `:124 lemma mono {Γ} {s s' : ℕ} {φ} (hp : Hierarchy Γ s φ) (h : s ≤ s') : Hierarchy Γ s' φ`. Inductive `Hierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop` at :10-26 (constructors `verum falsum rel nrel and or ball bexs exs all sigma pi dummy_sigma dummy_pi`). The `definability` tactic/attr: `Foundation/FirstOrder/Basic/Definability.lean:499-505` (`macro "definability" : attr`, `macro "definability" (config)? : tactic`).

---

## (7) Modal → arithmetic interpretation: ABSENT at this commit (recoverable from history)

No file in the pinned tree matches `Realization|arithmetical|Solovay` except unrelated docstrings (`Arithmetic/Prenex.lean:8`, `Incompleteness/Definability.lean:7`). Removed by `947950e8` (2026-07-02, "refactor: Remove ProvabilityLogic (#829)") and `1defcb8a` (2026-07-22, "Remove Modal Logic ... (#852)"). Files that existed at `947950e8^`: `Foundation/ProvabilityLogic/{Arithmetic, Realization, SolovaySentences, GL/Soundness, GL/Completeness, GL/Uniform, GL/Unprovability, Grz/Completeness, N/Soundness, S/Soundness, S/Completeness, Classification/*}.lean`. Verbatim from `git show 947950e8^:Foundation/ProvabilityLogic/Realization.lean` (old namespace `LO`, depends on the removed `Foundation.Modal.Hilbert.Normal.Basic`):

```lean
-- Realization.lean:13  variable {L : Language} [L.ReferenceableBy L] {T₀ T U : Theory L}
-- :18
structure Realization (𝔅 : Provability T₀ T) where
  val : ℕ → FirstOrder.Sentence L
-- :21
abbrev _root_.LO.FirstOrder.ArithmeticTheory.StandardRealization (T : ArithmeticTheory) [T.Δ₁] := Realization T.standardProvability
-- :28
@[coe] def interpret {𝔅 : Provability T₀ T} (f : Realization 𝔅) : Formula ℕ → FirstOrder.Sentence L
  | .atom a => f.val a
  |      □φ => 𝔅 (f.interpret φ)
  |       ⊥ => ⊥
  |   φ 🡒 ψ => (f.interpret φ) 🡒 (f.interpret ψ)
-- :60-70 simp lemmas def_atom/def_imp/def_bot/def_box, def_boxItr (n : ℕ) : f (□^[n] A) = 𝔅^[n] (f A)
-- :88-209 iff_provable_imp/box/boxItr/neg/or/and/lconj/fconj/boxdot  (U ⊢ f (A 🡒 B) ↔ U ⊢ (f A) 🡒 (f B), U ⊢ f (□A) ↔ U ⊢ 𝔅 (f A), ...)
-- :218-237 models lemmas: M ⊧ₘ f (□A) ↔ M ⊧ₘ 𝔅 (f A) etc.
```
```lean
-- GL/Soundness.lean:16
variable {L : FirstOrder.Language} [L.ReferenceableBy L] [L.DecidableEq]
         {T U : FirstOrder.Theory L} [Diagonalization T]  [T ⪯ U]
         {𝔅 : Provability T U} [𝔅.HBL]
-- :21
lemma GL.arithmetical_soundness (h : Modal.GL ⊢ A) {f : Realization 𝔅} : U ⊢ f A := by
  induction h using Hilbert.Normal.rec! with
  | axm _ hp =>
    rcases hp with (⟨_, rfl⟩ | ⟨_, rfl⟩)
    . exact WeakerThan.pbl $ 𝔅.D2;
    . exact WeakerThan.pbl $ formalized_löb_theorem;
  | nec ihp => exact WeakerThan.pbl $ 𝔅.D1 ihp;
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | _ => dsimp [Realization.interpret]; cl_prover;
-- :33
theorem GLPlusBoxBot.arithmetical_soundness (hA : Modal.GLPlusBoxBot 𝔅.height ⊢ A) (f : Realization 𝔅) : U ⊢ f A
```
What survives in the pinned tree and is exactly what that soundness proof consumed: `Provability`, `HBL`, `D1/D2/D3`, `formalized_löb_theorem`, `Diagonalization`, `Height` (§4) — all present. So a bounded-GL translation can be written directly against `ProvabilityAbstraction` without the modal package: define an interpretation of the engine's `Formula`/`Pf` into `Sentence ℒₒᵣ` with `.box` ↦ some `Provability`-shaped predicate and discharge each `Pf` constructor by the corresponding abstract lemma (D2 ↦ `HBL2.D2`, nec ↦ `D1`, Löb ↦ `formalized_löb_theorem`). Caveat: `Provability.prov : Semisentence L₀ 1` is UNindexed by budget; a budget-indexed `□_k` is a family `k ↦ Provability 𝗜𝚺₁ T` (as `restrictedProvable fDef e` is a family in `e`), and `bew_def`(D1) for a bounded predicate is not free — it needs the proof-length estimate (this is what `ArithS.Proper`/`LenProvable` is for).

---

## (8) Definability API summary

`Foundation/FirstOrder/Arithmetic/Definability/Hierarchy.lean`:
```lean
-- :21
structure HierarchySymbol where Γ : SigmaPiDelta ; rank : ℕ
-- :26  scoped notation:max Γ:max "-[" n "]" => HierarchySymbol.mk Γ n
-- :28-50  abbrev sigmaZero := 𝚺-[0] ... ; notation "𝚺₁" => HierarchySymbol.sigmaOne ; "𝚷₁" ; "𝚫₁" ; "𝚺₀" "𝚷₀" "𝚫₀"
-- :55
protected inductive Semiformula : HierarchySymbol → Type _ where
  | mkSigma {m} (φ : ArithmeticSemiformula ξ n) (hφ : Hierarchy 𝚺 m φ := by simp) : 𝚺-[m].Semiformula
  | mkPi {m} (φ : ArithmeticSemiformula ξ n) (hφ : Hierarchy 𝚷 m φ := by simp) : 𝚷-[m].Semiformula
  | mkDelta {m} : 𝚺-[m].Semiformula → 𝚷-[m].Semiformula → 𝚫-[m].Semiformula
-- :60
protected abbrev Semisentence (Γ : HierarchySymbol) (n : ℕ) := Γ.Semiformula Empty n
-- :62
protected abbrev Sentence (Γ : HierarchySymbol) := Γ.Semiformula Empty 0
-- :70
@[coe] def val {Γ : HierarchySymbol} : Γ.Semiformula ξ n → ArithmeticSemiformula ξ n
  | mkSigma φ _ => φ | mkPi φ _ => φ | mkDelta φ _ => φ.val
-- :75,77,79
@[simp] lemma val_mkSigma (φ : ArithmeticSemiformula ξ n) (hp : Hierarchy 𝚺 m φ) : (mkSigma φ hp).val = φ := rfl
@[simp] lemma val_mkPi ... ; @[simp] lemma val_mkDelta (φ : 𝚺-[m].Semiformula ξ n) (ψ : 𝚷-[m].Semiformula ξ n) : (mkDelta φ ψ).val = φ.val := rfl
-- :81-86  instance : Coe (𝚺₁.Semisentence n) (ArithmeticSemisentence n) := ⟨Semiformula.val⟩ (and 𝚷₁, 𝚫₁, 𝚺₀, 𝚷₀, 𝚫₀)
-- :89
@[simp] lemma sigma_prop : (φ : 𝚺-[m].Semiformula ξ n) → Hierarchy 𝚺 m φ.val
-- :92
@[simp] lemma pi_prop : (φ : 𝚷-[m].Semiformula ξ n) → Hierarchy 𝚷 m φ.val
-- :99,:104
def sigma : 𝚫-[m].Semiformula ξ n → 𝚺-[m].Semiformula ξ n ; def pi : 𝚫-[m].Semiformula ξ n → 𝚷-[m].Semiformula ξ n
-- :109
lemma val_sigma (φ : 𝚫-[m].Semiformula ξ n) : φ.sigma.val = φ.val
-- :117,:119
@[simp] lemma hierarchy_sigma (φ : 𝚺-[m].Semiformula ξ n) : Hierarchy 𝚺 m φ.val ; hierarchy_pi
-- :132
def ProperOn (φ : 𝚫-[m].Semisentence n) : Prop := ∀ (e : Fin n → M), φ.sigma.val.Evalb e ↔ φ.pi.val.Evalb e
-- :138
def ProvablyProperOn (φ : 𝚫-[m].Semisentence n) (T : ArithmeticTheory) : Prop := T ⊢ ∀¹* “!φ.sigma.val ⋯ ↔ !φ.pi.val ⋯”
-- :273,:275
def all (φ : 𝚷-[m + 1].Semiformula ξ (n + 1)) : 𝚷-[m + 1].Semiformula ξ n ; def exs (φ : 𝚺-[m + 1].Semiformula ξ (n + 1)) : 𝚺-[m + 1].Semiformula ξ n
```
`Foundation/FirstOrder/Arithmetic/Definability/Definable.lean` (namespace `FFL.FirstOrder.Arithmetic.HierarchySymbol`, `{V : Type*} [ORingStructure V]`):
```lean
-- :13
abbrev IsDefinedBy (R : (Fin k → V) → Prop) : {ℌ : HierarchySymbol} → ℌ.Semisentence k → Prop
  | 𝚺-[_], φ => FirstOrder.IsDefinedBy R φ.val
  | 𝚷-[_], φ => FirstOrder.IsDefinedBy R φ.val
  | 𝚫-[_], φ => φ.ProperOn V ∧ FirstOrder.IsDefinedBy R φ.val
-- :24
class Defined (R : outParam ((Fin k → V) → Prop)) {ℌ : HierarchySymbol} (φ : ℌ.Semisentence k) where
  defined : IsDefinedBy R φ
-- :31
class Definable {k} (P : (Fin k → V) → Prop) : Prop where
  definable : ∃ φ : ℌ.Semiformula V k, IsDefinedByWithParam P φ
-- :34-45  abbrev DefinedPred (P : V → Prop) (φ : ℌ.Semisentence 1) := Defined (fun v ↦ P (v 0)) φ ; DefinedRel ; DefinedRel₃ ; DefinedRel₄
-- :48
abbrev DefinedFunction {k} (f : (Fin k → V) → V) (φ : ℌ.Semisentence (k + 1)) : Prop := Defined (fun v ↦ v 0 = f (v ·.succ)) φ
-- :56,:59  abbrev DefinedFunction₁ (f : V → V) (φ : ℌ.Semisentence 2) ; DefinedFunction₂ (f : V → V → V) (φ : ℌ.Semisentence 3)
-- :71-95  abbrev DefinablePred/DefinableRel/…/DefinableFunction (f) := ℌ.Definable (k := k + 1) (fun v ↦ v 0 = f (v ·.succ)) ; DefinableFunction₁ ; ₂
-- :99-170 notations:  Γ "-Predicate " P " via " φ => DefinedPred Γ P φ ; Γ "-Relation " P " via " φ ; Γ "-Function₁ " f " via " φ ; ...
--                    Γ "-Predicate " P => DefinablePred Γ P ; Γ "-Function₁ " f => DefinableFunction₁ Γ f ; with "[" V "]" variants
-- :181
lemma Defined.df {R} {φ : ℌ.Semisentence k} (h : Defined R φ) : FirstOrder.IsDefinedBy R φ.val
-- :186
@[simp] lemma Defined.proper {R} {m} {φ : 𝚫-[m].Semisentence k} [h : Defined R φ] : φ.ProperOn V
-- :189
@[simp] lemma Defined.iff {R} {φ : ℌ.Semisentence k} [h : Defined R φ] : φ.val.Evalb v ↔ R v
-- :192,:195  iff_delta_pi : φ.pi.val.Evalb v ↔ R v ; iff_delta_sigma : φ.sigma.val.Evalb v ↔ R v   (φ : 𝚫-[m].Semisentence k)
-- :199  lemma Defined.of_zero ; :205 lemma Defined.of_iff (h : ∀ x, P x ↔ Q x) (H : Defined Q φ) : Defined P φ
-- :208
lemma Defined.to_definable (φ : ℌ.Semisentence k) (hP : Defined P φ) : ℌ.Definable P
-- :224  lemma DefinedFunction.of_eq ; :227 lemma DefinedFunction.graph_delta {φ : 𝚺-[m].Semisentence (k + 1)} (h : DefinedFunction f φ) : DefinedFunction f φ.graphDelta
```
`Foundation/FirstOrder/Basic/Definability.lean:19 abbrev IsDefinedBy (R : (Fin k → M) → Prop) (φ : Semisentence L k) : Prop := ∀ v, φ.Evalb v ↔ R v`.

**Building `Sentence ℒₒᵣ` from `σ : 𝚺₁.Semisentence n` + numerals with `ℕ ⊧ · ↔ R a`**: the sentence is `σ.val ⇜ fun i ↦ Semiterm.Operator.numeral ℒₒᵣ (a i)` (or `σ.val/[↑a₀, ↑a₁, …]`); truth in ℕ: `nat_modelsWithParam_iff_models_substs : σ.val.Evalb a ↔ ℕ↓[ℒₒᵣ] ⊧ (σ.val ⇜ fun i ↦ numeral ℒₒᵣ (a i))` (Absoluteness.lean:9) composed with `Defined.iff`; provability: `sigma_one_completeness_iff_param σ.sigma_prop` (Absoluteness.lean:89). A `𝚺₁.Sentence` wrapper exists too: `.mkSigma (σ.val/[…]) (by simp)` pattern — e.g. `provabilityPred' T σ : 𝚺₁.Sentence := .mkSigma “!(provable T) !!(⌜σ⌝)”` (Proof/Basic.lean:493) with `provabilityPred'_val` (:498; note comment "Proving this by `rfl` overflows memory on Lean v4.33.1", proven by `unfold; simp only [val_mkSigma]`).

Gödel-number terms: `Basic/Operator.lean:111 class GödelNumber (L : Language) (α : Type*) where gödelNumber : α → Semiterm.Const L`; `:221 abbrev gödelNumber' (a : α) : Semiterm L ξ n := const (gödelNumber a)`; `:223 instance : GödelQuote α (Semiterm L ξ n) := ⟨gödelNumber'⟩`; `:225 abbrev ofEncodable [Operator.Zero L] [Operator.One L] [Operator.Add L] {α} [Encodable α] : GödelNumber L α := ⟨Operator.encode L⟩`; `Arithmetic/Basic/Misc.lean:103 instance {α} [Encodable α] : Semiterm.Operator.GödelNumber ℒₒᵣ α := ...ofEncodable` (this gives `ℒₒᵣ.ReferenceableBy ℒₒᵣ` and `L.ReferenceableBy ℒₒᵣ` for any encodable `Sentence L`); `:112 lemma gödelNumber'_eq_coe_encode (a : α) : (⌜a⌝ : ArithmeticSemiterm ξ n) = ↑(Encodable.encode a) := rfl`; `:117 @[simp] lemma rew_gödelNumber' (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) (a : α) : ω ⌜a⌝ = ⌜a⌝`. `Vorspiel/NotationClass.lean:115 class GödelQuote (α β : Sort*) where quote : α → β`, `:118 notation:max "⌜" x "⌝" => GödelQuote.quote x`. Element-level quote into a model `V`: `Bootstrapping/Syntax/Formula/Coding.lean:289 noncomputable instance : GödelQuote (Semisentence L n) V where quote σ := ⌜(Rewriting.emb σ : Semiproposition L n)⌝`; `:292 lemma quote_def`; `:303 lemma quote_eq_encode (σ : Semisentence L n) : (⌜σ⌝ : V) = ↑(encode σ)`; `:304 lemma coe_quote_eq_quote (σ) : (↑(⌜σ⌝ : ℕ) : V) = ⌜σ⌝`; `:307 lemma quote_eq_encode_nat (σ) : (⌜σ⌝ : ℕ) = encode σ`; `:312 @[simp] lemma val_quote {bv : Fin m → V} {fv : ξ → V} (σ : Semisentence L n) : (⌜σ⌝ : ArithmeticSemiterm ξ m).val bv fv = ⌜σ⌝` (term-quote evaluates to element-quote — the lemma that connects `prov/[⌜σ⌝]` to `Provable T ⌜σ⌝`); `:315 @[simp] lemma coe_quote (σ) : ↑(⌜σ⌝ : ℕ) = (⌜σ⌝ : ArithmeticSemiterm ξ m)`; `:322 @[simp] lemma quote_inj_iff : (⌜σ₁⌝ : V) = ⌜σ₂⌝ ↔ σ₁ = σ₂`.

Cross-reference: the project's `arith/ArithS/Bew.lean` (`/Users/colomband/Library/CloudStorage/OneDrive-Personal/Documents/Studies/ETH/Master Thesis/workspace/open-source-game-theory/arith/ArithS/Bew.lean`) already mirrors §5 one-to-one (`LenProvable f k T φ := ∃ d < f (numeral k), Proof T d φ ∧ dlen T d ≤ numeral k`, `lenProvable : 𝚷₁.Semisentence 1`, `lenProvabilityPred`, `LenProvable.defined` with `[𝚺₁-Function₁[V] f via fDef]`, `lenGödel := fixedpoint (∼(lenProvable T fDef k))`, private Σ₁ twin `lenGödel'` with `by definability`).