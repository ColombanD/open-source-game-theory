# READ: Foundation's calculus, coded derivations, provability abstraction, fixed points, Σ₁-completeness — what the bounded-HBL design depends on

Verbatim reader report. Source: `/Users/colomband/wt/arith-lake/packages/Foundation` at commit
`58c76ac8b26cfda45d0d5430511750489d39b25a` (Lean v4.33.1; namespace root `FFL`). File paths below are
relative to `Foundation/` inside that package. Paragraphs marked **ANALYSIS** are mine; everything else is
quoted or paraphrased with `file:line`.

Target of the next milestone (restated for reference; the ArithS side is only summarised in §0):
`LenProvable f k T φ := ∃ d < f k, Proof T d φ ∧ dlen T d ≤ k`, bounded HBL conditions in parametric form
(budget a free variable inside PA sentences), and a parametric bounded Löb theorem.

---

## 0. What ArithS already bridges (orientation only; another reader covers it in detail)

`/Users/colomband/wt/osgt-arith-m3/arith/ArithS/`:

- `Bew.lean:35` — `def LenProvable (f : V → V) (k : ℕ) (T : Theory L) [T.Δ₁] (φ : V) : Prop := ∃ d < f (ORingStructure.numeral k), Proof T d φ ∧ dlen T d ≤ ORingStructure.numeral k`; `lenProvable … : 𝚷₁.Semisentence 1` (:40); `LenProvable.mono` (:53), `LenProvable.provable` (:60); the length-Gödel sentence `lenGödel` and `lower_bound_dlen_proof_lenGödel` (:170), modelled 1:1 on Foundation's `RestrictedProvability.lean` (§3.4 below).
- `BewV.lean:23` — `def LenProvableV (k φ : V) : Prop := ∃ d < fbound k, Proof T d φ ∧ dlen T d ≤ k` with the **Δ₁** definition `lenProvableV : 𝚫₁.Semisentence 2` (:25-28) and `lenProvableV_numeral` (:43). This is the budget-as-object-variable predicate the parametric box needs.
- `MetaLength.lean` — `tlen`/`flen` (meta symbol counts, :27/:66), `termLen_quote`/`formulaLen_quote` (:51/:76), `setLen_quote` (:161), `sqlen`, `mlen : T ⟹₂ Γ → ℕ` (:184), `derivation_quote : Derivation T (⌜d⌝ : ℕ)` (:197), `dlen_quote : dlen T (⌜d⌝ : ℕ) = mlen d` (:201).
- `Sound.lean:25` — `theorem Derivation.sound' {d : ℕ} (h : Derivation T d) : ∃ Γ : Finset (Proposition L), ∃ b : T ⟹₂ Γ, (⌜b⌝ : ℕ) = d` (code-for-code strengthening of Foundation's `Derivation.sound`) and `Proof.sound'` (:118).
- `Cut.lean` — bounded D2 in rule form: `cutMP` (:111), `mlen_cutMP` (:120), `lenProvable_mp` (:234), `lenProvable_fbound_mono` (:151), `lenProvable_of_derivation` (:164), `derivation_of_lenProvable` (:179).

So: `Derivation2`, `typedQuote`, `Proof`, `Derivation.sound`, `RestrictedProvable`, `mlen`/`dlen` are already bridged. What is NOT yet bridged is anything that produces a **PA-derivation with a length bound of a sentence about codes** (bounded D1/D3) or a **parametric** box.

---

## 1. The proof calculus (`FirstOrder/Basic/Calculus.lean`, `Calculus2.lean`, `Logic/Calculus.lean`, `Logic/Entailment.lean`, `Propositional/Entailment/*`)

### 1.1 Sequents and the one-sided LK derivation (`Basic/Calculus.lean`)

Sequents are **multisets** (not lists) in this Foundation version:

```
Calculus.lean:19   abbrev Sequent (L : Language) := Multiset (Proposition L)
Calculus.lean:25   def newVar (Γ : Sequent L) : ℕ := (Γ.map Semiformula.fvSup).foldr max 0
Calculus.lean:42   def IsClosed (Γ : Sequent L) : Prop := ∃ φ ∈ Γ, ∼φ ∈ Γ
Calculus.lean:44   def embed (Γ : Multiset (Sentence L)) : Sequent L := Γ.map Rewriting.emb
```

The derivation type, verbatim (`Calculus.lean:61-73`):

```lean
/-- Derivation for $\mathbf{LK}$ -/
inductive Derivation : Sequent L → Type _
| identity (r : L.Rel k) (v) : Derivation ⦃.rel r v, .nrel r v⦄
| cut : Derivation (Γ + ⦃φ⦄) → Derivation (Δ + ⦃∼φ⦄) → Derivation (Γ + Δ)
| contraction : Derivation Δ → Δ ⊆ Γ → Derivation Γ
| verum : Derivation ⦃⊤⦄
| or : Derivation (Γ + ⦃φ, ψ⦄) → Derivation (Γ + ⦃φ ⋎ ψ⦄)
| and : Derivation (Γ + ⦃φ⦄) → Derivation (Γ + ⦃ψ⦄) →
    Derivation (Γ + ⦃φ ⋏ ψ⦄)
| all : Derivation (Γ⁺ + ⦃φ.free⦄) → Derivation (Γ + ⦃∀¹ φ⦄)
| exs : Derivation (Γ + ⦃φ/[t]⦄) → Derivation (Γ + ⦃∃¹ φ⦄)

prefix:45 "⊢ᴸᴷ¹ " => Derivation
```

Note: there is no `axL`/`wk`/`root`/`axm` in `Derivation`; the identity axiom is on **atoms** only, weakening is `contraction : Derivation Δ → Δ ⊆ Γ → Derivation Γ` (multiset-subset, so it is weakening+contraction+exchange in one rule), and there is no theory-axiom rule (theories enter through `Theory.Proof`, §1.3).

Height (the only size notion on `Derivation`), `Calculus.lean:79-87`:

```lean
def height {Δ : Sequent L} : ⊢ᴸᴷ¹ Δ → ℕ
  |    identity _ _ => 0
  |       cut dp dn => max dp.height dn.height + 1
  | contraction d _ => d.height + 1
  |           verum => 0
  |            or d => d.height + 1
  |       and dp dq => max (height dp) (height dq) + 1
  |           all d => d.height + 1
  |           exs d => d.height + 1
```

with `@[simp]` equations `height_id … height_exs` (:91-112) and `height_cast` (:118).

Structural helpers (all **defs**, i.e. proof-object constructions):

```
Calculus.lean:116  abbrev cast (d : ⊢ᴸᴷ¹ Δ) (e : Δ = Γ := by abel) : ⊢ᴸᴷ¹ Γ := e ▸ d
Calculus.lean:121  def contra (d : ⊢ᴸᴷ¹ Δ) (h : Δ ⊆ Γ := by simp) : ⊢ᴸᴷ¹ Γ := contraction d h
Calculus.lean:123  def top (h : ⊤ ∈ Δ := by simp) : ⊢ᴸᴷ¹ Δ := verum.contraction (by simpa using h)
Calculus.lean:125  def identity' (r : L.Rel k) (v) (hpos : Semiformula.rel r v ∈ Δ := by simp)
                       (hneg : Semiformula.nrel r v ∈ Δ := by simp) : ⊢ᴸᴷ¹ Δ
Calculus.lean:131  def tensor {φ ψ} (dφ : ⊢ᴸᴷ¹ Γ + ⦃φ⦄) (dψ : ⊢ᴸᴷ¹ Δ + ⦃ψ⦄) : ⊢ᴸᴷ¹ Γ + Δ + ⦃φ ⋏ ψ⦄
Calculus.lean:137  def eta : (φ : Proposition L) → ⊢ᴸᴷ¹ ⦃φ, ∼φ⦄     -- cut-free identity on any formula,
                     … termination_by φ => φ.complexity             -- by recursion on complexity (:158)
Calculus.lean:174  def rewrite {Γ} (f : ℕ → SyntacticTerm L) : ⊢ᴸᴷ¹ Γ → ⊢ᴸᴷ¹ Γ.map (Rew.rewrite f ▹ ·)
Calculus.lean:204  protected def map {Δ : Sequent L} (d : ⊢ᴸᴷ¹ Δ) (f : ℕ → ℕ) : ⊢ᴸᴷ¹ Δ.map (Rew.rewriteMap f ▹ ·)
Calculus.lean:207  protected def shift {Δ : Sequent L} (d : ⊢ᴸᴷ¹ Δ) : ⊢ᴸᴷ¹ Δ⁺
Calculus.lean:218  def lMap (Φ : L₁ →ᵥ L₂) {Γ} : ⊢ᴸᴷ¹ Γ → ⊢ᴸᴷ¹ Γ.map (.lMap Φ)
Calculus.lean:261  def generalizeByNewVar {φ : Semiproposition L 1} (hp : ¬φ.FVar? m)
                       (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m) (d : ⊢ᴸᴷ¹ Δ + ⦃φ/[&m]⦄) : ⊢ᴸᴷ¹ Δ + ⦃∀¹ φ⦄
Calculus.lean:269  def exOfInstances (v : List (SyntacticTerm L)) (φ : Semiproposition L 1)
                       (h : ⊢ᴸᴷ¹ (v.map (φ/[·]) : Multiset _) + Γ) : ⊢ᴸᴷ¹ Γ + ⦃∃¹ φ⦄
Calculus.lean:289  def allNvar {Δ : Sequent L} {φ} (h : ∀¹ φ ∈ Δ) : ⊢ᴸᴷ¹ Δ + ⦃φ/[&Δ.newVar]⦄ → ⊢ᴸᴷ¹ Δ
```

`Calculus.lean:160-168` registers `Derivation` as an instance of the abstract `OneSidedLK` and `OneSidedLK.Cut` classes (§1.4); `:170 lemma of_isClosed {Γ : Sequent L} (h : Γ.IsClosed) : Nonempty (⊢ᴸᴷ¹ Γ)`.

### 1.2 The pure-logic system `𝐋𝐊¹` (`Calculus.lean:302-353`)

```
Calculus.lean:304  inductive LK (L : Language) | symbol
Calculus.lean:311  abbrev LK.Proof (φ : Proposition L) := ⊢ᴸᴷ¹ ⦃φ⦄
Calculus.lean:313  instance : Entailment (LK L) (Proposition L) where Prf _ := LK.Proof
Calculus.lean:318  lemma def_eq (φ : Proposition L) : (𝐋𝐊¹ ⊢! φ) = (⊢ᴸᴷ¹ ⦃φ⦄) := rfl
Calculus.lean:320  lemma provable_def (φ : Proposition L) : 𝐋𝐊¹ ⊢ φ ↔ Nonempty (⊢ᴸᴷ¹ ⦃φ⦄) := by rfl
Calculus.lean:330  instance classical : Entailment.Cl (𝐋𝐊¹ : LK L) := inferInstance
Calculus.lean:332  lemma all (φ : Semiproposition L 1) : 𝐋𝐊¹ ⊢ φ.free → 𝐋𝐊¹ ⊢ ∀¹ φ
Calculus.lean:343  lemma univCl' {φ : Proposition L} (b : 𝐋𝐊¹ ⊢ φ) : 𝐋𝐊¹ ⊢ φ.univCl'
```

### 1.3 Theory proofs `T ⊢! φ` / `T ⊢ φ` (`Calculus.lean:355-518`)

```lean
Calculus.lean:355
structure Theory.Proof (T : Theory L) (σ : Sentence L) where
  axioms : Multiset (Sentence L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
  derivation : OneSidedLK.Pullback Derivation Rewriting.emb (⦃σ⦄ + ∼axioms)

Calculus.lean:362  instance : Entailment (Theory L) (Sentence L) where Prf := Theory.Proof
```

So `T ⊢! σ` (the TYPE) is a finite multiset of axioms plus an LK derivation of `σ, ¬axioms` (embedded to propositions), and `T ⊢ σ := Nonempty (T ⊢! σ)` (`Logic/Entailment.lean:48,53`).

```
Calculus.lean:370  def ofDerivation {T : Theory L} {φ : Sentence L}
                       (d : OneSidedLK.Pullback Derivation Rewriting.emb ⦃φ⦄) : T ⊢! φ := ⟨0, by simp, OneSidedLK.cast d⟩
Calculus.lean:374  instance : Entailment.Compact (Theory L)             -- core b := {φ | φ ∈ b.axioms}
Calculus.lean:380  instance (T : Theory L) : Entailment.ModusPonens T where
                     mdp! {φ ψ} bi bp := ⟨bi.axioms + bp.axioms, …, OneSidedLK.cast (OneSidedLK.modusPonens … bi.derivation … bp.derivation) …⟩
Calculus.lean:388  instance : Entailment.Cl T := OneSidedLK.AxiomDerivation.cl T ofDerivation
Calculus.lean:390  instance : Entailment.Axiomatized (Theory L) where
                     prfAxm {𝓢 φ} h := ⟨⦃φ⦄, …, … Derivation.eta (Rewriting.emb φ)⟩
                     weakening {𝓢 𝓣 φ} h b := ⟨b.axioms, fun ψ hψ ↦ h (b.axioms_mem ψ hψ), b.derivation⟩
Calculus.lean:398  /-- Replaces each used axiom by its proof in another theory. … -/
Calculus.lean:400  noncomputable def cut {U : Theory L} (h : T ⊢!* U) (b : U ⊢! φ) : T ⊢! φ     -- list recursion + mdp!
Calculus.lean:419  noncomputable instance : Entailment.StrongCut (Theory L) (Theory L) := ⟨cut⟩
Calculus.lean:421  instance : Entailment.DeductiveExplosion (Theory L)
Calculus.lean:428  lemma weakerThan_of_le {T U : Theory L} (h : T ⊆ U) : T ⪯ U
Calculus.lean:435  lemma provable_iff : T ⊢ φ ↔ ∃ Γ : Multiset (Sentence L), (∀ ψ ∈ Γ, ψ ∈ T) ∧
                       Nonempty (⊢ᴸᴷ¹ ⦃(φ : Proposition L)⦄ + ∼Sequent.embed Γ)
Calculus.lean:445  lemma inconsistent_iff : Entailment.Inconsistent T ↔ ∃ Γ …, Nonempty (⊢ᴸᴷ¹ ∼Sequent.embed Γ)
Calculus.lean:459  @[simp] lemma empty_provable_iff_eprovable : (∅ : Theory L) ⊢ φ ↔ 𝐋𝐊¹ ⊢ (φ : Proposition L)
Calculus.lean:475  lemma of_LK_provable {T : Theory L} {φ : Sentence L} : 𝐋𝐊¹ ⊢ (φ : Proposition L) → T ⊢ φ
Calculus.lean:481  lemma specialize {T : Theory L} (φ : Semisentence L 1) (t : ClosedTerm L) :
                       T ⊢ ∀¹ φ 🡒 Semiformula.subst φ ![t]
                     -- proof BUILDS the derivation: Derivation.or … (Derivation.exs … (Derivation.eta …)) (:484-493)
Calculus.lean:496  noncomputable instance : Entailment.Deduction (Theory L)   -- ofInsert filters the axiom multiset
Calculus.lean:522  def Theory.theory (T : Theory L) : Theory L := {σ | T ⊢ σ}
```

### 1.4 The abstract one-sided calculus (`Logic/Calculus.lean`)

```lean
Logic/Calculus.lean:22
class OneSidedLK {F : Type*} [LogicalConnective F] [LogicalNeutral F]
    [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F] (𝔇 : Multiset F → Type*) where
  identity (φ) : 𝔇 ⦃φ, ∼φ⦄
  contraction : 𝔇 Δ → Δ ⊆ Γ → 𝔇 Γ
  verum : 𝔇 ⦃⊤⦄
  and : 𝔇 (Γ + ⦃φ⦄) → 𝔇 (Γ + ⦃ψ⦄) → 𝔇 (Γ + ⦃φ ⋏ ψ⦄)
  or : 𝔇 (Γ + ⦃φ, ψ⦄) → 𝔇 (Γ + ⦃φ ⋎ ψ⦄)

Logic/Calculus.lean:30
class OneSidedLK.Cut … (𝔇 : Multiset F → Type*) extends OneSidedLK 𝔇 where
  cut : 𝔇 (Γ + ⦃φ⦄) → 𝔇 (Δ + ⦃∼φ⦄) → 𝔇 (Γ + Δ)
```

Derived constructions (defs): `cast` (:41), `contra` (:43), `close` (:45), `top` (:50), `tensor` (:52), `eCut` (:60), `removeBot` (:65), and the routine modus ponens as two cuts:

```lean
Logic/Calculus.lean:70
def modusPonens [Cut 𝔇] (di : 𝔇 (Γ + ⦃φ 🡒 ψ⦄)) (dp : 𝔇 (Δ + ⦃φ⦄)) :
    𝔇 (Γ + Δ + ⦃ψ⦄) :=
  have h₁ : 𝔇 ⦃∼(φ 🡒 ψ), ∼φ, ψ⦄ := cast (tensor … (cast (identity φ) …) (cast (identity (∼ψ)) …)) …
  have h₂ : 𝔇 (Γ + ⦃∼φ, ψ⦄) := cast <| cut (φ := φ 🡒 ψ) (Γ := Γ) (Δ := ⦃∼φ, ψ⦄) di (cast h₁)
  cast <| cut (φ := φ) (Γ := Δ) (Δ := Γ + ⦃ψ⦄) dp (cast h₂)
```

`disj₂` (:80), `conj₂` (:96); `AxiomDerivation.{introOr, introDisj, negEquiv, implyK, implyS, and₁, and₂, and₃, or₁, or₂, or₃, dne}` (:105-194) are the explicit rule expansions of the Hilbert axioms; `abbrev AxiomDerivation.cl … (lift : ∀ {φ}, 𝔇 ⦃φ⦄ → 𝓟 ⊢! φ) : Entailment.Cl 𝓟` (:201-226) turns them into a classical entailment; `class PrincipalEntailment (𝔇) (𝓟) where equiv {φ} : 𝓟 ⊢! φ ≃ 𝔇 ⦃φ⦄` (:229-230); `abbrev Pullback (𝔇) (f : G →ˡᶜ F) : Multiset G → Type _ := fun Γ ↦ 𝔇 (Γ.map f)` (:264-265) with `OneSidedLK`/`Cut` instances (:278-290).

### 1.5 The `Entailment` layer (`Logic/Entailment.lean`, `Propositional/Entailment/Minimal.lean`, `Cl.lean`)

```
Logic/Entailment.lean:34   class Entailment (S : Type*) (F : outParam Type*) where Prf : S → F → Type*
Logic/Entailment.lean:37   infix:45 " ⊢! " => Entailment.Prf
Logic/Entailment.lean:48   def Provable (φ : F) : Prop := Nonempty (𝓢 ⊢! φ)
Logic/Entailment.lean:51   abbrev Unprovable (φ : F) : Prop := ¬Provable 𝓢 φ
Logic/Entailment.lean:53   infix:45 " ⊢ " => Provable
Logic/Entailment.lean:55   infix:45 " ⊬ " => Unprovable
Logic/Entailment.lean:58   def PrfSet (s : Set F) : Type _ := ⦃φ : F⦄ → φ ∈ s → 𝓢 ⊢! φ      -- ⊢!*
Logic/Entailment.lean:61   def ProvableSet (s : Set F) : Prop := ∀ {φ}, φ ∈ s → 𝓢 ⊢ φ         -- ⊢*
Logic/Entailment.lean:72   def cast {𝓢 : S} {φ ψ : F} (b : 𝓢 ⊢! φ) (e : φ = ψ := by simp) : 𝓢 ⊢! ψ := e ▸ b
Logic/Entailment.lean:79   noncomputable def Provable.get {𝓢 : S} {φ : F} (h : 𝓢 ⊢ φ) : 𝓢 ⊢! φ := Classical.choice h
Logic/Entailment.lean:90   class WeakerThan (𝓢 : S) (𝓣 : T) : Prop where subset : theory 𝓢 ⊆ theory 𝓣
Logic/Entailment.lean:93   infix:40 " ⪯ " => WeakerThan
Logic/Entailment.lean:116  lemma WeakerThan.wk (h : 𝓢 ⪯ 𝓣) {φ} : 𝓢 ⊢ φ → 𝓣 ⊢ φ
Logic/Entailment.lean:118  lemma WeakerThan.pbl [h : 𝓢 ⪯ 𝓣] {φ} : 𝓢 ⊢ φ → 𝓣 ⊢ φ
Logic/Entailment.lean:125  lemma weakerThan_iff : 𝓢 ⪯ 𝓣 ↔ (∀ {φ}, 𝓢 ⊢ φ → 𝓣 ⊢ φ)
Logic/Entailment.lean:232  def Inconsistent (𝓢 : S) : Prop := ∀ φ, 𝓢 ⊢ φ
Logic/Entailment.lean:234  class Consistent (𝓢 : S) : Prop where not_inconsistent : ¬Inconsistent 𝓢
Logic/Entailment.lean:277  class DeductiveExplosion [LogicalNeutral F] where dexp {𝓢 : S} : 𝓢 ⊢! ⊥ → (φ : F) → 𝓢 ⊢! φ
Logic/Entailment.lean:354  class Axiomatized [AdjunctiveSet F S] where
                             prfAxm {𝓢 : S} : 𝓢 ⊢!* AdjunctiveSet.set 𝓢
                             weakening {𝓢 𝓣 : S} : 𝓢 ⊆ 𝓣 → 𝓢 ⊢! φ → 𝓣 ⊢! φ
Logic/Entailment.lean:360  class StrongCut [AdjunctiveSet F T] where
                             cut {𝓢 : S} {𝓣 : T} {φ} : 𝓢 ⊢!* AdjunctiveSet.set 𝓣 → 𝓣 ⊢! φ → 𝓢 ⊢! φ
Logic/Entailment.lean:371  def byAxm {𝓢 : S} (h : φ ∈ 𝓢) : 𝓢 ⊢! φ := prfAxm (by simp [h])
Logic/Entailment.lean:431  class Compact [AdjunctiveSet F S] where core … corePrf … core_subset … core_finite …
Logic/Entailment.lean:478  class Deduction [Adjoin F S] where
                             ofInsert {φ ψ : F} {𝓢 : S} : adjoin φ 𝓢 ⊢! ψ → 𝓢 ⊢! φ 🡒 ψ
                             inv {φ ψ : F} {𝓢 : S} : 𝓢 ⊢! φ 🡒 ψ → adjoin φ 𝓢 ⊢! ψ
Logic/Entailment.lean:513  class Sound (𝓢 : S) (𝓜 : M) : Prop where sound : ∀ {φ : F}, 𝓢 ⊢ φ → 𝓜 ⊧ φ
Logic/Entailment.lean:516  class Complete (𝓢 : S) (𝓜 : M) : Prop where complete : ∀ {φ : F}, 𝓜 ⊧ φ → 𝓢 ⊢ φ
```

Modus ponens and `⨀` (`Propositional/Entailment/Minimal.lean:51-61`):

```lean
class ModusPonens (𝓢 : S) where
  mdp! {φ ψ : F} : 𝓢 ⊢! φ 🡒 ψ → 𝓢 ⊢! φ → 𝓢 ⊢! ψ

alias mdp! := ModusPonens.mdp!
infixl:90 "⨀" => mdp!

lemma mdp [ModusPonens 𝓢] : 𝓢 ⊢ φ 🡒 ψ → 𝓢 ⊢ φ → 𝓢 ⊢ ψ := by
  rintro ⟨hpq⟩ ⟨hp⟩;
  exact ⟨hpq ⨀ hp⟩
infixl:90 "⨀" => mdp
infixl:90 "⨀!" => mdp!
```

(`⨀` is overloaded: on `⊢!` it is the proof-term `mdp!`, on `⊢` the Prop-level `mdp`.)

```
Minimal.lean:244  def C!_trans [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bpq : 𝓢 ⊢! φ 🡒 ψ) (bqr : 𝓢 ⊢! ψ 🡒 χ) : 𝓢 ⊢! φ 🡒 χ := implyS! ⨀ C!_of_conseq! bqr ⨀ bpq
Minimal.lean:245  @[grind <=] lemma C_trans [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hpq : 𝓢 ⊢ φ 🡒 ψ) (hqr : 𝓢 ⊢ ψ 🡒 χ) : 𝓢 ⊢ φ 🡒 χ := ⟨C!_trans hpq.some hqr.some⟩
Cl.lean:123       protected class Cl (𝓢 : S) extends Entailment.Minimal 𝓢, Entailment.HasAxiomDNE 𝓢
Meta/ClProver.lean:82  syntax (name := cl_prover) "cl_prover" : tactic
```

`cl_prover` (`Meta/ClProver.lean`, header: "Proof automation based on the proof search on $\mathbf{LK}$") closes goals `𝓢 ⊢ φ` for any `[Entailment.Cl 𝓢]` by propositional tautology search, optionally from hypotheses `cl_prover [h₁, h₂]` (used throughout `ProvabilityAbstraction/Basic.lean`, e.g. :137, :198, :237). It produces `⊢` (Prop) facts, never a proof term with a size bound.

### 1.6 `Derivation2` — the sequent calculus with a theory-axiom rule (`Basic/Calculus2.lean`)

This is the calculus the internal `Derivation` predicate mirrors node-for-node, and the one `typedQuote` (§2.2) quotes. Verbatim (`Calculus2.lean:13-33`):

```lean
inductive Derivation2 (T : Theory L) : Finset (Proposition L) → Type _
| closed (Γ) (φ : Proposition L) : φ ∈ Γ → ∼φ ∈ Γ → Derivation2 T Γ
| axm {Γ} (φ : Sentence L) : φ ∈ T → (φ : Proposition L) ∈ Γ → Derivation2 T Γ
| verum {Γ} : ⊤ ∈ Γ → Derivation2 T Γ
| and {Γ} {φ ψ : Proposition L} : φ ⋏ ψ ∈ Γ → Derivation2 T (insert φ Γ) → Derivation2 T (insert ψ Γ) → Derivation2 T Γ
| or {Γ} {φ ψ : Proposition L} : φ ⋎ ψ ∈ Γ → Derivation2 T (insert φ (insert ψ Γ)) → Derivation2 T Γ
| all {Γ} {φ : Semiproposition L 1} : ∀¹ φ ∈ Γ → Derivation2 T (insert (Rewriting.free φ) (Γ.image Rewriting.shift)) → Derivation2 T Γ
| exs {Γ} {φ : Semiproposition L 1} : ∃¹ φ ∈ Γ → (t : SyntacticTerm L) → Derivation2 T (insert (φ/[t]) Γ) → Derivation2 T Γ
| wk {Δ Γ} : Derivation2 T Δ → Δ ⊆ Γ → Derivation2 T Γ
| shift {Γ}   : Derivation2 T Γ → Derivation2 T (Γ.image Rewriting.shift)
| cut {Γ φ} : Derivation2 T (insert φ Γ) → Derivation2 T (insert (∼φ) Γ) → Derivation2 T Γ

scoped infix:45 " ⟹₂" => Derivation2
abbrev Derivable2 (T : Theory L) (Γ : Finset (Proposition L)) := Nonempty (T ⟹₂ Γ)
scoped infix:45 " ⟹₂! " => Derivable2
abbrev _root_.FFL.FirstOrder.Theory.Proof2 (T : Theory L) (φ : Proposition L) := T ⟹₂ {φ}
scoped infix: 45 " ⊢₂! " => Theory.Proof2
```

Sequents here are `Finset`s; `closed` is the identity axiom on **arbitrary** formulas (so no `eta` expansion is needed), `axm` is the theory-axiom rule. **`Derivation2` has no `height` and no length function in Foundation** — ArithS's `mlen` (`MetaLength.lean:184`) is the only size measure on it.

Conversions:

```
Calculus2.lean:40   def Derivation.toDerivation2 (T) {Γ : Sequent L} : ⊢ᴸᴷ¹ Γ → T ⟹₂ Γ.toFinset      -- structural, no cut added
Calculus2.lean:70   def Derivation.absorb (d : ⊢ᴸᴷ¹ Γ + ⦃φ⦄) (h : φ ∈ Γ) : ⊢ᴸᴷ¹ Γ
Calculus2.lean:77   structure ProofData (T : Theory L) (Γ : Finset (Proposition L)) where
                      axioms : Multiset (Sentence L); axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
                      derivation : ⊢ᴸᴷ¹ Γ.1 + ∼Sequent.embed axioms
Calculus2.lean:82   noncomputable def cast {Γ Δ : Finset (Proposition L)} (d : T ⟹₂ Γ) (h : Γ = Δ := by simp) : T ⟹₂ Δ := h ▸ d
Calculus2.lean:90   @[reducible] noncomputable def cutManyProof (A : Multiset (Sentence L)) (hA : ∀ ψ ∈ A, ψ ∈ T)
                      (d : T ⟹₂ (insert (φ : Proposition L) (∼Sequent.embed A).toFinset)) : T ⟹₂ {φ}
                      -- one `cut` against `axm ψ` per axiom (list recursion, :94-111)
Calculus2.lean:113  noncomputable def toProofData : {Γ : Finset (Proposition L)} → T ⟹₂ Γ → ProofData T Γ
                      -- `closed φ` ↦ Derivation.eta φ  (:116)      `axm φ` ↦ axiom multiset ⦃φ⦄ + eta  (:119-123)
Calculus2.lean:182  noncomputable def Proof.toProof2 {φ : Sentence L} (b : T ⊢! φ) : T ⊢₂! (φ : Proposition L) :=
                      Derivation2.cutManyProof b.axioms b.axioms_mem <| Derivation2.cast (Derivation.toDerivation2 T b.derivation) …
Calculus2.lean:186  noncomputable def Proof2.toProof {φ : Sentence L} (d : T ⊢₂! (φ : Proposition L)) : T ⊢! φ
Calculus2.lean:192  lemma provable_iff_derivable2 {φ : Sentence L} : T ⊢ φ ↔ Nonempty (T ⊢₂! (φ : Proposition L))
```

**ANALYSIS (sizes across the conversions).** `Proof.toProof2` adds one `cut` + one `axm` leaf per axiom used, and `toDerivation2` is node-for-node; `toProofData` in the other direction replaces `closed φ` by `Derivation.eta φ` (size linear in `|φ|` in nodes, but each node carries whole sequents). Nothing in Foundation tracks this; if the design ever needs to move a length bound from `T ⊢! φ` to `Derivation2` or back, that accounting is new work. ArithS already measures directly on `Derivation2` (`mlen`), which is the right side.

---

## 2. Coded derivations (`FirstOrder/Bootstrapping/Syntax/Proof/{Basic,Typed,Coding,Primrec}.lean`, `DerivabilityCondition/{D1,D2,D3,PeanoMinus,EquationalTheory}.lean`)

Ambient variables in all these files: `{V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`, `{L : Language} [L.Encodable] [L.LORDefinable]`, `{T : Theory L} [T.Δ₁]`.

### 2.1 Δ₁ theories (`Bootstrapping/Syntax/Theory.lean`)

```lean
Theory.lean:13
class Δ₁ (T : Theory L) where
  ch : 𝚫₁.Semisentence 1
  mem_iff : ∀ φ : Proposition L, ℕ ⊧/![⌜φ⌝] ch.val ↔ ∃ σ ∈ T, φ = σ
  isDelta1 : ch.ProvablyProperOn 𝗜𝚺₁

Theory.lean:61   def _root_.FFL.FirstOrder.Theory.Δ₁Class (T : Theory L) [T.Δ₁] : Set V := { φ : V | V ⊧/![φ] T.Δ₁ch.val }
Theory.lean:85   @[simp] lemma Δ₁Class.mem_iff {φ : Sentence L} : (⌜φ⌝ : V) ∈ T.Δ₁Class ↔ φ ∈ T
```

`𝗣𝗔⁻.Δ₁` (`Incompleteness/Definability.lean:640`), `𝗣𝗔.Δ₁` (:1070), `𝗜𝚺₁.Δ₁` (:1072); `Δ₁.add` (:107), `singleton` (:125), `insert` (:145) for finite extensions.

### 2.2 The internal derivation predicate (`Proof/Basic.lean`)

Node codes (Cantor-pair tuples, tag in the second slot), `Basic.lean:134-152`:

```lean
noncomputable def axL (s p : V) : V := ⟪s, 0, p⟫ + 1
noncomputable def verumIntro (s : V) : V := ⟪s, 1, 0⟫ + 1
noncomputable def andIntro (s p q dp dq : V) : V := ⟪s, 2, p, q, dp, dq⟫ + 1
noncomputable def orIntro (s p q d : V) : V := ⟪s, 3, p, q, d⟫ + 1
noncomputable def allIntro (s p d : V) : V := ⟪s, 4, p, d⟫ + 1
noncomputable def exsIntro (s p t d : V) : V := ⟪s, 5, p, t, d⟫ + 1
noncomputable def wkRule (s d : V) : V := ⟪s, 6, d⟫ + 1
noncomputable def shiftRule (s d : V) : V := ⟪s, 7, d⟫ + 1
noncomputable def cutRule (s p d₁ d₂ : V) : V := ⟪s, 8, p, d₁, d₂⟫ + 1
noncomputable def axm (s p : V) : V := ⟪s, 9, p⟫ + 1
```

Each has a **Σ₀** graph (`axLGraph : 𝚺₀.Semisentence 3` … `axmGraph`, :156-204) and `@[simp]` magnitude lemmas `seq_lt_axL : s < axL s p`, `p_lt_andIntro`, `dp_lt_andIntro`, … , `p_lt_axm` (:212-265) — every component is strictly below the node code — plus `fstIdx_<rule> : fstIdx (<rule> s …) = s` (:267-276), so `fstIdx d` is the conclusion sequent.

The one-step operator, `Basic.lean:286-297` (the internal `Derivation2`, sequents as finite sets `s`, `p ^⋏ q` etc. the internal connectives, `T.Δ₁Class` the internal axiom set):

```lean
def Phi (C : Set V) (d : V) : Prop :=
  IsFormulaSet L (fstIdx d) ∧
  ( (∃ s p, d = axL s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
    (∃ s, d = verumIntro s ∧ ^⊤ ∈ s) ∨
    (∃ s p q dp dq, d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧ (fstIdx dp = insert p s ∧ dp ∈ C) ∧ (fstIdx dq = insert q s ∧ dq ∈ C)) ∨
    (∃ s p q dpq, d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧ fstIdx dpq = insert p (insert q s) ∧ dpq ∈ C) ∨
    (∃ s p dp, d = allIntro s p dp ∧ ^∀ p ∈ s ∧ fstIdx dp = insert (free L p) (setShift L s) ∧ dp ∈ C) ∨
    (∃ s p t dp, d = exsIntro s p t dp ∧ ^∃ p ∈ s ∧ IsTerm L t ∧ fstIdx dp = insert (substs1 L t p) s ∧ dp ∈ C) ∨
    (∃ s d', d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ d' ∈ C) ∨
    (∃ s d', d = shiftRule s d' ∧ s = setShift L (fstIdx d') ∧ d' ∈ C) ∨
    (∃ s p d₁ d₂, d = cutRule s p d₁ d₂ ∧ (fstIdx d₁ = insert p s ∧ d₁ ∈ C) ∧ (fstIdx d₂ = insert (neg L p) s ∧ d₂ ∈ C)) ∨
    (∃ s p, d = axm s p ∧ p ∈ s ∧ p ∈ T.Δ₁Class) )
```

`blueprint : Fixpoint.Blueprint 0` (:351), `Phi_definable : 𝚫₁.Defined …` (:412), `construction : Fixpoint.Construction V (blueprint T)` (:417), `StrongFinite` (:437) — the IΣ₁ fixpoint machinery (strong finiteness = every premise code is below the node code, which is what makes the fixpoint Δ₁).

The predicates and their formulas, `Basic.lean:465-489`:

```lean
def Derivation : V → Prop := (construction T).Fixpoint ![]
def DerivationOf (d s : V) : Prop := fstIdx d = s ∧ Derivation T d
def Derivable (s : V) : Prop := ∃ d, DerivationOf T d s
def Proof (d φ : V) : Prop := DerivationOf T d {φ}
def Provable (φ : V) : Prop := ∃ d, Proof T d φ

noncomputable def derivation : 𝚫₁.Semisentence 1 := (blueprint T).fixpointDefΔ₁
noncomputable def derivationOf : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “d s. !fstIdxDef s d ∧ !(derivation T).sigma d”)
  (.mkPi “d s. !fstIdxDef s d ∧ !(derivation T).pi d”)
noncomputable def derivable : 𝚺₁.Semisentence 1 := .mkSigma “Γ. ∃ d, !(derivationOf T).sigma d Γ”
noncomputable def proof : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “d φ. ∃ s, !insertDef s φ 0 ∧ !(derivationOf T).sigma d s”)
  (.mkPi “d φ. ∀ s, !insertDef s φ 0 → !(derivationOf T).pi d s”)
noncomputable def provable : 𝚺₁.Semisentence 1 := .mkSigma “φ. ∃ d, !(proof T).sigma d φ”
noncomputable abbrev provabilityPred (σ : Sentence L) : ArithmeticSentence := (provable T).val/[⌜σ⌝]
```

Classification instances: `Derivation.defined : 𝚫₁-Predicate[V] Derivation T via derivation T` (:505), `DerivationOf.defined : 𝚫₁-Relation[V]` (:511), `Derivable.defined : 𝚺₁-Predicate[V]` (:518), `Proof.defined : 𝚫₁-Relation[V] Proof T via proof T` (:525), `Provable.defined : 𝚺₁-Predicate[V] Provable T via provable T` (:532). Note the comment at :495: "Proving this by `rfl` overflows memory on Lean v4.33.1." for `provabilityPred'_val`.

Case analysis and induction on codes, `Basic.lean:543-596`:

```lean
lemma case_iff {d : V} :
    Derivation T d ↔
    IsFormulaSet L (fstIdx d) ∧
    ( (∃ s p, d = Bootstrapping.axL s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
      (∃ s, d = verumIntro s ∧ ^⊤ ∈ s) ∨
      (∃ s p q dp dq, d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧ DerivationOf T dp (insert p s) ∧ DerivationOf T dq (insert q s)) ∨
      … (one disjunct per rule, `DerivationOf` in place of `∈ C`) …
      (∃ s p, d = axm s p ∧ p ∈ s ∧ p ∈ T.Δ₁Class) ) :=
  (construction T).case

alias ⟨case, _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.Derivation.mk⟩ := case_iff

lemma induction1 (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    {d} (hd : Derivation T d)
    (hAxL : ∀ s, IsFormulaSet L s → ∀ p ∈ s, neg L p ∈ s → P (axL s p))
    (hVerumIntro : ∀ s, IsFormulaSet L s → ^⊤ ∈ s → P (verumIntro s))
    (hAnd : ∀ s, IsFormulaSet L s → ∀ p q dp dq, p ^⋏ q ∈ s → DerivationOf T dp (insert p s) → DerivationOf T dq (insert q s) →
      P dp → P dq → P (andIntro s p q dp dq))
    (hOr : …) (hAll : …) (hExs : …) (hWk : …) (hShift : …)
    (hCut : ∀ s, IsFormulaSet L s → ∀ p d₁ d₂, DerivationOf T d₁ (insert p s) → DerivationOf T d₂ (insert (neg L p) s) →
      P d₁ → P d₂ → P (cutRule s p d₁ d₂))
    (hRoot : ∀ s, IsFormulaSet L s → ∀ p, p ∈ s → p ∈ T.Δ₁Class → P (axm s p)) : P d
```

`induction1` requires `P` to be **Σ₁ or Π₁** (`Γ-[1]-Predicate P`) — it is IΣ₁'s induction inside `V`, not Lean's. Introduction lemmas (all `Bootstrapping.Derivation.mk ⟨…, Or.inr …⟩`): `axL` (:603), `verumIntro` (:606), `andIntro` (:610), `orIntro` (:616), `allIntro` (:622), `exsIntro` (:629), `wkRule` (:637), `shiftRule` (:643), `cutRule` (:649), `axm` (:657); `of_ss (h : T.Δ₁Class (V := V) ⊆ U.Δ₁Class) : Derivation T d → Derivation U d` (:665). `Derivable.*` (:690-837) repeat them for the existential `Derivable`; `Provable.conj`/`disj` (:850-857); `internal_provable_iff_internal_derivable` (:839).

### 2.3 The typed internal layer (`Proof/Typed.lean`)

```lean
Typed.lean:106  structure InternalTheory (V : Type*) (L : Language) [L.Encodable] [L.LORDefinable] where
                  theory : Theory L
                  Δ₁ : theory.Δ₁
Typed.lean:116  def _root_.FFL.FirstOrder.Theory.internalize (T : Theory L) [T.Δ₁] : InternalTheory V L := ⟨T, inferInstance⟩
Typed.lean:123  structure TDerivation (T : InternalTheory V L) (Γ : Sequent V L) where
                  val : V
                  derivationOf : DerivationOf T.theory val Γ.val
Typed.lean:129  scoped infix:45 " ⊢!ᵈᵉʳ " => TDerivation
Typed.lean:131  def TProof (T : InternalTheory V L) (φ : Formula V L) := T ⊢!ᵈᵉʳ insert φ ∅
Typed.lean:133  instance : Entailment (InternalTheory V L) (Formula V L) := ⟨TProof⟩
Typed.lean:146  lemma TProvable.iff_provable {σ : Formula V L} : T ⊢ σ ↔ Provable T.theory σ.val
Typed.lean:158  lemma tprovable_iff_provable {T : Theory L} [T.Δ₁] {σ : Formula V L} : T.internalize V ⊢ σ ↔ Provable T σ.val
Typed.lean:161  lemma tprovable_tquote_iff_provable_quote {T : Theory L} [T.Δ₁] {φ : Proposition L} : T.internalize V ⊢ ⌜φ⌝ ↔ Provable T (⌜φ⌝ : V)
```

So `T.internalize V ⊢! φ` is a TYPE whose inhabitants are **elements `val : V` that are internal derivation codes** — a proof object living in the model `V`, not a meta derivation. The constructors return such codes and record the code equation:

```
Typed.lean:183  noncomputable def byAxm (φ) (h : φ ∈' T.theory) (hΓ : φ ∈ Γ) : T ⊢!ᵈᵉʳ Γ          -- val = axm Γ.val φ.val
Typed.lean:189  noncomputable def em (φ) (h : φ ∈ Γ := by simp) (hn : ∼φ ∈ Γ := by simp) : T ⊢!ᵈᵉʳ Γ    -- val = axL
Typed.lean:195  noncomputable def verum (h : ⊤ ∈ Γ := by simp) : T ⊢!ᵈᵉʳ Γ
Typed.lean:201  noncomputable def and' (H : φ ⋏ ψ ∈ Γ) (dp : T ⊢!ᵈᵉʳ insert φ Γ) (dq : T ⊢!ᵈᵉʳ insert ψ Γ) : T ⊢!ᵈᵉʳ Γ
Typed.lean:208  noncomputable def or' …   Typed.lean:214 all' …   Typed.lean:220 exs' … (t : Term V L) …
Typed.lean:226  noncomputable def wk (d : T ⊢!ᵈᵉʳ Δ) (h : Δ ⊆ Γ) : T ⊢!ᵈᵉʳ Γ        -- (wk d h).val = wkRule Γ.val d.val (:229)
Typed.lean:231  noncomputable def shift (d : T ⊢!ᵈᵉʳ Γ) : T ⊢!ᵈᵉʳ Γ.shift
Typed.lean:236  noncomputable def cut (d₁ : T ⊢!ᵈᵉʳ insert φ Γ) (d₂ : T ⊢!ᵈᵉʳ insert (∼φ) Γ) : T ⊢!ᵈᵉʳ Γ :=
                  ⟨cutRule Γ.val φ.val d₁.val d₂.val, by simp, Derivation.cutRule (by simpa using d₁.derivationOf) (by simpa using d₂.derivationOf)⟩
Typed.lean:242  noncomputable def and … or … all … exs (introduction forms, via Derivable.toTDerivation — code NOT tracked)
Typed.lean:264  noncomputable def modusPonens (dpq : T ⊢!ᵈᵉʳ insert (φ 🡒 ψ) Γ) (dp : T ⊢!ᵈᵉʳ insert φ Γ) : T ⊢!ᵈᵉʳ insert ψ Γ
                  -- wk + and + em + one cut (:265-270)
Typed.lean:313  noncomputable instance : Entailment.ModusPonens T   … :329 Entailment.Minimal T   … :403 Entailment.Cl T
Typed.lean:442  noncomputable def all {φ : Semiformula V L 1} (dp : T ⊢! φ.free) : T ⊢! ∀¹ φ
Typed.lean:531  noncomputable def exs {φ : Semiformula V L 1} (t) (dp : T ⊢! φ.subst ![t]) : T ⊢! ∃¹ φ
Typed.lean:533  lemma exs! {φ : Semiformula V L 1} (t) (dp : T ⊢ φ.subst ![t]) : T ⊢ ∃¹ φ
```

**ANALYSIS.** The `and/or/all/exs` introduction forms at :242-255 go through `Derivable.toTDerivation` (`Typed.lean:139`, `choose`), so their `.val` is an unspecified code; only the primed forms and `wk/shift/cut/em/byAxm/verum` have `@[simp] *_val` equations. Any internal length accounting on `TDerivation` would have to use the primed forms.

### 2.4 Quoting a meta derivation to a code (`Proof/Coding.lean`) and unquoting (`Derivation.sound`)

Sequent codes are **sums of exponentials** (bit-set encoding):

```
Coding.lean:21   noncomputable def Sequent.quote (Γ : Finset (Proposition L)) : V := ∑ φ ∈ Γ, Exp.exp (⌜φ⌝ : V)
Coding.lean:34   @[simp] lemma Sequent.mem_quote_iff {Γ : Finset (Proposition L)} {φ} : ⌜φ⌝ ∈ (⌜Γ⌝ : V) ↔ φ ∈ Γ
Coding.lean:46   lemma Sequent.quote_inj {Γ Δ : Finset (Proposition L)} : (⌜Γ⌝ : V) = ⌜Δ⌝ → Γ = Δ
Coding.lean:54   @[simp] lemma Sequent.quote_insert (Γ) (φ) : (⌜(insert φ Γ)⌝ : V) = insert ⌜φ⌝ ⌜Γ⌝
Coding.lean:82   lemma setShift_quote (Γ) : setShift L (⌜Γ⌝ : V) = ⌜Finset.image Rewriting.shift Γ⌝
Coding.lean:128  lemma Sequent.coe_eq (Γ) : (↑(⌜Γ⌝ : ℕ) : V) = ⌜Γ⌝
Coding.lean:137  lemma isFormulaSet_sound {s : ℕ} : IsFormulaSet L s → ∃ S : Finset (Proposition L), ⌜S⌝ = s
```

The quote of a `Derivation2` as a typed internal derivation, verbatim (`Coding.lean:160-178`):

```lean
noncomputable def typedQuote {Γ : Finset (Proposition L)} : T ⟹₂ Γ → T.internalize V ⊢!ᵈᵉʳ ⌜Γ⌝
  |   closed Δ φ h hn => TDerivation.em ⌜φ⌝ (by simpa) (by simpa using! Sequent.quote_mem_quote.mpr hn)
  |       axm φ hT hΓ => TDerivation.byAxm ⌜φ⌝ (by … (Δ₁Class.mem_iff'' (T := T) (φ := φ)).mpr hT) (by …)
  |           verum h => TDerivation.verum (by simpa using! Sequent.quote_mem_quote.mpr h)
  |       and (φ := φ) (ψ := ψ) h bp bq =>
    TDerivation.and' (show ⌜φ⌝ ⋏ ⌜ψ⌝ ∈ ⌜Γ⌝ by …) (bp.typedQuote.cast (by simp)) (bq.typedQuote.cast (by simp))
  |            or (φ := φ) (ψ := ψ) h b => TDerivation.or' (…) <| b.typedQuote.cast (by simp)
  |           all (φ := φ) h d => TDerivation.all' (…) <| d.typedQuote.cast (by simp)
  |          exs (φ := φ) h t d => TDerivation.exs' (…) ⌜t⌝ <| d.typedQuote.cast (by simp [Matrix.constant_eq_singleton])
  |           wk d ss => TDerivation.wk d.typedQuote (by simpa)
  |           shift d => (TDerivation.shift d.typedQuote).cast (by simp)
  | cut (φ := φ) d dn => TDerivation.cut (φ := ⌜φ⌝) (d.typedQuote.cast (by simp)) (dn.typedQuote.cast (by simp))

noncomputable instance (Γ) : GödelQuote (T ⟹₂ Γ) (T.internalize V ⊢!ᵈᵉʳ ⌜Γ⌝) := ⟨typedQuote V⟩      -- :180
noncomputable instance (Γ) : GödelQuote (T ⟹₂ Γ) V := ⟨fun d ↦ (⌜d⌝ : T.internalize V ⊢!ᵈᵉʳ ⌜Γ⌝).val⟩  -- :182
```

The **meta code equations** (one per constructor), `Coding.lean:195-233`:

```lean
lemma quote_closed (h : φ ∈ Γ) (hn : ∼φ ∈ Γ) : (⌜closed (T := T) Γ φ h hn⌝ : V) = axL ⌜Γ⌝ ⌜φ⌝
lemma quote_axm (σ : Sentence L) (hT : σ ∈ T) (hΓ : (σ : Proposition L) ∈ Γ) : (⌜axm (Γ := Γ) σ hT hΓ⌝ : V) = Bootstrapping.axm ⌜Γ⌝ ⌜σ⌝
lemma quote_verum (h : ⊤ ∈ Γ) : (⌜verum (T := T) h⌝ : V) = verumIntro ⌜Γ⌝
lemma quote_and (h : φ ⋏ ψ ∈ Γ) (d₁ : T ⟹₂ insert φ Γ) (d₂ : T ⟹₂ insert ψ Γ) : (⌜and h d₁ d₂⌝ : V) = andIntro ⌜Γ⌝ ⌜φ⌝ ⌜ψ⌝ ⌜d₁⌝ ⌜d₂⌝
lemma quote_or (h : φ ⋎ ψ ∈ Γ) (d : T ⟹₂ insert φ (insert ψ Γ)) : (⌜or h d⌝ : V) = orIntro ⌜Γ⌝ ⌜φ⌝ ⌜ψ⌝ ⌜d⌝
lemma quote_all {φ : Semiproposition L 1} (h : ∀¹ φ ∈ Γ) (d : T ⟹₂ insert (Rewriting.free φ) (Γ.image Rewriting.shift)) : (⌜all h d⌝ : V) = allIntro ⌜Γ⌝ ⌜φ⌝ ⌜d⌝
lemma quote_exs {φ : Semiproposition L 1} (h : ∃¹ φ ∈ Γ) (t : SyntacticTerm L) (d : T ⟹₂ insert (φ/[t]) Γ) : (⌜exs h t d⌝ : V) = exsIntro ⌜Γ⌝ ⌜φ⌝ ⌜t⌝ ⌜d⌝
lemma quote_wk (d : T ⟹₂ Δ) (ss : Δ ⊆ Γ) : (⌜wk d ss⌝ : V) = wkRule ⌜Γ⌝ ⌜d⌝
lemma quote_shift (d : T ⟹₂ Γ) : (⌜shift d⌝ : V) = shiftRule ⌜Γ.image Rewriting.shift⌝ ⌜d⌝
lemma quote_cut (d₁ : T ⟹₂ insert φ Γ) (d₂ : T ⟹₂ insert (∼φ) Γ) : (⌜cut d₁ d₂⌝ : V) = cutRule ⌜Γ⌝ ⌜φ⌝ ⌜d₁⌝ ⌜d₂⌝
```

Absoluteness of the code and the bridge to `T ⊢! φ`:

```
Coding.lean:238  lemma coe_typedQuote_val_eq (d : T ⟹₂ Γ) : ↑(d.typedQuote ℕ).val = (d.typedQuote V).val
Coding.lean:268  lemma coe_quote_eq (d : T ⟹₂ Γ) : (↑(⌜d⌝ : ℕ) : V) = ⌜d⌝
Coding.lean:272  noncomputable instance (Γ : Sequent L) : GödelQuote (⊢ᴸᴷ¹ Γ) V := ⟨fun b ↦ ⌜Derivation.toDerivation2 (∅ : Theory L) b⌝⟩
Coding.lean:274  noncomputable instance (φ : Sentence L) : GödelQuote (T ⊢! φ) V := ⟨fun b ↦ ⌜b.toProof2⌝⟩
Coding.lean:281  @[simp] lemma derivation_of_quote_derivation {Γ : Sequent L} (b : ⊢ᴸᴷ¹ Γ) : DerivationOf T (⌜b⌝ : V) ⌜Γ.toFinset⌝
Coding.lean:289  @[simp] lemma proof_of_quote_proof2 {φ : Sentence L} (d : T ⊢₂! (φ : Proposition L)) : Proof T (⌜d⌝ : V) ⌜φ⌝
Coding.lean:295  @[simp] lemma proof_of_quote_proof {φ : Sentence L} (b : T ⊢! φ) : Proof T (⌜b⌝ : V) ⌜φ⌝
Coding.lean:298  lemma coe_quote_proof_eq (d : T ⊢! φ) : (↑(⌜d⌝ : ℕ) : V) = ⌜d⌝
```

Unquoting (only on the standard model, and only **existentially**), `Coding.lean:305-392`:

```lean
lemma Derivation.sound {d : ℕ} (h : Derivation T d) : ∃ Γ, ⌜Γ⌝ = fstIdx d ∧ T ⟹₂! Γ := by
  induction d using Nat.strongRec        -- meta strong induction on the ℕ code, one case per disjunct of `case`
  …
noncomputable def Provable.sound2 {φ : Proposition L} (h : Provable T (⌜φ⌝ : ℕ)) : T ⊢₂! φ := by
  let d := Classical.choose h …          -- Classical.choose, then Classical.choice on the Nonempty
lemma Provable.sound {φ : Sentence L} (h : Provable T (⌜φ⌝ : ℕ)) : T ⊢ φ :=
  provable_iff_derivable2.mpr ⟨Provable.sound2 (by simpa using! h)⟩
```

ArithS's `Derivation.sound'` (`Sound.lean:25`) is the code-for-code strengthening (`⌜b⌝ = d`), which Foundation does not have.

`Proof/Primrec.lean` proves the node constructors primitive recursive (`primrec_axL` :32 … `primrec_axm` :82, `primrec_quote_or` :101, `primrec_quote_axm` :108) — used by `Speedup.lean`.

### 2.5 Internal substitution and numerals (`Bootstrapping/Syntax/{Formula,Term}/*.lean`, `FixedPoint.lean`)

Untyped internal substitution (a term vector `w` into formula code `p`):

```
Formula/Functions.lean:436  noncomputable def subst (w p : V) : V := (construction L).result L w p
Formula/Functions.lean:438  noncomputable def substsGraph : 𝚺₁.Semisentence 3 := (blueprint L).result L
Formula/Functions.lean:444  instance subst.defined : 𝚺₁-Function₂[V] subst L via substsGraph L := (construction L).result_defined
Formula/Functions.lean:665  lemma substs_substs {p} (hp : IsSemiformula L l p) :
                              IsSemitermVec L n m w → IsSemitermVec L l n v → subst L w (subst L v p) = subst L (termSubstVec L l w v) p
Formula/Functions.lean:766  noncomputable def substs1 (t u : V) : V := subst L ?[t] u
Formula/Functions.lean:768  noncomputable def substs1Graph : 𝚺₁.Semisentence 3 := .mkSigma “ z t p. ∃ v, !adjoinDef v t 0 ∧ !(substsGraph L) z v p”
Formula/Functions.lean:776  instance substs1.defined : 𝚺₁-Function₂[V] substs1 L via substs1Graph L
Term/Functions.lean:37      noncomputable def termSubst (w t : V) : V := construction.result L ![w] t
Term/Functions.lean:744     noncomputable def numeral (x : V) : V := if x = 0 then 𝟎 else numeralAux (x - 1)
Term/Functions.lean:746     def numeralGraph : 𝚺₁.Semisentence 2 := .mkSigma “t x. (x = 0 → t = ↑Arithmetic.zero) ∧ (x ≠ 0 → ∃ x', !subDef x' x 1 ∧ !numeralAuxGraph t x')”
```

Typed wrappers and their `val` equations:

```
Formula/Typed.lean:156  noncomputable def subst (w : SemitermVec V L n m) (φ : Semiformula V L n) : Semiformula V L m :=
                          ⟨Bootstrapping.subst L w.val φ.val, φ.isSemiformula.subst w.isSemitermVec⟩
Formula/Typed.lean:160  @[simp] lemma val_substs (φ : Semiformula V L n) (w : SemitermVec V L n m) : (φ.subst w).val = Bootstrapping.subst L w.val φ.val := rfl
Formula/Typed.lean:236  lemma substs_substs {n m l : ℕ} (v : SemitermVec V L m l) (w : SemitermVec V L n m) (φ : Semiformula V L n) :
                          (φ.subst w).subst v = φ.subst ((Semiterm.subst v)⨟ w)
Formula/Typed.lean:240  noncomputable def free (φ : Semiformula V L 1) : Formula V L := φ.shift.subst ![Semiterm.fvar 0]
Term/Typed.lean:135     noncomputable def subst (w : SemitermVec V L n m) (t : Semiterm V L n) : Semiterm V L m
Term/Typed.lean:143     @[simp] lemma val_substs (w : SemitermVec V L n m) (t : Semiterm V L n) : (t.subst w).val = termSubst L w.val t.val := rfl
```

Meta code equations for substitution and quotes:

```
Formula/Coding.lean:105  @[simp] lemma typed_quote_substs {n m} (w : Fin n → SyntacticSemiterm L m) (φ : Semiproposition L n) :
                           (⌜φ ⇜ w⌝ : Bootstrapping.Semiformula V L m) = Bootstrapping.Semiformula.subst (fun i ↦ ⌜w i⌝) ⌜φ⌝
Formula/Coding.lean:119  @[simp] lemma free_quote (φ : Semiproposition L 1) : (⌜Rewriting.free φ⌝ : Bootstrapping.Formula V L) = Bootstrapping.Semiformula.free ⌜φ⌝
Formula/Coding.lean:196  lemma quote_def (φ : Semiproposition L n) : (⌜φ⌝ : V) = (⌜φ⌝ : Bootstrapping.Semiformula V L n).val := rfl
Formula/Coding.lean:225  lemma quote_eq_encode (φ : Semiproposition L n) : (⌜φ⌝ : V) = ↑(encode φ)
Formula/Coding.lean:237  lemma coe_quote_eq_quote (φ : Semiproposition L n) : (↑(⌜φ⌝ : ℕ) : V) = ⌜φ⌝
Formula/Coding.lean:244  lemma quote_eq_encode_nat (φ : Semiproposition L n) : (⌜φ⌝ : ℕ) = encode φ
Formula/Coding.lean:292  lemma quote_def (σ : Semisentence L n) : (⌜σ⌝ : V) = ⌜(Rewriting.emb σ : Semiproposition L n)⌝ := rfl
Formula/Coding.lean:302  lemma quote_eq_encode (σ : Semisentence L n) : (⌜σ⌝ : V) = ↑(encode σ)
Term/Coding.lean:44      @[simp] lemma typed_quote_substs {n m} (t : SyntacticSemiterm L n) (w : Fin n → SyntacticSemiterm L m) : …
Term/Coding.lean:120     lemma quote_eq_encode (t : SyntacticSemiterm L n) : (⌜t⌝ : V) = ↑(encode t)
Basic/Syntax/Rew.lean:236  lemma coe_subst_eq_subst_coe (φ : Semisentence L k) (v : Fin k → ClosedSemiterm L n) :
                             (↑(φ ⇜ v) : Semiproposition L n) = (↑φ : Semiproposition L k)⇜(fun i ↦ (↑(v i) : Semiterm L ℕ n))
Basic/Syntax/Rew.lean:240  lemma coe_subst_eq_subst_coe₁ (φ : Semisentence L 1) (t : ClosedSemiterm L n) :
                             (↑(φ/[t]) : Semiproposition L n) = (↑φ : Semiproposition L 1)/[(↑t : Semiterm L ℕ n)]
Syntax/Predicate/Rew.lean:1051  lemma emb_subst_eq_subst_emb … (φ : O k) (v : Fin k → Semiterm L ο n) :
                             (emb (ξ := ξ) (φ ⇜ v)) = Rewriting.subst (ξ := ξ) (emb (ξ := ξ) φ) (fun i ↦ Rew.emb (v i))
```

Numeral substitution into a **code** (the diagonalisation primitives), `Bootstrapping/FixedPoint.lean:22-115`:

```lean
noncomputable def substNumeral (φ x : V) : V := subst ℒₒᵣ ?[numeral x] φ

lemma substNumeral_app_quote (σ π : ArithmeticSemisentence 1) :
    substNumeral ⌜σ⌝ (⌜π⌝ : V) = ⌜(σ/[⌜π⌝] : ArithmeticSentence)⌝ := by
  simp [substNumeral, Sentence.quote_def, Semiformula.quote_def, Rewriting.emb_subst_eq_subst_coe₁]

noncomputable def substNumerals (φ : V) (v : Fin k → V) : V := subst ℒₒᵣ (matrixToVec (fun i ↦ numeral (v i))) φ

lemma substNumerals_app_quote (σ : ArithmeticSemisentence k) (v : Fin k → ℕ) :
    (substNumerals ⌜σ⌝ (v ·) : V) = ⌜((Rew.subst (fun i ↦ ↑(v i))) ▹ σ : ArithmeticSentence)⌝

lemma substNumerals_app_quote_quote (σ : ArithmeticSemisentence k) (π : Fin k → ArithmeticSemisentence k) :
    substNumerals (⌜σ⌝ : V) (fun i ↦ ⌜π i⌝) = ⌜((Rew.subst (fun i ↦ ⌜π i⌝)) ▹ σ : ArithmeticSentence)⌝

noncomputable def substNumeralParams (k : ℕ) (φ x : V) : V := subst ℒₒᵣ (matrixToVec (numeral x :> fun i : Fin k ↦ qqBvar i)) φ

lemma substNumeralParams_app_quote (σ τ : ArithmeticSemisentence (k + 1)) :
    (substNumeralParams k ⌜σ⌝ ⌜τ⌝ : V) = ⌜((Rew.subst (⌜τ⌝ :> fun i : Fin k ↦ #i)) ▹ σ : ArithmeticSemisentence k)⌝

noncomputable def ssnum : 𝚺₁.Semisentence 3 := .mkSigma
  “y φ x. ∃ n, !numeralGraph n x ∧ ∃ v, !adjoinDef v n 0 ∧ !(substsGraph ℒₒᵣ) y v φ”
instance substNumeral.defined : 𝚺₁-Function₂ (substNumeral : V → V → V) via ssnum                       -- :54
noncomputable def ssnums : 𝚺₁.Semisentence (k + 2) := .mkSigma “y φ. ∃ n, !lenDef ↑k n ∧ (⋀ i, ∃ z, !nthDef z n ↑(i : Fin k).val ∧ !numeralGraph z #i.succ.succ.succ.succ) ∧ !(substsGraph ℒₒᵣ) y n φ”   -- :60
noncomputable def ssnumParams (k : ℕ) : 𝚺₁.Semisentence 3 := .mkSigma “y φ x. ∃ v, !lenDef ↑(k + 1) v ∧ (∃ z, !nthDef z v 0 ∧ !numeralGraph z x) ∧ (⋀ i, ∃ z, !nthDef z v ↑(i : Fin k).val.succ ∧ !qqBvarDef z ↑i) ∧ !(substsGraph ℒₒᵣ) y v φ”   -- :88
instance ssnumParams.defined : 𝚺₁-Function₂[V] substNumeralParams k via ssnumParams k                  -- :94
```

Note: `substNumeral_app_quote` is stated only for `x = ⌜π⌝`; the general-numeral case is `substNumerals_app_quote` with `k = 1` (`v : Fin 1 → ℕ`, the substituted term is `↑(v i)` = the numeral).

### 2.6 D1, D2, D3 at the internal level (`DerivabilityCondition/{D1,D2,D3}.lean`)

```lean
D1.lean:20  lemma derivable_quote {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : Derivable T (⌜Γ⌝ : V) :=
              ⟨⌜d⌝, by simpa [Semiformula.quote_def] using! (⌜d⌝ : Theory.internalize V T ⊢!ᵈᵉʳ ⌜Γ⌝).derivationOf⟩
D1.lean:24  /-- Hilbert–Bernays provability condition D1 -/
            theorem internalize_provability {φ} : T ⊢ φ → Provable T (⌜φ⌝ : V) := fun h ↦ by
              simpa using! derivable_quote (V := V) (provable_iff_derivable2.mp h).some
D1.lean:27  theorem internal_provable_of_outer_provable {φ} : T ⊢ φ → T.internalize V ⊢ ⌜φ⌝
D1.lean:30  @[simp] lemma Provable.complete {φ : Sentence L} : T.internalize ℕ ⊢ ⌜φ⌝ ↔ T ⊢ φ
D1.lean:34  @[simp] lemma provable_iff_provable {T : Theory L} [T.Δ₁] {φ : Sentence L} : Provable T (⌜φ⌝ : ℕ) ↔ T ⊢ φ
```

(D1 internal is **constructive in the code**: the witness is literally `⌜d⌝`; the V-generic statement is a `theorem` because `Provable` is Prop.)

```lean
D2.lean:21  theorem modus_ponens {φ ψ : Proposition L} (hφψ : Provable T (⌜φ 🡒 ψ⌝ : V)) (hφ : Provable T (⌜φ⌝ : V)) : Provable T (⌜ψ⌝ : V) := by
              apply (tprovable_tquote_iff_provable_quote (L := L)).mp
              … exact hφψ ⨀ hφ            -- ⨀ = TDerivation.modusPonens on the internal typed layer
D2.lean:28  theorem modus_ponens_sentence {σ τ : Sentence L} (hστ : Provable T (⌜σ 🡒 τ⌝ : V)) (hσ : Provable T (⌜σ⌝ : V)) : Provable T (⌜τ⌝ : V)
```

D3 / formalized Σ₁-completeness, `D3.lean:37-167` (`variable (T : ArithmeticTheory) [Theory.Δ₁ T] [𝗣𝗔⁻ ⪯ T]`, `toNumVec w := ((𝕹 ·)⨟ w)`):

```lean
theorem term_complete {n : ℕ} (t : FirstOrder.ClosedSemiterm ℒₒᵣ n) (w : Fin n → V) :
    T.internalize V ⊢ (toNumVec w ⤕ ⌜t⌝) ≐  𝕹 (t.valb w)           -- structural recursion on t; uses numeral_add/numeral_mul (§2.7)

theorem bold_sigma_one_complete {n} {φ : ArithmeticSemisentence n} (hp : Hierarchy 𝚺 1 φ) {w} :
    V ⊧/w φ → T.internalize V ⊢ (toNumVec w ⤔ ⌜φ⌝) := by
  revert w
  apply sigma₁_induction' hp
  case hVerum … hFalsum … hEQ (term_complete + eq_trans) … hNEQ (numeral_ne, subst_ne) … hLT (numeral_lt, subst_lt) … hNLT …
  case hAnd => … K_intro (ihφ H.1) (ihψ H.2)
  case hOr  => … A_intro_left / A_intro_right
  case hBall => … ball_intro … ball_replace T … ⨀ (eq_comm <| term_complete T t w) ⨀ this
  case hExs => … apply TProof.exs! (𝕹 i) …

theorem sigma_one_provable_of_models {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) : V↓[ℒₒᵣ] ⊧ σ → T.internalize V ⊢ ⌜σ⌝
/-- Hilbert–Bernays provability condition D3 -/
theorem sigma_one_complete {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) : V↓[ℒₒᵣ] ⊧ σ → Provable T (⌜σ⌝ : V)
theorem provable_internalize {σ : ArithmeticSentence} : Provable T (⌜σ⌝ : V) → Provable T (⌜provabilityPred T σ⌝ : V)
```

**ANALYSIS.** `bold_sigma_one_complete` IS a derivation-building Σ₁-completeness — but the derivations it builds are **internal codes in `V`** (`T.internalize V ⊢ …` is `Nonempty (TDerivation …)`, and every step is `⨀`/`K_intro`/`ball_intro`/`exs!`, each of which is an internal `cut`/`and`/`exs` node), and the statement is `Prop`. It is quantified over an arbitrary `V ⊧* IΣ₁`, so it is exactly what the completeness theorem consumes to get `𝗜𝚺₁ ⊢ σ 🡒 □σ` (§3.2). It is **not** a meta derivation of `T ⊢! σ`, and no length is recorded.

### 2.7 Internal PA⁻ numeral lemmas (`DerivabilityCondition/PeanoMinus.lean`, `EquationalTheory.lean`)

All in `T.internalize V ⊢ …` (internal, Prop), `variable (T : ArithmeticTheory) [Theory.Δ₁ T] [𝗣𝗔⁻ ⪯ T]` (:42):

```
PeanoMinus.lean:60   lemma numeral_add (n m : V) : T.internalize V ⊢ (𝕹 n + 𝕹 m) ≐ 𝕹 (n + m)        -- induction m using sigma1_pos_succ_induction
PeanoMinus.lean:92   lemma numeral_mul (n m : V) : T.internalize V ⊢ 𝕹 n * 𝕹 m ≐ 𝕹 (n * m)
PeanoMinus.lean:131  lemma numeral_eq {n m : V} : n = m → T.internalize V ⊢ 𝕹 n ≐ 𝕹 m
PeanoMinus.lean:135  lemma numeral_lt {n m : V} : n < m → T.internalize V ⊢ 𝕹 n <' 𝕹 m
PeanoMinus.lean:156  lemma numeral_ne {n m : V} : n ≠ m → T.internalize V ⊢ 𝕹 n ≉ 𝕹 m
PeanoMinus.lean:171  lemma numeral_nlt {n m : V} : n ≥ m → T.internalize V ⊢ 𝕹 n ≮' 𝕹 m
PeanoMinus.lean:190  lemma lt_iff_substItrDisj (t : Term V ℒₒᵣ) (m : V) : T.internalize V ⊢ (t <' 𝕹 m) 🡘 substItrDisj ![t] (#'1 ≐ #'0) m
PeanoMinus.lean:231  lemma ball_intro (φ : Semiformula V ℒₒᵣ 1) (n : V) (bs : ∀ i < n, T.internalize V ⊢ φ.subst ![𝕹 i]) : T.internalize V ⊢ φ.ball (𝕹 n)
PeanoMinus.lean:249  lemma bexs_intro (φ : Semiformula V ℒₒᵣ 1) (n : V) {i} (hi : i < n) (b : T.internalize V ⊢ φ.subst ![𝕹 i]) : T.internalize V ⊢ φ.bexs (𝕹 n)
PeanoMinus.lean:258  lemma ball_replace (φ : Semiformula V ℒₒᵣ 1) (t u : Term V ℒₒᵣ) : T.internalize V ⊢ (t ≐ u) 🡒 φ.ball t 🡒 φ.ball u
EquationalTheory.lean:39  @[simp] lemma eq_refl (t : Term V ℒₒᵣ) : T.internalize V ⊢ t ≐ t
EquationalTheory.lean:45  @[simp] lemma eq_symm (t u) : T.internalize V ⊢ (t ≐ u) 🡒 (u ≐ t)
EquationalTheory.lean:80  lemma subst_eq (t₁ t₂ u₁ u₂) : T.internalize V ⊢ (t₁ ≐ t₂) 🡒 (u₁ ≐ u₂) 🡒 (t₁ ≐ u₁) 🡒 (t₂ ≐ u₂)
EquationalTheory.lean:85  lemma subst_lt …  :91 subst_ne …  :97 subst_nlt …  :103 subst_add_eq_add …  :109 subst_mul_eq_mul …
EquationalTheory.lean:492 lemma replace (φ : Semiformula V ℒₒᵣ 1) (u₁ u₂ : Term V ℒₒᵣ) : … (u₁ ≐ u₂) 🡒 φ.subst ![u₁] 🡒 φ.subst ![u₂]
```

`sigma1_pos_succ_induction` (`Arithmetic/Induction.lean:18-20`): `@[elab_as_elim] lemma sigma1_pos_succ_induction {P : V → Prop} (hP : 𝚺₁-Predicate P) (zero : P 0) (one : P 1) (succ : ∀ x, P (x + 1) → P (x + 2)) : ∀ x, P x` — the internal numeral lemmas are proved by **IΣ₁-induction inside `V`** on the internal predicate "`T.internalize V ⊢ …`" (which is Σ₁ because `Provable` is), not by Lean recursion.

---

## 3. Provability abstraction and the standard predicate

### 3.1 `ProvabilityAbstraction/Basic.lean`

```lean
Basic.lean:19  abbrev Language.ReferenceableBy (L L₀ : Language) := Semiterm.Operator.GödelNumber L₀ (Sentence L)
Basic.lean:23
structure Provability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  prov : Semisentence L₀ 1
  /-- Derivability condition `D1` -/
  bew_def {σ : Sentence L} : T ⊢ σ → T₀ ⊢ prov/[⌜σ⌝]
Basic.lean:32  @[coe] def pr (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L₀ := 𝔅.prov/[⌜σ⌝]
Basic.lean:35  def con (𝔅 : Provability T₀ T) : Sentence L₀ := ∼𝔅 ⊥
Basic.lean:37  abbrev dia (𝔅 : Provability T₀ T) (φ : Sentence L) : Sentence L₀ := ∼𝔅 (∼φ)
Basic.lean:52  lemma D1 {𝔅 : Provability T₀ T} {σ : Sentence L} : T ⊢ σ → T₀ ⊢ 𝔅 σ := fun h ↦ 𝔅.bew_def h
Basic.lean:54  class HBL2 … (𝔅 : Provability T₀ T) where D2 {σ τ : Sentence L} : T₀ ⊢ 𝔅 (σ 🡒 τ) 🡒 𝔅 σ 🡒 𝔅 τ
Basic.lean:60  class HBL3 where D3 {σ : Sentence L} : T₀ ⊢ 𝔅 σ 🡒 𝔅 (𝔅 σ)
Basic.lean:64  class HBL extends 𝔅.HBL2, 𝔅.HBL3
Basic.lean:66  class Mono … where mono {σ τ : Sentence L} : T ⊢ σ 🡒 τ → T₀ ⊢ 𝔅 σ 🡒 𝔅 τ
Basic.lean:70  class Ext … where ext {σ τ : Sentence L} : T ⊢ σ 🡘 τ → T₀ ⊢ 𝔅 σ 🡘 𝔅 τ
Basic.lean:74  class Rosser … where Ros {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ ∼𝔅 σ
Basic.lean:84  class FormalizedCompleteOn (𝔅 : Provability T₀ T) (σ) where formalized_complete_on : T₀ ⊢ σ 🡒 𝔅 σ
Basic.lean:89  instance [∀ σ, 𝔅.FormalizedCompleteOn (𝔅 σ)] : 𝔅.HBL3 := ⟨by simp⟩
Basic.lean:94  class Kreisel … (𝔅 : Provability T₀ T) where KR {σ : Sentence L} : T ⊢ 𝔅 σ → T ⊢ σ
Basic.lean:100 class SoundOn … (𝔅 : Provability T₀ T) (M : outParam Type*) [Nonempty M] [Structure L₀ M] where
                 sound_on {σ : Sentence L} : M↓[L₀] ⊧ (𝔅 σ : Sentence L₀) → T ⊢ σ
Basic.lean:109 lemma syntactical_sound … [SoundOn 𝔅 M] [M↓[L] ⊧* T₀] : ∀ {σ : Sentence L}, T₀ ⊢ 𝔅 σ → T ⊢ σ
Basic.lean:129 lemma bew_distribute_imply [𝔅.HBL2] (h : T₀ ⊢ 𝔅 (σ 🡒 τ)) : T₀ ⊢ 𝔅 σ 🡒 𝔅 τ := D2 ⨀ h
Basic.lean:131 instance [𝔅.HBL2] : 𝔅.Mono := ⟨λ h => bew_distribute_imply $ D1 h⟩
Basic.lean:161 lemma mono' [𝔅.Mono] (h : T₀ ⊢ σ 🡒 τ) : T₀ ⊢ 𝔅 σ 🡒 𝔅 τ := 𝔅.mono $ WeakerThan.pbl h
Basic.lean:174
class Diagonalization [L.ReferenceableBy L] (T : Theory L) where
  fixedpoint : Semisentence L 1 → Sentence L
  diag (θ) : T ⊢ fixedpoint θ 🡘 θ/[⌜fixedpoint θ⌝]
Basic.lean:184 def gödel (𝔅 : Provability T₀ T) : Sentence L := fixedpoint T₀ “x. ¬!𝔅.prov x”
Basic.lean:187 lemma gödel_spec : T₀ ⊢ (gödel 𝔅) 🡘 ∼𝔅 (gödel 𝔅)
Basic.lean:194 theorem unprovable_gödel : T ⊬ (gödel 𝔅)      … :214 theorem first_incompleteness [𝔅.Kreisel] : Incomplete T
Basic.lean:232 theorem formalized_unprovable_gödel  : T₀ ⊢ 𝔅.con 🡒 ∼𝔅 𝐆      … :245 con_unprovable
Basic.lean:267 def kreisel (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L := fixedpoint T₀ “x. !𝔅.prov x → !σ”
Basic.lean:273 lemma kreisel_spec : T₀ ⊢ (𝐊 σ) 🡘 (𝔅 (𝐊 σ) 🡒 σ)
Basic.lean:281 private lemma kreisel_specAux₁ [L.DecidableEq] [T₀ ⪯ T] : T₀ ⊢ 𝔅 (𝐊 σ) 🡒 𝔅 σ :=
                 Entailment.mdp₁ (C_trans (mdp D2 (D1 (WeakerThan.pbl <| K_left (kreisel_spec)))) D2) D3
Basic.lean:286 theorem löb_theorem (H : T ⊢ 𝔅 σ 🡒 σ) : T ⊢ σ := by
                 have d₁ : T ⊢ 𝔅 (𝐊 σ) 🡒 σ := C_trans (WeakerThan.pbl kreisel_specAux₁) H;
                 have d₂ : T ⊢ 𝔅 (𝐊 σ)     := WeakerThan.pbl $ D1 $ WeakerThan.pbl kreisel_specAux₂ ⨀ d₁;
                 exact d₁ ⨀ d₂;
Basic.lean:291 theorem formalized_löb_theorem : T₀ ⊢ 𝔅 (𝔅 σ 🡒 σ) 🡒 𝔅 σ := by
                 have h₁ : T₀ ⊢ 𝔅 (𝐊 σ) 🡒 𝔅 σ := kreisel_specAux₁;
                 have h₂ : T₀ ⊢ (𝔅 σ 🡒 σ) 🡒 (𝔅 (𝐊 σ) 🡒 σ) := CCC_of_C_left h₁;
                 have h₃ : T ⊢ (𝔅 σ 🡒 σ) 🡒 𝐊 σ := WeakerThan.pbl $ C_trans (CCC_of_C_left h₁) kreisel_specAux₂;
                 exact C_trans (D2 ⨀ (D1 h₃)) h₁;
```

The whole abstraction is at the `⊢` (Prop) level: `Provability` carries `prov : Semisentence L₀ 1` (one free variable, the code) and no budget. `Height.lean`: `noncomputable def Provability.height (𝔅) : ENat := ENat.find (T ⊢ 𝔅^[·] ⊥)` (:18), `boxBot_monotone [T₀ ⪯ T] [𝔅.HBL] : n ≤ m → T ⊢ 𝔅^[n] ⊥ 🡒 𝔅^[m] ⊥` (:24), `height_le_iff_boxBot` (:68). `Refutability.lean`: `structure Refutability` (:15), `jeroslow` (:52) — dual, not needed.

### 3.2 `Incompleteness/StandardProvability.lean` — in full, with the route of each proof

```lean
:18  noncomputable instance : Diagonalization 𝗜𝚺₁ where fixedpoint := fixedpoint ; diag θ := diagonal θ
:24  variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]
:26  local prefix:90 "□" => provabilityPred T

:29  /-- The derivability condition D1. -/
     theorem provable_D1 {σ} : T ⊢ σ → 𝗜𝚺₁ ⊢ □σ := fun h ↦
       complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by simpa [models_iff] using internalize_provability (V := V) h
```
ROUTE: **completeness theorem** (`complete`, §6). The V-generic content `internalize_provability` does construct the internal code `⌜d⌝`, but the passage to `𝗜𝚺₁ ⊢ □σ` is model-theoretic; no IΣ₁ proof object exists.

```lean
:33  /-- The derivability condition D2. -/
     theorem provable_D2 {σ π} : 𝗜𝚺₁ ⊢ □(σ 🡒 π) 🡒 □σ 🡒 □π :=
       complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by simpa [models_iff] using modus_ponens_sentence T
```
ROUTE: **completeness**; the V-generic content is `TDerivation.modusPonens` (an internal cut).

```lean
:38  noncomputable abbrev _root_.FFL.FirstOrder.Theory.standardProvability : Provability 𝗜𝚺₁ T where
       prov := provable T
       bew_def := provable_D1
:44  instance : T.standardProvability.HBL2 := ⟨provable_D2⟩
:46  lemma standardProvability_def (σ : Sentence L) : T.standardProvability σ = provabilityPred T σ := rfl
:48  instance : T.standardProvability.SoundOn ℕ :=
       ⟨fun h ↦ by simpa [Arithmetic.standardProvability_def, models_iff] using h⟩
```
(`SoundOn ℕ` unfolds to `provable_iff_provable`, i.e. `Provable.sound` = `Derivation.sound` on ℕ, §2.4.)

```lean
:55  variable {T U : ArithmeticTheory} [T.Δ₁]
:59  lemma provable_sigma_one_complete [𝗣𝗔⁻ ⪯ T] {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
         𝗜𝚺₁ ⊢ σ 🡒 □σ :=
       complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
         simpa [models_iff] using Bootstrapping.Arithmetic.sigma_one_complete (T := T) (V := V) hσ
```
ROUTE: **completeness**; the V-generic content is `bold_sigma_one_complete` (internal derivation-building, §2.6).

```lean
:65  /-- The derivability condition D3. -/
     theorem provable_D3 [𝗣𝗔⁻ ⪯ T] {σ : ArithmeticSentence} : 𝗜𝚺₁ ⊢ □σ 🡒 □□σ := provable_sigma_one_complete (by simp)
```
ROUTE: instance of the above (□σ is Σ₁ by `simp`/definability).

```lean
:70  lemma provable_D2_context [𝗜𝚺₁ ⪯ U] {Γ σ π} (hσπ : Γ ⊢[U] □(σ 🡒 π)) (hσ : Γ ⊢[U] □σ) : Γ ⊢[U] □π :=
       FiniteContext.of' (weakening inferInstance provable_D2) ⨀ hσπ ⨀ hσ
:73  lemma provable_D3_context [𝗣𝗔⁻ ⪯ T] [𝗜𝚺₁ ⪯ U] {Γ σ} (hσπ : Γ ⊢[U] □σ) : Γ ⊢[U] □□σ
:76  lemma provable_sound [U.SoundOnHierarchy 𝚺 1] {σ} : U ⊢ □σ → T ⊢ σ := fun h ↦ by
       have : ℕ↓[ℒₒᵣ] ⊧ provabilityPred T σ := ArithmeticTheory.SoundOn.sound (F := Arithmetic.Hierarchy 𝚺 1) h (by simp)
       simpa [models_iff] using this
```
ROUTE: **Σ₁-soundness of U on ℕ** (semantic), then `provable_iff_provable` (= `Derivation.sound`, existential meta reconstruction).

```lean
:80  lemma provable_complete [U.SoundOnHierarchy 𝚺 1] [𝗜𝚺₁ ⪯ U] {σ} : T ⊢ σ ↔ U ⊢ □σ :=
       ⟨fun h ↦ weakening inferInstance (provable_D1 h), provable_sound⟩
:83  instance [𝗣𝗔⁻ ⪯ T] : T.standardProvability.HBL3 := ⟨provable_D3⟩
:85  instance [𝗣𝗔⁻ ⪯ T] : T.standardProvability.HBL where
:87  instance [T.SoundOnHierarchy 𝚺 1] : T.standardProvability.Kreisel := ⟨fun h ↦ provable_sound h⟩
:94  lemma provable_sigma_one_complete_of_E {σ π} [𝗜𝚺₁ ⪯ T] (hσ : Hierarchy 𝚺 1 σ) (hσπ : 𝗜𝚺₁ ⊢ σ 🡘 π) : 𝗜𝚺₁ ⊢ π 🡒 □π := by
       apply C_replace ?_ ?_ $ provable_sigma_one_complete (T := T) $ hσ;
       . cl_prover [hσπ];
       . apply T.standardProvability.mono';
         cl_prover [hσπ];
```

`Löb.lean:16-20`: `theorem löb_theorem : T ⊢ provabilityPred T σ 🡒 σ → T ⊢ σ := ProvabilityAbstraction.löb_theorem (𝔅 := T.standardProvability)` and `theorem formalized_löb_theorem : 𝗜𝚺₁ ⊢ provabilityPred T (provabilityPred T σ 🡒 σ) 🡒 provabilityPred T σ` (`variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]`).

**Summary of routes.** D1, D2, D3/Σ₁-completeness: **all through `complete`** (model-theoretic, no IΣ₁ derivation object, no length). Soundness/Kreisel: semantic (`SoundOnHierarchy`) + existential `Derivation.sound`. Löb: pure `⊢`-level algebra over the abstraction. Nothing here can yield a size bound.

### 3.3 `Incompleteness/RestrictedProvability.lean` — in full (this is ArithS's template)

```lean
:27  /-- Provability with restriction of proof size -/
     def RestrictedProvable (f : V → V) (e : ℕ) (T : Theory L) [T.Δ₁] (φ : V) := ∃ d < f (ORingStructure.numeral e), Arithmetic.Bootstrapping.Proof T d φ
:29  noncomputable def restrictedProvable (fDef : 𝚺₁.Semisentence 2) (e : ℕ) : 𝚷₁.Semisentence 1 := .mkPi “φ. ∀ E, !fDef E !e → ∃ d < E, !(proof T).pi d φ”
:31  noncomputable abbrev restrictedProvabilityPred (fDef : 𝚺₁.Semisentence 2) (e : ℕ) (σ : Sentence L) : ArithmeticSentence := (T.restrictedProvable fDef e).val/[⌜σ⌝]
:33  instance RestrictedProvable.defined {f : V → V} {fDef : 𝚺₁.Semisentence 2} [𝚺₁-Function₁[V] f via fDef] {e} :
       𝚷₁-Predicate[V] (T.RestrictedProvable f e) via (T.restrictedProvable fDef e)
:38  /-- Gödel sentence by restricted provability -/
     noncomputable abbrev restrictedGödel (fDef : 𝚺₁.Semisentence 2) (e : ℕ) (T : Theory L) [T.Δ₁] : ArithmeticSentence := fixedpoint (∼(T.restrictedProvable fDef e))
:43  private lemma restrictedGödel'_sigmaOne … : Hierarchy 𝚺 1 (T.restrictedGödel' fDef e) := by definability;
:54  lemma def_restrictedGödel [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel fDef e 🡘 (∼(T.restrictedProvable fDef e).val)/[⌜T.restrictedGödel fDef e⌝] := diagonal _
:71  lemma models_restrictedGödel (f : V → V) [𝚺₁-Function₁[V] f via fDef] :
       V↓[ℒₒᵣ] ⊧ T.restrictedGödel fDef e ↔ ∀ x : V, x < f (ORingStructure.numeral e) → ¬Arithmetic.Bootstrapping.Proof T x (⌜T.restrictedGödel fDef e⌝)
:80  variable [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
:83  theorem true_restrictedGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] : ℕ↓[ℒₒᵣ] ⊧ T.restrictedGödel fDef e
       -- by_contra; a proof below f e would make the Σ₁ negation provable (provable_of_standard_proof) hence true; contradiction
:94  theorem provable_restrictedGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] : T ⊢ T.restrictedGödel fDef e := by
       apply iff_provable_restrictedGödel_provable_restrictedGödel'.mpr;
       apply Arithmetic.sigma_one_completeness_iff T.restrictedGödel'_sigmaOne |>.mp;        -- ← via R0 Σ₁-completeness = `complete`
       apply iff_true_restrictedGödel_true_restrictedGödel'.mp $ true_restrictedGödel f;
:100 /-- Lower bound of a Gödel number of proof of restricted Gödel sentence is `f e`. -/
     theorem lower_bound_gödelNumber_proof_restrictedGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] :
       ∀ b : T ⊢! T.restrictedGödel fDef e, f (ORingStructure.numeral e) ≤ ⌜b⌝
:117 theorem two_pow_le_superexp {e : ℕ} (he : 1 ≤ e) : 2 ^ e ≤ Superexp.superexp e
:125 theorem provable_restrictedGödel_superexp {e : ℕ} : T ⊢ T.restrictedGödel superexpDef e := provable_restrictedGödel Superexp.superexp
:128 theorem lower_bound_gödelNumber_proof_restrictedGödel_superexp {e : ℕ} : ∀ b : T ⊢! T.restrictedGödel superexpDef e, Superexp.superexp e ≤ ⌜b⌝
```

Note the budget `e : ℕ` is a **meta** parameter substituted as a numeral `!e` inside `restrictedProvable` (:29) — this is NOT parametric in the sense the milestone needs; ArithS's `LenProvableV` (`BewV.lean`) is the parametric form. `RestrictedProvable` is Π₁ (because `f` is given by a Σ₁ graph and the bound is universally quantified); ArithS's `lenProvableV` is made Δ₁ by giving both a Σ and a Π reading of `fbound`.

### 3.4 `Incompleteness/Speedup.lean` (`minProof`, computability of `Proof`)

```lean
:33  noncomputable def _root_.FFL.FirstOrder.Theory.minProof (T : Theory L) [T.Δ₁] (σ : Sentence L) : ℕ :=
       sInf (Set.range λ d : T ⊢₂! (σ : Proposition L) ↦ (⌜d⌝ : ℕ))
:37  lemma proof_minProof (h : T ⊢ σ) : Proof T (T.minProof σ) ⌜σ⌝
:43  lemma minProof_eq_zero_of_unprovable (h : T ⊬ σ) : T.minProof σ = 0
:49  lemma minProof_le (d : T ⊢₂! (σ : Proposition L)) : T.minProof σ ≤ ⌜d⌝
:57  lemma computablePred_proof : ComputablePred λ p : ℕ × ℕ ↦ Proof T p.1 p.2            -- via computablePred_iff_delta1 + definability
:74  lemma computablePred_bddExists_proof [L.Primcodable] (hF : Computable F) {bd : α → ℕ} (hbd : Computable bd) :
       ComputablePred λ a ↦ ∃ d ≤ bd a, Proof T d ⌜F a⌝
:93  private def speedupProof (T : Theory L) (σ π : Sentence L) : insert σ T ⊢₂! ((σ ⋎ π : Sentence L)) :=
       Derivation2.or (φ := σ) (ψ := π) (by simp) $ Derivation2.axm σ (by simp) (by simp)      -- an explicit two-node Derivation2 term
:98  private lemma computable_quote_speedupProof [L.Primcodable] : Computable λ π ↦ (⌜speedupProof T σ π⌝ : ℕ)
:112 theorem ehrenfeucht_mycielski_speedup [L.Primcodable] (hU : ¬ComputablePred (insert (∼σ) T).theory) (f : ℕ → ℕ) (hf : Computable f) :
       ∃ π : Sentence L, T ⊢ π ∧ f ((insert σ T).minProof π) < T.minProof π
```

`speedupProof` is the one place in `Incompleteness/` where a **concrete `Derivation2` proof term** is written down and its code computed (`quote_or`, `quote_axm` at :104) — the pattern a bounded D1 would need at scale.

---

## 4. The diagonal lemma (`Bootstrapping/FixedPoint.lean`) — YES, a parametric fixed point exists

Ambient: `variable {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T]` (:122). Note that `diag`/`fixedpoint` are stated for any `T ⊇ 𝗜𝚺₁`, not only `𝗜𝚺₁`.

```lean
:126 noncomputable def diag (θ : ArithmeticSemisentence 1) : ArithmeticSemisentence 1 := “x. ∀ y, !ssnum y x x → !θ y”
:128 noncomputable def fixedpoint (θ : ArithmeticSemisentence 1) : ArithmeticSentence := (diag θ)/[⌜diag θ⌝]
:130 theorem diagonal (θ : ArithmeticSemisentence 1) :
         T ⊢ fixedpoint θ 🡘 θ/[⌜fixedpoint θ⌝] :=
       haveI : 𝗘𝗤 _ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
       complete.{0} T _ fun (V : Type) _ _ ↦ by
         have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ T inferInstance
         suffices V ⊧/![] (fixedpoint θ) ↔ V ⊧/![⌜fixedpoint θ⌝] θ by simpa [models_iff, Matrix.constant_eq_singleton]
         let t : V := ⌜diag θ⌝
         have ht : substNumeral t t = ⌜fixedpoint θ⌝ := by simp [t, fixedpoint, substNumeral_app_quote]
         calc V ⊧/![] (fixedpoint θ)
           _ ↔ V ⊧/![t] (diag θ)         := by simp [fixedpoint, t]
           _ ↔ V ⊧/![substNumeral t t] θ := by simp [diag]
           _ ↔ V ⊧/![⌜fixedpoint θ⌝] θ   := by simp [ht]
```

ROUTE: **`complete`** (model-theoretic). The proof does not construct a derivation; it checks the equivalence in every `V ⊧* T` using the code equation `substNumeral_app_quote`. The `∀ y` in `diag` makes `fixedpoint θ` inherit a Π-prefix over θ (see `multifixedpoint_pi` :192).

Multi-fixed-point (:150-198): `multidiag` (:151), `multifixedpoint (θ : Fin k → ArithmeticSemisentence k) (i : Fin k) : ArithmeticSentence` (:156), `theorem multidiagonal … : T ⊢ multifixedpoint θ i 🡘 (Rew.subst fun j ↦ ⌜multifixedpoint θ j⌝) ▹ (θ i)` (:158), `exclusiveMultifixedpoint` (:174) with injectivity (:177), `multifixedpoint_pi` (:192). All via `complete.{0} T _`.

**The parametric fixed point** (:202-233), verbatim:

```lean
section ParameterizedDiagonalization

noncomputable def parameterizedDiag (θ : ArithmeticSemisentence (k + 1)) : ArithmeticSemisentence (k + 1) := “x. ∀ y, !(ssnumParams k) y x x → !θ y ⋯”

noncomputable def parameterizedFixedpoint (θ : ArithmeticSemisentence (k + 1)) : ArithmeticSemisentence k :=
    (Rew.subst (⌜parameterizedDiag θ⌝ :> fun j ↦ #j)) ▹ parameterizedDiag θ

theorem parameterized_diagonal (θ : ArithmeticSemisentence (k + 1)) :
    T ⊢ ∀¹* (parameterizedFixedpoint θ 🡘 “!θ !!(⌜parameterizedFixedpoint θ⌝) ⋯”) :=
  haveI : 𝗘𝗤 _ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  complete.{0} T _ fun (V : Type) _ _ ↦ by
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ T inferInstance
    suffices ∀ params : Fin k → V, V ⊧/params (parameterizedFixedpoint θ) ↔ V ⊧/(⌜parameterizedFixedpoint θ⌝ :> params) θ by
      simpa [models_iff, Matrix.comp_vecCons', BinderNotation.finSuccItr, Function.comp_def, Matrix.empty_eq]
    intro params
    let t : V := ⌜parameterizedDiag θ⌝
    have ht : substNumeralParams k t t = ⌜parameterizedFixedpoint θ⌝ := by simp [t, substNumeralParams_app_quote, parameterizedFixedpoint]
    calc V ⊧/params (parameterizedFixedpoint θ)
        ↔ V ⊧/(t :> params) (parameterizedDiag θ)       := by simp [parameterizedFixedpoint, Matrix.comp_vecCons', t, Function.comp_def]
      _ ↔ V ⊧/(substNumeralParams k t t :> params) θ    := by simp [parameterizedDiag, Matrix.comp_vecCons', BinderNotation.finSuccItr, Function.comp_def]
      _ ↔ V ⊧/(⌜parameterizedFixedpoint θ⌝ :> params) θ := by simp [ht]

theorem parameterized_diagonal₁ (θ : ArithmeticSemisentence 2) :
    T ⊢ ∀¹ (parameterizedFixedpoint θ 🡘 θ/[⌜parameterizedFixedpoint θ⌝, #0]) := by
  simpa [allClosure, BinderNotation.finSuccItr, Matrix.fun_eq_vec_one] using parameterized_diagonal (T := T) θ

end ParameterizedDiagonalization
```

So for `θ : Semisentence 2` (variables: `#0` = the code, `#1` = the parameter `x`), `ψ := parameterizedFixedpoint θ : Semisentence 1` satisfies `T ⊢ ∀ x, (ψ(x) ↔ θ(⌜ψ⌝, x))` — exactly the `ψ(x) ↔ θ(⌜ψ⌝, x)` asked for; the code substituted is the code of the **open** semisentence `ψ` (a `Semisentence 1`), and `θ`'s first slot receives it as a numeral (`Rew.subst (⌜parameterizedDiag θ⌝ :> fun j ↦ #j)` keeps the parameters as bound variables). Quantified form: one `∀¹` outside (`parameterized_diagonal₁`), or `∀¹*` over `k` parameters. Proof: `complete`, no derivation, hence no length information about the equivalence proof.

---

## 5. Σ₁-completeness — proof objects? (THE question)

### 5.1 Meta-level Σ₁-completeness (`Arithmetic/R0/Basic.lean`, `Definability/Absoluteness.lean`)

```lean
R0/Basic.lean:15
inductive R0 : ArithmeticTheory
  | equal : ∀ φ ∈ 𝗘𝗤 ℒₒᵣ, R0 φ
  | Ω₁ (n m : ℕ) : R0 “↑n + ↑m = ↑(n + m)”
  | Ω₂ (n m : ℕ) : R0 “↑n * ↑m = ↑(n * m)”
  | Ω₃ (n m : ℕ) : n ≠ m → R0 “↑n ≠ ↑m”
  | Ω₄ (n : ℕ) : R0 “∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i”
```

Every numeral fact about `𝗥₀` is proved **in a model `M ⊧* 𝗥₀`** by instantiating the axiom (`Theory.models M _ (R0.Ω₁ n m)`):

```
R0/Basic.lean:45  lemma numeral_add_numeral (n m : ℕ) : (numeral n : M) + numeral m = numeral (n + m)
R0/Basic.lean:48  lemma numeral_mul_numeral (n m : ℕ) : (numeral n : M) * numeral m = numeral (n * m)
R0/Basic.lean:51  lemma numeral_ne_numeral_of_ne {n m : ℕ} (h : n ≠ m) : (numeral n : M) ≠ numeral m
R0/Basic.lean:54  lemma lt_numeral_iff {x : M} {n : ℕ} : x < numeral n ↔ ∃ i : Fin n, x = numeral i
R0/Basic.lean:76  lemma val_numeral {n ξ} (bv : Fin n → ℕ) (fv : ξ → ℕ) (t : ArithmeticSemiterm ξ n) :
                    t.val (M := M) (numeral ∘ bv) (numeral ∘ fv) = numeral (t.val bv fv)          -- structural recursion on t, IN THE MODEL
R0/Basic.lean:86  lemma bold_sigma_one_completeness {n} {φ : ArithmeticSemiformula ξ n} (hp : Hierarchy 𝚺 1 φ) {bv : Fin n → ℕ} {fv : ξ → ℕ} :
                    φ.Eval bv fv → φ.Eval (M := M) (numeral ∘ bv) (numeral ∘ fv)                  -- sigma₁_induction', IN THE MODEL
R0/Basic.lean:112 lemma R0.model_complete {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) : ℕ↓[ℒₒᵣ] ⊧ σ → M↓[ℒₒᵣ] ⊧ σ
R0/Basic.lean:131 lemma bold_sigma_one_completeness' {n} {σ : ArithmeticSemisentence n} (hσ : Hierarchy 𝚺 1 σ) {bv} :
                    σ.Evalb (M := ℕ) bv → σ.Evalb (M := M) (numeral ∘ bv)
R0/Basic.lean:141 variable {T : ArithmeticTheory} [𝗥₀ ⪯ T]
R0/Basic.lean:143 theorem sigma_one_completeness {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
                    ℕ↓[ℒₒᵣ] ⊧ σ → T ⊢ σ := fun H =>
                  haveI : 𝗘𝗤 _ ⪯ T := …
                  complete.{0} _ _ <| fun M _ _ ↦ by
                    have : M↓[ℒₒᵣ] ⊧* 𝗥₀ := ModelsTheory.of_provably_subtheory M 𝗥₀ T inferInstance
                    exact R0.model_complete hσ H
R0/Basic.lean:151 theorem sigma_one_completeness_iff [T.SoundOnHierarchy 𝚺 1] {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) : ℕ↓[ℒₒᵣ] ⊧ σ ↔ T ⊢ σ
Absoluteness.lean:89  theorem sigma_one_completeness_iff_param {σ : ArithmeticSemisentence n} (hσ : Hierarchy 𝚺 1 σ) {e : Fin n → ℕ} :
                    ℕ ⊧/e σ ↔ T ⊢ (σ ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x))      -- variable {T} [𝗣𝗔⁻ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
Absoluteness.lean:94  lemma models_iff_provable_of_Sigma0_param [V↓[ℒₒᵣ] ⊧* T] {σ} (hσ : Hierarchy 𝚺 0 σ) {e : Fin n → ℕ} :
                    V ⊧/(Nat.cast ∘ e) σ ↔ T ⊢ (σ ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x))
Absoluteness.lean:102 lemma models_iff_provable_of_Delta1_param [V↓[ℒₒᵣ] ⊧* T] {σ : 𝚫₁.Semisentence n} (hσ : σ.ProperOn ℕ) (hσV : σ.ProperOn V) {e : Fin n → ℕ} :
                    V ⊧/(Nat.cast ∘ e) σ.val ↔ T ⊢ (σ.val ⇜ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x))
```

`Q/Basic.lean` (Robinson's `𝗤`, :11-20) likewise proves `numeral_add (n m : ℕ) : (numeral n : M) + numeral m = numeral (n + m)` (:192, by `match m` + `Arithmetic.add_succ`), `numeral_mul` (:216), `numeral_ne_of_ne` (:246), `numeral_lt_of_lt` (:260) **in an arbitrary model `M ⊧* 𝗤`**. `PeanoMinus/Basic.lean:314-319` gives `numeral_eq_natCast : (ORingStructure.numeral : ℕ → M) = Nat.cast`. There is **no** `𝗤 ⊢ …`/`𝗥₀ ⊢ …`/`𝗣𝗔⁻ ⊢ …` numeral lemma anywhere (grep over `Arithmetic/{Q,R0,PeanoMinus}`: the only hit is an internal `have hConj : 𝗣𝗔⁻ ⊢ finite.toFinset.conj` in `PeanoMinus/Basic.lean:141`, unrelated).

### 5.2 The sweep for derivation-building definitions

Grep over `FirstOrder/{Arithmetic,Incompleteness,Basic}` and `Bootstrapping/{DerivabilityCondition,FixedPoint}` for `def … : … ⊢! …` (a definition returning a proof **type**): the only hits are the generic calculus plumbing

- `Basic/Calculus.lean:400 noncomputable def cut … (b : U ⊢! φ) : T ⊢! φ`,
- `Basic/Calculus2.lean:182 Proof.toProof2`, `:186 Proof2.toProof`,

plus the two-node `speedupProof` (`Speedup.lean:93`, `Derivation2` term) and the `lemma specialize` whose body is an explicit `Derivation.or … (Derivation.exs …)` (`Calculus.lean:481-493`). A grep for `Derivation.(all|exs|and|or|cut|identity|verum)`, `Derivation2.` or `Nat.rec` in `Arithmetic/` and `Incompleteness/` hits only `Speedup.lean` (the same term) and `R0/Representation.lean:124,131` (a `Nat.rec` on `Part` values in the arithmetisation of partial recursive functions — nothing to do with derivations). The Semiterm/Semiformula `complexity` recursions and `Derivation.eta` build derivations only for **logical** identities.

### 5.3 Answer

**No proof-object Σ₁-completeness exists at the meta level anywhere in Foundation.** For numeral arithmetic (`n̄ + m̄ = ↑(n+m)`, `n̄ < m̄`, bounded quantifiers), the only theorem-producing statements are `T ⊢` (Prop, `Nonempty`) and every one of them goes through the completeness theorem `complete` (§6): `sigma_one_completeness` (R0), `sigma_one_completeness_iff_param`, `models_iff_provable_of_Delta1_param`, `provable_sigma_one_complete`/`provable_D3` (StandardProvability). The numeral lemmas in `Q/Basic`, `R0/Basic`, `PeanoMinus/Basic` are statements **about elements of a model `M`**, proved by instantiating axioms in `M`; no `Derivation`/`Derivation2` term is ever built by recursion on `n`, on a term, or on a Σ₁ formula.

The **one** derivation-building Σ₁-completeness is the **internal** one: `Bootstrapping.Arithmetic.bold_sigma_one_complete` (`D3.lean:76`) together with `term_complete` (`D3.lean:48`) and the internal PA⁻ numeral lemmas (`DerivabilityCondition/PeanoMinus.lean`, §2.7). These recurse (Lean recursion on the meta formula `φ` / term `t`, IΣ₁-induction on the numeral inside `V`) and at each step glue **internal proof codes** with `⨀` (= `TDerivation.modusPonens`, one `cut`), `K_intro`, `ball_intro`, `TProof.exs!`. Their conclusion is `T.internalize V ⊢ …` = `Nonempty (TDerivation …)` = `Provable T ⌜…⌝` in `V` — an object of the model, not a Lean `Derivation2`, and with no size accounting (the `and/or/exs` typed constructors at `Typed.lean:242-255` even lose the code equation, §2.3). On `V = ℕ` it yields a meta `T ⊢ σ` only via `Provable.sound` = `Classical.choose` over `Derivation.sound` (§2.4).

---

## 6. The completeness-theorem route for internal universal statements

```lean
Arithmetic/Basic/Model.lean:77
/-- provable_of_models -/
lemma complete (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (φ : ArithmeticSentence) (H : ∀ (M : Type*) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T], M↓[ℒₒᵣ] ⊧ φ) :
    T ⊢ φ := complete_aux T φ fun M _ s _ _ ↦ by
  rcases standardModel_unique M s
  exact H M

Arithmetic/Basic/Model.lean:8
private lemma complete_aux (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (φ : ArithmeticSentence)
    (H : ∀ (M : Type w) [ORingStructure M] [Structure ℒₒᵣ M] [Structure.ORing ℒₒᵣ M] [M↓[ℒₒᵣ] ⊧* T], M↓[ℒₒᵣ] ⊧ φ) :
    T ⊢ φ := Theory.Proof.complete <| consequence_iff_eq.mpr fun M _ _ _ hT ↦
  letI : (Structure.Model ℒₒᵣ M)↓[ℒₒᵣ] ⊧* T := Structure.ElementaryEquiv.modelsTheory.mp hT
  Structure.ElementaryEquiv.models.mpr (H (Structure.Model ℒₒᵣ M))
```

Underneath:

```lean
Completeness/CounterModel.lean:233
/-- Completeness theorem (II) -/
theorem Proof.complete : T ⊨[Struc.{max u w} L] φ → T ⊢ φ := by
  contrapose!
  intro h
  have : Consistent (insert (∼φ) T) := unprovable_iff_consistent_adjoin.mp h
  have : Semantics.Satisfiable (Struc.{max u w} L) (insert (∼φ) T) := satisfiable_iff_consistent.mpr this
  rcases this with ⟨⟨M, i, s⟩, hM⟩
  have : ¬M↓[L] ⊧ φ ∧ M↓[L] ⊧* T := by simpa using hM
  simpa [consequence_iff] using ⟨M, i.some, s, this.2, this.1⟩
Completeness/CounterModel.lean:245  theorem Proof.complete_iff : T ⊨ φ ↔ T ⊢ φ := ⟨fun h ↦ Proof.complete h, Proof.sound⟩
Basic/Semantics/Semantics.lean:559  lemma consequence_iff {φ} : T ⊨[Struc.{v, u} L] φ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M], M↓[L] ⊧* T → M↓[L] ⊧ φ)
Basic/Eq.lean:265                   lemma consequence_iff_eq {T : Theory L} [𝗘𝗤 L ⪯ T] {σ : Sentence L} :
                                      T ⊨[Struc.{v, u} L] σ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M], M↓[L] ⊧* T → M↓[L] ⊧ σ)
Basic/Soundness.lean:99             theorem Proof.sound {φ : Sentence L} : T ⊢ φ → T ⊨[Struc.{v, u} L] φ
Basic/Soundness.lean:128            lemma models_of_provable (hT : M↓[L] ⊧* T) {φ : Sentence L} (h : T ⊢ φ) : M↓[L] ⊧ φ := consequence_iff.mp (Theory.Proof.sound h) M inferInstance
Arithmetic/Basic/Model.lean:83      lemma provable_iff_of_models_iff {T} [𝗘𝗤 ℒₒᵣ ⪯ T] {n} {φ ψ : ArithmeticSemisentence n}
                                      (h : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ) : T ⊢ ∀¹* (φ 🡘 ψ)
Arithmetic/Basic/Model.lean:92      lemma models_iff_of_provable_iff … (h : T ⊢ ∀¹* (φ 🡘 ψ)) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) : V ⊧/e φ ↔ V ⊧/e ψ
Arithmetic/Basic/Model.lean:109     class ArithmeticTheory.SoundOn (T : ArithmeticTheory) (F : ArithmeticSentence → Prop) where sound : ∀ {σ}, T ⊢ σ → F σ → ℕ↓[ℒₒᵣ] ⊧ σ
RosserProvability.lean:55           lemma provable_of_standard_proof {n : ℕ} {φ : Sentence L} : Proof T (n : V) ⌜φ⌝ → T ⊢ φ
                                      -- Δ₁-absoluteness `Defined.shigmaOne_absolute` moves `Proof T ↑n ⌜φ⌝` from V to ℕ, then `provable_iff_provable`
```

The **typical usage pattern**, from `StandardProvability.lean:29-30, 33-34, 61-62` and `FixedPoint.lean:133`:

```lean
theorem foo : 𝗜𝚺₁ ⊢ σ :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by simpa [models_iff] using <V-generic lemma with [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]> (V := V)
```

i.e. prove `∀ (V) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], P V` where `P V` unfolds (via `models_iff`) to `V↓[ℒₒᵣ] ⊧ σ`, then `complete`. `Theory.Proof.complete` is classical (`contrapose!`, canonical/Henkin model of a consistent theory): it yields `Nonempty (T ⊢! σ)` with no information about the derivation whatsoever.

---

## 7. Lengths and sizes in Foundation

- **Term complexity** (`Syntax/Predicate/Term.lean:96-107`): `def complexity : Semiterm L ξ n → ℕ` with `complexity_bvar = 0`, `complexity_fvar = 0`, `complexity_func … = Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1` — a **depth**, not a symbol count.
- **Formula complexity** (`Basic/Syntax/Formula.lean:194-202`):
  ```lean
  def complexity {n : ℕ} : Semiformula L ξ n → ℕ
  |        ⊤ => 0 | ⊥ => 0 | rel _ _ => 0 | nrel _ _ => 0
  |    φ ⋏ ψ => max φ.complexity ψ.complexity + 1
  |    φ ⋎ ψ => max φ.complexity ψ.complexity + 1
  |     ∀¹ φ => φ.complexity + 1
  |     ∃¹ φ => φ.complexity + 1
  ```
  (depth again; atoms cost 0). `complexity_rew (ω : Rew …) (φ) : (ω ▹ φ).complexity = φ.complexity` (`Basic/Syntax/Rew.lean:159`). Used only as a termination measure (`Derivation.eta`).
- **Derivation height** (`Basic/Calculus.lean:79-87`, §1.1): on `Derivation` (LK) only; **no** height/length on `Derivation2`, `Theory.Proof`, `TDerivation`, or the internal `Derivation` predicate. ArithS's `mlen`/`dlen` fill this gap.
- **Gödel-number magnitudes**: sequents are `∑ φ ∈ Γ, Exp.exp ⌜φ⌝` (`Proof/Coding.lean:21`), nodes are `⟪s, tag, …⟫ + 1` (`Proof/Basic.lean:134-152`) with component-below-node lemmas (`:212-265`); term/formula constructors have the same shape with `var_lt_qqBvar : z < ^#z`, `terms_lt_qqFunc : v < ^func k f v`, `nth_lt_qqFunc_of_lt` (`Term/Basic.lean:30-43`), `nth_lt_qqRel_of_lt` (`Formula/Basic.lean:127`), `le_qqAll : p ≤ ^∀ p`, `succ_le_qqAll`, `index_le_qqAlls`, `le_qqAlls` (`Incompleteness/Definability.lean:57-82`), `lt_q_qqBall`, `lt_u_qqBall` (`:438-441`). Quotes equal Mathlib `encode`: `quote_eq_encode`/`quote_eq_encode_nat` (`Term/Coding.lean:120,135`; `Formula/Coding.lean:225,244,302,307`), `Sentence.quote_eq_encode_nat` used in `Speedup.lean:81`. **No upper bounds** of the form `⌜φ⌝ ≤ f(size φ)` exist in Foundation.
- **Superexponential bounds**: `iterExp` (`HFS/Superexp.lean:30`, `iterExp_zero`, `iterExp_succ : iterExp x (y + 1) = Exp.exp (iterExp x y)`), `Superexp.superexp x := iterExp x x` (:51-53), `superexpDef : 𝚺₁.Semisentence 2` (:83), `two_pow_le_superexp {e : ℕ} (he : 1 ≤ e) : 2 ^ e ≤ Superexp.superexp e` (`RestrictedProvability.lean:117`).
- The numeral used inside formulas is `Semiterm.Operator.numeral L : ℕ → Const L` (`Basic/Operator.lean:156-158`: `0 ↦ Zero.zero`, `n+1 ↦ Add.add.foldr One.one (List.replicate n One.one)`) — **unary** (`n` copies of `1` summed); `⌜a⌝` as an arithmetic term is `Semiterm.Operator.encode ℒₒᵣ a`, i.e. the unary numeral of `Encodable.encode a` (`Arithmetic/Basic/Misc.lean:103-110`, `gödelNumber'_def`). The internal `numeral : V → V` (`Term/Functions.lean:744`) is likewise unary in the code (`numeral_add_two : numeral (n + 1 + 1) = numeral (n + 1) ^+ 𝟏`).

---

## ANALYSIS: what a bounded D1 would need, and what Foundation already gives

Target: `LenProvable f k T ⌜σ⌝ → LenProvable f (e k) T ⌜□_k σ⌝` with an explicit `e`, where `□_k σ` is `lenProvabilityPred fDef k σ` (`Bew.lean:44`), a Π₁ sentence (or, with `LenProvableV`, a Δ₁ one whose Σ-form is `∃ E, fbound E k̄ ∧ ∃ d < E, proof T d ⌜σ⌝ ∧ ∃ n, dlen n d ∧ n ≤ k̄`).

**Given (meta):** a `Derivation2` proof `b : T ⟹₂ {σ}` with `mlen b ≤ k` (from `Proof.sound'`, `Sound.lean:118`, and `dlen_quote`). **Needed:** a `Derivation2` proof `b' : T ⟹₂ {□_k σ}` and a bound `mlen b' ≤ e k`.

What Foundation gives, piece by piece:

1. **The witness.** `⌜b⌝ : ℕ` with `Proof T ⌜b⌝ ⌜σ⌝` in every `V` (`proof_of_quote_proof2`, `Coding.lean:289`) and `↑(⌜b⌝ : ℕ) = (⌜b⌝ : V)` (`coe_quote_eq`, :268). Its **magnitude** is the problem: `Sequent.quote Γ = ∑ exp ⌜φ⌝`, so the conclusion sequent's code has about `⌜σ⌝` bits, and `⌜σ⌝ = encode σ` is a Cantor-pair tree, itself exponential in `|σ|`. Under Foundation's **unary** numerals, the term `⌜b⌝̄` alone has length `≈ ⌜b⌝ ≥ 2^{⌜σ⌝}`, i.e. **doubly** exponential in `|σ|` — no `e` of the form `poly(k)` exists on Foundation's coding with Foundation's numerals. (This is the same phenomenon recorded in the project's memory note `project_arith_numeral_vacuity.md`: binary numeral **descriptions** fix the numeral length, but the Cantor code of the box guard is still `≥ bnum k`.) Any bounded D1 must either (a) use ArithS's binary numeral terms for the witness, making the numeral length `O(log ⌜b⌝) = O(⌜σ⌝ + Σ_nodes …)` — still exponential in `|σ|` because of the `exp` in `Sequent.quote` — or (b) change the sequent coding away from bit-sets, which means re-deriving `Proof/Basic.lean` (out of scope), or (c) accept `e k` exponential/superexponential in `k` and prove D1 with that `e` (Critch's model only needs *some* computable `e`; the bounded Löb argument tolerates any monotone `e`, but the *engine's* `c_node`-style additive costs would then not be matched).

2. **The Δ₁ facts about the witness.** `□_k σ`'s Σ-form, instantiated at the witness, is the conjunction `d = ⌜b⌝ < fbound k̄ ∧ proof T d ⌜σ⌝ ∧ dlen d = mlen b ≤ k̄`. Foundation proves each of these **true in every V** (`proof_of_quote_proof2`; `fbound`/`dlen` via ArithS's Σ₁ graphs and `dlen_quote`), so `sigma_one_completeness`/`models_iff_provable_of_Delta1_param` (`Absoluteness.lean:102`) gives `T ⊢ □_k σ` — as a `Nonempty`, through `complete`, **with no derivation and no length**. To get a *derivation* one needs a **meta derivation-building Σ₁-completeness** that Foundation does not have (§5.3): a `def` by recursion on the Σ₁ formula producing `T ⟹₂ {σ⇜numerals}` from the Lean truth witness, with numeral-arithmetic leaves as **explicit `Derivation2` terms over PA⁻ axioms** (the internal `numeral_add … numeral_nlt`, `ball_intro`, `bexs_intro` of `DerivabilityCondition/PeanoMinus.lean` are exactly the right *lemma shapes* — each would have to be re-proved as a meta `Derivation2` construction with an `mlen` bound, with the IΣ₁-induction on `m` replaced by Lean recursion on `m : ℕ`).

3. **The hard leaf: `proof T ⌜b⌝ ⌜σ⌝`.** This is not a numeral identity but the Δ₁ fixpoint predicate `(blueprint T).fixpointDefΔ₁` (`Proof/Basic.lean:475`). A PA derivation of `proof T ⌜b⌝̄ ⌜σ⌝̄` must unwind the fixpoint definition along the tree `b`: for each node, prove (in PA) the corresponding disjunct of `case_iff` for the numerals of the subcodes — i.e. a *meta-level* mirror of `typedQuote` that emits, instead of internal codes, **`Derivation2` proofs of `Derivation T n̄`** for each subterm code `n`, glued by the PA-formalised `Derivation.mk` direction of `case_iff`. Foundation has (i) the `quote_*` node equations (§2.4) telling which disjunct applies, (ii) Σ₀ graphs for the node constructors so `d = andIntro s̄ p̄ q̄ dp̄ dq̄` is a bounded numeral identity, (iii) the `fixpointDefΔ₁` machinery whose defining equivalence (`Fixpoint.Construction.case`) is a *theorem about V*, not a PA-provable schema with a known proof length. Turning (iii) into a PA proof of bounded length for numeral instances is the genuinely new work; its cost per node is at least the length of the numerals involved (point 1) plus a constant for the fixed `case` unfolding — so `e k` is at least (number of nodes) × (numeral length of the largest subcode), i.e. dominated by point 1 again. Alternatively one can route the leaf through **Δ₁ evaluation**: `proof T` is Δ₁, so `models_iff_provable_of_Delta1_param` gives PA-provability of the instance from truth — but again only through `complete`.

4. **What can be reused as-is.** The internal-side machinery *does* give bounded **D2** in rule form already (ArithS `Cut.lean`) and will give the *statement* of bounded D1/D3 at the internal level for free: `bold_sigma_one_complete` (`D3.lean:76`) applied to the Σ-form of `□_k σ` in `V` yields `Provable T ⌜□_k σ⌝` in every `V` — the unbounded internal D3 pattern (`provable_internalize`, `D3.lean:165`). A bounded *internal* D1 (`LenProvableV T k ⌜σ⌝ → LenProvableV T (e k) ⌜□_k σ⌝` as a statement inside V) would need the internal `TDerivation` constructions to carry a `dlen` bound — possible in principle via the `*_val` equations of the primed constructors (`Typed.lean:183-239`) and ArithS's `dlen` recursion, but `TProof.exs`/`and`/`or`/`all` (`:242-255, 442, 531`) use `Derivable.toTDerivation` and lose the code, so they would have to be re-implemented with the primed forms. This is the parametric route: prove `∀ k, □_k σ → □_{e k} □_k σ` **inside V** (as a Σ₁-formula about `k`) and then lift once by `complete`, which is what the engine's bounded-GL interface wants for `D3`-style fields; but for the *meta* claim "a PA proof of `□_k σ` of length ≤ e k exists" it does not help (it produces internal codes, and on nonstandard `V` those need not be standard).

**Bottom line.** Foundation gives every *semantic* ingredient (witness code, its absoluteness, Δ₁-ness of `proof`, Σ₁-completeness as truth→provability, code equations per node) and the *internal* derivation-building Σ₁-completeness; it gives **no** meta derivation-building Σ₁-completeness, **no** size bounds on codes, and its coding makes any honest `e` at least exponential. The new construction is: a meta `Derivation2`-building Σ₁-completeness with `mlen` accounting (numeral leaves over PA⁻ as explicit terms; the `proof T n̄ m̄` leaf by mirroring `typedQuote` against the PA-formalised `case_iff`), with binary numerals for the witnesses, and `e` chosen to dominate the resulting bound.

---

## ANALYSIS: how the parametric box `□_x ψ(x)` should be written

We want an arithmetic semisentence `Box : Semisentence 1` (free variable `x` = the budget) such that instantiating `x := n̄` yields (provably, and with a computable code equation) `□_n (ψ/[n̄])`, where `ψ : Semisentence 1` is the sentence-schema whose budget slot must match the box's budget.

**Ingredients, all present:**

- The budget-as-variable predicate: ArithS `lenProvableV T : 𝚫₁.Semisentence 2` (`BewV.lean:25`), semantics `LenProvableV T k φ` (:23), Δ₁-defined (:29), with `lenProvableV_numeral` (:43) relating the numeral instance to `LenProvable fbound k`.
- The internal "substitute the numeral of `x` into the code `⌜ψ⌝`" function: `substNumeral (φ x : V) : V := subst ℒₒᵣ ?[numeral x] φ` (`FixedPoint.lean:22`), Σ₁-defined **via `ssnum : 𝚺₁.Semisentence 3`** with argument order `“y φ x.”` (`:51-54`; instance `substNumeral.defined : 𝚺₁-Function₂ substNumeral via ssnum`). Its meta code equation for a general numeral is the `k = 1` case of `substNumerals_app_quote` (`:31-35`): `(substNumerals ⌜σ⌝ (v ·) : V) = ⌜((Rew.subst (fun i ↦ ↑(v i))) ▹ σ : ArithmeticSentence)⌝` — with `v = ![n]` this says `substNumeral ⌜ψ⌝ (n : V) = ⌜ψ/[n̄]⌝`, using `substNumerals ⌜ψ⌝ ![n] = substNumeral ⌜ψ⌝ n`, which holds by `rfl`: `matrixToVec (v : Fin k → V) := Matrix.foldr (fun t w ↦ t ∷ w) 0 v` with `matrixToVec_succ`/`matrixToVec_nil` both `rfl` (`Term/Typed.lean:16-20`), so `matrixToVec ![numeral n] = numeral n ∷ 0 = ?[numeral n]`. (`substNumeral_app_quote`, :24, is the special case `x = ⌜π⌝` used by diagonalisation.) If `ψ` has further free parameters, use `substNumeralParams k` (:41) with graph `ssnumParams k` (:88) and `substNumeralParams_app_quote` (:43).

**The box** (in Foundation's binder notation, `!p a b` = apply the semisentence `p` to terms):

```
Box_ψ(x) :≡ ∃ y, ssnum(y, ⌜ψ⌝, x) ∧ lenProvableV_T(x, y)
```

as a Lean term, schematically `“x. ∃ y, !ssnum y !!(⌜ψ⌝) x ∧ !(lenProvableV T) x y”` (with `⌜ψ⌝` the numeral of the code of the **open** semisentence `ψ`, `gödelNumber'_def`, `Misc.lean:106`). Classification: `ssnum` is Σ₁ and `lenProvableV T` is Δ₁, so `Box_ψ` is **Σ₁** (as a Semisentence 1). Because `substNumeral` is a *function*, the `∃ y` can be traded for `∀ y` (Π-form) for free in every `V ⊧* IΣ₁` — the standard `.mkDelta` pattern used by `derivationOf` (`Proof/Basic.lean:477`) and by `diag` itself (`FixedPoint.lean:126` uses the `∀ y, ssnum y x x → θ y` form), so `Box_ψ` can be packaged as a `𝚫₁.Semisentence 1` if the argument needs it.

**Semantics** (what `complete` will consume): in any `V ⊧* IΣ₁`, `V ⊧/![k] Box_ψ ↔ LenProvableV T k (substNumeral ⌜ψ⌝ k)`, by `substNumeral.defined` and `LenProvableV.defined`.

**Numeral instance / code equation**: for `n : ℕ`, `V ⊧/![n] Box_ψ ↔ LenProvableV T n ⌜ψ/[n̄]⌝` (by the `k=1` case of `substNumerals_app_quote` plus `coe_quote_eq_quote`), and `LenProvableV T (n : V) φ ↔ LenProvable fbound n T φ` (`lenProvableV_numeral`). So `Box_ψ/[n̄]` is provably (over IΣ₁, via `provable_iff_of_models_iff`, `Model.lean:83`) equivalent to `lenProvabilityPred fboundDef n (ψ/[n̄])` — the meta box at budget `n`.

**Parametric fixed point for bounded Löb.** Take `θ : Semisentence 2` with `#0` = the code slot and `#1` = the budget `x`:

```
θ(p, x) :≡ (∃ y, ssnum(y, p, x) ∧ lenProvableV_T(x, y)) → σ(x)        -- "□_x (p/[x̄]) → σ(x)"
```

Then `ψ := parameterizedFixedpoint θ : Semisentence 1` and `parameterized_diagonal₁ θ : T ⊢ ∀¹ (ψ 🡘 θ/[⌜ψ⌝, #0])` (`FixedPoint.lean:228`) give `T ⊢ ∀ x, (ψ(x) ↔ (□_x ψ(x) → σ(x)))` — the parametric Kreisel/Löb sentence, uniformly in the budget, with the box's budget and the sentence's budget the same bound variable. This is exactly `kreisel` (`ProvabilityAbstraction/Basic.lean:267`) with `fixedpoint` replaced by `parameterizedFixedpoint` and `𝔅.prov x` replaced by the two-argument `Box`. The proof of the equivalence is `complete` (no length), which is fine for the *statement* of the fixed point; the bounded Löb *derivation* (bounded `D1`/`D2`/`D3` applied to it) is where the length accounting of the previous section enters — the budget shifts `k ↦ e k` at each application appear as explicit arithmetic on the free variable `x`, so `e` must itself be a Σ₁-definable function whose graph is substituted into `θ` (the same way `fboundDef` enters `lenProvableV`).

**One caution about `Provability`.** `ProvabilityAbstraction.Provability` (`Basic.lean:23`) has `prov : Semisentence L₀ 1` and `pr 𝔅 σ := 𝔅.prov/[⌜σ⌝]`; a budgeted box is a `Semisentence 2` (code, budget) and does not fit that structure — the HBL classes there (`HBL2`, `HBL3`, `Mono`, `Diagonalization`) cannot be instantiated for `□_k` without either fixing `k` (then D2/D3 change the budget and break the class shape) or writing a budget-indexed family of `Provability` structures, which loses the parametricity. The bounded interface must be its own structure (the engine's `Base/BoundedGL.lean` is the model to mirror), using `parameterizedFixedpoint` for `Diagonalization` and `lenProvableV` for `prov`.
