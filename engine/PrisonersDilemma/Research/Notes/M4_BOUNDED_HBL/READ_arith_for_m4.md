# READ — inventory of `arith/ArithS/` for M4 (bounded HBL + parametric PBLT)

Read-only report, 2026-09-11, branch `colomban-arith-m3` (engine v4.33.1, Foundation at
`/Users/colomband/wt/arith-lake/packages/Foundation`). Every statement below is VERBATIM
from the source with `file:line` (paths relative to `arith/ArithS/` unless prefixed
`Foundation/`). Paragraphs marked **ANALYSIS** are mine and not in the code.

Module order (`arith/ArithS.lean:1-37`): Basic, Length, SequentLength, DerivationLength,
Bew, MetaLength, Proper, LangAct, TheoryAct, Transpose, Sound, Symmetry, ProofLength, Cut,
RelabelTemplate, Prog, Bnum, BewV, Guard, Subst, Eval, EvalN, SimTest, Template, RedCell,
Fit, Code, Neg, Agent, AgentConverse, Inst, Det, FitBox, EngineBridge, Core.Tr, Core.Sound,
Audit.

Two naming corrections to the task brief: `lenProvableV_nat` lives in `RedCell.lean:78`
(the `ℕ` instance), while `BewV.lean:43` has the `V`-generic `lenProvableV_numeral`; and
`lenProvableV_mp` lives in `RedCell.lean:85`, not in `Cut.lean` (Cut imports Symmetry and
ProofLength only, RedCell imports Cut).

---

## 1. The predicate and its metatheory

### 1.1 `Bew.lean` — `LenProvable`, Π₁ definition, monotonicity, the `□_k` Gödel sentence

Variables in scope (`Bew.lean:30-32`):
```
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]
```

`Bew.lean:35-36`
```
def LenProvable (f : V → V) (k : ℕ) (T : Theory L) [T.Δ₁] (φ : V) : Prop :=
  ∃ d < f (ORingStructure.numeral k), Proof T d φ ∧ dlen T d ≤ ORingStructure.numeral k
```
`Bew.lean:40-41`
```
noncomputable def lenProvable (fDef : 𝚺₁.Semisentence 2) (k : ℕ) : 𝚷₁.Semisentence 1 :=
  .mkPi “φ. ∀ E, !fDef E !k → ∃ d < E, !(proof T).pi d φ ∧ ∀ n, !(dlenDef T) n d → n ≤ !k”
```
`Bew.lean:44-45`
```
noncomputable abbrev lenProvabilityPred (fDef : 𝚺₁.Semisentence 2) (k : ℕ) (σ : Sentence L) :
    ArithmeticSentence := (lenProvable T fDef k).val/[⌜σ⌝]
```
`Bew.lean:49-51`
```
instance LenProvable.defined {f : V → V} {fDef : 𝚺₁.Semisentence 2} [𝚺₁-Function₁[V] f via fDef] {k} :
    𝚷₁-Predicate[V] (LenProvable f k T) via (lenProvable T fDef k) where
  defined {φ} := by simp [lenProvable, LenProvable, dlen_defined.iff]
```
`Bew.lean:53-54`
```
lemma LenProvable.mono {f : V → V} (hf : Monotone f) {k k' : ℕ} (h : k ≤ k') {φ : V} :
    LenProvable f k T φ → LenProvable f k' T φ := by
```
`Bew.lean:60`
```
lemma LenProvable.provable {f : V → V} {k : ℕ} {φ : V} : LenProvable f k T φ → Provable T φ := by
```
`Bew.lean:70-71`
```
noncomputable abbrev lenGödel (fDef : 𝚺₁.Semisentence 2) (k : ℕ) : ArithmeticSentence :=
  fixedpoint (∼(lenProvable T fDef k))
```
The three gate theorems (namespace `ArithS.Arithmetic`, `variable {V : Type}`, `{T U : ArithmeticTheory} [T.Δ₁]`, `[𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]` at `Bew.lean:90-92,128`):

`Bew.lean:115-118`
```
lemma models_lenGödel (f : V → V) [𝚺₁-Function₁[V] f via fDef] :
    V↓[ℒₒᵣ] ⊧ lenGödel T fDef k ↔
    ∀ x : V, x < f (ORingStructure.numeral k) →
      ¬(Proof T x (⌜lenGödel T fDef k⌝) ∧ dlen T x ≤ ORingStructure.numeral k) := by
```
`Bew.lean:131`
```
theorem true_lenGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] : ℕ↓[ℒₒᵣ] ⊧ lenGödel T fDef k := by
```
`Bew.lean:142`
```
theorem provable_lenGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] : T ⊢ lenGödel T fDef k := by
```
`Bew.lean:148-149`
```
theorem lower_bound_proof_lenGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] :
    ∀ b : T ⊢! lenGödel T fDef k, f k ≤ ⌜b⌝ ∨ k < dlen T (⌜b⌝ : ℕ) := by
```
`Bew.lean:164-165`
```
def Proper (f : ℕ → ℕ) (k : ℕ) (T : ArithmeticTheory) [T.Δ₁] : Prop :=
  ∀ b : T ⊢! lenGödel T fDef k, dlen T (⌜b⌝ : ℕ) ≤ k → ⌜b⌝ < f k
```
`Bew.lean:170-172`
```
theorem lower_bound_dlen_proof_lenGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef]
    (hf : Proper (fDef := fDef) f k T) :
    ∀ b : T ⊢! lenGödel T fDef k, k < dlen T (⌜b⌝ : ℕ) := by
```

### 1.2 `BewV.lean` — the budget as an object variable

`BewV.lean:18-20` scope: `{V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`, `{L} [L.Encodable] [L.LORDefinable]`, `(T : Theory L) [T.Δ₁]`.

`BewV.lean:23`
```
def LenProvableV (k φ : V) : Prop := ∃ d < fbound k, Proof T d φ ∧ dlen T d ≤ k
```
`BewV.lean:25-27`
```
noncomputable def lenProvableV : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “k φ. ∃ E, !fboundDef E k ∧ ∃ d < E, !(proof T).sigma d φ ∧ ∃ n, !(dlenDef T) n d ∧ n ≤ k”)
  (.mkPi “k φ. ∀ E, !fboundDef E k → ∃ d < E, !(proof T).pi d φ ∧ ∀ n, !(dlenDef T) n d → n ≤ k”)
```
`BewV.lean:29`  `instance LenProvableV.defined : 𝚫₁-Relation[V] (LenProvableV T) via lenProvableV T := .mk`
`BewV.lean:37`  `instance LenProvableV.definable : 𝚫₁-Relation[V] (LenProvableV T) := (LenProvableV.defined T).to_definable`
`BewV.lean:39-40` `instance LenProvableV.definable' : Γ-[m + 1]-Relation[V] (LenProvableV T) := (LenProvableV.definable T).of_deltaOne`
`BewV.lean:43-44`
```
lemma lenProvableV_numeral (k : ℕ) (φ : V) :
    LenProvableV T (ORingStructure.numeral k) φ ↔ LenProvable (fbound : V → V) k T φ := Iff.rfl
```
The `.sigma`/`.pi` sides are used by name: `!(lenProvableV TAct).sigma k gc` / `¬!(lenProvableV TAct).pi k gc` in the evaluator blueprint (`Eval.lean:67-68, 84-85`), and `lenProvG := Semiformula.lMap emb (lenProvableV TAct).sigma.val` (`Code.lean:139`).

`RedCell.lean:78-79` (the `ℕ` instance, named as the brief calls it)
```
lemma lenProvableV_nat (k φ : ℕ) :
    LenProvableV TAct k φ ↔ LenProvable (fbound : ℕ → ℕ) k TAct φ := by
```

### 1.3 `Proper.lean` — `fbound`, the towers, `quote_derivation_le`

`Proper.lean:28-29`  `def E (s : ℕ) : ℕ := 2 ^ (2 ^ s)` / `def F (s : ℕ) : ℕ := 2 ^ (2 ^ (2 ^ s))`
`Proper.lean:49`  `lemma F_mono {s t : ℕ} (h : s ≤ t) : F s ≤ F t :=`
`Proper.lean:67` `lemma pair_E {a b s : ℕ} (ha : a ≤ E s) (hb : b ≤ E s) : Nat.pair a b + 1 ≤ E (s + 2)`; `:77` `pair_F` likewise; `:87` `two_pow_E_succ_le_F (s : ℕ) : 2 ^ (E s + 1) ≤ F (s + 1)`.
`Proper.lean:150-151`
```
def SmallCodes (L : Language) [L.Encodable] : Prop :=
  ∀ {k : ℕ} (f : L.Func k), Encodable.encode f ≤ 8
```
`Proper.lean:222-223` `def SmallRelCodes (L : Language) [L.Encodable] : Prop := ∀ {k : ℕ} (r : L.Rel k), Encodable.encode r ≤ 8`
`Proper.lean:170` `theorem quote_term_le (hL : SmallCodes L) {n : ℕ} (t : SyntacticSemiterm L n) :` (bound `E (8 · tlen)`); `:263` `quote_formula_le` (`E (8 · flen)`); `:347` `quote_sequent_le` (`F (8·sqlen+1)`).
`Proper.lean:399-400`
```
theorem quote_derivation_le (hL : SmallCodes L) (hR : SmallRelCodes L)
    {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : (⌜d⌝ : ℕ) ≤ F (12 * mlen d) := by
```
`Proper.lean:581` (scope `{V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`)
```
noncomputable def fbound (k : V) : V := Exp.exp (Exp.exp (Exp.exp (12 * k))) + 1
```
`Proper.lean:583-585`
```
def fboundDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y k. ∃ a, !(expDef.ofZero 𝚺₁) a (12 * k) ∧ ∃ b, !(expDef.ofZero 𝚺₁) b a ∧
    ∃ c, !(expDef.ofZero 𝚺₁) c b ∧ y = c + 1”
```
`Proper.lean:587` `instance fbound_defined : 𝚺₁-Function₁[V] fbound via fboundDef`; `:590` `fbound_definable`.
`Proper.lean:592` `lemma fbound_nat (k : ℕ) : fbound k = F (12 * k) + 1 := by`
`Proper.lean:603-604`
```
theorem proper_of_small (hL : SmallCodes L) (hR : SmallRelCodes L) {k : ℕ} {σ : Sentence L}
    (b : T ⊢! σ) (h : dlen T (⌜b⌝ : ℕ) ≤ k) : (⌜b⌝ : ℕ) < fbound k := by
```
`Proper.lean:615,619,622,626` `smallCodes_LOR`, `smallRelCodes_LOR`, `smallCodes_LAct : SmallCodes LAct`, `smallRelCodes_LAct : SmallRelCodes LAct`.
`Proper.lean:639-641`
```
theorem lower_bound_dlen_proof_lenGödel_fbound :
    ∀ b : T ⊢! lenGödel T fboundDef k, k < dlen T (⌜b⌝ : ℕ) :=
```

### 1.4 `MetaLength.lean` — `tlen/flen/sqlen/mlen`, the quote bridges

`MetaLength.lean:27-30`
```
def tlen {n : ℕ} : SyntacticSemiterm L n → ℕ
  | #x => x + 1
  | &x => x + 1
  | FirstOrder.Semiterm.func _ v => (∑ i, tlen (v i)) + 1
```
`MetaLength.lean:51-52` `theorem termLen_quote {n : ℕ} (t : SyntacticSemiterm L n) : termLen L (⌜t⌝ : V) = ↑(tlen t) := by` (V-generic)
`MetaLength.lean:66-74`
```
def flen {n : ℕ} : Semiproposition L n → ℕ
  | .rel _ v => (∑ i, tlen (v i)) + 1
  | .nrel _ v => (∑ i, tlen (v i)) + 1
  | .verum => 1
  | .falsum => 1
  | .and φ ψ => flen φ + flen ψ + 1
  | .or φ ψ => flen φ + flen ψ + 1
  | .all φ => flen φ + 1
  | .exs φ => flen φ + 1
```
`MetaLength.lean:76-77` `theorem formulaLen_quote {n : ℕ} (φ : Semiproposition L n) : formulaLen L (⌜φ⌝ : V) = ↑(flen φ) := by` (V-generic)
`MetaLength.lean:112` section header `/-! ### Sequents (at V = ℕ) -/`; `:161` `theorem setLen_quote (Γ : Finset (Proposition L)) : setLen L (⌜Γ⌝ : ℕ) = ∑ φ ∈ Γ, flen φ`; `:151` `setLen_insert_of_not_mem` (ℕ).
`MetaLength.lean:180` `abbrev sqlen (Γ : Finset (Proposition L)) : ℕ := ∑ φ ∈ Γ, flen φ`
`MetaLength.lean:184-194` (one clause per `Derivation2` constructor)
```
def mlen : {Γ : Finset (Proposition L)} → T ⟹₂ Γ → ℕ
  | Γ, .closed _ _ _ _ => sqlen Γ + 1
  | Γ, .axm _ _ _ => sqlen Γ + 1
  | Γ, .verum _ => sqlen Γ + 1
  | Γ, .and _ d₁ d₂ => sqlen Γ + mlen d₁ + mlen d₂ + 1
  | Γ, .or _ d => sqlen Γ + mlen d + 1
  | Γ, .all _ d => sqlen Γ + mlen d + 1
  | Γ, .exs _ t d => sqlen Γ + tlen t + mlen d + 1
  | Γ, .wk d _ => sqlen Γ + mlen d + 1
  | _, .shift (Γ := Γ) d => sqlen (Γ.image Rewriting.shift) + mlen d + 1
  | Γ, .cut d₁ d₂ => sqlen Γ + mlen d₁ + mlen d₂ + 1
```
`MetaLength.lean:197` `lemma derivation_quote {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : Derivation T (⌜d⌝ : ℕ) :=`
`MetaLength.lean:201` `theorem dlen_quote {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : dlen T (⌜d⌝ : ℕ) = mlen d := by`

The V-generic code-level length (`DerivationLength.lean`): `:219 def DlenGraph (d n : V) : Prop`, `:253 lemma DlenGraph.case_iff`, per-rule inversions `:274 DlenGraph.axL_iff {s p n : V} : DlenGraph L (axL s p) n ↔ n = setLen L s + 1`, `:277 verumIntro_iff`, `:280 axm_iff`, `:283 andIntro_iff`, `:288 orIntro_iff`, `:292 allIntro_iff`, `:296 exsIntro_iff`, `:301 wkRule_iff`, `:305 shiftRule_iff`, `:309 cutRule_iff`; `:389 noncomputable def dlen (d : V) : V`, `:393 theorem dlen_graph {d : V} (hd : Derivation T d) : DlenGraph L d (dlen T d)`, `:396 dlen_of_not`, `:399 dlen_eq_of_graph`, `:404 dlenDef : 𝚺₁.Semisentence 2`, `:409 instance dlen_defined`.

### 1.5 `ProofLength.lean`

`ProofLength.lean:25-34` the `@[simp]` `rfl` equations `flen_rel`, `flen_nrel`, `flen_verum`, `flen_falsum`, `flen_and`, `flen_or`, `flen_all`, `flen_exs`.
`ProofLength.lean:43-44`
```
lemma flen_le_mlen {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) {σ : Proposition L} (h : σ ∈ Γ) :
    flen σ ≤ mlen d :=
```
`ProofLength.lean:50-51`
```
theorem flen_le_of_lenProvable {σ : Sentence LAct} {k : ℕ}
    (h : LenProvable (fbound : ℕ → ℕ) k TAct (⌜σ⌝ : ℕ)) : flen (σ : Proposition LAct) ≤ k := by
```

### 1.6 `Sound.lean` — codes come from meta derivations, code for code (ℕ only)

`Sound.lean:21` `lemma fstIdx_quote {Γ : Finset (Proposition L)} (b : T ⟹₂ Γ) : fstIdx (⌜b⌝ : ℕ) = ⌜Γ⌝ :=`
`Sound.lean:25-26`
```
theorem Derivation.sound' {d : ℕ} (h : Derivation T d) :
    ∃ Γ : Finset (Proposition L), ∃ b : T ⟹₂ Γ, (⌜b⌝ : ℕ) = d := by
```
`Sound.lean:118-119`
```
theorem Proof.sound' {φ : Proposition L} {d : ℕ} (h : Proof T d (⌜φ⌝ : ℕ)) :
    ∃ b : T ⟹₂ {φ}, (⌜b⌝ : ℕ) = d := by
```

### 1.7 `Symmetry.lean` — τ-closure at every length, and the proof pattern

`Symmetry.lean:25-26`
```
def ProvableLen (T : Theory LAct) [T.Δ₁] (k : ℕ) (φ : Proposition LAct) : Prop :=
  ∃ d : ℕ, Proof T d (⌜φ⌝ : ℕ) ∧ dlen T d ≤ k
```
`Symmetry.lean:38-39` `theorem provableLen_swap_iff (k : ℕ) (φ : Proposition LAct) : ProvableLen TAct k φ ↔ ProvableLen TAct k (Semiformula.lMap swap φ) :=`
`Symmetry.lean:46-48`
```
theorem lenProvable_fbound_swap {k : ℕ} {φ : Sentence LAct}
    (h : LenProvable (fbound : ℕ → ℕ) k TAct (⌜φ⌝ : ℕ)) :
    LenProvable (fbound : ℕ → ℕ) k TAct (⌜Semiformula.lMap swap φ⌝ : ℕ) := by
```
The proof pattern (`Symmetry.lean:49-67`), reused verbatim by `Cut.lean`:
```
  rcases h with ⟨d, hdk, hd, hk⟩
  have e : (ORingStructure.numeral k : ℕ) = k := by simp
  rw [Sentence.quote_def] at hd
  obtain ⟨b, rfl⟩ := Proof.sound' hd
  obtain ⟨b', hb'⟩ := transpose_exists _ b
  rw [dlen_quote, e] at hk
  have hk' : mlen b ≤ k := by
    rcases le_def.mp hk with h | h
    · exact Nat.le_of_eq h
    · exact Nat.le_of_lt h
  refine ⟨⌜b'⌝, ?_, ⟨?_, derivation_quote b'⟩, ?_⟩
  · rw [e, fbound_nat]
    refine Nat.lt_succ_of_le (le_trans (quote_derivation_le smallCodes_LAct smallRelCodes_LAct b')
      (F_mono ?_))
    rw [hb']
    exact Nat.mul_le_mul_left 12 hk'
  · rw [fstIdx_quote b', Sentence.quote_def, ← Semiformula.lMap_emb]
    exact Derivation2.Sequent.quote_singleton _
  · rw [dlen_quote, hb', e]; exact hk
```
`Symmetry.lean:69-71`
```
theorem lenProvable_fbound_swap_iff (k : ℕ) (φ : Sentence LAct) :
    LenProvable (fbound : ℕ → ℕ) k TAct (⌜φ⌝ : ℕ) ↔
    LenProvable (fbound : ℕ → ℕ) k TAct (⌜Semiformula.lMap swap φ⌝ : ℕ) :=
```

### 1.8 `Cut.lean` IN FULL (statements)

Scope: `open FFL FFL.FirstOrder Arithmetic Bootstrapping`, `open PeanoMinus`, `open LAct` (`Cut.lean:34-36`); section `flen` has `variable {L : Language} [L.DecidableEq]` (`:42`).

`Cut.lean:46` `lemma flen_neg {n : ℕ} (φ : Semiproposition L n) : flen (∼φ) = flen φ := by`
`Cut.lean:67` `lemma flen_imply {n : ℕ} (φ ψ : Semiproposition L n) : flen (φ 🡒 ψ) = flen φ + flen ψ + 1 := by`
`Cut.lean:71` `lemma sqlen_singleton (φ : Proposition L) : sqlen ({φ} : Finset (Proposition L)) = flen φ :=`
`Cut.lean:75-76`
```
lemma sqlen_insert_le (φ : Proposition L) (Γ : Finset (Proposition L)) :
    sqlen (insert φ Γ) ≤ flen φ + sqlen Γ := by
```
Section `mlen` (`variable {L : Language} [L.DecidableEq] {T : Theory L}`, `:87`):
`Cut.lean:89-90` `lemma mlen_closed (Γ : Finset (Proposition L)) (φ : Proposition L) (h : φ ∈ Γ) (hn : ∼φ ∈ Γ) : mlen (Derivation2.closed (T := T) Γ φ h hn) = sqlen Γ + 1 := by simp [mlen]`
`Cut.lean:92-93` `lemma mlen_verum {Γ : Finset (Proposition L)} (h : ⊤ ∈ Γ) : mlen (Derivation2.verum (T := T) h) = sqlen Γ + 1 := by simp [mlen]`
`Cut.lean:95-96` `lemma mlen_wk {Δ Γ : Finset (Proposition L)} (d : T ⟹₂ Δ) (ss : Δ ⊆ Γ) : mlen (Derivation2.wk d ss) = sqlen Γ + mlen d + 1 := by simp [mlen]`
`Cut.lean:98-100` `lemma mlen_and {Γ : Finset (Proposition L)} {φ ψ : Proposition L} (h : φ ⋏ ψ ∈ Γ) (d₁ : T ⟹₂ insert φ Γ) (d₂ : T ⟹₂ insert ψ Γ) : mlen (Derivation2.and h d₁ d₂) = sqlen Γ + mlen d₁ + mlen d₂ + 1 := by simp [mlen]`
`Cut.lean:102-104` `lemma mlen_cut {Γ : Finset (Proposition L)} {φ : Proposition L} (d₁ : T ⟹₂ insert φ Γ) (d₂ : T ⟹₂ insert (∼φ) Γ) : mlen (Derivation2.cut d₁ d₂) = sqlen Γ + mlen d₁ + mlen d₂ + 1 := by simp [mlen]`

`Cut.lean:111-117`
```
noncomputable def cutMP {φ ψ : Proposition L} (d₁ : T ⟹₂ {φ 🡒 ψ}) (d₂ : T ⟹₂ {φ}) :
    T ⟹₂ {ψ} :=
  Derivation2.cut (Γ := {ψ}) (φ := φ 🡒 ψ)
    (Derivation2.wk d₁ (by simp))
    (Derivation2.and (φ := φ) (ψ := ∼ψ) (by simp [Semiformula.imp_eq])
      (Derivation2.wk d₂ (by simp))
      (Derivation2.closed _ ψ (by simp) (by simp)))
```
`Cut.lean:120-121`
```
theorem mlen_cutMP {φ ψ : Proposition L} (d₁ : T ⟹₂ {φ 🡒 ψ}) (d₂ : T ⟹₂ {φ}) :
    mlen (cutMP d₁ d₂) ≤ mlen d₁ + mlen d₂ + 5 * flen φ + 10 * flen ψ + 9 := by
```
Section `code` (`variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]`, `{T : Theory L} [T.Δ₁]`, `:145-146`; all at `ℕ`):

`Cut.lean:151-152`
```
theorem lenProvable_fbound_mono {k k' : ℕ} (h : k ≤ k') {φ : ℕ} :
    LenProvable (fbound : ℕ → ℕ) k T φ → LenProvable (fbound : ℕ → ℕ) k' T φ :=
```
`Cut.lean:164-166`
```
theorem lenProvable_of_derivation (hL : SmallCodes L) (hR : SmallRelCodes L)
    {σ : Sentence L} {k : ℕ} (b : T ⟹₂ {(σ : Proposition L)}) (hb : mlen b ≤ k) :
    LenProvable (fbound : ℕ → ℕ) k T (⌜σ⌝ : ℕ) := by
```
`Cut.lean:179-181`
```
theorem derivation_of_lenProvable {σ : Sentence L} {k : ℕ}
    (h : LenProvable (fbound : ℕ → ℕ) k T (⌜σ⌝ : ℕ)) :
    ∃ b : T ⟹₂ {(σ : Proposition L)}, mlen b ≤ k := by
```
`Cut.lean:193-199`
```
theorem lenProvable_mp_sharp_of_small (hL : SmallCodes L) (hR : SmallRelCodes L)
    {k₁ k₂ : ℕ} {φ ψ : Sentence L}
    (h₁ : LenProvable (fbound : ℕ → ℕ) k₁ T (⌜φ 🡒 ψ⌝ : ℕ))
    (h₂ : LenProvable (fbound : ℕ → ℕ) k₂ T (⌜φ⌝ : ℕ)) :
    LenProvable (fbound : ℕ → ℕ)
      (k₁ + k₂ + 5 * flen (φ : Proposition L) + 10 * flen (ψ : Proposition L) + 9)
      T (⌜ψ⌝ : ℕ) := by
```
`Cut.lean:209-210`
```
theorem lenProvable_verum_of_small (hL : SmallCodes L) (hR : SmallRelCodes L) :
    LenProvable (fbound : ℕ → ℕ) 2 T (⌜(⊤ : Sentence L)⌝ : ℕ) := by
```
At `TAct` (`Cut.lean:221-226, 234-240, 243-244`):
```
theorem lenProvable_mp_sharp {k₁ k₂ : ℕ} {φ ψ : Sentence LAct}
    (h₁ : LenProvable (fbound : ℕ → ℕ) k₁ TAct (⌜φ 🡒 ψ⌝ : ℕ))
    (h₂ : LenProvable (fbound : ℕ → ℕ) k₂ TAct (⌜φ⌝ : ℕ)) :
    LenProvable (fbound : ℕ → ℕ)
      (k₁ + k₂ + 5 * flen (φ : Proposition LAct) + 10 * flen (ψ : Proposition LAct) + 9)
      TAct (⌜ψ⌝ : ℕ) :=
  lenProvable_mp_sharp_of_small smallCodes_LAct smallRelCodes_LAct h₁ h₂

theorem lenProvable_mp {k₁ k₂ : ℕ} {φ ψ : Sentence LAct}
    (h₁ : LenProvable (fbound : ℕ → ℕ) k₁ TAct (⌜φ 🡒 ψ⌝ : ℕ))
    (h₂ : LenProvable (fbound : ℕ → ℕ) k₂ TAct (⌜φ⌝ : ℕ)) :
    LenProvable (fbound : ℕ → ℕ)
      (k₁ + k₂ + 10 * (flen (φ : Proposition LAct) + flen (ψ : Proposition LAct)) + 9)
      TAct (⌜ψ⌝ : ℕ) :=
  lenProvable_fbound_mono (by omega) (lenProvable_mp_sharp h₁ h₂)

theorem lenProvable_verum : LenProvable (fbound : ℕ → ℕ) 2 TAct (⌜(⊤ : Sentence LAct)⌝ : ℕ) :=
  lenProvable_verum_of_small smallCodes_LAct smallRelCodes_LAct
```
`RedCell.lean:85-88` (the `LenProvableV` form, ℕ)
```
theorem lenProvableV_mp {k₁ k₂ : ℕ} {φ ψ : Sentence LAct}
    (h₁ : LenProvableV TAct k₁ (⌜φ 🡒 ψ⌝ : ℕ)) (h₂ : LenProvableV TAct k₂ (⌜φ⌝ : ℕ)) :
    LenProvableV TAct (k₁ + k₂ + 10 * (flen (φ : Proposition LAct) + flen (ψ : Proposition LAct)) + 9)
      (⌜ψ⌝ : ℕ) := by
```
The Cut docstring's own open item (`Cut.lean:24-29` and roadmap `ARITHMETIZED_S_ROADMAP.md:780-781`): "Still open here: D2 as an INTERNAL sentence (`IΣ₁ ⊢ □_a(φ➝ψ) ⋏ □_b φ ➝ □_{…} ψ`), which needs the cut construction formalized inside IΣ₁."

---

## 2. Numerals and descriptions

### 2.1 `Bnum.lean` — binary numerals

`Bnum.lean:39` `noncomputable def qqTwo : V := (𝟏 : V) ^+ (𝟏 : V)` (notation `𝟐`).
`Bnum.lean:50-53`
```
def Phi (C : Set V) (pr : V) : Prop :=
  pr = ⟪(0 : V), (𝟎 : V)⟫ ∨ pr = ⟪(1 : V), (𝟏 : V)⟫ ∨
  (∃ m t, 1 ≤ m ∧ ⟪m, t⟫ ∈ C ∧ pr = ⟪2 * m, 𝟐 ^* t⟫) ∨
  (∃ m t, 1 ≤ m ∧ ⟪m, t⟫ ∈ C ∧ pr = ⟪2 * m + 1, (𝟐 ^* t) ^+ 𝟏⟫)
```
`Bnum.lean:55` `noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta …` (Δ₁ core citing `qqAddGraph`/`qqMulGraph` in both polarities, `:56-73`); `:124` `instance : construction.StrongFinite V`.
`Bnum.lean:137` `def BnumGraph (n t : V) : Prop := Bnum.construction.Fixpoint ![] ⟪n, t⟫`
`Bnum.lean:139-141`
```
noncomputable def bnumGraphDef : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “n t. ∃ pr <⁺ (n + t + 1)², !pairDef pr n t ∧ !Bnum.blueprint.fixpointDefΔ₁.sigma pr”)
  (.mkPi “n t. ∀ pr <⁺ (n + t + 1)², !pairDef pr n t → !Bnum.blueprint.fixpointDefΔ₁.pi pr”)
```
`Bnum.lean:149` `instance bnumGraph_defined : 𝚫₁-Relation[V] BnumGraph via bnumGraphDef`
`Bnum.lean:320` `noncomputable def bnum (n : V) : V := Classical.choose! (bnumGraph_existsUnique n)`
`Bnum.lean:322` `lemma bnum_graph (n : V) : BnumGraph n (bnum n)`; `:324` `bnum_eq_of_graph`.
`Bnum.lean:327` `noncomputable def bnumGraph : 𝚺₁.Semisentence 2 := .mkSigma “t n. !bnumGraphDef.sigma n t”` (argument order **`t n`**: value first).
`Bnum.lean:329` `instance bnum.defined : 𝚺₁-Function₁[V] bnum via bnumGraph`; `:335` `bnum.definable`; `:337` `bnum.definable'`.
Equations: `:341 bnum_zero : bnum (0 : V) = 𝟎`, `:343 bnum_one : bnum (1 : V) = 𝟏`, `:345 bnum_two_mul {m : V} (hm : 1 ≤ m) : bnum (2 * m) = 𝟐 ^* bnum m`, `:348 bnum_two_mul_add_one {m : V} (hm : 1 ≤ m) : bnum (2 * m + 1) = (𝟐 ^* bnum m) ^+ 𝟏`, `:359 bnum_even`, `:365 bnum_odd`.
`Bnum.lean:371` `lemma bnum_semiterm (k n : V) : IsSemiterm ℒₒᵣ k (bnum n)` (by `ISigma1.pi1_order_induction`); `:382` `bnum_uterm`.
`Bnum.lean:389` `noncomputable def twoT : ClosedSemiterm ℒₒᵣ 0 := ‘1 + 1’`
`Bnum.lean:392-397`
```
noncomputable def bnumT : ℕ → ClosedSemiterm ℒₒᵣ 0
  | 0 => ‘0’
  | 1 => ‘1’
  | n + 2 =>
    if (n + 2) % 2 = 0 then ‘!!twoT * !!(bnumT ((n + 2) / 2))’
    else ‘!!twoT * !!(bnumT ((n + 2) / 2)) + 1’
```
`Bnum.lean:436` `theorem quote_bnumT (n : ℕ) : (⌜bnumT n⌝ : V) = bnum (n : V) := by` (**every model**)
`Bnum.lean:461` `theorem val_bnumT (n : ℕ) : (bnumT n).val (s := standardModel ℕ) ![] Empty.elim = n := by` (**ℕ only**; V version at `Det.lean:153`)
`Bnum.lean:540-541`
```
theorem tlen_bnumT (n : ℕ) :
    tlen (Rew.emb (bnumT n) : SyntacticSemiterm ℒₒᵣ 0) ≤ 6 * Nat.size n + 1 := by
```
`Neg.lean:102-103`
```
theorem size_le_tlen_bnumT (n : ℕ) :
    Nat.size n ≤ tlen (Rew.emb (bnumT n) : SyntacticSemiterm ℒₒᵣ 0) := by
```
`FitBox.lean:201` `theorem two_pow_succ_le_bnum : ∀ n : ℕ, 2 ^ (n + 1) ≤ bnum (n : ℕ) := by`
`FitBox.lean:225` `theorem size_bnum_ge (n : ℕ) : n + 2 ≤ Nat.size (bnum (n : ℕ)) :=`

### 2.2 `Guard.lean` — descriptions and `guardCode` (all V-generic)

`Guard.lean:40` `noncomputable def csym (u : V) : V := ^func 0 (2 + u) 0`; `:42` `csymGraph : 𝚺₁.Semisentence 2 := .mkSigma “y u. !qqFuncDef y 0 (2 + u) 0”`.
`Guard.lean:53` `noncomputable def dnum (x : V) : V := if x ≤ swapcode x then x else swapcode x`
`Guard.lean:56-57`
```
noncomputable def dU (x : V) : V :=
  if x < swapcode x then csym 0 else if swapcode x < x then csym 1 else numeral 0
```
`Guard.lean:60-61`
```
noncomputable def dW (x : V) : V :=
  if x < swapcode x then csym 1 else if swapcode x < x then csym 0 else numeral 1
```
`Guard.lean:64-65` `noncomputable def actTermCode (a : V) : V := if a = 0 then csym 0 else if a = 1 then csym 1 else numeral a`
`Guard.lean:69-70`
```
noncomputable def dnumGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ s, !relabelDef s 1 0 x ∧ (x ≤ s → y = x) ∧ (s < x → y = s)”
```
`Guard.lean:86-88`
```
noncomputable def dUGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ s, !relabelDef s 1 0 x ∧ ∃ c0, !csymGraph c0 0 ∧ ∃ c1, !csymGraph c1 1 ∧ ∃ z, !numeralGraph z 0 ∧
    (x < s → y = c0) ∧ (s < x → y = c1) ∧ (x = s → y = z)”
```
`Guard.lean:106-108` `dWGraph` (same shape, `c1`/`c0` swapped, `!numeralGraph z 1`).
`Guard.lean:72,90,110,130` `instance dnum.defined / dU.defined / dW.defined / actTermCode.defined : 𝚺₁-Function₁[V] … via …Graph`.
`Guard.lean:149-150`
```
noncomputable def descVec (me opp : V) : V :=
  bnum (dnum me) ∷ dU me ∷ dW me ∷ bnum (dnum opp) ∷ dU opp ∷ dW opp ∷ 0
```
`Guard.lean:153`
```
noncomputable def guardCode (g me opp : V) : V := subst LAct (descVec me opp) g
```
`Guard.lean:155-159`
```
noncomputable def descVecGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y me opp. ∃ n₁, !dnumGraph n₁ me ∧ ∃ t₁, !bnumGraph t₁ n₁ ∧ ∃ u₁, !dUGraph u₁ me ∧ ∃ w₁, !dWGraph w₁ me ∧
    ∃ n₂, !dnumGraph n₂ opp ∧ ∃ t₂, !bnumGraph t₂ n₂ ∧ ∃ u₂, !dUGraph u₂ opp ∧ ∃ w₂, !dWGraph w₂ opp ∧
    ∃ v₅, !adjoinDef v₅ w₂ 0 ∧ ∃ v₄, !adjoinDef v₄ u₂ v₅ ∧
    ∃ v₃, !adjoinDef v₃ t₂ v₄ ∧ ∃ v₂, !adjoinDef v₂ w₁ v₃ ∧ ∃ v₁, !adjoinDef v₁ u₁ v₂ ∧ !adjoinDef y t₁ v₁”
```
`Guard.lean:161-162` `instance descVec.defined : 𝚺₁-Function₂ (descVec : V → V → V) via descVecGraph := .mk fun v ↦ by simp [descVecGraph, descVec]`
`Guard.lean:166-167`
```
noncomputable def guardCodeGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y g me opp. ∃ w, !descVecGraph w me opp ∧ !(substsGraph LAct) y w g”
```
`Guard.lean:169-170` `instance guardCode.defined : 𝚺₁-Function₃ (guardCode : V → V → V → V) via guardCodeGraph := .mk fun v ↦ by simp [guardCodeGraph, guardCode]`; `:172` `guardCode.definable`; `:175` `guardCode.definable'`.

Supporting V-generic facts in `Subst.lean`: `:120-122 lemma isSemiformula_guardCode {g : V} (hg : IsSemiformula LAct 6 g) (me opp : V) : IsSemiformula LAct 0 (guardCode g me opp)`; `:131-132 lemma subst_eq_self_of_le {n w p : V} (hp : IsSemiformula LAct n p) : IsUTermVec LAct (len w) w → n ≤ len w → (∀ i < n, w.[i] = ^#i) → subst LAct w p = p`; `:180-182 lemma guardCode_of_sentence {g : V} (hg : IsSemiformula LAct 0 g) (me opp : V) : guardCode g me opp = g`; `:189-190 noncomputable def gsubst (me opp g : V) : V := if IsSemiformula LAct 6 g then guardCode g me opp else g`; `:192-193 gsubst_of_template`; `:205-206 theorem guardCode_gsubst {g : V} (hg : IsSemiformula LAct 6 g) (me opp me' opp' : V) : guardCode (gsubst me opp g) me' opp' = gsubst me opp g`; `:399 dnum_of_lt {x : V} (h : x < swapcode x) : dnum x = x`, `:402 dnum_of_eq`, `:405 dnum_of_gt {x : V} (h : swapcode x < x) : dnum x = swapcode x`, `:413 lemma dnum_swapcode (x : V) : dnum (swapcode x) = dnum x`; `:476-477 theorem termRelabelVec_descVec (me opp : V) : termRelabelVec 1 0 6 (descVec me opp) = descVec (swapcode me) (swapcode opp)`.

Program codes (`Prog.lean`, V-generic): `:33 pConst (a : V) : V := ⟪0, a⟫ + 1`, `:39 pSearch (k g p q : V) : V := ⟪6, k, g, p, q⟫ + 1`; graphs `:43 pConstGraph : 𝚺₀.Semisentence 2 := .mkSigma “y a. ∃ y' < y, !pairDef y' 0 a ∧ y = y' + 1”`, `:63-64 pSearchGraph : 𝚺₀.Semisentence 5 := .mkSigma “y k g p q. ∃ y' < y, !pair₅Def y' 6 k g p q ∧ y = y' + 1”`, `:65 instance pSearch.defined : 𝚺₀-Function₄ (pSearch : V → V → V → V → V) via pSearchGraph`; `:483 noncomputable def relabel (u w x : V) : V`, `:491 relabelDef : 𝚺₁.Semisentence 4 := .mkSigma “y u w x. !relabelGraphDef.sigma u w x y”`, `:519 @[simp] lemma relabel_search (u w k g p q : V)`, `:527 theorem relabel_zero_one (x : V) : relabel 0 1 x = x`, `:543 noncomputable abbrev swapcode (x : V) : V := relabel 1 0 x`, `:546 theorem swapcode_swapcode (x : V) : swapcode (swapcode x) = x`.

### 2.3 `Template.lean` — the restricted template, its instances, the three equations

`Template.lean:37-39`
```
noncomputable def gtmpl : 𝚺₁.Semisentence 7 := .mkSigma
  “x₁ u₁ w₁ x₂ u₂ w₂ t. ∃ me, !relabelDef me u₁ w₁ x₁ ∧ ∃ opp, !relabelDef opp u₂ w₂ x₂ ∧
    ∃ n, !evalGraphDef n opp me opp t”
```
`Template.lean:45-47` (V-generic)
```
lemma eval_gtmpl (v : Fin 7 → V) :
    V ⊧/v gtmpl.val ↔
    ∃ n, EvalGraph n (relabel (v 4) (v 5) (v 3)) (relabel (v 1) (v 2) (v 0)) (relabel (v 4) (v 5) (v 3)) (v 6) := by
```
`Template.lean:53` `noncomputable def Gtmpl : Semisentence LAct 7 := Semiformula.lMap emb gtmpl.val`
`Template.lean:60` `noncomputable def numT (k : ℕ) : ClosedSemiterm LAct 0 := Semiterm.lMap emb (↑k : ClosedSemiterm ℒₒᵣ 0)` (UNARY; only used in the tie case and `actT` for `a ≥ 2`)
`Template.lean:63` `noncomputable def dnumT (x : ℕ) : ClosedSemiterm LAct 0 := Semiterm.lMap emb (bnumT (dnum x))`
`Template.lean:66-67` `noncomputable def dUT (x : ℕ) : ClosedSemiterm LAct 0 := if x < swapcode x then cterm Act.C else if swapcode x < x then cterm Act.D else numT 0`
`Template.lean:70-71` `dWT` (C/D swapped, `numT 1`).
`Template.lean:74-75` `noncomputable def actT (a : ℕ) : ClosedSemiterm LAct 0 := if a = 0 then cterm Act.C else if a = 1 then cterm Act.D else numT a`
`Template.lean:78` `noncomputable def actT6 (a : ℕ) : Semiterm LAct Empty 6 := Rew.castLE (Nat.zero_le 6) (actT a)`
`Template.lean:82-83`
```
noncomputable def GtmplA (a : ℕ) : Semisentence LAct 6 :=
  Gtmpl ⇜ ![#0, #1, #2, #3, #4, #5, actT6 a]
```
`Template.lean:86-87`
```
noncomputable def descTerms (me opp : ℕ) : Fin 6 → ClosedSemiterm LAct 0 :=
  ![dnumT me, dUT me, dWT me, dnumT opp, dUT opp, dWT opp]
```
`Template.lean:90` `noncomputable def guardSentenceA (a me opp : ℕ) : Sentence LAct := GtmplA a ⇜ descTerms me opp`
`Template.lean:132` `theorem lMap_swap_GtmplA (a : ℕ) : Semiformula.lMap swap (GtmplA a) = GtmplA (swapAct a) := by`
`Template.lean:141-143`
```
theorem lMap_swap_guardSentenceA (a me opp : ℕ) :
    Semiformula.lMap swap (guardSentenceA a me opp) =
    guardSentenceA (swapAct a) (swapcode me) (swapcode opp) := by
```
`Template.lean:152-153` `theorem relabelTemplate_quote_GtmplA (a : ℕ) : relabelTemplate 1 0 (⌜GtmplA a⌝ : ℕ) = ⌜GtmplA (swapAct a)⌝ := by`
V-generic code lemmas: `:162 lemma quote_Gtmpl : (⌜Gtmpl⌝ : V) = ⌜gtmpl.val⌝`, `:173 lemma quote_numT (k : ℕ) : (⌜numT k⌝ : V) = numeral (k : V)`, `:183 quote_cterm_C : (⌜(cterm Act.C : ClosedSemiterm LAct 0)⌝ : V) = csym 0`, `:189 quote_cterm_D … = csym 1`.
ℕ-only code lemmas: `:198 lemma quote_dnumT (x : ℕ) : (⌜dnumT x⌝ : ℕ) = bnum (dnum x)`, `:204 quote_dUT (x : ℕ) : (⌜dUT x⌝ : ℕ) = dU x`, `:212 quote_dWT`, `:220 quote_actT (a : ℕ) : (⌜actT a⌝ : ℕ) = actTermCode a`, `:232-234 semitermVec_val_descTerms (me opp : ℕ) : SemitermVec.val (fun i ↦ (⌜(Rew.emb (descTerms me opp i) : SyntacticSemiterm LAct 0)⌝ : Bootstrapping.Semiterm ℕ LAct 0)) = descVec me opp`.
`Template.lean:247-248` (**the code equation**, ℕ)
```
theorem quote_guardSentenceA (a me opp : ℕ) :
    (⌜guardSentenceA a me opp⌝ : ℕ) = guardCode (⌜GtmplA a⌝ : ℕ) me opp := by
```
ℕ-only truth lemmas (`stdAct`): `:260 val_numT`, `:265-266 val_cterm_C/D`, `:268 lemma val_dnumT (x : ℕ) : (dnumT x).val (s := stdAct) ![] Empty.elim = dnum x`, `:274-275 lemma relabel_val_desc (x : ℕ) : relabel ((dUT x).val (s := stdAct) ![] Empty.elim) ((dWT x).val (s := stdAct) ![] Empty.elim) (dnum x) = x`, `:287 val_actT`, `:295 val_actT6`.
`Template.lean:301-302` (**the truth equation**, ℕ)
```
theorem models_guardSentenceA_iff (a me opp : ℕ) :
    ℕ↓[LAct] ⊧ guardSentenceA a me opp ↔ ∃ n, EvalGraph n opp me opp a := by
```

### 2.4 `RedCell.lean` IN FULL (statements)

`RedCell.lean:31` `noncomputable def Dupoc (k : ℕ) : ℕ := pSearch k (⌜GtmplA 0⌝ : ℕ) (pConst 0) (pConst 1)`
`RedCell.lean:35` `noncomputable def Cupod (k : ℕ) : ℕ := pSearch k (⌜GtmplA 1⌝ : ℕ) (pConst 1) (pConst 0)`
`RedCell.lean:37-38` `lemma swapAct_zero : swapAct (0 : ℕ) = 1` / `lemma swapAct_one : swapAct (1 : ℕ) = 0`
`RedCell.lean:42` `theorem swapcode_Dupoc (k : ℕ) : swapcode (Dupoc k) = Cupod k := by` (proof `unfold Dupoc Cupod swapcode; rw [relabel_search, relabel_const, relabel_const, relabelTemplate_quote_GtmplA, swapAct_zero]; simp [relabelAct]`, `:43-45`)
`RedCell.lean:47` `theorem swapcode_Cupod (k : ℕ) : swapcode (Cupod k) = Dupoc k := by`
`RedCell.lean:52,59` `lemma models_axNe : ℕ↓[LAct] ⊧ axNe` / `models_axNe'`
`RedCell.lean:66` `instance models_TAct : ℕ↓[LAct] ⊧* TAct := by`
`RedCell.lean:78-79` `lenProvableV_nat` (quoted in §1.2); `:85-88` `lenProvableV_mp` (quoted in §1.8).
`RedCell.lean:93-95`
```
theorem evalGraph_of_guard {k me opp a : ℕ}
    (h : LenProvableV TAct k (guardCode (⌜GtmplA a⌝ : ℕ) me opp)) :
    ∃ n, EvalGraph n opp me opp a := by
  rw [← quote_guardSentenceA, lenProvableV_nat] at h
  have hp : TAct ⊢ guardSentenceA a me opp := provable_iff_provable.mp h.provable
  exact (models_guardSentenceA_iff a me opp).mp (models_of_provable models_TAct hp)
```
`RedCell.lean:102-106`
```
theorem guard_Dupoc_iff_guard_Cupod (k : ℕ) :
    LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) (Cupod k)) ↔
    LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : ℕ) (Cupod k) (Dupoc k)) := by
  rw [← quote_guardSentenceA, ← quote_guardSentenceA, lenProvableV_nat, lenProvableV_nat,
    lenProvable_fbound_swap_iff, lMap_swap_guardSentenceA, swapcode_Dupoc, swapcode_Cupod, swapAct_zero]
```
`RedCell.lean:112-133`
```
theorem red_cell (k : ℕ) :
    EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 1 ∧ EvalGraph 2 (Cupod k) (Dupoc k) (Cupod k) 0 := by
  have hG : ¬LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) (Cupod k)) := by
    intro hD
    have hC := (guard_Dupoc_iff_guard_Cupod k).mp hD
    -- Cupod's guard is true: Dupoc defects against Cupod.
    obtain ⟨n, hn⟩ := evalGraph_of_guard hC
    -- But Dupoc, finding its proof, cooperates.
    have hcoop : EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 0 := by
      show EvalGraph (1 + 1) (Dupoc k) (Cupod k) (pSearch k (⌜GtmplA 0⌝ : ℕ) (pConst 0) (pConst 1)) 0
      rw [EvalGraph.search_iff]
      exact Or.inl ⟨hD, (EvalGraph.const_iff (n := 0)).mpr rfl⟩
    exact absurd (EvalGraph.unique' hn hcoop) (by decide)
  have hG' : ¬LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : ℕ) (Cupod k) (Dupoc k)) :=
    fun h ↦ hG ((guard_Dupoc_iff_guard_Cupod k).mpr h)
  constructor
  · show EvalGraph (1 + 1) (Dupoc k) (Cupod k) (pSearch k (⌜GtmplA 0⌝ : ℕ) (pConst 0) (pConst 1)) 1
    rw [EvalGraph.search_iff]
    exact Or.inr ⟨hG, (EvalGraph.const_iff (n := 0)).mpr rfl⟩
  · show EvalGraph (1 + 1) (Cupod k) (Dupoc k) (pSearch k (⌜GtmplA 1⌝ : ℕ) (pConst 1) (pConst 0)) 0
    rw [EvalGraph.search_iff]
    exact Or.inr ⟨hG', (EvalGraph.const_iff (n := 0)).mpr rfl⟩
```
`RedCell.lean:136-139`
```
theorem red_cell_unique (k n : ℕ) {a b : ℕ}
    (ha : EvalGraph n (Dupoc k) (Cupod k) (Dupoc k) a) (hb : EvalGraph n (Cupod k) (Dupoc k) (Cupod k) b) :
    a = 1 ∧ b = 0 :=
  ⟨EvalGraph.unique' ha (red_cell k).1, EvalGraph.unique' hb (red_cell k).2⟩
```

### 2.5 `Fit.lean` — the guard fits (Critch (b), box-free)

`Fit.lean:192-195`
```
theorem flen_subst_le {k : ℕ} (φ : Semisentence L k) (w : Fin k → ClosedSemiterm L 0) :
    flen (Rewriting.emb (φ ⇜ w) : Proposition L) ≤
    flen (Rewriting.emb φ : Semiproposition L k) *
      (∑ i, tlen (Rew.emb (w i) : SyntacticSemiterm L 0) + 1) := by
```
`Fit.lean:211-212` `lemma tlen_emb_dnumT (x : ℕ) : tlen (Rew.emb (dnumT x) : SyntacticSemiterm LAct 0) ≤ 6 * Nat.size (dnum x) + 1`; `:257 tlen_emb_dUT (x : ℕ) : … ≤ 1`; `:264 tlen_emb_dWT`.
`Fit.lean:279-281`
```
theorem sum_tlen_descTerms_le (me opp : ℕ) :
    ∑ i, tlen (Rew.emb (descTerms me opp i) : SyntacticSemiterm LAct 0) ≤
    6 * (Nat.size (dnum me) + Nat.size (dnum opp)) + 6 := by
```
`Fit.lean:297` `noncomputable def cG (a : ℕ) : ℕ := flen (Rewriting.emb (GtmplA a) : Semiproposition LAct 6)` — `attribute [irreducible] cG` at `:310` (proof-craft: never evaluate).
`Fit.lean:300-302`
```
theorem flen_guardSentence_le' (me opp a : ℕ) :
    flen (Rewriting.emb (guardSentenceA a me opp) : Proposition LAct) ≤
    cG a * (6 * (Nat.size (dnum me) + Nat.size (dnum opp)) + 7) :=
```
`Fit.lean:324-326`
```
theorem exists_guard_const : ∃ c : ℕ, ∀ me opp a : ℕ, a ≤ 1 →
    flen (Rewriting.emb (guardSentenceA a me opp) : Proposition LAct) ≤
    10 * c + 6 * c * (Nat.size (dnum me) + Nat.size (dnum opp)) :=
```
`Fit.lean:375` `noncomputable def cP : ℕ := ⟪(⌜GtmplA 0⌝ : ℕ), pConst 0, pConst 1⟫`; `:377 lemma Dupoc_eq (k : ℕ) : Dupoc k = ⟪6, k, cP⟫ + 1 := rfl`; `:380 attribute [irreducible] cP`.
`Fit.lean:383` `lemma dnum_le_self (x : ℕ) : dnum x ≤ x`
`Fit.lean:389` `theorem size_Dupoc_le (k : ℕ) : Nat.size (Dupoc k) ≤ 4 * Nat.size k + (4 * Nat.size cP + 26)`
`Fit.lean:398-399`
```
theorem size_dnum_Dupoc_le (k : ℕ) :
    Nat.size (dnum (Dupoc k)) ≤ 4 * Nat.size k + (4 * Nat.size cP + 26) :=
```
`Fit.lean:402-403` `theorem size_dnum_Cupod_le (k : ℕ) : Nat.size (dnum (Cupod k)) ≤ 4 * Nat.size k + (4 * Nat.size cP + 26)`
`Fit.lean:409-410`
```
theorem exists_size_const : ∃ P : ℕ, ∀ k : ℕ,
    Nat.size (dnum (Dupoc k)) ≤ 4 * Nat.size k + P ∧ Nat.size (dnum (Cupod k)) ≤ 4 * Nat.size k + P :=
```
`Fit.lean:436` `lemma exists_linear_size_le (C₀ C₁ : ℕ) : ∃ K, ∀ k ≥ K, C₀ + C₁ * Nat.size k ≤ k`
`Fit.lean:450-452`
```
theorem guard_fits :
    ∃ K, ∀ k ≥ K, ∀ a ≤ 1,
      flen (Rewriting.emb (guardSentenceA a (Dupoc k) (Cupod k)) : Proposition LAct) ≤ k := by
```
`Fit.lean:467-469` `theorem guard_fits' : ∃ K, ∀ k ≥ K, ∀ a ≤ 1, flen (Rewriting.emb (guardSentenceA a (Cupod k) (Dupoc k)) : Proposition LAct) ≤ k`

### 2.6 `Code.lean` / `FitBox.lean` — the translation's box, and why stored numerals are fatal

`Code.lean:126` `noncomputable def numTB (c : ℕ) : ClosedSemiterm LAct 0 := Semiterm.lMap emb (bnumT c)`; `:128 lemma dnumT_eq_numTB (x : ℕ) : dnumT x = numTB (dnum x) := rfl`.
`Code.lean:133-139`
```
noncomputable def relDesc : Semisentence LAct 4 := Semiformula.lMap emb relabelDef.val
noncomputable def evalG : Semisentence LAct 5 := Semiformula.lMap emb evalGraphDef.val
noncomputable def guardCodeG : Semisentence LAct 4 := Semiformula.lMap emb guardCodeGraph.val
noncomputable def lenProvG : Semisentence LAct 2 := Semiformula.lMap emb (lenProvableV TAct).sigma.val
```
`Code.lean:151-152` `noncomputable def descF {n : ℕ} (X T U W : Semiterm LAct Empty (n + 1)) : Semisentence LAct n := ∃¹ (Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#0, T] ⋏ (relDesc ⇜ ![X, U, W, #0]))`
`Code.lean:222-226` (the `.box` clause of `tmpl`)
```
    | .box k ψ =>
        ∃¹ (∃¹ ((progAux .self 0 ⇜ ![#1, #2, #3, #4, #5, #6, #7]) ⋏
          ((progAux .opp 0 ⇜ ![#0, #2, #3, #4, #5, #6, #7]) ⋏
            (∃¹ ((guardCodeG ⇜ ![#0, cl (numTB (⌜tmpl ψ⌝ : ℕ)), #2, #1]) ⋏
              (lenProvG ⇜ ![cl (numTB k), #0]))))))
```
`Code.lean:235` `noncomputable def tcode (φ : PD.Formula) : ℕ := ⌜tmpl φ⌝`; `:281-282 noncomputable def trAt (me opp : PD.Prog) (φ : PD.Formula) : Sentence LAct := tmpl φ ⇜ descTerms (pcode me) (pcode opp)`; `:286-287 theorem quote_trAt (me opp : PD.Prog) (φ : PD.Formula) : (⌜trAt me opp φ⌝ : ℕ) = guardCode (tcode φ) (pcode me) (pcode opp)`.
`Code.lean:44-52` docstring: "WHY `.box` IS EXCLUDED … the translated box carries the CODE of its body as a numeral constant, and codes are not compositional under substitution … This is the same phenomenon as `□A(x)` vs `Prov(sub(⌜A⌝, x))` in provability logic."

`FitBox.lean:445` `lemma fOcc_lenProvableV : FOcc (0 : Fin 2) ((lenProvableV TAct).sigma.val)` (the budget variable occurs, in `n ≤ k`); `:463 lemma quote_numTB (c : ℕ) : (⌜numTB c⌝ : ℕ) = bnum c`; `:584-588 inductive HasBox (k : ℕ) : PD.Formula → Prop`; `:777-778`
```
theorem box_guard_never_fits {k : ℕ} {φ : PD.Formula} (h : HasBox k φ) (k' : ℕ) (p q opp : PD.Prog) :
    k < flen (Rewriting.emb (trAt (.search k' φ p q) opp φ) : Proposition LAct) := by
```
`FitBox.lean:827` `lemma tlen_emb_numTB (c : ℕ) : tlen (Rew.emb (numTB c) : SyntacticSemiterm LAct 0) ≤ 6 * Nat.size c + 1`; `:872 noncomputable def cL : ℕ := flen (Rewriting.emb lenProvG : Semiproposition LAct 2)`; `:884-885 theorem flen_emb_tmpl_box_le (k : ℕ) (ψ : PD.Formula) : flen (Rewriting.emb (tmpl (.box k ψ)) : Semiproposition LAct 6) ≤ cBox ψ + 6 * cL * Nat.size k`; `:896-897 exists_flen_tmpl_box_const`; `:903-907 inductive BudgetLinear : (ℕ → PD.Formula) → Prop` (`const`, `box`, `impl`, `neg`); `:923-924 theorem exists_flen_tmpl_const {F : ℕ → PD.Formula} (h : BudgetLinear F) : ∃ c₀ c₁ : ℕ, ∀ k, flen (Rewriting.emb (tmpl (F k)) : Semiproposition LAct 6) ≤ c₀ + c₁ * Nat.size k`.
The design fix (`FitBox.lean:776-787`, prose): "**Box budgets as node DATA.** Make the box template a SEVEN-variable formula with the box budget as the extra variable (`lenProvG ⇜ ![#6, #0]` instead of `![cl (numTB k), #0]`), and let the search node's own `k` … be substituted by `descVec` at evaluation time … The stored template then does not mention `k` at all, its code is a constant … and `guard_fits` goes through verbatim."

---

## 3. The evaluator

### 3.1 `Eval.lean`

`Eval.lean:36-49` (the operator; search clause at `:46-49`)
```
def Phi (C : Set V) (pr : V) : Prop :=
  (∃ n me opp a, pr = ⟪n + 1, me, opp, pConst a, a⟫) ∨
  …
  (∃ n me opp k g p q a,
    ((LenProvableV TAct k (guardCode g me opp) ∧ ⟪n, me, opp, p, a⟫ ∈ C) ∨
      (¬LenProvableV TAct k (guardCode g me opp) ∧ ⟪n, me, opp, q, a⟫ ∈ C)) ∧
    pr = ⟪n + 1, me, opp, pSearch k g p q, a⟫)
```
Blueprint search clause, Σ side (`Eval.lean:65-68`):
```
      (∃ k < p, ∃ g < p, ∃ p' < p, ∃ q < p, !pSearchGraph p k g p' q ∧
        ∃ gc, !guardCodeGraph gc g me opp ∧
          ((!(lenProvableV TAct).sigma k gc ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨
           (¬!(lenProvableV TAct).pi k gc ∧ ∃ t, !pair₅Def t n me opp q a ∧ t ∈ C))) )”)
```
Π side (`Eval.lean:82-85`):
```
      (∃ k < p, ∃ g < p, ∃ p' < p, ∃ q < p, !pSearchGraph p k g p' q ∧
        ∀ gc, !guardCodeGraph gc g me opp →
          ((!(lenProvableV TAct).pi k gc ∧ ∀ t, !pair₅Def t n me opp p' a → t ∈ C) ∨
           (¬!(lenProvableV TAct).sigma k gc ∧ ∀ t, !pair₅Def t n me opp q a → t ∈ C))) )”)⟩
```
`Eval.lean:183` `instance : construction.Finite V where` (NOT `StrongFinite`).
`Eval.lean:213` `def EvalGraph (n me opp p a : V) : Prop := EvalFix.construction.Fixpoint ![] ⟪n, me, opp, p, a⟫`
`Eval.lean:215-216`
```
noncomputable def evalGraphDef : 𝚺₁.Semisentence 5 := .mkSigma
  “n me opp p a. ∃ pr, !pair₅Def pr n me opp p a ∧ !EvalFix.blueprint.fixpointDef pr”
```
`Eval.lean:222-223` `lemma evalGraph_defined : 𝚺₁.Defined (fun v : Fin 5 → V ↦ EvalGraph (v 0) (v 1) (v 2) (v 3) (v 4)) evalGraphDef`; `:227 instance evalGraph_definable : 𝚺₁-Relation₅[V] EvalGraph`.
`Eval.lean:229-242`
```
lemma EvalGraph.case_iff {n me opp p a : V} :
    EvalGraph n me opp p a ↔
    ∃ n', n = n' + 1 ∧
    ( p = pConst a ∨
      (p = pSelf ∧ EvalGraph n' me opp me a) ∨
      (p = pOpp ∧ EvalGraph n' me opp opp a) ∨
      (∃ p', p = pBot p' ∧ EvalGraph n' me opp p' a) ∨
      (∃ p' q, p = pSim p' q ∧
        EvalGraph n' (psubst me opp p') (psubst me opp q) (psubst me opp p') a) ∨
      (∃ b a' p' q r, p = pIte b a' p' q ∧ EvalGraph n' me opp b r ∧
        ((r = a' ∧ EvalGraph n' me opp p' a) ∨ (r ≠ a' ∧ EvalGraph n' me opp q a))) ∨
      (∃ k g p' q, p = pSearch k g p' q ∧
        ((LenProvableV TAct k (guardCode g me opp) ∧ EvalGraph n' me opp p' a) ∨
         (¬LenProvableV TAct k (guardCode g me opp) ∧ EvalGraph n' me opp q a))) ) := by
```

### 3.2 `EvalN.lean`

Section `inversion` is **V-generic** (`EvalN.lean:17 variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`):
`EvalN.lean:21` `lemma EvalGraph.zero_iff {me opp p a : V} : ¬EvalGraph 0 me opp p a`
`EvalN.lean:26-27` `lemma EvalGraph.const_iff {n me opp a a' : V} : EvalGraph (n + 1) me opp (pConst a) a' ↔ a' = a`
`EvalN.lean:53-56`
```
lemma EvalGraph.search_iff {n me opp k g p q a : V} :
    EvalGraph (n + 1) me opp (pSearch k g p q) a ↔
    ((LenProvableV TAct k (guardCode g me opp) ∧ EvalGraph n me opp p a) ∨
     (¬LenProvableV TAct k (guardCode g me opp) ∧ EvalGraph n me opp q a)) := by
```
(also `self_iff :30`, `opp_iff :34`, `bot_iff :38`, `sim_iff :42`, `ite_iff :47`).
Section `nat` (**ℕ only**): `:66-67 theorem EvalGraph.unique (n : ℕ) : ∀ me opp p a₁ a₂ : ℕ, EvalGraph n me opp p a₁ → EvalGraph n me opp p a₂ → a₁ = a₂`; `:106 theorem EvalGraph.mono (n : ℕ) : ∀ me opp p a : ℕ, EvalGraph n me opp p a → EvalGraph (n + 1) me opp p a`; `:132-133 theorem EvalGraph.mono_le {n n' me opp p a : ℕ} (h : n ≤ n') (e : EvalGraph n me opp p a) : EvalGraph n' me opp p a`; `:139-140 theorem EvalGraph.unique' {n n' me opp p a a' : ℕ} (h : EvalGraph n me opp p a) (h' : EvalGraph n' me opp p a') : a = a'`.

### 3.3 `Det.lean` — determinism in every model, and the completeness-theorem pattern

`Det.lean:57-58` (scope `{V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`)
```
theorem EvalGraph.unique_V' (n : V) : ∀ n' me opp p a₁ a₂ : V,
    EvalGraph n me opp p a₁ → EvalGraph n' me opp p a₂ → a₁ = a₂ := by
  induction n using ISigma1.pi1_order_induction with
  | hP => definability
  | ind n ih =>
```
`Det.lean:100-101` `theorem EvalGraph.unique_V {n me opp p a₁ a₂ : V} (h₁ : EvalGraph n me opp p a₁) (h₂ : EvalGraph n me opp p a₂) : a₁ = a₂`
`Det.lean:115-116` `@[instance_reducible] noncomputable def stdActV : Structure LAct V := Structure.lMap inst (standardModel V)`
`Det.lean:124-125` `lemma models_inst_V (σ : Sentence LAct) : V↓[ℒₒᵣ] ⊧ Semiformula.lMap inst σ ↔ Semiformula.Eval (s := stdActV V) ![] Empty.elim σ`
`Det.lean:144` `lemma val_numT_V (k : ℕ) : (numT k).val (s := stdActV V) ![] Empty.elim = (k : V)`
`Det.lean:153` `theorem val_bnumT_V (n : ℕ) : (bnumT n).val (s := standardModel V) ![] Empty.elim = (n : V) := by`
`Det.lean:177` `lemma val_dnumT_V (x : ℕ) : (dnumT x).val (s := stdActV V) ![] Empty.elim = ((dnum x : ℕ) : V)`
`Det.lean:183-186`
```
lemma cast_relabel (u w x : ℕ) : ((relabel u w x : ℕ) : V) = relabel (u : V) (w : V) (x : V) := by
  have := DefinedFunction.shigmaOne_absolute_func V (relabel_defined (V := ℕ)) (relabel_defined (V := V))
    ![u, w, x]
  simpa [Function.comp_def] using this
```
`Det.lean:189-191`
```
lemma relabel_val_desc_V (x : ℕ) :
    relabel ((dUT x).val (s := stdActV V) ![] Empty.elim) ((dWT x).val (s := stdActV V) ![] Empty.elim)
      ((dnum x : ℕ) : V) = (x : V) := by
```
`Det.lean:225-229`
```
lemma eval_evalG_V (v : Fin 5 → V) :
    Semiformula.Eval (s := stdActV V) v Empty.elim evalG ↔ EvalGraph (v 0) (v 1) (v 2) (v 3) (v 4) := by
  unfold evalG
  rw [Semiformula.eval_lMap, stdActV_lMap_emb]
  exact evalGraph_defined.df v
```
`Det.lean:248-251`
```
theorem models_trAt_plays_V (me' opp' me opp : PD.Prog) (a : PD.Action)
    (hme : Proper me) (hopp : Proper opp) :
    V↓[ℒₒᵣ] ⊧ Semiformula.lMap inst (trAt me' opp' (.plays me opp a)) ↔
      ∃ N : V, EvalGraph N (pcode me : V) (pcode opp : V) (pcode me : V) (actCode a : V) := by
```
**The exact completeness pattern** (`Det.lean:275-296`):
```
theorem models_neg_inst_trAt_plays_V (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (me' opp' me opp : PD.Prog) {b aN : PD.Action} (hne : b ≠ aN)
    (hme : Proper me) (hopp : Proper opp)
    (hpos : 𝗣𝗔 ⊢ Semiformula.lMap inst (trAt me' opp' (.plays me opp b))) :
    V↓[ℒₒᵣ] ⊧ ∼ Semiformula.lMap inst (trAt me' opp' (.plays me opp aN)) := by
  have hV : V↓[ℒₒᵣ] ⊧ Semiformula.lMap inst (trAt me' opp' (.plays me opp b)) :=
    models_of_provable inferInstance hpos
  rw [models_trAt_plays_V me' opp' me opp b hme hopp] at hV
  obtain ⟨N, hN⟩ := hV
  rw [Semantics.Not.models_not, models_trAt_plays_V me' opp' me opp aN hme hopp]
  rintro ⟨N', hN'⟩
  have e : (actCode b : V) = (actCode aN : V) := EvalGraph.unique_V' N N' _ _ _ _ _ hN hN'
  exact hne (actCode_inj (nat_cast_inj.mp e))

theorem pa_proves_neg_trAt_inst_of_pos (me' opp' me opp : PD.Prog) {b aN : PD.Action} (hne : b ≠ aN)
    (hme : Proper me) (hopp : Proper opp)
    (hpos : 𝗣𝗔 ⊢ Semiformula.lMap inst (trAt me' opp' (.plays me opp b))) :
    𝗣𝗔 ⊢ ∼ Semiformula.lMap inst (trAt me' opp' (.plays me opp aN)) :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ ↦
    models_neg_inst_trAt_plays_V V me' opp' me opp hne hme hopp hpos
```
Foundation's theorem behind it, `Foundation/FirstOrder/Arithmetic/Basic/Model.lean:78`:
```
lemma complete (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (φ : ArithmeticSentence) (H : ∀ (M : Type*) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T], M↓[ℒₒᵣ] ⊧ φ) :
```
The same pattern IS how Foundation proves the unbounded HBL conditions (`Foundation/FirstOrder/Incompleteness/StandardProvability.lean:29-34, 59-62, 65-66`):
```
theorem provable_D1 {σ} : T ⊢ σ → 𝗜𝚺₁ ⊢ □σ := fun h ↦
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by simpa [models_iff] using internalize_provability (V := V) h

theorem provable_D2 {σ π} : 𝗜𝚺₁ ⊢ □(σ 🡒 π) 🡒 □σ 🡒 □π :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by simpa [models_iff] using modus_ponens_sentence T

lemma provable_sigma_one_complete [𝗣𝗔⁻ ⪯ T] {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    𝗜𝚺₁ ⊢ σ 🡒 □σ :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using Bootstrapping.Arithmetic.sigma_one_complete (T := T) (V := V) hσ

theorem provable_D3 [𝗣𝗔⁻ ⪯ T] {σ : ArithmeticSentence} :
    𝗜𝚺₁ ⊢ □σ 🡒 □□σ := provable_sigma_one_complete (by simp)
```
with the V-generic internal cut `Foundation/FirstOrder/Bootstrapping/DerivabilityCondition/D2.lean:28-29`:
```
theorem modus_ponens_sentence {σ τ : Sentence L} (hστ : Provable T (⌜σ 🡒 τ⌝ : V)) (hσ : Provable T (⌜σ⌝ : V)) :
    Provable T (⌜τ⌝ : V) := by
```
and the internal calculus `Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean:465-473`: `def Derivation : V → Prop := (construction T).Fixpoint ![]`, `def Derivable (s : V) : Prop := ∃ d, DerivationOf T d s`, `def Proof (d φ : V) : Prop := DerivationOf T d {φ}`, `def Provable (φ : V) : Prop := ∃ d, Proof T d φ`. Foundation's numeral substitution (`Foundation/FirstOrder/Bootstrapping/FixedPoint.lean:22, 29, 41, 54, 128, 130`):
```
noncomputable def substNumeral (φ x : V) : V := subst ℒₒᵣ ?[numeral x] φ
noncomputable def substNumerals (φ : V) (v : Fin k → V) : V := subst ℒₒᵣ (matrixToVec (fun i ↦ numeral (v i))) φ
noncomputable def substNumeralParams (k : ℕ) (φ x : V) : V := subst ℒₒᵣ (matrixToVec (numeral x :> fun i : Fin k ↦ qqBvar i)) φ
instance substNumeral.defined : 𝚺₁-Function₂ (substNumeral : V → V → V) via ssnum := .mk fun v ↦ by simp [ssnum, substNumeral]
noncomputable def fixedpoint (θ : ArithmeticSemisentence 1) : ArithmeticSentence := (diag θ)/[⌜diag θ⌝]
theorem diagonal (θ : ArithmeticSemisentence 1) :
```

---

## 4. ANALYSIS

### (i) The self-guard of `Dupoc k` as a function of `k`; Σ₁-definability

**ANALYSIS.** Unfolding `RedCell.lean:31`, `Fit.lean:375-377`, `Guard.lean:149-153`:

```
Dupoc k = pSearch k ⌜GtmplA 0⌝ (pConst 0) (pConst 1) = ⟪6, k, cP⟫ + 1,   cP = ⟪⌜GtmplA 0⌝, pConst 0, pConst 1⟫
guardCode ⌜GtmplA 0⌝ (Dupoc k) (Dupoc k)
  = subst LAct (bnum (dnum D) ∷ dU D ∷ dW D ∷ bnum (dnum D) ∷ dU D ∷ dW D ∷ 0) ⌜GtmplA 0⌝,   D := Dupoc k
dnum D = min (Dupoc k) (Cupod k)          (swapcode_Dupoc, RedCell.lean:42; dnum, Guard.lean:53)
dU D, dW D ∈ {csym 0, csym 1}             (no tie: pConst 0 ≠ pConst 1 sits in the 2nd/3rd slot of cP,
                                            so Dupoc k ≠ Cupod k)
```
Which of `csym 0`/`csym 1` `dU D` is depends on `Dupoc k < Cupod k`, i.e. on `⟪6, k, cP⟫ < ⟪6, k, cP'⟫` with `cP' = ⟪⌜GtmplA 1⌝, pConst 1, pConst 0⟫`; since `Nat.pair` is strictly monotone in each coordinate this is `cP < cP'`, INDEPENDENT of `k` — so `dU D`, `dW D` are two fixed constants and the only `k`-dependence of the self-guard is through `bnum (dnum (Dupoc k))` in slots 0 and 3. (Not proved anywhere in the package; a two-line lemma.)

By the code equation `quote_guardSentenceA` (`Template.lean:247`) this code is `⌜guardSentenceA 0 (Dupoc k) (Dupoc k)⌝ = ⌜GtmplA 0 ⇜ descTerms (Dupoc k) (Dupoc k)⌝` — at `ℕ` only.

**Σ₁-definability in `k`: YES, with the existing graphs, no new fixpoint.** `pSearchGraph : 𝚺₀.Semisentence 5` (`Prog.lean:63`), `pConstGraph : 𝚺₀.Semisentence 2` (`Prog.lean:43`), `guardCodeGraph : 𝚺₁.Semisentence 4` (`Guard.lean:166`, which already packs `descVecGraph` = `dnumGraph` + `bnumGraph` + `dUGraph` + `dWGraph` + `adjoinDef`, and `substsGraph LAct`). The wanted `σDupoc : 𝚺₁.Semisentence 2` is
```
“y k. ∃ c₀, !pConstGraph c₀ 0 ∧ ∃ c₁, !pConstGraph c₁ 1 ∧ ∃ d, !pSearchGraph d k g₀ c₀ c₁ ∧ !guardCodeGraph y g₀ d d”
```
with `g₀` the numeral of `⌜GtmplA 0⌝` (a closed constant of the DEFINITION — its length is irrelevant to definability; it must NOT be stored as a numeral inside an agent's template, per FitBox). Simplest route: define `DupocV (k : V) : V := pSearch k (⌜GtmplA 0⌝ : V) (pConst 0) (pConst 1)` (V-generic; `⌜GtmplA 0⌝ : V` exists since quotes are V-polymorphic, cf. `quote_Gtmpl` `Template.lean:162`) and `selfGuard (k : V) : V := guardCode ⌜GtmplA 0⌝ (DupocV k) (DupocV k)`; `𝚺₁-Function₁[V] selfGuard` follows from `guardCode.definable` (`Guard.lean:172`) and `pSearch.defined` (`Prog.lean:65`) by the `definability` tactic (composition of Σ₁ functions). At `ℕ`, `DupocV k = Dupoc k` is `rfl`. **What is MISSING:** `Dupoc`/`Cupod` are ℕ-only (`RedCell.lean:31,35`); the V-lift and the `σDupoc` semisentence do not exist.

**Length:** `flen (guardSentenceA 0 (Dupoc k) (Dupoc k)) ≤ 10c + 6c·(2·size (dnum (Dupoc k))) ≤ 10c + 12c·(4·size k + P)` by `exists_guard_const` (`Fit.lean:324`) + `exists_size_const` (`Fit.lean:409`) = `O(size k)`; a `guard_fits_self : ∃ K, ∀ k ≥ K, flen (guardSentenceA 0 (Dupoc k) (Dupoc k)) ≤ k` is `guard_fits` (`Fit.lean:450-465`) with `Cupod k` replaced by `Dupoc k` (the proof uses `hP k` for both slots; with both slots `Dupoc` it uses `h1` twice). Not present; a copy.

### (ii) The cell sentence `∀ x, lenProvableV.sigma x g(x) → evalGraphDef 2 d(x) d(x) d(x) 0`

**ANALYSIS — expressibility: YES, as an `ArithmeticSentence` (over `ℒₒᵣ`), hence over `TAct` via `emb`.** Every ingredient is an `ℒₒᵣ`-semisentence: `lenProvableV TAct : 𝚫₁.Semisentence 2` (`BewV.lean:25` — `T` is only a parameter; `[L.LORDefinable]` makes the definition arithmetic), `evalGraphDef : 𝚺₁.Semisentence 5` (`Eval.lean:215`), `guardCodeGraph`, `pSearchGraph`. The sentence is
```
“∀ x, ∀ d, !DupocGraph d x → ∀ g, !guardCodeGraph g g₀ d d → !(lenProvableV TAct).sigma x g → !evalGraphDef 2 d d d 0”
```
and its `TAct` form is `Semiformula.lMap emb (…)` — exactly how `lenProvG`, `evalG`, `guardCodeG` are built (`Code.lean:133-139`).

**Hierarchy: as written it is Π₂, not Π₁.** `evalGraphDef` is Σ₁ ONLY — the fixpoint is `Finite`, not `StrongFinite` (`Eval.lean:20-22, 183`), so there is no Π₁ side; `∀x (Δ₁ → Σ₁)` is Π₂. `EvalGraph.unique_V'` gives functionality inside every model but not a Π₁ DEFINITION. However at FUEL 2 the consequent is not needed at all: in EVERY model of `𝗜𝚺₁`, `EvalGraph 2 d d d 0 ↔ LenProvableV TAct x (guardCode g₀ d d)` by `EvalGraph.search_iff` + `const_iff` (V-generic, `EvalN.lean:53, 26`), so the displayed implication is a tautology and the SUBSTANTIVE content of the cell is
```
∀ x ≥ N, ∃ g, σDupoc g x ∧ (lenProvableV TAct).sigma x g          — a Π₂ sentence (∀∃),
```
equivalently the parametric box `∀ x ≥ N, □_x guard(x)` of (iii).

**How the `Det.lean` pattern discharges it — and what it cannot.** The pattern is `Arithmetic.complete 𝗣𝗔 σ (fun (V : Type) _ _ ↦ h_V)` (`Det.lean:295-296`; Foundation `Model.lean:78`): supply truth in EVERY model `V ⊧* 𝗣𝗔`. For the evaluator half this works verbatim: inside `V` rewrite `!evalGraphDef …` with `evalGraph_defined.df` (`Eval.lean:222`; the `eval_evalG_V` idiom `Det.lean:225-229`), `!(lenProvableV TAct).sigma` with `(LenProvableV.defined TAct).df`, `!guardCodeGraph` with `guardCode.defined.df`, `!pSearchGraph` with `pSearch.defined.df`, then `EvalGraph.search_iff`/`const_iff` exactly as `red_cell` does at `ℕ` (`RedCell.lean:120-123`, with `EvalGraph.unique_V'` for `unique'`). The result is a `𝗣𝗔`-theorem over `ℒₒᵣ`; to state it over `TAct` use `TAct ⊇ Theory.lMap emb 𝗣𝗔` (`TheoryAct.lean:56`) — an `lMap`-provability transport (Foundation's `Theory.lMap` API; ArithS uses only its model side `models_lMap_emb`, `TheoryAct.lean:38`). Note `Arithmetic.complete` is for `ArithmeticTheory` (over `ℒₒᵣ`); it does not apply to `TAct` directly.
What the pattern CANNOT give is the Löbian core, `∀ x ≥ N, lenProvableV x g(x)`: truth in a model `V` at a NONSTANDARD `x` means a `V`-code `d < fbound x` with `Proof TAct d g(x) ∧ dlen TAct d ≤ x`, where `g(x)` is a nonstandard sentence code — i.e. the whole parametric Löb argument carried out INSIDE `V` on internal derivation codes (Foundation's `Derivation`/`Provable`, `Proof/Basic.lean:465-473`, with the length tracked through the V-generic `DlenGraph.*_iff` clauses, `DerivationLength.lean:274-309`). The completeness theorem converts a V-GENERIC CONSTRUCTION into a PA theorem — it is exactly how Foundation gets `provable_D2` from the V-generic `modus_ponens_sentence` (`StandardProvability.lean:33-34`, `D2.lean:28`) and `provable_D3` from the internal `sigma_one_complete` (`D3.lean:160`). So the M4 route is: make bounded D1/D2/D3 V-generic constructions on codes (`Cut.lean`'s `cutMP` is the META cut on `Derivation2`, `ℕ`-only through `Proof.sound'`/`derivation_quote`; its internal twin = `modus_ponens_sentence` + `DlenGraph.cutRule_iff/wkRule_iff/andIntro_iff/axL_iff` + `setLen` bounds on the two side sequents), then `complete`.

### (iii) What is MISSING for a parametric box

**ANALYSIS.** `Bootstrapping.substNumeral`/`substNumerals`/`substNumeralParams` (`FixedPoint.lean:22,29,41`) are used NOWHERE in ArithS (grep over `arith/ArithS`: the only `subst`-on-codes uses are `guardCode … := subst LAct (descVec me opp) g` `Guard.lean:153`, `!(substsGraph LAct) y w g` `Guard.lean:167`, and `subst LAct w p` in `Subst.lean:132,316`; `Sound.lean:86` uses the meta `substs1`). But `guardCode` IS the same mechanism as `substNumeral φ x = subst ℒₒᵣ ?[numeral x] φ`, with `LAct` for `ℒₒᵣ`, a six-entry vector for `?[·]`, and `bnum` for `numeral`. Hence:

* `□_x ψ(x)` as `∃ g, g = subst LAct (bnum x ∷ 0) ⌜ψ⌝ ∧ LenProvableV TAct x g` is expressible with existing pieces: define `bsubst (φ x : V) : V := subst LAct (bnum x ∷ 0) φ` (the `bnum`-analogue of `substNumeral`; Σ₁ via `bnumGraph` `Bnum.lean:327` + `adjoinDef` + `substsGraph LAct`, with the one-line `.mk fun v ↦ by simp [...]` proof of `guardCode.defined` `Guard.lean:169-170`), then
  `boxB : 𝚺₁.Semisentence 2 := “x φ. ∃ g, !bsubstGraph g φ x ∧ !(lenProvableV TAct).sigma x g”`.
  Nothing of this exists yet. (The `.pi` side is also available since `lenProvableV` is Δ₁, so `boxB` is Δ₁ once `bsubst` is total — it is, `subst` is total.)
* Its `flen` as a function of `x`: the box FORMULA has `x` FREE, so its length is a CONSTANT `cB := flen boxB` (this is the point of the parametric form). Closing it at a budget and a body — `boxB/[bnum-term of x, numeral-term of ⌜ψ⌝]` — costs, by `flen_subst_le` (`Fit.lean:192`), at most `cB · (tlen(bnumT x) + tlen(numeral of ⌜ψ⌝) + 1) ≤ cB · (6·size x + 6·size ⌜ψ⌝ + 3)` PROVIDED `⌜ψ⌝` is also written as a binary numeral (`numTB ⌜ψ⌝`, `Code.lean:126`; `tlen_emb_numTB` `FitBox.lean:827`). With Foundation's unary `numeral ⌜ψ⌝` it is `~2·⌜ψ⌝`, exponential in the size of `ψ` — the retired-`Vacuity` trap again.
* The FitBox warning transfers: the CODE of `bnum x` is `≥ 2^(x+1)` (`FitBox.lean:201`), so `bnum x` may appear only as a RUNTIME-substituted term (like `descVec`), never inside a STORED template constant — the existing `tmpl (.box k ψ)` (`Code.lean:225-226`) stores `cl (numTB k)` and is exactly what `box_guard_never_fits` (`FitBox.lean:777`) kills. A parametric box in a stored template must carry the budget as a 7th VARIABLE and substitute it at evaluation time (the "box budgets as node data" fix, `FitBox.lean:776-787`). The existing `tmpl (.box k ψ)` is already parametric in the PLAYERS (it uses `guardCodeG` on the frame's descriptions, `Code.lean:225`) — only the BUDGET slot is a constant.
* Exactly the instruction "never as a numeral of the code of `ψ(k̄)`" is the `Code.lean:44-52` non-compositionality remark: `Prov(sub(⌜A⌝, x))`, not `⌜A(x̄)⌝`.

### (iv) ℕ-only lemmas that need general-`V` versions for PA-internal reasoning

**ANALYSIS.** V-generic ALREADY: `bnum`, `bnumGraph`, `bnum_two_mul`, `bnum_semiterm` (`Bnum.lean:320-382`); `quote_bnumT` (`Bnum.lean:436`); `dnum/dU/dW/descVec/guardCode` and all their graphs (`Guard.lean`); `dnum_of_lt/eq/gt`, `dnum_swapcode`, `termRelabelVec_descVec`, `guardCode_of_sentence`, `isSemiformula_guardCode`, `gsubst`, `guardCode_gsubst` (`Subst.lean`); `relabel`, `relabel_zero_one`, `swapcode_swapcode`, all `pX` graphs (`Prog.lean`); `EvalGraph.case_iff` and the inversion lemmas (`Eval.lean:229`, `EvalN.lean:15-59`); `EvalGraph.unique_V'` (`Det.lean:57`); `val_bnumT_V`, `val_dnumT_V`, `cast_relabel`, `relabel_val_desc_V`, `val_actT_V`, `eval_evalG_V`, `models_trAt_plays_V` (`Det.lean:144-251`); `eval_gtmpl` (`Template.lean:45`); `quote_Gtmpl`, `quote_numT`, `quote_cterm_C/D` (`Template.lean:162-189`); `termLen_quote`/`formulaLen_quote` (`MetaLength.lean:51,76`); `DlenGraph.*_iff`, `dlen`, `dlen_defined` (`DerivationLength.lean`); `LenProvableV.defined`, `lenProvableV_numeral` (`BewV.lean`); `fbound`, `fbound_defined` (`Proper.lean:581-587`).

ℕ-ONLY, needing a `V` twin for internal reasoning about `bnum/dnum/descVec/guardCode` and the cell:
1. `Template.lean:198 quote_dnumT`, `:204 quote_dUT`, `:212 quote_dWT`, `:220 quote_actT`, `:232 semitermVec_val_descTerms`, `:247 quote_guardSentenceA` — the CODE equations linking `descTerms`/`guardSentenceA` (meta) to `descVec`/`guardCode` (internal) are stated at `ℕ` (they go through `Semiterm.empty_quote_def`/`typed_quote_substs` at `ℕ`). Their `V` forms are needed wherever a `V`-element `guardCode g₀ D D` must be recognised as the quote of a meta sentence — but for a nonstandard `D` there is no meta sentence, so the internal argument should stay on codes and use these only at `ℕ` (as `red_cell` does).
2. `Template.lean:268 val_dnumT`, `:274 relabel_val_desc`, `:301 models_guardSentenceA_iff` — the roadmap's two named items. `Det.lean:177,189` supply `val_dnumT_V`, `relabel_val_desc_V`; a `models_guardSentenceA_iff_V` (truth of `Gtmpl`-based guard sentences in `stdActV V`) does NOT exist — `Det.lean` proved the analogue only for the `Code.lean` translation `trAt`/`tmpl` (`models_trAt_plays_V`), whose shape (`descF`/`progAux`/`evalG`) differs from `Gtmpl` (`Code.lean:696-700` docstring: "two different searchers with provably equivalent guards, not one code").
3. `RedCell.lean:31,35 Dupoc/Cupod` (ℕ), `:42 swapcode_Dupoc`, `:78 lenProvableV_nat`, `:85 lenProvableV_mp`, `:93 evalGraph_of_guard` (uses `models_TAct : ℕ↓[LAct] ⊧* TAct`, soundness — inherently about `ℕ`-truth; its internal analogue is the reflection-free argument via internal soundness of the evaluator clause, not soundness of `TAct`), `:102 guard_Dupoc_iff_guard_Cupod`.
4. `Symmetry.lean` (all): `provableLen_swap`, `lenProvable_fbound_swap(_iff)` rest on `Proof.sound'` (`Sound.lean:118`, `{d : ℕ}`) and the META `transpose_exists`. An internal τ-closure needs `relabelTemplate` (`RelabelTemplate.lean`, on FORMULA codes, V-generic) lifted to DERIVATION codes with a `Derivation`-induction — absent.
5. `Cut.lean` (all code-level theorems): `lenProvable_fbound_mono` (via `fbound_nat`/`F_mono`, ℕ — the `V` version needs monotonicity of `Exp.exp` in `𝗜𝚺₁`), `lenProvable_of_derivation`, `derivation_of_lenProvable`, `lenProvable_mp(_sharp)`, `lenProvable_verum` — all through `Proof.sound'`/`derivation_quote`/`quote_derivation_le`. Internal D2 = `modus_ponens_sentence` (V-generic, `D2.lean:28`) + length accounting via `DlenGraph.cutRule_iff/wkRule_iff/andIntro_iff/axL_iff` and INTERNAL `setLen` insertion bounds (`MetaLength.lean:112-161` is the "Sequents (at V = ℕ)" section; `setLen_insert_of_not_mem :151` is ℕ) — plus the internal code bound `d < fbound x`, i.e. an INTERNAL `quote_derivation_le` (`Proper.lean:399` is a meta estimate on `⌜d⌝ : ℕ`); the properness of `fbound` for `V`-codes is not available.
6. `Fit.lean` (all): meta lengths (`flen`, `tlen`, `Nat.size`); the internal counterpart would be `formulaLen`/`termLen` (`Length.lean`, V-generic) with an internal `formulaLen (subst w φ) ≤ formulaLen φ * (Σ termLen w + 1)` — absent — and an internal `termLen (bnum n) ≤ 6·‖n‖ + 1` (`tlen_bnumT` `Bnum.lean:540` is meta; `‖·‖` = Foundation's `length`).
7. `EvalN.lean:106,132,139 EvalGraph.mono / mono_le / unique'` — fuel MONOTONICITY in `V` (`mono_V`) is missing (only `unique_V'` exists); needed to move between `EvalGraph 2 …` and `∃ n, EvalGraph n …` inside `V` (same `pi1_order_induction` template as `unique_V'`).
8. `Agent.lean:102 models_trAt_of_lenProvableV`, `RedCell.lean:66 models_TAct` — `ℕ`-soundness facts; fine as they are (they are used where `ℕ`-truth is the target).
