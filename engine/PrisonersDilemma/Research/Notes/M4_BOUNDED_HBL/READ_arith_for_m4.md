# READ — inventory of `arith/ArithS/` for M4 (bounded HBL + parametric PBLT)

Read-only report, 2026-09-11, branch `colomban-arith-m3` (engine v4.33.1, Foundation at
`/Users/colomband/wt/arith-lake/packages/Foundation`). Every statement below is VERBATIM
from the source with `file:line` (paths relative to `arith/ArithS/` unless prefixed
`Foundation/`). Paragraphs marked **ANALYSIS** are mine and not in the code.

Module order (`arith/ArithS.lean:1-37`): Basic, Length, SequentLength, DerivationLength,
Bew, MetaLength, Proper, LangAct, TheoryAct, Transpose, Sound, Symmetry, ProofLength, Cut,
RevalueTemplate, Prog, BinNumeral, BewV, Guard, Subst, Eval, EvalN, SimTest, Template, RedCell,
Fit, Code, Neg, Agent, AgentConverse, Inst, Det, FitBox, EngineBridge, Core.Tr, Core.Sound,
Audit.

Two naming corrections to the task brief: `lenBox_nat` lives in `RedCell.lean:78`
(the `ℕ` instance), while `BewV.lean:43` has the `V`-generic `lenBox_numeral`; and
`lenBox_mp` lives in `RedCell.lean:85`, not in `Cut.lean` (Cut imports Symmetry and
ProofLength only, RedCell imports Cut).

---

## 1. The predicate and its metatheory

### 1.1 `Bew.lean` — `LenBoxNat`, Π₁ definition, monotonicity, the `□_k` Gödel sentence

Variables in scope (`Bew.lean:30-32`):
```
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]
```

`Bew.lean:35-36`
```
def LenBoxNat (f : V → V) (k : ℕ) (T : Theory L) [T.Δ₁] (φ : V) : Prop :=
  ∃ d < f (ORingStructure.numeral k), Proof T d φ ∧ proofLen T d ≤ ORingStructure.numeral k
```
`Bew.lean:40-41`
```
noncomputable def lenBoxNat (fDef : 𝚺₁.Semisentence 2) (k : ℕ) : 𝚷₁.Semisentence 1 :=
  .mkPi “φ. ∀ E, !fDef E !k → ∃ d < E, !(proof T).pi d φ ∧ ∀ n, !(proofLenDef T) n d → n ≤ !k”
```
`Bew.lean:44-45`
```
noncomputable abbrev lenProvabilityPred (fDef : 𝚺₁.Semisentence 2) (k : ℕ) (σ : Sentence L) :
    ArithmeticSentence := (lenBoxNat T fDef k).val/[⌜σ⌝]
```
`Bew.lean:49-51`
```
instance LenBoxNat.defined {f : V → V} {fDef : 𝚺₁.Semisentence 2} [𝚺₁-Function₁[V] f via fDef] {k} :
    𝚷₁-Predicate[V] (LenBoxNat f k T) via (lenBoxNat T fDef k) where
  defined {φ} := by simp [lenBoxNat, LenBoxNat, proofLen_defined.iff]
```
`Bew.lean:53-54`
```
lemma LenBoxNat.mono {f : V → V} (hf : Monotone f) {k k' : ℕ} (h : k ≤ k') {φ : V} :
    LenBoxNat f k T φ → LenBoxNat f k' T φ := by
```
`Bew.lean:60`
```
lemma LenBoxNat.provable {f : V → V} {k : ℕ} {φ : V} : LenBoxNat f k T φ → Provable T φ := by
```
`Bew.lean:70-71`
```
noncomputable abbrev lenGödel (fDef : 𝚺₁.Semisentence 2) (k : ℕ) : ArithmeticSentence :=
  fixedpoint (∼(lenBoxNat T fDef k))
```
The three gate theorems (namespace `ArithS.Arithmetic`, `variable {V : Type}`, `{T U : ArithmeticTheory} [T.Δ₁]`, `[𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]` at `Bew.lean:90-92,128`):

`Bew.lean:115-118`
```
lemma models_lenGödel (f : V → V) [𝚺₁-Function₁[V] f via fDef] :
    V↓[ℒₒᵣ] ⊧ lenGödel T fDef k ↔
    ∀ x : V, x < f (ORingStructure.numeral k) →
      ¬(Proof T x (⌜lenGödel T fDef k⌝) ∧ proofLen T x ≤ ORingStructure.numeral k) := by
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
    ∀ b : T ⊢! lenGödel T fDef k, f k ≤ ⌜b⌝ ∨ k < proofLen T (⌜b⌝ : ℕ) := by
```
`Bew.lean:164-165`
```
def Proper (f : ℕ → ℕ) (k : ℕ) (T : ArithmeticTheory) [T.Δ₁] : Prop :=
  ∀ b : T ⊢! lenGödel T fDef k, proofLen T (⌜b⌝ : ℕ) ≤ k → ⌜b⌝ < f k
```
`Bew.lean:170-172`
```
theorem lower_bound_proofLen_proof_lenGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef]
    (hf : Proper (fDef := fDef) f k T) :
    ∀ b : T ⊢! lenGödel T fDef k, k < proofLen T (⌜b⌝ : ℕ) := by
```

### 1.2 `BewV.lean` — the budget as an object variable

`BewV.lean:18-20` scope: `{V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`, `{L} [L.Encodable] [L.LORDefinable]`, `(T : Theory L) [T.Δ₁]`.

`BewV.lean:23`
```
def LenBox (k φ : V) : Prop := ∃ d < codeBound k, Proof T d φ ∧ proofLen T d ≤ k
```
`BewV.lean:25-27`
```
noncomputable def lenBox : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “k φ. ∃ E, !codeBoundDef E k ∧ ∃ d < E, !(proof T).sigma d φ ∧ ∃ n, !(proofLenDef T) n d ∧ n ≤ k”)
  (.mkPi “k φ. ∀ E, !codeBoundDef E k → ∃ d < E, !(proof T).pi d φ ∧ ∀ n, !(proofLenDef T) n d → n ≤ k”)
```
`BewV.lean:29`  `instance LenBox.defined : 𝚫₁-Relation[V] (LenBox T) via lenBox T := .mk`
`BewV.lean:37`  `instance LenBox.definable : 𝚫₁-Relation[V] (LenBox T) := (LenBox.defined T).to_definable`
`BewV.lean:39-40` `instance LenBox.definable' : Γ-[m + 1]-Relation[V] (LenBox T) := (LenBox.definable T).of_deltaOne`
`BewV.lean:43-44`
```
lemma lenBox_numeral (k : ℕ) (φ : V) :
    LenBox T (ORingStructure.numeral k) φ ↔ LenBoxNat (codeBound : V → V) k T φ := Iff.rfl
```
The `.sigma`/`.pi` sides are used by name: `!(lenBox TAct).sigma k gc` / `¬!(lenBox TAct).pi k gc` in the evaluator blueprint (`Eval.lean:67-68, 84-85`), and `lenProvG := Semiformula.lMap emb (lenBox TAct).sigma.val` (`Code.lean:139`).

`RedCell.lean:78-79` (the `ℕ` instance, named as the brief calls it)
```
lemma lenBox_nat (k φ : ℕ) :
    LenBox TAct k φ ↔ LenBoxNat (codeBound : ℕ → ℕ) k TAct φ := by
```

### 1.3 `Proper.lean` — `codeBound`, the towers, `quote_derivation_le`

`Proper.lean:28-29`  `def E (s : ℕ) : ℕ := 2 ^ (2 ^ s)` / `def F (s : ℕ) : ℕ := 2 ^ (2 ^ (2 ^ s))`
`Proper.lean:49`  `lemma F_mono {s t : ℕ} (h : s ≤ t) : F s ≤ F t :=`
`Proper.lean:67` `lemma pair_E {a b s : ℕ} (ha : a ≤ E s) (hb : b ≤ E s) : Nat.pair a b + 1 ≤ E (s + 2)`; `:77` `pair_F` likewise; `:87` `two_pow_E_succ_le_F (s : ℕ) : 2 ^ (E s + 1) ≤ F (s + 1)`.
`Proper.lean:150-151`
```
def SmallCodes (L : Language) [L.Encodable] : Prop :=
  ∀ {k : ℕ} (f : L.Func k), Encodable.encode f ≤ 8
```
`Proper.lean:222-223` `def SmallRelCodes (L : Language) [L.Encodable] : Prop := ∀ {k : ℕ} (r : L.Rel k), Encodable.encode r ≤ 8`
`Proper.lean:170` `theorem quote_term_le (hL : SmallCodes L) {n : ℕ} (t : SyntacticSemiterm L n) :` (bound `E (8 · termLenMeta)`); `:263` `quote_formula_le` (`E (8 · formulaLenMeta)`); `:347` `quote_sequent_le` (`F (8·sequentLenMeta+1)`).
`Proper.lean:399-400`
```
theorem quote_derivation_le (hL : SmallCodes L) (hR : SmallRelCodes L)
    {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : (⌜d⌝ : ℕ) ≤ F (12 * proofLenMeta d) := by
```
`Proper.lean:581` (scope `{V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`)
```
noncomputable def codeBound (k : V) : V := Exp.exp (Exp.exp (Exp.exp (12 * k))) + 1
```
`Proper.lean:583-585`
```
def codeBoundDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y k. ∃ a, !(expDef.ofZero 𝚺₁) a (12 * k) ∧ ∃ b, !(expDef.ofZero 𝚺₁) b a ∧
    ∃ c, !(expDef.ofZero 𝚺₁) c b ∧ y = c + 1”
```
`Proper.lean:587` `instance codeBound_defined : 𝚺₁-Function₁[V] codeBound via codeBoundDef`; `:590` `codeBound_definable`.
`Proper.lean:592` `lemma codeBound_nat (k : ℕ) : codeBound k = F (12 * k) + 1 := by`
`Proper.lean:603-604`
```
theorem properPlayer_of_small (hL : SmallCodes L) (hR : SmallRelCodes L) {k : ℕ} {σ : Sentence L}
    (b : T ⊢! σ) (h : proofLen T (⌜b⌝ : ℕ) ≤ k) : (⌜b⌝ : ℕ) < codeBound k := by
```
`Proper.lean:615,619,622,626` `smallCodes_LOR`, `smallRelCodes_LOR`, `smallCodes_LAct : SmallCodes LAct`, `smallRelCodes_LAct : SmallRelCodes LAct`.
`Proper.lean:639-641`
```
theorem lower_bound_proofLen_proof_lenGödel_codeBound :
    ∀ b : T ⊢! lenGödel T codeBoundDef k, k < proofLen T (⌜b⌝ : ℕ) :=
```

### 1.4 `MetaLength.lean` — `termLenMeta/formulaLenMeta/sequentLenMeta/proofLenMeta`, the quote bridges

`MetaLength.lean:27-30`
```
def termLenMeta {n : ℕ} : SyntacticSemiterm L n → ℕ
  | #x => x + 1
  | &x => x + 1
  | FirstOrder.Semiterm.func _ v => (∑ i, termLenMeta (v i)) + 1
```
`MetaLength.lean:51-52` `theorem termLen_quote {n : ℕ} (t : SyntacticSemiterm L n) : termLen L (⌜t⌝ : V) = ↑(termLenMeta t) := by` (V-generic)
`MetaLength.lean:66-74`
```
def formulaLenMeta {n : ℕ} : Semiproposition L n → ℕ
  | .rel _ v => (∑ i, termLenMeta (v i)) + 1
  | .nrel _ v => (∑ i, termLenMeta (v i)) + 1
  | .verum => 1
  | .falsum => 1
  | .and φ ψ => formulaLenMeta φ + formulaLenMeta ψ + 1
  | .or φ ψ => formulaLenMeta φ + formulaLenMeta ψ + 1
  | .all φ => formulaLenMeta φ + 1
  | .exs φ => formulaLenMeta φ + 1
```
`MetaLength.lean:76-77` `theorem formulaLen_quote {n : ℕ} (φ : Semiproposition L n) : formulaLen L (⌜φ⌝ : V) = ↑(formulaLenMeta φ) := by` (V-generic)
`MetaLength.lean:112` section header `/-! ### Sequents (at V = ℕ) -/`; `:161` `theorem sequentLen_quote (Γ : Finset (Proposition L)) : sequentLen L (⌜Γ⌝ : ℕ) = ∑ φ ∈ Γ, formulaLenMeta φ`; `:151` `sequentLen_insert_of_not_mem` (ℕ).
`MetaLength.lean:180` `abbrev sequentLenMeta (Γ : Finset (Proposition L)) : ℕ := ∑ φ ∈ Γ, formulaLenMeta φ`
`MetaLength.lean:184-194` (one clause per `Derivation2` constructor)
```
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
```
`MetaLength.lean:197` `lemma derivation_quote {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : Derivation T (⌜d⌝ : ℕ) :=`
`MetaLength.lean:201` `theorem proofLen_quote {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : proofLen T (⌜d⌝ : ℕ) = proofLenMeta d := by`

The V-generic code-level length (`DerivationLength.lean`): `:219 def ProofLenGraph (d n : V) : Prop`, `:253 lemma ProofLenGraph.case_iff`, per-rule inversions `:274 ProofLenGraph.axL_iff {s p n : V} : ProofLenGraph L (axL s p) n ↔ n = sequentLen L s + 1`, `:277 verumIntro_iff`, `:280 axm_iff`, `:283 andIntro_iff`, `:288 orIntro_iff`, `:292 allIntro_iff`, `:296 exsIntro_iff`, `:301 wkRule_iff`, `:305 shiftRule_iff`, `:309 cutRule_iff`; `:389 noncomputable def proofLen (d : V) : V`, `:393 theorem proofLen_graph {d : V} (hd : Derivation T d) : ProofLenGraph L d (proofLen T d)`, `:396 proofLen_of_not`, `:399 proofLen_eq_of_graph`, `:404 proofLenDef : 𝚺₁.Semisentence 2`, `:409 instance proofLen_defined`.

### 1.5 `ProofLength.lean`

`ProofLength.lean:25-34` the `@[simp]` `rfl` equations `formulaLenMeta_rel`, `formulaLenMeta_nrel`, `formulaLenMeta_verum`, `formulaLenMeta_falsum`, `formulaLenMeta_and`, `formulaLenMeta_or`, `formulaLenMeta_all`, `formulaLenMeta_exs`.
`ProofLength.lean:43-44`
```
lemma formulaLenMeta_le_proofLenMeta {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) {σ : Proposition L} (h : σ ∈ Γ) :
    formulaLenMeta σ ≤ proofLenMeta d :=
```
`ProofLength.lean:50-51`
```
theorem formulaLenMeta_le_of_lenBoxNat {σ : Sentence LAct} {k : ℕ}
    (h : LenBoxNat (codeBound : ℕ → ℕ) k TAct (⌜σ⌝ : ℕ)) : formulaLenMeta (σ : Proposition LAct) ≤ k := by
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
  ∃ d : ℕ, Proof T d (⌜φ⌝ : ℕ) ∧ proofLen T d ≤ k
```
`Symmetry.lean:38-39` `theorem provableLen_swap_iff (k : ℕ) (φ : Proposition LAct) : ProvableLen TAct k φ ↔ ProvableLen TAct k (Semiformula.lMap swap φ) :=`
`Symmetry.lean:46-48`
```
theorem lenBoxNat_codeBound_swap {k : ℕ} {φ : Sentence LAct}
    (h : LenBoxNat (codeBound : ℕ → ℕ) k TAct (⌜φ⌝ : ℕ)) :
    LenBoxNat (codeBound : ℕ → ℕ) k TAct (⌜Semiformula.lMap swap φ⌝ : ℕ) := by
```
The proof pattern (`Symmetry.lean:49-67`), reused verbatim by `Cut.lean`:
```
  rcases h with ⟨d, hdk, hd, hk⟩
  have e : (ORingStructure.numeral k : ℕ) = k := by simp
  rw [Sentence.quote_def] at hd
  obtain ⟨b, rfl⟩ := Proof.sound' hd
  obtain ⟨b', hb'⟩ := transpose_exists _ b
  rw [proofLen_quote, e] at hk
  have hk' : proofLenMeta b ≤ k := by
    rcases le_def.mp hk with h | h
    · exact Nat.le_of_eq h
    · exact Nat.le_of_lt h
  refine ⟨⌜b'⌝, ?_, ⟨?_, derivation_quote b'⟩, ?_⟩
  · rw [e, codeBound_nat]
    refine Nat.lt_succ_of_le (le_trans (quote_derivation_le smallCodes_LAct smallRelCodes_LAct b')
      (F_mono ?_))
    rw [hb']
    exact Nat.mul_le_mul_left 12 hk'
  · rw [fstIdx_quote b', Sentence.quote_def, ← Semiformula.lMap_emb]
    exact Derivation2.Sequent.quote_singleton _
  · rw [proofLen_quote, hb', e]; exact hk
```
`Symmetry.lean:69-71`
```
theorem lenBoxNat_swap_iff (k : ℕ) (φ : Sentence LAct) :
    LenBoxNat (codeBound : ℕ → ℕ) k TAct (⌜φ⌝ : ℕ) ↔
    LenBoxNat (codeBound : ℕ → ℕ) k TAct (⌜Semiformula.lMap swap φ⌝ : ℕ) :=
```

### 1.8 `Cut.lean` IN FULL (statements)

Scope: `open FFL FFL.FirstOrder Arithmetic Bootstrapping`, `open PeanoMinus`, `open LAct` (`Cut.lean:34-36`); section `formulaLenMeta` has `variable {L : Language} [L.DecidableEq]` (`:42`).

`Cut.lean:46` `lemma formulaLenMeta_neg {n : ℕ} (φ : Semiproposition L n) : formulaLenMeta (∼φ) = formulaLenMeta φ := by`
`Cut.lean:67` `lemma formulaLenMeta_imply {n : ℕ} (φ ψ : Semiproposition L n) : formulaLenMeta (φ 🡒 ψ) = formulaLenMeta φ + formulaLenMeta ψ + 1 := by`
`Cut.lean:71` `lemma sequentLenMeta_singleton (φ : Proposition L) : sequentLenMeta ({φ} : Finset (Proposition L)) = formulaLenMeta φ :=`
`Cut.lean:75-76`
```
lemma sequentLenMeta_insert_le (φ : Proposition L) (Γ : Finset (Proposition L)) :
    sequentLenMeta (insert φ Γ) ≤ formulaLenMeta φ + sequentLenMeta Γ := by
```
Section `proofLenMeta` (`variable {L : Language} [L.DecidableEq] {T : Theory L}`, `:87`):
`Cut.lean:89-90` `lemma proofLenMeta_closed (Γ : Finset (Proposition L)) (φ : Proposition L) (h : φ ∈ Γ) (hn : ∼φ ∈ Γ) : proofLenMeta (Derivation2.closed (T := T) Γ φ h hn) = sequentLenMeta Γ + 1 := by simp [proofLenMeta]`
`Cut.lean:92-93` `lemma proofLenMeta_verum {Γ : Finset (Proposition L)} (h : ⊤ ∈ Γ) : proofLenMeta (Derivation2.verum (T := T) h) = sequentLenMeta Γ + 1 := by simp [proofLenMeta]`
`Cut.lean:95-96` `lemma proofLenMeta_wk {Δ Γ : Finset (Proposition L)} (d : T ⟹₂ Δ) (ss : Δ ⊆ Γ) : proofLenMeta (Derivation2.wk d ss) = sequentLenMeta Γ + proofLenMeta d + 1 := by simp [proofLenMeta]`
`Cut.lean:98-100` `lemma proofLenMeta_and {Γ : Finset (Proposition L)} {φ ψ : Proposition L} (h : φ ⋏ ψ ∈ Γ) (d₁ : T ⟹₂ insert φ Γ) (d₂ : T ⟹₂ insert ψ Γ) : proofLenMeta (Derivation2.and h d₁ d₂) = sequentLenMeta Γ + proofLenMeta d₁ + proofLenMeta d₂ + 1 := by simp [proofLenMeta]`
`Cut.lean:102-104` `lemma proofLenMeta_cut {Γ : Finset (Proposition L)} {φ : Proposition L} (d₁ : T ⟹₂ insert φ Γ) (d₂ : T ⟹₂ insert (∼φ) Γ) : proofLenMeta (Derivation2.cut d₁ d₂) = sequentLenMeta Γ + proofLenMeta d₁ + proofLenMeta d₂ + 1 := by simp [proofLenMeta]`

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
theorem proofLenMeta_cutMP {φ ψ : Proposition L} (d₁ : T ⟹₂ {φ 🡒 ψ}) (d₂ : T ⟹₂ {φ}) :
    proofLenMeta (cutMP d₁ d₂) ≤ proofLenMeta d₁ + proofLenMeta d₂ + 5 * formulaLenMeta φ + 10 * formulaLenMeta ψ + 9 := by
```
Section `code` (`variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]`, `{T : Theory L} [T.Δ₁]`, `:145-146`; all at `ℕ`):

`Cut.lean:151-152`
```
theorem lenBoxNat_codeBound_mono {k k' : ℕ} (h : k ≤ k') {φ : ℕ} :
    LenBoxNat (codeBound : ℕ → ℕ) k T φ → LenBoxNat (codeBound : ℕ → ℕ) k' T φ :=
```
`Cut.lean:164-166`
```
theorem lenBoxNat_of_derivation (hL : SmallCodes L) (hR : SmallRelCodes L)
    {σ : Sentence L} {k : ℕ} (b : T ⟹₂ {(σ : Proposition L)}) (hb : proofLenMeta b ≤ k) :
    LenBoxNat (codeBound : ℕ → ℕ) k T (⌜σ⌝ : ℕ) := by
```
`Cut.lean:179-181`
```
theorem derivation_of_lenBoxNat {σ : Sentence L} {k : ℕ}
    (h : LenBoxNat (codeBound : ℕ → ℕ) k T (⌜σ⌝ : ℕ)) :
    ∃ b : T ⟹₂ {(σ : Proposition L)}, proofLenMeta b ≤ k := by
```
`Cut.lean:193-199`
```
theorem lenBoxNat_mp_sharp_of_small (hL : SmallCodes L) (hR : SmallRelCodes L)
    {k₁ k₂ : ℕ} {φ ψ : Sentence L}
    (h₁ : LenBoxNat (codeBound : ℕ → ℕ) k₁ T (⌜φ 🡒 ψ⌝ : ℕ))
    (h₂ : LenBoxNat (codeBound : ℕ → ℕ) k₂ T (⌜φ⌝ : ℕ)) :
    LenBoxNat (codeBound : ℕ → ℕ)
      (k₁ + k₂ + 5 * formulaLenMeta (φ : Proposition L) + 10 * formulaLenMeta (ψ : Proposition L) + 9)
      T (⌜ψ⌝ : ℕ) := by
```
`Cut.lean:209-210`
```
theorem lenBoxNat_verum_of_small (hL : SmallCodes L) (hR : SmallRelCodes L) :
    LenBoxNat (codeBound : ℕ → ℕ) 2 T (⌜(⊤ : Sentence L)⌝ : ℕ) := by
```
At `TAct` (`Cut.lean:221-226, 234-240, 243-244`):
```
theorem lenBoxNat_mp_sharp {k₁ k₂ : ℕ} {φ ψ : Sentence LAct}
    (h₁ : LenBoxNat (codeBound : ℕ → ℕ) k₁ TAct (⌜φ 🡒 ψ⌝ : ℕ))
    (h₂ : LenBoxNat (codeBound : ℕ → ℕ) k₂ TAct (⌜φ⌝ : ℕ)) :
    LenBoxNat (codeBound : ℕ → ℕ)
      (k₁ + k₂ + 5 * formulaLenMeta (φ : Proposition LAct) + 10 * formulaLenMeta (ψ : Proposition LAct) + 9)
      TAct (⌜ψ⌝ : ℕ) :=
  lenBoxNat_mp_sharp_of_small smallCodes_LAct smallRelCodes_LAct h₁ h₂

theorem lenBoxNat_mp {k₁ k₂ : ℕ} {φ ψ : Sentence LAct}
    (h₁ : LenBoxNat (codeBound : ℕ → ℕ) k₁ TAct (⌜φ 🡒 ψ⌝ : ℕ))
    (h₂ : LenBoxNat (codeBound : ℕ → ℕ) k₂ TAct (⌜φ⌝ : ℕ)) :
    LenBoxNat (codeBound : ℕ → ℕ)
      (k₁ + k₂ + 10 * (formulaLenMeta (φ : Proposition LAct) + formulaLenMeta (ψ : Proposition LAct)) + 9)
      TAct (⌜ψ⌝ : ℕ) :=
  lenBoxNat_codeBound_mono (by omega) (lenBoxNat_mp_sharp h₁ h₂)

theorem lenBoxNat_verum : LenBoxNat (codeBound : ℕ → ℕ) 2 TAct (⌜(⊤ : Sentence LAct)⌝ : ℕ) :=
  lenBoxNat_verum_of_small smallCodes_LAct smallRelCodes_LAct
```
`RedCell.lean:85-88` (the `LenBox` form, ℕ)
```
theorem lenBox_mp {k₁ k₂ : ℕ} {φ ψ : Sentence LAct}
    (h₁ : LenBox TAct k₁ (⌜φ 🡒 ψ⌝ : ℕ)) (h₂ : LenBox TAct k₂ (⌜φ⌝ : ℕ)) :
    LenBox TAct (k₁ + k₂ + 10 * (formulaLenMeta (φ : Proposition LAct) + formulaLenMeta (ψ : Proposition LAct)) + 9)
      (⌜ψ⌝ : ℕ) := by
```
The Cut docstring's own open item (`Cut.lean:24-29` and roadmap `ARITHMETIZED_S_ROADMAP.md:780-781`): "Still open here: D2 as an INTERNAL sentence (`IΣ₁ ⊢ □_a(φ➝ψ) ⋏ □_b φ ➝ □_{…} ψ`), which needs the cut construction formalized inside IΣ₁."

---

## 2. Numerals and descriptions

### 2.1 `BinNumeral.lean` — binary numerals

`BinNumeral.lean:39` `noncomputable def qqTwo : V := (𝟏 : V) ^+ (𝟏 : V)` (notation `𝟐`).
`BinNumeral.lean:50-53`
```
def Phi (C : Set V) (pr : V) : Prop :=
  pr = ⟪(0 : V), (𝟎 : V)⟫ ∨ pr = ⟪(1 : V), (𝟏 : V)⟫ ∨
  (∃ m t, 1 ≤ m ∧ ⟪m, t⟫ ∈ C ∧ pr = ⟪2 * m, 𝟐 ^* t⟫) ∨
  (∃ m t, 1 ≤ m ∧ ⟪m, t⟫ ∈ C ∧ pr = ⟪2 * m + 1, (𝟐 ^* t) ^+ 𝟏⟫)
```
`BinNumeral.lean:55` `noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta …` (Δ₁ core citing `qqAddGraph`/`qqMulGraph` in both polarities, `:56-73`); `:124` `instance : construction.StrongFinite V`.
`BinNumeral.lean:137` `def BinNumeralGraph (n t : V) : Prop := BinNumeral.construction.Fixpoint ![] ⟪n, t⟫`
`BinNumeral.lean:139-141`
```
noncomputable def binNumeralGraphDef : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “n t. ∃ pr <⁺ (n + t + 1)², !pairDef pr n t ∧ !BinNumeral.blueprint.fixpointDefΔ₁.sigma pr”)
  (.mkPi “n t. ∀ pr <⁺ (n + t + 1)², !pairDef pr n t → !BinNumeral.blueprint.fixpointDefΔ₁.pi pr”)
```
`BinNumeral.lean:149` `instance binNumeralGraph_defined : 𝚫₁-Relation[V] BinNumeralGraph via binNumeralGraphDef`
`BinNumeral.lean:320` `noncomputable def binNumeral (n : V) : V := Classical.choose! (binNumeralGraph_existsUnique n)`
`BinNumeral.lean:322` `lemma binNumeral_graph (n : V) : BinNumeralGraph n (binNumeral n)`; `:324` `binNumeral_eq_of_graph`.
`BinNumeral.lean:327` `noncomputable def binNumeralGraph : 𝚺₁.Semisentence 2 := .mkSigma “t n. !binNumeralGraphDef.sigma n t”` (argument order **`t n`**: value first).
`BinNumeral.lean:329` `instance binNumeral.defined : 𝚺₁-Function₁[V] binNumeral via binNumeralGraph`; `:335` `binNumeral.definable`; `:337` `binNumeral.definable'`.
Equations: `:341 binNumeral_zero : binNumeral (0 : V) = 𝟎`, `:343 binNumeral_one : binNumeral (1 : V) = 𝟏`, `:345 binNumeral_two_mul {m : V} (hm : 1 ≤ m) : binNumeral (2 * m) = 𝟐 ^* binNumeral m`, `:348 binNumeral_two_mul_add_one {m : V} (hm : 1 ≤ m) : binNumeral (2 * m + 1) = (𝟐 ^* binNumeral m) ^+ 𝟏`, `:359 binNumeral_even`, `:365 binNumeral_odd`.
`BinNumeral.lean:371` `lemma binNumeral_semiterm (k n : V) : IsSemiterm ℒₒᵣ k (binNumeral n)` (by `ISigma1.pi1_order_induction`); `:382` `binNumeral_uterm`.
`BinNumeral.lean:389` `noncomputable def twoT : ClosedSemiterm ℒₒᵣ 0 := ‘1 + 1’`
`BinNumeral.lean:392-397`
```
noncomputable def binNumeralMeta : ℕ → ClosedSemiterm ℒₒᵣ 0
  | 0 => ‘0’
  | 1 => ‘1’
  | n + 2 =>
    if (n + 2) % 2 = 0 then ‘!!twoT * !!(binNumeralMeta ((n + 2) / 2))’
    else ‘!!twoT * !!(binNumeralMeta ((n + 2) / 2)) + 1’
```
`BinNumeral.lean:436` `theorem quote_binNumeralMeta (n : ℕ) : (⌜binNumeralMeta n⌝ : V) = binNumeral (n : V) := by` (**every model**)
`BinNumeral.lean:461` `theorem val_binNumeralMeta (n : ℕ) : (binNumeralMeta n).val (s := standardModel ℕ) ![] Empty.elim = n := by` (**ℕ only**; V version at `Det.lean:153`)
`BinNumeral.lean:540-541`
```
theorem termLenMeta_binNumeralMeta (n : ℕ) :
    termLenMeta (Rew.emb (binNumeralMeta n) : SyntacticSemiterm ℒₒᵣ 0) ≤ 6 * Nat.size n + 1 := by
```
`Neg.lean:102-103`
```
theorem size_le_termLenMeta_binNumeralMeta (n : ℕ) :
    Nat.size n ≤ termLenMeta (Rew.emb (binNumeralMeta n) : SyntacticSemiterm ℒₒᵣ 0) := by
```
`FitBox.lean:201` `theorem two_pow_succ_le_binNumeral : ∀ n : ℕ, 2 ^ (n + 1) ≤ binNumeral (n : ℕ) := by`
`FitBox.lean:225` `theorem size_binNumeral_ge (n : ℕ) : n + 2 ≤ Nat.size (binNumeral (n : ℕ)) :=`

### 2.2 `Guard.lean` — descriptions and `guardCode` (all V-generic)

`Guard.lean:40` `noncomputable def csym (u : V) : V := ^func 0 (2 + u) 0`; `:42` `csymGraph : 𝚺₁.Semisentence 2 := .mkSigma “y u. !qqFuncDef y 0 (2 + u) 0”`.
`Guard.lean:53` `noncomputable def canonical (x : V) : V := if x ≤ transposeCode x then x else transposeCode x`
`Guard.lean:56-57`
```
noncomputable def revalueU (x : V) : V :=
  if x < transposeCode x then csym 0 else if transposeCode x < x then csym 1 else numeral 0
```
`Guard.lean:60-61`
```
noncomputable def revalueW (x : V) : V :=
  if x < transposeCode x then csym 1 else if transposeCode x < x then csym 0 else numeral 1
```
`Guard.lean:64-65` `noncomputable def actTermCode (a : V) : V := if a = 0 then csym 0 else if a = 1 then csym 1 else numeral a`
`Guard.lean:69-70`
```
noncomputable def canonicalGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ s, !revalueDef s 1 0 x ∧ (x ≤ s → y = x) ∧ (s < x → y = s)”
```
`Guard.lean:86-88`
```
noncomputable def revalueUGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ s, !revalueDef s 1 0 x ∧ ∃ c0, !csymGraph c0 0 ∧ ∃ c1, !csymGraph c1 1 ∧ ∃ z, !numeralGraph z 0 ∧
    (x < s → y = c0) ∧ (s < x → y = c1) ∧ (x = s → y = z)”
```
`Guard.lean:106-108` `revalueWGraph` (same shape, `c1`/`c0` swapped, `!numeralGraph z 1`).
`Guard.lean:72,90,110,130` `instance canonical.defined / revalueU.defined / revalueW.defined / actTermCode.defined : 𝚺₁-Function₁[V] … via …Graph`.
`Guard.lean:149-150`
```
noncomputable def descriptions (me opp : V) : V :=
  binNumeral (canonical me) ∷ revalueU me ∷ revalueW me ∷ binNumeral (canonical opp) ∷ revalueU opp ∷ revalueW opp ∷ 0
```
`Guard.lean:153`
```
noncomputable def guardCode (g me opp : V) : V := subst LAct (descriptions me opp) g
```
`Guard.lean:155-159`
```
noncomputable def descriptionsGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y me opp. ∃ n₁, !canonicalGraph n₁ me ∧ ∃ t₁, !binNumeralGraph t₁ n₁ ∧ ∃ u₁, !revalueUGraph u₁ me ∧ ∃ w₁, !revalueWGraph w₁ me ∧
    ∃ n₂, !canonicalGraph n₂ opp ∧ ∃ t₂, !binNumeralGraph t₂ n₂ ∧ ∃ u₂, !revalueUGraph u₂ opp ∧ ∃ w₂, !revalueWGraph w₂ opp ∧
    ∃ v₅, !adjoinDef v₅ w₂ 0 ∧ ∃ v₄, !adjoinDef v₄ u₂ v₅ ∧
    ∃ v₃, !adjoinDef v₃ t₂ v₄ ∧ ∃ v₂, !adjoinDef v₂ w₁ v₃ ∧ ∃ v₁, !adjoinDef v₁ u₁ v₂ ∧ !adjoinDef y t₁ v₁”
```
`Guard.lean:161-162` `instance descriptions.defined : 𝚺₁-Function₂ (descriptions : V → V → V) via descriptionsGraph := .mk fun v ↦ by simp [descriptionsGraph, descriptions]`
`Guard.lean:166-167`
```
noncomputable def guardCodeGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y g me opp. ∃ w, !descriptionsGraph w me opp ∧ !(substsGraph LAct) y w g”
```
`Guard.lean:169-170` `instance guardCode.defined : 𝚺₁-Function₃ (guardCode : V → V → V → V) via guardCodeGraph := .mk fun v ↦ by simp [guardCodeGraph, guardCode]`; `:172` `guardCode.definable`; `:175` `guardCode.definable'`.

Supporting V-generic facts in `Subst.lean`: `:120-122 lemma isSemiformula_guardCode {g : V} (hg : IsSemiformula LAct 6 g) (me opp : V) : IsSemiformula LAct 0 (guardCode g me opp)`; `:131-132 lemma subst_eq_self_of_le {n w p : V} (hp : IsSemiformula LAct n p) : IsUTermVec LAct (len w) w → n ≤ len w → (∀ i < n, w.[i] = ^#i) → subst LAct w p = p`; `:180-182 lemma guardCode_of_sentence {g : V} (hg : IsSemiformula LAct 0 g) (me opp : V) : guardCode g me opp = g`; `:189-190 noncomputable def substTemplate (me opp g : V) : V := if IsSemiformula LAct 6 g then guardCode g me opp else g`; `:192-193 substTemplate_of_template`; `:205-206 theorem guardCode_substTemplate {g : V} (hg : IsSemiformula LAct 6 g) (me opp me' opp' : V) : guardCode (substTemplate me opp g) me' opp' = substTemplate me opp g`; `:399 canonical_of_lt {x : V} (h : x < transposeCode x) : canonical x = x`, `:402 canonical_of_eq`, `:405 canonical_of_gt {x : V} (h : transposeCode x < x) : canonical x = transposeCode x`, `:413 lemma canonical_transposeCode (x : V) : canonical (transposeCode x) = canonical x`; `:476-477 theorem termRelabelVec_descriptions (me opp : V) : termRelabelVec 1 0 6 (descriptions me opp) = descriptions (transposeCode me) (transposeCode opp)`.

Program codes (`Prog.lean`, V-generic): `:33 pConst (a : V) : V := ⟪0, a⟫ + 1`, `:39 pSearch (k g p q : V) : V := ⟪6, k, g, p, q⟫ + 1`; graphs `:43 pConstGraph : 𝚺₀.Semisentence 2 := .mkSigma “y a. ∃ y' < y, !pairDef y' 0 a ∧ y = y' + 1”`, `:63-64 pSearchGraph : 𝚺₀.Semisentence 5 := .mkSigma “y k g p q. ∃ y' < y, !pair₅Def y' 6 k g p q ∧ y = y' + 1”`, `:65 instance pSearch.defined : 𝚺₀-Function₄ (pSearch : V → V → V → V → V) via pSearchGraph`; `:483 noncomputable def revalue (u w x : V) : V`, `:491 revalueDef : 𝚺₁.Semisentence 4 := .mkSigma “y u w x. !revalueGraphDef.sigma u w x y”`, `:519 @[simp] lemma revalue_search (u w k g p q : V)`, `:527 theorem revalue_zero_one (x : V) : revalue 0 1 x = x`, `:543 noncomputable abbrev transposeCode (x : V) : V := revalue 1 0 x`, `:546 theorem transposeCode_transposeCode (x : V) : transposeCode (transposeCode x) = x`.

### 2.3 `Template.lean` — the restricted template, its instances, the three equations

`Template.lean:37-39`
```
noncomputable def guardTemplateRaw : 𝚺₁.Semisentence 7 := .mkSigma
  “x₁ u₁ w₁ x₂ u₂ w₂ t. ∃ me, !revalueDef me u₁ w₁ x₁ ∧ ∃ opp, !revalueDef opp u₂ w₂ x₂ ∧
    ∃ n, !evalGraphDef n opp me opp t”
```
`Template.lean:45-47` (V-generic)
```
lemma eval_guardTemplateRaw (v : Fin 7 → V) :
    V ⊧/v guardTemplateRaw.val ↔
    ∃ n, EvalGraph n (revalue (v 4) (v 5) (v 3)) (revalue (v 1) (v 2) (v 0)) (revalue (v 4) (v 5) (v 3)) (v 6) := by
```
`Template.lean:53` `noncomputable def guardTemplate7 : Semisentence LAct 7 := Semiformula.lMap emb guardTemplateRaw.val`
`Template.lean:60` `noncomputable def numT (k : ℕ) : ClosedSemiterm LAct 0 := Semiterm.lMap emb (↑k : ClosedSemiterm ℒₒᵣ 0)` (UNARY; only used in the tie case and `actT` for `a ≥ 2`)
`Template.lean:63` `noncomputable def canonicalMeta (x : ℕ) : ClosedSemiterm LAct 0 := Semiterm.lMap emb (binNumeralMeta (canonical x))`
`Template.lean:66-67` `noncomputable def revalueUMeta (x : ℕ) : ClosedSemiterm LAct 0 := if x < transposeCode x then cterm Act.C else if transposeCode x < x then cterm Act.D else numT 0`
`Template.lean:70-71` `revalueWMeta` (C/D swapped, `numT 1`).
`Template.lean:74-75` `noncomputable def actT (a : ℕ) : ClosedSemiterm LAct 0 := if a = 0 then cterm Act.C else if a = 1 then cterm Act.D else numT a`
`Template.lean:78` `noncomputable def actT6 (a : ℕ) : Semiterm LAct Empty 6 := Rew.castLE (Nat.zero_le 6) (actT a)`
`Template.lean:82-83`
```
noncomputable def GtmplA (a : ℕ) : Semisentence LAct 6 :=
  guardTemplate7 ⇜ ![#0, #1, #2, #3, #4, #5, actT6 a]
```
`Template.lean:86-87`
```
noncomputable def descriptionTerms (me opp : ℕ) : Fin 6 → ClosedSemiterm LAct 0 :=
  ![canonicalMeta me, revalueUMeta me, revalueWMeta me, canonicalMeta opp, revalueUMeta opp, revalueWMeta opp]
```
`Template.lean:90` `noncomputable def guardSentence (a me opp : ℕ) : Sentence LAct := GtmplA a ⇜ descriptionTerms me opp`
`Template.lean:132` `theorem lMap_swap_GtmplA (a : ℕ) : Semiformula.lMap swap (GtmplA a) = GtmplA (swapAction a) := by`
`Template.lean:141-143`
```
theorem lMap_swap_guardSentence (a me opp : ℕ) :
    Semiformula.lMap swap (guardSentence a me opp) =
    guardSentence (swapAction a) (transposeCode me) (transposeCode opp) := by
```
`Template.lean:152-153` `theorem revalueTemplate_quote_GtmplA (a : ℕ) : revalueTemplate 1 0 (⌜GtmplA a⌝ : ℕ) = ⌜GtmplA (swapAction a)⌝ := by`
V-generic code lemmas: `:162 lemma quote_guardTemplate7 : (⌜guardTemplate7⌝ : V) = ⌜guardTemplateRaw.val⌝`, `:173 lemma quote_numT (k : ℕ) : (⌜numT k⌝ : V) = numeral (k : V)`, `:183 quote_cterm_C : (⌜(cterm Act.C : ClosedSemiterm LAct 0)⌝ : V) = csym 0`, `:189 quote_cterm_D … = csym 1`.
ℕ-only code lemmas: `:198 lemma quote_canonicalMeta (x : ℕ) : (⌜canonicalMeta x⌝ : ℕ) = binNumeral (canonical x)`, `:204 quote_revalueUMeta (x : ℕ) : (⌜revalueUMeta x⌝ : ℕ) = revalueU x`, `:212 quote_revalueWMeta`, `:220 quote_actT (a : ℕ) : (⌜actT a⌝ : ℕ) = actTermCode a`, `:232-234 semitermVec_val_descriptionTerms (me opp : ℕ) : SemitermVec.val (fun i ↦ (⌜(Rew.emb (descriptionTerms me opp i) : SyntacticSemiterm LAct 0)⌝ : Bootstrapping.Semiterm ℕ LAct 0)) = descriptions me opp`.
`Template.lean:247-248` (**the code equation**, ℕ)
```
theorem quote_guardSentence (a me opp : ℕ) :
    (⌜guardSentence a me opp⌝ : ℕ) = guardCode (⌜GtmplA a⌝ : ℕ) me opp := by
```
ℕ-only truth lemmas (`stdReadingNat`): `:260 val_numT`, `:265-266 val_cterm_C/D`, `:268 lemma val_canonicalMeta (x : ℕ) : (canonicalMeta x).val (s := stdReadingNat) ![] Empty.elim = canonical x`, `:274-275 lemma revalue_val_desc (x : ℕ) : revalue ((revalueUMeta x).val (s := stdReadingNat) ![] Empty.elim) ((revalueWMeta x).val (s := stdReadingNat) ![] Empty.elim) (canonical x) = x`, `:287 val_actT`, `:295 val_actT6`.
`Template.lean:301-302` (**the truth equation**, ℕ)
```
theorem models_guardSentence_iff (a me opp : ℕ) :
    ℕ↓[LAct] ⊧ guardSentence a me opp ↔ ∃ n, EvalGraph n opp me opp a := by
```

### 2.4 `RedCell.lean` IN FULL (statements)

`RedCell.lean:31` `noncomputable def Dupoc (k : ℕ) : ℕ := pSearch k (⌜GtmplA 0⌝ : ℕ) (pConst 0) (pConst 1)`
`RedCell.lean:35` `noncomputable def Cupod (k : ℕ) : ℕ := pSearch k (⌜GtmplA 1⌝ : ℕ) (pConst 1) (pConst 0)`
`RedCell.lean:37-38` `lemma swapAction_zero : swapAction (0 : ℕ) = 1` / `lemma swapAction_one : swapAction (1 : ℕ) = 0`
`RedCell.lean:42` `theorem transposeCode_Dupoc (k : ℕ) : transposeCode (Dupoc k) = Cupod k := by` (proof `unfold Dupoc Cupod transposeCode; rw [revalue_search, revalue_const, revalue_const, revalueTemplate_quote_GtmplA, swapAction_zero]; simp [revalueAction]`, `:43-45`)
`RedCell.lean:47` `theorem transposeCode_Cupod (k : ℕ) : transposeCode (Cupod k) = Dupoc k := by`
`RedCell.lean:52,59` `lemma models_constNe : ℕ↓[LAct] ⊧ constNe` / `models_constNe'`
`RedCell.lean:66` `instance models_TAct : ℕ↓[LAct] ⊧* TAct := by`
`RedCell.lean:78-79` `lenBox_nat` (quoted in §1.2); `:85-88` `lenBox_mp` (quoted in §1.8).
`RedCell.lean:93-95`
```
theorem evalGraph_of_guard {k me opp a : ℕ}
    (h : LenBox TAct k (guardCode (⌜GtmplA a⌝ : ℕ) me opp)) :
    ∃ n, EvalGraph n opp me opp a := by
  rw [← quote_guardSentence, lenBox_nat] at h
  have hp : TAct ⊢ guardSentence a me opp := provable_iff_provable.mp h.provable
  exact (models_guardSentence_iff a me opp).mp (models_of_provable models_TAct hp)
```
`RedCell.lean:102-106`
```
theorem guard_Dupoc_iff_guard_Cupod (k : ℕ) :
    LenBox TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) (Cupod k)) ↔
    LenBox TAct k (guardCode (⌜GtmplA 1⌝ : ℕ) (Cupod k) (Dupoc k)) := by
  rw [← quote_guardSentence, ← quote_guardSentence, lenBox_nat, lenBox_nat,
    lenBoxNat_swap_iff, lMap_swap_guardSentence, transposeCode_Dupoc, transposeCode_Cupod, swapAction_zero]
```
`RedCell.lean:112-133`
```
theorem red_cell (k : ℕ) :
    EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 1 ∧ EvalGraph 2 (Cupod k) (Dupoc k) (Cupod k) 0 := by
  have hG : ¬LenBox TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) (Cupod k)) := by
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
  have hG' : ¬LenBox TAct k (guardCode (⌜GtmplA 1⌝ : ℕ) (Cupod k) (Dupoc k)) :=
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
theorem formulaLenMeta_subst_le {k : ℕ} (φ : Semisentence L k) (w : Fin k → ClosedSemiterm L 0) :
    formulaLenMeta (Rewriting.emb (φ ⇜ w) : Proposition L) ≤
    formulaLenMeta (Rewriting.emb φ : Semiproposition L k) *
      (∑ i, termLenMeta (Rew.emb (w i) : SyntacticSemiterm L 0) + 1) := by
```
`Fit.lean:211-212` `lemma termLenMeta_emb_canonicalMeta (x : ℕ) : termLenMeta (Rew.emb (canonicalMeta x) : SyntacticSemiterm LAct 0) ≤ 6 * Nat.size (canonical x) + 1`; `:257 termLenMeta_emb_revalueUMeta (x : ℕ) : … ≤ 1`; `:264 termLenMeta_emb_revalueWMeta`.
`Fit.lean:279-281`
```
theorem sum_termLenMeta_descriptionTerms_le (me opp : ℕ) :
    ∑ i, termLenMeta (Rew.emb (descriptionTerms me opp i) : SyntacticSemiterm LAct 0) ≤
    6 * (Nat.size (canonical me) + Nat.size (canonical opp)) + 6 := by
```
`Fit.lean:297` `noncomputable def cG (a : ℕ) : ℕ := formulaLenMeta (Rewriting.emb (GtmplA a) : Semiproposition LAct 6)` — `attribute [irreducible] cG` at `:310` (proof-craft: never evaluate).
`Fit.lean:300-302`
```
theorem formulaLenMeta_guardSentence_le' (me opp a : ℕ) :
    formulaLenMeta (Rewriting.emb (guardSentence a me opp) : Proposition LAct) ≤
    cG a * (6 * (Nat.size (canonical me) + Nat.size (canonical opp)) + 7) :=
```
`Fit.lean:324-326`
```
theorem exists_guard_const : ∃ c : ℕ, ∀ me opp a : ℕ, a ≤ 1 →
    formulaLenMeta (Rewriting.emb (guardSentence a me opp) : Proposition LAct) ≤
    10 * c + 6 * c * (Nat.size (canonical me) + Nat.size (canonical opp)) :=
```
`Fit.lean:375` `noncomputable def cP : ℕ := ⟪(⌜GtmplA 0⌝ : ℕ), pConst 0, pConst 1⟫`; `:377 lemma Dupoc_eq (k : ℕ) : Dupoc k = ⟪6, k, cP⟫ + 1 := rfl`; `:380 attribute [irreducible] cP`.
`Fit.lean:383` `lemma canonical_le_self (x : ℕ) : canonical x ≤ x`
`Fit.lean:389` `theorem size_Dupoc_le (k : ℕ) : Nat.size (Dupoc k) ≤ 4 * Nat.size k + (4 * Nat.size cP + 26)`
`Fit.lean:398-399`
```
theorem size_canonical_Dupoc_le (k : ℕ) :
    Nat.size (canonical (Dupoc k)) ≤ 4 * Nat.size k + (4 * Nat.size cP + 26) :=
```
`Fit.lean:402-403` `theorem size_canonical_Cupod_le (k : ℕ) : Nat.size (canonical (Cupod k)) ≤ 4 * Nat.size k + (4 * Nat.size cP + 26)`
`Fit.lean:409-410`
```
theorem exists_size_const : ∃ P : ℕ, ∀ k : ℕ,
    Nat.size (canonical (Dupoc k)) ≤ 4 * Nat.size k + P ∧ Nat.size (canonical (Cupod k)) ≤ 4 * Nat.size k + P :=
```
`Fit.lean:436` `lemma exists_linear_size_le (C₀ C₁ : ℕ) : ∃ K, ∀ k ≥ K, C₀ + C₁ * Nat.size k ≤ k`
`Fit.lean:450-452`
```
theorem guard_fits :
    ∃ K, ∀ k ≥ K, ∀ a ≤ 1,
      formulaLenMeta (Rewriting.emb (guardSentence a (Dupoc k) (Cupod k)) : Proposition LAct) ≤ k := by
```
`Fit.lean:467-469` `theorem guard_fits' : ∃ K, ∀ k ≥ K, ∀ a ≤ 1, formulaLenMeta (Rewriting.emb (guardSentence a (Cupod k) (Dupoc k)) : Proposition LAct) ≤ k`

### 2.6 `Code.lean` / `FitBox.lean` — the translation's box, and why stored numerals are fatal

`Code.lean:126` `noncomputable def numTB (c : ℕ) : ClosedSemiterm LAct 0 := Semiterm.lMap emb (binNumeralMeta c)`; `:128 lemma canonicalMeta_eq_numTB (x : ℕ) : canonicalMeta x = numTB (canonical x) := rfl`.
`Code.lean:133-139`
```
noncomputable def relDesc : Semisentence LAct 4 := Semiformula.lMap emb revalueDef.val
noncomputable def evalG : Semisentence LAct 5 := Semiformula.lMap emb evalGraphDef.val
noncomputable def guardCodeG : Semisentence LAct 4 := Semiformula.lMap emb guardCodeGraph.val
noncomputable def lenProvG : Semisentence LAct 2 := Semiformula.lMap emb (lenBox TAct).sigma.val
```
`Code.lean:151-152` `noncomputable def descF {n : ℕ} (X T U W : Semiterm LAct Empty (n + 1)) : Semisentence LAct n := ∃¹ (Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#0, T] ⋏ (relDesc ⇜ ![X, U, W, #0]))`
`Code.lean:222-226` (the `.box` clause of `template`)
```
    | .box k ψ =>
        ∃¹ (∃¹ ((progAux .self 0 ⇜ ![#1, #2, #3, #4, #5, #6, #7]) ⋏
          ((progAux .opp 0 ⇜ ![#0, #2, #3, #4, #5, #6, #7]) ⋏
            (∃¹ ((guardCodeG ⇜ ![#0, cl (numTB (⌜template ψ⌝ : ℕ)), #2, #1]) ⋏
              (lenProvG ⇜ ![cl (numTB k), #0]))))))
```
`Code.lean:235` `noncomputable def templateCode (φ : PD.Formula) : ℕ := ⌜template φ⌝`; `:281-282 noncomputable def sentenceAt (me opp : PD.Prog) (φ : PD.Formula) : Sentence LAct := template φ ⇜ descriptionTerms (progCode me) (progCode opp)`; `:286-287 theorem quote_sentenceAt (me opp : PD.Prog) (φ : PD.Formula) : (⌜sentenceAt me opp φ⌝ : ℕ) = guardCode (templateCode φ) (progCode me) (progCode opp)`.
`Code.lean:44-52` docstring: "WHY `.box` IS EXCLUDED … the translated box carries the CODE of its body as a numeral constant, and codes are not compositional under substitution … This is the same phenomenon as `□A(x)` vs `Prov(sub(⌜A⌝, x))` in provability logic."

`FitBox.lean:445` `lemma fOcc_lenBox : FOcc (0 : Fin 2) ((lenBox TAct).sigma.val)` (the budget variable occurs, in `n ≤ k`); `:463 lemma quote_numTB (c : ℕ) : (⌜numTB c⌝ : ℕ) = binNumeral c`; `:584-588 inductive HasBox (k : ℕ) : PD.Formula → Prop`; `:777-778`
```
theorem box_guard_never_fits {k : ℕ} {φ : PD.Formula} (h : HasBox k φ) (k' : ℕ) (p q opp : PD.Prog) :
    k < formulaLenMeta (Rewriting.emb (sentenceAt (.search k' φ p q) opp φ) : Proposition LAct) := by
```
`FitBox.lean:827` `lemma termLenMeta_emb_numTB (c : ℕ) : termLenMeta (Rew.emb (numTB c) : SyntacticSemiterm LAct 0) ≤ 6 * Nat.size c + 1`; `:872 noncomputable def cL : ℕ := formulaLenMeta (Rewriting.emb lenProvG : Semiproposition LAct 2)`; `:884-885 theorem formulaLenMeta_emb_template_box_le (k : ℕ) (ψ : PD.Formula) : formulaLenMeta (Rewriting.emb (template (.box k ψ)) : Semiproposition LAct 6) ≤ cBox ψ + 6 * cL * Nat.size k`; `:896-897 exists_formulaLenMeta_template_box_const`; `:903-907 inductive BudgetLinear : (ℕ → PD.Formula) → Prop` (`const`, `box`, `impl`, `neg`); `:923-924 theorem exists_formulaLenMeta_template_const {F : ℕ → PD.Formula} (h : BudgetLinear F) : ∃ c₀ c₁ : ℕ, ∀ k, formulaLenMeta (Rewriting.emb (template (F k)) : Semiproposition LAct 6) ≤ c₀ + c₁ * Nat.size k`.
The design fix (`FitBox.lean:776-787`, prose): "**Box budgets as node DATA.** Make the box template a SEVEN-variable formula with the box budget as the extra variable (`lenProvG ⇜ ![#6, #0]` instead of `![cl (numTB k), #0]`), and let the search node's own `k` … be substituted by `descriptions` at evaluation time … The stored template then does not mention `k` at all, its code is a constant … and `guard_fits` goes through verbatim."

---

## 3. The evaluator

### 3.1 `Eval.lean`

`Eval.lean:36-49` (the operator; search clause at `:46-49`)
```
def Phi (C : Set V) (pr : V) : Prop :=
  (∃ n me opp a, pr = ⟪n + 1, me, opp, pConst a, a⟫) ∨
  …
  (∃ n me opp k g p q a,
    ((LenBox TAct k (guardCode g me opp) ∧ ⟪n, me, opp, p, a⟫ ∈ C) ∨
      (¬LenBox TAct k (guardCode g me opp) ∧ ⟪n, me, opp, q, a⟫ ∈ C)) ∧
    pr = ⟪n + 1, me, opp, pSearch k g p q, a⟫)
```
Blueprint search clause, Σ side (`Eval.lean:65-68`):
```
      (∃ k < p, ∃ g < p, ∃ p' < p, ∃ q < p, !pSearchGraph p k g p' q ∧
        ∃ gc, !guardCodeGraph gc g me opp ∧
          ((!(lenBox TAct).sigma k gc ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨
           (¬!(lenBox TAct).pi k gc ∧ ∃ t, !pair₅Def t n me opp q a ∧ t ∈ C))) )”)
```
Π side (`Eval.lean:82-85`):
```
      (∃ k < p, ∃ g < p, ∃ p' < p, ∃ q < p, !pSearchGraph p k g p' q ∧
        ∀ gc, !guardCodeGraph gc g me opp →
          ((!(lenBox TAct).pi k gc ∧ ∀ t, !pair₅Def t n me opp p' a → t ∈ C) ∨
           (¬!(lenBox TAct).sigma k gc ∧ ∀ t, !pair₅Def t n me opp q a → t ∈ C))) )”)⟩
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
        EvalGraph n' (substCode me opp p') (substCode me opp q) (substCode me opp p') a) ∨
      (∃ b a' p' q r, p = pIte b a' p' q ∧ EvalGraph n' me opp b r ∧
        ((r = a' ∧ EvalGraph n' me opp p' a) ∨ (r ≠ a' ∧ EvalGraph n' me opp q a))) ∨
      (∃ k g p' q, p = pSearch k g p' q ∧
        ((LenBox TAct k (guardCode g me opp) ∧ EvalGraph n' me opp p' a) ∨
         (¬LenBox TAct k (guardCode g me opp) ∧ EvalGraph n' me opp q a))) ) := by
```

### 3.2 `EvalN.lean`

Section `inversion` is **V-generic** (`EvalN.lean:17 variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`):
`EvalN.lean:21` `lemma EvalGraph.zero_iff {me opp p a : V} : ¬EvalGraph 0 me opp p a`
`EvalN.lean:26-27` `lemma EvalGraph.const_iff {n me opp a a' : V} : EvalGraph (n + 1) me opp (pConst a) a' ↔ a' = a`
`EvalN.lean:53-56`
```
lemma EvalGraph.search_iff {n me opp k g p q a : V} :
    EvalGraph (n + 1) me opp (pSearch k g p q) a ↔
    ((LenBox TAct k (guardCode g me opp) ∧ EvalGraph n me opp p a) ∨
     (¬LenBox TAct k (guardCode g me opp) ∧ EvalGraph n me opp q a)) := by
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
`Det.lean:115-116` `@[instance_reducible] noncomputable def stdReadingV : Structure LAct V := Structure.lMap inst (standardModel V)`
`Det.lean:124-125` `lemma models_inst_V (σ : Sentence LAct) : V↓[ℒₒᵣ] ⊧ Semiformula.lMap inst σ ↔ Semiformula.Eval (s := stdReadingV V) ![] Empty.elim σ`
`Det.lean:144` `lemma val_numT_V (k : ℕ) : (numT k).val (s := stdReadingV V) ![] Empty.elim = (k : V)`
`Det.lean:153` `theorem val_binNumeralMeta_V (n : ℕ) : (binNumeralMeta n).val (s := standardModel V) ![] Empty.elim = (n : V) := by`
`Det.lean:177` `lemma val_canonicalMeta_V (x : ℕ) : (canonicalMeta x).val (s := stdReadingV V) ![] Empty.elim = ((canonical x : ℕ) : V)`
`Det.lean:183-186`
```
lemma cast_revalue (u w x : ℕ) : ((revalue u w x : ℕ) : V) = revalue (u : V) (w : V) (x : V) := by
  have := DefinedFunction.shigmaOne_absolute_func V (revalue_defined (V := ℕ)) (revalue_defined (V := V))
    ![u, w, x]
  simpa [Function.comp_def] using this
```
`Det.lean:189-191`
```
lemma revalue_val_desc_V (x : ℕ) :
    revalue ((revalueUMeta x).val (s := stdReadingV V) ![] Empty.elim) ((revalueWMeta x).val (s := stdReadingV V) ![] Empty.elim)
      ((canonical x : ℕ) : V) = (x : V) := by
```
`Det.lean:225-229`
```
lemma eval_evalG_V (v : Fin 5 → V) :
    Semiformula.Eval (s := stdReadingV V) v Empty.elim evalG ↔ EvalGraph (v 0) (v 1) (v 2) (v 3) (v 4) := by
  unfold evalG
  rw [Semiformula.eval_lMap, stdReadingV_lMap_emb]
  exact evalGraph_defined.df v
```
`Det.lean:248-251`
```
theorem models_sentenceAt_plays_V (me' opp' me opp : PD.Prog) (a : PD.Action)
    (hme : Proper me) (hopp : Proper opp) :
    V↓[ℒₒᵣ] ⊧ Semiformula.lMap inst (sentenceAt me' opp' (.plays me opp a)) ↔
      ∃ N : V, EvalGraph N (progCode me : V) (progCode opp : V) (progCode me : V) (actCode a : V) := by
```
**The exact completeness pattern** (`Det.lean:275-296`):
```
theorem models_neg_inst_sentenceAt_plays_V (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (me' opp' me opp : PD.Prog) {b aN : PD.Action} (hne : b ≠ aN)
    (hme : Proper me) (hopp : Proper opp)
    (hpos : 𝗣𝗔 ⊢ Semiformula.lMap inst (sentenceAt me' opp' (.plays me opp b))) :
    V↓[ℒₒᵣ] ⊧ ∼ Semiformula.lMap inst (sentenceAt me' opp' (.plays me opp aN)) := by
  have hV : V↓[ℒₒᵣ] ⊧ Semiformula.lMap inst (sentenceAt me' opp' (.plays me opp b)) :=
    models_of_provable inferInstance hpos
  rw [models_sentenceAt_plays_V me' opp' me opp b hme hopp] at hV
  obtain ⟨N, hN⟩ := hV
  rw [Semantics.Not.models_not, models_sentenceAt_plays_V me' opp' me opp aN hme hopp]
  rintro ⟨N', hN'⟩
  have e : (actCode b : V) = (actCode aN : V) := EvalGraph.unique_V' N N' _ _ _ _ _ hN hN'
  exact hne (actCode_inj (nat_cast_inj.mp e))

theorem pa_proves_neg_sentenceAt_inst_of_pos (me' opp' me opp : PD.Prog) {b aN : PD.Action} (hne : b ≠ aN)
    (hme : Proper me) (hopp : Proper opp)
    (hpos : 𝗣𝗔 ⊢ Semiformula.lMap inst (sentenceAt me' opp' (.plays me opp b))) :
    𝗣𝗔 ⊢ ∼ Semiformula.lMap inst (sentenceAt me' opp' (.plays me opp aN)) :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ ↦
    models_neg_inst_sentenceAt_plays_V V me' opp' me opp hne hme hopp hpos
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
  = subst LAct (binNumeral (canonical D) ∷ revalueU D ∷ revalueW D ∷ binNumeral (canonical D) ∷ revalueU D ∷ revalueW D ∷ 0) ⌜GtmplA 0⌝,   D := Dupoc k
canonical D = min (Dupoc k) (Cupod k)          (transposeCode_Dupoc, RedCell.lean:42; canonical, Guard.lean:53)
revalueU D, revalueW D ∈ {csym 0, csym 1}             (no tie: pConst 0 ≠ pConst 1 sits in the 2nd/3rd slot of cP,
                                            so Dupoc k ≠ Cupod k)
```
Which of `csym 0`/`csym 1` `revalueU D` is depends on `Dupoc k < Cupod k`, i.e. on `⟪6, k, cP⟫ < ⟪6, k, cP'⟫` with `cP' = ⟪⌜GtmplA 1⌝, pConst 1, pConst 0⟫`; since `Nat.pair` is strictly monotone in each coordinate this is `cP < cP'`, INDEPENDENT of `k` — so `revalueU D`, `revalueW D` are two fixed constants and the only `k`-dependence of the self-guard is through `binNumeral (canonical (Dupoc k))` in slots 0 and 3. (Not proved anywhere in the package; a two-line lemma.)

By the code equation `quote_guardSentence` (`Template.lean:247`) this code is `⌜guardSentence 0 (Dupoc k) (Dupoc k)⌝ = ⌜GtmplA 0 ⇜ descriptionTerms (Dupoc k) (Dupoc k)⌝` — at `ℕ` only.

**Σ₁-definability in `k`: YES, with the existing graphs, no new fixpoint.** `pSearchGraph : 𝚺₀.Semisentence 5` (`Prog.lean:63`), `pConstGraph : 𝚺₀.Semisentence 2` (`Prog.lean:43`), `guardCodeGraph : 𝚺₁.Semisentence 4` (`Guard.lean:166`, which already packs `descriptionsGraph` = `canonicalGraph` + `binNumeralGraph` + `revalueUGraph` + `revalueWGraph` + `adjoinDef`, and `substsGraph LAct`). The wanted `σDupoc : 𝚺₁.Semisentence 2` is
```
“y k. ∃ c₀, !pConstGraph c₀ 0 ∧ ∃ c₁, !pConstGraph c₁ 1 ∧ ∃ d, !pSearchGraph d k g₀ c₀ c₁ ∧ !guardCodeGraph y g₀ d d”
```
with `g₀` the numeral of `⌜GtmplA 0⌝` (a closed constant of the DEFINITION — its length is irrelevant to definability; it must NOT be stored as a numeral inside an agent's template, per FitBox). Simplest route: define `DupocV (k : V) : V := pSearch k (⌜GtmplA 0⌝ : V) (pConst 0) (pConst 1)` (V-generic; `⌜GtmplA 0⌝ : V` exists since quotes are V-polymorphic, cf. `quote_guardTemplate7` `Template.lean:162`) and `selfGuard (k : V) : V := guardCode ⌜GtmplA 0⌝ (DupocV k) (DupocV k)`; `𝚺₁-Function₁[V] selfGuard` follows from `guardCode.definable` (`Guard.lean:172`) and `pSearch.defined` (`Prog.lean:65`) by the `definability` tactic (composition of Σ₁ functions). At `ℕ`, `DupocV k = Dupoc k` is `rfl`. **What is MISSING:** `Dupoc`/`Cupod` are ℕ-only (`RedCell.lean:31,35`); the V-lift and the `σDupoc` semisentence do not exist.

**Length:** `formulaLenMeta (guardSentence 0 (Dupoc k) (Dupoc k)) ≤ 10c + 6c·(2·size (canonical (Dupoc k))) ≤ 10c + 12c·(4·size k + P)` by `exists_guard_const` (`Fit.lean:324`) + `exists_size_const` (`Fit.lean:409`) = `O(size k)`; a `guard_fits_self : ∃ K, ∀ k ≥ K, formulaLenMeta (guardSentence 0 (Dupoc k) (Dupoc k)) ≤ k` is `guard_fits` (`Fit.lean:450-465`) with `Cupod k` replaced by `Dupoc k` (the proof uses `hP k` for both slots; with both slots `Dupoc` it uses `h1` twice). Not present; a copy.

### (ii) The cell sentence `∀ x, lenBox.sigma x g(x) → evalGraphDef 2 d(x) d(x) d(x) 0`

**ANALYSIS — expressibility: YES, as an `ArithmeticSentence` (over `ℒₒᵣ`), hence over `TAct` via `emb`.** Every ingredient is an `ℒₒᵣ`-semisentence: `lenBox TAct : 𝚫₁.Semisentence 2` (`BewV.lean:25` — `T` is only a parameter; `[L.LORDefinable]` makes the definition arithmetic), `evalGraphDef : 𝚺₁.Semisentence 5` (`Eval.lean:215`), `guardCodeGraph`, `pSearchGraph`. The sentence is
```
“∀ x, ∀ d, !DupocGraph d x → ∀ g, !guardCodeGraph g g₀ d d → !(lenBox TAct).sigma x g → !evalGraphDef 2 d d d 0”
```
and its `TAct` form is `Semiformula.lMap emb (…)` — exactly how `lenProvG`, `evalG`, `guardCodeG` are built (`Code.lean:133-139`).

**Hierarchy: as written it is Π₂, not Π₁.** `evalGraphDef` is Σ₁ ONLY — the fixpoint is `Finite`, not `StrongFinite` (`Eval.lean:20-22, 183`), so there is no Π₁ side; `∀x (Δ₁ → Σ₁)` is Π₂. `EvalGraph.unique_V'` gives functionality inside every model but not a Π₁ DEFINITION. However at FUEL 2 the consequent is not needed at all: in EVERY model of `𝗜𝚺₁`, `EvalGraph 2 d d d 0 ↔ LenBox TAct x (guardCode g₀ d d)` by `EvalGraph.search_iff` + `const_iff` (V-generic, `EvalN.lean:53, 26`), so the displayed implication is a tautology and the SUBSTANTIVE content of the cell is
```
∀ x ≥ N, ∃ g, σDupoc g x ∧ (lenBox TAct).sigma x g          — a Π₂ sentence (∀∃),
```
equivalently the parametric box `∀ x ≥ N, □_x guard(x)` of (iii).

**How the `Det.lean` pattern discharges it — and what it cannot.** The pattern is `Arithmetic.complete 𝗣𝗔 σ (fun (V : Type) _ _ ↦ h_V)` (`Det.lean:295-296`; Foundation `Model.lean:78`): supply truth in EVERY model `V ⊧* 𝗣𝗔`. For the evaluator half this works verbatim: inside `V` rewrite `!evalGraphDef …` with `evalGraph_defined.df` (`Eval.lean:222`; the `eval_evalG_V` idiom `Det.lean:225-229`), `!(lenBox TAct).sigma` with `(LenBox.defined TAct).df`, `!guardCodeGraph` with `guardCode.defined.df`, `!pSearchGraph` with `pSearch.defined.df`, then `EvalGraph.search_iff`/`const_iff` exactly as `red_cell` does at `ℕ` (`RedCell.lean:120-123`, with `EvalGraph.unique_V'` for `unique'`). The result is a `𝗣𝗔`-theorem over `ℒₒᵣ`; to state it over `TAct` use `TAct ⊇ Theory.lMap emb 𝗣𝗔` (`TheoryAct.lean:56`) — an `lMap`-provability transport (Foundation's `Theory.lMap` API; ArithS uses only its model side `models_lMap_emb`, `TheoryAct.lean:38`). Note `Arithmetic.complete` is for `ArithmeticTheory` (over `ℒₒᵣ`); it does not apply to `TAct` directly.
What the pattern CANNOT give is the Löbian core, `∀ x ≥ N, lenBox x g(x)`: truth in a model `V` at a NONSTANDARD `x` means a `V`-code `d < codeBound x` with `Proof TAct d g(x) ∧ proofLen TAct d ≤ x`, where `g(x)` is a nonstandard sentence code — i.e. the whole parametric Löb argument carried out INSIDE `V` on internal derivation codes (Foundation's `Derivation`/`Provable`, `Proof/Basic.lean:465-473`, with the length tracked through the V-generic `ProofLenGraph.*_iff` clauses, `DerivationLength.lean:274-309`). The completeness theorem converts a V-GENERIC CONSTRUCTION into a PA theorem — it is exactly how Foundation gets `provable_D2` from the V-generic `modus_ponens_sentence` (`StandardProvability.lean:33-34`, `D2.lean:28`) and `provable_D3` from the internal `sigma_one_complete` (`D3.lean:160`). So the M4 route is: make bounded D1/D2/D3 V-generic constructions on codes (`Cut.lean`'s `cutMP` is the META cut on `Derivation2`, `ℕ`-only through `Proof.sound'`/`derivation_quote`; its internal twin = `modus_ponens_sentence` + `ProofLenGraph.cutRule_iff/wkRule_iff/andIntro_iff/axL_iff` + `sequentLen` bounds on the two side sequents), then `complete`.

### (iii) What is MISSING for a parametric box

**ANALYSIS.** `Bootstrapping.substNumeral`/`substNumerals`/`substNumeralParams` (`FixedPoint.lean:22,29,41`) are used NOWHERE in ArithS (grep over `arith/ArithS`: the only `subst`-on-codes uses are `guardCode … := subst LAct (descriptions me opp) g` `Guard.lean:153`, `!(substsGraph LAct) y w g` `Guard.lean:167`, and `subst LAct w p` in `Subst.lean:132,316`; `Sound.lean:86` uses the meta `substs1`). But `guardCode` IS the same mechanism as `substNumeral φ x = subst ℒₒᵣ ?[numeral x] φ`, with `LAct` for `ℒₒᵣ`, a six-entry vector for `?[·]`, and `binNumeral` for `numeral`. Hence:

* `□_x ψ(x)` as `∃ g, g = subst LAct (binNumeral x ∷ 0) ⌜ψ⌝ ∧ LenBox TAct x g` is expressible with existing pieces: define `bsubst (φ x : V) : V := subst LAct (binNumeral x ∷ 0) φ` (the `binNumeral`-analogue of `substNumeral`; Σ₁ via `binNumeralGraph` `BinNumeral.lean:327` + `adjoinDef` + `substsGraph LAct`, with the one-line `.mk fun v ↦ by simp [...]` proof of `guardCode.defined` `Guard.lean:169-170`), then
  `boxB : 𝚺₁.Semisentence 2 := “x φ. ∃ g, !bsubstGraph g φ x ∧ !(lenBox TAct).sigma x g”`.
  Nothing of this exists yet. (The `.pi` side is also available since `lenBox` is Δ₁, so `boxB` is Δ₁ once `bsubst` is total — it is, `subst` is total.)
* Its `formulaLenMeta` as a function of `x`: the box FORMULA has `x` FREE, so its length is a CONSTANT `cB := formulaLenMeta boxB` (this is the point of the parametric form). Closing it at a budget and a body — `boxB/[binNumeral-term of x, numeral-term of ⌜ψ⌝]` — costs, by `formulaLenMeta_subst_le` (`Fit.lean:192`), at most `cB · (termLenMeta(binNumeralMeta x) + termLenMeta(numeral of ⌜ψ⌝) + 1) ≤ cB · (6·size x + 6·size ⌜ψ⌝ + 3)` PROVIDED `⌜ψ⌝` is also written as a binary numeral (`numTB ⌜ψ⌝`, `Code.lean:126`; `termLenMeta_emb_numTB` `FitBox.lean:827`). With Foundation's unary `numeral ⌜ψ⌝` it is `~2·⌜ψ⌝`, exponential in the size of `ψ` — the retired-`Vacuity` trap again.
* The FitBox warning transfers: the CODE of `binNumeral x` is `≥ 2^(x+1)` (`FitBox.lean:201`), so `binNumeral x` may appear only as a RUNTIME-substituted term (like `descriptions`), never inside a STORED template constant — the existing `template (.box k ψ)` (`Code.lean:225-226`) stores `cl (numTB k)` and is exactly what `box_guard_never_fits` (`FitBox.lean:777`) kills. A parametric box in a stored template must carry the budget as a 7th VARIABLE and substitute it at evaluation time (the "box budgets as node data" fix, `FitBox.lean:776-787`). The existing `template (.box k ψ)` is already parametric in the PLAYERS (it uses `guardCodeG` on the frame's descriptions, `Code.lean:225`) — only the BUDGET slot is a constant.
* Exactly the instruction "never as a numeral of the code of `ψ(k̄)`" is the `Code.lean:44-52` non-compositionality remark: `Prov(sub(⌜A⌝, x))`, not `⌜A(x̄)⌝`.

### (iv) ℕ-only lemmas that need general-`V` versions for PA-internal reasoning

**ANALYSIS.** V-generic ALREADY: `binNumeral`, `binNumeralGraph`, `binNumeral_two_mul`, `binNumeral_semiterm` (`BinNumeral.lean:320-382`); `quote_binNumeralMeta` (`BinNumeral.lean:436`); `canonical/revalueU/revalueW/descriptions/guardCode` and all their graphs (`Guard.lean`); `canonical_of_lt/eq/gt`, `canonical_transposeCode`, `termRelabelVec_descriptions`, `guardCode_of_sentence`, `isSemiformula_guardCode`, `substTemplate`, `guardCode_substTemplate` (`Subst.lean`); `revalue`, `revalue_zero_one`, `transposeCode_transposeCode`, all `pX` graphs (`Prog.lean`); `EvalGraph.case_iff` and the inversion lemmas (`Eval.lean:229`, `EvalN.lean:15-59`); `EvalGraph.unique_V'` (`Det.lean:57`); `val_binNumeralMeta_V`, `val_canonicalMeta_V`, `cast_revalue`, `revalue_val_desc_V`, `val_actT_V`, `eval_evalG_V`, `models_sentenceAt_plays_V` (`Det.lean:144-251`); `eval_guardTemplateRaw` (`Template.lean:45`); `quote_guardTemplate7`, `quote_numT`, `quote_cterm_C/D` (`Template.lean:162-189`); `termLen_quote`/`formulaLen_quote` (`MetaLength.lean:51,76`); `ProofLenGraph.*_iff`, `proofLen`, `proofLen_defined` (`DerivationLength.lean`); `LenBox.defined`, `lenBox_numeral` (`BewV.lean`); `codeBound`, `codeBound_defined` (`Proper.lean:581-587`).

ℕ-ONLY, needing a `V` twin for internal reasoning about `binNumeral/canonical/descriptions/guardCode` and the cell:
1. `Template.lean:198 quote_canonicalMeta`, `:204 quote_revalueUMeta`, `:212 quote_revalueWMeta`, `:220 quote_actT`, `:232 semitermVec_val_descriptionTerms`, `:247 quote_guardSentence` — the CODE equations linking `descriptionTerms`/`guardSentence` (meta) to `descriptions`/`guardCode` (internal) are stated at `ℕ` (they go through `Semiterm.empty_quote_def`/`typed_quote_substs` at `ℕ`). Their `V` forms are needed wherever a `V`-element `guardCode g₀ D D` must be recognised as the quote of a meta sentence — but for a nonstandard `D` there is no meta sentence, so the internal argument should stay on codes and use these only at `ℕ` (as `red_cell` does).
2. `Template.lean:268 val_canonicalMeta`, `:274 revalue_val_desc`, `:301 models_guardSentence_iff` — the roadmap's two named items. `Det.lean:177,189` supply `val_canonicalMeta_V`, `revalue_val_desc_V`; a `models_guardSentence_iff_V` (truth of `guardTemplate7`-based guard sentences in `stdReadingV V`) does NOT exist — `Det.lean` proved the analogue only for the `Code.lean` translation `sentenceAt`/`template` (`models_sentenceAt_plays_V`), whose shape (`descF`/`progAux`/`evalG`) differs from `guardTemplate7` (`Code.lean:696-700` docstring: "two different searchers with provably equivalent guards, not one code").
3. `RedCell.lean:31,35 Dupoc/Cupod` (ℕ), `:42 transposeCode_Dupoc`, `:78 lenBox_nat`, `:85 lenBox_mp`, `:93 evalGraph_of_guard` (uses `models_TAct : ℕ↓[LAct] ⊧* TAct`, soundness — inherently about `ℕ`-truth; its internal analogue is the reflection-free argument via internal soundness of the evaluator clause, not soundness of `TAct`), `:102 guard_Dupoc_iff_guard_Cupod`.
4. `Symmetry.lean` (all): `provableLen_swap`, `lenBoxNat_codeBound_swap(_iff)` rest on `Proof.sound'` (`Sound.lean:118`, `{d : ℕ}`) and the META `transpose_exists`. An internal τ-closure needs `revalueTemplate` (`RevalueTemplate.lean`, on FORMULA codes, V-generic) lifted to DERIVATION codes with a `Derivation`-induction — absent.
5. `Cut.lean` (all code-level theorems): `lenBoxNat_codeBound_mono` (via `codeBound_nat`/`F_mono`, ℕ — the `V` version needs monotonicity of `Exp.exp` in `𝗜𝚺₁`), `lenBoxNat_of_derivation`, `derivation_of_lenBoxNat`, `lenBoxNat_mp(_sharp)`, `lenBoxNat_verum` — all through `Proof.sound'`/`derivation_quote`/`quote_derivation_le`. Internal D2 = `modus_ponens_sentence` (V-generic, `D2.lean:28`) + length accounting via `ProofLenGraph.cutRule_iff/wkRule_iff/andIntro_iff/axL_iff` and INTERNAL `sequentLen` insertion bounds (`MetaLength.lean:112-161` is the "Sequents (at V = ℕ)" section; `sequentLen_insert_of_not_mem :151` is ℕ) — plus the internal code bound `d < codeBound x`, i.e. an INTERNAL `quote_derivation_le` (`Proper.lean:399` is a meta estimate on `⌜d⌝ : ℕ`); the properness of `codeBound` for `V`-codes is not available.
6. `Fit.lean` (all): meta lengths (`formulaLenMeta`, `termLenMeta`, `Nat.size`); the internal counterpart would be `formulaLen`/`termLen` (`Length.lean`, V-generic) with an internal `formulaLen (subst w φ) ≤ formulaLen φ * (Σ termLen w + 1)` — absent — and an internal `termLen (binNumeral n) ≤ 6·‖n‖ + 1` (`termLenMeta_binNumeralMeta` `BinNumeral.lean:540` is meta; `‖·‖` = Foundation's `length`).
7. `EvalN.lean:106,132,139 EvalGraph.mono / mono_le / unique'` — fuel MONOTONICITY in `V` (`mono_V`) is missing (only `unique_V'` exists); needed to move between `EvalGraph 2 …` and `∃ n, EvalGraph n …` inside `V` (same `pi1_order_induction` template as `unique_V'`).
8. `Agent.lean:102 models_sentenceAt_of_lenBox`, `RedCell.lean:66 models_TAct` — `ℕ`-soundness facts; fine as they are (they are used where `ℕ`-truth is the target).
