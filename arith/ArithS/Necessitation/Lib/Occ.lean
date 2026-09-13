import ArithS.Necessitation.Lib.Walk
import ArithS.Necessitation.WalkLemmas

/-!
# ArithS.Necessitation.Lib.Occ — occurrence-count and shift-length rows of the library `Λ`

`DESIGN_inner_necessitation.md` §4.1–4.2 and `DESIGN_describe.md` §9.2 / summary item 15: the
`dlen` bookkeeping of the verification proof bounds the length of every node by a binary numeral,
and at `allIntro`/`shiftRule` sites the node's sequent is a SHIFTED sequent whose length the
`Lengths.lean` rows cannot bound (the term vector of a shifted atom is opaque). `ShiftLen.lean`
proved the exact laws `termLen (termShift t) = termLen t + fvOcc t`, `formulaLen (shift p) =
formulaLen p + fvOccF p`, `setLen (setShift s) ≤ setLen s + fvOccS s`; this module states them,
the occurrence counts' totality and per-constructor equations, the `free`/`subst` occurrence
bounds of `WalkLemmas.lean`, and the `O(1)` order glue §4.1's node recurrence needs, as library
rows on the `Lengths.lean` convention (body `xB` in index order, `x := ∀¹* xB`, `models_x`,
`pa_proves_x`, `lib_x`; Δ₁ hypotheses `.pi`, conclusions `.sigma`; every auxiliary object a
universal variable with its graph as a hypothesis — the totality rows supply the witnesses).

Sections:
1. Totality: `fvOccTotal`, `fvOccVecTotal`, `fvOccFTotal`, `fvOccSTotal`, `bvOccFTotal`.
2. Per constructor: `fvOccBvar/Fvar/Func`, `fvOccFRel/NRel/Verum/Falsum/And/Or/All/Exs`,
   `fvOccSInsertLe`, `fvOccSEmpty`.
3. Shift laws and bounds: `termLenShift`, `formulaLenShift`, `setLenSetShiftLe`, `fvOccFShift`,
   `fvOccSSetShiftLe`, `fvOccTermShift`; sanity `fvOccLeTermLen`, `fvOccFLeFormulaLen`,
   `fvOccSLeSetLen`; `fvOccFFreeLe'` (via `shiftGraph` + `substs1Graph`, Foundation has no
   `free` graph) and `fvOccFSubstLe` (the entry bound `M` over the vector code `w` in the `.pi`
   shape Foundation's own `isSemitermVec` uses: `∀ i < n, ∀ e, !nthDef e w i → ∀ x,
   !(fvOccGraph LAct) x e → x ≤ M`).
4. The §4.1 node bookkeeping, in the DSL syntax the `dlen` rows of `Nodes.lean` produce (the DSL
   numeral `1` is NOT `rfl`-equal to `Lengths.lean`'s `oneO`, while DSL `+`, `=`, `≤` ARE
   `addO`, `eqO`, `leF`): `dlenLeafLe`, `dlenUnaryLe`, `dlenBinaryLe` (one row use per node),
   `addLeAdd₃`, `leOfEqLe`, `leAddLeAdd`, `leAddLeft`, `leRefl`; the bridge `dslSuccEqSuccO :
   x + 1 = x + oneO` between the two syntaxes.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. Totality -/

/-- `∀ t, ∃ o, o = fvOcc t`. -/
noncomputable def fvOccTotalB : ArithmeticSemisentence 1 := “t. ∃ o, !(fvOccGraph LAct) o t”
noncomputable def fvOccTotal : ArithmeticSentence := ∀¹* fvOccTotalB

lemma models_fvOccTotal : V↓[ℒₒᵣ] ⊧ fvOccTotal ↔ ∀ t : V, ∃ o, o = fvOcc LAct t := by
  simp [fvOccTotal, fvOccTotalB, models_iff, fvOcc.defined.iff]

theorem pa_proves_fvOccTotal : 𝗣𝗔 ⊢ fvOccTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_fvOccTotal : Lib fvOccTotal := Lib.of_pa pa_proves_fvOccTotal

/-- `∀ k v, ∃ M, M = fvOccVec k v`. -/
noncomputable def fvOccVecTotalB : ArithmeticSemisentence 2 := “v k. ∃ M, !(fvOccVecGraph LAct) M k v”
noncomputable def fvOccVecTotal : ArithmeticSentence := ∀¹* fvOccVecTotalB

lemma models_fvOccVecTotal :
    V↓[ℒₒᵣ] ⊧ fvOccVecTotal ↔ ∀ v k : V, ∃ M, M = fvOccVec LAct k v := by
  simp [fvOccVecTotal, fvOccVecTotalB, models_iff, fvOccVec.defined.iff]

theorem pa_proves_fvOccVecTotal : 𝗣𝗔 ⊢ fvOccVecTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccVecTotal.mpr fun _ _ ↦ ⟨_, rfl⟩

theorem lib_fvOccVecTotal : Lib fvOccVecTotal := Lib.of_pa pa_proves_fvOccVecTotal

/-- `∀ p, ∃ o, o = fvOccF p`. -/
noncomputable def fvOccFTotalB : ArithmeticSemisentence 1 := “p. ∃ o, !(fvOccFGraph LAct) o p”
noncomputable def fvOccFTotal : ArithmeticSentence := ∀¹* fvOccFTotalB

lemma models_fvOccFTotal : V↓[ℒₒᵣ] ⊧ fvOccFTotal ↔ ∀ p : V, ∃ o, o = fvOccF LAct p := by
  simp [fvOccFTotal, fvOccFTotalB, models_iff, fvOccF.defined.iff]

theorem pa_proves_fvOccFTotal : 𝗣𝗔 ⊢ fvOccFTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccFTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_fvOccFTotal : Lib fvOccFTotal := Lib.of_pa pa_proves_fvOccFTotal

/-- `∀ s, ∃ o, o = fvOccS s`. -/
noncomputable def fvOccSTotalB : ArithmeticSemisentence 1 := “s. ∃ o, !(fvOccSDef LAct) o s”
noncomputable def fvOccSTotal : ArithmeticSentence := ∀¹* fvOccSTotalB

lemma models_fvOccSTotal : V↓[ℒₒᵣ] ⊧ fvOccSTotal ↔ ∀ s : V, ∃ o, o = fvOccS LAct s := by
  simp [fvOccSTotal, fvOccSTotalB, models_iff, fvOccS_defined.iff]

theorem pa_proves_fvOccSTotal : 𝗣𝗔 ⊢ fvOccSTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccSTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_fvOccSTotal : Lib fvOccSTotal := Lib.of_pa pa_proves_fvOccSTotal

/-- `∀ p, ∃ b, b = bvOccF p`. -/
noncomputable def bvOccFTotalB : ArithmeticSemisentence 1 := “p. ∃ b, !(bvOccFGraph LAct) b p”
noncomputable def bvOccFTotal : ArithmeticSentence := ∀¹* bvOccFTotalB

lemma models_bvOccFTotal : V↓[ℒₒᵣ] ⊧ bvOccFTotal ↔ ∀ p : V, ∃ b, b = bvOccF LAct p := by
  simp [bvOccFTotal, bvOccFTotalB, models_iff, bvOccF.defined.iff]

theorem pa_proves_bvOccFTotal : 𝗣𝗔 ⊢ bvOccFTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_bvOccFTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_bvOccFTotal : Lib bvOccFTotal := Lib.of_pa pa_proves_bvOccFTotal

/-! ### 2. Per constructor -/

/-- `fvOcc #z = 0`. -/
noncomputable def fvOccBvarB : ArithmeticSemisentence 3 :=
  “o t z. !qqBvarDef t z → !(fvOccGraph LAct) o t → o = 0”
noncomputable def fvOccBvar : ArithmeticSentence := ∀¹* fvOccBvarB

lemma models_fvOccBvar :
    V↓[ℒₒᵣ] ⊧ fvOccBvar ↔ ∀ o t z : V, t = qqBvar z → o = fvOcc LAct t → o = 0 := by
  simp [fvOccBvar, fvOccBvarB, models_iff, Matrix.vecForall_iff, fvOcc.defined.iff]

theorem pa_proves_fvOccBvar : 𝗣𝗔 ⊢ fvOccBvar :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccBvar.mpr fun _ _ z ht ho ↦ by
    subst ht; subst ho; exact fvOcc_bvar z

theorem lib_fvOccBvar : Lib fvOccBvar := Lib.of_pa pa_proves_fvOccBvar

/-- `fvOcc &x = 1`. -/
noncomputable def fvOccFvarB : ArithmeticSemisentence 3 :=
  “o t x. !qqFvarDef t x → !(fvOccGraph LAct) o t → o = 1”
noncomputable def fvOccFvar : ArithmeticSentence := ∀¹* fvOccFvarB

lemma models_fvOccFvar :
    V↓[ℒₒᵣ] ⊧ fvOccFvar ↔ ∀ o t x : V, t = qqFvar x → o = fvOcc LAct t → o = 1 := by
  simp [fvOccFvar, fvOccFvarB, models_iff, Matrix.vecForall_iff, fvOcc.defined.iff]

theorem pa_proves_fvOccFvar : 𝗣𝗔 ⊢ fvOccFvar :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccFvar.mpr fun _ _ x ht ho ↦ by
    subst ht; subst ho; exact fvOcc_fvar x

theorem lib_fvOccFvar : Lib fvOccFvar := Lib.of_pa pa_proves_fvOccFvar

/-- `fvOcc (func k f v) = listSum (fvOccVec k v)`. -/
noncomputable def fvOccFuncB : ArithmeticSemisentence 5 :=
  “o t v f k. !LAct.isFunc k f → !(isUTermVec LAct).pi k v → !qqFuncDef t k f v →
    !(fvOccGraph LAct) o t → ∃ M s, !(fvOccVecGraph LAct) M k v ∧ !listSumDef s M ∧ o = s”
noncomputable def fvOccFunc : ArithmeticSentence := ∀¹* fvOccFuncB

lemma models_fvOccFunc :
    V↓[ℒₒᵣ] ⊧ fvOccFunc ↔
    ∀ o t v f k : V, LAct.IsFunc k f → IsUTermVec LAct k v → t = qqFunc k f v → o = fvOcc LAct t →
      ∃ M s, M = fvOccVec LAct k v ∧ s = listSum M ∧ o = s := by
  simp [fvOccFunc, fvOccFuncB, models_iff, Matrix.vecForall_iff, fvOcc.defined.iff,
    fvOccVec.defined.iff, listSum_defined.iff]

theorem pa_proves_fvOccFunc : 𝗣𝗔 ⊢ fvOccFunc :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccFunc.mpr fun _ _ _ _ _ hf hv ht ho ↦ by
    subst ht; subst ho; exact ⟨_, _, rfl, rfl, fvOcc_func hf hv⟩

theorem lib_fvOccFunc : Lib fvOccFunc := Lib.of_pa pa_proves_fvOccFunc

/-- `fvOccF (rel k R v) = listSum (fvOccVec k v)`. -/
noncomputable def fvOccFRelB : ArithmeticSemisentence 5 :=
  “o p v R k. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqRelDef p k R v →
    !(fvOccFGraph LAct) o p → ∃ M s, !(fvOccVecGraph LAct) M k v ∧ !listSumDef s M ∧ o = s”
noncomputable def fvOccFRel : ArithmeticSentence := ∀¹* fvOccFRelB

lemma models_fvOccFRel :
    V↓[ℒₒᵣ] ⊧ fvOccFRel ↔
    ∀ o p v R k : V, LAct.IsRel k R → IsUTermVec LAct k v → p = ^rel k R v → o = fvOccF LAct p →
      ∃ M s, M = fvOccVec LAct k v ∧ s = listSum M ∧ o = s := by
  simp [fvOccFRel, fvOccFRelB, models_iff, Matrix.vecForall_iff, fvOccF.defined.iff,
    fvOccVec.defined.iff, listSum_defined.iff]

theorem pa_proves_fvOccFRel : 𝗣𝗔 ⊢ fvOccFRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccFRel.mpr fun _ _ _ _ _ hR hv hp ho ↦ by
    subst hp; subst ho; exact ⟨_, _, rfl, rfl, fvOccF_rel hR hv⟩

theorem lib_fvOccFRel : Lib fvOccFRel := Lib.of_pa pa_proves_fvOccFRel

/-- `fvOccF (nrel k R v) = listSum (fvOccVec k v)`. -/
noncomputable def fvOccFNRelB : ArithmeticSemisentence 5 :=
  “o p v R k. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqNRelDef p k R v →
    !(fvOccFGraph LAct) o p → ∃ M s, !(fvOccVecGraph LAct) M k v ∧ !listSumDef s M ∧ o = s”
noncomputable def fvOccFNRel : ArithmeticSentence := ∀¹* fvOccFNRelB

lemma models_fvOccFNRel :
    V↓[ℒₒᵣ] ⊧ fvOccFNRel ↔
    ∀ o p v R k : V, LAct.IsRel k R → IsUTermVec LAct k v → p = ^nrel k R v → o = fvOccF LAct p →
      ∃ M s, M = fvOccVec LAct k v ∧ s = listSum M ∧ o = s := by
  simp [fvOccFNRel, fvOccFNRelB, models_iff, Matrix.vecForall_iff, fvOccF.defined.iff,
    fvOccVec.defined.iff, listSum_defined.iff]

theorem pa_proves_fvOccFNRel : 𝗣𝗔 ⊢ fvOccFNRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccFNRel.mpr fun _ _ _ _ _ hR hv hp ho ↦ by
    subst hp; subst ho; exact ⟨_, _, rfl, rfl, fvOccF_nrel hR hv⟩

theorem lib_fvOccFNRel : Lib fvOccFNRel := Lib.of_pa pa_proves_fvOccFNRel

/-- `fvOccF ⊤ = 0`. -/
noncomputable def fvOccFVerumB : ArithmeticSemisentence 2 :=
  “o p. !qqVerumDef p → !(fvOccFGraph LAct) o p → o = 0”
noncomputable def fvOccFVerum : ArithmeticSentence := ∀¹* fvOccFVerumB

lemma models_fvOccFVerum :
    V↓[ℒₒᵣ] ⊧ fvOccFVerum ↔ ∀ o p : V, p = ^⊤ → o = fvOccF LAct p → o = 0 := by
  simp [fvOccFVerum, fvOccFVerumB, models_iff, Matrix.vecForall_iff, fvOccF.defined.iff]

theorem pa_proves_fvOccFVerum : 𝗣𝗔 ⊢ fvOccFVerum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccFVerum.mpr fun _ _ hp ho ↦ by
    subst hp; subst ho; exact fvOccF_verum

theorem lib_fvOccFVerum : Lib fvOccFVerum := Lib.of_pa pa_proves_fvOccFVerum

/-- `fvOccF ⊥ = 0`. -/
noncomputable def fvOccFFalsumB : ArithmeticSemisentence 2 :=
  “o p. !qqFalsumDef p → !(fvOccFGraph LAct) o p → o = 0”
noncomputable def fvOccFFalsum : ArithmeticSentence := ∀¹* fvOccFFalsumB

lemma models_fvOccFFalsum :
    V↓[ℒₒᵣ] ⊧ fvOccFFalsum ↔ ∀ o p : V, p = ^⊥ → o = fvOccF LAct p → o = 0 := by
  simp [fvOccFFalsum, fvOccFFalsumB, models_iff, Matrix.vecForall_iff, fvOccF.defined.iff]

theorem pa_proves_fvOccFFalsum : 𝗣𝗔 ⊢ fvOccFFalsum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccFFalsum.mpr fun _ _ hp ho ↦ by
    subst hp; subst ho; exact fvOccF_falsum

theorem lib_fvOccFFalsum : Lib fvOccFFalsum := Lib.of_pa pa_proves_fvOccFFalsum

/-- `fvOccF (p ⋏ q) = fvOccF p + fvOccF q`. -/
noncomputable def fvOccFAndB : ArithmeticSemisentence 7 :=
  “or oq op r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqAndDef r p q →
    !(fvOccFGraph LAct) op p → !(fvOccFGraph LAct) oq q → !(fvOccFGraph LAct) or r → or = op + oq”
noncomputable def fvOccFAnd : ArithmeticSentence := ∀¹* fvOccFAndB

lemma models_fvOccFAnd :
    V↓[ℒₒᵣ] ⊧ fvOccFAnd ↔
    ∀ or oq op r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋏ q →
      op = fvOccF LAct p → oq = fvOccF LAct q → or = fvOccF LAct r → or = op + oq := by
  simp [fvOccFAnd, fvOccFAndB, models_iff, Matrix.vecForall_iff, fvOccF.defined.iff]

theorem pa_proves_fvOccFAnd : 𝗣𝗔 ⊢ fvOccFAnd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccFAnd.mpr fun _ _ _ _ _ _ _ hp hq hr h₁ h₂ h₃ ↦ by
    subst hr; subst h₁; subst h₂; subst h₃; exact fvOccF_and hp.isUFormula hq.isUFormula

theorem lib_fvOccFAnd : Lib fvOccFAnd := Lib.of_pa pa_proves_fvOccFAnd

/-- `fvOccF (p ⋎ q) = fvOccF p + fvOccF q`. -/
noncomputable def fvOccFOrB : ArithmeticSemisentence 7 :=
  “or oq op r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqOrDef r p q →
    !(fvOccFGraph LAct) op p → !(fvOccFGraph LAct) oq q → !(fvOccFGraph LAct) or r → or = op + oq”
noncomputable def fvOccFOr : ArithmeticSentence := ∀¹* fvOccFOrB

lemma models_fvOccFOr :
    V↓[ℒₒᵣ] ⊧ fvOccFOr ↔
    ∀ or oq op r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋎ q →
      op = fvOccF LAct p → oq = fvOccF LAct q → or = fvOccF LAct r → or = op + oq := by
  simp [fvOccFOr, fvOccFOrB, models_iff, Matrix.vecForall_iff, fvOccF.defined.iff]

theorem pa_proves_fvOccFOr : 𝗣𝗔 ⊢ fvOccFOr :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccFOr.mpr fun _ _ _ _ _ _ _ hp hq hr h₁ h₂ h₃ ↦ by
    subst hr; subst h₁; subst h₂; subst h₃; exact fvOccF_or hp.isUFormula hq.isUFormula

theorem lib_fvOccFOr : Lib fvOccFOr := Lib.of_pa pa_proves_fvOccFOr

/-- `fvOccF (∀ p) = fvOccF p`. -/
noncomputable def fvOccFAllB : ArithmeticSemisentence 5 :=
  “oq op q p n. !(isSemiformula LAct).pi (n + 1) p → !qqAllDef q p →
    !(fvOccFGraph LAct) op p → !(fvOccFGraph LAct) oq q → oq = op”
noncomputable def fvOccFAll : ArithmeticSentence := ∀¹* fvOccFAllB

lemma models_fvOccFAll :
    V↓[ℒₒᵣ] ⊧ fvOccFAll ↔
    ∀ oq op q p n : V, IsSemiformula LAct (n + 1) p → q = ^∀ p →
      op = fvOccF LAct p → oq = fvOccF LAct q → oq = op := by
  simp [fvOccFAll, fvOccFAllB, models_iff, Matrix.vecForall_iff, fvOccF.defined.iff]

theorem pa_proves_fvOccFAll : 𝗣𝗔 ⊢ fvOccFAll :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccFAll.mpr fun _ _ _ _ _ hp hq h₁ h₂ ↦ by
    subst hq; subst h₁; subst h₂; exact fvOccF_all hp.isUFormula

theorem lib_fvOccFAll : Lib fvOccFAll := Lib.of_pa pa_proves_fvOccFAll

/-- `fvOccF (∃ p) = fvOccF p`. -/
noncomputable def fvOccFExsB : ArithmeticSemisentence 5 :=
  “oq op q p n. !(isSemiformula LAct).pi (n + 1) p → !qqExsDef q p →
    !(fvOccFGraph LAct) op p → !(fvOccFGraph LAct) oq q → oq = op”
noncomputable def fvOccFExs : ArithmeticSentence := ∀¹* fvOccFExsB

lemma models_fvOccFExs :
    V↓[ℒₒᵣ] ⊧ fvOccFExs ↔
    ∀ oq op q p n : V, IsSemiformula LAct (n + 1) p → q = ^∃ p →
      op = fvOccF LAct p → oq = fvOccF LAct q → oq = op := by
  simp [fvOccFExs, fvOccFExsB, models_iff, Matrix.vecForall_iff, fvOccF.defined.iff]

theorem pa_proves_fvOccFExs : 𝗣𝗔 ⊢ fvOccFExs :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccFExs.mpr fun _ _ _ _ _ hp hq h₁ h₂ ↦ by
    subst hq; subst h₁; subst h₂; exact fvOccF_exs hp.isUFormula

theorem lib_fvOccFExs : Lib fvOccFExs := Lib.of_pa pa_proves_fvOccFExs

/-- `fvOccS (insert x s) ≤ fvOccS s + fvOccF x`. -/
noncomputable def fvOccSInsertLeB : ArithmeticSemisentence 6 :=
  “ox os o t s x. !insertDef t x s → !(fvOccSDef LAct) o t → !(fvOccSDef LAct) os s →
    !(fvOccFGraph LAct) ox x → o ≤ os + ox”
noncomputable def fvOccSInsertLe : ArithmeticSentence := ∀¹* fvOccSInsertLeB

lemma models_fvOccSInsertLe :
    V↓[ℒₒᵣ] ⊧ fvOccSInsertLe ↔
    ∀ ox os o t s x : V, t = insert x s → o = fvOccS LAct t → os = fvOccS LAct s →
      ox = fvOccF LAct x → o ≤ os + ox := by
  simp [fvOccSInsertLe, fvOccSInsertLeB, models_iff, Matrix.vecForall_iff, fvOccS_defined.iff,
    fvOccF.defined.iff]

theorem pa_proves_fvOccSInsertLe : 𝗣𝗔 ⊢ fvOccSInsertLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccSInsertLe.mpr fun _ _ _ _ s x ht ho hos hox ↦ by
    subst ht; subst ho; subst hos; subst hox; exact fvOccS_insert_le x s

theorem lib_fvOccSInsertLe : Lib fvOccSInsertLe := Lib.of_pa pa_proves_fvOccSInsertLe

/-- `fvOccS ∅ = 0`. -/
noncomputable def fvOccSEmptyB : ArithmeticSemisentence 1 := “o. !(fvOccSDef LAct) o 0 → o = 0”
noncomputable def fvOccSEmpty : ArithmeticSentence := ∀¹* fvOccSEmptyB

lemma models_fvOccSEmpty : V↓[ℒₒᵣ] ⊧ fvOccSEmpty ↔ ∀ o : V, o = fvOccS LAct 0 → o = 0 := by
  simp [fvOccSEmpty, fvOccSEmptyB, models_iff, Matrix.vecForall_iff, fvOccS_defined.iff]

theorem pa_proves_fvOccSEmpty : 𝗣𝗔 ⊢ fvOccSEmpty :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccSEmpty.mpr fun _ h ↦ by
    subst h; exact fvOccS_empty

theorem lib_fvOccSEmpty : Lib fvOccSEmpty := Lib.of_pa pa_proves_fvOccSEmpty

/-! ### 3. The shift laws, the sanity bounds, `free`/`subst` -/

/-- `termLen (termShift t) = termLen t + fvOcc t` (`termLen_termShift_eq`). -/
noncomputable def termLenShiftB : ArithmeticSemisentence 4 :=
  “t' o l t. !(isUTerm LAct).pi t → !(termLenGraph LAct) l t → !(fvOccGraph LAct) o t →
    !(termShiftGraph LAct) t' t → !(termLenGraph LAct) (l + o) t'”
noncomputable def termLenShift : ArithmeticSentence := ∀¹* termLenShiftB

lemma models_termLenShift :
    V↓[ℒₒᵣ] ⊧ termLenShift ↔
    ∀ t' o l t : V, IsUTerm LAct t → l = termLen LAct t → o = fvOcc LAct t → t' = termShift LAct t →
      l + o = termLen LAct t' := by
  simp [termLenShift, termLenShiftB, models_iff, Matrix.vecForall_iff, termLen.defined.iff,
    fvOcc.defined.iff, termShift.defined.iff]

theorem pa_proves_termLenShift : 𝗣𝗔 ⊢ termLenShift :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termLenShift.mpr fun _ _ _ _ ht hl ho ht' ↦ by
    subst hl; subst ho; subst ht'; exact (termLen_termShift_eq ht).symm

theorem lib_termLenShift : Lib termLenShift := Lib.of_pa pa_proves_termLenShift

/-- `formulaLen (shift p) = formulaLen p + fvOccF p` (`formulaLen_shift_eq`). -/
noncomputable def formulaLenShiftB : ArithmeticSemisentence 4 :=
  “q o l p. !(isUFormula LAct).pi p → !(formulaLenGraph LAct) l p → !(fvOccFGraph LAct) o p →
    !(shiftGraph LAct) q p → !(formulaLenGraph LAct) (l + o) q”
noncomputable def formulaLenShift : ArithmeticSentence := ∀¹* formulaLenShiftB

lemma models_formulaLenShift :
    V↓[ℒₒᵣ] ⊧ formulaLenShift ↔
    ∀ q o l p : V, IsUFormula LAct p → l = formulaLen LAct p → o = fvOccF LAct p → q = shift LAct p →
      l + o = formulaLen LAct q := by
  simp [formulaLenShift, formulaLenShiftB, models_iff, Matrix.vecForall_iff, formulaLen.defined.iff,
    fvOccF.defined.iff, shift.defined.iff]

theorem pa_proves_formulaLenShift : 𝗣𝗔 ⊢ formulaLenShift :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_formulaLenShift.mpr fun _ _ _ _ hp hl ho hq ↦ by
    subst hl; subst ho; subst hq; exact (formulaLen_shift_eq hp).symm

theorem lib_formulaLenShift : Lib formulaLenShift := Lib.of_pa pa_proves_formulaLenShift

/-- `setLen (setShift s) ≤ setLen s + fvOccS s` (`setLen_setShift_le_occ`; the shape of
`setLenInsertLe` — the shifted set's length arrives from `setLenTotal`). -/
noncomputable def setLenSetShiftLeB : ArithmeticSemisentence 5 :=
  “l' o l s' s. !(isFormulaSet LAct).pi s → !(setShiftGraph LAct) s' s → !(setLenDef LAct) l s →
    !(fvOccSDef LAct) o s → !(setLenDef LAct) l' s' → l' ≤ l + o”
noncomputable def setLenSetShiftLe : ArithmeticSentence := ∀¹* setLenSetShiftLeB

lemma models_setLenSetShiftLe :
    V↓[ℒₒᵣ] ⊧ setLenSetShiftLe ↔
    ∀ l' o l s' s : V, IsFormulaSet LAct s → s' = setShift LAct s → l = setLen LAct s →
      o = fvOccS LAct s → l' = setLen LAct s' → l' ≤ l + o := by
  simp [setLenSetShiftLe, setLenSetShiftLeB, models_iff, Matrix.vecForall_iff, setLen_defined.iff,
    fvOccS_defined.iff, setShift.defined.iff]

theorem pa_proves_setLenSetShiftLe : 𝗣𝗔 ⊢ setLenSetShiftLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_setLenSetShiftLe.mpr fun _ _ _ _ _ hs hs' hl ho hl' ↦ by
    subst hs'; subst hl; subst ho; subst hl'; exact setLen_setShift_le_occ hs

theorem lib_setLenSetShiftLe : Lib setLenSetShiftLe := Lib.of_pa pa_proves_setLenSetShiftLe

/-- `fvOccF (shift p) = fvOccF p` (`fvOccF_shift`), as a graph transport. -/
noncomputable def fvOccFShiftB : ArithmeticSemisentence 3 :=
  “q o p. !(isUFormula LAct).pi p → !(fvOccFGraph LAct) o p → !(shiftGraph LAct) q p →
    !(fvOccFGraph LAct) o q”
noncomputable def fvOccFShift : ArithmeticSentence := ∀¹* fvOccFShiftB

lemma models_fvOccFShift :
    V↓[ℒₒᵣ] ⊧ fvOccFShift ↔
    ∀ q o p : V, IsUFormula LAct p → o = fvOccF LAct p → q = shift LAct p → o = fvOccF LAct q := by
  simp [fvOccFShift, fvOccFShiftB, models_iff, Matrix.vecForall_iff, fvOccF.defined.iff,
    shift.defined.iff]

theorem pa_proves_fvOccFShift : 𝗣𝗔 ⊢ fvOccFShift :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccFShift.mpr fun _ _ _ hp ho hq ↦ by
    subst ho; subst hq; exact (fvOccF_shift hp).symm

theorem lib_fvOccFShift : Lib fvOccFShift := Lib.of_pa pa_proves_fvOccFShift

/-- `fvOccS (setShift s) ≤ fvOccS s` (`fvOccS_setShift_le`). -/
noncomputable def fvOccSSetShiftLeB : ArithmeticSemisentence 4 :=
  “o' s' o s. !(isFormulaSet LAct).pi s → !(fvOccSDef LAct) o s → !(setShiftGraph LAct) s' s →
    !(fvOccSDef LAct) o' s' → o' ≤ o”
noncomputable def fvOccSSetShiftLe : ArithmeticSentence := ∀¹* fvOccSSetShiftLeB

lemma models_fvOccSSetShiftLe :
    V↓[ℒₒᵣ] ⊧ fvOccSSetShiftLe ↔
    ∀ o' s' o s : V, IsFormulaSet LAct s → o = fvOccS LAct s → s' = setShift LAct s →
      o' = fvOccS LAct s' → o' ≤ o := by
  simp [fvOccSSetShiftLe, fvOccSSetShiftLeB, models_iff, Matrix.vecForall_iff, fvOccS_defined.iff,
    setShift.defined.iff]

theorem pa_proves_fvOccSSetShiftLe : 𝗣𝗔 ⊢ fvOccSSetShiftLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccSSetShiftLe.mpr fun _ _ _ _ hs ho hs' ho' ↦ by
    subst ho; subst hs'; subst ho'; exact fvOccS_setShift_le hs

theorem lib_fvOccSSetShiftLe : Lib fvOccSSetShiftLe := Lib.of_pa pa_proves_fvOccSSetShiftLe

/-- `fvOcc (termShift t) = fvOcc t` (`fvOcc_termShift`), as a graph transport. -/
noncomputable def fvOccTermShiftB : ArithmeticSemisentence 3 :=
  “t' o t. !(isUTerm LAct).pi t → !(fvOccGraph LAct) o t → !(termShiftGraph LAct) t' t →
    !(fvOccGraph LAct) o t'”
noncomputable def fvOccTermShift : ArithmeticSentence := ∀¹* fvOccTermShiftB

lemma models_fvOccTermShift :
    V↓[ℒₒᵣ] ⊧ fvOccTermShift ↔
    ∀ t' o t : V, IsUTerm LAct t → o = fvOcc LAct t → t' = termShift LAct t → o = fvOcc LAct t' := by
  simp [fvOccTermShift, fvOccTermShiftB, models_iff, Matrix.vecForall_iff, fvOcc.defined.iff,
    termShift.defined.iff]

theorem pa_proves_fvOccTermShift : 𝗣𝗔 ⊢ fvOccTermShift :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccTermShift.mpr fun _ _ _ ht ho ht' ↦ by
    subst ho; subst ht'; exact (fvOcc_termShift ht).symm

theorem lib_fvOccTermShift : Lib fvOccTermShift := Lib.of_pa pa_proves_fvOccTermShift

/-- `fvOcc t ≤ termLen t`. -/
noncomputable def fvOccLeTermLenB : ArithmeticSemisentence 3 :=
  “l o t. !(isUTerm LAct).pi t → !(fvOccGraph LAct) o t → !(termLenGraph LAct) l t → o ≤ l”
noncomputable def fvOccLeTermLen : ArithmeticSentence := ∀¹* fvOccLeTermLenB

lemma models_fvOccLeTermLen :
    V↓[ℒₒᵣ] ⊧ fvOccLeTermLen ↔
    ∀ l o t : V, IsUTerm LAct t → o = fvOcc LAct t → l = termLen LAct t → o ≤ l := by
  simp [fvOccLeTermLen, fvOccLeTermLenB, models_iff, Matrix.vecForall_iff, fvOcc.defined.iff,
    termLen.defined.iff]

theorem pa_proves_fvOccLeTermLen : 𝗣𝗔 ⊢ fvOccLeTermLen :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccLeTermLen.mpr fun _ _ _ ht ho hl ↦ by
    subst ho; subst hl; exact fvOcc_le_termLen ht

theorem lib_fvOccLeTermLen : Lib fvOccLeTermLen := Lib.of_pa pa_proves_fvOccLeTermLen

/-- `fvOccF p ≤ formulaLen p`. -/
noncomputable def fvOccFLeFormulaLenB : ArithmeticSemisentence 3 :=
  “l o p. !(isUFormula LAct).pi p → !(fvOccFGraph LAct) o p → !(formulaLenGraph LAct) l p → o ≤ l”
noncomputable def fvOccFLeFormulaLen : ArithmeticSentence := ∀¹* fvOccFLeFormulaLenB

lemma models_fvOccFLeFormulaLen :
    V↓[ℒₒᵣ] ⊧ fvOccFLeFormulaLen ↔
    ∀ l o p : V, IsUFormula LAct p → o = fvOccF LAct p → l = formulaLen LAct p → o ≤ l := by
  simp [fvOccFLeFormulaLen, fvOccFLeFormulaLenB, models_iff, Matrix.vecForall_iff, fvOccF.defined.iff,
    formulaLen.defined.iff]

theorem pa_proves_fvOccFLeFormulaLen : 𝗣𝗔 ⊢ fvOccFLeFormulaLen :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccFLeFormulaLen.mpr fun _ _ _ hp ho hl ↦ by
    subst ho; subst hl; exact fvOccF_le_formulaLen hp

theorem lib_fvOccFLeFormulaLen : Lib fvOccFLeFormulaLen := Lib.of_pa pa_proves_fvOccFLeFormulaLen

/-- `fvOccS s ≤ setLen s`. -/
noncomputable def fvOccSLeSetLenB : ArithmeticSemisentence 3 :=
  “l o s. !(isFormulaSet LAct).pi s → !(fvOccSDef LAct) o s → !(setLenDef LAct) l s → o ≤ l”
noncomputable def fvOccSLeSetLen : ArithmeticSentence := ∀¹* fvOccSLeSetLenB

lemma models_fvOccSLeSetLen :
    V↓[ℒₒᵣ] ⊧ fvOccSLeSetLen ↔
    ∀ l o s : V, IsFormulaSet LAct s → o = fvOccS LAct s → l = setLen LAct s → o ≤ l := by
  simp [fvOccSLeSetLen, fvOccSLeSetLenB, models_iff, Matrix.vecForall_iff, fvOccS_defined.iff,
    setLen_defined.iff]

theorem pa_proves_fvOccSLeSetLen : 𝗣𝗔 ⊢ fvOccSLeSetLen :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvOccSLeSetLen.mpr fun _ _ _ hs ho hl ↦ by
    subst ho; subst hl; exact fvOccS_le_setLen hs

theorem lib_fvOccSLeSetLen : Lib fvOccSLeSetLen := Lib.of_pa pa_proves_fvOccSLeSetLen

/-- `fvOccF (free p) ≤ fvOccF p + bvOccF p` (`fvOccF_free_le'`). Foundation has no graph for
`free`; `free p = substs1 &0 (shift p)` is spelled out: `z = &0`, `sp = shift p`,
`q = substs1 z sp`. -/
noncomputable def fvOccFFreeLe'B : ArithmeticSemisentence 7 :=
  “o' q sp z b o p. !(isSemiformula LAct).pi 1 p → !(fvOccFGraph LAct) o p → !(bvOccFGraph LAct) b p →
    !qqFvarDef z 0 → !(shiftGraph LAct) sp p → !(substs1Graph LAct) q z sp →
    !(fvOccFGraph LAct) o' q → o' ≤ o + b”
noncomputable def fvOccFFreeLe' : ArithmeticSentence := ∀¹* fvOccFFreeLe'B

lemma models_fvOccFFreeLe' :
    V↓[ℒₒᵣ] ⊧ fvOccFFreeLe' ↔
    ∀ o' q sp z b o p : V, IsSemiformula LAct 1 p → o = fvOccF LAct p → b = bvOccF LAct p →
      z = ^&0 → sp = shift LAct p → q = substs1 LAct z sp → o' = fvOccF LAct q → o' ≤ o + b := by
  simp [fvOccFFreeLe', fvOccFFreeLe'B, models_iff, Matrix.vecForall_iff, fvOccF.defined.iff,
    bvOccF.defined.iff, shift.defined.iff, substs1.defined.iff]

theorem pa_proves_fvOccFFreeLe' : 𝗣𝗔 ⊢ fvOccFFreeLe' :=
  Lib.pa_proves_of_models fun _ _ _ ↦
    models_fvOccFFreeLe'.mpr fun _ _ _ _ _ _ _ hp ho hb hz hsp hq ho' ↦ by
      subst ho; subst hb; subst hz; subst hsp; subst hq; subst ho'; exact fvOccF_free_le' hp

theorem lib_fvOccFFreeLe' : Lib fvOccFFreeLe' := Lib.of_pa pa_proves_fvOccFFreeLe'

/-- `fvOccF (subst w p) ≤ fvOccF p + bvOccF p · M` when every entry of `w` has at most `M`
free-variable occurrences (`fvOccF_subst_le`). The entry bound is the bounded `.pi` shape
Foundation's `isSemitermVec` uses: `∀ i < n, ∀ e, !nthDef e w i → ∀ x, !(fvOccGraph LAct) x e →
x ≤ M`. -/
noncomputable def fvOccFSubstLeB : ArithmeticSemisentence 9 :=
  “o' q b o M w m p n. !(isSemiformula LAct).pi n p → !(isSemitermVec LAct).pi n m w →
    (∀ i < n, ∀ e, !nthDef e w i → ∀ x, !(fvOccGraph LAct) x e → x ≤ M) →
    !(fvOccFGraph LAct) o p → !(bvOccFGraph LAct) b p → !(substsGraph LAct) q w p →
    !(fvOccFGraph LAct) o' q → o' ≤ o + b * M”
noncomputable def fvOccFSubstLe : ArithmeticSentence := ∀¹* fvOccFSubstLeB

lemma models_fvOccFSubstLe :
    V↓[ℒₒᵣ] ⊧ fvOccFSubstLe ↔
    ∀ o' q b o M w m p n : V, IsSemiformula LAct n p → IsSemitermVec LAct n m w →
      (∀ i < n, fvOcc LAct w.[i] ≤ M) →
      o = fvOccF LAct p → b = bvOccF LAct p → q = subst LAct w p → o' = fvOccF LAct q →
      o' ≤ o + b * M := by
  simp [fvOccFSubstLe, fvOccFSubstLeB, models_iff, Matrix.vecForall_iff, fvOccF.defined.iff,
    bvOccF.defined.iff, fvOcc.defined.iff, nth_defined.iff, subst.defined.iff]

theorem pa_proves_fvOccFSubstLe : 𝗣𝗔 ⊢ fvOccFSubstLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦
    models_fvOccFSubstLe.mpr fun _ _ _ _ _ _ _ _ _ hp hw hM ho hb hq ho' ↦ by
      subst ho; subst hb; subst hq; subst ho'; exact fvOccF_subst_le hp hw hM

theorem lib_fvOccFSubstLe : Lib fvOccFSubstLe := Lib.of_pa pa_proves_fvOccFSubstLe

/-! ### 4. The §4.1 node bookkeeping — DSL syntax, one row use per node

`Nodes.lean`'s `dlen` rows conclude `!(dlenGraphDef LAct).sigma e (l + np + nq + 1)` in the DSL;
the DSL `+`, `=`, `≤` are `rfl`-equal to `Lengths.lean`'s `addO`, `eqO`, `leF`, but the DSL
numeral `1` is not `rfl`-equal to `oneO`, so the rows that must match a `dlen` conclusion are
stated here in the DSL. -/

/-- Leaf: `n = l + 1 → l ≤ a → n ≤ a + 1` (`dlenAxL`, `dlenVerum`). -/
noncomputable def dlenLeafLeB : ArithmeticSemisentence 3 :=
  “a l n. n = l + 1 → l ≤ a → n ≤ a + 1”
noncomputable def dlenLeafLe : ArithmeticSentence := ∀¹* dlenLeafLeB

lemma models_dlenLeafLe : V↓[ℒₒᵣ] ⊧ dlenLeafLe ↔ ∀ a l n : V, n = l + 1 → l ≤ a → n ≤ a + 1 := by
  simp [dlenLeafLe, dlenLeafLeB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_dlenLeafLe : 𝗣𝗔 ⊢ dlenLeafLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_dlenLeafLe.mpr fun _ _ _ hn hl ↦ by
    subst hn; exact add_le_add hl (le_refl 1)

theorem lib_dlenLeafLe : Lib dlenLeafLe := Lib.of_pa pa_proves_dlenLeafLe

/-- Unary node: `n = l + n₁ + 1 → l ≤ a → n₁ ≤ b → n ≤ a + b + 1` (`dlenOr`, `dlenAll`, …). -/
noncomputable def dlenUnaryLeB : ArithmeticSemisentence 5 :=
  “b a np l n. n = l + np + 1 → l ≤ a → np ≤ b → n ≤ a + b + 1”
noncomputable def dlenUnaryLe : ArithmeticSentence := ∀¹* dlenUnaryLeB

lemma models_dlenUnaryLe :
    V↓[ℒₒᵣ] ⊧ dlenUnaryLe ↔ ∀ b a np l n : V, n = l + np + 1 → l ≤ a → np ≤ b → n ≤ a + b + 1 := by
  simp [dlenUnaryLe, dlenUnaryLeB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_dlenUnaryLe : 𝗣𝗔 ⊢ dlenUnaryLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_dlenUnaryLe.mpr fun _ _ _ _ _ hn hl hp ↦ by
    subst hn; exact add_le_add (add_le_add hl hp) (le_refl 1)

theorem lib_dlenUnaryLe : Lib dlenUnaryLe := Lib.of_pa pa_proves_dlenUnaryLe

/-- Binary node, §4.1's recurrence: `n = l + n₁ + n₂ + 1 → l ≤ a → n₁ ≤ b → n₂ ≤ c →
n ≤ a + b + c + 1` (`dlenAnd`, cut). -/
noncomputable def dlenBinaryLeB : ArithmeticSemisentence 7 :=
  “c b a nq np l n. n = l + np + nq + 1 → l ≤ a → np ≤ b → nq ≤ c → n ≤ a + b + c + 1”
noncomputable def dlenBinaryLe : ArithmeticSentence := ∀¹* dlenBinaryLeB

lemma models_dlenBinaryLe :
    V↓[ℒₒᵣ] ⊧ dlenBinaryLe ↔
    ∀ c b a nq np l n : V, n = l + np + nq + 1 → l ≤ a → np ≤ b → nq ≤ c → n ≤ a + b + c + 1 := by
  simp [dlenBinaryLe, dlenBinaryLeB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_dlenBinaryLe : 𝗣𝗔 ⊢ dlenBinaryLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_dlenBinaryLe.mpr fun _ _ _ _ _ _ _ hn hl hp hq ↦ by
    subst hn; exact add_le_add (add_le_add (add_le_add hl hp) hq) (le_refl 1)

theorem lib_dlenBinaryLe : Lib dlenBinaryLe := Lib.of_pa pa_proves_dlenBinaryLe

/-- `a ≤ x → b ≤ y → c ≤ z → a + b + c ≤ x + y + z`. -/
noncomputable def addLeAdd₃B : ArithmeticSemisentence 6 :=
  “z y x c b a. a ≤ x → b ≤ y → c ≤ z → a + b + c ≤ x + y + z”
noncomputable def addLeAdd₃ : ArithmeticSentence := ∀¹* addLeAdd₃B

lemma models_addLeAdd₃ :
    V↓[ℒₒᵣ] ⊧ addLeAdd₃ ↔ ∀ z y x c b a : V, a ≤ x → b ≤ y → c ≤ z → a + b + c ≤ x + y + z := by
  simp [addLeAdd₃, addLeAdd₃B, models_iff, Matrix.vecForall_iff]

theorem pa_proves_addLeAdd₃ : 𝗣𝗔 ⊢ addLeAdd₃ :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_addLeAdd₃.mpr fun _ _ _ _ _ _ h₁ h₂ h₃ ↦
    add_le_add (add_le_add h₁ h₂) h₃

theorem lib_addLeAdd₃ : Lib addLeAdd₃ := Lib.of_pa pa_proves_addLeAdd₃

/-- `x = y → y ≤ z → x ≤ z` (rewrite a length equation into its bound). -/
noncomputable def leOfEqLeB : ArithmeticSemisentence 3 := “z y x. x = y → y ≤ z → x ≤ z”
noncomputable def leOfEqLe : ArithmeticSentence := ∀¹* leOfEqLeB

lemma models_leOfEqLe : V↓[ℒₒᵣ] ⊧ leOfEqLe ↔ ∀ z y x : V, x = y → y ≤ z → x ≤ z := by
  simp [leOfEqLe, leOfEqLeB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_leOfEqLe : 𝗣𝗔 ⊢ leOfEqLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_leOfEqLe.mpr fun _ _ _ e h ↦ e ▸ h

theorem lib_leOfEqLe : Lib leOfEqLe := Lib.of_pa pa_proves_leOfEqLe

/-- `x ≤ y + z → y ≤ a → z ≤ b → x ≤ a + b` (§4.2: `setLen s' ≤ setLen s + formulaLen p`
with both summands bounded, in one use). -/
noncomputable def leAddLeAddB : ArithmeticSemisentence 5 :=
  “b a z y x. x ≤ y + z → y ≤ a → z ≤ b → x ≤ a + b”
noncomputable def leAddLeAdd : ArithmeticSentence := ∀¹* leAddLeAddB

lemma models_leAddLeAdd :
    V↓[ℒₒᵣ] ⊧ leAddLeAdd ↔ ∀ b a z y x : V, x ≤ y + z → y ≤ a → z ≤ b → x ≤ a + b := by
  simp [leAddLeAdd, leAddLeAddB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_leAddLeAdd : 𝗣𝗔 ⊢ leAddLeAdd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_leAddLeAdd.mpr fun _ _ _ _ _ h h₁ h₂ ↦
    le_trans h (add_le_add h₁ h₂)

theorem lib_leAddLeAdd : Lib leAddLeAdd := Lib.of_pa pa_proves_leAddLeAdd

/-- `n ≤ y → n ≤ x + y` (the left twin of `leAddRight`). -/
noncomputable def leAddLeftB : ArithmeticSemisentence 3 := “y x n. n ≤ y → n ≤ x + y”
noncomputable def leAddLeft : ArithmeticSentence := ∀¹* leAddLeftB

lemma models_leAddLeft : V↓[ℒₒᵣ] ⊧ leAddLeft ↔ ∀ y x n : V, n ≤ y → n ≤ x + y := by
  simp [leAddLeft, leAddLeftB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_leAddLeft : 𝗣𝗔 ⊢ leAddLeft :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_leAddLeft.mpr fun _ _ _ h ↦ le_trans h le_add_self

theorem lib_leAddLeft : Lib leAddLeft := Lib.of_pa pa_proves_leAddLeft

/-- `x ≤ x`. -/
noncomputable def leReflB : ArithmeticSemisentence 1 := “x. x ≤ x”
noncomputable def leRefl : ArithmeticSentence := ∀¹* leReflB

lemma models_leRefl : V↓[ℒₒᵣ] ⊧ leRefl ↔ ∀ x : V, x ≤ x := by
  simp [leRefl, leReflB, models_iff]

theorem pa_proves_leRefl : 𝗣𝗔 ⊢ leRefl :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_leRefl.mpr fun x ↦ le_refl x

theorem lib_leRefl : Lib leRefl := Lib.of_pa pa_proves_leRefl

/-- **The syntax bridge**: the DSL numeral `1` (what the `dlen` rows and the rows above
produce) against `Lengths.lean`'s `oneO` (what the `bnum` bit laws `twoMulOneSucc`, `succLeSucc`
consume): `x + 1 = x + oneO`. Neither side is `rfl`-equal to the other as syntax; with `leOfLeEq`
one row use crosses over. -/
noncomputable def dslSuccEqSuccOB : ArithmeticSemisentence 1 := eqO ‘x. x + 1’ (addO #0 oneO)
noncomputable def dslSuccEqSuccO : ArithmeticSentence := ∀¹* dslSuccEqSuccOB

lemma models_dslSuccEqSuccO : V↓[ℒₒᵣ] ⊧ dslSuccEqSuccO ↔ ∀ x : V, x + 1 = x + 1 := by
  simp [dslSuccEqSuccO, dslSuccEqSuccOB, eqO, addO, oneO, models_iff]

theorem pa_proves_dslSuccEqSuccO : 𝗣𝗔 ⊢ dslSuccEqSuccO :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_dslSuccEqSuccO.mpr fun _ ↦ rfl

theorem lib_dslSuccEqSuccO : Lib dslSuccEqSuccO := Lib.of_pa pa_proves_dslSuccEqSuccO

/-! ### Syntax facts (the DSL against `Lengths.lean`'s term-level syntax) -/

example : (“x y. x + y = y + x” : ArithmeticSemisentence 2) = addCommB := rfl
example : (“x y. x ≤ y” : ArithmeticSemisentence 2) = leF #0 #1 := rfl
example : (“x. x + 1 = x + 1” : ArithmeticSemisentence 1) = eqO ‘x. x + 1’ ‘x. x + 1’ := rfl

end ArithS
