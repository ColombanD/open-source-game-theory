import ArithS.Necessitation.Lib.Walk
import ArithS.Necessitation.WalkLemmas

/-!
# ArithS.Necessitation.Lib.Occ — occurrence-count and shift-length rows of the library `Λ`

`DESIGN_inner_necessitation.md` §4.1–4.2 and `DESIGN_describe.md` §9.2 / summary item 15: the
`proofLen` bookkeeping of the verification proof bounds the length of every node by a binary numeral,
and at `allIntro`/`shiftRule` sites the node's sequent is a SHIFTED sequent whose length the
`Lengths.lean` rows cannot bound (the term vector of a shifted atom is opaque). `ShiftLen.lean`
proved the exact laws `termLen (termShift t) = termLen t + fvOcc t`, `formulaLen (shift p) =
formulaLen p + fvOccF p`, `sequentLen (setShift s) ≤ sequentLen s + fvOccS s`; this module states them,
the occurrence counts' totality and per-constructor equations, the `free`/`subst` occurrence
bounds of `WalkLemmas.lean`, and the `O(1)` order glue §4.1's node recurrence needs, as library
rows on the `Lengths.lean` convention (body `xB` in index order, `x := ∀¹* xB`, `models_x`,
`pa_proves_x`, `lib_x`; Δ₁ hypotheses `.pi`, conclusions `.sigma`; every auxiliary object a
universal variable with its graph as a hypothesis — the totality rows supply the witnesses).

Sections:
1. Totality: `fvOccTotal`, `fvOccVecTotal`, `fvOccFTotal`, `fvOccSTotal`, `bvOccFTotal`.
2. Per constructor: `fvOccBvar/Fvar/Func`, `fvOccFRel/NRel/Verum/Falsum/And/Or/All/Exs`,
   `fvOccSInsertLe`, `fvOccSEmpty`.
3. Shift laws and bounds: `termLenShift`, `formulaLenShift`, `sequentLenSetShiftLe`, `fvOccFShift`,
   `fvOccSSetShiftLe`, `fvOccTermShift`; sanity `fvOccLeTermLen`, `fvOccFLeFormulaLen`,
   `fvOccSLeSetLen`; `fvOccFFreeLe'` (via `shiftGraph` + `substs1Graph`, Foundation has no
   `free` graph) and `fvOccFSubstLe` (the entry bound `M` over the vector code `w` in the `.pi`
   shape Foundation's own `isSemitermVec` uses: `∀ i < n, ∀ e, !nthDef e w i → ∀ x,
   !(fvOccGraph LAct) x e → x ≤ M`).
4. The §4.1 node bookkeeping, in the DSL syntax the `proofLen` rows of `Nodes.lean` produce (the DSL
   numeral `1` is NOT `rfl`-equal to `Lengths.lean`'s `oneO`, while DSL `+`, `=`, `≤` ARE
   `addO`, `eqO`, `leF`): `proofLenLeafLe`, `proofLenUnaryLe`, `proofLenBinaryLe` (one row use per node),
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

/-- `sequentLen (setShift s) ≤ sequentLen s + fvOccS s` (`sequentLen_setShift_le_occ`; the shape of
`sequentLenInsertLe` — the shifted set's length arrives from `sequentLenTotal`). -/
noncomputable def sequentLenSetShiftLeB : ArithmeticSemisentence 5 :=
  “l' o l s' s. !(isFormulaSet LAct).pi s → !(setShiftGraph LAct) s' s → !(sequentLenDef LAct) l s →
    !(fvOccSDef LAct) o s → !(sequentLenDef LAct) l' s' → l' ≤ l + o”
noncomputable def sequentLenSetShiftLe : ArithmeticSentence := ∀¹* sequentLenSetShiftLeB

lemma models_sequentLenSetShiftLe :
    V↓[ℒₒᵣ] ⊧ sequentLenSetShiftLe ↔
    ∀ l' o l s' s : V, IsFormulaSet LAct s → s' = setShift LAct s → l = sequentLen LAct s →
      o = fvOccS LAct s → l' = sequentLen LAct s' → l' ≤ l + o := by
  simp [sequentLenSetShiftLe, sequentLenSetShiftLeB, models_iff, Matrix.vecForall_iff, sequentLen_defined.iff,
    fvOccS_defined.iff, setShift.defined.iff]

theorem pa_proves_sequentLenSetShiftLe : 𝗣𝗔 ⊢ sequentLenSetShiftLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_sequentLenSetShiftLe.mpr fun _ _ _ _ _ hs hs' hl ho hl' ↦ by
    subst hs'; subst hl; subst ho; subst hl'; exact sequentLen_setShift_le_occ hs

theorem lib_sequentLenSetShiftLe : Lib sequentLenSetShiftLe := Lib.of_pa pa_proves_sequentLenSetShiftLe

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

`Nodes.lean`'s `proofLen` rows conclude `!(proofLenGraphDef LAct).sigma e (l + np + nq + 1)` in the DSL;
the DSL `+`, `=`, `≤` are `rfl`-equal to `Lengths.lean`'s `addO`, `eqO`, `leF`, but the DSL
numeral `1` is not `rfl`-equal to `oneO`, so the rows that must match a `proofLen` conclusion are
stated here in the DSL. -/

/-- Leaf: `n = l + 1 → l ≤ a → n ≤ a + 1` (`proofLenAxL`, `proofLenVerum`). -/
noncomputable def proofLenLeafLeB : ArithmeticSemisentence 3 :=
  “a l n. n = l + 1 → l ≤ a → n ≤ a + 1”
noncomputable def proofLenLeafLe : ArithmeticSentence := ∀¹* proofLenLeafLeB

lemma models_proofLenLeafLe : V↓[ℒₒᵣ] ⊧ proofLenLeafLe ↔ ∀ a l n : V, n = l + 1 → l ≤ a → n ≤ a + 1 := by
  simp [proofLenLeafLe, proofLenLeafLeB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_proofLenLeafLe : 𝗣𝗔 ⊢ proofLenLeafLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_proofLenLeafLe.mpr fun _ _ _ hn hl ↦ by
    subst hn; exact add_le_add hl (le_refl 1)

theorem lib_proofLenLeafLe : Lib proofLenLeafLe := Lib.of_pa pa_proves_proofLenLeafLe

/-- Unary node: `n = l + n₁ + 1 → l ≤ a → n₁ ≤ b → n ≤ a + b + 1` (`proofLenOr`, `proofLenAll`, …). -/
noncomputable def proofLenUnaryLeB : ArithmeticSemisentence 5 :=
  “b a np l n. n = l + np + 1 → l ≤ a → np ≤ b → n ≤ a + b + 1”
noncomputable def proofLenUnaryLe : ArithmeticSentence := ∀¹* proofLenUnaryLeB

lemma models_proofLenUnaryLe :
    V↓[ℒₒᵣ] ⊧ proofLenUnaryLe ↔ ∀ b a np l n : V, n = l + np + 1 → l ≤ a → np ≤ b → n ≤ a + b + 1 := by
  simp [proofLenUnaryLe, proofLenUnaryLeB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_proofLenUnaryLe : 𝗣𝗔 ⊢ proofLenUnaryLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_proofLenUnaryLe.mpr fun _ _ _ _ _ hn hl hp ↦ by
    subst hn; exact add_le_add (add_le_add hl hp) (le_refl 1)

theorem lib_proofLenUnaryLe : Lib proofLenUnaryLe := Lib.of_pa pa_proves_proofLenUnaryLe

/-- Binary node, §4.1's recurrence: `n = l + n₁ + n₂ + 1 → l ≤ a → n₁ ≤ b → n₂ ≤ c →
n ≤ a + b + c + 1` (`proofLenAnd`, cut). -/
noncomputable def proofLenBinaryLeB : ArithmeticSemisentence 7 :=
  “c b a nq np l n. n = l + np + nq + 1 → l ≤ a → np ≤ b → nq ≤ c → n ≤ a + b + c + 1”
noncomputable def proofLenBinaryLe : ArithmeticSentence := ∀¹* proofLenBinaryLeB

lemma models_proofLenBinaryLe :
    V↓[ℒₒᵣ] ⊧ proofLenBinaryLe ↔
    ∀ c b a nq np l n : V, n = l + np + nq + 1 → l ≤ a → np ≤ b → nq ≤ c → n ≤ a + b + c + 1 := by
  simp [proofLenBinaryLe, proofLenBinaryLeB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_proofLenBinaryLe : 𝗣𝗔 ⊢ proofLenBinaryLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_proofLenBinaryLe.mpr fun _ _ _ _ _ _ _ hn hl hp hq ↦ by
    subst hn; exact add_le_add (add_le_add (add_le_add hl hp) hq) (le_refl 1)

theorem lib_proofLenBinaryLe : Lib proofLenBinaryLe := Lib.of_pa pa_proves_proofLenBinaryLe

/-- `x ≤ y + z → y ≤ a → z ≤ b → x ≤ a + b` (§4.2: `sequentLen s' ≤ sequentLen s + formulaLen p`
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

/-- `x ≤ x`. -/
noncomputable def leReflB : ArithmeticSemisentence 1 := “x. x ≤ x”
noncomputable def leRefl : ArithmeticSentence := ∀¹* leReflB

lemma models_leRefl : V↓[ℒₒᵣ] ⊧ leRefl ↔ ∀ x : V, x ≤ x := by
  simp [leRefl, leReflB, models_iff]

theorem pa_proves_leRefl : 𝗣𝗔 ⊢ leRefl :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_leRefl.mpr fun x ↦ le_refl x

theorem lib_leRefl : Lib leRefl := Lib.of_pa pa_proves_leRefl

/-- **The syntax bridge**: the DSL numeral `1` (what the `proofLen` rows and the rows above
produce) against `Lengths.lean`'s `oneO` (what the `binNumeral` bit laws `twoMulOneSucc`, `succLeSucc`
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
