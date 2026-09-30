import ArithS.Necessitation.Primitives
import ArithS.Necessitation.Lib.Basic

/-!
# ArithS.Necessitation.Lib.Nodes — the node rows of the library `Λ`

`DESIGN_inner_necessitation.md` §1.4, §3.1 (rows `Intro_tag`, `ProofLen_tag`, `axioms`), §3.6:
the per-tag INTRODUCTION clauses of the derivation fixpoint, the per-tag `proofLen` clauses of
the length graph, the totality of the ten node-code graphs, and the axiom recognizer — each an
`ℒₒᵣ`-sentence in PRENEX universal form over the SAME formula objects the target sentence uses
(`!(derivation TAct).sigma`, `!(proofLenGraphDef LAct).sigma`, `!(sequentLenDef LAct)`,
`!(termLenGraph LAct)`, `!(isFormulaSet LAct).pi`, `!insertDef`, `!fstIdxDef`,
`!bitSubsetDef`, the Σ₀ node graphs `axLGraph … axmGraph`, `!(Theory.Δ₁ch TAct).sigma`),
true in every model of `𝗜𝚺₁` (Foundation's `Derivation.axL … axm` and the package's
`ProofLenGraph.*_iff`), hence `𝗣𝗔`-theorems (`complete`) and library sentences (`Lib`).

**Conventions** (the `Sets` file's, with the polarity the target forces):
* every auxiliary object of a clause (`fstIdx dp`, `insert p s`, `neg p`, `free p`,
  `setShift s`, the node code `e`) is a UNIVERSAL variable with its graph as a hypothesis —
  the fragments name every such object by an eigenvariable and never prove an existential
  to use a row; the ten totality rows (`∀ …, ∃ e, !…Graph e …`) supply the node codes;
* `derivation` and `proofLenGraph` facts are `.sigma` in hypotheses AND conclusions — the
  polarity of `lenBoxUnboundedDef` (`proof.sigma`), so a sub-goal's output feeds the next row
  without a bridge (the `.sigma ↔ .pi` bridges are provided anyway);
* `IsFormulaSet` hypotheses are `.pi` (the `Sets` convention, bridges there);
* the `axm` premise `p ∈ T.Δ₁Class` is `!(Theory.Δ₁ch TAct).sigma p`, the form the
  recognizer rows produce;
* membership `r ∈ s` is the DSL's `∈`, the same Δ₀ formula the fixpoint blueprint uses;
* DSL names are listed in index order (`x₀ = #0`, the INNERMOST quantifier of `∀¹*`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### `Intro_tag` — the ten introduction clauses (`Derivation.axL … axm` on codes) -/

/-- `Intro_axL`: `IsFormulaSet s → p ∈ s → neg p ∈ s → derivation (axL s p)`. -/
noncomputable def introAxLB : ArithmeticSemisentence 4 :=
  “e np p s. !(isFormulaSet LAct).pi s → p ∈ s → !(negGraph LAct) np p → np ∈ s →
    !axLGraph e s p → !(derivation TAct).sigma e”
noncomputable def introAxL : ArithmeticSentence := ∀¹* introAxLB

lemma models_introAxL :
    V↓[ℒₒᵣ] ⊧ introAxL ↔ ∀ e np p s : V,
      IsFormulaSet LAct s → p ∈ s → np = neg LAct p → np ∈ s → e = axL s p →
      Derivation TAct e := by
  simp [introAxL, introAxLB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_introAxL : 𝗣𝗔 ⊢ introAxL :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_introAxL.mpr
    fun _ _ _ _ hs hp hnp hnps he ↦ by subst hnp he; exact Derivation.axL hs hp hnps

theorem lib_introAxL : Lib introAxL := Lib.of_pa pa_proves_introAxL

/-- `Intro_verum`: `IsFormulaSet s → ^⊤ ∈ s → derivation (verumIntro s)`. -/
noncomputable def introVerumB : ArithmeticSemisentence 3 :=
  “e v s. !(isFormulaSet LAct).pi s → !qqVerumDef v → v ∈ s →
    !verumIntroGraph e s → !(derivation TAct).sigma e”
noncomputable def introVerum : ArithmeticSentence := ∀¹* introVerumB

lemma models_introVerum :
    V↓[ℒₒᵣ] ⊧ introVerum ↔ ∀ e v s : V,
      IsFormulaSet LAct s → v = ^⊤ → v ∈ s → e = verumIntro s → Derivation TAct e := by
  simp [introVerum, introVerumB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_introVerum : 𝗣𝗔 ⊢ introVerum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_introVerum.mpr
    fun _ _ _ hs hv hvs he ↦ by subst hv he; exact Derivation.verumIntro hs hvs

theorem lib_introVerum : Lib introVerum := Lib.of_pa pa_proves_introVerum

/-- `Intro_and`: `p ⋏ q ∈ s → DerivationOf dp (insert p s) → DerivationOf dq (insert q s) →
derivation (andIntro s p q dp dq)`. -/
noncomputable def introAndB : ArithmeticSemisentence 9 :=
  “e cq cp r dq dp q p s. !andIntroGraph e s p q dp dq → !qqAndDef r p q → r ∈ s →
    !fstIdxDef cp dp → !insertDef cp p s → !(derivation TAct).sigma dp →
    !fstIdxDef cq dq → !insertDef cq q s → !(derivation TAct).sigma dq →
    !(derivation TAct).sigma e”
noncomputable def introAnd : ArithmeticSentence := ∀¹* introAndB

lemma models_introAnd :
    V↓[ℒₒᵣ] ⊧ introAnd ↔ ∀ e cq cp r dq dp q p s : V,
      e = andIntro s p q dp dq → r = p ^⋏ q → r ∈ s →
      cp = fstIdx dp → cp = insert p s → Derivation TAct dp →
      cq = fstIdx dq → cq = insert q s → Derivation TAct dq → Derivation TAct e := by
  simp [introAnd, introAndB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_introAnd : 𝗣𝗔 ⊢ introAnd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_introAnd.mpr
    fun _ _ _ _ _ _ _ _ _ he hr hrs hcp hcp' hdp hcq hcq' hdq ↦ by
      subst he hr
      exact Derivation.andIntro hrs ⟨hcp.symm.trans hcp', hdp⟩ ⟨hcq.symm.trans hcq', hdq⟩

theorem lib_introAnd : Lib introAnd := Lib.of_pa pa_proves_introAnd

/-- `Intro_or`: `p ⋎ q ∈ s → DerivationOf d (insert p (insert q s)) → derivation (orIntro s p q d)`. -/
noncomputable def introOrB : ArithmeticSemisentence 8 :=
  “e c c' r d q p s. !orIntroGraph e s p q d → !qqOrDef r p q → r ∈ s →
    !fstIdxDef c d → !insertDef c' q s → !insertDef c p c' → !(derivation TAct).sigma d →
    !(derivation TAct).sigma e”
noncomputable def introOr : ArithmeticSentence := ∀¹* introOrB

lemma models_introOr :
    V↓[ℒₒᵣ] ⊧ introOr ↔ ∀ e c c' r d q p s : V,
      e = orIntro s p q d → r = p ^⋎ q → r ∈ s →
      c = fstIdx d → c' = insert q s → c = insert p c' → Derivation TAct d →
      Derivation TAct e := by
  simp [introOr, introOrB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_introOr : 𝗣𝗔 ⊢ introOr :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_introOr.mpr
    fun _ _ _ _ _ _ _ _ he hr hrs hc hc' hc'' hd ↦ by
      subst he hr hc'
      exact Derivation.orIntro hrs ⟨hc.symm.trans hc'', hd⟩

theorem lib_introOr : Lib introOr := Lib.of_pa pa_proves_introOr

/-- `Intro_all`: `^∀ p ∈ s → DerivationOf d (insert (free p) (setShift s)) → derivation (allIntro s p d)`. -/
noncomputable def introAllB : ArithmeticSemisentence 8 :=
  “e c ss fp r d p s. !allIntroGraph e s p d → !qqAllDef r p → r ∈ s →
    !fstIdxDef c d → !(freeGraph LAct) fp p → !(setShiftGraph LAct) ss s → !insertDef c fp ss →
    !(derivation TAct).sigma d → !(derivation TAct).sigma e”
noncomputable def introAll : ArithmeticSentence := ∀¹* introAllB

lemma models_introAll :
    V↓[ℒₒᵣ] ⊧ introAll ↔ ∀ e c ss fp r d p s : V,
      e = allIntro s p d → r = ^∀ p → r ∈ s →
      c = fstIdx d → fp = free LAct p → ss = setShift LAct s → c = insert fp ss →
      Derivation TAct d → Derivation TAct e := by
  simp [introAll, introAllB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_introAll : 𝗣𝗔 ⊢ introAll :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_introAll.mpr
    fun _ _ _ _ _ _ _ _ he hr hrs hc hfp hss hc' hd ↦ by
      subst he hr hfp hss
      exact Derivation.allIntro hrs ⟨hc.symm.trans hc', hd⟩

theorem lib_introAll : Lib introAll := Lib.of_pa pa_proves_introAll

/-- `Intro_exs`: `^∃ p ∈ s → IsTerm t → DerivationOf d (insert (substs1 t p) s) →
derivation (exsIntro s p t d)`. -/
noncomputable def introExsB : ArithmeticSemisentence 9 :=
  “e c pt r d t p s. !exsIntroGraph e s p t d → !qqExsDef r p → r ∈ s →
    !(isSemiterm LAct).pi 0 t → !fstIdxDef c d → !(substs1Graph LAct) pt t p → !insertDef c pt s →
    !(derivation TAct).sigma d → !(derivation TAct).sigma e”
noncomputable def introExs : ArithmeticSentence := ∀¹* introExsB

lemma models_introExs :
    V↓[ℒₒᵣ] ⊧ introExs ↔ ∀ e c pt r d t p s : V,
      e = exsIntro s p t d → r = ^∃ p → r ∈ s →
      IsSemiterm LAct 0 t → c = fstIdx d → pt = substs1 LAct t p → c = insert pt s →
      Derivation TAct d → Derivation TAct e := by
  simp [introExs, introExsB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_introExs : 𝗣𝗔 ⊢ introExs :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_introExs.mpr
    fun _ _ _ _ _ _ _ _ he hr hrs ht hc hpt hc' hd ↦ by
      subst he hr hpt
      exact Derivation.exsIntro hrs ht ⟨hc.symm.trans hc', hd⟩

theorem lib_introExs : Lib introExs := Lib.of_pa pa_proves_introExs

/-- `Intro_wk`: `IsFormulaSet s → fstIdx d ⊆ s → derivation d → derivation (wkRule s d)`. -/
noncomputable def introWkB : ArithmeticSemisentence 4 :=
  “e c d s. !(isFormulaSet LAct).pi s → !fstIdxDef c d → !bitSubsetDef c s →
    !(derivation TAct).sigma d → !wkRuleGraph e s d → !(derivation TAct).sigma e”
noncomputable def introWk : ArithmeticSentence := ∀¹* introWkB

lemma models_introWk :
    V↓[ℒₒᵣ] ⊧ introWk ↔ ∀ e c d s : V,
      IsFormulaSet LAct s → c = fstIdx d → c ⊆ s → Derivation TAct d → e = wkRule s d →
      Derivation TAct e := by
  simp [introWk, introWkB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_introWk : 𝗣𝗔 ⊢ introWk :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_introWk.mpr
    fun _ _ _ _ hs hc hcs hd he ↦ by subst he hc; exact Derivation.wkRule hs hcs ⟨rfl, hd⟩

theorem lib_introWk : Lib introWk := Lib.of_pa pa_proves_introWk

/-- `Intro_shift`: `derivation d → derivation (shiftRule (setShift (fstIdx d)) d)`. -/
noncomputable def introShiftB : ArithmeticSemisentence 4 :=
  “e ss c d. !fstIdxDef c d → !(setShiftGraph LAct) ss c → !(derivation TAct).sigma d →
    !shiftRuleGraph e ss d → !(derivation TAct).sigma e”
noncomputable def introShift : ArithmeticSentence := ∀¹* introShiftB

lemma models_introShift :
    V↓[ℒₒᵣ] ⊧ introShift ↔ ∀ e ss c d : V,
      c = fstIdx d → ss = setShift LAct c → Derivation TAct d → e = shiftRule ss d →
      Derivation TAct e := by
  simp [introShift, introShiftB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_introShift : 𝗣𝗔 ⊢ introShift :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_introShift.mpr
    fun _ _ _ _ hc hss hd he ↦ by subst hc hss he; exact Derivation.shiftRule ⟨rfl, hd⟩

theorem lib_introShift : Lib introShift := Lib.of_pa pa_proves_introShift

/-- `Intro_cut`: `DerivationOf d₁ (insert p s) → DerivationOf d₂ (insert (neg p) s) →
derivation (cutRule s p d₁ d₂)`. -/
noncomputable def introCutB : ArithmeticSemisentence 9 :=
  “e c₂ np c₁ d₂ d₁ p s. !cutRuleGraph e s p d₁ d₂ →
    !fstIdxDef c₁ d₁ → !insertDef c₁ p s → !(derivation TAct).sigma d₁ →
    !fstIdxDef c₂ d₂ → !(negGraph LAct) np p → !insertDef c₂ np s → !(derivation TAct).sigma d₂ →
    !(derivation TAct).sigma e”
noncomputable def introCut : ArithmeticSentence := ∀¹* introCutB

lemma models_introCut :
    V↓[ℒₒᵣ] ⊧ introCut ↔ ∀ e c₂ np c₁ d₂ d₁ p s : V,
      e = cutRule s p d₁ d₂ →
      c₁ = fstIdx d₁ → c₁ = insert p s → Derivation TAct d₁ →
      c₂ = fstIdx d₂ → np = neg LAct p → c₂ = insert np s → Derivation TAct d₂ →
      Derivation TAct e := by
  simp [introCut, introCutB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_introCut : 𝗣𝗔 ⊢ introCut :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_introCut.mpr
    fun _ _ _ _ _ _ _ _ he hc₁ hc₁' hd₁ hc₂ hnp hc₂' hd₂ ↦ by
      subst he hnp
      exact Derivation.cutRule ⟨hc₁.symm.trans hc₁', hd₁⟩ ⟨hc₂.symm.trans hc₂', hd₂⟩

theorem lib_introCut : Lib introCut := Lib.of_pa pa_proves_introCut

/-- `Intro_axm`: `IsFormulaSet s → p ∈ s → TAct.Δ₁ch p → derivation (axm s p)`. -/
noncomputable def introAxmB : ArithmeticSemisentence 3 :=
  “e p s. !(isFormulaSet LAct).pi s → p ∈ s → !(Theory.Δ₁ch TAct).sigma p →
    !axmGraph e s p → !(derivation TAct).sigma e”
noncomputable def introAxm : ArithmeticSentence := ∀¹* introAxmB

lemma models_introAxm :
    V↓[ℒₒᵣ] ⊧ introAxm ↔ ∀ e p s : V,
      IsFormulaSet LAct s → p ∈ s → p ∈ TAct.Δ₁Class → e = axm s p → Derivation TAct e := by
  simp [introAxm, introAxmB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_introAxm : 𝗣𝗔 ⊢ introAxm :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_introAxm.mpr
    fun _ _ _ hs hp hT he ↦ by subst he; exact Derivation.axm hs hp hT

theorem lib_introAxm : Lib introAxm := Lib.of_pa pa_proves_introAxm

/-! ### Totality of the ten node-code graphs -/

noncomputable def totAxLB : ArithmeticSemisentence 2 := “p s. ∃ e, !axLGraph e s p”
noncomputable def totAxL : ArithmeticSentence := ∀¹* totAxLB
lemma models_totAxL : V↓[ℒₒᵣ] ⊧ totAxL ↔ ∀ p s : V, ∃ e, e = axL s p := by
  simp [totAxL, totAxLB, models_iff]
theorem pa_proves_totAxL : 𝗣𝗔 ⊢ totAxL :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_totAxL.mpr fun _ _ ↦ ⟨_, rfl⟩
theorem lib_totAxL : Lib totAxL := Lib.of_pa pa_proves_totAxL

noncomputable def totVerumIntroB : ArithmeticSemisentence 1 := “s. ∃ e, !verumIntroGraph e s”
noncomputable def totVerumIntro : ArithmeticSentence := ∀¹* totVerumIntroB
lemma models_totVerumIntro : V↓[ℒₒᵣ] ⊧ totVerumIntro ↔ ∀ s : V, ∃ e, e = verumIntro s := by
  simp [totVerumIntro, totVerumIntroB, models_iff]
theorem pa_proves_totVerumIntro : 𝗣𝗔 ⊢ totVerumIntro :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_totVerumIntro.mpr fun _ ↦ ⟨_, rfl⟩
theorem lib_totVerumIntro : Lib totVerumIntro := Lib.of_pa pa_proves_totVerumIntro

noncomputable def totAndIntroB : ArithmeticSemisentence 5 :=
  “dq dp q p s. ∃ e, !andIntroGraph e s p q dp dq”
noncomputable def totAndIntro : ArithmeticSentence := ∀¹* totAndIntroB
lemma models_totAndIntro :
    V↓[ℒₒᵣ] ⊧ totAndIntro ↔ ∀ dq dp q p s : V, ∃ e, e = andIntro s p q dp dq := by
  simp [totAndIntro, totAndIntroB, models_iff]
theorem pa_proves_totAndIntro : 𝗣𝗔 ⊢ totAndIntro :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_totAndIntro.mpr fun _ _ _ _ _ ↦ ⟨_, rfl⟩
theorem lib_totAndIntro : Lib totAndIntro := Lib.of_pa pa_proves_totAndIntro

noncomputable def totOrIntroB : ArithmeticSemisentence 4 := “d q p s. ∃ e, !orIntroGraph e s p q d”
noncomputable def totOrIntro : ArithmeticSentence := ∀¹* totOrIntroB
lemma models_totOrIntro : V↓[ℒₒᵣ] ⊧ totOrIntro ↔ ∀ d q p s : V, ∃ e, e = orIntro s p q d := by
  simp [totOrIntro, totOrIntroB, models_iff]
theorem pa_proves_totOrIntro : 𝗣𝗔 ⊢ totOrIntro :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_totOrIntro.mpr fun _ _ _ _ ↦ ⟨_, rfl⟩
theorem lib_totOrIntro : Lib totOrIntro := Lib.of_pa pa_proves_totOrIntro

noncomputable def totAllIntroB : ArithmeticSemisentence 3 := “d p s. ∃ e, !allIntroGraph e s p d”
noncomputable def totAllIntro : ArithmeticSentence := ∀¹* totAllIntroB
lemma models_totAllIntro : V↓[ℒₒᵣ] ⊧ totAllIntro ↔ ∀ d p s : V, ∃ e, e = allIntro s p d := by
  simp [totAllIntro, totAllIntroB, models_iff]
theorem pa_proves_totAllIntro : 𝗣𝗔 ⊢ totAllIntro :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_totAllIntro.mpr fun _ _ _ ↦ ⟨_, rfl⟩
theorem lib_totAllIntro : Lib totAllIntro := Lib.of_pa pa_proves_totAllIntro

noncomputable def totExsIntroB : ArithmeticSemisentence 4 := “d t p s. ∃ e, !exsIntroGraph e s p t d”
noncomputable def totExsIntro : ArithmeticSentence := ∀¹* totExsIntroB
lemma models_totExsIntro : V↓[ℒₒᵣ] ⊧ totExsIntro ↔ ∀ d t p s : V, ∃ e, e = exsIntro s p t d := by
  simp [totExsIntro, totExsIntroB, models_iff]
theorem pa_proves_totExsIntro : 𝗣𝗔 ⊢ totExsIntro :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_totExsIntro.mpr fun _ _ _ _ ↦ ⟨_, rfl⟩
theorem lib_totExsIntro : Lib totExsIntro := Lib.of_pa pa_proves_totExsIntro

noncomputable def totWkRuleB : ArithmeticSemisentence 2 := “d s. ∃ e, !wkRuleGraph e s d”
noncomputable def totWkRule : ArithmeticSentence := ∀¹* totWkRuleB
lemma models_totWkRule : V↓[ℒₒᵣ] ⊧ totWkRule ↔ ∀ d s : V, ∃ e, e = wkRule s d := by
  simp [totWkRule, totWkRuleB, models_iff]
theorem pa_proves_totWkRule : 𝗣𝗔 ⊢ totWkRule :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_totWkRule.mpr fun _ _ ↦ ⟨_, rfl⟩
theorem lib_totWkRule : Lib totWkRule := Lib.of_pa pa_proves_totWkRule

noncomputable def totShiftRuleB : ArithmeticSemisentence 2 := “d s. ∃ e, !shiftRuleGraph e s d”
noncomputable def totShiftRule : ArithmeticSentence := ∀¹* totShiftRuleB
lemma models_totShiftRule : V↓[ℒₒᵣ] ⊧ totShiftRule ↔ ∀ d s : V, ∃ e, e = shiftRule s d := by
  simp [totShiftRule, totShiftRuleB, models_iff]
theorem pa_proves_totShiftRule : 𝗣𝗔 ⊢ totShiftRule :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_totShiftRule.mpr fun _ _ ↦ ⟨_, rfl⟩
theorem lib_totShiftRule : Lib totShiftRule := Lib.of_pa pa_proves_totShiftRule

noncomputable def totCutRuleB : ArithmeticSemisentence 4 := “d₂ d₁ p s. ∃ e, !cutRuleGraph e s p d₁ d₂”
noncomputable def totCutRule : ArithmeticSentence := ∀¹* totCutRuleB
lemma models_totCutRule : V↓[ℒₒᵣ] ⊧ totCutRule ↔ ∀ d₂ d₁ p s : V, ∃ e, e = cutRule s p d₁ d₂ := by
  simp [totCutRule, totCutRuleB, models_iff]
theorem pa_proves_totCutRule : 𝗣𝗔 ⊢ totCutRule :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_totCutRule.mpr fun _ _ _ _ ↦ ⟨_, rfl⟩
theorem lib_totCutRule : Lib totCutRule := Lib.of_pa pa_proves_totCutRule

noncomputable def totAxmB : ArithmeticSemisentence 2 := “p s. ∃ e, !axmGraph e s p”
noncomputable def totAxm : ArithmeticSentence := ∀¹* totAxmB
lemma models_totAxm : V↓[ℒₒᵣ] ⊧ totAxm ↔ ∀ p s : V, ∃ e, e = axm s p := by
  simp [totAxm, totAxmB, models_iff]
theorem pa_proves_totAxm : 𝗣𝗔 ⊢ totAxm :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_totAxm.mpr fun _ _ ↦ ⟨_, rfl⟩
theorem lib_totAxm : Lib totAxm := Lib.of_pa pa_proves_totAxm

/-! ### `ProofLen_tag` — the ten length clauses (`ProofLenGraph.*_iff`, the `mpr` direction) -/

/-- `ProofLen_axL`: `proofLenGraph (axL s p) (sequentLen s + 1)`. -/
noncomputable def proofLenAxLB : ArithmeticSemisentence 4 :=
  “l p s e. !axLGraph e s p → !(sequentLenDef LAct) l s → !(proofLenGraphDef LAct).sigma e (l + 1)”
noncomputable def proofLenAxL : ArithmeticSentence := ∀¹* proofLenAxLB
lemma models_proofLenAxL : V↓[ℒₒᵣ] ⊧ proofLenAxL ↔ ∀ l p s e : V,
    e = axL s p → l = sequentLen LAct s → ProofLenGraph LAct e (l + 1) := by
  simp [proofLenAxL, proofLenAxLB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_proofLenAxL : 𝗣𝗔 ⊢ proofLenAxL :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_proofLenAxL.mpr fun _ _ _ _ he hl ↦ by
    subst he hl; exact ProofLenGraph.axL_iff.mpr rfl
theorem lib_proofLenAxL : Lib proofLenAxL := Lib.of_pa pa_proves_proofLenAxL

/-- `ProofLen_verum`: `proofLenGraph (verumIntro s) (sequentLen s + 1)`. -/
noncomputable def proofLenVerumB : ArithmeticSemisentence 3 :=
  “l s e. !verumIntroGraph e s → !(sequentLenDef LAct) l s → !(proofLenGraphDef LAct).sigma e (l + 1)”
noncomputable def proofLenVerum : ArithmeticSentence := ∀¹* proofLenVerumB
lemma models_proofLenVerum : V↓[ℒₒᵣ] ⊧ proofLenVerum ↔ ∀ l s e : V,
    e = verumIntro s → l = sequentLen LAct s → ProofLenGraph LAct e (l + 1) := by
  simp [proofLenVerum, proofLenVerumB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_proofLenVerum : 𝗣𝗔 ⊢ proofLenVerum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_proofLenVerum.mpr fun _ _ _ he hl ↦ by
    subst he hl; exact ProofLenGraph.verumIntro_iff.mpr rfl
theorem lib_proofLenVerum : Lib proofLenVerum := Lib.of_pa pa_proves_proofLenVerum

/-- `ProofLen_and`: `proofLen (andIntro s p q dp dq) = sequentLen s + proofLen dp + proofLen dq + 1`. -/
noncomputable def proofLenAndB : ArithmeticSemisentence 9 :=
  “l nq np dq dp q p s e. !andIntroGraph e s p q dp dq →
    !(proofLenGraphDef LAct).sigma dp np → !(proofLenGraphDef LAct).sigma dq nq → !(sequentLenDef LAct) l s →
    !(proofLenGraphDef LAct).sigma e (l + np + nq + 1)”
noncomputable def proofLenAnd : ArithmeticSentence := ∀¹* proofLenAndB
lemma models_proofLenAnd : V↓[ℒₒᵣ] ⊧ proofLenAnd ↔ ∀ l nq np dq dp q p s e : V,
    e = andIntro s p q dp dq → ProofLenGraph LAct dp np → ProofLenGraph LAct dq nq →
    l = sequentLen LAct s → ProofLenGraph LAct e (l + np + nq + 1) := by
  simp [proofLenAnd, proofLenAndB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_proofLenAnd : 𝗣𝗔 ⊢ proofLenAnd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_proofLenAnd.mpr fun _ _ _ _ _ _ _ _ _ he hp hq hl ↦ by
    subst he hl; exact ProofLenGraph.andIntro_iff.mpr ⟨_, _, hp, hq, rfl⟩
theorem lib_proofLenAnd : Lib proofLenAnd := Lib.of_pa pa_proves_proofLenAnd

/-- `ProofLen_or`: `proofLen (orIntro s p q d) = sequentLen s + proofLen d + 1`. -/
noncomputable def proofLenOrB : ArithmeticSemisentence 7 :=
  “l n d q p s e. !orIntroGraph e s p q d → !(proofLenGraphDef LAct).sigma d n → !(sequentLenDef LAct) l s →
    !(proofLenGraphDef LAct).sigma e (l + n + 1)”
noncomputable def proofLenOr : ArithmeticSentence := ∀¹* proofLenOrB
lemma models_proofLenOr : V↓[ℒₒᵣ] ⊧ proofLenOr ↔ ∀ l n d q p s e : V,
    e = orIntro s p q d → ProofLenGraph LAct d n → l = sequentLen LAct s → ProofLenGraph LAct e (l + n + 1) := by
  simp [proofLenOr, proofLenOrB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_proofLenOr : 𝗣𝗔 ⊢ proofLenOr :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_proofLenOr.mpr fun _ _ _ _ _ _ _ he hd hl ↦ by
    subst he hl; exact ProofLenGraph.orIntro_iff.mpr ⟨_, hd, rfl⟩
theorem lib_proofLenOr : Lib proofLenOr := Lib.of_pa pa_proves_proofLenOr

/-- `ProofLen_all`: `proofLen (allIntro s p d) = sequentLen s + proofLen d + 1`. -/
noncomputable def proofLenAllB : ArithmeticSemisentence 6 :=
  “l n d p s e. !allIntroGraph e s p d → !(proofLenGraphDef LAct).sigma d n → !(sequentLenDef LAct) l s →
    !(proofLenGraphDef LAct).sigma e (l + n + 1)”
noncomputable def proofLenAll : ArithmeticSentence := ∀¹* proofLenAllB
lemma models_proofLenAll : V↓[ℒₒᵣ] ⊧ proofLenAll ↔ ∀ l n d p s e : V,
    e = allIntro s p d → ProofLenGraph LAct d n → l = sequentLen LAct s → ProofLenGraph LAct e (l + n + 1) := by
  simp [proofLenAll, proofLenAllB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_proofLenAll : 𝗣𝗔 ⊢ proofLenAll :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_proofLenAll.mpr fun _ _ _ _ _ _ he hd hl ↦ by
    subst he hl; exact ProofLenGraph.allIntro_iff.mpr ⟨_, hd, rfl⟩
theorem lib_proofLenAll : Lib proofLenAll := Lib.of_pa pa_proves_proofLenAll

/-- `ProofLen_exs`: `proofLen (exsIntro s p t d) = sequentLen s + termLen t + proofLen d + 1`. -/
noncomputable def proofLenExsB : ArithmeticSemisentence 8 :=
  “lt l n d t p s e. !exsIntroGraph e s p t d → !(proofLenGraphDef LAct).sigma d n →
    !(sequentLenDef LAct) l s → !(termLenGraph LAct) lt t →
    !(proofLenGraphDef LAct).sigma e (l + lt + n + 1)”
noncomputable def proofLenExs : ArithmeticSentence := ∀¹* proofLenExsB
lemma models_proofLenExs : V↓[ℒₒᵣ] ⊧ proofLenExs ↔ ∀ lt l n d t p s e : V,
    e = exsIntro s p t d → ProofLenGraph LAct d n → l = sequentLen LAct s → lt = termLen LAct t →
    ProofLenGraph LAct e (l + lt + n + 1) := by
  simp [proofLenExs, proofLenExsB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_proofLenExs : 𝗣𝗔 ⊢ proofLenExs :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_proofLenExs.mpr fun _ _ _ _ _ _ _ _ he hd hl hlt ↦ by
    subst he hl hlt; exact ProofLenGraph.exsIntro_iff.mpr ⟨_, hd, rfl⟩
theorem lib_proofLenExs : Lib proofLenExs := Lib.of_pa pa_proves_proofLenExs

/-- `ProofLen_wk`: `proofLen (wkRule s d) = sequentLen s + proofLen d + 1`. -/
noncomputable def proofLenWkB : ArithmeticSemisentence 5 :=
  “l n d s e. !wkRuleGraph e s d → !(proofLenGraphDef LAct).sigma d n → !(sequentLenDef LAct) l s →
    !(proofLenGraphDef LAct).sigma e (l + n + 1)”
noncomputable def proofLenWk : ArithmeticSentence := ∀¹* proofLenWkB
lemma models_proofLenWk : V↓[ℒₒᵣ] ⊧ proofLenWk ↔ ∀ l n d s e : V,
    e = wkRule s d → ProofLenGraph LAct d n → l = sequentLen LAct s → ProofLenGraph LAct e (l + n + 1) := by
  simp [proofLenWk, proofLenWkB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_proofLenWk : 𝗣𝗔 ⊢ proofLenWk :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_proofLenWk.mpr fun _ _ _ _ _ he hd hl ↦ by
    subst he hl; exact ProofLenGraph.wkRule_iff.mpr ⟨_, hd, rfl⟩
theorem lib_proofLenWk : Lib proofLenWk := Lib.of_pa pa_proves_proofLenWk

/-- `ProofLen_shift`: `proofLen (shiftRule s d) = sequentLen s + proofLen d + 1`. -/
noncomputable def proofLenShiftB : ArithmeticSemisentence 5 :=
  “l n d s e. !shiftRuleGraph e s d → !(proofLenGraphDef LAct).sigma d n → !(sequentLenDef LAct) l s →
    !(proofLenGraphDef LAct).sigma e (l + n + 1)”
noncomputable def proofLenShift : ArithmeticSentence := ∀¹* proofLenShiftB
lemma models_proofLenShift : V↓[ℒₒᵣ] ⊧ proofLenShift ↔ ∀ l n d s e : V,
    e = shiftRule s d → ProofLenGraph LAct d n → l = sequentLen LAct s → ProofLenGraph LAct e (l + n + 1) := by
  simp [proofLenShift, proofLenShiftB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_proofLenShift : 𝗣𝗔 ⊢ proofLenShift :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_proofLenShift.mpr fun _ _ _ _ _ he hd hl ↦ by
    subst he hl; exact ProofLenGraph.shiftRule_iff.mpr ⟨_, hd, rfl⟩
theorem lib_proofLenShift : Lib proofLenShift := Lib.of_pa pa_proves_proofLenShift

/-- `ProofLen_cut`: `proofLen (cutRule s p d₁ d₂) = sequentLen s + proofLen d₁ + proofLen d₂ + 1`. -/
noncomputable def proofLenCutB : ArithmeticSemisentence 8 :=
  “l n₂ n₁ d₂ d₁ p s e. !cutRuleGraph e s p d₁ d₂ →
    !(proofLenGraphDef LAct).sigma d₁ n₁ → !(proofLenGraphDef LAct).sigma d₂ n₂ → !(sequentLenDef LAct) l s →
    !(proofLenGraphDef LAct).sigma e (l + n₁ + n₂ + 1)”
noncomputable def proofLenCut : ArithmeticSentence := ∀¹* proofLenCutB
lemma models_proofLenCut : V↓[ℒₒᵣ] ⊧ proofLenCut ↔ ∀ l n₂ n₁ d₂ d₁ p s e : V,
    e = cutRule s p d₁ d₂ → ProofLenGraph LAct d₁ n₁ → ProofLenGraph LAct d₂ n₂ →
    l = sequentLen LAct s → ProofLenGraph LAct e (l + n₁ + n₂ + 1) := by
  simp [proofLenCut, proofLenCutB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_proofLenCut : 𝗣𝗔 ⊢ proofLenCut :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_proofLenCut.mpr fun _ _ _ _ _ _ _ _ he h₁ h₂ hl ↦ by
    subst he hl; exact ProofLenGraph.cutRule_iff.mpr ⟨_, _, h₁, h₂, rfl⟩
theorem lib_proofLenCut : Lib proofLenCut := Lib.of_pa pa_proves_proofLenCut

/-- `ProofLen_axm`: `proofLenGraph (axm s p) (sequentLen s + 1)`. -/
noncomputable def proofLenAxmB : ArithmeticSemisentence 4 :=
  “l p s e. !axmGraph e s p → !(sequentLenDef LAct) l s → !(proofLenGraphDef LAct).sigma e (l + 1)”
noncomputable def proofLenAxm : ArithmeticSentence := ∀¹* proofLenAxmB
lemma models_proofLenAxm : V↓[ℒₒᵣ] ⊧ proofLenAxm ↔ ∀ l p s e : V,
    e = axm s p → l = sequentLen LAct s → ProofLenGraph LAct e (l + 1) := by
  simp [proofLenAxm, proofLenAxmB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_proofLenAxm : 𝗣𝗔 ⊢ proofLenAxm :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_proofLenAxm.mpr fun _ _ _ _ he hl ↦ by
    subst he hl; exact ProofLenGraph.axm_iff.mpr rfl
theorem lib_proofLenAxm : Lib proofLenAxm := Lib.of_pa pa_proves_proofLenAxm

/-! ### Properness bridges (`.sigma ↔ .pi`) for `derivation`, `proofLenGraphDef`, `Δ₁ch` -/

noncomputable def derivationPiSigmaB : ArithmeticSemisentence 1 :=
  “d. !(derivation TAct).pi d → !(derivation TAct).sigma d”
noncomputable def derivationPiSigma : ArithmeticSentence := ∀¹* derivationPiSigmaB
lemma models_derivationPiSigma :
    V↓[ℒₒᵣ] ⊧ derivationPiSigma ↔ ∀ d : V, Derivation TAct d → Derivation TAct d := by
  simp [derivationPiSigma, derivationPiSigmaB, models_iff]
theorem pa_proves_derivationPiSigma : 𝗣𝗔 ⊢ derivationPiSigma :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_derivationPiSigma.mpr fun _ h ↦ h
theorem lib_derivationPiSigma : Lib derivationPiSigma := Lib.of_pa pa_proves_derivationPiSigma

/-! ### The axiom recognizer (i): every axiom of `TAct` by its code -/

/-- `p = ⌜σ⌝ → TAct.Δ₁ch p` — the recognizer accepts the (unary-numeral) code of `σ`. ONE
parametric row: every `σ ∈ TAct` (the four action sentences, every `𝗣𝗔⁻` axiom, and in
fact every induction instance too) is an instance; the code is never evaluated. -/
noncomputable def axiomRecB (σ : Sentence LAct) : ArithmeticSemisentence 1 :=
  “p. p = ↑(Encodable.encode σ) → !(Theory.Δ₁ch TAct).sigma p”
noncomputable def axiomRec (σ : Sentence LAct) : ArithmeticSentence := ∀¹* (axiomRecB σ)

lemma models_axiomRec (σ : Sentence LAct) :
    V↓[ℒₒᵣ] ⊧ axiomRec σ ↔ ∀ p : V, p = (Encodable.encode σ : V) → p ∈ TAct.Δ₁Class := by
  simp [axiomRec, axiomRecB, models_iff, Matrix.vecForall_iff, numeral_eq_natCast]

theorem pa_proves_axiomRec {σ : Sentence LAct} (h : σ ∈ TAct) : 𝗣𝗔 ⊢ axiomRec σ :=
  Lib.pa_proves_of_models fun _ _ _ ↦ (models_axiomRec σ).mpr fun _ hp ↦ by
    subst hp; rw [← Sentence.quote_eq_encode]; exact Δ₁Class.mem_iff.mpr h

theorem lib_axiomRec {σ : Sentence LAct} (h : σ ∈ TAct) : Lib (axiomRec σ) :=
  Lib.of_pa (pa_proves_axiomRec h)

/-- The four action axioms. -/
theorem lib_axiomRec_actionAxiom : Lib (axiomRec actionAxiom) := lib_axiomRec actionAxiom_mem_TAct

/-- Every `𝗣𝗔`-axiom (the finitely many `𝗣𝗔⁻` ones and every induction instance), embedded. -/
theorem lib_axiomRec_pa {σ : Sentence ℒₒᵣ} (h : σ ∈ 𝗣𝗔) : Lib (axiomRec (Semiformula.lMap emb σ)) :=
  lib_axiomRec (lMap_emb_mem_TAct h)

/-! ### The axiom recognizer (ii): the induction scheme

`TAct.Δ₁ch` is, by construction (`Theory.Δ₁.insert` four times over `embPA_delta1`, whose
`ch` is `isFormulaOR ⋏ 𝗣𝗔.Δ₁ch`, with `𝗣𝗔.Δ₁ch = 𝗣𝗔⁻.ch ⋎ chUniv`), the disjunction pinned
by `tact_ch_eq`/`pa_ch_eq` — `rfl`, never `simp` (unfolding the chain by `simp` loops). The
induction recognizer `chUniv = chInd ⊤` (`Incompleteness/Definability.lean`) accepts `p` iff
`InductionR (fun _ ↦ True) p`: `p = qqAlls b m` (the universal closure over the `m`
parameters), `IsUFormula b`, `shift b = b` (no free variables), `bv b = m`, and
`subst (fvarVec m) b = indBodyVal K` for a `1`-semiformula `K` — `indBodyVal K` the
`succInd` body `K(0) → (∀ (K → K(#0+1))) → ∀ K` through the graphs `substsGraph`, `impGraph`,
`qqAllDef` (`indBodyValGraph`). The row `indRec` is that clause read as a universal
sentence over the SAME ℒₒᵣ-indexed graph objects the recognizer uses (`qqAllsDef`,
`(isUFormula ℒₒᵣ).pi`, `(shiftGraph ℒₒᵣ)`, `(bvGraph ℒₒᵣ)`, `fvarVecDef`,
`(substsGraph ℒₒᵣ)`, `(isSemiformula ℒₒᵣ).pi 1`, `indBodyValGraph`) — the shape the
recognizer forces. NOTE: these are `ℒₒᵣ`-graphs, not `LAct`-graphs; a fragment holding
`LAct`-shape facts about an `ℒₒᵣ`-code needs the (not yet written) language-restriction
bridge rows. -/

section indRec

lemma tact_ch_eq : Theory.Δ₁ch TAct =
    (((((isFormulaOR ⋏ Theory.Δ₁ch 𝗣𝗔) ⋎ (Theory.Δ₁.singleton constNe').ch) ⋎ (Theory.Δ₁.singleton constNe).ch)
      ⋎ (Theory.Δ₁.singleton actionAxiom').ch) ⋎ (Theory.Δ₁.singleton actionAxiom).ch) := rfl

lemma pa_ch_eq : Theory.Δ₁ch (𝗣𝗔 : ArithmeticTheory) = PeanoMinus.delta1.ch ⋎ chUniv := rfl

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma mem_TAct_class_iff (p : V) : p ∈ TAct.Δ₁Class ↔ V ⊧/![p] (Theory.Δ₁ch TAct).val := Iff.rfl

/-- `eval_isFormulaOR` (`TheoryAct`) for a universe-polymorphic `V`. -/
lemma eval_isFormulaOR' (p : V) : V ⊧/![p] isFormulaOR.val ↔ IsSemiformula ℒₒᵣ 0 p := by
  simp [isFormulaOR, HierarchySymbol.Semiformula.val_sigma,
    HierarchySymbol.Semiformula.val_mkDelta]

/-- An `ℒₒᵣ`-formula code accepted by the induction recognizer is a `TAct`-axiom code. -/
lemma mem_TAct_Δ₁Class_of_inductionR {p : V} (hF : IsSemiformula ℒₒᵣ 0 p)
    (h : InductionR (fun _ ↦ True) p) : p ∈ TAct.Δ₁Class := by
  rw [mem_TAct_class_iff, tact_ch_eq, pa_ch_eq]
  simp only [HierarchySymbol.Semiformula.val_or, HierarchySymbol.Semiformula.val_and,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.or_eq, LogicalConnective.Prop.and_eq, HierarchySymbol.Defined.iff,
    Matrix.cons_val_fin_one]
  exact Or.inl (Or.inl (Or.inl (Or.inl ⟨(eval_isFormulaOR' p).mpr hF, Or.inr h⟩)))

/-- `Ind_rec`: the induction-scheme recognizer as ONE universal sentence — every code of the
shape `∀^m (indBodyVal K)[parameters]` is a `TAct`-axiom code. -/
noncomputable def indRecB : ArithmeticSemisentence 6 :=
  “K s fv b m p. !qqAllsDef p b m → !(isUFormula ℒₒᵣ).pi b → !(shiftGraph ℒₒᵣ) b b →
    !(bvGraph ℒₒᵣ) m b → !fvarVecDef fv m → !(substsGraph ℒₒᵣ) s fv b →
    !(isSemiformula ℒₒᵣ).pi 1 K → !indBodyValGraph s K → !(Theory.Δ₁ch TAct).sigma p”
noncomputable def indRec : ArithmeticSentence := ∀¹* indRecB

lemma models_indRec :
    V↓[ℒₒᵣ] ⊧ indRec ↔ ∀ K s fv b m p : V,
      p = qqAlls b m → IsUFormula ℒₒᵣ b → b = shift ℒₒᵣ b → m = bv ℒₒᵣ b →
      fv = fvarVec m → s = subst ℒₒᵣ fv b → IsSemiformula ℒₒᵣ 1 K → s = indBodyVal K →
      p ∈ TAct.Δ₁Class := by
  simp [indRec, indRecB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_indRec : 𝗣𝗔 ⊢ indRec :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_indRec.mpr
    fun K s fv b m p hp hb hsh hm hfv hs hK hind ↦ by
      subst hp hfv hs
      have hbm : IsSemiformula ℒₒᵣ (0 + m) b := isSemiformula_iff.mpr ⟨hb, by rw [hm, zero_add]⟩
      refine mem_TAct_Δ₁Class_of_inductionR hbm.qqAlls
        ⟨m, index_le_qqAlls _ _, b, le_qqAlls _ _, rfl, hb, hsh.symm, hm.symm, K, ?_, hK, trivial, hind⟩
      rw [hind]; exact le_indBodyVal K

theorem lib_indRec : Lib indRec := Lib.of_pa pa_proves_indRec

end indRec

end ArithS
