import ArithS.Necessitation.PrologueRows

/-!
# ArithS.Necessitation.Prologue — the PROLOGUE producers (`DESIGN_fragments.md` §3–§4)

The per-tag node fragments of `Frag1`/`Frag2` take the layout of their node as HYPOTHESES
(`neg … ∈ Γ`). This file produces those layouts: from the parent's canonical layout it emits the
Σ₁ step lists that establish the CHILD's layout, so that `pro ++ (child's list) ++ node<Tag>`
composes into the verification list of `Verify.lean`.

## The table (§0)

Two row lineages collided: the certification table `certRows` keeps its rows at `100 + k`, and the
fragment tables `frag1Rows`/`frag2Rows`/`topRows` keep theirs at `87 … 154`. One step list runs at ONE
table, so the prologue table `proRows := topRows ++ proExtraRows ++ certTailRows` (the prologue's own
rows of `PrologueRows.lean` at `155 + k`, then the certification tail) carries the certification tail at
`i + certShiftN` (`certShiftN = topRowCount + proExtraRowCount − walkRowCount`), and every certification list
(`certNeg`, `certShift`, `lenSteps`, all stated at a `CertTable`) is RE-INDEXED by `reidxL`
(`sRow ↦ cshiftV sRow` on the three Horn tags, everything else untouched). The re-indexing changes
nothing but the row index: `ctxAfter`, `stepCost`, `shiftsV`, `finalCtx`, `NoDrop'`, `HornOnly`,
`SizeOK` and `costSum` are invariant (§0.3), and `ListOK` transfers from `certView tbl` — the
certification table READ OFF a prologue table, of length exactly `certRowCount` — to `tbl` (§0.4).
The alternative (regenerating `CertRows` at `155 + k`) touches a file under concurrent edit; this
wrapper is self-contained and becomes deletable the day the tables are unified.

## Contents

* §0 the table, the certification view, the re-indexing and its invariance.
* §1 `Layout` — the canonical layout of a sequent (one predicate, one transport lemma).
* §2 `layoutSteps` — the layout builder (member walks + lengths, the chain, the length fold).
* §3 the leaves `axL`/`verumIntro`.
* §4 (pending) the identification of an `insert` object with a chain; `and`/`or`/`cut`; `wk`; `shift`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

/-! ## 0. The prologue table and the re-indexing of certification lists -/

section proTable

/-- The prologue rows: the top rows at their indices, the prologue's own rows at `topRowCount + k`, then
the certification tail (`certRows` without its 40 walk rows) at `topRowCount + proExtraRowCount + k`. -/
noncomputable def proRows : List WRow := topRows ++ proExtraRows ++ certTailRows

/-- Where the certification tail starts. -/
def proBase : ℕ := topRowCount + proExtraRowCount

/-- How far a certification row (index `≥ walkRowCount` in `certRows`) moves. -/
def certShiftN : ℕ := proBase - walkRowCount

def proRowCount : ℕ := proBase + (certRowCount - walkRowCount)

lemma proRows_length : proRows.length = proRowCount := rfl

/-- The prologue table: `proRowCount` rows at least, the `i`-th with the arity and matrix of `proRows[i]`. -/
def ProTable (tbl : V) : Prop :=
  (proRowCount : V) ≤ len tbl ∧
  ∀ (i : ℕ) (h : i < proRows.length),
    rowM tbl.[(i : V)] = ((proRows[i]).m : V) ∧ rowB tbl.[(i : V)] = ⌜Semiformula.lMap emb (proRows[i]).B⌝

lemma ProTable.topTable {tbl : V} (h : ProTable tbl) : TopTable tbl := by
  refine ⟨le_trans (by exact_mod_cast (show topRowCount ≤ proRowCount by simp only [proRowCount, proBase]; omega)) h.1, ?_⟩
  intro i hi
  have hi' : i < proRows.length := by
    rw [proRows_length]; rw [topRows_length] at hi; simp only [proRowCount, proBase]; omega
  have := h.2 i hi'
  have hi'' : i < (topRows ++ proExtraRows).length := by
    rw [List.length_append]; exact lt_of_lt_of_le hi (Nat.le_add_right _ _)
  rwa [show proRows[i] = topRows[i] from
    (List.getElem_append_left hi'').trans (List.getElem_append_left hi)] at this

lemma ProTable.frag2Table {tbl : V} (h : ProTable tbl) : Frag2Table tbl := h.topTable.frag2Table
lemma ProTable.frag1Table {tbl : V} (h : ProTable tbl) : Frag1Table tbl := h.topTable.frag1Table
lemma ProTable.layoutTable {tbl : V} (h : ProTable tbl) : LayoutTable tbl := h.topTable.layoutTable
lemma ProTable.walkTable {tbl : V} (h : ProTable tbl) : WalkTable tbl := h.topTable.walkTable

/-- The reading of the prologue's own row `setLenSingLe` (what `pok_setLenSingLe` takes). -/
lemma ProTable.setLenSingLe {tbl : V} (h : ProTable tbl) :
    ((pIdx_setLenSingLe : ℕ) : V) < len tbl ∧
    rowM tbl.[((pIdx_setLenSingLe : ℕ) : V)] = ((4 : ℕ) : V) ∧
    rowB tbl.[((pIdx_setLenSingLe : ℕ) : V)] = impChainV LAct (vecOf row_setLenSingLe_as) row_setLenSingLe_c := by
  have hlt : pIdx_setLenSingLe < proRows.length := by
    rw [proRows_length]; simp only [proRowCount, proBase, pIdx_setLenSingLe, topRowCount, proExtraRowCount]; omega
  have hr := h.2 pIdx_setLenSingLe hlt
  have e' : proRows[pIdx_setLenSingLe]? = proExtraRows[0]? := by
    have h1 : pIdx_setLenSingLe < (topRows ++ proExtraRows).length := by
      rw [List.length_append]; simp only [pIdx_setLenSingLe, topRows_length, proExtraRows_length, topRowCount, proExtraRowCount]; omega
    have h2 : topRows.length ≤ pIdx_setLenSingLe := by rw [topRows_length]; simp only [pIdx_setLenSingLe, topRowCount]; omega
    unfold proRows
    rw [List.getElem?_append_left h1, List.getElem?_append_right h2]
    rfl
  have e : proRows[pIdx_setLenSingLe] = proExtraRows[0] := by
    rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem (by decide : 0 < proExtraRows.length)] at e'
    exact Option.some.inj e'
  rw [e] at hr
  refine ⟨lt_of_lt_of_le (by exact_mod_cast hlt) (proRows_length ▸ h.1), hr.1, ?_⟩
  rw [impChainV_vecOf, hr.2]
  exact quote_row_setLenSingLe

theorem exists_proTable : ∃ N : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∃ tbl : V, TableOK tbl (N : V) ∧ ProTable tbl := by
  obtain ⟨N, hN⟩ := exists_rows proRows
  refine ⟨N, fun V _ _ ↦ ?_⟩
  obtain ⟨rows, hlen, hok, hidx⟩ := hN V
  refine ⟨vecOf rows, tableOK_vecOf rows hok, ?_, ?_⟩
  · rw [len_vecOf, hlen, proRows_length]
  · intro i h
    have h' : i < rows.length := by rw [hlen]; exact h
    rw [nth_vecOf rows i h']
    exact hidx i h h'

/-! ### 0.1 The index map and the certification view -/

/-- Walk rows stay; the certification tail moves up by `certShiftN`. -/
def cshiftN (i : ℕ) : ℕ := if i < walkRowCount then i else i + certShiftN

noncomputable def cshiftV (r : V) : V := if r < (walkRowCount : V) then r else r + (certShiftN : V)

lemma cshiftV_natCast (i : ℕ) : cshiftV (i : V) = (cshiftN i : V) := by
  unfold cshiftV cshiftN
  by_cases h : i < walkRowCount
  · rw [if_pos (by exact_mod_cast h), if_pos h]
  · rw [if_neg (by exact_mod_cast h), if_neg h]; push_cast; rfl

lemma cshiftN_lt {i : ℕ} (hi : i < certRowCount) : cshiftN i < proRowCount := by
  unfold cshiftN
  split_ifs with h
  · simp only [proRowCount, certShiftN, proBase, certRowCount, topRowCount, proExtraRowCount, walkRowCount] at hi h ⊢
    omega
  · simp only [proRowCount, certShiftN, proBase, certRowCount, topRowCount, proExtraRowCount, walkRowCount] at hi h ⊢
    omega

/-- `proRows` at the moved index is the certification row (the proof-free `getElem?` form). -/
lemma proRows_cshiftN' (i : ℕ) (hi : i < certRowCount) : proRows[cshiftN i]? = certRows[i]? := by
  unfold cshiftN
  split_ifs with hw
  · have h1 : i < walkRows.length := by rw [walkRows_length]; exact hw
    have h2 : i < layoutRows.length := by
      rw [layoutRows_length]; exact lt_of_lt_of_le hw (by decide)
    have h3 : i < frag1Rows.length := by
      rw [frag1Rows_length]; exact lt_of_lt_of_le hw (by decide)
    have h4 : i < frag2Rows.length := by
      rw [frag2Rows_length]; exact lt_of_lt_of_le hw (by decide)
    have h5 : i < topRows.length := by
      rw [topRows_length]; exact lt_of_lt_of_le hw (by decide)
    have h6 : i < (topRows ++ proExtraRows).length := by
      rw [List.length_append]; exact lt_of_lt_of_le h5 (Nat.le_add_right _ _)
    unfold proRows certRows
    rw [List.getElem?_append_left h6, List.getElem?_append_left h5, List.getElem?_append_left h1]
    unfold topRows
    rw [List.getElem?_append_left h4]
    unfold frag2Rows
    rw [List.getElem?_append_left h3]
    unfold frag1Rows
    rw [List.getElem?_append_left h2]
    unfold layoutRows
    rw [List.getElem?_append_left h1]
  · have hw' : walkRowCount ≤ i := not_lt.mp hw
    have h1 : (topRows ++ proExtraRows).length ≤ i + certShiftN := by
      rw [List.length_append, topRows_length, proExtraRows_length]
      simp only [certShiftN, proBase, topRowCount, proExtraRowCount, walkRowCount] at hw' ⊢; omega
    have h2 : walkRows.length ≤ i := by rw [walkRows_length]; exact hw'
    unfold proRows certRows
    rw [List.getElem?_append_right h1, List.getElem?_append_right h2]
    congr 1

lemma proRows_cshiftN (i : ℕ) (hi : i < certRowCount) (h₁ : cshiftN i < proRows.length)
    (h₂ : i < certRows.length) : proRows[cshiftN i] = certRows[i] := by
  have := proRows_cshiftN' i hi
  rw [List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂] at this
  exact Option.some.inj this

/-- The certification table read off a prologue table: exactly `certRowCount` rows, the `i`-th being
`tbl.[cshiftN i]`. -/
noncomputable def certView (tbl : V) : V :=
  vecOf ((List.range certRowCount).map fun i ↦ tbl.[(cshiftN i : V)])

lemma len_certView (tbl : V) : len (certView tbl) = (certRowCount : V) := by
  simp [certView]

lemma nth_certView (tbl : V) (i : ℕ) (hi : i < certRowCount) :
    (certView tbl).[(i : V)] = tbl.[(cshiftN i : V)] := by
  unfold certView
  rw [nth_vecOf _ i (by simpa using hi)]
  simp [hi]

lemma ProTable.certTable {tbl : V} (h : ProTable tbl) : CertTable (certView tbl) := by
  refine ⟨by rw [len_certView], ?_⟩
  intro i hi
  have hi' : i < certRowCount := certRows_length ▸ hi
  rw [nth_certView tbl i hi']
  have := h.2 (cshiftN i) (proRows_length ▸ cshiftN_lt hi')
  rwa [proRows_cshiftN i hi' (proRows_length ▸ cshiftN_lt hi') hi] at this

/-- For a V-index below the view's length, the moved index is in range and reads the same row. -/
lemma certView_row {tbl : V} (h : ProTable tbl) {r : V} (hr : r < len (certView tbl)) :
    cshiftV r < len tbl ∧ tbl.[cshiftV r] = (certView tbl).[r] := by
  rw [len_certView] at hr
  obtain ⟨m, rfl⟩ := eq_nat_of_lt_nat hr
  have hm : m < certRowCount := by exact_mod_cast hr
  rw [cshiftV_natCast, nth_certView tbl m hm]
  exact ⟨lt_of_lt_of_le (by exact_mod_cast cshiftN_lt hm) h.1, rfl⟩

lemma ProTable.tableOK_certView {tbl N : V} (htbl : TableOK tbl N) (h : ProTable tbl) :
    TableOK (certView tbl) N := by
  intro r hr
  obtain ⟨hlt, heq⟩ := certView_row h hr
  rw [← heq]
  exact htbl _ hlt

/-! ### 0.2 Re-indexing a step: the three Horn tags move their row index, everything else is untouched -/

noncomputable def reidxS (s : V) : V :=
  if sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2 then ⟪sTag s, cshiftV (sRow s), π₂ (π₂ s)⟫ else s

lemma reidxS_of_horn {s : V} (h : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2) :
    reidxS s = ⟪sTag s, cshiftV (sRow s), π₂ (π₂ s)⟫ := by unfold reidxS; rw [if_pos h]

lemma reidxS_of_not_horn {s : V} (h : ¬ (sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2)) : reidxS s = s := by
  unfold reidxS; rw [if_neg h]

@[simp] lemma sTag_reidxS (s : V) : sTag (reidxS s) = sTag s := by
  unfold reidxS; split_ifs <;> simp [sTag]

lemma sRow_reidxS_of_horn {s : V} (h : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2) :
    sRow (reidxS s) = cshiftV (sRow s) := by
  rw [reidxS_of_horn h]; simp [sRow]

@[simp] lemma sEv_reidxS (s : V) : sEv (reidxS s) = sEv s := by
  unfold reidxS; split_ifs <;> simp [sEv]

@[simp] lemma sAs_reidxS (s : V) : sAs (reidxS s) = sAs s := by
  unfold reidxS; split_ifs <;> simp [sAs]

@[simp] lemma sC_reidxS (s : V) : sC (reidxS s) = sC s := by
  unfold reidxS; split_ifs <;> simp [sC]

lemma ctxAfter_reidxS (Γ s : V) : ctxAfter Γ (reidxS s) = ctxAfter Γ s := by
  by_cases h : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2
  · rcases h with h | h | h
    · simp only [ctxAfter, sTag_reidxS, sEv_reidxS, sC_reidxS, h]; simp
    · simp only [ctxAfter, sTag_reidxS, sEv_reidxS, sC_reidxS, h]; simp
    · simp only [ctxAfter, sTag_reidxS, sEv_reidxS, sC_reidxS, h]; simp
  · rw [reidxS_of_not_horn h]

lemma stepCost_reidxS (N E Γ s : V) : stepCost N E Γ (reidxS s) = stepCost N E Γ s := by
  by_cases h : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2
  · rcases h with h | h | h
    · simp only [stepCost, sTag_reidxS, sEv_reidxS, sAs_reidxS, sC_reidxS, h]; simp
    · simp only [stepCost, sTag_reidxS, sEv_reidxS, sAs_reidxS, sC_reidxS, h]; simp
    · simp only [stepCost, sTag_reidxS, sEv_reidxS, sAs_reidxS, sC_reidxS, h]; simp
  · rw [reidxS_of_not_horn h]

lemma stepSizeOK_reidxS {Q D s : V} (h : StepSizeOK Q D s) : StepSizeOK Q D (reidxS s) := by
  by_cases hh : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2
  · rcases hh with hh | hh | hh
    · exact Or.inl (by rw [sTag_reidxS, hh])
    · exact Or.inr (Or.inl (by rw [sTag_reidxS, hh]))
    · exact Or.inr (Or.inr (Or.inl (by rw [sTag_reidxS, hh])))
  · rw [reidxS_of_not_horn hh]; exact h

/-- **A step applicable at the certification view is applicable at the prologue table once re-indexed.** -/
lemma stepOK_reidxS {tbl E M Γ s : V} (hP : ProTable tbl) (hok : StepOK (certView tbl) E M Γ s) :
    StepOK tbl E M Γ (reidxS s) := by
  obtain ⟨hΓ, hcase⟩ := hok
  refine ⟨hΓ, ?_⟩
  have horn : ∀ (ht : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2), HornOK (certView tbl) E M Γ s →
      HornOK tbl E M Γ (reidxS s) ∧ tbl.[sRow (reidxS s)] = (certView tbl).[sRow s] := by
    intro ht hH
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hH
    obtain ⟨hlt, heq⟩ := certView_row hP h1
    refine ⟨?_, ?_⟩
    · unfold HornOK
      rw [sRow_reidxS_of_horn ht, sEv_reidxS, sAs_reidxS, heq]
      exact ⟨hlt, h2, h3, h4, h5, h6⟩
    · rw [sRow_reidxS_of_horn ht]; exact heq
  rcases hcase with ⟨ht, hH, hB⟩ | ⟨ht, hH, hB⟩ | ⟨ht, hH, hB⟩ | h3 | h4 | h5 | h6 | h7
  · obtain ⟨hH', heq⟩ := horn (Or.inl ht) hH
    exact Or.inl ⟨by rw [sTag_reidxS]; exact ht, hH', by rw [heq, sAs_reidxS, sC_reidxS]; exact hB⟩
  · obtain ⟨hH', heq⟩ := horn (Or.inr (Or.inl ht)) hH
    exact Or.inr (Or.inl ⟨by rw [sTag_reidxS]; exact ht, hH', by rw [heq, sAs_reidxS, sC_reidxS]; exact hB⟩)
  · obtain ⟨hH', heq⟩ := horn (Or.inr (Or.inr ht)) hH
    exact Or.inr (Or.inr (Or.inl ⟨by rw [sTag_reidxS]; exact ht, hH', by rw [heq, sAs_reidxS, sC_reidxS]; exact hB⟩))
  · have hn : ¬ (sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2) := by
      rw [h3.1]; norm_num
    rw [reidxS_of_not_horn hn]; exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  · have hn : ¬ (sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2) := by
      rw [h4.1]; norm_num
    rw [reidxS_of_not_horn hn]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
  · have hn : ¬ (sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2) := by
      rw [h5.1]; norm_num
    rw [reidxS_of_not_horn hn]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
  · have hn : ¬ (sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2) := by
      rw [h6.1]; norm_num
    rw [reidxS_of_not_horn hn]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))
  · have hn : ¬ (sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2) := by
      rw [h7.1]; norm_num
    rw [reidxS_of_not_horn hn]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h7))))))

/-! ### Σ₁-definability of the re-indexing -/

noncomputable def cshiftVDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y r. (r < ↑walkRowCount → y = r) ∧ (¬ r < ↑walkRowCount → y = r + ↑certShiftN)”

instance cshiftV_defined : 𝚺₁-Function₁ (cshiftV : V → V) via cshiftVDef := .mk fun v ↦ by
  simp [cshiftVDef, cshiftV, numeral_eq_natCast]
  by_cases h : v 1 < (walkRowCount : V)
  · simp [h]
  · simp [h]
    try exact Or.inl (not_lt.mp h)
instance cshiftV_definable : 𝚺₁-Function₁ (cshiftV : V → V) := cshiftV_defined.to_definable

noncomputable def reidxSDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y s. ∃ t, !pi₁Def t s ∧ ∃ p, !pi₂Def p s ∧ ∃ r, !pi₁Def r p ∧ ∃ q, !pi₂Def q p ∧
    ((t = 0 ∨ t = 1 ∨ t = 2) → ∃ r', !cshiftVDef r' r ∧ ∃ w, !pairDef w r' q ∧ !pairDef y t w) ∧
    (t ≠ 0 → t ≠ 1 → t ≠ 2 → y = s)”

instance reidxS_defined : 𝚺₁-Function₁ (reidxS : V → V) via reidxSDef := .mk fun v ↦ by
  simp [reidxSDef, cshiftV_defined.iff, numeral_eq_natCast]
  unfold reidxS sTag sRow
  by_cases h0 : π₁ (v 1) = 0
  · simp [h0]
  by_cases h1 : π₁ (v 1) = 1
  · simp [h1]
  by_cases h2 : π₁ (v 1) = 2
  · simp [h2]
  · simp [h0, h1, h2]
instance reidxS_definable : 𝚺₁-Function₁ (reidxS : V → V) := reidxS_defined.to_definable

namespace ReidxL

noncomputable def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y = 0”
  adjoin := .mkSigma “y x xs ih. ∃ r, !reidxSDef r x ∧ !adjoinDef y r ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin _ x _ ih := reidxS x ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint, reidxS_defined.iff]

end ReidxL

/-- `reidxL L` — every step of `L` re-indexed. -/
noncomputable def reidxL (L : V) : V := ReidxL.construction.result ![] L

@[simp] lemma reidxL_nil : reidxL (0 : V) = 0 := by simp [reidxL, ReidxL.construction]
@[simp] lemma reidxL_adjoin (s L : V) : reidxL (s ∷ L) = reidxS s ∷ reidxL L := by
  simp [reidxL, ReidxL.construction]

noncomputable def reidxLDef : 𝚺₁.Semisentence 2 := ReidxL.blueprint.resultDef

instance reidxL_defined : 𝚺₁-Function₁ (reidxL : V → V) via reidxLDef := .mk
  fun v ↦ by simp [ReidxL.construction.eval_resultDef, reidxLDef]; rfl
instance reidxL_definable : 𝚺₁-Function₁ (reidxL : V → V) := reidxL_defined.to_definable

/-! ### 0.3 The re-indexed list: length, entries, `appendV`, contexts, shifts, costs -/

lemma reidxL_appendV : ∀ A B : V, reidxL (appendV A B) = appendV (reidxL A) (reidxL B) := by
  intro A B
  induction A using adjoin_ISigma1.sigma1_succ_induction with
  | hP => definability
  | nil => simp
  | adjoin x A ih => rw [appendV_adjoin, reidxL_adjoin, reidxL_adjoin, appendV_adjoin, ih]

lemma len_reidxL : ∀ L : V, len (reidxL L) = len L := by
  intro L
  induction L using adjoin_ISigma1.sigma1_succ_induction with
  | hP => definability
  | nil => simp
  | adjoin x L ih => rw [reidxL_adjoin, len_adjoin, len_adjoin, ih]

lemma nth_reidxL : ∀ L : V, ∀ m < len L, (reidxL L).[m] = reidxS L.[m] := by
  intro L
  induction L using adjoin_ISigma1.pi1_succ_induction with
  | hP => definability
  | nil => intro m hm; simp at hm
  | adjoin x L ih =>
    intro m hm
    rw [reidxL_adjoin]
    rcases zero_or_succ m with rfl | ⟨m, rfl⟩
    · simp
    · rw [nth_adjoin_succ, nth_adjoin_succ]
      exact ih m (by rw [len_adjoin] at hm; exact lt_of_add_lt_add_right hm)

lemma nthFromEnd_reidxL {L j : V} (hj : j < len L) : nthFromEnd (reidxL L) j = reidxS (nthFromEnd L j) := by
  obtain ⟨a, ha⟩ : ∃ a, len L = a + (j + 1) := ⟨len L - (j + 1), by
    rw [add_comm]; exact (add_tsub_cancel_of_le (lt_iff_succ_le.mp hj)).symm⟩
  rw [nthFromEnd_eq (v := reidxL L) (by rw [len_reidxL]; exact ha), nthFromEnd_eq ha]
  exact nth_reidxL L a (by rw [ha]; exact lt_add_of_pos_right _ (lt_of_lt_of_le _root_.zero_lt_one le_add_self))

lemma ctxVecAux_reidxL (Γ L : V) : ∀ n ≤ len L, ctxVecAux Γ (reidxL L) n = ctxVecAux Γ L n := by
  intro n
  induction n using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hn' : n < len L := lt_of_lt_of_le (lt_add_one n) hn
    rw [ctxVecAux_succ, ctxVecAux_succ, ih (le_of_lt hn'), nth_reidxL L n hn', ctxAfter_reidxS]

lemma ctxVec_reidxL (Γ L : V) : ctxVec Γ (reidxL L) = ctxVec Γ L := by
  unfold ctxVec; rw [len_reidxL]; exact ctxVecAux_reidxL Γ L (len L) le_rfl

lemma finalCtx_reidxL (Γ L : V) : finalCtx Γ (reidxL L) = finalCtx Γ L := by
  unfold finalCtx; rw [ctxVec_reidxL, len_reidxL]

lemma shiftsAux_reidxL (L : V) : ∀ n ≤ len L, shiftsAux (reidxL L) n = shiftsAux L n := by
  intro n
  induction n using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hn' : n < len L := lt_of_lt_of_le (lt_add_one n) hn
    rw [shiftsAux_succ, shiftsAux_succ, ih (le_of_lt hn'), nth_reidxL L n hn', sTag_reidxS]

lemma shiftsV_reidxL (L : V) : shiftsV (reidxL L) = shiftsV L := by
  unfold shiftsV; rw [len_reidxL]; exact shiftsAux_reidxL L (len L) le_rfl

lemma costAux_reidxL (N E C L : V) : ∀ j ≤ len L, costAux N E C (reidxL L) j = costAux N E C L j := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hj' : j < len L := lt_of_lt_of_le (lt_add_one j) hj
    rw [costAux_succ, costAux_succ, ih (le_of_lt hj'), nthFromEnd_reidxL hj', stepCost_reidxS]

lemma costSum_reidxL (N E Γ L : V) : costSum N E Γ (reidxL L) = costSum N E Γ L := by
  unfold costSum; rw [ctxVec_reidxL, len_reidxL]; exact costAux_reidxL N E _ L (len L) le_rfl

lemma noDrop'_reidxL {L : V} (h : NoDrop' L) : NoDrop' (reidxL L) := by
  intro i hi
  rw [len_reidxL] at hi
  rw [nth_reidxL L i hi, sTag_reidxS]; exact h i hi

lemma noDrop_reidxL {L : V} (h : NoDrop L) : NoDrop (reidxL L) := by
  intro i hi
  rw [len_reidxL] at hi
  rw [nth_reidxL L i hi, sTag_reidxS]; exact h i hi

lemma hornOnly_reidxL {L : V} (h : HornOnly L) : HornOnly (reidxL L) := by
  intro i hi
  rw [len_reidxL] at hi
  rw [nth_reidxL L i hi, sTag_reidxS]; exact h i hi

lemma sizeOK_reidxL {Q D L : V} (h : SizeOK Q D L) : SizeOK Q D (reidxL L) := by
  intro i hi
  rw [len_reidxL] at hi
  rw [nth_reidxL L i hi]; exact stepSizeOK_reidxS (h i hi)

/-- **`ListOK` transfers from the certification view to the prologue table under re-indexing.** -/
theorem listOK_reidxL {tbl E M Γ L : V} (hP : ProTable tbl) (hok : ListOK (certView tbl) E M Γ L) :
    ListOK tbl E M Γ (reidxL L) := by
  intro i hi
  rw [len_reidxL] at hi
  rw [ctxVec_reidxL, nth_reidxL L i hi]
  exact stepOK_reidxS hP (hok i hi)

end proTable

/-! ## 1. The canonical layout of a sequent (`DESIGN_fragments.md` §3.2, in this file's frame)

Members `xs = memberList s` (ascending, `k = len xs`). The layout at CHAIN OFFSET `i`:

* the fresh length object `l_s = &i` with `setLenFact &i &(i + k + 1)` and the NUMERIC bound
  `leFact &i (bnum (setLen s))`;
* the chain `s_j = &(i + k + 1 + j)` (`s = s_0`), with `insFact &(i+k+1+j) X_j (prev)` (`prev` = `s_{j+1}`,
  or the literal `𝟎` for the innermost member), `fsetPiFact &(i+k+1+j)` and `memFact X_j &(i+k+1)`;
* the member objects `X_j = &(mTop i k o_j)` with `o_j = (offVec xs).[j]` (the offsets left by the member
  blocks: `o_j = mLen x_j + Σ_{j' > j} mShift x_{j'}`), each with its WALK dossier (`DossF`),
  `piFact 𝟎 X_j` and its numeric length `lenFact (bnum |x_j|) X_j`.

The offsets are Σ₁ functions of `s` and the piece tables alone, so a child fragment recomputes them. -/

section layoutDef

/-- The shifts of the length pass of a member (`lenSteps` at offset `0`). -/
noncomputable def mLen (Wc T x : V) : V := shiftsV (lenSteps Wc T 0 x 0)

noncomputable def mLenDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y Wc T x. ∃ l, !lenStepsDef l Wc T 0 x 0 ∧ !shiftsVDef y l”

instance mLen_defined : 𝚺₁-Function₃ (mLen : V → V → V → V) via mLenDef := .mk fun v ↦ by
  simp [mLenDef, mLen, lenSteps_defined.iff, shiftsV_defined.iff, numeral_eq_natCast]
instance mLen_definable : 𝚺₁-Function₃ (mLen : V → V → V → V) := mLen_defined.to_definable

/-- The shifts of a member's block: its walk and its length pass. -/
noncomputable def mShift (Ww Wc T x : V) : V := descCountF Ww 0 x + mLen Wc T x

noncomputable def mShiftDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y Ww Wc T x. ∃ c, !descCountFDef c Ww 0 x ∧ ∃ l, !mLenDef l Wc T x ∧ y = c + l”

instance mShift_defined : 𝚺₁-Function₄ (mShift : V → V → V → V → V) via mShiftDef := .mk fun v ↦ by
  simp [mShiftDef, mShift, descCountF_defined.iff, mLen_defined.iff, numeral_eq_natCast]
instance mShift_definable : 𝚺₁-Function₄ (mShift : V → V → V → V → V) := mShift_defined.to_definable

namespace TailShift

noncomputable def blueprint : VecRec.Blueprint 3 where
  nil := .mkSigma “y Ww Wc T. y = 0”
  adjoin := .mkSigma “y x xs ih Ww Wc T. ∃ m, !mShiftDef m Ww Wc T x ∧ y = m + ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin v x _ ih := mShift (v 0) (v 1) (v 2) x + ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint, mShift_defined.iff]

end TailShift

/-- `tailShift v Ww Wc T` — the total block shift of the members in `v` (vector first: the `VecRec` order). -/
noncomputable def tailShift (v Ww Wc T : V) : V := TailShift.construction.result ![Ww, Wc, T] v

@[simp] lemma tailShift_nil (Ww Wc T : V) : tailShift 0 Ww Wc T = 0 := by simp [tailShift, TailShift.construction]
@[simp] lemma tailShift_adjoin (x v Ww Wc T : V) :
    tailShift (x ∷ v) Ww Wc T = mShift Ww Wc T x + tailShift v Ww Wc T := by
  simp [tailShift, TailShift.construction]

noncomputable def tailShiftDef : 𝚺₁.Semisentence 5 := TailShift.blueprint.resultDef

instance tailShift_defined : 𝚺₁-Function₄ (tailShift : V → V → V → V → V) via tailShiftDef := .mk
  fun v ↦ by simp [TailShift.construction.eval_resultDef, tailShiftDef]; rfl
instance tailShift_definable : 𝚺₁-Function₄ (tailShift : V → V → V → V → V) := tailShift_defined.to_definable

namespace OffVec

noncomputable def blueprint : VecRec.Blueprint 3 where
  nil := .mkSigma “y Ww Wc T. y = 0”
  adjoin := .mkSigma “y x xs ih Ww Wc T. ∃ l, !mLenDef l Wc T x ∧ ∃ t, !tailShiftDef t xs Ww Wc T ∧
    ∃ o, o = l + t ∧ !adjoinDef y o ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin v x xs ih := (mLen (v 1) (v 2) x + tailShift xs (v 0) (v 1) (v 2)) ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint, mLen_defined.iff, tailShift_defined.iff]

end OffVec

/-- `offVec v Ww Wc T` — the offset of each member's top after all member blocks
(`o_j = mLen x_j + tailShift (tail)`; vector first). -/
noncomputable def offVec (v Ww Wc T : V) : V := OffVec.construction.result ![Ww, Wc, T] v

@[simp] lemma offVec_nil (Ww Wc T : V) : offVec 0 Ww Wc T = 0 := by simp [offVec, OffVec.construction]
@[simp] lemma offVec_adjoin (x v Ww Wc T : V) :
    offVec (x ∷ v) Ww Wc T = (mLen Wc T x + tailShift v Ww Wc T) ∷ offVec v Ww Wc T := by
  simp [offVec, OffVec.construction]

noncomputable def offVecDef : 𝚺₁.Semisentence 5 := OffVec.blueprint.resultDef

instance offVec_defined : 𝚺₁-Function₄ (offVec : V → V → V → V → V) via offVecDef := .mk
  fun v ↦ by simp [OffVec.construction.eval_resultDef, offVecDef]; rfl
instance offVec_definable : 𝚺₁-Function₄ (offVec : V → V → V → V → V) := offVec_defined.to_definable

lemma len_offVec (Ww Wc T : V) : ∀ v : V, len (offVec v Ww Wc T) = len v := by
  intro v
  induction v using adjoin_ISigma1.sigma1_succ_induction with
  | hP => definability
  | nil => simp
  | adjoin x v ih => rw [offVec_adjoin, len_adjoin, len_adjoin, ih]

namespace FvarVec

noncomputable def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y = 0”
  adjoin := .mkSigma “y x xs ih. ∃ z, !qqFvarDef z x ∧ !adjoinDef y z ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin _ x _ ih := (^&x : V) ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end FvarVec

/-- `fvarVec o` — the eigenvariables `^&o_j` of a vector of indices. -/
noncomputable def fvarVec (o : V) : V := FvarVec.construction.result ![] o

@[simp] lemma fvarVec_nil : fvarVec (0 : V) = 0 := by simp [fvarVec, FvarVec.construction]
@[simp] lemma fvarVec_adjoin (x o : V) : fvarVec (x ∷ o) = (^&x : V) ∷ fvarVec o := by
  simp [fvarVec, FvarVec.construction]

noncomputable def fvarVecDef : 𝚺₁.Semisentence 2 := FvarVec.blueprint.resultDef

instance fvarVec_defined : 𝚺₁-Function₁ (fvarVec : V → V) via fvarVecDef := .mk
  fun v ↦ by simp [FvarVec.construction.eval_resultDef, fvarVecDef]; rfl
instance fvarVec_definable : 𝚺₁-Function₁ (fvarVec : V → V) := fvarVec_defined.to_definable

lemma len_fvarVec : ∀ o : V, len (fvarVec o) = len o := by
  intro o
  induction o using adjoin_ISigma1.sigma1_succ_induction with
  | hP => definability
  | nil => simp
  | adjoin x o ih => rw [fvarVec_adjoin, len_adjoin, len_adjoin, ih]

lemma nth_fvarVec : ∀ o : V, ∀ m < len o, (fvarVec o).[m] = ^&(o.[m]) := by
  intro o
  induction o using adjoin_ISigma1.pi1_succ_induction with
  | hP => definability
  | nil => intro m hm; simp at hm
  | adjoin x o ih =>
    intro m hm
    rw [fvarVec_adjoin]
    rcases zero_or_succ m with rfl | ⟨m, rfl⟩
    · simp
    · rw [nth_adjoin_succ, nth_adjoin_succ]
      exact ih m (by rw [len_adjoin] at hm; exact lt_of_add_lt_add_right hm)

/-- The index of the top of a member with offset `o` in a layout at chain offset `i` with `k` members. -/
noncomputable def mTop (i k o : V) : V := i + (2 * k + 1 + o)

/-- The set below prefix `j` of the chain: `s_{j+1}` at `&(i + k + 2 + j)`, or `𝟎` for the innermost member. -/
noncomputable def prevI (i k j : V) : V := prevAt (i + (2 * k + 1)) (i + (k + 1 + j))

/-- **The canonical layout of the sequent `s` at chain offset `i`.** -/
def Layout (Ww Wc T Γ s i : V) : Prop :=
  (∀ j < len (memberList s),
    DossF Ww Γ 0 (memberList s).[j] (mTop i (len (memberList s)) (offVec (memberList s) Ww Wc T).[j]) ∧
    neg LAct (piFact (𝟎 : V) (^&(mTop i (len (memberList s)) (offVec (memberList s) Ww Wc T).[j]))) ∈ Γ ∧
    neg LAct (lenFact (bnum (formulaLen LAct (memberList s).[j]))
      (^&(mTop i (len (memberList s)) (offVec (memberList s) Ww Wc T).[j]))) ∈ Γ ∧
    neg LAct (insFact (^&(i + (len (memberList s) + 1 + j)))
      (^&(mTop i (len (memberList s)) (offVec (memberList s) Ww Wc T).[j])) (prevI i (len (memberList s)) j)) ∈ Γ ∧
    neg LAct (fsetPiFact (^&(i + (len (memberList s) + 1 + j)))) ∈ Γ ∧
    neg LAct (memFact (^&(mTop i (len (memberList s)) (offVec (memberList s) Ww Wc T).[j]))
      (^&(i + (len (memberList s) + 1)))) ∈ Γ) ∧
  neg LAct (setLenFact (^&i) (^&(i + (len (memberList s) + 1)))) ∈ Γ ∧
  neg LAct (leFact (^&i) (bnum (setLen LAct s))) ∈ Γ

/-! ### 1.1 The one transport lemma -/

lemma termShiftIterV_prevAt (k i : V) : ∀ c : V, termShiftIterV (prevAt k i) c = prevAt (k + c) (i + c) := by
  intro c
  induction c using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ c ih => rw [termShiftIterV_succ, ih, termShift_prevAt, add_assoc, add_assoc]

lemma shiftIterV_leFact {n u : V} (hn : IsSemiterm LAct 0 n) (hu : IsSemiterm LAct 0 u) :
    ∀ c : V, shiftIterV (leFact n u) c = leFact (termShiftIterV n c) (termShiftIterV u c) := by
  intro c
  induction c using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ c ih =>
    rw [shiftIterV_succ, ih, shift_leFact (isSemiterm_termShiftIterV hn c) (isSemiterm_termShiftIterV hu c),
      termShiftIterV_succ, termShiftIterV_succ]

lemma termShiftIterV_bnum' (k : V) : ∀ c : V, termShiftIterV (bnum k) c = bnum k := termShiftIterV_bnumTop k

lemma isSemiterm_bnum0 (a : V) : IsSemiterm LAct 0 (bnum a) := isSemiterm_bnum_LAct 0 a

/-- **The layout survives any cut-admitting list, at the moved offset.** -/
theorem Layout.transport {Ww Wc T Γ s i S : V} (hS : NoDrop' S) (h : Layout Ww Wc T Γ s i) :
    Layout Ww Wc T (finalCtx Γ S) s (i + shiftsV S) := by
  obtain ⟨hmem, hsl, hle⟩ := h
  set c := shiftsV S with hc
  set k := len (memberList s) with hk
  have h0 : IsSemiterm LAct (0 : V) (𝟎 : V) := isSemiterm_qqZero_LAct 0
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨hD, hpi, hln, hins, hfs, hm⟩ := hmem j hj
    have e1 : mTop i k (offVec (memberList s) Ww Wc T).[j] + c = mTop (i + c) k (offVec (memberList s) Ww Wc T).[j] := by
      unfold mTop; ring
    have e2 : i + (k + 1 + j) + c = i + c + (k + 1 + j) := by ring
    have e3 : i + (k + 1) + c = i + c + (k + 1) := by ring
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := dossF_transport' hS hD; rwa [← hc, e1] at this
    · have := mem_finalCtx_of_mem' hS hpi
      rwa [shiftIterV_neg (isFormula_piFact h0 (by simp)), shiftIterV_piFact h0 (by simp), termShiftIterV_zeroV,
        termShiftIterV_fvar, ← hc, e1] at this
    · have := mem_finalCtx_of_mem' hS hln
      rwa [shiftIterV_neg (isFormula_lenFact (isSemiterm_bnum0 _) (by simp)),
        shiftIterV_lenFact (isSemiterm_bnum0 _) (by simp), termShiftIterV_bnum', termShiftIterV_fvar, ← hc, e1] at this
    · have := mem_finalCtx_of_mem' hS hins
      unfold prevI at this ⊢
      rw [shiftIterV_neg (isFormula_insFact (by simp) (by simp) (isSemiterm_prevAt _ _)),
        shiftIterV_insFact (by simp) (by simp) (isSemiterm_prevAt _ _), termShiftIterV_fvar, termShiftIterV_fvar,
        termShiftIterV_prevAt, ← hc, e1, e2] at this
      have e4 : i + (2 * k + 1) + c = i + c + (2 * k + 1) := by ring
      rwa [e4] at this
    · have := mem_finalCtx_of_mem' hS hfs
      rwa [shiftIterV_neg (isFormula_fsetPiFact (by simp)), shiftIterV_fsetPiFact (by simp), termShiftIterV_fvar,
        ← hc, e2] at this
    · have := mem_finalCtx_of_mem' hS hm
      rwa [shiftIterV_neg (isFormula_memFact (by simp) (by simp)), shiftIterV_memFact (by simp) (by simp),
        termShiftIterV_fvar, termShiftIterV_fvar, ← hc, e1, e3] at this
  · have := mem_finalCtx_of_mem' hS hsl
    have e3 : i + (k + 1) + c = i + c + (k + 1) := by ring
    rwa [shiftIterV_neg (isFormula_setLenFact (by simp) (by simp)), shiftIterV_setLenFact (by simp) (by simp),
      termShiftIterV_fvar, termShiftIterV_fvar, ← hc, e3] at this
  · have := mem_finalCtx_of_mem' hS hle
    rwa [shiftIterV_neg (isFormula_leFact (by simp) (isSemiterm_bnum0 _)), shiftIterV_leFact (by simp) (isSemiterm_bnum0 _),
      termShiftIterV_fvar, termShiftIterV_bnum', ← hc] at this

end layoutDef

/-! ## 2. The layout builder `layoutSteps` (member blocks, the chain, the `setLen` fold) -/

section layoutBuild

/-! ### 2.1 Member blocks: the walk of a member, then its (re-indexed) length pass -/

/-- `memberBlock x := describeF Ww 0 x ++ reidxL (lenSteps Wc T 0 x 0)`. -/
noncomputable def memberBlock (Ww Wc T x : V) : V :=
  appendV (describeF Ww 0 x) (reidxL (lenSteps Wc T 0 x 0))

noncomputable def memberBlockDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y Ww Wc T x. ∃ d, !describeFDef d Ww 0 x ∧ ∃ l, !lenStepsDef l Wc T 0 x 0 ∧ ∃ r, !reidxLDef r l ∧ !appendVDef y d r”

instance memberBlock_defined : 𝚺₁-Function₄ (memberBlock : V → V → V → V → V) via memberBlockDef := .mk fun v ↦ by
  simp [memberBlockDef, memberBlock, describeF_defined.iff, lenSteps_defined.iff, reidxL_defined.iff,
    appendV_defined.iff, numeral_eq_natCast]
instance memberBlock_definable : 𝚺₁-Function₄ (memberBlock : V → V → V → V → V) := memberBlock_defined.to_definable

namespace MemberBlocks

noncomputable def blueprint : VecRec.Blueprint 3 where
  nil := .mkSigma “y Ww Wc T. y = 0”
  adjoin := .mkSigma “y x xs ih Ww Wc T. ∃ b, !memberBlockDef b Ww Wc T x ∧ !appendVDef y b ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin v x _ ih := appendV (memberBlock (v 0) (v 1) (v 2) x) ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint, memberBlock_defined.iff, appendV_defined.iff]

end MemberBlocks

/-- `memberBlocks v Ww Wc T` — the member blocks of `v`, first member first (vector first). -/
noncomputable def memberBlocks (v Ww Wc T : V) : V := MemberBlocks.construction.result ![Ww, Wc, T] v

@[simp] lemma memberBlocks_nil (Ww Wc T : V) : memberBlocks 0 Ww Wc T = 0 := by
  simp [memberBlocks, MemberBlocks.construction]
@[simp] lemma memberBlocks_adjoin (x v Ww Wc T : V) :
    memberBlocks (x ∷ v) Ww Wc T = appendV (memberBlock Ww Wc T x) (memberBlocks v Ww Wc T) := by
  simp [memberBlocks, MemberBlocks.construction]

noncomputable def memberBlocksDef : 𝚺₁.Semisentence 5 := MemberBlocks.blueprint.resultDef

instance memberBlocks_defined : 𝚺₁-Function₄ (memberBlocks : V → V → V → V → V) via memberBlocksDef := .mk
  fun v ↦ by simp [MemberBlocks.construction.eval_resultDef, memberBlocksDef]; rfl
instance memberBlocks_definable : 𝚺₁-Function₄ (memberBlocks : V → V → V → V → V) := memberBlocks_defined.to_definable

/-! ### 2.2 The prefix sets of the chain (from the end) -/

namespace PsetAux

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y xs. y = 0”
  succ := .mkSigma “y ih c xs. ∃ t, !nthFromEndDef t xs c ∧ !insertDef y t ih”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 0
  succ := fun v c ih ↦ insert (nthFromEnd (v 0) c) ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, nthFromEnd_defined.iff]

end PsetAux

/-- `psetAux xs c` — the set of the last `c` members (`s_{k−c}` of the chain). -/
noncomputable def psetAux (xs c : V) : V := PsetAux.construction.result ![xs] c

@[simp] lemma psetAux_zero (xs : V) : psetAux xs 0 = 0 := by simp [psetAux, PsetAux.construction]
lemma psetAux_succ (xs c : V) : psetAux xs (c + 1) = insert (nthFromEnd xs c) (psetAux xs c) := by
  simp [psetAux, PsetAux.construction]

noncomputable def psetAuxDef : 𝚺₁.Semisentence 3 := PsetAux.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance psetAux_defined : 𝚺₁-Function₂ (psetAux : V → V → V) via psetAuxDef := .mk
  fun v ↦ by simp [PsetAux.construction.result_defined_iff, psetAuxDef]; rfl
instance psetAux_definable : 𝚺₁-Function₂ (psetAux : V → V → V) := psetAux_defined.to_definable

/-! ### 2.3 The `setLen` fold: one block per member, innermost first -/

/-- `sum2Fact a b n = leFact (bnum a ^+ bnum b) (bnum n)` as a Σ₁ graph. -/
noncomputable def sum2FactDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y a b n. ∃ x, !bnumGraph x a ∧ ∃ u, !bnumGraph u b ∧ ∃ p, !qqAddGraph p x u ∧ ∃ w, !bnumGraph w n ∧ !leFactDef y p w”

instance sum2Fact_defined : 𝚺₁-Function₃ (sum2Fact : V → V → V → V) via sum2FactDef := .mk fun v ↦ by
  simp [sum2FactDef, sum2Fact, bnum.defined.iff, leFact_defined.iff, numeral_eq_natCast]
instance sum2Fact_definable : 𝚺₁-Function₃ (sum2Fact : V → V → V → V) := sum2Fact_defined.to_definable

/-- The innermost block (`c = 0`): a length object for `s_{k−1}` (at `&k`), then `setLenSingLe`. The member's
object is at `&(o + (k + 1) + c + 1)` after the shift. -/
noncomputable def foldBlock0 (W k c o x : V) : V :=
  ?[mkStep W 85 ?[^&k], mkStep W 155 ?[^&(o + (k + 1) + c + 1), ^&(k + 1), ^&0, bnum (formulaLen LAct x)]]

/-- A general block (`c ≥ 1`): the length object, `setLenInsertLe`, `leRefl`, `leAddLeAdd`, the closed
`sum2Fact L' |x| L` (`L' = setLen s_{j+1}`, `L = setLen s_j`), `leTrans`. -/
noncomputable def foldBlockS (W T k c o x L' L : V) : V :=
  ?[mkStep W 85 ?[^&k],
    mkStep W 111 ?[^&(o + (k + 1) + c + 1), ^&(k + 2), ^&(k + 1), ^&0, ^&1, bnum (formulaLen LAct x)],
    mkStep W 109 ?[bnum (formulaLen LAct x)],
    mkStep W 108 ?[^&0, ^&1, bnum (formulaLen LAct x), bnum L', bnum (formulaLen LAct x)],
    sLemma (sum2Fact L' (formulaLen LAct x) L) (sum2Code T L' (formulaLen LAct x) L),
    mkStep W 110 ?[bnum L, bnum L' ^+ bnum (formulaLen LAct x), ^&0]]

noncomputable def foldBlock0Def : 𝚺₁.Semisentence 6 := .mkSigma
  “y W k c o x. ∃ zk, !qqFvarDef zk k ∧ ∃ e₁, !adjoinDef e₁ zk 0 ∧ ∃ s₁, !mkStepDef s₁ W 85 e₁ ∧
    ∃ i₁, i₁ = o + (k + 1) + c + 1 ∧ ∃ zx, !qqFvarDef zx i₁ ∧ ∃ i₂, i₂ = k + 1 ∧ ∃ zs, !qqFvarDef zs i₂ ∧
    ∃ z0, !qqFvarDef z0 0 ∧ ∃ fl, !(formulaLenGraph LAct) fl x ∧ ∃ bl, !bnumGraph bl fl ∧
    ∃ v₁, !adjoinDef v₁ bl 0 ∧ ∃ v₂, !adjoinDef v₂ z0 v₁ ∧ ∃ v₃, !adjoinDef v₃ zs v₂ ∧ ∃ e₂, !adjoinDef e₂ zx v₃ ∧
    ∃ s₂, !mkStepDef s₂ W 155 e₂ ∧ ∃ r₂, !adjoinDef r₂ s₂ 0 ∧ !adjoinDef y s₁ r₂”

instance foldBlock0_defined : 𝚺₁-Function₅ (foldBlock0 : V → V → V → V → V → V) via foldBlock0Def := .mk fun v ↦ by
  simp [foldBlock0Def, foldBlock0, mkStep_defined.iff, formulaLen.defined.iff, bnum.defined.iff, numeral_eq_natCast]
instance foldBlock0_definable : 𝚺₁.DefinableFunction₅ (foldBlock0 : V → V → V → V → V → V) := foldBlock0_defined.to_definable

noncomputable def foldBlockSDef : 𝚺₁.Semisentence 9 := .mkSigma
  “y W T k c o x L' L. ∃ zk, !qqFvarDef zk k ∧ ∃ e₁, !adjoinDef e₁ zk 0 ∧ ∃ s₁, !mkStepDef s₁ W 85 e₁ ∧
    ∃ i₁, i₁ = o + (k + 1) + c + 1 ∧ ∃ zx, !qqFvarDef zx i₁ ∧ ∃ i₂, i₂ = k + 2 ∧ ∃ zs₂, !qqFvarDef zs₂ i₂ ∧
    ∃ i₃, i₃ = k + 1 ∧ ∃ zs₁, !qqFvarDef zs₁ i₃ ∧ ∃ z0, !qqFvarDef z0 0 ∧ ∃ z1, !qqFvarDef z1 1 ∧
    ∃ fl, !(formulaLenGraph LAct) fl x ∧ ∃ bl, !bnumGraph bl fl ∧ ∃ bL', !bnumGraph bL' L' ∧ ∃ bL, !bnumGraph bL L ∧
    ∃ u₁, !adjoinDef u₁ bl 0 ∧ ∃ u₂, !adjoinDef u₂ z1 u₁ ∧ ∃ u₃, !adjoinDef u₃ z0 u₂ ∧ ∃ u₄, !adjoinDef u₄ zs₁ u₃ ∧
    ∃ u₅, !adjoinDef u₅ zs₂ u₄ ∧ ∃ e₂, !adjoinDef e₂ zx u₅ ∧ ∃ s₂, !mkStepDef s₂ W 111 e₂ ∧
    ∃ e₃, !adjoinDef e₃ bl 0 ∧ ∃ s₃, !mkStepDef s₃ W 109 e₃ ∧
    ∃ w₁, !adjoinDef w₁ bl 0 ∧ ∃ w₂, !adjoinDef w₂ bL' w₁ ∧ ∃ w₃, !adjoinDef w₃ bl w₂ ∧ ∃ w₄, !adjoinDef w₄ z1 w₃ ∧
    ∃ e₄, !adjoinDef e₄ z0 w₄ ∧ ∃ s₄, !mkStepDef s₄ W 108 e₄ ∧
    ∃ A, !sum2FactDef A L' fl L ∧ ∃ dA, !sum2CodeDef dA T L' fl L ∧ ∃ q, !pairDef q A dA ∧ ∃ s₅, !pairDef s₅ 7 q ∧
    ∃ p, !qqAddGraph p bL' bl ∧ ∃ t₁, !adjoinDef t₁ z0 0 ∧ ∃ t₂, !adjoinDef t₂ p t₁ ∧ ∃ e₆, !adjoinDef e₆ bL t₂ ∧
    ∃ s₆, !mkStepDef s₆ W 110 e₆ ∧
    ∃ r₆, !adjoinDef r₆ s₆ 0 ∧ ∃ r₅, !adjoinDef r₅ s₅ r₆ ∧ ∃ r₄, !adjoinDef r₄ s₄ r₅ ∧ ∃ r₃, !adjoinDef r₃ s₃ r₄ ∧
    ∃ r₂, !adjoinDef r₂ s₂ r₃ ∧ !adjoinDef y s₁ r₂”

instance foldBlockS_defined :
    𝚺₁.DefinedFunction (fun v : Fin 8 → V ↦ foldBlockS (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) foldBlockSDef := .mk
  fun v ↦ by
    simp [foldBlockSDef, foldBlockS, mkStep_defined.iff, formulaLen.defined.iff, bnum.defined.iff,
      sum2Fact_defined.iff, sum2Code_defined.iff, sLemma, numeral_eq_natCast]

/-- Block `c` of the fold: `x = nthFromEnd xs c` (the member), `o = nthFromEnd os c` (its offset). -/
noncomputable def foldBlock (W T xs os k c : V) : V :=
  if c = 0 then foldBlock0 W k c (nthFromEnd os c) (nthFromEnd xs c)
  else foldBlockS W T k c (nthFromEnd os c) (nthFromEnd xs c) (setLen LAct (psetAux xs c)) (setLen LAct (psetAux xs (c + 1)))

noncomputable def foldBlockDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y W T xs os k c. ∃ o, !nthFromEndDef o os c ∧ ∃ x, !nthFromEndDef x xs c ∧
    (c = 0 → !foldBlock0Def y W k c o x) ∧
    (c ≠ 0 → ∃ p', !psetAuxDef p' xs c ∧ ∃ L', !(setLenDef LAct) L' p' ∧ ∃ c1, c1 = c + 1 ∧
      ∃ p, !psetAuxDef p xs c1 ∧ ∃ L, !(setLenDef LAct) L p ∧ !foldBlockSDef y W T k c o x L' L)”

instance foldBlock_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ foldBlock (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) foldBlockDef := .mk
  fun v ↦ by
    simp [foldBlockDef, nthFromEnd_defined.iff, foldBlock0_defined.iff, psetAux_defined.iff, setLen_defined.iff,
      foldBlockS_defined.iff, numeral_eq_natCast]
    unfold foldBlock
    by_cases h : v 6 = 0
    · simp [h]
    · simp [h]

namespace LenFoldAux

/-- The parameters packed: `p = ⟪W, T, xs, os, k⟫` (one parameter keeps the function 2-ary, which
`definability` can use; a 6-ary function defeats it). -/
noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y p. y = 0”
  succ := .mkSigma “y ih c p. ∃ W, !pi₁Def W p ∧ ∃ q₁, !pi₂Def q₁ p ∧ ∃ T, !pi₁Def T q₁ ∧ ∃ q₂, !pi₂Def q₂ q₁ ∧
    ∃ xs, !pi₁Def xs q₂ ∧ ∃ q₃, !pi₂Def q₃ q₂ ∧ ∃ os, !pi₁Def os q₃ ∧ ∃ k, !pi₂Def k q₃ ∧
    ∃ b, !foldBlockDef b W T xs os k c ∧ !appendVDef y ih b”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 0
  succ := fun v c ih ↦ appendV ih (foldBlock (π₁ (v 0)) (π₁ (π₂ (v 0))) (π₁ (π₂ (π₂ (v 0))))
    (π₁ (π₂ (π₂ (π₂ (v 0))))) (π₂ (π₂ (π₂ (π₂ (v 0))))) c)
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, foldBlock_defined.iff, appendV_defined.iff]

end LenFoldAux

/-- The first `c` blocks of the fold, with the parameters packed. -/
noncomputable def lenFoldAuxP (p c : V) : V := LenFoldAux.construction.result ![p] c

noncomputable def lenFoldAuxPDef : 𝚺₁.Semisentence 3 :=
  LenFoldAux.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance lenFoldAuxP_defined : 𝚺₁-Function₂ (lenFoldAuxP : V → V → V) via lenFoldAuxPDef := .mk
  fun v ↦ by simp [LenFoldAux.construction.result_defined_iff, lenFoldAuxPDef]; rfl
instance lenFoldAuxP_definable : 𝚺₁-Function₂ (lenFoldAuxP : V → V → V) := lenFoldAuxP_defined.to_definable

/-- The first `c` blocks of the fold. -/
noncomputable def lenFoldAux (W T xs os k c : V) : V := lenFoldAuxP ⟪W, T, xs, os, k⟫ c

@[simp] lemma lenFoldAux_zero (W T xs os k : V) : lenFoldAux W T xs os k 0 = 0 := by
  simp [lenFoldAux, lenFoldAuxP, LenFoldAux.construction]
lemma lenFoldAux_succ (W T xs os k c : V) :
    lenFoldAux W T xs os k (c + 1) = appendV (lenFoldAux W T xs os k c) (foldBlock W T xs os k c) := by
  simp [lenFoldAux, lenFoldAuxP, LenFoldAux.construction]

noncomputable def lenFoldAuxDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y W T xs os k c. ∃ q₃, !pairDef q₃ os k ∧ ∃ q₂, !pairDef q₂ xs q₃ ∧ ∃ q₁, !pairDef q₁ T q₂ ∧ ∃ p, !pairDef p W q₁ ∧
    !lenFoldAuxPDef y p c”

instance lenFoldAux_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ lenFoldAux (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) lenFoldAuxDef := .mk
  fun v ↦ by simp [lenFoldAuxDef, lenFoldAux, lenFoldAuxP_defined.iff]

/-- **The `setLen` fold** of the whole chain: `k` blocks, innermost first. -/
noncomputable def lenFold (W T xs os : V) : V := lenFoldAux W T xs os (len xs) (len xs)

noncomputable def lenFoldDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y W T xs os. ∃ k, !lenDef k xs ∧ !lenFoldAuxDef y W T xs os k k”

instance lenFold_defined : 𝚺₁-Function₄ (lenFold : V → V → V → V → V) via lenFoldDef := .mk fun v ↦ by
  simp [lenFoldDef, lenFold, lenFoldAux_defined.iff]
instance lenFold_definable : 𝚺₁-Function₄ (lenFold : V → V → V → V → V) := lenFold_defined.to_definable

/-! ### 2.4 The whole builder -/

/-- **`layoutSteps s`**: the member blocks (ascending), the chain over the member objects, the `setLen` fold.
Pieces: `Ww` (walk), `Wl` (layout), `Wc` (certification), `W` (prologue); `T` the `NumSteps` table. -/
noncomputable def layoutSteps (Ww Wl Wc W T s : V) : V :=
  appendV (memberBlocks (memberList s) Ww Wc T)
    (appendV (chainSteps Wl (fvarVec (offVec (memberList s) Ww Wc T)))
      (lenFold W T (memberList s) (offVec (memberList s) Ww Wc T)))

noncomputable def layoutStepsDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y Ww Wl Wc W T s. ∃ xs, !memberListDef xs s ∧ ∃ M, !memberBlocksDef M xs Ww Wc T ∧
    ∃ os, !offVecDef os xs Ww Wc T ∧ ∃ ov, !fvarVecDef ov os ∧ ∃ C, !chainStepsDef C Wl ov ∧
    ∃ F, !lenFoldDef F W T xs os ∧ ∃ r, !appendVDef r C F ∧ !appendVDef y M r”

instance layoutSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ layoutSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) layoutStepsDef := .mk
  fun v ↦ by
    simp [layoutStepsDef, layoutSteps, memberList_defined.iff, memberBlocks_defined.iff, offVec_defined.iff,
      fvarVec_defined.iff, chainSteps_defined.iff, lenFold_defined.iff, appendV_defined.iff]

end layoutBuild

/-! ### 2.5 The member blocks are applicable -/

section memberBlocksOK

/-- The walk's count bound, standalone. -/
lemma descCountF_succ_le {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {r : V} (hr : IsSemiformula LAct 0 r) :
    descCountF walkPieces 0 r + 1 ≤ 2 * formulaLen LAct r :=
  (describeF_ok htbl hW hr (E := 2 * 0 + 2 * formulaLen LAct r + 8) le_rfl (Γ := 0) IsFormulaSet.empty).2.2.2.1

lemma mLen_succ_le {Wc : V} (hWc : Wc = certPieces) (T : V) {x : V} (hx : IsSemiformula LAct 0 x) :
    mLen Wc T x + 1 ≤ 2 * formulaLen LAct x := (lenSteps_struct hWc T hx 0).2.1

lemma mShift_le {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {Wc : V} (hWc : Wc = certPieces) (T : V)
    {x : V} (hx : IsSemiformula LAct 0 x) : mShift walkPieces Wc T x ≤ 4 * formulaLen LAct x := by
  have h1 := descCountF_succ_le htbl hW hx
  have h2 := mLen_succ_le hWc T hx
  unfold mShift
  calc descCountF walkPieces 0 x + mLen Wc T x ≤ 2 * formulaLen LAct x + 2 * formulaLen LAct x :=
        add_le_add (le_trans le_self_add h1) (le_trans le_self_add h2)
    _ = 4 * formulaLen LAct x := by ring

lemma tailShift_le {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {Wc : V} (hWc : Wc = certPieces) (T : V) :
    ∀ v : V, (∀ j < len v, IsSemiformula LAct 0 v.[j]) → tailShift v walkPieces Wc T ≤ 4 * listSum (flenVec v) := by
  intro v
  induction v using adjoin_ISigma1.pi1_succ_induction with
  | hP => definability
  | nil => intro _; simp
  | adjoin x v ih =>
    intro hv
    have hx : IsSemiformula LAct 0 x := by have := hv 0 (by simp); rwa [nth_adjoin_zero] at this
    have hv' : ∀ j < len v, IsSemiformula LAct 0 v.[j] := fun j hj ↦ by
      have := hv (j + 1) (by rw [len_adjoin]; exact (add_lt_add_iff_right 1).mpr hj)
      rwa [nth_adjoin_succ] at this
    rw [tailShift_adjoin, flenVec_adjoin, listSum_adjoin]
    calc mShift walkPieces Wc T x + tailShift v walkPieces Wc T
        ≤ 4 * formulaLen LAct x + 4 * listSum (flenVec v) := add_le_add (mShift_le htbl hW hWc T hx) (ih hv')
      _ = 4 * (formulaLen LAct x + listSum (flenVec v)) := by ring

lemma nth_offVec_le (Ww Wc T : V) : ∀ v : V, ∀ j < len v, (offVec v Ww Wc T).[j] ≤ tailShift v Ww Wc T := by
  intro v
  induction v using adjoin_ISigma1.pi1_succ_induction with
  | hP => definability
  | nil => intro j hj; simp at hj
  | adjoin x v ih =>
    intro j hj
    rw [offVec_adjoin, tailShift_adjoin]
    rcases zero_or_succ j with rfl | ⟨j, rfl⟩
    · rw [nth_adjoin_zero]
      exact add_le_add (le_add_self) le_rfl
    · rw [nth_adjoin_succ]
      exact le_trans (ih j (by rw [len_adjoin] at hj; exact lt_of_add_lt_add_right hj)) le_add_self

/-- **One member block is applicable**: it walks `x` and derives its numeric length; afterwards the walk dossier,
`piFact 𝟎` and `lenFact (bnum |x|)` of `x` sit at `&(mLen x)`. -/
theorem memberBlock_ok {tbl N N' B' Wc T x D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWc : Wc = certPieces)
    (hx : IsSemiformula LAct 0 x) (hxD : formulaLen LAct x ≤ D) (hE : 13 * D + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (memberBlock walkPieces Wc T x) ∧ NoDrop' (memberBlock walkPieces Wc T x) ∧
    shiftsV (memberBlock walkPieces Wc T x) = mShift walkPieces Wc T x ∧
    len (memberBlock walkPieces Wc T x) ≤ 26 * formulaLen LAct x ∧
    DossF walkPieces (finalCtx Γ (memberBlock walkPieces Wc T x)) 0 x (mLen Wc T x) ∧
    neg LAct (piFact (𝟎 : V) (^&(mLen Wc T x))) ∈ finalCtx Γ (memberBlock walkPieces Wc T x) ∧
    neg LAct (lenFact (bnum (formulaLen LAct x)) (^&(mLen Wc T x))) ∈ finalCtx Γ (memberBlock walkPieces Wc T x) := by
  have hW := hP.walkTable
  have hC := hP.certTable
  have htblC := hP.tableOK_certView htbl
  have h2D : 2 * formulaLen LAct x ≤ 13 * D :=
    le_trans (mul_le_mul_of_nonneg_left hxD zero_le) (mul_le_mul_of_nonneg_right (by norm_num) zero_le)
  have h5D : 5 * formulaLen LAct x ≤ 13 * D :=
    le_trans (mul_le_mul_of_nonneg_left hxD zero_le) (mul_le_mul_of_nonneg_right (by norm_num) zero_le)
  have hE1 : 2 * (0 : V) + 2 * formulaLen LAct x + 8 ≤ E := by
    rw [mul_zero, zero_add]; exact le_trans (add_le_add h2D le_rfl) hE
  obtain ⟨wok, wnd, wsh, _, wpi⟩ := describeF_ok htbl hW hx hE1 hΓ
  set Γ₁ := finalCtx Γ (describeF walkPieces 0 x) with hΓ₁
  have hΓ₁f : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ wok
  have hD₀ : DossF walkPieces Γ₁ 0 x 0 := dossF_of_walk wnd
  have hE2 : 2 * (0 : V) + 13 * formulaLen LAct x + 8 ≤ E := by
    rw [mul_zero, zero_add]; exact le_trans (add_le_add (mul_le_mul_of_nonneg_left hxD zero_le) le_rfl) hE
  have hE3 : (0 : V) + 5 * formulaLen LAct x + 2 ≤ E := by
    rw [zero_add]; exact le_trans (add_le_add h5D (by norm_num)) hE
  obtain ⟨lok, lnd, lsh, llen, lfact⟩ := lenSteps_ok htblC hC htblN rfl hWc hx hE2 hE3 hΓ₁f hD₀
  rw [zero_add] at lfact
  have lok' := listOK_reidxL hP lok
  have hlw := len_describeF_le walkPieces hx
  have hpi : neg LAct (piFact (𝟎 : V) (^&0)) ∈ Γ₁ := by rwa [cTV_zero] at wpi
  refine ⟨listOK_appendV wok (by rw [← hΓ₁]; exact lok'), noDrop'_appendV wnd.noDrop' (noDrop'_reidxL lnd), ?_, ?_, ?_, ?_, ?_⟩
  · unfold memberBlock; rw [shiftsV_appendV, shiftsV_reidxL, wsh]; rfl
  · unfold memberBlock; rw [len_appendV, len_reidxL]
    calc len (describeF walkPieces 0 x) + len (lenSteps Wc T 0 x 0)
        ≤ 12 * formulaLen LAct x + 14 * formulaLen LAct x := add_le_add (le_trans le_self_add hlw) llen
      _ = 26 * formulaLen LAct x := by ring
  · unfold memberBlock; rw [finalCtx_appendV, finalCtx_reidxL, ← hΓ₁]
    have := dossF_transport' lnd hD₀; rwa [zero_add] at this
  · unfold memberBlock; rw [finalCtx_appendV, finalCtx_reidxL, ← hΓ₁]
    have := mem_finalCtx_of_mem' lnd hpi
    rwa [shiftIterV_neg (isFormula_piFact (isSemiterm_qqZero_LAct 0) (by simp)),
      shiftIterV_piFact (isSemiterm_qqZero_LAct 0) (by simp), termShiftIterV_zeroV, termShiftIterV_fvar, zero_add] at this
  · unfold memberBlock; rw [finalCtx_appendV, finalCtx_reidxL, ← hΓ₁]; exact lfact

/-- The invariant of the member blocks (packaged for `definability`). -/
def MBOut (tbl E Ww Wc T v Γ : V) : Prop :=
  ListOK tbl E ((8 : ℕ) : V) Γ (memberBlocks v Ww Wc T) ∧ NoDrop' (memberBlocks v Ww Wc T) ∧
  shiftsV (memberBlocks v Ww Wc T) = tailShift v Ww Wc T ∧ len (memberBlocks v Ww Wc T) ≤ 26 * listSum (flenVec v) ∧
  ∀ j < len v, DossF Ww (finalCtx Γ (memberBlocks v Ww Wc T)) 0 v.[j] (offVec v Ww Wc T).[j] ∧
    neg LAct (piFact (𝟎 : V) (^&((offVec v Ww Wc T).[j]))) ∈ finalCtx Γ (memberBlocks v Ww Wc T) ∧
    neg LAct (lenFact (bnum (formulaLen LAct v.[j])) (^&((offVec v Ww Wc T).[j]))) ∈ finalCtx Γ (memberBlocks v Ww Wc T)

set_option maxHeartbeats 1000000 in
instance mbOut_definable : 𝚫₁.Definable (fun v : Fin 7 → V ↦ MBOut (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := by
  unfold MBOut; definability

/-- **The member blocks are applicable, member by member.** -/
theorem memberBlocks_ok {tbl N N' B' Wc T D E : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWc : Wc = certPieces) (hE : 13 * D + 8 ≤ E) :
    ∀ v : V, (∀ j < len v, IsSemiformula LAct 0 v.[j] ∧ formulaLen LAct v.[j] ≤ D) →
      ∀ Γ, IsFormulaSet LAct Γ → MBOut tbl E walkPieces Wc T v Γ := by
  intro v
  induction v using adjoin_ISigma1.pi1_succ_induction with
  | hP => definability
  | nil =>
    intro _ Γ hΓ
    refine ⟨by rw [memberBlocks_nil]; exact listOK_nil _ _ _ _, by rw [memberBlocks_nil]; exact noDrop'_nil,
      by rw [memberBlocks_nil, shiftsV_nil, tailShift_nil], by rw [memberBlocks_nil]; simp, fun j hj ↦ by simp at hj⟩
  | adjoin x v ih =>
    intro hv Γ hΓ
    have hx := hv 0 (by simp)
    rw [nth_adjoin_zero] at hx
    have hv' : ∀ j < len v, IsSemiformula LAct 0 v.[j] ∧ formulaLen LAct v.[j] ≤ D := fun j hj ↦ by
      have := hv (j + 1) (by rw [len_adjoin]; exact (add_lt_add_iff_right 1).mpr hj)
      rwa [nth_adjoin_succ] at this
    obtain ⟨bok, bnd, bsh, blen, bD, bpi, bln⟩ := memberBlock_ok htbl hP htblN hWc hx.1 hx.2 hE hΓ
    set Γ₁ := finalCtx Γ (memberBlock walkPieces Wc T x) with hΓ₁
    have hΓ₁f : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ bok
    obtain ⟨vok, vnd, vsh, vlen, vfacts⟩ := ih hv' Γ₁ hΓ₁f
    rw [MBOut, memberBlocks_adjoin]
    refine ⟨listOK_appendV bok vok, noDrop'_appendV bnd vnd, ?_, ?_, ?_⟩
    · rw [shiftsV_appendV, bsh, vsh, tailShift_adjoin]
    · rw [len_appendV, flenVec_adjoin, listSum_adjoin]
      calc len (memberBlock walkPieces Wc T x) + len (memberBlocks v walkPieces Wc T)
          ≤ 26 * formulaLen LAct x + 26 * listSum (flenVec v) := add_le_add blen vlen
        _ = 26 * (formulaLen LAct x + listSum (flenVec v)) := by ring
    · intro j hj
      rw [finalCtx_appendV, ← hΓ₁]
      rcases zero_or_succ j with rfl | ⟨j, rfl⟩
      · rw [nth_adjoin_zero, offVec_adjoin, nth_adjoin_zero]
        refine ⟨?_, ?_, ?_⟩
        · have := dossF_transport' vnd bD; rwa [vsh] at this
        · have := mem_finalCtx_of_mem' vnd bpi
          rwa [shiftIterV_neg (isFormula_piFact (isSemiterm_qqZero_LAct 0) (by simp)),
            shiftIterV_piFact (isSemiterm_qqZero_LAct 0) (by simp), termShiftIterV_zeroV, termShiftIterV_fvar, vsh] at this
        · have := mem_finalCtx_of_mem' vnd bln
          rwa [shiftIterV_neg (isFormula_lenFact (isSemiterm_bnum0 _) (by simp)),
            shiftIterV_lenFact (isSemiterm_bnum0 _) (by simp), termShiftIterV_bnum', termShiftIterV_fvar, vsh] at this
      · rw [nth_adjoin_succ, offVec_adjoin, nth_adjoin_succ]
        exact vfacts j (by rw [len_adjoin] at hj; exact lt_of_add_lt_add_right hj)

end memberBlocksOK

/-! ### 2.6 The prefix sets: membership, distinctness, lengths -/

section psetLemmas

lemma mem_psetAux (xs : V) : ∀ c : V, ∀ y, y ∈ psetAux xs c ↔ ∃ m < c, nthFromEnd xs m = y := by
  intro c
  induction c using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro y; simp
  | succ c ih =>
    intro y
    rw [psetAux_succ, mem_bitInsert_iff, ih]
    constructor
    · rintro (rfl | ⟨m, hm, rfl⟩)
      · exact ⟨c, lt_add_one c, rfl⟩
      · exact ⟨m, lt_trans hm (lt_add_one c), rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hm) with h | rfl
      · exact Or.inr ⟨m, h, rfl⟩
      · exact Or.inl rfl

lemma nthFromEnd_memberList {s c : V} (hc : c < len (memberList s)) :
    nthFromEnd (memberList s) c = (memberList s).[len (memberList s) - (c + 1)] :=
  nthFromEnd_eq (by rw [tsub_add_cancel_of_le (lt_iff_succ_le.mp hc)])

lemma sub_succ_lt_len {s c : V} (hc : c < len (memberList s)) :
    len (memberList s) - (c + 1) < len (memberList s) :=
  tsub_lt_self (lt_of_le_of_lt zero_le hc) (lt_of_lt_of_le _root_.zero_lt_one le_add_self)

/-- The members are distinct: the next member is not among the later ones. -/
lemma nthFromEnd_not_mem_psetAux {s c : V} (hc : c < len (memberList s)) :
    nthFromEnd (memberList s) c ∉ psetAux (memberList s) c := by
  intro h
  obtain ⟨m, hm, hme⟩ := (mem_psetAux _ c _).mp h
  have hmk : m < len (memberList s) := lt_trans hm hc
  rw [nthFromEnd_memberList hmk, nthFromEnd_memberList hc] at hme
  have e := memberList_nodup (sub_succ_lt_len hmk) (sub_succ_lt_len hc) hme
  have h1 := tsub_add_cancel_of_le (lt_iff_succ_le.mp hmk)
  have h2 := tsub_add_cancel_of_le (lt_iff_succ_le.mp hc)
  rw [e] at h1
  have h3 : m + 1 = c + 1 := add_left_cancel (h1.trans h2.symm)
  have h4 : m = c := add_right_cancel h3
  subst h4
  exact _root_.lt_irrefl m hm

lemma setLen_psetAux_succ {s c : V} (hc : c < len (memberList s)) :
    setLen LAct (psetAux (memberList s) (c + 1)) =
      setLen LAct (psetAux (memberList s) c) + formulaLen LAct (nthFromEnd (memberList s) c) := by
  rw [psetAux_succ]; exact setLen_insert_of_not_mem_V (nthFromEnd_not_mem_psetAux hc)

lemma setLen_psetAux_zero (xs : V) : setLen LAct (psetAux xs 0) = 0 := by
  rw [psetAux_zero]; exact setLen_empty

/-- The whole chain is the sequent. -/
lemma psetAux_len_eq (s : V) : psetAux (memberList s) (len (memberList s)) = s := by
  apply mem_ext
  intro y
  rw [mem_psetAux, ← mem_memberList_iff]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨_, sub_succ_lt_len hm, (nthFromEnd_memberList hm).symm⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨len (memberList s) - (a + 1), sub_succ_lt_len ha, nthFromEnd_eq ?_⟩
    rw [show a + (len (memberList s) - (a + 1) + 1) = len (memberList s) - (a + 1) + (a + 1) by ring,
      tsub_add_cancel_of_le (lt_iff_succ_le.mp ha)]

lemma setLen_psetAux_mono (s : V) :
    ∀ c ≤ len (memberList s), ∀ c' ≤ c, setLen LAct (psetAux (memberList s) c') ≤ setLen LAct (psetAux (memberList s) c) := by
  intro c
  induction c using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _ c' hc'; rw [le_zero_iff.mp hc']
  | succ c ih =>
    intro hc c' hc'
    rcases lt_or_eq_of_le hc' with h | rfl
    · have := ih (le_trans le_self_add hc) c' (lt_succ_iff_le.mp h)
      rw [setLen_psetAux_succ (lt_of_lt_of_le (lt_add_one c) hc)]
      exact le_trans this le_self_add
    · exact le_rfl

lemma setLen_psetAux_le {s c : V} (hc : c ≤ len (memberList s)) :
    setLen LAct (psetAux (memberList s) c) ≤ setLen LAct s := by
  have := setLen_psetAux_mono s (len (memberList s)) le_rfl c hc
  rwa [psetAux_len_eq] at this

end psetLemmas

/-! ### 2.7 The fold blocks are applicable -/

section foldOK

lemma mkStep_pro_layout (i : ℕ) (hi : i < layoutRowCount) (ev : V) :
    mkStep proPieces (i : V) ev = mkStep layoutPieces (i : V) ev := by
  rw [mkStep_proPieces_lt i (lt_of_lt_of_le hi (by decide)), mkStep_topPieces_lt i (lt_of_lt_of_le hi (by decide)),
    mkStep_frag2Pieces_lt i (lt_of_lt_of_le hi (by decide)), mkStep_frag1Pieces_lt i hi]

lemma mkStep_pro_frag1 (i : ℕ) (hi : i < frag1RowCount) (ev : V) :
    mkStep proPieces (i : V) ev = mkStep frag1Pieces (i : V) ev := by
  rw [mkStep_proPieces_lt i (lt_of_lt_of_le hi (by decide)), mkStep_topPieces_lt i (lt_of_lt_of_le hi (by decide)),
    mkStep_frag2Pieces_lt i hi]

lemma mkStep_pro_frag2 (i : ℕ) (hi : i < frag2RowCount) (ev : V) :
    mkStep proPieces (i : V) ev = mkStep frag2Pieces (i : V) ev := by
  rw [mkStep_proPieces_lt i (lt_of_lt_of_le hi (by decide)), mkStep_topPieces_lt i hi]

lemma memIns {Γ f x : V} (h : x ∈ Γ) : x ∈ insert f Γ := by simp [h]
lemma memInsSelf (f Γ : V) : f ∈ insert f Γ := by simp

lemma termLen_fvar_le' {i E : V} (h : i + 1 ≤ E) : termLen LAct (^&i : V) ≤ E := by rw [termLen_fvar]; exact h

set_option maxHeartbeats 4000000 in
/-- **The innermost block** (`c = 0`): from the chain's `insFact &k X 𝟎` and `lenFact (bnum |x|) X`, a length object
for `s_{k−1}` and `leFact &0 (bnum |x|)`. -/
theorem foldBlock0_ok {tbl N W k c o x D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (hWp : W = proPieces)
    (hΓ : IsFormulaSet LAct Γ) (hkE : k + 3 ≤ E) (hXE : o + (k + 1) + c + 3 ≤ E) (hxD : formulaLen LAct x ≤ D)
    (hE : 18 * ‖D‖ + 7 ≤ E)
    (hins : neg LAct (insFact (^&k) (^&(o + (k + 1) + c)) (𝟎 : V)) ∈ Γ)
    (hln : neg LAct (lenFact (bnum (formulaLen LAct x)) (^&(o + (k + 1) + c))) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (foldBlock0 W k c o x) ∧ NoDrop' (foldBlock0 W k c o x) ∧
    shiftsV (foldBlock0 W k c o x) = 1 ∧ len (foldBlock0 W k c o x) = 2 ∧
    neg LAct (setLenFact (^&0) (^&(k + 1))) ∈ finalCtx Γ (foldBlock0 W k c o x) ∧
    neg LAct (leFact (^&0) (bnum (formulaLen LAct x))) ∈ finalCtx Γ (foldBlock0 W k c o x) := by
  subst hWp
  have hL := hP.layoutTable
  have e85 : ∀ ev : V, mkStep proPieces (85 : V) ev = mkStep layoutPieces (85 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 85 (by decide) ev; simpa using this
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hkE)
  have h0 : IsSemiterm LAct (0 : V) (𝟎 : V) := isSemiterm_qqZero_LAct 0
  -- step 1
  obtain ⟨ok₁, tg₁, cx₁⟩ := lok_setLenTotalC htbl hL rfl hΓ (by simp : IsSemiterm LAct 0 (^&k : V))
    (termLen_fvar_le' (le_trans (add_le_add le_rfl (by norm_num)) hkE))
  rw [← e85] at ok₁ tg₁ cx₁
  rw [Nat.cast_zero, termShift_fvar] at cx₁
  set Γ₁ := insert (neg LAct (setLenFact (^&0) (^&(k + 1)))) (setShift LAct Γ) with hΓ₁
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  -- the shifted facts
  have hins' : neg LAct (insFact (^&(k + 1)) (^&(o + (k + 1) + c + 1)) (𝟎 : V)) ∈ Γ₁ := by
    have := mem_shift_insert (f := neg LAct (setLenFact (^&0) (^&(k + 1)))) hins
    rwa [shift_neg (isFormula_insFact (by simp) (by simp) h0), shift_insFact (by simp) (by simp) h0,
      termShift_fvar, termShift_fvar, termShift_zeroV] at this
  have hln' : neg LAct (lenFact (bnum (formulaLen LAct x)) (^&(o + (k + 1) + c + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := neg LAct (setLenFact (^&0) (^&(k + 1)))) hln
    rwa [shift_neg (isFormula_lenFact (isSemiterm_bnum0 _) (by simp)), shift_lenFact (isSemiterm_bnum0 _) (by simp),
      termShift_bnum, termShift_fvar] at this
  have hsl₁ : neg LAct (setLenFact (^&0) (^&(k + 1))) ∈ Γ₁ := memInsSelf _ _
  -- step 2
  obtain ⟨hlen, hrow⟩ := hP.setLenSingLe
  have hX1 : o + (k + 1) + c + 1 + 1 ≤ E := by
    rw [add_assoc (o + (k + 1) + c) 1 1, one_add_one_eq_two]
    exact le_trans (add_le_add le_rfl (by norm_num)) hXE
  have hk2 : k + 1 + 1 ≤ E := by
    rw [add_assoc, one_add_one_eq_two]; exact le_trans (add_le_add le_rfl (by norm_num)) hkE
  have h01 : (0 : V) + 1 ≤ E := by rw [zero_add]; exact hE1
  have hX0 : IsSemiterm LAct 0 (^&(o + (k + 1) + c + 1) : V) := by simp
  have hk0 : IsSemiterm LAct 0 (^&(k + 1) : V) := by simp
  have h00 : IsSemiterm LAct 0 (^&0 : V) := by simp
  obtain ⟨ok₂, tg₂, cx₂⟩ := pok_setLenSingLe htbl rfl hlen ⟨hrow.1, hrow.2⟩ hΓ₁f
    hX0 (termLen_fvar_le' hX1) hk0 (termLen_fvar_le' hk2) h00 (termLen_fvar_le' h01)
    (isSemiterm_bnum0 _) (termLen_bnum_le_bkE hxD hE) hins' hsl₁ hln'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold foldBlock0
    exact listOK_cons ok₁ (by rw [cx₁]; exact listOK_single ok₂)
  · unfold foldBlock0
    exact noDrop'_cons (Or.inr (Or.inr (Or.inl tg₁))) (noDrop'_single (Or.inl tg₂))
  · unfold foldBlock0
    rw [shiftsV_cons_tag2 tg₁, shiftsV_single_tag0 tg₂, add_zero]
  · unfold foldBlock0; simp only [len_adjoin, len_nil]; norm_num
  · unfold foldBlock0
    rw [finalCtx_cons, cx₁, finalCtx_single, cx₂]
    exact memIns hsl₁
  · unfold foldBlock0
    rw [finalCtx_cons, cx₁, finalCtx_single, cx₂]
    exact memInsSelf _ _

set_option maxHeartbeats 2000000 in
/-- **A general block** (`c ≥ 1`): from the chain's `insFact &k X &(k+1)`, `lenFact (bnum |x|) X`, the previous
length object `setLenFact &0 &(k+1)` and its bound `leFact &0 (bnum L')`, a new length object and
`leFact &0 (bnum L)` (with `L' + |x| ≤ L`). -/
theorem foldBlockS_ok {tbl N N' B' W T k c o x L' L D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWp : W = proPieces)
    (hΓ : IsFormulaSet LAct Γ) (hkE : k + 3 ≤ E) (hXE : o + (k + 1) + c + 3 ≤ E) (hxD : formulaLen LAct x ≤ D)
    (hL'D : L' ≤ D) (hLD : L ≤ D) (hLL : L' + formulaLen LAct x ≤ L) (hE : 18 * ‖D‖ + 7 ≤ E)
    (hins : neg LAct (insFact (^&k) (^&(o + (k + 1) + c)) (^&(k + 1))) ∈ Γ)
    (hln : neg LAct (lenFact (bnum (formulaLen LAct x)) (^&(o + (k + 1) + c))) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&0) (^&(k + 1))) ∈ Γ)
    (hle : neg LAct (leFact (^&0) (bnum L')) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (foldBlockS W T k c o x L' L) ∧ NoDrop' (foldBlockS W T k c o x L' L) ∧
    shiftsV (foldBlockS W T k c o x L' L) = 1 ∧ len (foldBlockS W T k c o x L' L) = 6 ∧
    neg LAct (setLenFact (^&0) (^&(k + 1))) ∈ finalCtx Γ (foldBlockS W T k c o x L' L) ∧
    neg LAct (leFact (^&0) (bnum L)) ∈ finalCtx Γ (foldBlockS W T k c o x L' L) := by
  subst hWp
  have hL := hP.layoutTable
  have hF := hP.frag1Table
  have e85 : ∀ ev : V, mkStep proPieces (85 : V) ev = mkStep layoutPieces (85 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 85 (by decide) ev; simpa using this
  have e111 : ∀ ev : V, mkStep proPieces (111 : V) ev = mkStep frag1Pieces (111 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag1 111 (by decide) ev; simpa using this
  have e109 : ∀ ev : V, mkStep proPieces (109 : V) ev = mkStep frag1Pieces (109 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag1 109 (by decide) ev; simpa using this
  have e108 : ∀ ev : V, mkStep proPieces (108 : V) ev = mkStep frag1Pieces (108 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag1 108 (by decide) ev; simpa using this
  have e110 : ∀ ev : V, mkStep proPieces (110 : V) ev = mkStep frag1Pieces (110 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag1 110 (by decide) ev; simpa using this
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hkE)
  have hE2 : (2 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hkE)
  have hk1 : k + 2 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hkE
  have hk2 : k + 1 + 1 ≤ E := by rw [add_assoc, one_add_one_eq_two]; exact hk1
  have hk3 : k + 2 + 1 ≤ E := by rw [add_assoc, show (2 : V) + 1 = 3 by norm_num]; exact hkE
  have hbx : termLen LAct (bnum (formulaLen LAct x)) ≤ E := termLen_bnum_le_bkE hxD hE
  have hbL' : termLen LAct (bnum L') ≤ E := termLen_bnum_le_bkE hL'D hE
  have hbL : termLen LAct (bnum L) ≤ E := termLen_bnum_le_bkE hLD hE
  have hsum : IsSemiterm LAct 0 (bnum L' ^+ bnum (formulaLen LAct x)) :=
    isSemiterm_qqAdd_LAct (isSemiterm_bnum0 _) (isSemiterm_bnum0 _)
  have hsumE : termLen LAct (bnum L' ^+ bnum (formulaLen LAct x)) ≤ E := by
    refine le_trans (termLen_qqAdd_le (isSemiterm_bnum0 _).isUTerm (isSemiterm_bnum0 _).isUTerm
      (termLen_bnum_le_bk hL'D) (termLen_bnum_le_bk hxD)) ?_
    calc 6 * ‖D‖ + 1 + (6 * ‖D‖ + 1) + 1 = 12 * ‖D‖ + 3 := by ring
      _ ≤ 18 * ‖D‖ + 7 := add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num)
      _ ≤ E := hE
  -- step 1: the length object of `s_j`
  obtain ⟨ok₁, tg₁, cx₁⟩ := lok_setLenTotalC htbl hL rfl hΓ (by simp : IsSemiterm LAct 0 (^&k : V))
    (termLen_fvar_le' (le_trans (add_le_add le_rfl (by norm_num)) hkE))
  rw [← e85] at ok₁ tg₁ cx₁
  rw [Nat.cast_zero, termShift_fvar] at cx₁
  set Γ₁ := insert (neg LAct (setLenFact (^&0) (^&(k + 1)))) (setShift LAct Γ) with hΓ₁
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  have hins' : neg LAct (insFact (^&(k + 1)) (^&(o + (k + 1) + c + 1)) (^&(k + 2))) ∈ Γ₁ := by
    have := mem_shift_insert (f := neg LAct (setLenFact (^&0) (^&(k + 1)))) hins
    rwa [shift_neg (isFormula_insFact (by simp) (by simp) (by simp)), shift_insFact (by simp) (by simp) (by simp),
      termShift_fvar, termShift_fvar, termShift_fvar, add_assoc k 1 1, one_add_one_eq_two] at this
  have hln' : neg LAct (lenFact (bnum (formulaLen LAct x)) (^&(o + (k + 1) + c + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := neg LAct (setLenFact (^&0) (^&(k + 1)))) hln
    rwa [shift_neg (isFormula_lenFact (isSemiterm_bnum0 _) (by simp)), shift_lenFact (isSemiterm_bnum0 _) (by simp),
      termShift_bnum, termShift_fvar] at this
  have hsl' : neg LAct (setLenFact (^&1) (^&(k + 2))) ∈ Γ₁ := by
    have := mem_shift_insert (f := neg LAct (setLenFact (^&0) (^&(k + 1)))) hsl
    rwa [shift_neg (isFormula_setLenFact (by simp) (by simp)), shift_setLenFact (by simp) (by simp),
      termShift_fvar, termShift_fvar, zero_add, add_assoc k 1 1, one_add_one_eq_two] at this
  have hle' : neg LAct (leFact (^&1) (bnum L')) ∈ Γ₁ := by
    have := mem_shift_insert (f := neg LAct (setLenFact (^&0) (^&(k + 1)))) hle
    rwa [shift_neg (isFormula_leFact (by simp) (isSemiterm_bnum0 _)), shift_leFact (by simp) (isSemiterm_bnum0 _),
      termShift_fvar, termShift_bnum, zero_add] at this
  have hsl₁ : neg LAct (setLenFact (^&0) (^&(k + 1))) ∈ Γ₁ := memInsSelf _ _
  -- step 2: setLenInsertLe
  obtain ⟨ok₂, tg₂, cx₂⟩ := fok_setLenInsertLe htbl hF rfl hΓ₁f
    (by simp) (termLen_fvar_le' (le_trans (by rw [add_assoc, show (1 : V) + 1 = 2 by norm_num]; exact add_le_add le_rfl (by norm_num)) hXE))
    (by simp) (termLen_fvar_le' hk3) (by simp) (termLen_fvar_le' hk2)
    (by simp) (termLen_fvar_le' (le_trans (by norm_num) hE1)) (by simp) (termLen_fvar_le' (le_trans (by norm_num) hE2))
    (isSemiterm_bnum0 _) hbx hins' hsl₁ hsl' hln'
  rw [← e111] at ok₂ tg₂ cx₂
  set Γ₂ := insert (neg LAct (leFact (^&0) ((^&1 : V) ^+ bnum (formulaLen LAct x)))) Γ₁ with hΓ₂
  have hΓ₂f : IsFormulaSet LAct Γ₂ := by rw [← cx₂]; exact isFormulaSet_ctxAfter 8 htbl ok₂
  -- step 3: leRefl
  obtain ⟨ok₃, tg₃, cx₃⟩ := fok_leRefl htbl hF rfl hΓ₂f (isSemiterm_bnum0 (formulaLen LAct x)) hbx
  rw [← e109] at ok₃ tg₃ cx₃
  set Γ₃ := insert (neg LAct (leFact (bnum (formulaLen LAct x)) (bnum (formulaLen LAct x)))) Γ₂ with hΓ₃
  have hΓ₃f : IsFormulaSet LAct Γ₃ := by rw [← cx₃]; exact isFormulaSet_ctxAfter 8 htbl ok₃
  -- step 4: leAddLeAdd
  obtain ⟨ok₄, tg₄, cx₄⟩ := fok_leAddLeAdd htbl hF rfl hΓ₃f
    (by simp) (termLen_fvar_le' (le_trans (by norm_num) hE1)) (by simp) (termLen_fvar_le' (le_trans (by norm_num) hE2))
    (isSemiterm_bnum0 _) hbx (isSemiterm_bnum0 _) hbL' (isSemiterm_bnum0 _) hbx
    (memIns (memInsSelf _ _)) (memIns (memIns hle')) (memInsSelf _ _)
  rw [← e108] at ok₄ tg₄ cx₄
  set Γ₄ := insert (neg LAct (leFact (^&0) (bnum L' ^+ bnum (formulaLen LAct x)))) Γ₃ with hΓ₄
  have hΓ₄f : IsFormulaSet LAct Γ₄ := by rw [← cx₄]; exact isFormulaSet_ctxAfter 8 htbl ok₄
  -- step 5: the closed lemma
  have ok₅ : StepOK tbl E ((8 : ℕ) : V) Γ₄ (sLemma (sum2Fact L' (formulaLen LAct x) L) (sum2Code T L' (formulaLen LAct x) L)) :=
    stepOK_sLemma hΓ₄f (lemmaOK_sum2 htblN hLL)
  have cx₅ := ctxAfter_sLemma Γ₄ (sum2Fact L' (formulaLen LAct x) L) (sum2Code T L' (formulaLen LAct x) L)
  set Γ₅ := insert (neg LAct (sum2Fact L' (formulaLen LAct x) L)) Γ₄ with hΓ₅
  have hΓ₅f : IsFormulaSet LAct Γ₅ := by rw [← cx₅]; exact isFormulaSet_ctxAfter 8 htbl ok₅
  -- step 6: leTrans
  obtain ⟨ok₆, tg₆, cx₆⟩ := fok_leTrans htbl hF rfl hΓ₅f (isSemiterm_bnum0 _) hbL hsum hsumE
    (by simp) (termLen_fvar_le' (le_trans (by norm_num) hE1))
    (memIns (memInsSelf _ _)) (by show neg LAct (sum2Fact L' (formulaLen LAct x) L) ∈ Γ₅; exact memInsSelf _ _)
  rw [← e110] at ok₆ tg₆ cx₆
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold foldBlockS
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    refine listOK_cons ok₄ ?_
    rw [cx₄]
    refine listOK_cons ok₅ ?_
    rw [cx₅]
    exact listOK_single ok₆
  · unfold foldBlockS
    exact noDrop'_cons (Or.inr (Or.inr (Or.inl tg₁))) (noDrop'_cons (Or.inl tg₂) (noDrop'_cons (Or.inl tg₃)
      (noDrop'_cons (Or.inl tg₄) (noDrop'_cons (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp)))))))
        (noDrop'_single (Or.inl tg₆))))))
  · unfold foldBlockS
    rw [shiftsV_cons_tag2 tg₁, shiftsV_cons_tag0 tg₂, shiftsV_cons_tag0 tg₃, shiftsV_cons_tag0 tg₄,
      shiftsV_cons_sLemma, shiftsV_single_tag0 tg₆, add_zero]
  · unfold foldBlockS; simp only [len_adjoin, len_nil]; norm_num
  · unfold foldBlockS
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_cons, cx₄,
      finalCtx_cons, cx₅, finalCtx_single, cx₆]
    exact memIns (memIns (memIns (memIns (memIns hsl₁))))
  · unfold foldBlockS
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_cons, cx₄,
      finalCtx_cons, cx₅, finalCtx_single, cx₆]
    exact memInsSelf _ _

end foldOK

/-! ### 2.8 The fold is applicable -/

section foldInd

/-- What the chain leaves for the fold (frame right after the chain: `s_j = &(j+1)`, member `j` at
`&(o_j + (k+1))`). -/
def ChainOut (Γ xs os k : V) : Prop :=
  ∀ i < k, neg LAct (insFact (^&(i + 1)) (^&(os.[i] + (k + 1))) (prevAt (k + 1) (i + 1))) ∈ Γ ∧
    neg LAct (lenFact (bnum (formulaLen LAct xs.[i])) (^&(os.[i] + (k + 1)))) ∈ Γ

/-- The fold's invariant after `c` blocks, over the PACKED parameters `p = ⟪W, T, xs, os, k⟫` (5-ary, so
that `definability`'s composition rules — which stop at arity 5 — apply to induction motives). -/
def FOut (tbl E p Γ c : V) : Prop :=
  ListOK tbl E ((8 : ℕ) : V) Γ (lenFoldAuxP p c) ∧ NoDrop' (lenFoldAuxP p c) ∧
  shiftsV (lenFoldAuxP p c) = c ∧ len (lenFoldAuxP p c) ≤ 6 * c ∧
  (1 ≤ c → neg LAct (setLenFact (^&0) (^&(π₂ (π₂ (π₂ (π₂ p))) + 1))) ∈ finalCtx Γ (lenFoldAuxP p c) ∧
    neg LAct (leFact (^&0) (bnum (setLen LAct (psetAux (π₁ (π₂ (π₂ p))) c)))) ∈ finalCtx Γ (lenFoldAuxP p c))

set_option maxHeartbeats 1000000 in
instance fOut_definable : 𝚫₁-Relation₅ (FOut : V → V → V → V → V → Prop) := by
  unfold FOut; definability

/-- The invariant, read at an explicit parameter pack. -/
lemma fOut_iff (tbl E W T xs os k Γ c : V) : FOut tbl E ⟪W, T, xs, os, k⟫ Γ c ↔
    (ListOK tbl E ((8 : ℕ) : V) Γ (lenFoldAux W T xs os k c) ∧ NoDrop' (lenFoldAux W T xs os k c) ∧
    shiftsV (lenFoldAux W T xs os k c) = c ∧ len (lenFoldAux W T xs os k c) ≤ 6 * c ∧
    (1 ≤ c → neg LAct (setLenFact (^&0) (^&(k + 1))) ∈ finalCtx Γ (lenFoldAux W T xs os k c) ∧
      neg LAct (leFact (^&0) (bnum (setLen LAct (psetAux xs c)))) ∈ finalCtx Γ (lenFoldAux W T xs os k c))) := by
  simp only [FOut, lenFoldAux, pi₁_pair, pi₂_pair]

lemma le_thirteen_mul {D : V} : D ≤ 13 * D := le_mul_of_one_le_left zero_le (by norm_num)

set_option maxHeartbeats 2000000 in
/-- **The fold is applicable**, block by block (`xs = memberList s`, `k = len xs`, as VARIABLES: the induction
motive must apply `FOut` to variables). -/
theorem lenFoldAux_ok {tbl N N' B' W T s xs k os D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWp : W = proPieces)
    (hs : IsFormulaSet LAct s) (hxs : xs = memberList s) (hk : k = len xs) (hsD : setLen LAct s ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 8 ≤ E)
    (hos : len os = k) (hosD : ∀ i < k, os.[i] ≤ 4 * D)
    (hΓ : IsFormulaSet LAct Γ) (hCh : ChainOut Γ xs os k) :
    ∀ c ≤ k, FOut tbl E ⟪W, T, xs, os, k⟫ Γ c := by
  have hkD : k ≤ D := by rw [hk, hxs]; exact le_trans (len_memberList_le_setLen hs) hsD
  have hDE : 13 * D ≤ E := le_trans le_self_add (le_trans le_self_add hE)
  have hkE : k + 3 ≤ E :=
    le_trans (add_le_add (le_trans hkD le_thirteen_mul) (by norm_num)) (le_trans (add_le_add le_self_add le_rfl) hE)
  have hE' : 18 * ‖D‖ + 7 ≤ E := le_trans (add_le_add le_add_self (by norm_num)) hE
  intro c
  induction c using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    rw [fOut_iff]
    refine ⟨by rw [lenFoldAux_zero]; exact listOK_nil _ _ _ _, by rw [lenFoldAux_zero]; exact noDrop'_nil,
      by rw [lenFoldAux_zero, shiftsV_nil], by rw [lenFoldAux_zero]; simp,
      fun h ↦ absurd h (not_le.mpr _root_.zero_lt_one)⟩
  | succ c ih =>
    intro hc
    rw [fOut_iff] at ih ⊢
    obtain ⟨fok, fnd, fsh, flen, ffacts⟩ := ih (le_trans le_self_add hc)
    rw [lenFoldAux_succ]
    set L := lenFoldAux W T xs os k c with hL
    set Γc := finalCtx Γ L with hΓc
    have hΓcf : IsFormulaSet LAct Γc := finalCtx_isFormulaSet 8 htbl hΓ fok
    have hck : c < k := lt_of_lt_of_le (lt_add_one c) hc
    have hck' : c < len (memberList s) := by rw [← hxs, ← hk]; exact hck
    have hjk : k - (c + 1) < k := by
      have := sub_succ_lt_len hck'; rwa [← hxs, ← hk] at this
    have ej : k - (c + 1) + 1 + c = k := by
      rw [add_assoc, add_comm 1 c, tsub_add_cancel_of_le (lt_iff_succ_le.mp hck)]
    have hxj : nthFromEnd xs c = xs.[k - (c + 1)] := by
      have := nthFromEnd_memberList hck'; rwa [← hxs, ← hk] at this
    have hoj : nthFromEnd os c = os.[k - (c + 1)] :=
      nthFromEnd_eq (by rw [hos]; exact (tsub_add_cancel_of_le (lt_iff_succ_le.mp hck)).symm)
    obtain ⟨hins, hln⟩ := hCh (k - (c + 1)) hjk
    have hins' := mem_finalCtx_of_mem' fnd hins
    rw [fsh, shiftIterV_neg (isFormula_insFact (by simp) (by simp) (isSemiterm_prevAt _ _)),
      shiftIterV_insFact (by simp) (by simp) (isSemiterm_prevAt _ _), termShiftIterV_fvar, termShiftIterV_fvar,
      termShiftIterV_prevAt, ej] at hins'
    have hln' := mem_finalCtx_of_mem' fnd hln
    rw [fsh, shiftIterV_neg (isFormula_lenFact (isSemiterm_bnum0 _) (by simp)),
      shiftIterV_lenFact (isSemiterm_bnum0 _) (by simp), termShiftIterV_bnum', termShiftIterV_fvar] at hln'
    have hmem : xs.[k - (c + 1)] ∈ s := by
      have := nth_memberList_mem (s := s) (m := k - (c + 1)) (by rw [← hxs, ← hk]; exact hjk)
      rwa [← hxs] at this
    have hxD : formulaLen LAct xs.[k - (c + 1)] ≤ D := le_trans (formulaLen_le_setLen_of_mem hmem) hsD
    have hoD : os.[k - (c + 1)] ≤ 4 * D := hosD _ hjk
    have hcD : c ≤ D := le_trans (le_of_lt hck) hkD
    have hXE : os.[k - (c + 1)] + (k + 1) + c + 3 ≤ E := by
      calc os.[k - (c + 1)] + (k + 1) + c + 3 ≤ 4 * D + (D + 1) + D + 3 :=
            add_le_add (add_le_add (add_le_add hoD (add_le_add hkD le_rfl)) hcD) le_rfl
        _ = 6 * D + 4 := by ring
        _ ≤ 13 * D + 18 * ‖D‖ + 8 :=
            add_le_add (le_trans (mul_le_mul_of_nonneg_right (by norm_num) zero_le) le_self_add) (by norm_num)
        _ ≤ E := hE
    have hpsucc : setLen LAct (psetAux xs (c + 1)) = setLen LAct (psetAux xs c) + formulaLen LAct xs.[k - (c + 1)] := by
      have := setLen_psetAux_succ hck'; rw [← hxs] at this; rw [this, hxj]
    by_cases hc0 : c = 0
    · have hprev : prevAt (k + 1 + c) k = (𝟎 : V) := by unfold prevAt; rw [if_pos (by rw [hc0, add_zero])]
      rw [hprev] at hins'
      unfold foldBlock
      rw [if_pos hc0, hoj, hxj]
      obtain ⟨b0ok, b0nd, b0sh, b0len, b0sl, b0le⟩ := foldBlock0_ok htbl hP hWp hΓcf hkE hXE hxD hE' hins' hln'
      refine ⟨listOK_appendV fok b0ok, noDrop'_appendV fnd b0nd, by rw [shiftsV_appendV, fsh, b0sh], ?_, fun _ ↦ ?_⟩
      · rw [len_appendV, b0len]
        calc len L + 2 ≤ 6 * c + 2 := add_le_add flen le_rfl
          _ ≤ 6 * (c + 1) := by rw [mul_add, mul_one]; exact add_le_add le_rfl (by norm_num)
      · rw [finalCtx_appendV, ← hΓc]
        refine ⟨b0sl, ?_⟩
        have hz : setLen LAct (psetAux xs c) = 0 := by rw [hc0]; exact setLen_psetAux_zero xs
        rw [hpsucc, hz, zero_add]
        exact b0le
    · have hc1 : 1 ≤ c := by
        have : (0 : V) < c := pos_iff_ne_zero.mpr hc0
        rw [lt_iff_succ_le, zero_add] at this; exact this
      obtain ⟨fsl, fle⟩ := ffacts hc1
      have hprev : prevAt (k + 1 + c) k = ^&(k + 1) :=
        prevAt_of_lt (lt_add_of_pos_right _ (pos_iff_ne_zero.mpr hc0))
      rw [hprev] at hins'
      unfold foldBlock
      rw [if_neg hc0, hoj, hxj]
      have hL'D : setLen LAct (psetAux xs c) ≤ D := by
        have := setLen_psetAux_le (s := s) (c := c) (by rw [← hxs, ← hk]; exact le_of_lt hck)
        rw [← hxs] at this; exact le_trans this hsD
      have hLD : setLen LAct (psetAux xs (c + 1)) ≤ D := by
        have := setLen_psetAux_le (s := s) (c := c + 1) (by rw [← hxs, ← hk]; exact hc)
        rw [← hxs] at this; exact le_trans this hsD
      have hLL : setLen LAct (psetAux xs c) + formulaLen LAct xs.[k - (c + 1)] ≤ setLen LAct (psetAux xs (c + 1)) := by
        rw [hpsucc]
      obtain ⟨bok, bnd, bsh, blen, bsl, ble⟩ :=
        foldBlockS_ok htbl hP htblN hWp hΓcf hkE hXE hxD hL'D hLD hLL hE' hins' hln' fsl fle
      refine ⟨listOK_appendV fok bok, noDrop'_appendV fnd bnd, by rw [shiftsV_appendV, fsh, bsh],
        by rw [len_appendV, blen]; exact le_trans (add_le_add flen le_rfl) (le_of_eq (by ring)), fun _ ↦ ?_⟩
      rw [finalCtx_appendV, ← hΓc]
      exact ⟨bsl, ble⟩

end foldInd

/-! ### 2.9 The whole builder is applicable and produces the layout at offset `0` -/

section layoutStepsOK

set_option maxHeartbeats 2000000 in
/-- **`layoutSteps` is applicable and leaves the canonical layout of `s` at chain offset `0`.**
Hypotheses: a non-empty formula set `s` with `setLen s ≤ D`, the cap `13D + 18‖D‖ + 8 ≤ E`. Shifts:
`tailShift + (k + 1) + k`; length `≤ 26·setLen s + 13k + 6`. -/
theorem layoutSteps_ok {tbl N N' B' Wl Wc W T s D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hs : IsFormulaSet LAct s) (hk1 : 1 ≤ len (memberList s)) (hsD : setLen LAct s ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (layoutSteps walkPieces Wl Wc W T s) ∧ NoDrop' (layoutSteps walkPieces Wl Wc W T s) ∧
    shiftsV (layoutSteps walkPieces Wl Wc W T s) =
      tailShift (memberList s) walkPieces Wc T + (len (memberList s) + 1) + len (memberList s) ∧
    len (layoutSteps walkPieces Wl Wc W T s) ≤ 26 * setLen LAct s + 13 * len (memberList s) + 6 ∧
    Layout walkPieces Wc T (finalCtx Γ (layoutSteps walkPieces Wl Wc W T s)) s 0 := by
  have hW := hP.walkTable
  have hL := hP.layoutTable
  set k := len (memberList s) with hk
  set xs := memberList s with hxs
  have hkD : k ≤ D := le_trans (len_memberList_le_setLen hs) hsD
  have hE13 : 13 * D + 8 ≤ E := le_trans (add_le_add le_self_add le_rfl) hE
  have hmem : ∀ j < len xs, IsSemiformula LAct 0 xs.[j] ∧ formulaLen LAct xs.[j] ≤ D := fun j hj ↦
    ⟨hs _ (nth_memberList_mem hj), le_trans (formulaLen_le_setLen_of_mem (nth_memberList_mem hj)) hsD⟩
  -- the member blocks
  obtain ⟨mok, mnd, msh, mlen, mfacts⟩ := memberBlocks_ok htbl hP htblN hWc hE13 xs hmem Γ hΓ
  set Γ₂ := finalCtx Γ (memberBlocks xs walkPieces Wc T) with hΓ₂
  have hΓ₂f : IsFormulaSet LAct Γ₂ := finalCtx_isFormulaSet 8 htbl hΓ mok
  set os := offVec xs walkPieces Wc T with hos
  have hos_len : len os = k := by rw [hos, len_offVec]
  have hsetLen : listSum (flenVec xs) = setLen LAct s := (setLen_eq_listSum_memberList s).symm
  have hosD : ∀ i < k, os.[i] ≤ 4 * D := fun i hi ↦ by
    refine le_trans (nth_offVec_le _ _ _ xs i hi) ?_
    refine le_trans (tailShift_le htbl hW hWc T xs (fun j hj ↦ (hmem j hj).1)) ?_
    rw [hsetLen]; exact mul_le_mul_of_nonneg_left hsD zero_le
  -- the chain
  set ov := fvarVec os with hov
  have hov_len : len ov = k := by rw [hov, len_fvarVec, hos_len]
  have hkE : k + 2 ≤ E := le_trans (add_le_add (le_trans hkD le_thirteen_mul) (by norm_num)) hE13
  have hxs' : ∀ i < len ov, IsSemiterm LAct 0 ov.[i] ∧ termLen LAct (termShiftIterV ov.[i] (len ov + 1)) ≤ E ∧
      neg LAct (piFact (𝟎 : V) ov.[i]) ∈ Γ₂ := fun i hi ↦ by
    rw [hov_len] at hi ⊢
    rw [hov, nth_fvarVec os i (hos_len ▸ hi), termShiftIterV_fvar, termLen_fvar]
    refine ⟨by simp, ?_, (mfacts i hi).2.1⟩
    calc os.[i] + (k + 1) + 1 ≤ 4 * D + (D + 1) + 1 := add_le_add (add_le_add (hosD i hi) (add_le_add hkD le_rfl)) le_rfl
      _ = 5 * D + 2 := by ring
      _ ≤ 13 * D + 8 := add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num)
      _ ≤ E := hE13
  obtain ⟨cok, cnd, cho, csh, clen, cfacts, csl⟩ :=
    chainSteps_ok htbl hL hWl hΓ₂f (by rw [hov_len]; exact hk1) (by rw [hov_len]; exact hkE) hxs'
  rw [hov_len] at csh clen cfacts
  set Γ₃ := finalCtx Γ₂ (chainSteps Wl ov) with hΓ₃
  have hΓ₃f : IsFormulaSet LAct Γ₃ := finalCtx_isFormulaSet 8 htbl hΓ₂f cok
  -- the member facts after the chain
  have mfacts₃ : ∀ j < k, DossF walkPieces Γ₃ 0 xs.[j] (os.[j] + (k + 1)) ∧
      neg LAct (piFact (𝟎 : V) (^&(os.[j] + (k + 1)))) ∈ Γ₃ ∧
      neg LAct (lenFact (bnum (formulaLen LAct xs.[j])) (^&(os.[j] + (k + 1)))) ∈ Γ₃ := fun j hj ↦ by
    obtain ⟨hD, hpi, hln⟩ := mfacts j hj
    refine ⟨?_, ?_, ?_⟩
    · have := dossF_transport cnd hD; rwa [csh] at this
    · have := mem_finalCtx_of_mem cnd hpi
      rwa [csh, shiftIterV_neg (isFormula_piFact (isSemiterm_qqZero_LAct 0) (by simp)),
        shiftIterV_piFact (isSemiterm_qqZero_LAct 0) (by simp), termShiftIterV_zeroV, termShiftIterV_fvar] at this
    · have := mem_finalCtx_of_mem cnd hln
      rwa [csh, shiftIterV_neg (isFormula_lenFact (isSemiterm_bnum0 _) (by simp)),
        shiftIterV_lenFact (isSemiterm_bnum0 _) (by simp), termShiftIterV_bnum', termShiftIterV_fvar] at this
  have hCh : ChainOut Γ₃ xs os k := fun i hi ↦ by
    obtain ⟨hins, _, _⟩ := cfacts i hi
    rw [hov, nth_fvarVec os i (hos_len ▸ hi), termShiftIterV_fvar] at hins
    exact ⟨hins, (mfacts₃ i hi).2.2⟩
  -- the fold
  obtain ⟨fok, fnd, fsh, flen, ffacts⟩ :=
    (fOut_iff _ _ _ _ _ _ _ _ _).mp (lenFoldAux_ok htbl hP htblN hWp hs hxs hk hsD hE hos_len hosD hΓ₃f hCh k le_rfl)
  obtain ⟨fsl, fle⟩ := ffacts hk1
  have hfold : lenFold W T xs os = lenFoldAux W T xs os k k := by rw [lenFold, ← hk]
  -- assembly
  have hlist : layoutSteps walkPieces Wl Wc W T s =
      appendV (memberBlocks xs walkPieces Wc T) (appendV (chainSteps Wl ov) (lenFoldAux W T xs os k k)) := by
    rw [layoutSteps, ← hxs, ← hos, ← hov, hfold]
  rw [hlist]
  refine ⟨listOK_appendV mok (by rw [← hΓ₂]; exact listOK_appendV cok (by rw [← hΓ₃]; exact fok)),
    noDrop'_appendV mnd (noDrop'_appendV cnd.noDrop' fnd), ?_, ?_, ?_⟩
  · rw [shiftsV_appendV, shiftsV_appendV, msh, csh, fsh]; ring
  · rw [len_appendV, len_appendV]
    calc len (memberBlocks xs walkPieces Wc T) + (len (chainSteps Wl ov) + len (lenFoldAux W T xs os k k))
        ≤ 26 * listSum (flenVec xs) + ((7 * k + 6) + 6 * k) := add_le_add mlen (add_le_add clen flen)
      _ = 26 * setLen LAct s + 13 * k + 6 := by rw [hsetLen]; ring
  · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₂, ← hΓ₃]
    set Γ₄ := finalCtx Γ₃ (lenFoldAux W T xs os k k) with hΓ₄
    refine ⟨fun j hj ↦ ?_, ?_, ?_⟩
    · obtain ⟨hD, hpi, hln⟩ := mfacts₃ j hj
      obtain ⟨hins, hfs, hm⟩ := cfacts j hj
      rw [hov, nth_fvarVec os j (hos_len ▸ hj), termShiftIterV_fvar] at hins hm
      have e1 : os.[j] + (k + 1) + k = mTop 0 k os.[j] := by unfold mTop; ring
      have e2 : j + 1 + k = 0 + (k + 1 + j) := by ring
      have e3 : (1 : V) + k = 0 + (k + 1) := by ring
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have := dossF_transport' fnd hD; rwa [fsh, e1] at this
      · have := mem_finalCtx_of_mem' fnd hpi
        rwa [fsh, shiftIterV_neg (isFormula_piFact (isSemiterm_qqZero_LAct 0) (by simp)),
          shiftIterV_piFact (isSemiterm_qqZero_LAct 0) (by simp), termShiftIterV_zeroV, termShiftIterV_fvar, e1] at this
      · have := mem_finalCtx_of_mem' fnd hln
        rwa [fsh, shiftIterV_neg (isFormula_lenFact (isSemiterm_bnum0 _) (by simp)),
          shiftIterV_lenFact (isSemiterm_bnum0 _) (by simp), termShiftIterV_bnum', termShiftIterV_fvar, e1] at this
      · have := mem_finalCtx_of_mem' fnd hins
        rw [fsh, shiftIterV_neg (isFormula_insFact (by simp) (by simp) (isSemiterm_prevAt _ _)),
          shiftIterV_insFact (by simp) (by simp) (isSemiterm_prevAt _ _), termShiftIterV_fvar, termShiftIterV_fvar,
          termShiftIterV_prevAt, e1, e2] at this
        unfold prevI
        have e4 : k + 1 + k = 0 + (2 * k + 1) := by ring
        rwa [e4] at this
      · have := mem_finalCtx_of_mem' fnd hfs
        rwa [fsh, shiftIterV_neg (isFormula_fsetPiFact (by simp)), shiftIterV_fsetPiFact (by simp),
          termShiftIterV_fvar, e2] at this
      · have := mem_finalCtx_of_mem' fnd hm
        rwa [fsh, shiftIterV_neg (isFormula_memFact (by simp) (by simp)), shiftIterV_memFact (by simp) (by simp),
          termShiftIterV_fvar, termShiftIterV_fvar, e1, e3] at this
    · rw [zero_add]; exact fsl
    · have e := psetAux_len_eq s
      rw [← hxs, ← hk] at e
      rw [e] at fle; exact fle

end layoutStepsOK

/-! ## 3. The leaves: `axL` and `verumIntro` (`DESIGN_fragments.md` §4.1–§4.2)

The member `p` and its negation `neg p` are both members of `s`, so both have WALK dossiers in the layout;
`certNeg` between the two dossiers (re-indexed to the prologue table) derives `negFact X_np X_p` — no
identification walk is needed. `verumIntro` needs no prologue at all: `verumFact X_⊤` is the top fact of
the member's dossier. -/

section leaves

/-! ### 3.1 The index of a member -/

namespace IdxAux

noncomputable def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y xs t. y = 0”
  succ := .mkSigma “y ih m xs t. ∃ e, !nthDef e xs m ∧ (e = t → y = m) ∧ (e ≠ t → y = ih)”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 0
  succ := fun v m ih ↦ if (v 0).[m] = v 1 then m else ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by
    simp [blueprint]
    by_cases h : (v 3).[v 2] = v 4
    · simp [h]
    · simp [h]

end IdxAux

/-- `idxAux xs t m` — the last index `< m` at which `xs` holds `t` (`0` if none). -/
noncomputable def idxAux (xs t m : V) : V := IdxAux.construction.result ![xs, t] m
/-- `idxOf xs t` — the index of `t` in `xs` (for a member of a duplicate-free list). -/
noncomputable def idxOf (xs t : V) : V := idxAux xs t (len xs)

@[simp] lemma idxAux_zero (xs t : V) : idxAux xs t 0 = 0 := by simp [idxAux, IdxAux.construction]
lemma idxAux_succ (xs t m : V) : idxAux xs t (m + 1) = if xs.[m] = t then m else idxAux xs t m := by
  simp [idxAux, IdxAux.construction]

noncomputable def idxAuxDef : 𝚺₁.Semisentence 4 := IdxAux.blueprint.resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])

instance idxAux_defined : 𝚺₁-Function₃ (idxAux : V → V → V → V) via idxAuxDef := .mk
  fun v ↦ by simp [IdxAux.construction.result_defined_iff, idxAuxDef]; rfl
instance idxAux_definable : 𝚺₁-Function₃ (idxAux : V → V → V → V) := idxAux_defined.to_definable

noncomputable def idxOfDef : 𝚺₁.Semisentence 3 := .mkSigma “y xs t. ∃ n, !lenDef n xs ∧ !idxAuxDef y xs t n”

instance idxOf_defined : 𝚺₁-Function₂ (idxOf : V → V → V) via idxOfDef := .mk fun v ↦ by
  simp [idxOfDef, idxOf, idxAux_defined.iff]
instance idxOf_definable : 𝚺₁-Function₂ (idxOf : V → V → V) := idxOf_defined.to_definable

lemma idxAux_spec (xs t : V) : ∀ m, (∃ j < m, xs.[j] = t) → idxAux xs t m < m ∧ xs.[idxAux xs t m] = t := by
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => rintro ⟨j, hj, _⟩; exact absurd hj (by simp)
  | succ m ih =>
    rintro ⟨j, hj, hjt⟩
    rw [idxAux_succ]
    by_cases h : xs.[m] = t
    · rw [if_pos h]; exact ⟨lt_add_one m, h⟩
    · rw [if_neg h]
      have hjm : j < m := lt_of_le_of_ne (lt_succ_iff_le.mp hj) (fun e ↦ h (e ▸ hjt))
      obtain ⟨h1, h2⟩ := ih ⟨j, hjm, hjt⟩
      exact ⟨lt_trans h1 (lt_add_one m), h2⟩

/-- A member's index is in range and reads the member. -/
lemma idxOf_spec {s y : V} (hy : y ∈ s) :
    idxOf (memberList s) y < len (memberList s) ∧ (memberList s).[idxOf (memberList s) y] = y :=
  idxAux_spec _ _ _ (mem_memberList_iff.mpr hy)

/-! ### 3.2 `proAxL` -/

/-- The index of the top of the member `y` of `s` in the layout at chain offset `i`. -/
noncomputable def memTop (Ww Wc T s y i : V) : V :=
  mTop i (len (memberList s)) (offVec (memberList s) Ww Wc T).[idxOf (memberList s) y]

/-- **The `axL` prologue**: `certNeg` from `p`'s dossier to `neg p`'s dossier, re-indexed. -/
noncomputable def proAxL (Ww Wc T s p i : V) : V :=
  reidxL (certNeg Wc 0 p (memTop Ww Wc T s p i) (memTop Ww Wc T s (neg LAct p) i))

noncomputable def proAxLDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y Ww Wc T s p i. ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧ ∃ os, !offVecDef os xs Ww Wc T ∧
    ∃ a, !idxOfDef a xs p ∧ ∃ oa, !nthDef oa os a ∧ ∃ np, !(negGraph LAct) np p ∧ ∃ b, !idxOfDef b xs np ∧
    ∃ ob, !nthDef ob os b ∧ ∃ ta, ta = i + (2 * k + 1 + oa) ∧ ∃ tb, tb = i + (2 * k + 1 + ob) ∧
    ∃ c, !passFDef c Wc 1 0 p ta tb ∧ !reidxLDef y c”

instance proAxL_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ proAxL (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) proAxLDef := .mk
  fun v ↦ by
    simp [proAxLDef, proAxL, memTop, mTop, certNeg, memberList_defined.iff, offVec_defined.iff, idxOf_defined.iff,
      neg.defined.iff, passF_defined.iff, reidxL_defined.iff, numeral_eq_natCast]

/-- The member facts of the layout, read at a member `y ∈ s`. -/
lemma Layout.member {Ww Wc T Γ s i y : V} (h : Layout Ww Wc T Γ s i) (hy : y ∈ s) :
    DossF Ww Γ 0 y (memTop Ww Wc T s y i) ∧
    neg LAct (piFact (𝟎 : V) (^&(memTop Ww Wc T s y i))) ∈ Γ ∧
    neg LAct (lenFact (bnum (formulaLen LAct y)) (^&(memTop Ww Wc T s y i))) ∈ Γ ∧
    neg LAct (memFact (^&(memTop Ww Wc T s y i)) (^&(i + (len (memberList s) + 1)))) ∈ Γ := by
  obtain ⟨hlt, heq⟩ := idxOf_spec hy
  obtain ⟨hD, hpi, hln, _, _, hm⟩ := h.1 _ hlt
  rw [heq] at hD hln
  exact ⟨hD, hpi, hln, hm⟩

/-- The sequent's formula-set fact (prefix `0` of the chain). -/
lemma Layout.fsetPi {Ww Wc T Γ s i : V} (h : Layout Ww Wc T Γ s i) (hk : 1 ≤ len (memberList s)) :
    neg LAct (fsetPiFact (^&(i + (len (memberList s) + 1)))) ∈ Γ := by
  have := (h.1 0 (lt_of_lt_of_le _root_.zero_lt_one hk)).2.2.2.2.1
  rwa [add_zero] at this

lemma memTop_le {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {Wc : V} (hWc : Wc = certPieces) (T : V)
    {s y i D : V} (hs : IsFormulaSet LAct s) (hy : y ∈ s) (hsD : setLen LAct s ≤ D) :
    memTop walkPieces Wc T s y i ≤ i + 6 * D + 1 := by
  obtain ⟨hlt, _⟩ := idxOf_spec hy
  have hkD : len (memberList s) ≤ D := le_trans (len_memberList_le_setLen hs) hsD
  have ho : (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) y] ≤ 4 * D := by
    refine le_trans (nth_offVec_le _ _ _ _ _ hlt) ?_
    refine le_trans (tailShift_le htbl hW hWc T _ (fun j hj ↦ hs _ (nth_memberList_mem hj))) ?_
    rw [← setLen_eq_listSum_memberList]; exact mul_le_mul_of_nonneg_left hsD zero_le
  unfold memTop mTop
  calc i + (2 * len (memberList s) + 1 + (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) y])
      ≤ i + (2 * D + 1 + 4 * D) := add_le_add le_rfl (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hkD zero_le) le_rfl) ho)
    _ = i + 6 * D + 1 := by ring

set_option maxHeartbeats 1000000 in
/-- **The `axL` prologue is applicable** and leaves `negFact X_np X_p`; together with the layout it discharges
EVERY hypothesis of `fragAxL_ok` at `is = i + (k + 1)`, `il = i`, `ip = memTop s p i`, `inp = memTop s (neg p) i`,
`L = setLen s` (the facts are listed in `fragAxL_ok`'s order). -/
theorem proAxL_ok {tbl N N' B' Wc T s p D E Γ i : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWc : Wc = certPieces)
    (hs : IsFormulaSet LAct s) (hp : p ∈ s) (hnp : neg LAct p ∈ s) (hsD : setLen LAct s ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 8 ≤ E) (hiE : i + 8 * D + 3 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hLay : Layout walkPieces Wc T Γ s i) :
    ListOK tbl E ((8 : ℕ) : V) Γ (proAxL walkPieces Wc T s p i) ∧ NoDrop (proAxL walkPieces Wc T s p i) ∧
    HornOnly (proAxL walkPieces Wc T s p i) ∧ shiftsV (proAxL walkPieces Wc T s p i) = 0 ∧
    len (proAxL walkPieces Wc T s p i) + 4 ≤ 12 * formulaLen LAct p ∧
    (neg LAct (fsetPiFact (^&(i + (len (memberList s) + 1)))) ∈ finalCtx Γ (proAxL walkPieces Wc T s p i) ∧
     neg LAct (memFact (^&(memTop walkPieces Wc T s p i)) (^&(i + (len (memberList s) + 1)))) ∈
       finalCtx Γ (proAxL walkPieces Wc T s p i) ∧
     neg LAct (negFact (^&(memTop walkPieces Wc T s (neg LAct p) i)) (^&(memTop walkPieces Wc T s p i))) ∈
       finalCtx Γ (proAxL walkPieces Wc T s p i) ∧
     neg LAct (memFact (^&(memTop walkPieces Wc T s (neg LAct p) i)) (^&(i + (len (memberList s) + 1)))) ∈
       finalCtx Γ (proAxL walkPieces Wc T s p i) ∧
     neg LAct (setLenFact (^&i) (^&(i + (len (memberList s) + 1)))) ∈ finalCtx Γ (proAxL walkPieces Wc T s p i) ∧
     neg LAct (leFact (^&i) (bnum (setLen LAct s))) ∈ finalCtx Γ (proAxL walkPieces Wc T s p i)) := by
  have hW := hP.walkTable
  have hC := hP.certTable
  have htblC := hP.tableOK_certView htbl
  have hpf : IsSemiformula LAct 0 p := hs p hp
  have hpD : formulaLen LAct p ≤ D := le_trans (formulaLen_le_setLen_of_mem hp) hsD
  have hk1 : 1 ≤ len (memberList s) := by
    obtain ⟨hlt, _⟩ := idxOf_spec hp
    have := lt_iff_succ_le.mp (lt_of_le_of_lt zero_le hlt); rwa [zero_add] at this
  obtain ⟨hDp, _, _, hmp⟩ := hLay.member hp
  obtain ⟨hDnp, _, _, hmnp⟩ := hLay.member hnp
  have h2D : 2 * formulaLen LAct p ≤ 2 * D := mul_le_mul_of_nonneg_left hpD zero_le
  have hE1 : 2 * (0 : V) + 2 * formulaLen LAct p + 8 ≤ E := by
    rw [mul_zero, zero_add]
    exact le_trans (add_le_add (le_trans h2D (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) le_rfl)
      (le_trans (add_le_add le_self_add le_rfl) hE)
  have htop : ∀ y ∈ s, memTop walkPieces Wc T s y i + 2 * formulaLen LAct p + 1 ≤ E := fun y hy ↦ by
    calc memTop walkPieces Wc T s y i + 2 * formulaLen LAct p + 1 ≤ (i + 6 * D + 1) + 2 * D + 1 :=
          add_le_add (add_le_add (memTop_le htbl hW hWc T hs hy hsD) h2D) le_rfl
      _ = i + 8 * D + 2 := by ring
      _ ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hiE
  obtain ⟨cok, cnd, cho, csh, cfact⟩ :=
    certNeg_ok htblC hC rfl hWc hpf hE1 (htop p hp) (htop _ hnp) hΓ hDp hDnp
  have tr : ∀ x ∈ Γ, x ∈ finalCtx Γ (proAxL walkPieces Wc T s p i) := fun x hx ↦ by
    unfold proAxL; rw [finalCtx_reidxL]
    have := mem_finalCtx_of_mem cnd hx; rwa [csh, shiftIterV_zero] at this
  refine ⟨listOK_reidxL hP cok, noDrop_reidxL cnd, hornOnly_reidxL cho, by unfold proAxL; rw [shiftsV_reidxL, csh],
    by unfold proAxL; rw [len_reidxL]; exact len_certNeg_le hpf, tr _ (hLay.fsetPi hk1), tr _ hmp, ?_, tr _ hmnp,
    tr _ hLay.2.1, tr _ hLay.2.2⟩
  unfold proAxL; rw [finalCtx_reidxL]; exact cfact

/-! ### 3.3 `verumIntro`: no steps — the layout already discharges every hypothesis of `fragVerum_ok` -/

/-- With `⊤ ∈ s`, the layout at offset `i` discharges `fragVerum_ok`'s hypotheses at `is = i + (k + 1)`, `il = i`,
`iv = memTop s ⊤ i`, `L = setLen s`. -/
theorem layout_verum {tbl N Wc T s Γ i : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (hv : (^⊤ : V) ∈ s) (hLay : Layout walkPieces Wc T Γ s i) :
    neg LAct (fsetPiFact (^&(i + (len (memberList s) + 1)))) ∈ Γ ∧
    neg LAct (verumFact (^&(memTop walkPieces Wc T s ^⊤ i))) ∈ Γ ∧
    neg LAct (memFact (^&(memTop walkPieces Wc T s ^⊤ i)) (^&(i + (len (memberList s) + 1)))) ∈ Γ ∧
    neg LAct (setLenFact (^&i) (^&(i + (len (memberList s) + 1)))) ∈ Γ ∧
    neg LAct (leFact (^&i) (bnum (setLen LAct s))) ∈ Γ := by
  have hk1 : 1 ≤ len (memberList s) := by
    obtain ⟨hlt, _⟩ := idxOf_spec hv
    have := lt_iff_succ_le.mp (lt_of_le_of_lt zero_le hlt); rwa [zero_add] at this
  obtain ⟨hD, _, _, hm⟩ := hLay.member hv
  exact ⟨hLay.fsetPi hk1, (dossF_verum htbl hP.walkTable rfl hD).1, hm, hLay.2.1, hLay.2.2⟩

end leaves

/-! ## 4. Identification of an `insert` object with a chain (`DESIGN_fragments.md` §3.4)

The child's sequent object the `Intro` rows need is a fresh `insertTotalC` object `cp = insert p s`; the child's
own layout is the CHAIN `s''` over the sorted members of `insert p s`. `eqFactB cp s''` is derived by
`subsetAntisymm` from `s'' ⊆ cp` (every member of the chain is in `cp`, folded by `insertSubset` along the
child's chain) and `cp ⊆ s''` (the parent's chain folded the same way, then one more `insertSubset` for `p`);
the per-member facts come from `eqSteps` between the two walk dossiers of the same code. -/

section identify

/-! ### 4.1 Counting a chain down without subtraction in a blueprint -/

/-- `jOf k c = k − (c + 1)` when `c + 1 ≤ k` (else `0`): the member index of the `c`-th link from the inside. -/
noncomputable def jOf (k c : V) : V := if c + 1 ≤ k then k - (c + 1) else 0

noncomputable def jOfDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y k c. (c + 1 ≤ k → y + (c + 1) = k) ∧ (¬ c + 1 ≤ k → y = 0)”

instance jOf_defined : 𝚺₁-Function₂ (jOf : V → V → V) via jOfDef := .mk fun v ↦ by
  simp [jOfDef, jOf]
  by_cases h : v 2 + 1 ≤ v 1
  · have h' : ¬ v 1 < v 2 + 1 := not_lt.mpr h
    simp [h, h']
    constructor
    · intro e; exact eq_tsub_of_add_eq e
    · intro e; rw [e]; exact tsub_add_cancel_of_le h
  · have h' : v 1 < v 2 + 1 := not_le.mp h
    simp [h, h']
instance jOf_definable : 𝚺₁-Function₂ (jOf : V → V → V) := jOf_defined.to_definable

lemma jOf_of_le {k c : V} (h : c + 1 ≤ k) : jOf k c = k - (c + 1) := by unfold jOf; rw [if_pos h]

lemma jOf_add {k c : V} (h : c + 1 ≤ k) : jOf k c + (c + 1) = k := by
  rw [jOf_of_le h]; exact tsub_add_cancel_of_le h

/-! ### 4.2 The links and the fold -/

/-- Link `c` (member `j = jOf k' c`): `insertSubset [s_{j+1}, X_j, A, s_j]` in the layout frame at chain offset
`i'` with `k'` members and offsets `os`. -/
noncomputable def subLink (W i' k' os A c : V) : V :=
  mkStep W 112 ?[prevI i' k' (jOf k' c), A, ^&(mTop i' k' (nthFromEnd os c)), ^&(i' + (k' + 1 + jOf k' c))]

noncomputable def subLinkDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y W i k os A c. ∃ j, !jOfDef j k c ∧ ∃ a, a = i + (2 * k + 1) ∧ ∃ b, b = i + (k + 1 + j) ∧ ∃ pv, !prevAtDef pv a b ∧
    ∃ o, !nthFromEndDef o os c ∧ ∃ t, t = i + (2 * k + 1 + o) ∧ ∃ zt, !qqFvarDef zt t ∧ ∃ zs, !qqFvarDef zs b ∧
    ∃ e₁, !adjoinDef e₁ zs 0 ∧ ∃ e₂, !adjoinDef e₂ zt e₁ ∧ ∃ e₃, !adjoinDef e₃ A e₂ ∧ ∃ e₄, !adjoinDef e₄ pv e₃ ∧
    !mkStepDef y W 112 e₄”

instance subLink_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ subLink (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) subLinkDef := .mk
  fun v ↦ by
    simp [subLinkDef, subLink, prevI, mTop, jOf_defined.iff, prevAt_defined.iff, nthFromEnd_defined.iff,
      mkStep_defined.iff, numeral_eq_natCast]

namespace SubChain

/-- Packed parameters `p = ⟪W, i', k', os, A⟫`. -/
noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y p. ∃ W, !pi₁Def W p ∧ ∃ q₁, !pi₂Def q₁ p ∧ ∃ q₂, !pi₂Def q₂ q₁ ∧ ∃ q₃, !pi₂Def q₃ q₂ ∧
    ∃ A, !pi₂Def A q₃ ∧ ∃ e, !adjoinDef e A 0 ∧ ∃ s, !mkStepDef s W 81 e ∧ !adjoinDef y s 0”
  succ := .mkSigma “y ih c p. ∃ W, !pi₁Def W p ∧ ∃ q₁, !pi₂Def q₁ p ∧ ∃ i, !pi₁Def i q₁ ∧ ∃ q₂, !pi₂Def q₂ q₁ ∧
    ∃ k, !pi₁Def k q₂ ∧ ∃ q₃, !pi₂Def q₃ q₂ ∧ ∃ os, !pi₁Def os q₃ ∧ ∃ A, !pi₂Def A q₃ ∧
    ∃ l, !subLinkDef l W i k os A c ∧ ∃ e, !adjoinDef e l 0 ∧ !appendVDef y ih e”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun v ↦ ?[mkStep (π₁ (v 0)) 81 ?[π₂ (π₂ (π₂ (π₂ (v 0))))]]
  succ := fun v c ih ↦ appendV ih ?[subLink (π₁ (v 0)) (π₁ (π₂ (v 0))) (π₁ (π₂ (π₂ (v 0))))
    (π₁ (π₂ (π₂ (π₂ (v 0))))) (π₂ (π₂ (π₂ (π₂ (v 0))))) c]
  zero_defined := .mk fun v ↦ by simp [blueprint, mkStep_defined.iff, numeral_eq_natCast]
  succ_defined := .mk fun v ↦ by simp [blueprint, subLink_defined.iff, appendV_defined.iff]

end SubChain

noncomputable def subChainAux (p c : V) : V := SubChain.construction.result ![p] c

noncomputable def subChainAuxDef : 𝚺₁.Semisentence 3 :=
  SubChain.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance subChainAux_defined : 𝚺₁-Function₂ (subChainAux : V → V → V) via subChainAuxDef := .mk
  fun v ↦ by simp [SubChain.construction.result_defined_iff, subChainAuxDef]; rfl
instance subChainAux_definable : 𝚺₁-Function₂ (subChainAux : V → V → V) := subChainAux_defined.to_definable

lemma subChainAux_zero (W i' k' os A : V) : subChainAux ⟪W, i', k', os, A⟫ 0 = ?[mkStep W 81 ?[A]] := by
  simp [subChainAux, SubChain.construction]
lemma subChainAux_succ (W i' k' os A c : V) :
    subChainAux ⟪W, i', k', os, A⟫ (c + 1) = appendV (subChainAux ⟪W, i', k', os, A⟫ c) ?[subLink W i' k' os A c] := by
  simp [subChainAux, SubChain.construction]

/-- **`subChain W i' k' os A`** — `subsetFact s A` for the chain `s` laid out at offset `i'` (`k'` members, offsets
`os`), from `memFact X_j A` for every member. -/
noncomputable def subChain (W i' k' os A : V) : V := subChainAux ⟪W, i', k', os, A⟫ k'

noncomputable def subChainDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y W i k os A. ∃ q₃, !pairDef q₃ os A ∧ ∃ q₂, !pairDef q₂ k q₃ ∧ ∃ q₁, !pairDef q₁ i q₂ ∧ ∃ p, !pairDef p W q₁ ∧
    !subChainAuxDef y p k”

instance subChain_defined : 𝚺₁-Function₅ (subChain : V → V → V → V → V → V) via subChainDef := .mk
  fun v ↦ by simp [subChainDef, subChain, subChainAux_defined.iff]

/-! ### 4.3 The fold is applicable -/

/-- The fold's invariant after `c` links: the derived subset fact is about `𝟎` (`c = 0`) or `s_{jOf k' (c−1)}`. -/
def SOut (tbl E p Γ c : V) : Prop :=
  ListOK tbl E ((8 : ℕ) : V) Γ (subChainAux p c) ∧ NoDrop (subChainAux p c) ∧ HornOnly (subChainAux p c) ∧
  shiftsV (subChainAux p c) = 0 ∧ len (subChainAux p c) = c + 1 ∧
  (c = 0 → neg LAct (subsetFact (𝟎 : V) (π₂ (π₂ (π₂ (π₂ p))))) ∈ finalCtx Γ (subChainAux p c)) ∧
  (1 ≤ c → neg LAct (subsetFact (^&(π₁ (π₂ p) + (π₁ (π₂ (π₂ p)) + 1 + jOf (π₁ (π₂ (π₂ p))) (c - 1))))
    (π₂ (π₂ (π₂ (π₂ p))))) ∈ finalCtx Γ (subChainAux p c))

set_option maxHeartbeats 1000000 in
instance sOut_definable : 𝚫₁-Relation₅ (SOut : V → V → V → V → V → Prop) := by
  unfold SOut; definability

lemma sOut_iff (tbl E W i' k' os A Γ c : V) : SOut tbl E ⟪W, i', k', os, A⟫ Γ c ↔
    (ListOK tbl E ((8 : ℕ) : V) Γ (subChainAux ⟪W, i', k', os, A⟫ c) ∧ NoDrop (subChainAux ⟪W, i', k', os, A⟫ c) ∧
    HornOnly (subChainAux ⟪W, i', k', os, A⟫ c) ∧ shiftsV (subChainAux ⟪W, i', k', os, A⟫ c) = 0 ∧
    len (subChainAux ⟪W, i', k', os, A⟫ c) = c + 1 ∧
    (c = 0 → neg LAct (subsetFact (𝟎 : V) A) ∈ finalCtx Γ (subChainAux ⟪W, i', k', os, A⟫ c)) ∧
    (1 ≤ c → neg LAct (subsetFact (^&(i' + (k' + 1 + jOf k' (c - 1)))) A) ∈ finalCtx Γ (subChainAux ⟪W, i', k', os, A⟫ c))) := by
  simp only [SOut, pi₁_pair, pi₂_pair]

/-- The chain facts a `subChain` reads: the insert facts of the layout frame and the member facts against `A`. -/
def SubIn (Γ i' k' os A : V) : Prop :=
  ∀ j < k', neg LAct (insFact (^&(i' + (k' + 1 + j))) (^&(mTop i' k' os.[j])) (prevI i' k' j)) ∈ Γ ∧
    neg LAct (memFact (^&(mTop i' k' os.[j])) A) ∈ Γ

lemma prevI_of_last {i' k' j : V} (h : j + 1 = k') : prevI i' k' j = (𝟎 : V) := by
  unfold prevI prevAt; rw [if_pos (by rw [← h]; ring)]

lemma prevI_of_lt {i' k' j : V} (h : j + 1 < k') : prevI i' k' j = ^&(i' + (k' + 1 + j) + 1) := by
  unfold prevI
  apply prevAt_of_lt
  calc i' + (k' + 1 + j) + 1 = i' + (k' + 1) + (j + 1) := by ring
    _ < i' + (k' + 1) + k' := (add_lt_add_iff_left _).mpr h
    _ = i' + (2 * k' + 1) := by ring

set_option maxHeartbeats 2000000 in
/-- **The subset fold is applicable**, link by link. -/
theorem subChainAux_ok {tbl N W i' k' os A E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (hWp : W = proPieces)
    (hΓ : IsFormulaSet LAct Γ) (hA : IsSemiterm LAct 0 A) (hAE : termLen LAct A ≤ E)
    (hkE : i' + (2 * k' + 2) ≤ E) (hosE : ∀ j < k', mTop i' k' os.[j] + 1 ≤ E) (hos : len os = k')
    (hin : SubIn Γ i' k' os A) :
    ∀ c ≤ k', SOut tbl E ⟪W, i', k', os, A⟫ Γ c := by
  have hL := hP.layoutTable
  have hF := hP.frag1Table
  have e81 : ∀ ev : V, mkStep proPieces (81 : V) ev = mkStep layoutPieces (81 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 81 (by decide) ev; simpa using this
  have e112 : ∀ ev : V, mkStep proPieces (112 : V) ev = mkStep frag1Pieces (112 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag1 112 (by decide) ev; simpa using this
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num : (1 : V) ≤ 2) (le_trans le_add_self (le_trans le_add_self hkE))
  intro c
  induction c using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    rw [sOut_iff, subChainAux_zero]
    obtain ⟨ok₀, tg₀, cx₀⟩ := lok_emptySubsetC htbl hL rfl hΓ hA hAE
    rw [← e81, ← hWp] at ok₀ tg₀ cx₀
    refine ⟨listOK_single ok₀, noDrop_single (Or.inl tg₀), hornOnly_single (Or.inl tg₀),
      shiftsV_single_tag0 tg₀, by rw [len_vec1, zero_add], fun _ ↦ ?_, fun h ↦ absurd h (not_le.mpr _root_.zero_lt_one)⟩
    rw [finalCtx_single, cx₀]; exact memInsSelf _ _
  | succ c ih =>
    intro hc
    rw [sOut_iff] at ih ⊢
    obtain ⟨sok, snd, sho, ssh, slen, s0, s1⟩ := ih (le_trans le_self_add hc)
    rw [subChainAux_succ]
    set L := subChainAux ⟪W, i', k', os, A⟫ c with hL'
    set Γc := finalCtx Γ L with hΓc
    have hΓcf : IsFormulaSet LAct Γc := finalCtx_isFormulaSet 8 htbl hΓ sok
    have tr : ∀ x ∈ Γ, x ∈ Γc := fun x hx ↦ by
      have := mem_finalCtx_of_mem snd hx; rwa [ssh, shiftIterV_zero] at this
    have hck : c < k' := lt_of_lt_of_le (lt_add_one c) hc
    set j := jOf k' c with hj
    have hjc : j + (c + 1) = k' := jOf_add hc
    have hjk : j < k' := by rw [← hjc]; exact lt_add_of_pos_right _ (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have hoj : nthFromEnd os c = os.[j] := nthFromEnd_eq (by rw [hos, ← hjc])
    obtain ⟨hins, hmem⟩ := hin j hjk
    -- the subset fact of the set below
    have hbelow : neg LAct (subsetFact (prevI i' k' j) A) ∈ Γc := by
      by_cases hc0 : c = 0
      · rw [prevI_of_last (by rw [← hjc, hc0, zero_add])]; exact s0 hc0
      · have hc1 : 1 ≤ c := by
          have : (0 : V) < c := pos_iff_ne_zero.mpr hc0
          rw [lt_iff_succ_le, zero_add] at this; exact this
        have hlt : j + 1 < k' := by
          rw [← hjc]; exact (add_lt_add_iff_left j).mpr (lt_add_of_pos_left 1 (pos_iff_ne_zero.mpr hc0))
        rw [prevI_of_lt hlt]
        have e : i' + (k' + 1 + j) + 1 = i' + (k' + 1 + jOf k' (c - 1)) := by
          have h1 : c - 1 + 1 = c := tsub_add_cancel_of_le hc1
          have h2 : jOf k' (c - 1) = j + 1 := by
            have := jOf_add (k := k') (c := c - 1) (by rw [h1]; exact le_of_lt hck)
            rw [h1] at this
            have h3 : jOf k' (c - 1) + c = (j + 1) + c := by rw [this, ← hjc]; ring
            exact add_right_cancel h3
          rw [h2]; ring
        rw [e]; exact s1 hc1
    have hjE2 : i' + (k' + 1 + j) + 2 ≤ E := by
      have h1 : j + 1 ≤ k' := lt_iff_succ_le.mp hjk
      calc i' + (k' + 1 + j) + 2 = i' + (k' + 1) + (j + 1) + 1 := by ring
        _ ≤ i' + (k' + 1) + k' + 1 := add_le_add (add_le_add le_rfl h1) le_rfl
        _ = i' + (2 * k' + 2) := by ring
        _ ≤ E := hkE
    have hjE : i' + (k' + 1 + j) + 1 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hjE2
    have hprevI : IsSemiterm LAct 0 (prevI i' k' j) := by unfold prevI; exact isSemiterm_prevAt _ _
    have hprevE : termLen LAct (prevI i' k' j) ≤ E := by
      unfold prevI; exact termLen_prevAt_le hjE2
    obtain ⟨ok₁, tg₁, cx₁⟩ := fok_insertSubset htbl hF rfl hΓcf hprevI hprevE hA hAE
      (by simp) (termLen_fvar_le' (hosE j hjk)) (by simp) (termLen_fvar_le' hjE)
      hbelow (tr _ hmem) (tr _ hins)
    rw [← e112, ← hWp] at ok₁ tg₁ cx₁
    rw [← hoj] at ok₁ tg₁ cx₁
    refine ⟨listOK_appendV sok (listOK_single (by unfold subLink; rw [← hj]; exact ok₁)),
      noDrop_appendV snd (noDrop_single (Or.inl (by unfold subLink; rw [← hj]; exact tg₁))),
      hornOnly_appendV sho (hornOnly_single (Or.inl (by unfold subLink; rw [← hj]; exact tg₁))),
      by rw [shiftsV_appendV, ssh, shiftsV_single_tag0 (by unfold subLink; rw [← hj]; exact tg₁), add_zero],
      by rw [len_appendV, slen, len_vec1],
      fun h ↦ absurd h (ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_add_self)),
      fun _ ↦ ?_⟩
    rw [finalCtx_appendV, ← hΓc, finalCtx_single]
    unfold subLink
    rw [← hj, cx₁, add_tsub_cancel_right, ← hj]
    exact memInsSelf _ _

/-- **`subChain` is applicable** and leaves `subsetFact s A` (`s` the chain top, at `&(i' + (k' + 1))`). -/
theorem subChain_ok {tbl N W i' k' os A E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (hWp : W = proPieces)
    (hΓ : IsFormulaSet LAct Γ) (hA : IsSemiterm LAct 0 A) (hAE : termLen LAct A ≤ E) (hk1 : 1 ≤ k')
    (hkE : i' + (2 * k' + 2) ≤ E) (hosE : ∀ j < k', mTop i' k' os.[j] + 1 ≤ E) (hos : len os = k')
    (hin : SubIn Γ i' k' os A) :
    ListOK tbl E ((8 : ℕ) : V) Γ (subChain W i' k' os A) ∧ NoDrop (subChain W i' k' os A) ∧
    HornOnly (subChain W i' k' os A) ∧ shiftsV (subChain W i' k' os A) = 0 ∧ len (subChain W i' k' os A) = k' + 1 ∧
    neg LAct (subsetFact (^&(i' + (k' + 1))) A) ∈ finalCtx Γ (subChain W i' k' os A) := by
  obtain ⟨sok, snd, sho, ssh, slen, _, s1⟩ :=
    (sOut_iff _ _ _ _ _ _ _ _ _).mp (subChainAux_ok htbl hP hWp hΓ hA hAE hkE hosE hos hin k' le_rfl)
  refine ⟨sok, snd, sho, ssh, slen, ?_⟩
  have h := s1 hk1
  have hj : jOf k' (k' - 1) = 0 := by
    have h1 : k' - 1 + 1 = k' := tsub_add_cancel_of_le hk1
    have := jOf_add (k := k') (c := k' - 1) (by rw [h1])
    rw [h1] at this
    exact add_right_cancel (by rw [this, zero_add] : jOf k' (k' - 1) + k' = 0 + k')
  rwa [hj, add_zero] at h

/-! ### 4.4 The packed parameters of an identification -/

/-- `qPack Wl W i₁ k os xs ip₁ k' os' ys p σ` — the frame of an identification: layout pieces `Wl`, prologue
pieces `W`, the PARENT layout at chain offset `i₁` (`k` members, offsets `os`, member list `xs`), the object of
`p` at `ip₁`, the CHILD layout at offset `0` (`k'` members, offsets `os'`, member list `ys`), the formula `p`,
and the `insertTotalC` object `cp` at `&σ`. -/
noncomputable def qPack (Wl W i₁ k os xs ip₁ k' os' ys p σ : V) : V :=
  ⟪Wl, W, i₁, k, os, xs, ip₁, k', os', ys, p, σ⟫

noncomputable def qWl (q : V) : V := π₁ q
noncomputable def qW (q : V) : V := π₁ (π₂ q)
noncomputable def qI (q : V) : V := π₁ (π₂ (π₂ q))
noncomputable def qK (q : V) : V := π₁ (π₂ (π₂ (π₂ q)))
noncomputable def qOs (q : V) : V := π₁ (π₂ (π₂ (π₂ (π₂ q))))
noncomputable def qXs (q : V) : V := π₁ (π₂ (π₂ (π₂ (π₂ (π₂ q)))))
noncomputable def qIp (q : V) : V := π₁ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ q))))))
noncomputable def qK' (q : V) : V := π₁ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ q)))))))
noncomputable def qOs' (q : V) : V := π₁ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ q))))))))
noncomputable def qYs (q : V) : V := π₁ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ q)))))))))
noncomputable def qP (q : V) : V := π₁ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ q))))))))))
noncomputable def qSig (q : V) : V := π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ q))))))))))

@[simp] lemma qWl_pack (Wl W i₁ k os xs ip₁ k' os' ys p σ : V) : qWl (qPack Wl W i₁ k os xs ip₁ k' os' ys p σ) = Wl := by simp [qWl, qPack]
@[simp] lemma qW_pack (Wl W i₁ k os xs ip₁ k' os' ys p σ : V) : qW (qPack Wl W i₁ k os xs ip₁ k' os' ys p σ) = W := by simp [qW, qPack]
@[simp] lemma qI_pack (Wl W i₁ k os xs ip₁ k' os' ys p σ : V) : qI (qPack Wl W i₁ k os xs ip₁ k' os' ys p σ) = i₁ := by simp [qI, qPack]
@[simp] lemma qK_pack (Wl W i₁ k os xs ip₁ k' os' ys p σ : V) : qK (qPack Wl W i₁ k os xs ip₁ k' os' ys p σ) = k := by simp [qK, qPack]
@[simp] lemma qOs_pack (Wl W i₁ k os xs ip₁ k' os' ys p σ : V) : qOs (qPack Wl W i₁ k os xs ip₁ k' os' ys p σ) = os := by simp [qOs, qPack]
@[simp] lemma qXs_pack (Wl W i₁ k os xs ip₁ k' os' ys p σ : V) : qXs (qPack Wl W i₁ k os xs ip₁ k' os' ys p σ) = xs := by simp [qXs, qPack]
@[simp] lemma qIp_pack (Wl W i₁ k os xs ip₁ k' os' ys p σ : V) : qIp (qPack Wl W i₁ k os xs ip₁ k' os' ys p σ) = ip₁ := by simp [qIp, qPack]
@[simp] lemma qK'_pack (Wl W i₁ k os xs ip₁ k' os' ys p σ : V) : qK' (qPack Wl W i₁ k os xs ip₁ k' os' ys p σ) = k' := by simp [qK', qPack]
@[simp] lemma qOs'_pack (Wl W i₁ k os xs ip₁ k' os' ys p σ : V) : qOs' (qPack Wl W i₁ k os xs ip₁ k' os' ys p σ) = os' := by simp [qOs', qPack]
@[simp] lemma qYs_pack (Wl W i₁ k os xs ip₁ k' os' ys p σ : V) : qYs (qPack Wl W i₁ k os xs ip₁ k' os' ys p σ) = ys := by simp [qYs, qPack]
@[simp] lemma qP_pack (Wl W i₁ k os xs ip₁ k' os' ys p σ : V) : qP (qPack Wl W i₁ k os xs ip₁ k' os' ys p σ) = p := by simp [qP, qPack]
@[simp] lemma qSig_pack (Wl W i₁ k os xs ip₁ k' os' ys p σ : V) : qSig (qPack Wl W i₁ k os xs ip₁ k' os' ys p σ) = σ := by simp [qSig, qPack]

/-- `eqSteps` as an explicit Σ₁ graph (`Layout` only provides `_definable`). -/
noncomputable def eqStepsDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y W i j r. ∃ t, !eqFPDef t 0 r ∧ ∃ t₂, !pi₂Def t₂ t ∧ ∃ t₃, !pi₂Def t₃ t₂ ∧ !relocSDef y t₃ W i j”

instance eqSteps_defined' : 𝚺₁-Function₄ (eqSteps : V → V → V → V → V) via eqStepsDef := .mk fun v ↦ by
  simp [eqStepsDef, eqSteps, eqFT, eqFP_defined.iff, relocS_defined.iff, numeral_eq_natCast]

/-! ### 4.5 The three member blocks and the two loops -/

/-- Loop A, member `j` of the CHILD: `memFact Y_j cp`. If `y_j = p`: `eqSteps Y_j P`, `memInsertSelfC`,
`congMem`; else (`y_j ∈ s`): `eqSteps Y_j X_{j'}`, `memInsertOfMem`, `congMem`. -/
noncomputable def blockA (q j : V) : V :=
  if (qYs q).[j] = qP q then
    appendV (eqSteps (qWl q) (mTop 0 (qK' q) (qOs' q).[j]) (qIp q) (qP q))
      ?[mkStep (qW q) 77 ?[^&(qIp q), ^&(qI q + (qK q + 1)), ^&(qSig q)],
        mkStep (qW q) 62 ?[^&(qIp q), ^&(mTop 0 (qK' q) (qOs' q).[j]), ^&(qSig q)]]
  else
    appendV (eqSteps (qWl q) (mTop 0 (qK' q) (qOs' q).[j]) (mTop (qI q) (qK q) (qOs q).[idxOf (qXs q) (qYs q).[j]]) (qYs q).[j])
      ?[mkStep (qW q) 113 ?[^&(mTop (qI q) (qK q) (qOs q).[idxOf (qXs q) (qYs q).[j]]), ^&(qI q + (qK q + 1)), ^&(qIp q), ^&(qSig q)],
        mkStep (qW q) 62 ?[^&(mTop (qI q) (qK q) (qOs q).[idxOf (qXs q) (qYs q).[j]]), ^&(mTop 0 (qK' q) (qOs' q).[j]), ^&(qSig q)]]

noncomputable def blockADef : 𝚺₁.Semisentence 3 := .mkSigma
  “y q j. ∃ Wl, !pi₁Def Wl q ∧ ∃ r1, !pi₂Def r1 q ∧ ∃ W, !pi₁Def W r1 ∧ ∃ r2, !pi₂Def r2 r1 ∧ ∃ i, !pi₁Def i r2 ∧ ∃ r3, !pi₂Def r3 r2 ∧ ∃ k, !pi₁Def k r3 ∧ ∃ r4, !pi₂Def r4 r3 ∧ ∃ os, !pi₁Def os r4 ∧ ∃ r5, !pi₂Def r5 r4 ∧ ∃ xs, !pi₁Def xs r5 ∧ ∃ r6, !pi₂Def r6 r5 ∧ ∃ ip, !pi₁Def ip r6 ∧ ∃ r7, !pi₂Def r7 r6 ∧ ∃ kk, !pi₁Def kk r7 ∧ ∃ r8, !pi₂Def r8 r7 ∧ ∃ oss, !pi₁Def oss r8 ∧ ∃ r9, !pi₂Def r9 r8 ∧ ∃ ys, !pi₁Def ys r9 ∧ ∃ r10, !pi₂Def r10 r9 ∧ ∃ p, !pi₁Def p r10 ∧ ∃ sg, !pi₂Def sg r10 ∧
    ∃ yj, !nthDef yj ys j ∧ ∃ oj, !nthDef oj oss j ∧ ∃ tj, tj = 0 + (2 * kk + 1 + oj) ∧ ∃ zj, !qqFvarDef zj tj ∧
    ∃ zip, !qqFvarDef zip ip ∧ ∃ is, is = i + (k + 1) ∧ ∃ zs, !qqFvarDef zs is ∧ ∃ zc, !qqFvarDef zc sg ∧
    (yj = p → ∃ e, !eqStepsDef e Wl tj ip p ∧
      ∃ a₁, !adjoinDef a₁ zc 0 ∧ ∃ a₂, !adjoinDef a₂ zs a₁ ∧ ∃ a₃, !adjoinDef a₃ zip a₂ ∧ ∃ s₁, !mkStepDef s₁ W 77 a₃ ∧
      ∃ b₁, !adjoinDef b₁ zc 0 ∧ ∃ b₂, !adjoinDef b₂ zj b₁ ∧ ∃ b₃, !adjoinDef b₃ zip b₂ ∧ ∃ s₂, !mkStepDef s₂ W 62 b₃ ∧
      ∃ l₂, !adjoinDef l₂ s₂ 0 ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧ !appendVDef y e l₁) ∧
    (yj ≠ p → ∃ jp, !idxOfDef jp xs yj ∧ ∃ oo, !nthDef oo os jp ∧ ∃ tx, tx = i + (2 * k + 1 + oo) ∧ ∃ zx, !qqFvarDef zx tx ∧
      ∃ e, !eqStepsDef e Wl tj tx yj ∧
      ∃ a₁, !adjoinDef a₁ zc 0 ∧ ∃ a₂, !adjoinDef a₂ zip a₁ ∧ ∃ a₃, !adjoinDef a₃ zs a₂ ∧ ∃ a₄, !adjoinDef a₄ zx a₃ ∧
      ∃ s₁, !mkStepDef s₁ W 113 a₄ ∧
      ∃ b₁, !adjoinDef b₁ zc 0 ∧ ∃ b₂, !adjoinDef b₂ zj b₁ ∧ ∃ b₃, !adjoinDef b₃ zx b₂ ∧ ∃ s₂, !mkStepDef s₂ W 62 b₃ ∧
      ∃ l₂, !adjoinDef l₂ s₂ 0 ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧ !appendVDef y e l₁)”

set_option maxHeartbeats 1000000 in
instance blockA_defined : 𝚺₁-Function₂ (blockA : V → V → V) via blockADef := .mk fun v ↦ by
  simp [blockADef, blockA, qWl, qW, qI, qK, qOs, qXs, qIp, qK', qOs', qYs, qP, qSig, mTop, eqSteps_defined'.iff,
    idxOf_defined.iff, mkStep_defined.iff, appendV_defined.iff, numeral_eq_natCast]
  by_cases h : (π₁ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (v 1))))))))))).[v 2] =
      π₁ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (v 1)))))))))))
  · simp [h]
  · simp [h]
instance blockA_definable : 𝚺₁-Function₂ (blockA : V → V → V) := blockA_defined.to_definable

/-- Loop B, member `j` of the PARENT: `memFact X_j s''` by `eqSteps Y_{j''} X_j`, `eqSymm`, `congMem`. -/
noncomputable def blockB (q j : V) : V :=
  appendV (eqSteps (qWl q) (mTop 0 (qK' q) (qOs' q).[idxOf (qYs q) (qXs q).[j]]) (mTop (qI q) (qK q) (qOs q).[j]) (qXs q).[j])
    ?[mkStep (qW q) 42 ?[^&(mTop 0 (qK' q) (qOs' q).[idxOf (qYs q) (qXs q).[j]]), ^&(mTop (qI q) (qK q) (qOs q).[j])],
      mkStep (qW q) 62 ?[^&(mTop 0 (qK' q) (qOs' q).[idxOf (qYs q) (qXs q).[j]]), ^&(mTop (qI q) (qK q) (qOs q).[j]),
        ^&(0 + (qK' q + 1))]]

noncomputable def blockBDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y q j. ∃ Wl, !pi₁Def Wl q ∧ ∃ r1, !pi₂Def r1 q ∧ ∃ W, !pi₁Def W r1 ∧ ∃ r2, !pi₂Def r2 r1 ∧ ∃ i, !pi₁Def i r2 ∧ ∃ r3, !pi₂Def r3 r2 ∧ ∃ k, !pi₁Def k r3 ∧ ∃ r4, !pi₂Def r4 r3 ∧ ∃ os, !pi₁Def os r4 ∧ ∃ r5, !pi₂Def r5 r4 ∧ ∃ xs, !pi₁Def xs r5 ∧ ∃ r6, !pi₂Def r6 r5 ∧ ∃ ip, !pi₁Def ip r6 ∧ ∃ r7, !pi₂Def r7 r6 ∧ ∃ kk, !pi₁Def kk r7 ∧ ∃ r8, !pi₂Def r8 r7 ∧ ∃ oss, !pi₁Def oss r8 ∧ ∃ r9, !pi₂Def r9 r8 ∧ ∃ ys, !pi₁Def ys r9 ∧ ∃ r10, !pi₂Def r10 r9 ∧ ∃ p, !pi₁Def p r10 ∧ ∃ sg, !pi₂Def sg r10 ∧
    ∃ xj, !nthDef xj xs j ∧ ∃ jy, !idxOfDef jy ys xj ∧ ∃ oy, !nthDef oy oss jy ∧ ∃ ty, ty = 0 + (2 * kk + 1 + oy) ∧
    ∃ zy, !qqFvarDef zy ty ∧ ∃ oj, !nthDef oj os j ∧ ∃ tx, tx = i + (2 * k + 1 + oj) ∧ ∃ zx, !qqFvarDef zx tx ∧
    ∃ is, is = 0 + (kk + 1) ∧ ∃ zs, !qqFvarDef zs is ∧
    ∃ e, !eqStepsDef e Wl ty tx xj ∧
    ∃ a₁, !adjoinDef a₁ zx 0 ∧ ∃ a₂, !adjoinDef a₂ zy a₁ ∧ ∃ s₁, !mkStepDef s₁ W 42 a₂ ∧
    ∃ b₁, !adjoinDef b₁ zs 0 ∧ ∃ b₂, !adjoinDef b₂ zx b₁ ∧ ∃ b₃, !adjoinDef b₃ zy b₂ ∧ ∃ s₂, !mkStepDef s₂ W 62 b₃ ∧
    ∃ l₂, !adjoinDef l₂ s₂ 0 ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧ !appendVDef y e l₁”

set_option maxHeartbeats 1000000 in
instance blockB_defined : 𝚺₁-Function₂ (blockB : V → V → V) via blockBDef := .mk fun v ↦ by
  simp [blockBDef, blockB, qWl, qW, qI, qK, qOs, qXs, qIp, qK', qOs', qYs, qP, qSig, mTop, eqSteps_defined'.iff,
    idxOf_defined.iff, mkStep_defined.iff, appendV_defined.iff, numeral_eq_natCast]
instance blockB_definable : 𝚺₁-Function₂ (blockB : V → V → V) := blockB_defined.to_definable

/-- The `p` block: `memFact P s''` by `eqSteps Y_{jp} P`, `eqSymm`, `congMem`. -/
noncomputable def blockP (q : V) : V :=
  appendV (eqSteps (qWl q) (mTop 0 (qK' q) (qOs' q).[idxOf (qYs q) (qP q)]) (qIp q) (qP q))
    ?[mkStep (qW q) 42 ?[^&(mTop 0 (qK' q) (qOs' q).[idxOf (qYs q) (qP q)]), ^&(qIp q)],
      mkStep (qW q) 62 ?[^&(mTop 0 (qK' q) (qOs' q).[idxOf (qYs q) (qP q)]), ^&(qIp q), ^&(0 + (qK' q + 1))]]

noncomputable def blockPDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y q. ∃ Wl, !pi₁Def Wl q ∧ ∃ r1, !pi₂Def r1 q ∧ ∃ W, !pi₁Def W r1 ∧ ∃ r2, !pi₂Def r2 r1 ∧ ∃ i, !pi₁Def i r2 ∧ ∃ r3, !pi₂Def r3 r2 ∧ ∃ k, !pi₁Def k r3 ∧ ∃ r4, !pi₂Def r4 r3 ∧ ∃ os, !pi₁Def os r4 ∧ ∃ r5, !pi₂Def r5 r4 ∧ ∃ xs, !pi₁Def xs r5 ∧ ∃ r6, !pi₂Def r6 r5 ∧ ∃ ip, !pi₁Def ip r6 ∧ ∃ r7, !pi₂Def r7 r6 ∧ ∃ kk, !pi₁Def kk r7 ∧ ∃ r8, !pi₂Def r8 r7 ∧ ∃ oss, !pi₁Def oss r8 ∧ ∃ r9, !pi₂Def r9 r8 ∧ ∃ ys, !pi₁Def ys r9 ∧ ∃ r10, !pi₂Def r10 r9 ∧ ∃ p, !pi₁Def p r10 ∧ ∃ sg, !pi₂Def sg r10 ∧
    ∃ jy, !idxOfDef jy ys p ∧ ∃ oy, !nthDef oy oss jy ∧ ∃ ty, ty = 0 + (2 * kk + 1 + oy) ∧ ∃ zy, !qqFvarDef zy ty ∧
    ∃ zip, !qqFvarDef zip ip ∧ ∃ is, is = 0 + (kk + 1) ∧ ∃ zs, !qqFvarDef zs is ∧
    ∃ e, !eqStepsDef e Wl ty ip p ∧
    ∃ a₁, !adjoinDef a₁ zip 0 ∧ ∃ a₂, !adjoinDef a₂ zy a₁ ∧ ∃ s₁, !mkStepDef s₁ W 42 a₂ ∧
    ∃ b₁, !adjoinDef b₁ zs 0 ∧ ∃ b₂, !adjoinDef b₂ zip b₁ ∧ ∃ b₃, !adjoinDef b₃ zy b₂ ∧ ∃ s₂, !mkStepDef s₂ W 62 b₃ ∧
    ∃ l₂, !adjoinDef l₂ s₂ 0 ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧ !appendVDef y e l₁”

set_option maxHeartbeats 1000000 in
instance blockP_defined : 𝚺₁-Function₁ (blockP : V → V) via blockPDef := .mk fun v ↦ by
  simp [blockPDef, blockP, qWl, qW, qI, qK, qOs, qXs, qIp, qK', qOs', qYs, qP, qSig, mTop, eqSteps_defined'.iff,
    idxOf_defined.iff, mkStep_defined.iff, appendV_defined.iff, numeral_eq_natCast]
instance blockP_definable : 𝚺₁-Function₁ (blockP : V → V) := blockP_defined.to_definable

namespace LoopA

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y q. y = 0”
  succ := .mkSigma “y ih j q. ∃ b, !blockADef b q j ∧ !appendVDef y ih b”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 0
  succ := fun v j ih ↦ appendV ih (blockA (v 0) j)
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, blockA_defined.iff, appendV_defined.iff]

end LoopA

namespace LoopB

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y q. y = 0”
  succ := .mkSigma “y ih j q. ∃ b, !blockBDef b q j ∧ !appendVDef y ih b”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 0
  succ := fun v j ih ↦ appendV ih (blockB (v 0) j)
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, blockB_defined.iff, appendV_defined.iff]

end LoopB

/-- Loop A over the first `m` child members. -/
noncomputable def loopA (q m : V) : V := LoopA.construction.result ![q] m
/-- Loop B over the first `m` parent members. -/
noncomputable def loopB (q m : V) : V := LoopB.construction.result ![q] m

@[simp] lemma loopA_zero (q : V) : loopA q 0 = 0 := by simp [loopA, LoopA.construction]
lemma loopA_succ (q m : V) : loopA q (m + 1) = appendV (loopA q m) (blockA q m) := by simp [loopA, LoopA.construction]
@[simp] lemma loopB_zero (q : V) : loopB q 0 = 0 := by simp [loopB, LoopB.construction]
lemma loopB_succ (q m : V) : loopB q (m + 1) = appendV (loopB q m) (blockB q m) := by simp [loopB, LoopB.construction]

noncomputable def loopADef : 𝚺₁.Semisentence 3 := LoopA.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])
noncomputable def loopBDef : 𝚺₁.Semisentence 3 := LoopB.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance loopA_defined : 𝚺₁-Function₂ (loopA : V → V → V) via loopADef := .mk
  fun v ↦ by simp [LoopA.construction.result_defined_iff, loopADef]; rfl
instance loopA_definable : 𝚺₁-Function₂ (loopA : V → V → V) := loopA_defined.to_definable
instance loopB_defined : 𝚺₁-Function₂ (loopB : V → V → V) via loopBDef := .mk
  fun v ↦ by simp [LoopB.construction.result_defined_iff, loopBDef]; rfl
instance loopB_definable : 𝚺₁-Function₂ (loopB : V → V → V) := loopB_defined.to_definable

/-- **`identIns q`**: Loop A, `s'' ⊆ cp`, Loop B, the `p` block, `S ⊆ s''`, `cp ⊆ s''` (`insertSubset`),
`subsetAntisymm` → `eqFactB cp s''`. -/
noncomputable def identIns (q : V) : V :=
  appendV (loopA q (qK' q)) (appendV (subChain (qW q) 0 (qK' q) (qOs' q) (^&(qSig q)))
    (appendV (loopB q (qK q)) (appendV (blockP q)
      (appendV (subChain (qW q) (qI q) (qK q) (qOs q) (^&(0 + (qK' q + 1))))
        ?[mkStep (qW q) 112 ?[^&(qI q + (qK q + 1)), ^&(0 + (qK' q + 1)), ^&(qIp q), ^&(qSig q)],
          mkStep (qW q) 75 ?[^&(qSig q), ^&(0 + (qK' q + 1))]]))))

noncomputable def identInsDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y q. ∃ Wl, !pi₁Def Wl q ∧ ∃ r1, !pi₂Def r1 q ∧ ∃ W, !pi₁Def W r1 ∧ ∃ r2, !pi₂Def r2 r1 ∧ ∃ i, !pi₁Def i r2 ∧ ∃ r3, !pi₂Def r3 r2 ∧ ∃ k, !pi₁Def k r3 ∧ ∃ r4, !pi₂Def r4 r3 ∧ ∃ os, !pi₁Def os r4 ∧ ∃ r5, !pi₂Def r5 r4 ∧ ∃ xs, !pi₁Def xs r5 ∧ ∃ r6, !pi₂Def r6 r5 ∧ ∃ ip, !pi₁Def ip r6 ∧ ∃ r7, !pi₂Def r7 r6 ∧ ∃ kk, !pi₁Def kk r7 ∧ ∃ r8, !pi₂Def r8 r7 ∧ ∃ oss, !pi₁Def oss r8 ∧ ∃ r9, !pi₂Def r9 r8 ∧ ∃ ys, !pi₁Def ys r9 ∧ ∃ r10, !pi₂Def r10 r9 ∧ ∃ p, !pi₁Def p r10 ∧ ∃ sg, !pi₂Def sg r10 ∧
    ∃ A, !loopADef A q kk ∧ ∃ zc, !qqFvarDef zc sg ∧ ∃ C₁, !subChainDef C₁ W 0 kk oss zc ∧
    ∃ B, !loopBDef B q k ∧ ∃ P, !blockPDef P q ∧ ∃ is, is = 0 + (kk + 1) ∧ ∃ zs, !qqFvarDef zs is ∧
    ∃ C₂, !subChainDef C₂ W i k os zs ∧ ∃ iS, iS = i + (k + 1) ∧ ∃ zS, !qqFvarDef zS iS ∧ ∃ zip, !qqFvarDef zip ip ∧
    ∃ a₁, !adjoinDef a₁ zc 0 ∧ ∃ a₂, !adjoinDef a₂ zip a₁ ∧ ∃ a₃, !adjoinDef a₃ zs a₂ ∧ ∃ a₄, !adjoinDef a₄ zS a₃ ∧
    ∃ s₁, !mkStepDef s₁ W 112 a₄ ∧
    ∃ b₁, !adjoinDef b₁ zs 0 ∧ ∃ b₂, !adjoinDef b₂ zc b₁ ∧ ∃ s₂, !mkStepDef s₂ W 75 b₂ ∧
    ∃ l₂, !adjoinDef l₂ s₂ 0 ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧
    ∃ r₅, !appendVDef r₅ C₂ l₁ ∧ ∃ r₄, !appendVDef r₄ P r₅ ∧ ∃ r₃, !appendVDef r₃ B r₄ ∧ ∃ r₂, !appendVDef r₂ C₁ r₃ ∧
    !appendVDef y A r₂”

set_option maxHeartbeats 1000000 in
instance identIns_defined : 𝚺₁-Function₁ (identIns : V → V) via identInsDef := .mk fun v ↦ by
  simp [identInsDef, identIns, qWl, qW, qI, qK, qOs, qXs, qIp, qK', qOs', qYs, qP, qSig, loopA_defined.iff,
    loopB_defined.iff, blockP_defined.iff, subChain_defined.iff, mkStep_defined.iff, appendV_defined.iff,
    numeral_eq_natCast]
instance identIns_definable : 𝚺₁-Function₁ (identIns : V → V) := identIns_defined.to_definable

end identify

end ArithS
