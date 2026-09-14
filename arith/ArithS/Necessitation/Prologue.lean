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

end ArithS
