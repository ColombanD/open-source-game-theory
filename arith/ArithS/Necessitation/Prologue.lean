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

/-! ### 4.6 The identification is applicable -/

section identOK

/-- The identification frame: the child's layout at `0` (sequent `insert p s`), the parent's at `i₁`, the
dossier of `p` at `ip₁`, and the `insertTotalC` object `cp = &σ`. -/
structure IdFrame (Ww Wc T Γ s p i₁ ip₁ σ : V) : Prop where
  child : Layout Ww Wc T Γ (insert p s) 0
  parent : Layout Ww Wc T Γ s i₁
  dp : DossF Ww Γ 0 p ip₁
  cp : neg LAct (insFact (^&σ) (^&ip₁) (^&(i₁ + (len (memberList s) + 1)))) ∈ Γ

/-- The caps: `D` bounds `setLen (insert p s)`. -/
structure IdCap (D E i₁ ip₁ σ : V) : Prop where
  hE : 13 * D + 18 * ‖D‖ + 12 ≤ E
  hi : i₁ + 8 * D + 3 ≤ E
  hip : ip₁ + 2 * D + 2 ≤ E
  hσ : σ + 1 ≤ E

lemma setLen_le_insert (p s : V) : setLen LAct s ≤ setLen LAct (insert p s) := by
  by_cases h : p ∈ s
  · have e : insert p s = s := mem_ext (fun x ↦ by
      rw [mem_bitInsert_iff]
      exact ⟨fun hx ↦ by rcases hx with rfl | hx; exact h; exact hx, fun hx ↦ Or.inr hx⟩)
    rw [e]
  · rw [setLen_insert_of_not_mem_V h]; exact le_self_add

/-- `6D + c ≤ 13D + 18‖D‖ + 12` for `c ≤ 12`. -/
lemma six_le_cap {D c : V} (hc : c ≤ 12) : 6 * D + c ≤ 13 * D + 18 * ‖D‖ + 12 :=
  add_le_add (le_trans (mul_le_mul_of_nonneg_right (by norm_num) zero_le) le_self_add) hc

/-- `8D + c ≤ 13D + 18‖D‖ + 12` for `c ≤ 12`. -/
lemma eight_le_cap {D c : V} (hc : c ≤ 12) : 8 * D + c ≤ 13 * D + 18 * ‖D‖ + 12 :=
  add_le_add (le_trans (mul_le_mul_of_nonneg_right (by norm_num) zero_le) le_self_add) hc

/-- The top of member `j` of a layout is at most `i + 6D + 1`. -/
lemma mTop_le {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {Wc : V} (hWc : Wc = certPieces) (T : V)
    {s i D j : V} (hs : IsFormulaSet LAct s) (hsD : setLen LAct s ≤ D) (hj : j < len (memberList s)) :
    mTop i (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[j] ≤ i + 6 * D + 1 := by
  have hkD : len (memberList s) ≤ D := le_trans (len_memberList_le_setLen hs) hsD
  have ho : (offVec (memberList s) walkPieces Wc T).[j] ≤ 4 * D := by
    refine le_trans (nth_offVec_le _ _ _ _ _ hj) ?_
    refine le_trans (tailShift_le htbl hW hWc T _ (fun j hj ↦ hs _ (nth_memberList_mem hj))) ?_
    rw [← setLen_eq_listSum_memberList]; exact mul_le_mul_of_nonneg_left hsD zero_le
  unfold mTop
  calc i + (2 * len (memberList s) + 1 + (offVec (memberList s) walkPieces Wc T).[j])
      ≤ i + (2 * D + 1 + 4 * D) := add_le_add le_rfl (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hkD zero_le) le_rfl) ho)
    _ = i + 6 * D + 1 := by ring

/-- `eqCount r + 1 ≤ 2|r|` for a formula. -/
lemma eqCount_succ_le {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {r : V} (hr : IsSemiformula LAct 0 r) :
    eqCount r + 1 ≤ 2 * formulaLen LAct r := by
  rw [eqCount_eq_descCountF walkPieces hr]; exact descCountF_succ_le htbl hW hr

/-- Loop A's invariant. -/
def AOut (tbl E q Γ m : V) : Prop :=
  ListOK tbl E ((8 : ℕ) : V) Γ (loopA q m) ∧ NoDrop (loopA q m) ∧ HornOnly (loopA q m) ∧ shiftsV (loopA q m) = 0 ∧
  ∀ j < m, neg LAct (memFact (^&(mTop 0 (qK' q) (qOs' q).[j])) (^&(qSig q))) ∈ finalCtx Γ (loopA q m)

set_option maxHeartbeats 1000000 in
instance aOut_definable : 𝚫₁-Relation₅ (AOut : V → V → V → V → V → Prop) := by
  unfold AOut qK' qOs' qSig mTop; definability

/-- Loop B's invariant. -/
def BOut (tbl E q Γ m : V) : Prop :=
  ListOK tbl E ((8 : ℕ) : V) Γ (loopB q m) ∧ NoDrop (loopB q m) ∧ HornOnly (loopB q m) ∧ shiftsV (loopB q m) = 0 ∧
  ∀ j < m, neg LAct (memFact (^&(mTop (qI q) (qK q) (qOs q).[j])) (^&(0 + (qK' q + 1)))) ∈ finalCtx Γ (loopB q m)

set_option maxHeartbeats 1000000 in
instance bOut_definable : 𝚫₁-Relation₅ (BOut : V → V → V → V → V → Prop) := by
  unfold BOut qI qK qOs qK' mTop; definability

/-- A Horn-only, shift-free list keeps every fact of its start. -/
lemma tr_of_zero {Γ S x : V} (hnd : NoDrop S) (hsh : shiftsV S = 0) (hx : x ∈ Γ) : x ∈ finalCtx Γ S := by
  have := mem_finalCtx_of_mem hnd hx; rwa [hsh, shiftIterV_zero] at this

lemma DossierAt.mono {P Γ Γ' i r : V} (h : ∀ x ∈ Γ, x ∈ Γ') (hD : DossierAt P Γ i r) : DossierAt P Γ' i r :=
  (dossierAt_iff _ _ _ _).mpr (allNeg_mono h ((dossierAt_iff _ _ _ _).mp hD))

set_option maxHeartbeats 4000000 in
/-- **Loop A is applicable**: every child member is in `cp`. -/
theorem loopA_ok {tbl N Wl W Wc T s p i₁ ip₁ σ D E Γ q : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hq : q = qPack Wl W i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) ip₁
      (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T) (memberList (insert p s)) p σ)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p) (hsD : setLen LAct (insert p s) ≤ D)
    (hcap : IdCap D E i₁ ip₁ σ) (hΓ : IsFormulaSet LAct Γ) (hF : IdFrame walkPieces Wc T Γ s p i₁ ip₁ σ) :
    ∀ m ≤ len (memberList (insert p s)), AOut tbl E q Γ m := by
  have hW := hP.walkTable
  have hL := hP.layoutTable
  have hF1 := hP.frag1Table
  have hcs : IsFormulaSet LAct (insert p s) := IsFormulaSet.insert_iff.mpr ⟨hp, hs⟩
  have hsD' : setLen LAct s ≤ D := le_trans (setLen_le_insert p s) hsD
  have hpD : formulaLen LAct p ≤ D := le_trans (formulaLen_le_setLen_of_mem (by simp)) hsD
  have hkD : len (memberList s) ≤ D := le_trans (len_memberList_le_setLen hs) hsD'
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hcap.hE)
  have hD13 : 13 * D ≤ E := le_trans le_self_add (le_trans le_self_add hcap.hE)
  have e77 : ∀ ev : V, mkStep proPieces (77 : V) ev = mkStep layoutPieces (77 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 77 (by decide) ev; simpa using this
  have e62 : ∀ ev : V, mkStep proPieces (62 : V) ev = mkStep layoutPieces (62 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 62 (by decide) ev; simpa using this
  have e113 : ∀ ev : V, mkStep proPieces (113 : V) ev = mkStep frag1Pieces (113 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag1 113 (by decide) ev; simpa using this
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    exact ⟨by rw [loopA_zero]; exact listOK_nil _ _ _ _, by rw [loopA_zero]; exact noDrop_nil,
      by rw [loopA_zero]; exact hornOnly_nil, by rw [loopA_zero, shiftsV_nil], fun j hj ↦ absurd hj (by simp)⟩
  | succ m ih =>
    intro hm
    obtain ⟨aok, and, aho, ash, afacts⟩ := ih (le_trans le_self_add hm)
    have hmk : m < len (memberList (insert p s)) := lt_of_lt_of_le (lt_add_one m) hm
    set Γm := finalCtx Γ (loopA q m) with hΓm
    have hΓmf : IsFormulaSet LAct Γm := finalCtx_isFormulaSet 8 htbl hΓ aok
    have tr : ∀ x ∈ Γ, x ∈ Γm := fun x hx ↦ tr_of_zero and ash hx
    -- the child member
    have hym : (memberList (insert p s)).[m] ∈ insert p s := nth_memberList_mem hmk
    have hyf : IsSemiformula LAct 0 (memberList (insert p s)).[m] := hcs _ hym
    have hyD : formulaLen LAct (memberList (insert p s)).[m] ≤ D := le_trans (formulaLen_le_setLen_of_mem hym) hsD
    obtain ⟨hDy, _, _, _, _, hmy⟩ := hF.child.1 m hmk
    have hYD := dossierAt_of_dossF htbl hW rfl hyf hDy
    have hYle : mTop 0 (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T).[m] ≤ 0 + 6 * D + 1 :=
      mTop_le htbl hW hWc T hcs hsD hmk
    have hEy : 2 * (0 + formulaLen LAct (memberList (insert p s)).[m]) + 12 ≤ E := by
      rw [zero_add]
      calc 2 * formulaLen LAct (memberList (insert p s)).[m] + 12 ≤ 2 * D + 12 := add_le_add (mul_le_mul_of_nonneg_left hyD zero_le) le_rfl
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := add_le_add (le_trans (mul_le_mul_of_nonneg_right (by norm_num) zero_le) le_self_add) le_rfl
        _ ≤ E := hcap.hE
    have hcnt : eqCount (memberList (insert p s)).[m] + 1 ≤ 2 * D :=
      le_trans (eqCount_succ_le htbl hW hyf) (mul_le_mul_of_nonneg_left hyD zero_le)
    have hEY : mTop 0 (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T).[m] +
        eqCount (memberList (insert p s)).[m] + 1 ≤ E := by
      calc _ ≤ (0 + 6 * D + 1) + 2 * D := by rw [add_assoc]; exact add_le_add hYle hcnt
        _ = 8 * D + 1 := by ring
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := eight_le_cap (by norm_num)
        _ ≤ E := hcap.hE
    have hYE : mTop 0 (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T).[m] + 1 ≤ E := by
      calc _ ≤ 0 + 6 * D + 1 + 1 := add_le_add hYle le_rfl
        _ = 6 * D + 2 := by ring
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
        _ ≤ E := hcap.hE
    have hipE : ip₁ + 1 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) (le_trans (add_le_add le_self_add le_rfl) hcap.hip)
    have hSE : i₁ + (len (memberList s) + 1) + 1 ≤ E := by
      calc i₁ + (len (memberList s) + 1) + 1 = i₁ + (len (memberList s) + 2) := by ring
        _ ≤ i₁ + (8 * D + 3) := add_le_add le_rfl (add_le_add (le_trans hkD (le_mul_of_one_le_left zero_le (by norm_num))) (by norm_num))
        _ = i₁ + 8 * D + 3 := by ring
        _ ≤ E := hcap.hi
    -- the block
    rw [AOut, loopA_succ]
    have key : ListOK tbl E ((8 : ℕ) : V) Γm (blockA q m) ∧ NoDrop (blockA q m) ∧ HornOnly (blockA q m) ∧
        shiftsV (blockA q m) = 0 ∧
        neg LAct (memFact (^&(mTop 0 (qK' q) (qOs' q).[m])) (^&(qSig q))) ∈ finalCtx Γm (blockA q m) := by
      subst hq
      simp only [qWl_pack, qW_pack, qI_pack, qK_pack, qOs_pack, qXs_pack, qIp_pack, qK'_pack, qOs'_pack, qYs_pack,
        qP_pack, qSig_pack]
      unfold blockA
      simp only [qWl_pack, qW_pack, qI_pack, qK_pack, qOs_pack, qXs_pack, qIp_pack, qK'_pack, qOs'_pack, qYs_pack,
        qP_pack, qSig_pack]
      by_cases hyp : (memberList (insert p s)).[m] = p
      · rw [if_pos hyp]
        rw [hyp] at hYD hEy hEY
        have hPD := dossierAt_of_dossF htbl hW rfl hp hF.dp
        have hEP : ip₁ + eqCount p + 1 ≤ E := by
          have := eqCount_succ_le htbl hW hp
          calc ip₁ + eqCount p + 1 ≤ ip₁ + 2 * D := by rw [add_assoc]; exact add_le_add le_rfl (le_trans this (mul_le_mul_of_nonneg_left hpD zero_le))
            _ ≤ E := le_trans le_self_add hcap.hip
        obtain ⟨eok, end_, eho, esh, _, efact⟩ := eqSteps_ok htbl hL hWl rfl hp hEy hEY hEP hΓmf (hYD.mono tr) (hPD.mono tr)
        set Γe := finalCtx Γm (eqSteps Wl _ ip₁ p) with hΓe
        have hΓef : IsFormulaSet LAct Γe := finalCtx_isFormulaSet 8 htbl hΓmf eok
        have tre : ∀ x ∈ Γm, x ∈ Γe := fun x hx ↦ tr_of_zero end_ esh hx
        obtain ⟨ok₁, tg₁, cx₁⟩ := lok_memInsertSelfC htbl hL rfl hΓef (by simp) (termLen_fvar_le' hipE)
          (by simp) (termLen_fvar_le' hSE) (by simp) (termLen_fvar_le' hcap.hσ) (tre _ (tr _ hF.cp))
        rw [← e77, ← hWp] at ok₁ tg₁ cx₁
        have hΓ₁f : IsFormulaSet LAct (insert (neg LAct (memFact (^&ip₁) (^&σ))) Γe) := by
          rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
        obtain ⟨ok₂, tg₂, cx₂⟩ := lok_congMem htbl hL rfl hΓ₁f (by simp) (termLen_fvar_le' hipE)
          (by simp) (termLen_fvar_le' hYE) (by simp) (termLen_fvar_le' hcap.hσ) (memIns efact) (memInsSelf _ _)
        rw [← e62, ← hWp] at ok₂ tg₂ cx₂
        refine ⟨listOK_appendV eok (listOK_cons ok₁ (by rw [cx₁]; exact listOK_single ok₂)),
          noDrop_appendV end_ (noDrop_cons (Or.inl tg₁) (noDrop_single (Or.inl tg₂))),
          hornOnly_appendV eho (hornOnly_cons (Or.inl tg₁) (hornOnly_single (Or.inl tg₂))),
          by rw [shiftsV_appendV, esh, shiftsV_cons_tag0 tg₁, shiftsV_single_tag0 tg₂, add_zero], ?_⟩
        rw [finalCtx_appendV, ← hΓe, finalCtx_cons, cx₁, finalCtx_single, cx₂]
        exact memInsSelf _ _
      · rw [if_neg hyp]
        have hys : (memberList (insert p s)).[m] ∈ s := by
          rcases mem_bitInsert_iff.mp hym with h | h
          · exact absurd h hyp
          · exact h
        obtain ⟨hlt', heq'⟩ := idxOf_spec hys
        obtain ⟨hDx, _, _, _, _, hmx⟩ := hF.parent.1 _ hlt'
        rw [heq'] at hDx
        have hXD := dossierAt_of_dossF htbl hW rfl hyf hDx
        have hXle := mTop_le htbl hW hWc T hs hsD' hlt' (i := i₁)
        have hEX : mTop i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) (memberList (insert p s)).[m]] +
            eqCount (memberList (insert p s)).[m] + 1 ≤ E := by
          calc _ ≤ (i₁ + 6 * D + 1) + 2 * D := by rw [add_assoc]; exact add_le_add hXle hcnt
            _ = i₁ + 8 * D + 1 := by ring
            _ ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hcap.hi
        have hXE : mTop i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) (memberList (insert p s)).[m]] + 1 ≤ E := by
          calc _ ≤ i₁ + 6 * D + 1 + 1 := add_le_add hXle le_rfl
            _ = i₁ + (6 * D + 2) := by ring
            _ ≤ i₁ + (8 * D + 3) := add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num))
            _ = i₁ + 8 * D + 3 := by ring
            _ ≤ E := hcap.hi
        obtain ⟨eok, end_, eho, esh, _, efact⟩ := eqSteps_ok htbl hL hWl rfl hyf hEy hEY hEX hΓmf (hYD.mono tr) (hXD.mono tr)
        set Γe := finalCtx Γm (eqSteps Wl _ _ _) with hΓe
        have hΓef : IsFormulaSet LAct Γe := finalCtx_isFormulaSet 8 htbl hΓmf eok
        have tre : ∀ x ∈ Γm, x ∈ Γe := fun x hx ↦ tr_of_zero end_ esh hx
        obtain ⟨ok₁, tg₁, cx₁⟩ := fok_memInsertOfMem htbl hF1 rfl hΓef (by simp) (termLen_fvar_le' hXE)
          (by simp) (termLen_fvar_le' hSE) (by simp) (termLen_fvar_le' hipE) (by simp) (termLen_fvar_le' hcap.hσ)
          (tre _ (tr _ hmx)) (tre _ (tr _ hF.cp))
        rw [← e113, ← hWp] at ok₁ tg₁ cx₁
        have hΓ₁f : IsFormulaSet LAct (insert (neg LAct (memFact (^&(mTop i₁ (len (memberList s))
            (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) (memberList (insert p s)).[m]])) (^&σ))) Γe) := by
          rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
        obtain ⟨ok₂, tg₂, cx₂⟩ := lok_congMem htbl hL rfl hΓ₁f (by simp) (termLen_fvar_le' hXE)
          (by simp) (termLen_fvar_le' hYE) (by simp) (termLen_fvar_le' hcap.hσ) (memIns efact) (memInsSelf _ _)
        rw [← e62, ← hWp] at ok₂ tg₂ cx₂
        refine ⟨listOK_appendV eok (listOK_cons ok₁ (by rw [cx₁]; exact listOK_single ok₂)),
          noDrop_appendV end_ (noDrop_cons (Or.inl tg₁) (noDrop_single (Or.inl tg₂))),
          hornOnly_appendV eho (hornOnly_cons (Or.inl tg₁) (hornOnly_single (Or.inl tg₂))),
          by rw [shiftsV_appendV, esh, shiftsV_cons_tag0 tg₁, shiftsV_single_tag0 tg₂, add_zero], ?_⟩
        rw [finalCtx_appendV, ← hΓe, finalCtx_cons, cx₁, finalCtx_single, cx₂]
        exact memInsSelf _ _
    obtain ⟨bok, bnd, bho, bsh, bfact⟩ := key
    refine ⟨listOK_appendV aok (by rw [← hΓm]; exact bok), noDrop_appendV and bnd, hornOnly_appendV aho bho,
      by rw [shiftsV_appendV, ash, bsh, add_zero], fun j hj ↦ ?_⟩
    rw [finalCtx_appendV, ← hΓm]
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hj) with h | rfl
    · exact tr_of_zero bnd bsh (afacts j h)
    · exact bfact

set_option maxHeartbeats 4000000 in
/-- **Loop B is applicable**: every parent member is in the child's chain top `s''`. -/
theorem loopB_ok {tbl N Wl W Wc T s p i₁ ip₁ σ D E Γ q : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hq : q = qPack Wl W i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) ip₁
      (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T) (memberList (insert p s)) p σ)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p) (hsD : setLen LAct (insert p s) ≤ D)
    (hcap : IdCap D E i₁ ip₁ σ) (hΓ : IsFormulaSet LAct Γ) (hF : IdFrame walkPieces Wc T Γ s p i₁ ip₁ σ) :
    ∀ m ≤ len (memberList s), BOut tbl E q Γ m := by
  have hW := hP.walkTable
  have hL := hP.layoutTable
  have hcs : IsFormulaSet LAct (insert p s) := IsFormulaSet.insert_iff.mpr ⟨hp, hs⟩
  have hsD' : setLen LAct s ≤ D := le_trans (setLen_le_insert p s) hsD
  have hk'D : len (memberList (insert p s)) ≤ D := le_trans (len_memberList_le_setLen hcs) hsD
  have e42 : ∀ ev : V, mkStep proPieces (42 : V) ev = mkStep layoutPieces (42 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 42 (by decide) ev; simpa using this
  have e62 : ∀ ev : V, mkStep proPieces (62 : V) ev = mkStep layoutPieces (62 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 62 (by decide) ev; simpa using this
  have hs''E : 0 + (len (memberList (insert p s)) + 1) + 1 ≤ E := by
    calc 0 + (len (memberList (insert p s)) + 1) + 1 = len (memberList (insert p s)) + 2 := by ring
      _ ≤ 6 * D + 2 := add_le_add (le_trans hk'D (le_mul_of_one_le_left zero_le (by norm_num))) le_rfl
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
      _ ≤ E := hcap.hE
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    exact ⟨by rw [loopB_zero]; exact listOK_nil _ _ _ _, by rw [loopB_zero]; exact noDrop_nil,
      by rw [loopB_zero]; exact hornOnly_nil, by rw [loopB_zero, shiftsV_nil], fun j hj ↦ absurd hj (by simp)⟩
  | succ m ih =>
    intro hm
    obtain ⟨bok, bnd, bho, bsh, bfacts⟩ := ih (le_trans le_self_add hm)
    have hmk : m < len (memberList s) := lt_of_lt_of_le (lt_add_one m) hm
    set Γm := finalCtx Γ (loopB q m) with hΓm
    have hΓmf : IsFormulaSet LAct Γm := finalCtx_isFormulaSet 8 htbl hΓ bok
    have tr : ∀ x ∈ Γ, x ∈ Γm := fun x hx ↦ tr_of_zero bnd bsh hx
    -- the parent member and its twin in the child
    have hxm : (memberList s).[m] ∈ s := nth_memberList_mem hmk
    have hxc : (memberList s).[m] ∈ insert p s := mem_bitInsert_iff.mpr (Or.inr hxm)
    have hxf : IsSemiformula LAct 0 (memberList s).[m] := hs _ hxm
    have hxD : formulaLen LAct (memberList s).[m] ≤ D := le_trans (formulaLen_le_setLen_of_mem hxm) hsD'
    obtain ⟨hDx, _, _, _, _, _⟩ := hF.parent.1 m hmk
    have hXD := (dossierAt_of_dossF htbl hW rfl hxf hDx).mono tr
    obtain ⟨hDy, _, _, hmy⟩ := hF.child.member hxc
    have hYD := (dossierAt_of_dossF htbl hW rfl hxf hDy).mono tr
    have hXle := mTop_le htbl hW hWc T hs hsD' hmk (i := i₁)
    obtain ⟨hlt', _⟩ := idxOf_spec hxc
    have hYle := mTop_le htbl hW hWc T hcs hsD hlt' (i := 0)
    have hcnt : eqCount (memberList s).[m] + 1 ≤ 2 * D :=
      le_trans (eqCount_succ_le htbl hW hxf) (mul_le_mul_of_nonneg_left hxD zero_le)
    have hEy : 2 * (0 + formulaLen LAct (memberList s).[m]) + 12 ≤ E := by
      rw [zero_add]
      calc 2 * formulaLen LAct (memberList s).[m] + 12 ≤ 2 * D + 12 := add_le_add (mul_le_mul_of_nonneg_left hxD zero_le) le_rfl
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := add_le_add (le_trans (mul_le_mul_of_nonneg_right (by norm_num) zero_le) le_self_add) le_rfl
        _ ≤ E := hcap.hE
    have hEY : memTop walkPieces Wc T (insert p s) (memberList s).[m] 0 + eqCount (memberList s).[m] + 1 ≤ E := by
      unfold memTop
      calc _ ≤ (0 + 6 * D + 1) + 2 * D := by rw [add_assoc]; exact add_le_add hYle hcnt
        _ = 8 * D + 1 := by ring
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := eight_le_cap (by norm_num)
        _ ≤ E := hcap.hE
    have hEX : mTop i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[m] + eqCount (memberList s).[m] + 1 ≤ E := by
      calc _ ≤ (i₁ + 6 * D + 1) + 2 * D := by rw [add_assoc]; exact add_le_add hXle hcnt
        _ = i₁ + 8 * D + 1 := by ring
        _ ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hcap.hi
    have hYE : memTop walkPieces Wc T (insert p s) (memberList s).[m] 0 + 1 ≤ E := by
      unfold memTop
      calc _ ≤ 0 + 6 * D + 1 + 1 := add_le_add hYle le_rfl
        _ = 6 * D + 2 := by ring
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
        _ ≤ E := hcap.hE
    have hXE : mTop i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[m] + 1 ≤ E := by
      calc _ ≤ i₁ + 6 * D + 1 + 1 := add_le_add hXle le_rfl
        _ = i₁ + (6 * D + 2) := by ring
        _ ≤ i₁ + (8 * D + 3) := add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num))
        _ = i₁ + 8 * D + 3 := by ring
        _ ≤ E := hcap.hi
    unfold memTop at hEY hYE hmy hYD
    rw [BOut, loopB_succ]
    have key : ListOK tbl E ((8 : ℕ) : V) Γm (blockB q m) ∧ NoDrop (blockB q m) ∧ HornOnly (blockB q m) ∧
        shiftsV (blockB q m) = 0 ∧
        neg LAct (memFact (^&(mTop (qI q) (qK q) (qOs q).[m])) (^&(0 + (qK' q + 1)))) ∈ finalCtx Γm (blockB q m) := by
      subst hq
      simp only [qWl_pack, qW_pack, qI_pack, qK_pack, qOs_pack, qXs_pack, qIp_pack, qK'_pack, qOs'_pack, qYs_pack,
        qP_pack, qSig_pack]
      unfold blockB
      simp only [qWl_pack, qW_pack, qI_pack, qK_pack, qOs_pack, qXs_pack, qIp_pack, qK'_pack, qOs'_pack, qYs_pack,
        qP_pack, qSig_pack]
      obtain ⟨eok, end_, eho, esh, _, efact⟩ := eqSteps_ok htbl hL hWl rfl hxf hEy hEY hEX hΓmf hYD hXD
      set Γe := finalCtx Γm (eqSteps Wl _ _ _) with hΓe
      have hΓef : IsFormulaSet LAct Γe := finalCtx_isFormulaSet 8 htbl hΓmf eok
      have tre : ∀ x ∈ Γm, x ∈ Γe := fun x hx ↦ tr_of_zero end_ esh hx
      obtain ⟨ok₁, tg₁, cx₁⟩ := lok_eqSymm htbl hL rfl hΓef (by simp) (termLen_fvar_le' hYE) (by simp) (termLen_fvar_le' hXE) efact
      rw [← e42, ← hWp] at ok₁ tg₁ cx₁
      have hΓ₁f : IsFormulaSet LAct (insert (neg LAct (eqFactB (^&(mTop i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[m]))
          (^&(mTop 0 (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T).[idxOf (memberList (insert p s)) (memberList s).[m]])))) Γe) := by
        rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
      obtain ⟨ok₂, tg₂, cx₂⟩ := lok_congMem htbl hL rfl hΓ₁f (by simp) (termLen_fvar_le' hYE)
        (by simp) (termLen_fvar_le' hXE) (by simp) (termLen_fvar_le' hs''E) (memInsSelf _ _) (memIns (tre _ (tr _ hmy)))
      rw [← e62, ← hWp] at ok₂ tg₂ cx₂
      refine ⟨listOK_appendV eok (listOK_cons ok₁ (by rw [cx₁]; exact listOK_single ok₂)),
        noDrop_appendV end_ (noDrop_cons (Or.inl tg₁) (noDrop_single (Or.inl tg₂))),
        hornOnly_appendV eho (hornOnly_cons (Or.inl tg₁) (hornOnly_single (Or.inl tg₂))),
        by rw [shiftsV_appendV, esh, shiftsV_cons_tag0 tg₁, shiftsV_single_tag0 tg₂, add_zero], ?_⟩
      rw [finalCtx_appendV, ← hΓe, finalCtx_cons, cx₁, finalCtx_single, cx₂]
      exact memInsSelf _ _
    obtain ⟨cok, cnd, cho, csh, cfact⟩ := key
    refine ⟨listOK_appendV bok (by rw [← hΓm]; exact cok), noDrop_appendV bnd cnd, hornOnly_appendV bho cho,
      by rw [shiftsV_appendV, bsh, csh, add_zero], fun j hj ↦ ?_⟩
    rw [finalCtx_appendV, ← hΓm]
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hj) with h | rfl
    · exact tr_of_zero cnd csh (bfacts j h)
    · exact cfact

set_option maxHeartbeats 2000000 in
/-- **The `p` block is applicable**: `memFact P s''`. -/
theorem blockP_ok {tbl N Wl W Wc T s p i₁ ip₁ σ D E Γ q : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hq : q = qPack Wl W i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) ip₁
      (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T) (memberList (insert p s)) p σ)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p) (hsD : setLen LAct (insert p s) ≤ D)
    (hcap : IdCap D E i₁ ip₁ σ) (hΓ : IsFormulaSet LAct Γ) (hF : IdFrame walkPieces Wc T Γ s p i₁ ip₁ σ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (blockP q) ∧ NoDrop (blockP q) ∧ HornOnly (blockP q) ∧ shiftsV (blockP q) = 0 ∧
    neg LAct (memFact (^&ip₁) (^&(0 + (len (memberList (insert p s)) + 1)))) ∈ finalCtx Γ (blockP q) := by
  have hW := hP.walkTable
  have hL := hP.layoutTable
  have hcs : IsFormulaSet LAct (insert p s) := IsFormulaSet.insert_iff.mpr ⟨hp, hs⟩
  have hpD : formulaLen LAct p ≤ D := le_trans (formulaLen_le_setLen_of_mem (by simp)) hsD
  have hk'D : len (memberList (insert p s)) ≤ D := le_trans (len_memberList_le_setLen hcs) hsD
  have e42 : ∀ ev : V, mkStep proPieces (42 : V) ev = mkStep layoutPieces (42 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 42 (by decide) ev; simpa using this
  have e62 : ∀ ev : V, mkStep proPieces (62 : V) ev = mkStep layoutPieces (62 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 62 (by decide) ev; simpa using this
  have hs''E : 0 + (len (memberList (insert p s)) + 1) + 1 ≤ E := by
    calc 0 + (len (memberList (insert p s)) + 1) + 1 = len (memberList (insert p s)) + 2 := by ring
      _ ≤ 6 * D + 2 := add_le_add (le_trans hk'D (le_mul_of_one_le_left zero_le (by norm_num))) le_rfl
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
      _ ≤ E := hcap.hE
  have hpc : p ∈ insert p s := by simp
  obtain ⟨hDy, _, _, hmy⟩ := hF.child.member hpc
  have hYD := dossierAt_of_dossF htbl hW rfl hp hDy
  have hPD := dossierAt_of_dossF htbl hW rfl hp hF.dp
  obtain ⟨hlt', _⟩ := idxOf_spec hpc
  have hYle := mTop_le htbl hW hWc T hcs hsD hlt' (i := 0)
  have hcnt : eqCount p + 1 ≤ 2 * D := le_trans (eqCount_succ_le htbl hW hp) (mul_le_mul_of_nonneg_left hpD zero_le)
  have hEy : 2 * (0 + formulaLen LAct p) + 12 ≤ E := by
    rw [zero_add]
    calc 2 * formulaLen LAct p + 12 ≤ 2 * D + 12 := add_le_add (mul_le_mul_of_nonneg_left hpD zero_le) le_rfl
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := add_le_add (le_trans (mul_le_mul_of_nonneg_right (by norm_num) zero_le) le_self_add) le_rfl
      _ ≤ E := hcap.hE
  have hEY : memTop walkPieces Wc T (insert p s) p 0 + eqCount p + 1 ≤ E := by
    unfold memTop
    calc _ ≤ (0 + 6 * D + 1) + 2 * D := by rw [add_assoc]; exact add_le_add hYle hcnt
      _ = 8 * D + 1 := by ring
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := eight_le_cap (by norm_num)
      _ ≤ E := hcap.hE
  have hEP : ip₁ + eqCount p + 1 ≤ E := by
    calc ip₁ + eqCount p + 1 ≤ ip₁ + 2 * D := by rw [add_assoc]; exact add_le_add le_rfl hcnt
      _ ≤ E := le_trans le_self_add hcap.hip
  have hYE : memTop walkPieces Wc T (insert p s) p 0 + 1 ≤ E := by
    unfold memTop
    calc _ ≤ 0 + 6 * D + 1 + 1 := add_le_add hYle le_rfl
      _ = 6 * D + 2 := by ring
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
      _ ≤ E := hcap.hE
  have hipE : ip₁ + 1 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) (le_trans (add_le_add le_self_add le_rfl) hcap.hip)
  unfold memTop at hEY hYE hmy hYD
  subst hq
  unfold blockP
  simp only [qWl_pack, qW_pack, qI_pack, qK_pack, qOs_pack, qXs_pack, qIp_pack, qK'_pack, qOs'_pack, qYs_pack,
    qP_pack, qSig_pack]
  obtain ⟨eok, end_, eho, esh, _, efact⟩ := eqSteps_ok htbl hL hWl rfl hp hEy hEY hEP hΓ hYD hPD
  set Γe := finalCtx Γ (eqSteps Wl _ ip₁ p) with hΓe
  have hΓef : IsFormulaSet LAct Γe := finalCtx_isFormulaSet 8 htbl hΓ eok
  have tre : ∀ x ∈ Γ, x ∈ Γe := fun x hx ↦ tr_of_zero end_ esh hx
  obtain ⟨ok₁, tg₁, cx₁⟩ := lok_eqSymm htbl hL rfl hΓef (by simp) (termLen_fvar_le' hYE) (by simp) (termLen_fvar_le' hipE) efact
  rw [← e42, ← hWp] at ok₁ tg₁ cx₁
  have hΓ₁f : IsFormulaSet LAct (insert (neg LAct (eqFactB (^&ip₁)
      (^&(mTop 0 (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T).[idxOf (memberList (insert p s)) p])))) Γe) := by
    rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  obtain ⟨ok₂, tg₂, cx₂⟩ := lok_congMem htbl hL rfl hΓ₁f (by simp) (termLen_fvar_le' hYE)
    (by simp) (termLen_fvar_le' hipE) (by simp) (termLen_fvar_le' hs''E) (memInsSelf _ _) (memIns (tre _ hmy))
  rw [← e62, ← hWp] at ok₂ tg₂ cx₂
  refine ⟨listOK_appendV eok (listOK_cons ok₁ (by rw [cx₁]; exact listOK_single ok₂)),
    noDrop_appendV end_ (noDrop_cons (Or.inl tg₁) (noDrop_single (Or.inl tg₂))),
    hornOnly_appendV eho (hornOnly_cons (Or.inl tg₁) (hornOnly_single (Or.inl tg₂))),
    by rw [shiftsV_appendV, esh, shiftsV_cons_tag0 tg₁, shiftsV_single_tag0 tg₂, add_zero], ?_⟩
  rw [finalCtx_appendV, ← hΓe, finalCtx_cons, cx₁, finalCtx_single, cx₂]
  exact memInsSelf _ _

/-- The frame survives a Horn-only, shift-free list. -/
lemma IdFrame.zero_transport {Ww Wc T Γ s p i₁ ip₁ σ S : V} (hS : NoDrop S) (hsh : shiftsV S = 0)
    (hF : IdFrame Ww Wc T Γ s p i₁ ip₁ σ) : IdFrame Ww Wc T (finalCtx Γ S) s p i₁ ip₁ σ where
  child := by have := hF.child.transport hS.noDrop' ; rwa [hsh, add_zero] at this
  parent := by have := hF.parent.transport hS.noDrop' ; rwa [hsh, add_zero] at this
  dp := by have := dossF_transport hS hF.dp; rwa [hsh, add_zero] at this
  cp := tr_of_zero hS hsh hF.cp

set_option maxHeartbeats 4000000 in
/-- **The identification is applicable** and leaves `eqFactB cp s''` (`cp = &σ`, `s'' = &(k' + 1)`). -/
theorem identIns_ok {tbl N Wl W Wc T s p i₁ ip₁ σ D E Γ q : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hq : q = qPack Wl W i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) ip₁
      (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T) (memberList (insert p s)) p σ)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p) (hk1 : 1 ≤ len (memberList s))
    (hsD : setLen LAct (insert p s) ≤ D)
    (hcap : IdCap D E i₁ ip₁ σ) (hΓ : IsFormulaSet LAct Γ) (hF : IdFrame walkPieces Wc T Γ s p i₁ ip₁ σ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (identIns q) ∧ NoDrop (identIns q) ∧ HornOnly (identIns q) ∧
    shiftsV (identIns q) = 0 ∧
    neg LAct (eqFactB (^&σ) (^&(0 + (len (memberList (insert p s)) + 1)))) ∈ finalCtx Γ (identIns q) := by
  have hW := hP.walkTable
  have hL := hP.layoutTable
  have hF1 := hP.frag1Table
  have hcs : IsFormulaSet LAct (insert p s) := IsFormulaSet.insert_iff.mpr ⟨hp, hs⟩
  have hsD' : setLen LAct s ≤ D := le_trans (setLen_le_insert p s) hsD
  have hkD : len (memberList s) ≤ D := le_trans (len_memberList_le_setLen hs) hsD'
  have hk'D : len (memberList (insert p s)) ≤ D := le_trans (len_memberList_le_setLen hcs) hsD
  have hk1' : 1 ≤ len (memberList (insert p s)) := by
    obtain ⟨hlt, _⟩ := idxOf_spec (show p ∈ insert p s by simp)
    have := lt_iff_succ_le.mp (lt_of_le_of_lt zero_le hlt); rwa [zero_add] at this
  have e112 : ∀ ev : V, mkStep proPieces (112 : V) ev = mkStep frag1Pieces (112 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag1 112 (by decide) ev; simpa using this
  have e75 : ∀ ev : V, mkStep proPieces (75 : V) ev = mkStep layoutPieces (75 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 75 (by decide) ev; simpa using this
  have hs''E : 0 + (len (memberList (insert p s)) + 1) + 1 ≤ E := by
    calc 0 + (len (memberList (insert p s)) + 1) + 1 = len (memberList (insert p s)) + 2 := by ring
      _ ≤ 6 * D + 2 := add_le_add (le_trans hk'D (le_mul_of_one_le_left zero_le (by norm_num))) le_rfl
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
      _ ≤ E := hcap.hE
  have hSE : i₁ + (len (memberList s) + 1) + 1 ≤ E := by
    calc i₁ + (len (memberList s) + 1) + 1 = i₁ + (len (memberList s) + 2) := by ring
      _ ≤ i₁ + (8 * D + 3) := add_le_add le_rfl (add_le_add (le_trans hkD (le_mul_of_one_le_left zero_le (by norm_num))) (by norm_num))
      _ = i₁ + 8 * D + 3 := by ring
      _ ≤ E := hcap.hi
  have hipE : ip₁ + 1 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) (le_trans (add_le_add le_self_add le_rfl) hcap.hip)
  have hkE' : 0 + (2 * len (memberList (insert p s)) + 2) ≤ E := by
    calc 0 + (2 * len (memberList (insert p s)) + 2) ≤ 6 * D + 2 := by
          rw [zero_add]
          exact add_le_add (le_trans (mul_le_mul_of_nonneg_left hk'D zero_le) (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) le_rfl
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
      _ ≤ E := hcap.hE
  have hkE : i₁ + (2 * len (memberList s) + 2) ≤ E := by
    calc i₁ + (2 * len (memberList s) + 2) ≤ i₁ + (8 * D + 3) :=
          add_le_add le_rfl (add_le_add (le_trans (mul_le_mul_of_nonneg_left hkD zero_le) (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) (by norm_num))
      _ = i₁ + 8 * D + 3 := by ring
      _ ≤ E := hcap.hi
  have hosE' : ∀ j < len (memberList (insert p s)),
      mTop 0 (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T).[j] + 1 ≤ E := fun j hj ↦ by
    calc _ ≤ 0 + 6 * D + 1 + 1 := add_le_add (mTop_le htbl hW hWc T hcs hsD hj) le_rfl
      _ = 6 * D + 2 := by ring
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
      _ ≤ E := hcap.hE
  have hosE : ∀ j < len (memberList s), mTop i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[j] + 1 ≤ E :=
    fun j hj ↦ by
    calc _ ≤ i₁ + 6 * D + 1 + 1 := add_le_add (mTop_le htbl hW hWc T hs hsD' hj) le_rfl
      _ = i₁ + (6 * D + 2) := by ring
      _ ≤ i₁ + (8 * D + 3) := add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num))
      _ = i₁ + 8 * D + 3 := by ring
      _ ≤ E := hcap.hi
  -- Loop A
  obtain ⟨aok, and, aho, ash, afacts⟩ := loopA_ok htbl hP hWl hWc hWp hq hs hp hsD hcap hΓ hF _ le_rfl
  set Γ₁ := finalCtx Γ (loopA q (len (memberList (insert p s)))) with hΓ₁
  have hΓ₁f : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ aok
  have hF₁ : IdFrame walkPieces Wc T Γ₁ s p i₁ ip₁ σ := hF.zero_transport and ash
  -- the child chain is in `cp`
  have hin₁ : SubIn Γ₁ 0 (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T) (^&σ) :=
    fun j hj ↦ ⟨(hF₁.child.1 j hj).2.2.2.1, by have := afacts j hj; rwa [hq, qK'_pack, qOs'_pack, qSig_pack] at this⟩
  obtain ⟨c1ok, c1nd, c1ho, c1sh, _, c1fact⟩ := subChain_ok htbl hP hWp hΓ₁f (by simp) (termLen_fvar_le' hcap.hσ)
    hk1' hkE' hosE' (len_offVec _ _ _ _) hin₁
  set Γ₂ := finalCtx Γ₁ (subChain W 0 (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T) (^&σ)) with hΓ₂
  have hΓ₂f : IsFormulaSet LAct Γ₂ := finalCtx_isFormulaSet 8 htbl hΓ₁f c1ok
  have hF₂ : IdFrame walkPieces Wc T Γ₂ s p i₁ ip₁ σ := hF₁.zero_transport c1nd c1sh
  -- Loop B
  obtain ⟨bok, bnd, bho, bsh, bfacts⟩ := loopB_ok htbl hP hWl hWc hWp hq hs hp hsD hcap hΓ₂f hF₂ _ le_rfl
  set Γ₃ := finalCtx Γ₂ (loopB q (len (memberList s))) with hΓ₃
  have hΓ₃f : IsFormulaSet LAct Γ₃ := finalCtx_isFormulaSet 8 htbl hΓ₂f bok
  have hF₃ : IdFrame walkPieces Wc T Γ₃ s p i₁ ip₁ σ := hF₂.zero_transport bnd bsh
  -- the `p` block
  obtain ⟨pok, pnd, pho, psh, pfact⟩ := blockP_ok htbl hP hWl hWc hWp hq hs hp hsD hcap hΓ₃f hF₃
  set Γ₄ := finalCtx Γ₃ (blockP q) with hΓ₄
  have hΓ₄f : IsFormulaSet LAct Γ₄ := finalCtx_isFormulaSet 8 htbl hΓ₃f pok
  have hF₄ : IdFrame walkPieces Wc T Γ₄ s p i₁ ip₁ σ := hF₃.zero_transport pnd psh
  -- the parent chain is in `s''`
  have hin₂ : SubIn Γ₄ i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (^&(0 + (len (memberList (insert p s)) + 1))) :=
    fun j hj ↦ ⟨(hF₄.parent.1 j hj).2.2.2.1, by
      have h1 := bfacts j hj
      rw [hq, qI_pack, qK_pack, qOs_pack, qK'_pack] at h1
      exact tr_of_zero pnd psh h1⟩
  obtain ⟨c2ok, c2nd, c2ho, c2sh, _, c2fact⟩ := subChain_ok htbl hP hWp hΓ₄f (by simp) (termLen_fvar_le' hs''E)
    hk1 hkE hosE (len_offVec _ _ _ _) hin₂
  set Γ₅ := finalCtx Γ₄ (subChain W i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (^&(0 + (len (memberList (insert p s)) + 1)))) with hΓ₅
  have hΓ₅f : IsFormulaSet LAct Γ₅ := finalCtx_isFormulaSet 8 htbl hΓ₄f c2ok
  have hF₅ : IdFrame walkPieces Wc T Γ₅ s p i₁ ip₁ σ := hF₄.zero_transport c2nd c2sh
  -- the two closing steps
  obtain ⟨ok₁, tg₁, cx₁⟩ := fok_insertSubset htbl hF1 rfl hΓ₅f (by simp) (termLen_fvar_le' hSE)
    (by simp) (termLen_fvar_le' hs''E) (by simp) (termLen_fvar_le' hipE) (by simp) (termLen_fvar_le' hcap.hσ)
    c2fact (tr_of_zero c2nd c2sh pfact) hF₅.cp
  rw [← e112, ← hWp] at ok₁ tg₁ cx₁
  have hΓ₆f : IsFormulaSet LAct (insert (neg LAct (subsetFact (^&σ) (^&(0 + (len (memberList (insert p s)) + 1))))) Γ₅) := by
    rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  have hc1' : neg LAct (subsetFact (^&(0 + (len (memberList (insert p s)) + 1))) (^&σ)) ∈ Γ₅ :=
    tr_of_zero c2nd c2sh (tr_of_zero pnd psh (tr_of_zero bnd bsh c1fact))
  obtain ⟨ok₂, tg₂, cx₂⟩ := lok_subsetAntisymm htbl hL rfl hΓ₆f (by simp) (termLen_fvar_le' hcap.hσ)
    (by simp) (termLen_fvar_le' hs''E) (memInsSelf _ _) (memIns hc1')
  rw [← e75, ← hWp] at ok₂ tg₂ cx₂
  -- assembly
  have hlist : identIns q = appendV (loopA q (len (memberList (insert p s))))
      (appendV (subChain W 0 (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T) (^&σ))
        (appendV (loopB q (len (memberList s))) (appendV (blockP q)
          (appendV (subChain W i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (^&(0 + (len (memberList (insert p s)) + 1))))
            ?[mkStep W 112 ?[^&(i₁ + (len (memberList s) + 1)), ^&(0 + (len (memberList (insert p s)) + 1)), ^&ip₁, ^&σ],
              mkStep W 75 ?[^&σ, ^&(0 + (len (memberList (insert p s)) + 1))]])))) := by
    unfold identIns; rw [hq]; simp only [qWl_pack, qW_pack, qI_pack, qK_pack, qOs_pack, qXs_pack, qIp_pack, qK'_pack,
      qOs'_pack, qYs_pack, qP_pack, qSig_pack]
  rw [hlist]
  have hok : ListOK tbl E ((8 : ℕ) : V) Γ (appendV (loopA q (len (memberList (insert p s))))
      (appendV (subChain W 0 (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T) (^&σ))
        (appendV (loopB q (len (memberList s))) (appendV (blockP q)
          (appendV (subChain W i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (^&(0 + (len (memberList (insert p s)) + 1))))
            ?[mkStep W 112 ?[^&(i₁ + (len (memberList s) + 1)), ^&(0 + (len (memberList (insert p s)) + 1)), ^&ip₁, ^&σ],
              mkStep W 75 ?[^&σ, ^&(0 + (len (memberList (insert p s)) + 1))]]))))) := by
    refine listOK_appendV aok ?_
    rw [← hΓ₁]
    refine listOK_appendV c1ok ?_
    rw [← hΓ₂]
    refine listOK_appendV bok ?_
    rw [← hΓ₃]
    refine listOK_appendV pok ?_
    rw [← hΓ₄]
    refine listOK_appendV c2ok ?_
    rw [← hΓ₅]
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    exact listOK_single ok₂
  refine ⟨hok,
    noDrop_appendV and (noDrop_appendV c1nd (noDrop_appendV bnd (noDrop_appendV pnd (noDrop_appendV c2nd
      (noDrop_cons (Or.inl tg₁) (noDrop_single (Or.inl tg₂))))))),
    hornOnly_appendV aho (hornOnly_appendV c1ho (hornOnly_appendV bho (hornOnly_appendV pho (hornOnly_appendV c2ho
      (hornOnly_cons (Or.inl tg₁) (hornOnly_single (Or.inl tg₂))))))), ?_, ?_⟩
  · rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, ash, c1sh, bsh, psh, c2sh,
      shiftsV_cons_tag0 tg₁, shiftsV_single_tag0 tg₂]
    simp
  · rw [finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂, ← hΓ₃,
      ← hΓ₄, ← hΓ₅, finalCtx_cons, cx₁, finalCtx_single, cx₂]
    exact memInsSelf _ _

end identOK

/-! ## 5. The `insert` child: `proIns` (before the child) and `postIns` (after it); the `and`/`or` readings -/

section insertChild

/-- The shifts of a child's layout. -/
noncomputable def proSig (Ww Wl Wc W T c : V) : V := shiftsV (layoutSteps Ww Wl Wc W T c)

/-- **The prologue of an `insert p s` child**: `cp := insertTotalC [P, S]`, the child's layout, the identification.
`i` = the parent's chain offset, `ip` = the index of `p`'s walk dossier. -/
noncomputable def proIns (Ww Wl Wc W T s p i ip : V) : V :=
  appendV ?[mkStep W 76 ?[^&ip, ^&(i + (len (memberList s) + 1))]]
    (appendV (layoutSteps Ww Wl Wc W T (insert p s))
      (identIns (qPack Wl W (i + 1 + proSig Ww Wl Wc W T (insert p s)) (len (memberList s))
        (offVec (memberList s) Ww Wc T) (memberList s) (ip + 1 + proSig Ww Wl Wc W T (insert p s))
        (len (memberList (insert p s))) (offVec (memberList (insert p s)) Ww Wc T) (memberList (insert p s)) p
        (proSig Ww Wl Wc W T (insert p s)))))

noncomputable def proInsDef : 𝚺₁.Semisentence 10 := .mkSigma
  “y Ww Wl Wc W T s p i ip. ∃ zip, !qqFvarDef zip ip ∧ ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧
    ∃ is, is = i + (k + 1) ∧ ∃ zs, !qqFvarDef zs is ∧ ∃ e₁, !adjoinDef e₁ zs 0 ∧ ∃ e₂, !adjoinDef e₂ zip e₁ ∧
    ∃ s₁, !mkStepDef s₁ W 76 e₂ ∧ ∃ l₁, !adjoinDef l₁ s₁ 0 ∧
    ∃ c, !insertDef c p s ∧ ∃ L, !layoutStepsDef L Ww Wl Wc W T c ∧ ∃ σ, !shiftsVDef σ L ∧
    ∃ os, !offVecDef os xs Ww Wc T ∧ ∃ ys, !memberListDef ys c ∧ ∃ kk, !lenDef kk ys ∧ ∃ oss, !offVecDef oss ys Ww Wc T ∧
    ∃ i₁, i₁ = i + 1 + σ ∧ ∃ ip₁, ip₁ = ip + 1 + σ ∧
    ∃ q₁₁, !pairDef q₁₁ p σ ∧ ∃ q₁₀, !pairDef q₁₀ ys q₁₁ ∧ ∃ q₉, !pairDef q₉ oss q₁₀ ∧ ∃ q₈, !pairDef q₈ kk q₉ ∧
    ∃ q₇, !pairDef q₇ ip₁ q₈ ∧ ∃ q₆, !pairDef q₆ xs q₇ ∧ ∃ q₅, !pairDef q₅ os q₆ ∧ ∃ q₄, !pairDef q₄ k q₅ ∧
    ∃ q₃, !pairDef q₃ i₁ q₄ ∧ ∃ q₂, !pairDef q₂ W q₃ ∧ ∃ q, !pairDef q Wl q₂ ∧
    ∃ I, !identInsDef I q ∧ ∃ r, !appendVDef r L I ∧ !appendVDef y l₁ r”

set_option maxHeartbeats 1000000 in
instance proIns_defined :
    𝚺₁.DefinedFunction (fun v : Fin 9 → V ↦ proIns (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) proInsDef := .mk
  fun v ↦ by
    simp [proInsDef, proIns, proSig, qPack, memberList_defined.iff, layoutSteps_defined.iff, shiftsV_defined.iff,
      offVec_defined.iff, identIns_defined.iff, mkStep_defined.iff, appendV_defined.iff, numeral_eq_natCast]

/-- The shifts of a layout are at most `6D + 1`. -/
lemma proSig_le {tbl N Wl Wc W T c D : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (hWc : Wc = certPieces)
    {N' B' E Γ : V} (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWp : W = proPieces)
    (hc : IsFormulaSet LAct c) (hk1 : 1 ≤ len (memberList c)) (hcD : setLen LAct c ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) :
    proSig walkPieces Wl Wc W T c ≤ 6 * D + 1 := by
  obtain ⟨_, _, hsh, _, _⟩ := layoutSteps_ok htbl hP htblN hWl hWc hWp hc hk1 hcD hE hΓ
  unfold proSig
  rw [hsh]
  have hkD : len (memberList c) ≤ D := le_trans (len_memberList_le_setLen hc) hcD
  have ht : tailShift (memberList c) walkPieces Wc T ≤ 4 * D := by
    refine le_trans (tailShift_le htbl hP.walkTable hWc T _ (fun j hj ↦ hc _ (nth_memberList_mem hj))) ?_
    rw [← setLen_eq_listSum_memberList]; exact mul_le_mul_of_nonneg_left hcD zero_le
  calc tailShift (memberList c) walkPieces Wc T + (len (memberList c) + 1) + len (memberList c)
      ≤ 4 * D + (D + 1) + D := add_le_add (add_le_add ht (add_le_add hkD le_rfl)) hkD
    _ = 6 * D + 1 := by ring

set_option maxHeartbeats 4000000 in
/-- **The `insert` child's prologue is applicable**: afterwards the child's layout is at `0`, the parent's at
`i + 1 + σ`, `p`'s dossier at `ip + 1 + σ`, the row object `cp = &σ` with `insFact cp P S` and `eqFactB cp s''`
(`σ = proSig … (insert p s)`, `s'' = &(k' + 1)` the child's chain top). -/
theorem proIns_ok {tbl N N' B' Wl Wc W T s p i ip D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p) (hk1 : 1 ≤ len (memberList s))
    (hsD : setLen LAct (insert p s) ≤ D) (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : i + 14 * D + 5 ≤ E)
    (hipE : ip + 8 * D + 4 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hLay : Layout walkPieces Wc T Γ s i) (hDp : DossF walkPieces Γ 0 p ip) :
    ListOK tbl E ((8 : ℕ) : V) Γ (proIns walkPieces Wl Wc W T s p i ip) ∧ NoDrop' (proIns walkPieces Wl Wc W T s p i ip) ∧
    shiftsV (proIns walkPieces Wl Wc W T s p i ip) = 1 + proSig walkPieces Wl Wc W T (insert p s) ∧
    Layout walkPieces Wc T (finalCtx Γ (proIns walkPieces Wl Wc W T s p i ip)) (insert p s) 0 ∧
    IdFrame walkPieces Wc T (finalCtx Γ (proIns walkPieces Wl Wc W T s p i ip)) s p
      (i + 1 + proSig walkPieces Wl Wc W T (insert p s)) (ip + 1 + proSig walkPieces Wl Wc W T (insert p s))
      (proSig walkPieces Wl Wc W T (insert p s)) ∧
    neg LAct (eqFactB (^&(proSig walkPieces Wl Wc W T (insert p s))) (^&(0 + (len (memberList (insert p s)) + 1)))) ∈
      finalCtx Γ (proIns walkPieces Wl Wc W T s p i ip) := by
  have hL := hP.layoutTable
  have hcs : IsFormulaSet LAct (insert p s) := IsFormulaSet.insert_iff.mpr ⟨hp, hs⟩
  have hsD' : setLen LAct s ≤ D := le_trans (setLen_le_insert p s) hsD
  have hkD : len (memberList s) ≤ D := le_trans (len_memberList_le_setLen hs) hsD'
  have hk1' : 1 ≤ len (memberList (insert p s)) := by
    obtain ⟨hlt, _⟩ := idxOf_spec (show p ∈ insert p s by simp)
    have := lt_iff_succ_le.mp (lt_of_le_of_lt zero_le hlt); rwa [zero_add] at this
  have hE8 : 13 * D + 18 * ‖D‖ + 8 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hE
  have e76 : ∀ ev : V, mkStep proPieces (76 : V) ev = mkStep layoutPieces (76 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 76 (by decide) ev; simpa using this
  set σ := proSig walkPieces Wl Wc W T (insert p s) with hσ
  have hσle : σ ≤ 6 * D + 1 := proSig_le htbl hP hWc htblN hWl hWp hcs hk1' hsD hE8 hΓ
  have hipE1 : ip + 1 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) (le_trans (add_le_add le_self_add le_rfl) hipE)
  have hSE : i + (len (memberList s) + 1) + 1 ≤ E := by
    calc i + (len (memberList s) + 1) + 1 = i + (len (memberList s) + 2) := by ring
      _ ≤ i + (14 * D + 5) := add_le_add le_rfl (add_le_add (le_trans hkD (le_mul_of_one_le_left zero_le (by norm_num))) (by norm_num))
      _ = i + 14 * D + 5 := by ring
      _ ≤ E := hiE
  -- step 1: the insert object
  obtain ⟨ok₁, tg₁, cx₁⟩ := lok_insertTotalC htbl hL rfl hΓ (by simp) (termLen_fvar_le' hipE1) (by simp) (termLen_fvar_le' hSE)
  rw [← e76, ← hWp] at ok₁ tg₁ cx₁
  rw [Nat.cast_zero, termShift_fvar, termShift_fvar] at cx₁
  have h1sh : shiftsV (?[mkStep W 76 ?[^&ip, ^&(i + (len (memberList s) + 1))]] : V) = 1 := shiftsV_single_tag2 tg₁
  have h1nd : NoDrop' (?[mkStep W 76 ?[^&ip, ^&(i + (len (memberList s) + 1))]] : V) := noDrop'_single (Or.inr (Or.inr (Or.inl tg₁)))
  set Γ₁ := finalCtx Γ ?[mkStep W 76 ?[^&ip, ^&(i + (len (memberList s) + 1))]] with hΓ₁
  have hΓ₁e : Γ₁ = insert (neg LAct (insFact (^&0) (^&(ip + 1)) (^&(i + (len (memberList s) + 1) + 1)))) (setShift LAct Γ) := by
    rw [hΓ₁, finalCtx_single, cx₁]
  have hΓ₁f : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ (listOK_single ok₁)
  have hLay₁ : Layout walkPieces Wc T Γ₁ s (i + 1) := by have := hLay.transport h1nd; rwa [h1sh] at this
  have hDp₁ : DossF walkPieces Γ₁ 0 p (ip + 1) := by have := dossF_transport' h1nd hDp; rwa [h1sh] at this
  have hcp₁ : neg LAct (insFact (^&0) (^&(ip + 1)) (^&(i + (len (memberList s) + 1) + 1))) ∈ Γ₁ := by
    rw [hΓ₁e]; exact memInsSelf _ _
  -- step 2: the child's layout
  obtain ⟨lok, lnd, _, _, lLay⟩ := layoutSteps_ok htbl hP htblN hWl hWc hWp hcs hk1' hsD hE8 hΓ₁f
  have lsh : shiftsV (layoutSteps walkPieces Wl Wc W T (insert p s)) = σ := by rw [hσ, proSig]
  set Γ₂ := finalCtx Γ₁ (layoutSteps walkPieces Wl Wc W T (insert p s)) with hΓ₂
  have hΓ₂f : IsFormulaSet LAct Γ₂ := finalCtx_isFormulaSet 8 htbl hΓ₁f lok
  have hLay₂ : Layout walkPieces Wc T Γ₂ s (i + 1 + σ) := by have := hLay₁.transport lnd; rwa [lsh] at this
  have hDp₂ : DossF walkPieces Γ₂ 0 p (ip + 1 + σ) := by have := dossF_transport' lnd hDp₁; rwa [lsh] at this
  have hcp₂ : neg LAct (insFact (^&σ) (^&(ip + 1 + σ)) (^&(i + 1 + σ + (len (memberList s) + 1)))) ∈ Γ₂ := by
    have := mem_finalCtx_of_mem' lnd hcp₁
    rw [lsh, shiftIterV_neg (isFormula_insFact (by simp) (by simp) (by simp)), shiftIterV_insFact (by simp) (by simp) (by simp),
      termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar, zero_add] at this
    have e : i + (len (memberList s) + 1) + 1 + σ = i + 1 + σ + (len (memberList s) + 1) := by ring
    rwa [e] at this
  have hF₂ : IdFrame walkPieces Wc T Γ₂ s p (i + 1 + σ) (ip + 1 + σ) σ := ⟨lLay, hLay₂, hDp₂, hcp₂⟩
  -- step 3: the identification
  have hcap : IdCap D E (i + 1 + σ) (ip + 1 + σ) σ := ⟨hE, by
      calc i + 1 + σ + 8 * D + 3 ≤ i + 1 + (6 * D + 1) + 8 * D + 3 := add_le_add (add_le_add (add_le_add le_rfl hσle) le_rfl) le_rfl
        _ = i + 14 * D + 5 := by ring
        _ ≤ E := hiE, by
      calc ip + 1 + σ + 2 * D + 2 ≤ ip + 1 + (6 * D + 1) + 2 * D + 2 := add_le_add (add_le_add (add_le_add le_rfl hσle) le_rfl) le_rfl
        _ = ip + 8 * D + 4 := by ring
        _ ≤ E := hipE, by
      calc σ + 1 ≤ 6 * D + 1 + 1 := add_le_add hσle le_rfl
        _ = 6 * D + 2 := by ring
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
        _ ≤ E := hE⟩
  obtain ⟨iok, ind, iho, ish, ifact⟩ := identIns_ok htbl hP hWl hWc hWp rfl hs hp hk1 hsD hcap hΓ₂f hF₂
  -- assembly
  have hlist : proIns walkPieces Wl Wc W T s p i ip = appendV ?[mkStep W 76 ?[^&ip, ^&(i + (len (memberList s) + 1))]]
      (appendV (layoutSteps walkPieces Wl Wc W T (insert p s))
        (identIns (qPack Wl W (i + 1 + σ) (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s)
          (ip + 1 + σ) (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T)
          (memberList (insert p s)) p σ))) := by
    unfold proIns; rw [← hσ]
  rw [hlist]
  refine ⟨listOK_appendV (listOK_single ok₁) (by rw [← hΓ₁]; exact listOK_appendV lok (by rw [← hΓ₂]; exact iok)),
    noDrop'_appendV h1nd (noDrop'_appendV lnd ind.noDrop'), ?_, ?_, ?_, ?_⟩
  · rw [shiftsV_appendV, shiftsV_appendV, h1sh, lsh, ish, add_zero]
  · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂]
    have := lLay.transport ind.noDrop'; rwa [ish, add_zero] at this
  · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂]
    exact hF₂.zero_transport ind ish
  · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂]
    exact ifact

/-- **`postIns W s'' cp n`**: recover the child's goal (`goalElim`: `d = &1`, `n = &0`), then move
`fstIdxFact s'' d` onto the row object `cp` by `congFstIdx` (the child's chain top and `cp` are at `s'' + 2`,
`cp + 2` after the two eliminations). -/
noncomputable def postIns (W s'' cp n : V) : V :=
  appendV (goalElim (^&s'') (bnum n)) ?[mkStep W 122 ?[^&1, ^&(s'' + 2), ^&(cp + 2)]]

noncomputable def postInsDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y W s cp n. ∃ zs, !qqFvarDef zs s ∧ ∃ bn, !bnumGraph bn n ∧ ∃ G, !goalElimDef G zs bn ∧
    ∃ z1, !qqFvarDef z1 1 ∧ ∃ s2, s2 = s + 2 ∧ ∃ zs2, !qqFvarDef zs2 s2 ∧ ∃ c2, c2 = cp + 2 ∧ ∃ zc2, !qqFvarDef zc2 c2 ∧
    ∃ e₁, !adjoinDef e₁ zc2 0 ∧ ∃ e₂, !adjoinDef e₂ zs2 e₁ ∧ ∃ e₃, !adjoinDef e₃ z1 e₂ ∧ ∃ st, !mkStepDef st W 122 e₃ ∧
    ∃ l, !adjoinDef l st 0 ∧ !appendVDef y G l”

instance postIns_defined : 𝚺₁-Function₄ (postIns : V → V → V → V → V) via postInsDef := .mk fun v ↦ by
  simp [postInsDef, postIns, bnum.defined.iff, goalElim_defined.iff, mkStep_defined.iff, appendV_defined.iff,
    numeral_eq_natCast]
instance postIns_definable : 𝚺₁-Function₄ (postIns : V → V → V → V → V) := postIns_defined.to_definable

/-- **`postIns` is applicable** and leaves the child's four facts on the row object: `derFact &1`,
`fstIdxFact &(cp + 2) &1`, `dlenFact &1 &0`, `leFact &0 (bnum n)`. -/
theorem postIns_ok {tbl N W s'' cp n E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (hWp : W = proPieces)
    (hΓ : IsFormulaSet LAct Γ) (hsE : s'' + 3 ≤ E) (hcE : cp + 3 ≤ E)
    (hg : neg LAct (goalFact (^&s'') (bnum n)) ∈ Γ) (heq : neg LAct (eqFactB (^&cp) (^&s'')) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (postIns W s'' cp n) ∧ NoDrop' (postIns W s'' cp n) ∧
    shiftsV (postIns W s'' cp n) = 2 ∧ len (postIns W s'' cp n) = 6 ∧
    neg LAct (derFact (^&1 : V)) ∈ finalCtx Γ (postIns W s'' cp n) ∧
    neg LAct (fstIdxFact (^&(cp + 2)) (^&1)) ∈ finalCtx Γ (postIns W s'' cp n) ∧
    neg LAct (dlenFact (^&1 : V) (^&0)) ∈ finalCtx Γ (postIns W s'' cp n) ∧
    neg LAct (leFact (^&0) (bnum n)) ∈ finalCtx Γ (postIns W s'' cp n) := by
  have hF1 := hP.frag1Table
  have e122 : ∀ ev : V, mkStep proPieces (122 : V) ev = mkStep frag1Pieces (122 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag1 122 (by decide) ev; simpa using this
  have hE2 : (2 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hsE)
  obtain ⟨gok, gnd, gsh, _, gd, gf, gn, gl⟩ := goalElim_ok 8 htbl hΓ (by simp) (isSemiterm_bnum0 n) hg
  rw [termShift_fvar, termShift_fvar, add_assoc, one_add_one_eq_two] at gf
  rw [termShift_bnum, termShift_bnum] at gl
  set Γg := finalCtx Γ (goalElim (^&s'') (bnum n)) with hΓg
  have hΓgf : IsFormulaSet LAct Γg := finalCtx_isFormulaSet 8 htbl hΓ gok
  have heq' : neg LAct (eqFactB (^&(cp + 2)) (^&(s'' + 2))) ∈ Γg := by
    have hf : IsFormula LAct (eqFactB (^&cp) (^&s'')) := isFormula_eqFact (by simp) (by simp)
    have := mem_finalCtx_of_mem' gnd heq
    rw [gsh, shiftIterV_neg hf, shiftIterV_eqFactB (by simp) (by simp), termShiftIterV_fvar, termShiftIterV_fvar] at this
    exact this
  obtain ⟨ok₁, tg₁, cx₁⟩ := fok_congFstIdx htbl hF1 rfl hΓgf (by simp) (termLen_fvar_le' (le_trans (by norm_num) hE2))
    (by simp) (termLen_fvar_le' (by rw [add_assoc, show (2 : V) + 1 = 3 by norm_num]; exact hsE))
    (by simp) (termLen_fvar_le' (by rw [add_assoc, show (2 : V) + 1 = 3 by norm_num]; exact hcE)) heq' gf
  rw [← e122, ← hWp] at ok₁ tg₁ cx₁
  refine ⟨listOK_appendV gok (by rw [← hΓg]; exact listOK_single ok₁), noDrop'_appendV gnd (noDrop'_single (Or.inl tg₁)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold postIns; rw [shiftsV_appendV, gsh, shiftsV_single_tag0 tg₁, add_zero]
  · unfold postIns; rw [len_appendV, len_goalElim, len_vec1]; norm_num
  · unfold postIns; rw [finalCtx_appendV, ← hΓg, finalCtx_single, cx₁]; exact memIns gd
  · unfold postIns; rw [finalCtx_appendV, ← hΓg, finalCtx_single, cx₁]; exact memInsSelf _ _
  · unfold postIns; rw [finalCtx_appendV, ← hΓg, finalCtx_single, cx₁]; exact memIns gn
  · unfold postIns; rw [finalCtx_appendV, ← hΓg, finalCtx_single, cx₁]; exact memIns gl

/-! ### 5.1 The `and`/`or` readings: the principal member's shape and its sub-formulas' dossiers -/

/-- With `r = p ⋏ q ∈ s`, the layout gives `andFact &ir &ip &iq`, the dossiers of `p`/`q` at `ip`/`iq` and
`memFact &ir &is` — the `nodeAnd_ok` hypotheses `hand`/`hmr` and the two `proIns` inputs. -/
theorem layout_and {tbl N Wc T s p q Γ i : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (hp : IsSemiformula LAct 0 p) (hq : IsSemiformula LAct 0 q) (hr : (p ^⋏ q) ∈ s)
    (hLay : Layout walkPieces Wc T Γ s i) :
    neg LAct (andFact (^&(memTop walkPieces Wc T s (p ^⋏ q) i))
      (^&(memTop walkPieces Wc T s (p ^⋏ q) i + descCountF walkPieces 0 q + 1))
      (^&(memTop walkPieces Wc T s (p ^⋏ q) i + 1))) ∈ Γ ∧
    DossF walkPieces Γ 0 p (memTop walkPieces Wc T s (p ^⋏ q) i + descCountF walkPieces 0 q + 1) ∧
    DossF walkPieces Γ 0 q (memTop walkPieces Wc T s (p ^⋏ q) i + 1) ∧
    neg LAct (memFact (^&(memTop walkPieces Wc T s (p ^⋏ q) i)) (^&(i + (len (memberList s) + 1)))) ∈ Γ := by
  obtain ⟨hD, _, _, hm⟩ := hLay.member hr
  obtain ⟨h1, _, hq', hp'⟩ := dossF_and htbl hP.walkTable rfl hp hq hD
  exact ⟨h1, hp', hq', hm⟩

/-- With `r = p ⋎ q ∈ s`, likewise (`nodeOr_ok`'s `hor`/`hmr`). -/
theorem layout_or {tbl N Wc T s p q Γ i : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (hp : IsSemiformula LAct 0 p) (hq : IsSemiformula LAct 0 q) (hr : (p ^⋎ q) ∈ s)
    (hLay : Layout walkPieces Wc T Γ s i) :
    neg LAct (orFact (^&(memTop walkPieces Wc T s (p ^⋎ q) i))
      (^&(memTop walkPieces Wc T s (p ^⋎ q) i + descCountF walkPieces 0 q + 1))
      (^&(memTop walkPieces Wc T s (p ^⋎ q) i + 1))) ∈ Γ ∧
    DossF walkPieces Γ 0 p (memTop walkPieces Wc T s (p ^⋎ q) i + descCountF walkPieces 0 q + 1) ∧
    DossF walkPieces Γ 0 q (memTop walkPieces Wc T s (p ^⋎ q) i + 1) ∧
    neg LAct (memFact (^&(memTop walkPieces Wc T s (p ^⋎ q) i)) (^&(i + (len (memberList s) + 1)))) ∈ Γ := by
  obtain ⟨hD, _, _, hm⟩ := hLay.member hr
  obtain ⟨h1, _, hq', hp'⟩ := dossF_or htbl hP.walkTable rfl hp hq hD
  exact ⟨h1, hp', hq', hm⟩

end insertChild

/-! ## 6. The `cut` prefix: the cut formula and its negation, walked and certified (`DESIGN_fragments.md` §4.9) -/

section cutPrefix

/-- **`proCutPre p`**: the member block of `p`, the member block of `neg p`, then `certNeg` (re-indexed). Afterwards
`p`'s dossier is at `mLen p + mShift (neg p)`, `neg p`'s at `mLen (neg p)`, and `negFact X_np X_p` holds. -/
noncomputable def proCutPre (Ww Wc T p : V) : V :=
  appendV (memberBlock Ww Wc T p) (appendV (memberBlock Ww Wc T (neg LAct p))
    (reidxL (certNeg Wc 0 p (mLen Wc T p + mShift Ww Wc T (neg LAct p)) (mLen Wc T (neg LAct p)))))

noncomputable def proCutPreDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y Ww Wc T p. ∃ b₁, !memberBlockDef b₁ Ww Wc T p ∧ ∃ np, !(negGraph LAct) np p ∧ ∃ b₂, !memberBlockDef b₂ Ww Wc T np ∧
    ∃ lp, !mLenDef lp Wc T p ∧ ∃ mn, !mShiftDef mn Ww Wc T np ∧ ∃ ip, ip = lp + mn ∧ ∃ inp, !mLenDef inp Wc T np ∧
    ∃ c, !passFDef c Wc 1 0 p ip inp ∧ ∃ r, !reidxLDef r c ∧ ∃ a, !appendVDef a b₂ r ∧ !appendVDef y b₁ a”

instance proCutPre_defined : 𝚺₁-Function₄ (proCutPre : V → V → V → V → V) via proCutPreDef := .mk fun v ↦ by
  simp [proCutPreDef, proCutPre, certNeg, memberBlock_defined.iff, neg.defined.iff, mLen_defined.iff, mShift_defined.iff,
    passF_defined.iff, reidxL_defined.iff, appendV_defined.iff, numeral_eq_natCast]
instance proCutPre_definable : 𝚺₁-Function₄ (proCutPre : V → V → V → V → V) := proCutPre_defined.to_definable

set_option maxHeartbeats 2000000 in
/-- **The `cut` prefix is applicable**: it leaves the two dossiers, their `piFact`/`lenFact`, and `negFact X_np X_p`. -/
theorem proCutPre_ok {tbl N N' B' Wc T p D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWc : Wc = certPieces)
    (hp : IsSemiformula LAct 0 p) (hpD : formulaLen LAct p ≤ D) (hnpD : formulaLen LAct (neg LAct p) ≤ D)
    (hE : 13 * D + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (proCutPre walkPieces Wc T p) ∧ NoDrop' (proCutPre walkPieces Wc T p) ∧
    shiftsV (proCutPre walkPieces Wc T p) = mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) ∧
    DossF walkPieces (finalCtx Γ (proCutPre walkPieces Wc T p)) 0 p (mLen Wc T p + mShift walkPieces Wc T (neg LAct p)) ∧
    neg LAct (lenFact (bnum (formulaLen LAct p)) (^&(mLen Wc T p + mShift walkPieces Wc T (neg LAct p)))) ∈
      finalCtx Γ (proCutPre walkPieces Wc T p) ∧
    DossF walkPieces (finalCtx Γ (proCutPre walkPieces Wc T p)) 0 (neg LAct p) (mLen Wc T (neg LAct p)) ∧
    neg LAct (lenFact (bnum (formulaLen LAct (neg LAct p))) (^&(mLen Wc T (neg LAct p)))) ∈
      finalCtx Γ (proCutPre walkPieces Wc T p) ∧
    neg LAct (negFact (^&(mLen Wc T (neg LAct p))) (^&(mLen Wc T p + mShift walkPieces Wc T (neg LAct p)))) ∈
      finalCtx Γ (proCutPre walkPieces Wc T p) := by
  have hW := hP.walkTable
  have hC := hP.certTable
  have htblC := hP.tableOK_certView htbl
  have hnp : IsSemiformula LAct 0 (neg LAct p) := hp.neg
  -- block of `p`
  obtain ⟨b1ok, b1nd, b1sh, _, b1D, _, b1ln⟩ := memberBlock_ok htbl hP htblN hWc hp hpD hE hΓ
  set Γ₁ := finalCtx Γ (memberBlock walkPieces Wc T p) with hΓ₁
  have hΓ₁f : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ b1ok
  -- block of `neg p`
  obtain ⟨b2ok, b2nd, b2sh, _, b2D, _, b2ln⟩ := memberBlock_ok htbl hP htblN hWc hnp hnpD hE hΓ₁f
  set Γ₂ := finalCtx Γ₁ (memberBlock walkPieces Wc T (neg LAct p)) with hΓ₂
  have hΓ₂f : IsFormulaSet LAct Γ₂ := finalCtx_isFormulaSet 8 htbl hΓ₁f b2ok
  have hD₁ : DossF walkPieces Γ₂ 0 p (mLen Wc T p + mShift walkPieces Wc T (neg LAct p)) := by
    have := dossF_transport' b2nd b1D; rwa [b2sh] at this
  have hln₁ : neg LAct (lenFact (bnum (formulaLen LAct p)) (^&(mLen Wc T p + mShift walkPieces Wc T (neg LAct p)))) ∈ Γ₂ := by
    have := mem_finalCtx_of_mem' b2nd b1ln
    rwa [b2sh, shiftIterV_neg (isFormula_lenFact (isSemiterm_bnum0 _) (by simp)),
      shiftIterV_lenFact (isSemiterm_bnum0 _) (by simp), termShiftIterV_bnum', termShiftIterV_fvar] at this
  -- the certification
  have hml : mLen Wc T p ≤ 2 * D := le_trans le_self_add (le_trans (mLen_succ_le hWc T hp) (mul_le_mul_of_nonneg_left hpD zero_le))
  have hmn : mLen Wc T (neg LAct p) ≤ 2 * D :=
    le_trans le_self_add (le_trans (mLen_succ_le hWc T hnp) (mul_le_mul_of_nonneg_left hnpD zero_le))
  have hms : mShift walkPieces Wc T (neg LAct p) ≤ 4 * D := le_trans (mShift_le htbl hW hWc T hnp) (mul_le_mul_of_nonneg_left hnpD zero_le)
  have h2p : 2 * formulaLen LAct p ≤ 2 * D := mul_le_mul_of_nonneg_left hpD zero_le
  have hE1 : 2 * (0 : V) + 2 * formulaLen LAct p + 8 ≤ E := by
    rw [mul_zero, zero_add]
    exact le_trans (add_le_add (le_trans h2p (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) le_rfl) hE
  have hEi : mLen Wc T p + mShift walkPieces Wc T (neg LAct p) + 2 * formulaLen LAct p + 1 ≤ E := by
    calc mLen Wc T p + mShift walkPieces Wc T (neg LAct p) + 2 * formulaLen LAct p + 1 ≤ 2 * D + 4 * D + 2 * D + 1 :=
          add_le_add (add_le_add (add_le_add hml hms) h2p) le_rfl
      _ = 8 * D + 1 := by ring
      _ ≤ 13 * D + 8 := add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num)
      _ ≤ E := hE
  have hEj : mLen Wc T (neg LAct p) + 2 * formulaLen LAct p + 1 ≤ E := by
    calc mLen Wc T (neg LAct p) + 2 * formulaLen LAct p + 1 ≤ 2 * D + 2 * D + 1 := add_le_add (add_le_add hmn h2p) le_rfl
      _ = 4 * D + 1 := by ring
      _ ≤ 13 * D + 8 := add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num)
      _ ≤ E := hE
  obtain ⟨cok, cnd, cho, csh, cfact⟩ := certNeg_ok htblC hC rfl hWc hp hE1 hEi hEj hΓ₂f hD₁ b2D
  have tr : ∀ x ∈ Γ₂, x ∈ finalCtx Γ₂ (reidxL (certNeg Wc 0 p (mLen Wc T p + mShift walkPieces Wc T (neg LAct p)) (mLen Wc T (neg LAct p)))) :=
    fun x hx ↦ by rw [finalCtx_reidxL]; exact tr_of_zero cnd csh hx
  refine ⟨listOK_appendV b1ok (by rw [← hΓ₁]; exact listOK_appendV b2ok (by rw [← hΓ₂]; exact listOK_reidxL hP cok)),
    noDrop'_appendV b1nd (noDrop'_appendV b2nd (noDrop'_reidxL cnd.noDrop')), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold proCutPre; rw [shiftsV_appendV, shiftsV_appendV, b1sh, b2sh, shiftsV_reidxL, csh, add_zero]
  · unfold proCutPre; rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂, finalCtx_reidxL]
    have := dossF_transport cnd hD₁; rwa [csh, add_zero] at this
  · unfold proCutPre; rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂]; exact tr _ hln₁
  · unfold proCutPre; rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂, finalCtx_reidxL]
    have := dossF_transport cnd b2D; rwa [csh, add_zero] at this
  · unfold proCutPre; rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂]; exact tr _ b2ln
  · unfold proCutPre; rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂, finalCtx_reidxL]; exact cfact

end cutPrefix

/-! ## 7. The `wk` child: every child member is in the parent's sequent, `subsetFact s'' S` (`DESIGN_fragments.md` §4.7) -/

section wkChild

/-- Loop W, child member `j`: `eqSteps Y_j X_{j'}`, `congMem [X_{j'}, Y_j, S]` → `memFact Y_j S` (the frame `q` with
`ys` the members of the CHILD `c ⊆ s`; `qIp`/`qP`/`qSig` unused). -/
noncomputable def blockW (q j : V) : V :=
  appendV (eqSteps (qWl q) (mTop 0 (qK' q) (qOs' q).[j]) (mTop (qI q) (qK q) (qOs q).[idxOf (qXs q) (qYs q).[j]]) (qYs q).[j])
    ?[mkStep (qW q) 62 ?[^&(mTop (qI q) (qK q) (qOs q).[idxOf (qXs q) (qYs q).[j]]), ^&(mTop 0 (qK' q) (qOs' q).[j]),
      ^&(qI q + (qK q + 1))]]

noncomputable def blockWDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y q j. ∃ Wl, !pi₁Def Wl q ∧ ∃ r1, !pi₂Def r1 q ∧ ∃ W, !pi₁Def W r1 ∧ ∃ r2, !pi₂Def r2 r1 ∧ ∃ i, !pi₁Def i r2 ∧ ∃ r3, !pi₂Def r3 r2 ∧ ∃ k, !pi₁Def k r3 ∧ ∃ r4, !pi₂Def r4 r3 ∧ ∃ os, !pi₁Def os r4 ∧ ∃ r5, !pi₂Def r5 r4 ∧ ∃ xs, !pi₁Def xs r5 ∧ ∃ r6, !pi₂Def r6 r5 ∧ ∃ ip, !pi₁Def ip r6 ∧ ∃ r7, !pi₂Def r7 r6 ∧ ∃ kk, !pi₁Def kk r7 ∧ ∃ r8, !pi₂Def r8 r7 ∧ ∃ oss, !pi₁Def oss r8 ∧ ∃ r9, !pi₂Def r9 r8 ∧ ∃ ys, !pi₁Def ys r9 ∧ ∃ r10, !pi₂Def r10 r9 ∧ ∃ p, !pi₁Def p r10 ∧ ∃ sg, !pi₂Def sg r10 ∧
    ∃ yj, !nthDef yj ys j ∧ ∃ oj, !nthDef oj oss j ∧ ∃ tj, tj = 0 + (2 * kk + 1 + oj) ∧ ∃ zj, !qqFvarDef zj tj ∧
    ∃ jp, !idxOfDef jp xs yj ∧ ∃ oo, !nthDef oo os jp ∧ ∃ tx, tx = i + (2 * k + 1 + oo) ∧ ∃ zx, !qqFvarDef zx tx ∧
    ∃ is, is = i + (k + 1) ∧ ∃ zs, !qqFvarDef zs is ∧
    ∃ e, !eqStepsDef e Wl tj tx yj ∧
    ∃ b₁, !adjoinDef b₁ zs 0 ∧ ∃ b₂, !adjoinDef b₂ zj b₁ ∧ ∃ b₃, !adjoinDef b₃ zx b₂ ∧ ∃ s₂, !mkStepDef s₂ W 62 b₃ ∧
    ∃ l₁, !adjoinDef l₁ s₂ 0 ∧ !appendVDef y e l₁”

set_option maxHeartbeats 1000000 in
instance blockW_defined : 𝚺₁-Function₂ (blockW : V → V → V) via blockWDef := .mk fun v ↦ by
  simp [blockWDef, blockW, qWl, qW, qI, qK, qOs, qXs, qIp, qK', qOs', qYs, qP, qSig, mTop, eqSteps_defined'.iff,
    idxOf_defined.iff, mkStep_defined.iff, appendV_defined.iff, numeral_eq_natCast]
instance blockW_definable : 𝚺₁-Function₂ (blockW : V → V → V) := blockW_defined.to_definable

namespace LoopW

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y q. y = 0”
  succ := .mkSigma “y ih j q. ∃ b, !blockWDef b q j ∧ !appendVDef y ih b”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 0
  succ := fun v j ih ↦ appendV ih (blockW (v 0) j)
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, blockW_defined.iff, appendV_defined.iff]

end LoopW

noncomputable def loopW (q m : V) : V := LoopW.construction.result ![q] m

@[simp] lemma loopW_zero (q : V) : loopW q 0 = 0 := by simp [loopW, LoopW.construction]
lemma loopW_succ (q m : V) : loopW q (m + 1) = appendV (loopW q m) (blockW q m) := by simp [loopW, LoopW.construction]

noncomputable def loopWDef : 𝚺₁.Semisentence 3 := LoopW.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance loopW_defined : 𝚺₁-Function₂ (loopW : V → V → V) via loopWDef := .mk
  fun v ↦ by simp [LoopW.construction.result_defined_iff, loopWDef]; rfl
instance loopW_definable : 𝚺₁-Function₂ (loopW : V → V → V) := loopW_defined.to_definable

/-- Loop W's invariant. -/
def WOut (tbl E q Γ m : V) : Prop :=
  ListOK tbl E ((8 : ℕ) : V) Γ (loopW q m) ∧ NoDrop (loopW q m) ∧ HornOnly (loopW q m) ∧ shiftsV (loopW q m) = 0 ∧
  ∀ j < m, neg LAct (memFact (^&(mTop 0 (qK' q) (qOs' q).[j])) (^&(qI q + (qK q + 1)))) ∈ finalCtx Γ (loopW q m)

set_option maxHeartbeats 1000000 in
instance wOut_definable : 𝚫₁-Relation₅ (WOut : V → V → V → V → V → Prop) := by
  unfold WOut qI qK qK' qOs' mTop; definability

set_option maxHeartbeats 4000000 in
/-- **Loop W is applicable**: every member of the child `c ⊆ s` is in the parent's sequent object `S`. -/
theorem loopW_ok {tbl N Wl W Wc T s c i₁ D E Γ q : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hq : q = qPack Wl W i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) 0
      (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) 0 0)
    (hs : IsFormulaSet LAct s) (hc : c ⊆ s) (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hi : i₁ + 8 * D + 3 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hCL : Layout walkPieces Wc T Γ c 0) (hPL : Layout walkPieces Wc T Γ s i₁) :
    ∀ m ≤ len (memberList c), WOut tbl E q Γ m := by
  have hW := hP.walkTable
  have hL := hP.layoutTable
  have hcs : IsFormulaSet LAct c := fun x hx ↦ hs x (hc hx)
  have hkD : len (memberList s) ≤ D := le_trans (len_memberList_le_setLen hs) hsD
  have e62 : ∀ ev : V, mkStep proPieces (62 : V) ev = mkStep layoutPieces (62 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 62 (by decide) ev; simpa using this
  have hSE : i₁ + (len (memberList s) + 1) + 1 ≤ E := by
    calc i₁ + (len (memberList s) + 1) + 1 = i₁ + (len (memberList s) + 2) := by ring
      _ ≤ i₁ + (8 * D + 3) := add_le_add le_rfl (add_le_add (le_trans hkD (le_mul_of_one_le_left zero_le (by norm_num))) (by norm_num))
      _ = i₁ + 8 * D + 3 := by ring
      _ ≤ E := hi
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    exact ⟨by rw [loopW_zero]; exact listOK_nil _ _ _ _, by rw [loopW_zero]; exact noDrop_nil,
      by rw [loopW_zero]; exact hornOnly_nil, by rw [loopW_zero, shiftsV_nil], fun j hj ↦ absurd hj (by simp)⟩
  | succ m ih =>
    intro hm
    obtain ⟨wok, wnd, who, wsh, wfacts⟩ := ih (le_trans le_self_add hm)
    have hmk : m < len (memberList c) := lt_of_lt_of_le (lt_add_one m) hm
    set Γm := finalCtx Γ (loopW q m) with hΓm
    have hΓmf : IsFormulaSet LAct Γm := finalCtx_isFormulaSet 8 htbl hΓ wok
    have tr : ∀ x ∈ Γ, x ∈ Γm := fun x hx ↦ tr_of_zero wnd wsh hx
    have hyc : (memberList c).[m] ∈ c := nth_memberList_mem hmk
    have hys : (memberList c).[m] ∈ s := hc hyc
    have hyf : IsSemiformula LAct 0 (memberList c).[m] := hcs _ hyc
    have hyD : formulaLen LAct (memberList c).[m] ≤ D := le_trans (formulaLen_le_setLen_of_mem hyc) hcD
    obtain ⟨hDy, _, _, _, _, _⟩ := hCL.1 m hmk
    have hYD := (dossierAt_of_dossF htbl hW rfl hyf hDy).mono tr
    obtain ⟨hDx, _, _, hmx⟩ := hPL.member hys
    have hXD := (dossierAt_of_dossF htbl hW rfl hyf hDx).mono tr
    unfold memTop at hmx hXD
    have hYle := mTop_le htbl hW hWc T hcs hcD hmk (i := 0)
    obtain ⟨hlt', _⟩ := idxOf_spec hys
    have hXle := mTop_le htbl hW hWc T hs hsD hlt' (i := i₁)
    have hcnt : eqCount (memberList c).[m] + 1 ≤ 2 * D :=
      le_trans (eqCount_succ_le htbl hW hyf) (mul_le_mul_of_nonneg_left hyD zero_le)
    have hEy : 2 * (0 + formulaLen LAct (memberList c).[m]) + 12 ≤ E := by
      rw [zero_add]
      calc 2 * formulaLen LAct (memberList c).[m] + 12 ≤ 2 * D + 12 := add_le_add (mul_le_mul_of_nonneg_left hyD zero_le) le_rfl
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := add_le_add (le_trans (mul_le_mul_of_nonneg_right (by norm_num) zero_le) le_self_add) le_rfl
        _ ≤ E := hE
    have hEY : mTop 0 (len (memberList c)) (offVec (memberList c) walkPieces Wc T).[m] + eqCount (memberList c).[m] + 1 ≤ E := by
      calc _ ≤ (0 + 6 * D + 1) + 2 * D := by rw [add_assoc]; exact add_le_add hYle hcnt
        _ = 8 * D + 1 := by ring
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := eight_le_cap (by norm_num)
        _ ≤ E := hE
    have hEX : mTop i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) (memberList c).[m]] +
        eqCount (memberList c).[m] + 1 ≤ E := by
      calc _ ≤ (i₁ + 6 * D + 1) + 2 * D := by rw [add_assoc]; exact add_le_add hXle hcnt
        _ = i₁ + 8 * D + 1 := by ring
        _ ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hi
    have hYE : mTop 0 (len (memberList c)) (offVec (memberList c) walkPieces Wc T).[m] + 1 ≤ E := by
      calc _ ≤ 0 + 6 * D + 1 + 1 := add_le_add hYle le_rfl
        _ = 6 * D + 2 := by ring
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
        _ ≤ E := hE
    have hXE : mTop i₁ (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) (memberList c).[m]] + 1 ≤ E := by
      calc _ ≤ i₁ + 6 * D + 1 + 1 := add_le_add hXle le_rfl
        _ = i₁ + (6 * D + 2) := by ring
        _ ≤ i₁ + (8 * D + 3) := add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num))
        _ = i₁ + 8 * D + 3 := by ring
        _ ≤ E := hi
    rw [WOut, loopW_succ]
    have key : ListOK tbl E ((8 : ℕ) : V) Γm (blockW q m) ∧ NoDrop (blockW q m) ∧ HornOnly (blockW q m) ∧
        shiftsV (blockW q m) = 0 ∧
        neg LAct (memFact (^&(mTop 0 (qK' q) (qOs' q).[m])) (^&(qI q + (qK q + 1)))) ∈ finalCtx Γm (blockW q m) := by
      subst hq
      simp only [qWl_pack, qW_pack, qI_pack, qK_pack, qOs_pack, qXs_pack, qIp_pack, qK'_pack, qOs'_pack, qYs_pack,
        qP_pack, qSig_pack]
      unfold blockW
      simp only [qWl_pack, qW_pack, qI_pack, qK_pack, qOs_pack, qXs_pack, qIp_pack, qK'_pack, qOs'_pack, qYs_pack,
        qP_pack, qSig_pack]
      obtain ⟨eok, end_, eho, esh, _, efact⟩ := eqSteps_ok htbl hL hWl rfl hyf hEy hEY hEX hΓmf hYD hXD
      set Γe := finalCtx Γm (eqSteps Wl _ _ _) with hΓe
      have hΓef : IsFormulaSet LAct Γe := finalCtx_isFormulaSet 8 htbl hΓmf eok
      have tre : ∀ x ∈ Γm, x ∈ Γe := fun x hx ↦ tr_of_zero end_ esh hx
      obtain ⟨ok₁, tg₁, cx₁⟩ := lok_congMem htbl hL rfl hΓef (by simp) (termLen_fvar_le' hXE)
        (by simp) (termLen_fvar_le' hYE) (by simp) (termLen_fvar_le' hSE) efact (tre _ (tr _ hmx))
      rw [← e62, ← hWp] at ok₁ tg₁ cx₁
      refine ⟨listOK_appendV eok (listOK_single ok₁), noDrop_appendV end_ (noDrop_single (Or.inl tg₁)),
        hornOnly_appendV eho (hornOnly_single (Or.inl tg₁)),
        by rw [shiftsV_appendV, esh, shiftsV_single_tag0 tg₁, add_zero], ?_⟩
      rw [finalCtx_appendV, ← hΓe, finalCtx_single, cx₁]
      exact memInsSelf _ _
    obtain ⟨bok, bnd, bho, bsh, bfact⟩ := key
    refine ⟨listOK_appendV wok (by rw [← hΓm]; exact bok), noDrop_appendV wnd bnd, hornOnly_appendV who bho,
      by rw [shiftsV_appendV, wsh, bsh, add_zero], fun j hj ↦ ?_⟩
    rw [finalCtx_appendV, ← hΓm]
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hj) with h | rfl
    · exact tr_of_zero bnd bsh (wfacts j h)
    · exact bfact

/-- **`proWk c`**: the child's layout, Loop W, then the child chain's subset fold against `S` — the `nodeWk_ok`
hypothesis `subsetFact &ic &is` with `ic = &(k' + 1)`, `is = &(i + σ + (k + 1))`. -/
noncomputable def proWk (Ww Wl Wc W T s c i : V) : V :=
  appendV (layoutSteps Ww Wl Wc W T c)
    (appendV (loopW (qPack Wl W (i + proSig Ww Wl Wc W T c) (len (memberList s)) (offVec (memberList s) Ww Wc T)
        (memberList s) 0 (len (memberList c)) (offVec (memberList c) Ww Wc T) (memberList c) 0 0) (len (memberList c)))
      (subChain W 0 (len (memberList c)) (offVec (memberList c) Ww Wc T) (^&(i + proSig Ww Wl Wc W T c + (len (memberList s) + 1)))))

noncomputable def proWkDef : 𝚺₁.Semisentence 9 := .mkSigma
  “y Ww Wl Wc W T s c i. ∃ L, !layoutStepsDef L Ww Wl Wc W T c ∧ ∃ σ, !shiftsVDef σ L ∧ ∃ i₁, i₁ = i + σ ∧
    ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧ ∃ os, !offVecDef os xs Ww Wc T ∧
    ∃ ys, !memberListDef ys c ∧ ∃ kk, !lenDef kk ys ∧ ∃ oss, !offVecDef oss ys Ww Wc T ∧
    ∃ q₁₁, !pairDef q₁₁ 0 0 ∧ ∃ q₁₀, !pairDef q₁₀ ys q₁₁ ∧ ∃ q₉, !pairDef q₉ oss q₁₀ ∧ ∃ q₈, !pairDef q₈ kk q₉ ∧
    ∃ q₇, !pairDef q₇ 0 q₈ ∧ ∃ q₆, !pairDef q₆ xs q₇ ∧ ∃ q₅, !pairDef q₅ os q₆ ∧ ∃ q₄, !pairDef q₄ k q₅ ∧
    ∃ q₃, !pairDef q₃ i₁ q₄ ∧ ∃ q₂, !pairDef q₂ W q₃ ∧ ∃ q, !pairDef q Wl q₂ ∧
    ∃ A, !loopWDef A q kk ∧ ∃ is, is = i₁ + (k + 1) ∧ ∃ zs, !qqFvarDef zs is ∧ ∃ C, !subChainDef C W 0 kk oss zs ∧
    ∃ r, !appendVDef r A C ∧ !appendVDef y L r”

set_option maxHeartbeats 1000000 in
instance proWk_defined :
    𝚺₁.DefinedFunction (fun v : Fin 8 → V ↦ proWk (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) proWkDef := .mk
  fun v ↦ by
    simp [proWkDef, proWk, proSig, qPack, layoutSteps_defined.iff, shiftsV_defined.iff, memberList_defined.iff,
      offVec_defined.iff, loopW_defined.iff, subChain_defined.iff, appendV_defined.iff, numeral_eq_natCast]

set_option maxHeartbeats 4000000 in
/-- **The `wk` child's prologue is applicable**: afterwards the child's layout is at `0`, the parent's at `i + σ`,
and `subsetFact &(k' + 1) &(i + σ + (k + 1))` holds (`σ = proSig … c`). -/
theorem proWk_ok {tbl N N' B' Wl Wc W T s c i D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hs : IsFormulaSet LAct s) (hc : c ⊆ s) (hk1 : 1 ≤ len (memberList c))
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D) (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : i + 14 * D + 5 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s i) :
    ListOK tbl E ((8 : ℕ) : V) Γ (proWk walkPieces Wl Wc W T s c i) ∧ NoDrop' (proWk walkPieces Wl Wc W T s c i) ∧
    shiftsV (proWk walkPieces Wl Wc W T s c i) = proSig walkPieces Wl Wc W T c ∧
    Layout walkPieces Wc T (finalCtx Γ (proWk walkPieces Wl Wc W T s c i)) c 0 ∧
    Layout walkPieces Wc T (finalCtx Γ (proWk walkPieces Wl Wc W T s c i)) s (i + proSig walkPieces Wl Wc W T c) ∧
    neg LAct (subsetFact (^&(0 + (len (memberList c) + 1)))
      (^&(i + proSig walkPieces Wl Wc W T c + (len (memberList s) + 1)))) ∈ finalCtx Γ (proWk walkPieces Wl Wc W T s c i) := by
  have hW := hP.walkTable
  have hcs : IsFormulaSet LAct c := fun x hx ↦ hs x (hc hx)
  have hkD : len (memberList s) ≤ D := le_trans (len_memberList_le_setLen hs) hsD
  have hk'D : len (memberList c) ≤ D := le_trans (len_memberList_le_setLen hcs) hcD
  have hE8 : 13 * D + 18 * ‖D‖ + 8 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hE
  set σ := proSig walkPieces Wl Wc W T c with hσ
  have hσle : σ ≤ 6 * D + 1 := proSig_le htbl hP hWc htblN hWl hWp hcs hk1 hcD hE8 hΓ
  have hi : i + σ + 8 * D + 3 ≤ E := by
    calc i + σ + 8 * D + 3 ≤ i + (6 * D + 1) + 8 * D + 3 := add_le_add (add_le_add (add_le_add le_rfl hσle) le_rfl) le_rfl
      _ = i + 14 * D + 4 := by ring
      _ ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hiE
  -- the child's layout
  obtain ⟨lok, lnd, _, _, lLay⟩ := layoutSteps_ok htbl hP htblN hWl hWc hWp hcs hk1 hcD hE8 hΓ
  have lsh : shiftsV (layoutSteps walkPieces Wl Wc W T c) = σ := by rw [hσ, proSig]
  set Γ₁ := finalCtx Γ (layoutSteps walkPieces Wl Wc W T c) with hΓ₁
  have hΓ₁f : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ lok
  have hLay₁ : Layout walkPieces Wc T Γ₁ s (i + σ) := by have := hLay.transport lnd; rwa [lsh] at this
  -- Loop W
  obtain ⟨wok, wnd, who, wsh, wfacts⟩ := loopW_ok htbl hP hWl hWc hWp rfl hs hc hsD hcD hE hi hΓ₁f lLay hLay₁ _ le_rfl
  set Γ₂ := finalCtx Γ₁ (loopW (qPack Wl W (i + σ) (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) 0
    (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) 0 0) (len (memberList c))) with hΓ₂
  have hΓ₂f : IsFormulaSet LAct Γ₂ := finalCtx_isFormulaSet 8 htbl hΓ₁f wok
  have lLay₂ : Layout walkPieces Wc T Γ₂ c 0 := by have := lLay.transport wnd.noDrop'; rwa [wsh, add_zero] at this
  have hLay₂ : Layout walkPieces Wc T Γ₂ s (i + σ) := by have := hLay₁.transport wnd.noDrop'; rwa [wsh, add_zero] at this
  -- the fold
  have hSE : i + σ + (len (memberList s) + 1) + 1 ≤ E := by
    calc i + σ + (len (memberList s) + 1) + 1 = i + σ + (len (memberList s) + 2) := by ring
      _ ≤ i + σ + (8 * D + 3) := add_le_add le_rfl (add_le_add (le_trans hkD (le_mul_of_one_le_left zero_le (by norm_num))) (by norm_num))
      _ = i + σ + 8 * D + 3 := by ring
      _ ≤ E := hi
  have hkE' : 0 + (2 * len (memberList c) + 2) ≤ E := by
    calc 0 + (2 * len (memberList c) + 2) ≤ 6 * D + 2 := by
          rw [zero_add]
          exact add_le_add (le_trans (mul_le_mul_of_nonneg_left hk'D zero_le) (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) le_rfl
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
      _ ≤ E := hE
  have hosE' : ∀ j < len (memberList c), mTop 0 (len (memberList c)) (offVec (memberList c) walkPieces Wc T).[j] + 1 ≤ E :=
    fun j hj ↦ by
    calc _ ≤ 0 + 6 * D + 1 + 1 := add_le_add (mTop_le htbl hW hWc T hcs hcD hj) le_rfl
      _ = 6 * D + 2 := by ring
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
      _ ≤ E := hE
  have hin : SubIn Γ₂ 0 (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (^&(i + σ + (len (memberList s) + 1))) :=
    fun j hj ↦ ⟨(lLay₂.1 j hj).2.2.2.1, by have := wfacts j hj; rwa [qK'_pack, qOs'_pack, qI_pack, qK_pack] at this⟩
  obtain ⟨cok, cnd, _, csh, _, cfact⟩ := subChain_ok htbl hP hWp hΓ₂f (by simp) (termLen_fvar_le' hSE) hk1 hkE' hosE'
    (len_offVec _ _ _ _) hin
  -- assembly
  have hlist : proWk walkPieces Wl Wc W T s c i = appendV (layoutSteps walkPieces Wl Wc W T c)
      (appendV (loopW (qPack Wl W (i + σ) (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) 0
          (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) 0 0) (len (memberList c)))
        (subChain W 0 (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (^&(i + σ + (len (memberList s) + 1))))) := by
    unfold proWk; rw [← hσ]
  rw [hlist]
  refine ⟨listOK_appendV lok (by rw [← hΓ₁]; exact listOK_appendV wok (by rw [← hΓ₂]; exact cok)),
    noDrop'_appendV lnd (noDrop'_appendV wnd.noDrop' cnd.noDrop'), ?_, ?_, ?_, ?_⟩
  · rw [shiftsV_appendV, shiftsV_appendV, lsh, wsh, csh, add_zero, add_zero]
  · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂]
    have := lLay₂.transport cnd.noDrop'; rwa [csh, add_zero] at this
  · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂]
    have := hLay₂.transport cnd.noDrop'; rwa [csh, add_zero] at this
  · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂]
    exact cfact

end wkChild

/-! ## 9. The `or` child: `insert p (insert q s)` — two `proIns` and one `congInsertS` (`DESIGN_fragments.md` §4.4)

The child sequent is a two-level insert. Rather than a two-level identification, the prologue lays out the
INTERMEDIATE sequent `insert q s` by `proIns s q` (its row object `cq = &σ₁` with `insFact cq Q S`, identified
with the intermediate chain top `s'_q`), then lays out the child `insert p (insert q s)` by `proIns (insert q s) p`
FROM the intermediate layout (its row object `cp' = &σ₂` with `insFact cp' P s'_q`, identified with the child's
chain top `s''`), and finally moves the second insert fact onto `cq` by `congInsertS` (`s'_q = cq`):
`insFact cp' P cq`. `nodeOr_ok`'s `hiq'` is `insFact cq Q S`, its `hip'` is `insFact cp' P cq`, its `hf` comes
from `postIns` on `cp'` (`eqFactB cp' s''`). The intermediate layout is redundant work, linear in the sizes. -/

section orChild

/-- **`proOr`**: `proIns s q i iq`, then `proIns (insert q s) p 0 (ip + 1 + σ₁)`, then `congInsertS`. -/
noncomputable def proOr (Ww Wl Wc W T s p q i ip iq : V) : V :=
  appendV (proIns Ww Wl Wc W T s q i iq)
    (appendV (proIns Ww Wl Wc W T (insert q s) p 0 (ip + 1 + proSig Ww Wl Wc W T (insert q s)))
      ?[mkStep W 125 ?[^&(proSig Ww Wl Wc W T (insert p (insert q s))),
        ^&(ip + 1 + proSig Ww Wl Wc W T (insert q s) + 1 + proSig Ww Wl Wc W T (insert p (insert q s))),
        ^&(0 + 1 + proSig Ww Wl Wc W T (insert p (insert q s)) + (len (memberList (insert q s)) + 1)),
        ^&(proSig Ww Wl Wc W T (insert q s) + (1 + proSig Ww Wl Wc W T (insert p (insert q s))))]])

noncomputable def proOrDef : 𝚺₁.Semisentence 12 := .mkSigma
  “y Ww Wl Wc W T s p q i ip iq. ∃ A, !proInsDef A Ww Wl Wc W T s q i iq ∧ ∃ cq, !insertDef cq q s ∧
    ∃ L₁, !layoutStepsDef L₁ Ww Wl Wc W T cq ∧ ∃ σ₁, !shiftsVDef σ₁ L₁ ∧ ∃ ip', ip' = ip + 1 + σ₁ ∧
    ∃ B, !proInsDef B Ww Wl Wc W T cq p 0 ip' ∧ ∃ t, !insertDef t p cq ∧
    ∃ L₂, !layoutStepsDef L₂ Ww Wl Wc W T t ∧ ∃ σ₂, !shiftsVDef σ₂ L₂ ∧ ∃ zc, !qqFvarDef zc σ₂ ∧
    ∃ jp, jp = ip' + 1 + σ₂ ∧ ∃ zp, !qqFvarDef zp jp ∧ ∃ ys, !memberListDef ys cq ∧ ∃ kq, !lenDef kq ys ∧
    ∃ js, js = 0 + 1 + σ₂ + (kq + 1) ∧ ∃ zs, !qqFvarDef zs js ∧ ∃ jq, jq = σ₁ + (1 + σ₂) ∧ ∃ zq, !qqFvarDef zq jq ∧
    ∃ e₁, !adjoinDef e₁ zq 0 ∧ ∃ e₂, !adjoinDef e₂ zs e₁ ∧ ∃ e₃, !adjoinDef e₃ zp e₂ ∧ ∃ e₄, !adjoinDef e₄ zc e₃ ∧
    ∃ st, !mkStepDef st W 125 e₄ ∧ ∃ l, !adjoinDef l st 0 ∧ ∃ r, !appendVDef r B l ∧ !appendVDef y A r”

set_option maxHeartbeats 1000000 in
instance proOr_defined :
    𝚺₁.DefinedFunction (fun v : Fin 11 → V ↦ proOr (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10))
      proOrDef := .mk
  fun v ↦ by
    simp [proOrDef, proOr, proSig, proIns_defined.iff, layoutSteps_defined.iff, shiftsV_defined.iff,
      memberList_defined.iff, mkStep_defined.iff, appendV_defined.iff, numeral_eq_natCast]

/-- `1 ≤ len (memberList (insert p s))`. -/
lemma one_le_len_memberList_insert (p s : V) : 1 ≤ len (memberList (insert p s)) := by
  obtain ⟨hlt, _⟩ := idxOf_spec (show p ∈ insert p s by simp)
  have := lt_iff_succ_le.mp (lt_of_le_of_lt zero_le hlt); rwa [zero_add] at this

set_option maxHeartbeats 4000000 in
/-- **The `or` child's prologue is applicable**: afterwards the child's layout is at `0`, the parent's at
`i + 1 + σ₁ + (1 + σ₂)`, and the three facts `nodeOr_ok` reads are in place: `insFact cq Q S` (`hiq'`, with
`cq = &(σ₁ + (1 + σ₂))`), `insFact cp' P cq` (`hip'`, with `cp' = &σ₂`), and `eqFactB cp' s''` for `postIns`
(`s'' = &(k'' + 1)` the child's chain top). `σ₁ = proSig … (insert q s)`, `σ₂ = proSig … (insert p (insert q s))`. -/
theorem proOr_ok {tbl N N' B' Wl Wc W T s p q i ip iq D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p) (hq : IsSemiformula LAct 0 q) (hk1 : 1 ≤ len (memberList s))
    (hsD : setLen LAct (insert p (insert q s)) ≤ D) (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : i + 14 * D + 5 ≤ E)
    (hipE : ip + 14 * D + 6 ≤ E) (hiqE : iq + 8 * D + 4 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hLay : Layout walkPieces Wc T Γ s i) (hDp : DossF walkPieces Γ 0 p ip) (hDq : DossF walkPieces Γ 0 q iq) :
    ListOK tbl E ((8 : ℕ) : V) Γ (proOr walkPieces Wl Wc W T s p q i ip iq) ∧
    NoDrop' (proOr walkPieces Wl Wc W T s p q i ip iq) ∧
    shiftsV (proOr walkPieces Wl Wc W T s p q i ip iq) =
      1 + proSig walkPieces Wl Wc W T (insert q s) + (1 + proSig walkPieces Wl Wc W T (insert p (insert q s))) ∧
    Layout walkPieces Wc T (finalCtx Γ (proOr walkPieces Wl Wc W T s p q i ip iq)) (insert p (insert q s)) 0 ∧
    Layout walkPieces Wc T (finalCtx Γ (proOr walkPieces Wl Wc W T s p q i ip iq)) s
      (i + 1 + proSig walkPieces Wl Wc W T (insert q s) + (1 + proSig walkPieces Wl Wc W T (insert p (insert q s)))) ∧
    neg LAct (insFact (^&(proSig walkPieces Wl Wc W T (insert q s) + (1 + proSig walkPieces Wl Wc W T (insert p (insert q s)))))
      (^&(iq + 1 + proSig walkPieces Wl Wc W T (insert q s) + (1 + proSig walkPieces Wl Wc W T (insert p (insert q s)))))
      (^&(i + 1 + proSig walkPieces Wl Wc W T (insert q s) + (len (memberList s) + 1) +
        (1 + proSig walkPieces Wl Wc W T (insert p (insert q s)))))) ∈
      finalCtx Γ (proOr walkPieces Wl Wc W T s p q i ip iq) ∧
    neg LAct (insFact (^&(proSig walkPieces Wl Wc W T (insert p (insert q s))))
      (^&(ip + 1 + proSig walkPieces Wl Wc W T (insert q s) + 1 + proSig walkPieces Wl Wc W T (insert p (insert q s))))
      (^&(proSig walkPieces Wl Wc W T (insert q s) + (1 + proSig walkPieces Wl Wc W T (insert p (insert q s)))))) ∈
      finalCtx Γ (proOr walkPieces Wl Wc W T s p q i ip iq) ∧
    neg LAct (eqFactB (^&(proSig walkPieces Wl Wc W T (insert p (insert q s))))
      (^&(0 + (len (memberList (insert p (insert q s))) + 1)))) ∈ finalCtx Γ (proOr walkPieces Wl Wc W T s p q i ip iq) := by
  have hF1 := hP.frag1Table
  have hqs : IsFormulaSet LAct (insert q s) := IsFormulaSet.insert_iff.mpr ⟨hq, hs⟩
  have hsD₁ : setLen LAct (insert q s) ≤ D := le_trans (setLen_le_insert p _) hsD
  have hkq : len (memberList (insert q s)) ≤ D := le_trans (len_memberList_le_setLen hqs) hsD₁
  have hkq1 : 1 ≤ len (memberList (insert q s)) := one_le_len_memberList_insert q s
  have hE8 : 13 * D + 18 * ‖D‖ + 8 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hE
  have e125 : ∀ ev : V, mkStep proPieces (125 : V) ev = mkStep frag1Pieces (125 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag1 125 (by decide) ev; simpa using this
  set σ₁ := proSig walkPieces Wl Wc W T (insert q s) with hσ₁
  set σ₂ := proSig walkPieces Wl Wc W T (insert p (insert q s)) with hσ₂
  have hσ₁le : σ₁ ≤ 6 * D + 1 := proSig_le htbl hP hWc htblN hWl hWp hqs hkq1 hsD₁ hE8 hΓ
  -- step 1: the intermediate sequent
  obtain ⟨ok₁, nd₁, sh₁, lay₁, fr₁, eq₁⟩ := proIns_ok htbl hP htblN hWl hWc hWp hs hq hk1 hsD₁ hE hiE hiqE hΓ hLay hDq
  rw [← hσ₁] at sh₁ fr₁ eq₁
  set Γ₁ := finalCtx Γ (proIns walkPieces Wl Wc W T s q i iq) with hΓ₁
  have hΓ₁f : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ ok₁
  have hDp₁ : DossF walkPieces Γ₁ 0 p (ip + 1 + σ₁) := by
    have := dossF_transport' nd₁ hDp; rwa [sh₁, ← add_assoc] at this
  have hσ₂le : σ₂ ≤ 6 * D + 1 := proSig_le htbl hP hWc htblN hWl hWp (IsFormulaSet.insert_iff.mpr ⟨hp, hqs⟩)
    (one_le_len_memberList_insert p _) hsD hE8 hΓ₁f
  -- step 2: the child from the intermediate layout
  have hiE₂ : (0 : V) + 14 * D + 5 ≤ E := by rw [zero_add]; exact le_trans (add_le_add le_add_self le_rfl) (le_trans (add_le_add le_rfl (by norm_num)) hipE)
  have hipE₂ : ip + 1 + σ₁ + 8 * D + 4 ≤ E := by
    calc ip + 1 + σ₁ + 8 * D + 4 ≤ ip + 1 + (6 * D + 1) + 8 * D + 4 := add_le_add (add_le_add (add_le_add le_rfl hσ₁le) le_rfl) le_rfl
      _ = ip + 14 * D + 6 := by ring
      _ ≤ E := hipE
  obtain ⟨ok₂, nd₂, sh₂, lay₂, fr₂, eq₂⟩ := proIns_ok htbl hP htblN hWl hWc hWp hqs hp hkq1 hsD hE hiE₂ hipE₂ hΓ₁f lay₁ hDp₁
  rw [← hσ₂] at sh₂ fr₂ eq₂
  set Γ₂ := finalCtx Γ₁ (proIns walkPieces Wl Wc W T (insert q s) p 0 (ip + 1 + σ₁)) with hΓ₂
  have hΓ₂f : IsFormulaSet LAct Γ₂ := finalCtx_isFormulaSet 8 htbl hΓ₁f ok₂
  -- the transported facts
  have hLay₂ : Layout walkPieces Wc T Γ₂ s (i + 1 + σ₁ + (1 + σ₂)) := by
    have := fr₁.parent.transport nd₂; rwa [sh₂] at this
  have hcq₂ : neg LAct (insFact (^&(σ₁ + (1 + σ₂))) (^&(iq + 1 + σ₁ + (1 + σ₂))) (^&(i + 1 + σ₁ + (len (memberList s) + 1) + (1 + σ₂)))) ∈ Γ₂ := by
    have := mem_finalCtx_of_mem' nd₂ fr₁.cp
    rwa [sh₂, shiftIterV_neg (isFormula_insFact (by simp) (by simp) (by simp)), shiftIterV_insFact (by simp) (by simp) (by simp),
      termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar] at this
  have heq₂ : neg LAct (eqFactB (^&(σ₁ + (1 + σ₂))) (^&(0 + 1 + σ₂ + (len (memberList (insert q s)) + 1)))) ∈ Γ₂ := by
    have := mem_finalCtx_of_mem' nd₂ eq₁
    rw [sh₂, shiftIterV_neg (isFormula_eqFactB (by simp) (by simp)), shiftIterV_eqFactB (by simp) (by simp),
      termShiftIterV_fvar, termShiftIterV_fvar] at this
    have e : 0 + (len (memberList (insert q s)) + 1) + (1 + σ₂) = 0 + 1 + σ₂ + (len (memberList (insert q s)) + 1) := by ring
    rwa [e] at this
  -- step 3: `congInsertS`
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hE)
  have hcpE : σ₂ + 1 ≤ E := by
    calc σ₂ + 1 ≤ 6 * D + 1 + 1 := add_le_add hσ₂le le_rfl
      _ = 6 * D + 2 := by ring
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
      _ ≤ E := hE
  have hPE : ip + 1 + σ₁ + 1 + σ₂ + 1 ≤ E := by
    calc ip + 1 + σ₁ + 1 + σ₂ + 1 ≤ ip + 1 + (6 * D + 1) + 1 + (6 * D + 1) + 1 :=
          add_le_add (add_le_add (add_le_add (add_le_add le_rfl hσ₁le) le_rfl) hσ₂le) le_rfl
      _ = ip + 12 * D + 5 := by ring
      _ ≤ ip + 14 * D + 6 := add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) (by norm_num)
      _ ≤ E := hipE
  have hsqE : 0 + 1 + σ₂ + (len (memberList (insert q s)) + 1) + 1 ≤ E := by
    calc 0 + 1 + σ₂ + (len (memberList (insert q s)) + 1) + 1 ≤ 0 + 1 + (6 * D + 1) + (D + 1) + 1 :=
          add_le_add (add_le_add (add_le_add le_rfl hσ₂le) (add_le_add hkq le_rfl)) le_rfl
      _ = 7 * D + 4 := by ring
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := add_le_add (le_trans (mul_le_mul_of_nonneg_right (by norm_num) zero_le) le_self_add) (by norm_num)
      _ ≤ E := hE
  have hcqE : σ₁ + (1 + σ₂) + 1 ≤ E := by
    calc σ₁ + (1 + σ₂) + 1 ≤ 6 * D + 1 + (1 + (6 * D + 1)) + 1 := add_le_add (add_le_add hσ₁le (add_le_add le_rfl hσ₂le)) le_rfl
      _ = 12 * D + 4 := by ring
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := add_le_add (le_trans (mul_le_mul_of_nonneg_right (by norm_num) zero_le) le_self_add) (by norm_num)
      _ ≤ E := hE
  obtain ⟨ok₃, tg₃, cx₃⟩ := fok_congInsertS htbl hF1 rfl hΓ₂f (by simp) (termLen_fvar_le' hcpE) (by simp) (termLen_fvar_le' hPE)
    (by simp) (termLen_fvar_le' hsqE) (by simp) (termLen_fvar_le' hcqE) heq₂ fr₂.cp
  rw [← e125, ← hWp] at ok₃ tg₃ cx₃
  -- assembly
  have hlist : proOr walkPieces Wl Wc W T s p q i ip iq = appendV (proIns walkPieces Wl Wc W T s q i iq)
      (appendV (proIns walkPieces Wl Wc W T (insert q s) p 0 (ip + 1 + σ₁))
        ?[mkStep W 125 ?[^&σ₂, ^&(ip + 1 + σ₁ + 1 + σ₂), ^&(0 + 1 + σ₂ + (len (memberList (insert q s)) + 1)), ^&(σ₁ + (1 + σ₂))]]) := by
    unfold proOr; rw [← hσ₁, ← hσ₂]
  rw [hlist]
  have tr₃ : ∀ x ∈ Γ₂, x ∈ finalCtx Γ₂ ?[mkStep W 125 ?[^&σ₂, ^&(ip + 1 + σ₁ + 1 + σ₂), ^&(0 + 1 + σ₂ + (len (memberList (insert q s)) + 1)), ^&(σ₁ + (1 + σ₂))]] :=
    fun x hx ↦ by rw [finalCtx_single, cx₃]; exact memIns hx
  refine ⟨listOK_appendV ok₁ (by rw [← hΓ₁]; exact listOK_appendV ok₂ (by rw [← hΓ₂]; exact listOK_single ok₃)),
    noDrop'_appendV nd₁ (noDrop'_appendV nd₂ (noDrop'_single (Or.inl tg₃))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [shiftsV_appendV, shiftsV_appendV, sh₁, sh₂, shiftsV_single_tag0 tg₃, add_zero]
  · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂]
    have := lay₂.transport (noDrop'_single (Or.inl tg₃)); rwa [shiftsV_single_tag0 tg₃, add_zero] at this
  · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂]
    have := hLay₂.transport (noDrop'_single (Or.inl tg₃)); rwa [shiftsV_single_tag0 tg₃, add_zero] at this
  · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂]; exact tr₃ _ hcq₂
  · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂, finalCtx_single, cx₃]; exact memInsSelf _ _
  · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂]; exact tr₃ _ eq₂

end orChild


/-! ## 10. The `shift` child: `c` with `s = setShift c` (`DESIGN_fragments.md` §4.8)

The parent `s = setShift c` is laid out at `i`; the prologue lays out the child `c` at `0` and derives
`setShiftFact S s''` for the parent's chain top `S` and the child's `s''` — `nodeShift_ok`'s `hss` (its `hf`
is the child's own goal after `goalElim`, no `congFstIdx`). Route: the fresh chain `u_j = insert X_{π j} u_{j+1}`
over the SHIFTED members' objects `X_{π j}` (the parent's dossiers of `shift y_j`, in the child's order — built by
`chainSteps`, `k' + 1` eigenvariables), `setShiftFact 𝟎 𝟎` (`shBase`), then the Horn-only tail: `certShift`
between the two dossiers of each `y_j` (Loop S, `shiftFact X_{π j} Y_j`), `setShiftInsert` up the chain
(Loop I, `setShiftFact u_j s''_j`), `insertSubset` up the chain against `S` (Fold U, `u_0 ⊆ S`),
`shiftMemSetShift` per member (Loop M, `X_{π j} ∈ u_0`) and the parent's `subChain` (`S ⊆ u_0`; surjectivity
of `shift` onto the parent's members is `mem_setShift_iff` + `memberList_nodup`), `subsetAntisymm`,
`congSetShiftL`. The frame is `shPack` (a `qPack` with the certification pieces in the `Wl` slot). -/

section shiftChild

/-! ### 10.1 Two more transports (and the missing definability instance of `setShiftFact`) -/

noncomputable def setShiftFactDef : 𝚺₁.Semisentence 3 := fact2Def (Semiformula.lMap emb (↑(setShiftGraph LAct) : ArithmeticSemisentence 2))
instance setShiftFact_defined : 𝚺₁-Function₂ (setShiftFact : V → V → V) via setShiftFactDef := fact2_defined _
instance setShiftFact_definable' : 𝚺₁-Function₂ (setShiftFact : V → V → V) := setShiftFact_defined.to_definable

lemma shiftIterV_setShiftFact {t s : V} (ht : IsSemiterm LAct 0 t) (hs : IsSemiterm LAct 0 s) :
    ∀ c : V, shiftIterV (setShiftFact t s) c = setShiftFact (termShiftIterV t c) (termShiftIterV s c) := by
  intro c
  induction c using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ c ih =>
    rw [shiftIterV_succ, ih, shift_setShiftFact (isSemiterm_termShiftIterV ht c) (isSemiterm_termShiftIterV hs c),
      termShiftIterV_succ, termShiftIterV_succ]

lemma shiftIterV_subsetFact {t s : V} (ht : IsSemiterm LAct 0 t) (hs : IsSemiterm LAct 0 s) :
    ∀ c : V, shiftIterV (subsetFact t s) c = subsetFact (termShiftIterV t c) (termShiftIterV s c) := by
  intro c
  induction c using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ c ih =>
    rw [shiftIterV_succ, ih, shift_subsetFact (isSemiterm_termShiftIterV ht c) (isSemiterm_termShiftIterV hs c),
      termShiftIterV_succ, termShiftIterV_succ]

/-! ### 10.2 The positions of the shifted members, in the child's order -/

namespace ShPos

noncomputable def blueprint : VecRec.Blueprint 4 where
  nil := .mkSigma “y xs os k i. y = 0”
  adjoin := .mkSigma “y x ys ih xs os k i. ∃ sh, !(shiftGraph LAct) sh x ∧ ∃ jx, !idxOfDef jx xs sh ∧
    ∃ o, !nthDef o os jx ∧ ∃ t, t = i + (2 * k + 1 + o) ∧ !adjoinDef y t ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin v x _ ih := (v 3 + (2 * v 2 + 1 + (v 1).[idxOf (v 0) (shift LAct x)])) ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint, shift.defined.iff, idxOf_defined.iff]

end ShPos

/-- `shPos xs os k i ys` — for each member `y` of `ys`, the top `mTop i k os.[idxOf xs (shift y)]` of `shift y` in
the layout of `xs` at chain offset `i` (vector first: the `VecRec` order). -/
noncomputable def shPos (ys xs os k i : V) : V := ShPos.construction.result ![xs, os, k, i] ys

@[simp] lemma shPos_nil (xs os k i : V) : shPos 0 xs os k i = 0 := by simp [shPos, ShPos.construction]
@[simp] lemma shPos_adjoin (y ys xs os k i : V) :
    shPos (y ∷ ys) xs os k i = mTop i k os.[idxOf xs (shift LAct y)] ∷ shPos ys xs os k i := by
  simp [shPos, ShPos.construction, mTop]

noncomputable def shPosDef : 𝚺₁.Semisentence 6 := ShPos.blueprint.resultDef

instance shPos_defined : 𝚺₁-Function₅ (shPos : V → V → V → V → V → V) via shPosDef := .mk
  fun v ↦ by simp [ShPos.construction.eval_resultDef, shPosDef]; rfl
instance shPos_definable : 𝚺₁.DefinableFunction₅ (shPos : V → V → V → V → V → V) := shPos_defined.to_definable

lemma len_shPos (xs os k i : V) : ∀ ys : V, len (shPos ys xs os k i) = len ys := by
  intro ys
  induction ys using adjoin_ISigma1.sigma1_succ_induction with
  | hP => definability
  | nil => simp
  | adjoin y ys ih => rw [shPos_adjoin, len_adjoin, len_adjoin, ih]

lemma nth_shPos (xs os k i : V) : ∀ ys : V, ∀ j < len ys, (shPos ys xs os k i).[j] = mTop i k os.[idxOf xs (shift LAct ys.[j])] := by
  intro ys
  induction ys using adjoin_ISigma1.pi1_succ_induction with
  | hP => unfold mTop; definability
  | nil => intro j hj; simp at hj
  | adjoin y ys ih =>
    intro j hj
    rw [shPos_adjoin]
    rcases zero_or_succ j with rfl | ⟨j, rfl⟩
    · simp
    · rw [nth_adjoin_succ, nth_adjoin_succ]
      exact ih j (by rw [len_adjoin] at hj; exact lt_of_add_lt_add_right hj)

/-! ### 10.3 The base: `setShiftFact 𝟎 𝟎` -/

/-- `setShiftTotal [𝟎]`, `setShiftEmpty [&0]`, `eqSymm [&0, 𝟎]`, `congSetShiftL [&0, 𝟎, 𝟎]`. -/
noncomputable def shBase (W : V) : V :=
  mkStep W 138 ?[(𝟎 : V)] ∷ mkStep W 145 ?[^&0] ∷ mkStep W 42 ?[^&0, (𝟎 : V)] ∷ mkStep W 148 ?[^&0, (𝟎 : V), (𝟎 : V)] ∷ (0 : V)

noncomputable def shBaseDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y W. ∃ z, !cTVGraph z 0 ∧ ∃ f, !qqFvarDef f 0 ∧
    ∃ e₁, !adjoinDef e₁ z 0 ∧ ∃ s₁, !mkStepDef s₁ W 138 e₁ ∧
    ∃ e₂, !adjoinDef e₂ f 0 ∧ ∃ s₂, !mkStepDef s₂ W 145 e₂ ∧
    ∃ e₃, !adjoinDef e₃ f e₁ ∧ ∃ s₃, !mkStepDef s₃ W 42 e₃ ∧
    ∃ e₄', !adjoinDef e₄' z e₁ ∧ ∃ e₄, !adjoinDef e₄ f e₄' ∧ ∃ s₄, !mkStepDef s₄ W 148 e₄ ∧
    ∃ l₄, !adjoinDef l₄ s₄ 0 ∧ ∃ l₃, !adjoinDef l₃ s₃ l₄ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ !adjoinDef y s₁ l₂”

instance shBase_defined : 𝚺₁-Function₁ (shBase : V → V) via shBaseDef := .mk fun v ↦ by
  simp [shBaseDef, shBase, mkStep_defined.iff, cTV.defined.iff, cTV_zero, numeral_eq_natCast]
instance shBase_definable : 𝚺₁-Function₁ (shBase : V → V) := shBase_defined.to_definable

/-- **The base is applicable**: one eigenvariable, `setShiftFact 𝟎 𝟎` afterwards. -/
theorem shBase_ok {tbl N W E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (hWp : W = proPieces)
    (hΓ : IsFormulaSet LAct Γ) (hE : (1 : V) ≤ E) :
    ListOK tbl E ((8 : ℕ) : V) Γ (shBase W) ∧ NoDrop' (shBase W) ∧ shiftsV (shBase W) = 1 ∧ len (shBase W) = 4 ∧
    neg LAct (setShiftFact (𝟎 : V) (𝟎 : V)) ∈ finalCtx Γ (shBase W) := by
  have hF2 := hP.frag2Table
  have hL := hP.layoutTable
  have e138 : ∀ ev : V, mkStep proPieces (138 : V) ev = mkStep frag2Pieces (138 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag2 138 (by decide) ev; simpa using this
  have e145 : ∀ ev : V, mkStep proPieces (145 : V) ev = mkStep frag2Pieces (145 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag2 145 (by decide) ev; simpa using this
  have e148 : ∀ ev : V, mkStep proPieces (148 : V) ev = mkStep frag2Pieces (148 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag2 148 (by decide) ev; simpa using this
  have e42 : ∀ ev : V, mkStep proPieces (42 : V) ev = mkStep layoutPieces (42 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 42 (by decide) ev; simpa using this
  have h0 : IsSemiterm LAct (0 : V) (𝟎 : V) := isSemiterm_qqZero_LAct 0
  have h0E : termLen LAct (𝟎 : V) ≤ E := termLen_zeroV_le hE
  have hf : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hfE : termLen LAct (^&0 : V) ≤ E := termLen_fvar0_le hE
  -- step 1
  obtain ⟨ok₁, tg₁, cx₁⟩ := gok_setShiftTotal htbl hF2 rfl hΓ h0 h0E
  rw [← e138, ← hWp] at ok₁ tg₁ cx₁
  rw [Nat.cast_zero, termShift_zeroV] at cx₁
  set Γ₁ := insert (neg LAct (setShiftFact (^&0) (𝟎 : V))) (setShift LAct Γ) with hΓ₁
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  -- step 2
  obtain ⟨ok₂, tg₂, cx₂⟩ := gok_setShiftEmpty htbl hF2 rfl hΓ₁f hf hfE (memInsSelf _ _)
  rw [← e145, ← hWp] at ok₂ tg₂ cx₂
  set Γ₂ := insert (neg LAct (eqFactB (^&0) (𝟎 : V))) Γ₁ with hΓ₂
  have hΓ₂f : IsFormulaSet LAct Γ₂ := by rw [← cx₂]; exact isFormulaSet_ctxAfter 8 htbl ok₂
  -- step 3
  obtain ⟨ok₃, tg₃, cx₃⟩ := lok_eqSymm htbl hL rfl hΓ₂f hf hfE h0 h0E (memInsSelf _ _)
  rw [← e42, ← hWp] at ok₃ tg₃ cx₃
  set Γ₃ := insert (neg LAct (eqFactB (𝟎 : V) (^&0))) Γ₂ with hΓ₃
  have hΓ₃f : IsFormulaSet LAct Γ₃ := by rw [← cx₃]; exact isFormulaSet_ctxAfter 8 htbl ok₃
  -- step 4
  obtain ⟨ok₄, tg₄, cx₄⟩ := gok_congSetShiftL htbl hF2 rfl hΓ₃f hf hfE h0 h0E h0 h0E (memInsSelf _ _)
    (memIns (memIns (memInsSelf _ _)))
  rw [← e148, ← hWp] at ok₄ tg₄ cx₄
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold shBase
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    exact listOK_single ok₄
  · unfold shBase
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp)
      (noDrop'_cons (by rw [tg₃]; simp) (noDrop'_single (by rw [tg₄]; simp))))
  · unfold shBase
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₃, tg₄]
    simp
  · unfold shBase; simp [len_adjoin]; norm_num
  · unfold shBase
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_single, cx₄]
    exact memInsSelf _ _

/-! ### 10.4 The frame and the certification loop (Loop S: `shiftFact X_{π j} Y_j` for every child member) -/

/-- The frame of the `shift` identification: `qPack Wc W i₂ k os xs 0 k' os' ys 0 σ` — the certification pieces in the
`Wl` slot (no `eqSteps` are used), the parent layout at `i₂`, the child at `0`, `σ` the shifts of the child's
layout (the chain objects `u_j` sit at `&(j + 1 + σ)`). -/
noncomputable def shPack (Wc W i₂ k os xs k' os' ys σ : V) : V := qPack Wc W i₂ k os xs 0 k' os' ys 0 σ

/-- The top of `shift y_j` in the parent's layout (the frame's view). -/
noncomputable def shX (q j : V) : V := mTop (qI q) (qK q) (qOs q).[idxOf (qXs q) (shift LAct (qYs q).[j])]
/-- The top of `y_j` in the child's layout. -/
noncomputable def shY (q j : V) : V := mTop 0 (qK' q) (qOs' q).[j]

lemma dossF_transport_zero {W Γ n r i S : V} (hS : NoDrop S) (hsh : shiftsV S = 0) (h : DossF W Γ n r i) :
    DossF W (finalCtx Γ S) n r i := by
  have := dossF_transport hS h; rwa [hsh, add_zero] at this

lemma prevAt_of_eq {k i : V} (h : i + 1 = k) : prevAt k i = (𝟎 : V) := by unfold prevAt; rw [if_pos h]

/-- Loop S, child member `j`: the re-indexed `certShift` between `y_j`'s dossier and `shift y_j`'s. -/
noncomputable def blockS (q j : V) : V := reidxL (certShift (qWl q) 0 (qYs q).[j] (shY q j) (shX q j))

noncomputable def blockSDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y q j. ∃ Wl, !pi₁Def Wl q ∧ ∃ r1, !pi₂Def r1 q ∧ ∃ W, !pi₁Def W r1 ∧ ∃ r2, !pi₂Def r2 r1 ∧ ∃ i, !pi₁Def i r2 ∧ ∃ r3, !pi₂Def r3 r2 ∧ ∃ k, !pi₁Def k r3 ∧ ∃ r4, !pi₂Def r4 r3 ∧ ∃ os, !pi₁Def os r4 ∧ ∃ r5, !pi₂Def r5 r4 ∧ ∃ xs, !pi₁Def xs r5 ∧ ∃ r6, !pi₂Def r6 r5 ∧ ∃ ip, !pi₁Def ip r6 ∧ ∃ r7, !pi₂Def r7 r6 ∧ ∃ kk, !pi₁Def kk r7 ∧ ∃ r8, !pi₂Def r8 r7 ∧ ∃ oss, !pi₁Def oss r8 ∧ ∃ r9, !pi₂Def r9 r8 ∧ ∃ ys, !pi₁Def ys r9 ∧ ∃ r10, !pi₂Def r10 r9 ∧ ∃ p, !pi₁Def p r10 ∧ ∃ sg, !pi₂Def sg r10 ∧
    ∃ yj, !nthDef yj ys j ∧ ∃ oj, !nthDef oj oss j ∧ ∃ tj, tj = 0 + (2 * kk + 1 + oj) ∧
    ∃ sh, !(shiftGraph LAct) sh yj ∧ ∃ jx, !idxOfDef jx xs sh ∧ ∃ oo, !nthDef oo os jx ∧ ∃ tx, tx = i + (2 * k + 1 + oo) ∧
    ∃ c, !passFDef c Wl 2 0 yj tj tx ∧ !reidxLDef y c”

set_option maxHeartbeats 1000000 in
instance blockS_defined : 𝚺₁-Function₂ (blockS : V → V → V) via blockSDef := .mk fun v ↦ by
  simp [blockSDef, blockS, shX, shY, certShift, qWl, qW, qI, qK, qOs, qXs, qIp, qK', qOs', qYs, qP, qSig, mTop,
    shift.defined.iff, idxOf_defined.iff, passF_defined.iff, reidxL_defined.iff, numeral_eq_natCast]
instance blockS_definable : 𝚺₁-Function₂ (blockS : V → V → V) := blockS_defined.to_definable

namespace LoopS

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y q. y = 0”
  succ := .mkSigma “y ih j q. ∃ b, !blockSDef b q j ∧ !appendVDef y ih b”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 0
  succ := fun v j ih ↦ appendV ih (blockS (v 0) j)
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, blockS_defined.iff, appendV_defined.iff]

end LoopS

noncomputable def loopS (q m : V) : V := LoopS.construction.result ![q] m

@[simp] lemma loopS_zero (q : V) : loopS q 0 = 0 := by simp [loopS, LoopS.construction]
lemma loopS_succ (q m : V) : loopS q (m + 1) = appendV (loopS q m) (blockS q m) := by simp [loopS, LoopS.construction]

noncomputable def loopSDef : 𝚺₁.Semisentence 3 := LoopS.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance loopS_defined : 𝚺₁-Function₂ (loopS : V → V → V) via loopSDef := .mk
  fun v ↦ by simp [LoopS.construction.result_defined_iff, loopSDef]; rfl
instance loopS_definable : 𝚺₁-Function₂ (loopS : V → V → V) := loopS_defined.to_definable

/-- Loop S's invariant. -/
def SSOut (tbl E q Γ m : V) : Prop :=
  ListOK tbl E ((8 : ℕ) : V) Γ (loopS q m) ∧ NoDrop (loopS q m) ∧ HornOnly (loopS q m) ∧ shiftsV (loopS q m) = 0 ∧
  ∀ j < m, neg LAct (shiftFact (^&(shX q j)) (^&(shY q j))) ∈ finalCtx Γ (loopS q m)

set_option maxHeartbeats 1000000 in
instance ssOut_definable : 𝚫₁-Relation₅ (SSOut : V → V → V → V → V → Prop) := by
  unfold SSOut shX shY qI qK qOs qXs qK' qOs' qYs mTop; definability

@[simp] lemma shX_pack (Wc W i₂ k os xs k' os' ys σ j : V) :
    shX (shPack Wc W i₂ k os xs k' os' ys σ) j = mTop i₂ k os.[idxOf xs (shift LAct ys.[j])] := by
  simp [shX, shPack]
@[simp] lemma shY_pack (Wc W i₂ k os xs k' os' ys σ j : V) :
    shY (shPack Wc W i₂ k os xs k' os' ys σ) j = mTop 0 k' os'.[j] := by
  simp [shY, shPack]

@[simp] lemma qWl_shPack (Wc W i₂ k os xs k' os' ys σ : V) : qWl (shPack Wc W i₂ k os xs k' os' ys σ) = Wc := by simp [shPack]
@[simp] lemma qW_shPack (Wc W i₂ k os xs k' os' ys σ : V) : qW (shPack Wc W i₂ k os xs k' os' ys σ) = W := by simp [shPack]
@[simp] lemma qI_shPack (Wc W i₂ k os xs k' os' ys σ : V) : qI (shPack Wc W i₂ k os xs k' os' ys σ) = i₂ := by simp [shPack]
@[simp] lemma qK_shPack (Wc W i₂ k os xs k' os' ys σ : V) : qK (shPack Wc W i₂ k os xs k' os' ys σ) = k := by simp [shPack]
@[simp] lemma qOs_shPack (Wc W i₂ k os xs k' os' ys σ : V) : qOs (shPack Wc W i₂ k os xs k' os' ys σ) = os := by simp [shPack]
@[simp] lemma qXs_shPack (Wc W i₂ k os xs k' os' ys σ : V) : qXs (shPack Wc W i₂ k os xs k' os' ys σ) = xs := by simp [shPack]
@[simp] lemma qK'_shPack (Wc W i₂ k os xs k' os' ys σ : V) : qK' (shPack Wc W i₂ k os xs k' os' ys σ) = k' := by simp [shPack]
@[simp] lemma qOs'_shPack (Wc W i₂ k os xs k' os' ys σ : V) : qOs' (shPack Wc W i₂ k os xs k' os' ys σ) = os' := by simp [shPack]
@[simp] lemma qYs_shPack (Wc W i₂ k os xs k' os' ys σ : V) : qYs (shPack Wc W i₂ k os xs k' os' ys σ) = ys := by simp [shPack]
@[simp] lemma qSig_shPack (Wc W i₂ k os xs k' os' ys σ : V) : qSig (shPack Wc W i₂ k os xs k' os' ys σ) = σ := by simp [shPack]

/-- The shift of a child member is a parent member. -/
lemma shift_mem_of_mem {s c y : V} (hsc : s = setShift LAct c) (hy : y ∈ c) : shift LAct y ∈ s := by
  rw [hsc]; exact mem_setShift_iff.mpr ⟨y, hy, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **Loop S is applicable**: `shiftFact X_{π j} Y_j` for every child member. -/
theorem loopS_ok {tbl N N' B' W Wc T s c i₂ σ D E Γ q : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hq : q = shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s)
      (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ)
    (hs : IsFormulaSet LAct s) (hc : IsFormulaSet LAct c) (hsc : s = setShift LAct c)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hi : i₂ + 8 * D + 3 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hCL : Layout walkPieces Wc T Γ c 0) (hPL : Layout walkPieces Wc T Γ s i₂) :
    ∀ m ≤ len (memberList c), SSOut tbl E q Γ m := by
  have hW := hP.walkTable
  have hC := hP.certTable
  have htblC := hP.tableOK_certView htbl
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    exact ⟨by rw [loopS_zero]; exact listOK_nil _ _ _ _, by rw [loopS_zero]; exact noDrop_nil,
      by rw [loopS_zero]; exact hornOnly_nil, by rw [loopS_zero, shiftsV_nil], fun j hj ↦ absurd hj (by simp)⟩
  | succ m ih =>
    intro hm
    obtain ⟨sok, snd, sho, ssh, sfacts⟩ := ih (le_trans le_self_add hm)
    have hmk : m < len (memberList c) := lt_of_lt_of_le (lt_add_one m) hm
    set Γm := finalCtx Γ (loopS q m) with hΓm
    have hΓmf : IsFormulaSet LAct Γm := finalCtx_isFormulaSet 8 htbl hΓ sok
    have tr : ∀ x ∈ Γ, x ∈ Γm := fun x hx ↦ tr_of_zero snd ssh hx
    have hyc : (memberList c).[m] ∈ c := nth_memberList_mem hmk
    have hyf : IsSemiformula LAct 0 (memberList c).[m] := hc _ hyc
    have hyD : formulaLen LAct (memberList c).[m] ≤ D := le_trans (formulaLen_le_setLen_of_mem hyc) hcD
    have hxs : shift LAct (memberList c).[m] ∈ s := shift_mem_of_mem hsc hyc
    obtain ⟨hDy, _, _, _, _, _⟩ := hCL.1 m hmk
    obtain ⟨hDx, _, _, _⟩ := hPL.member hxs
    unfold memTop at hDx
    have hYle := mTop_le htbl hW hWc T hc hcD hmk (i := 0)
    obtain ⟨hlt', _⟩ := idxOf_spec hxs
    have hXle := mTop_le htbl hW hWc T hs hsD hlt' (i := i₂)
    have h2y : 2 * formulaLen LAct (memberList c).[m] ≤ 2 * D := mul_le_mul_of_nonneg_left hyD zero_le
    have hEy : 2 * (0 : V) + 2 * formulaLen LAct (memberList c).[m] + 8 ≤ E := by
      rw [mul_zero, zero_add]
      calc 2 * formulaLen LAct (memberList c).[m] + 8 ≤ 2 * D + 8 := add_le_add h2y le_rfl
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := add_le_add (le_trans (mul_le_mul_of_nonneg_right (by norm_num) zero_le) le_self_add) (by norm_num)
        _ ≤ E := hE
    have hEY : mTop 0 (len (memberList c)) (offVec (memberList c) walkPieces Wc T).[m] + 2 * formulaLen LAct (memberList c).[m] + 1 ≤ E := by
      calc _ ≤ (0 + 6 * D + 1) + 2 * D + 1 := add_le_add (add_le_add hYle h2y) le_rfl
        _ = 8 * D + 2 := by ring
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := eight_le_cap (by norm_num)
        _ ≤ E := hE
    have hEX : mTop i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) (shift LAct (memberList c).[m])] +
        2 * formulaLen LAct (memberList c).[m] + 1 ≤ E := by
      calc _ ≤ (i₂ + 6 * D + 1) + 2 * D + 1 := add_le_add (add_le_add hXle h2y) le_rfl
        _ = i₂ + 8 * D + 2 := by ring
        _ ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hi
    rw [SSOut, loopS_succ]
    have key : ListOK tbl E ((8 : ℕ) : V) Γm (blockS q m) ∧ NoDrop (blockS q m) ∧ HornOnly (blockS q m) ∧
        shiftsV (blockS q m) = 0 ∧ neg LAct (shiftFact (^&(shX q m)) (^&(shY q m))) ∈ finalCtx Γm (blockS q m) := by
      subst hq
      unfold blockS
      simp only [shX_pack, shY_pack, qWl_shPack, qYs_shPack]
      obtain ⟨cok, cnd, cho, csh, cfact⟩ := certShift_ok htblC hC rfl hWc hyf hEy hEY hEX hΓmf (dossF_transport_zero snd ssh hDy)
        (dossF_transport_zero snd ssh hDx)
      refine ⟨listOK_reidxL hP cok, noDrop_reidxL cnd, hornOnly_reidxL cho, by rw [shiftsV_reidxL, csh], ?_⟩
      rw [finalCtx_reidxL]; exact cfact
    obtain ⟨bok, bnd, bho, bsh, bfact⟩ := key
    refine ⟨listOK_appendV sok (by rw [← hΓm]; exact bok), noDrop_appendV snd bnd, hornOnly_appendV sho bho,
      by rw [shiftsV_appendV, ssh, bsh, add_zero], fun j hj ↦ ?_⟩
    rw [finalCtx_appendV, ← hΓm]
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hj) with h | rfl
    · exact tr_of_zero bnd bsh (sfacts j h)
    · exact bfact

/-! ### 10.5 Loop I: `setShiftFact u_j s''_j` up the child's chain (`setShiftInsert`, innermost first) -/

/-- The unpacking prefix shared by the frame-indexed blocks (kept as text in each blueprint). -/
noncomputable def blockI (q c : V) : V :=
  ?[mkStep (qW q) 144 ?[prevI 0 (qK' q) (jOf (qK' q) c), ^&(0 + (qK' q + 1 + jOf (qK' q) c)),
      ^&(shY q (jOf (qK' q) c)), ^&(shX q (jOf (qK' q) c)),
      prevAt (qK' q + 1 + qSig q) (jOf (qK' q) c + 1 + qSig q), ^&(jOf (qK' q) c + 1 + qSig q)]]

noncomputable def blockIDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y q c. ∃ Wl, !pi₁Def Wl q ∧ ∃ r1, !pi₂Def r1 q ∧ ∃ W, !pi₁Def W r1 ∧ ∃ r2, !pi₂Def r2 r1 ∧ ∃ i, !pi₁Def i r2 ∧ ∃ r3, !pi₂Def r3 r2 ∧ ∃ k, !pi₁Def k r3 ∧ ∃ r4, !pi₂Def r4 r3 ∧ ∃ os, !pi₁Def os r4 ∧ ∃ r5, !pi₂Def r5 r4 ∧ ∃ xs, !pi₁Def xs r5 ∧ ∃ r6, !pi₂Def r6 r5 ∧ ∃ ip, !pi₁Def ip r6 ∧ ∃ r7, !pi₂Def r7 r6 ∧ ∃ kk, !pi₁Def kk r7 ∧ ∃ r8, !pi₂Def r8 r7 ∧ ∃ oss, !pi₁Def oss r8 ∧ ∃ r9, !pi₂Def r9 r8 ∧ ∃ ys, !pi₁Def ys r9 ∧ ∃ r10, !pi₂Def r10 r9 ∧ ∃ p, !pi₁Def p r10 ∧ ∃ sg, !pi₂Def sg r10 ∧
    ∃ j, !jOfDef j kk c ∧ ∃ a, a = 0 + (2 * kk + 1) ∧ ∃ b, b = 0 + (kk + 1 + j) ∧ ∃ pv, !prevAtDef pv a b ∧ ∃ zb, !qqFvarDef zb b ∧
    ∃ oj, !nthDef oj oss j ∧ ∃ ty, ty = 0 + (2 * kk + 1 + oj) ∧ ∃ zy, !qqFvarDef zy ty ∧
    ∃ yj, !nthDef yj ys j ∧ ∃ sh, !(shiftGraph LAct) sh yj ∧ ∃ jx, !idxOfDef jx xs sh ∧ ∃ oo, !nthDef oo os jx ∧
    ∃ tx, tx = i + (2 * k + 1 + oo) ∧ ∃ zx, !qqFvarDef zx tx ∧
    ∃ a2, a2 = kk + 1 + sg ∧ ∃ b2, b2 = j + 1 + sg ∧ ∃ pu, !prevAtDef pu a2 b2 ∧ ∃ zu, !qqFvarDef zu b2 ∧
    ∃ e₁, !adjoinDef e₁ zu 0 ∧ ∃ e₂, !adjoinDef e₂ pu e₁ ∧ ∃ e₃, !adjoinDef e₃ zx e₂ ∧ ∃ e₄, !adjoinDef e₄ zy e₃ ∧
    ∃ e₅, !adjoinDef e₅ zb e₄ ∧ ∃ e₆, !adjoinDef e₆ pv e₅ ∧ ∃ st, !mkStepDef st W 144 e₆ ∧ !adjoinDef y st 0”

set_option maxHeartbeats 1000000 in
instance blockI_defined : 𝚺₁-Function₂ (blockI : V → V → V) via blockIDef := .mk fun v ↦ by
  simp [blockIDef, blockI, shX, shY, prevI, qWl, qW, qI, qK, qOs, qXs, qIp, qK', qOs', qYs, qP, qSig, mTop,
    jOf_defined.iff, prevAt_defined.iff, shift.defined.iff, idxOf_defined.iff, mkStep_defined.iff, numeral_eq_natCast]
instance blockI_definable : 𝚺₁-Function₂ (blockI : V → V → V) := blockI_defined.to_definable

namespace LoopI

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y q. y = 0”
  succ := .mkSigma “y ih c q. ∃ b, !blockIDef b q c ∧ !appendVDef y ih b”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 0
  succ := fun v c ih ↦ appendV ih (blockI (v 0) c)
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, blockI_defined.iff, appendV_defined.iff]

end LoopI

noncomputable def loopI (q m : V) : V := LoopI.construction.result ![q] m

@[simp] lemma loopI_zero (q : V) : loopI q 0 = 0 := by simp [loopI, LoopI.construction]
lemma loopI_succ (q m : V) : loopI q (m + 1) = appendV (loopI q m) (blockI q m) := by simp [loopI, LoopI.construction]

noncomputable def loopIDef : 𝚺₁.Semisentence 3 := LoopI.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance loopI_defined : 𝚺₁-Function₂ (loopI : V → V → V) via loopIDef := .mk
  fun v ↦ by simp [LoopI.construction.result_defined_iff, loopIDef]; rfl
instance loopI_definable : 𝚺₁-Function₂ (loopI : V → V → V) := loopI_defined.to_definable

/-- Loop I's invariant: after `c` blocks, `setShiftFact u_j s''_j` for `j = jOf k' (c − 1)`. -/
def IOut (tbl E q Γ c : V) : Prop :=
  ListOK tbl E ((8 : ℕ) : V) Γ (loopI q c) ∧ NoDrop (loopI q c) ∧ HornOnly (loopI q c) ∧ shiftsV (loopI q c) = 0 ∧
  len (loopI q c) = c ∧
  (1 ≤ c → neg LAct (setShiftFact (^&(jOf (qK' q) (c - 1) + 1 + qSig q)) (^&(0 + (qK' q + 1 + jOf (qK' q) (c - 1))))) ∈
    finalCtx Γ (loopI q c))

set_option maxHeartbeats 1000000 in
instance iOut_definable : 𝚫₁-Relation₅ (IOut : V → V → V → V → V → Prop) := by
  unfold IOut qK' qSig; definability

/-- The facts Loops I/U/M read, at the frame `q = shPack Wc W i₂ k os xs k' os' ys σ`: the chain over the shifted
members (`insFact u_j X_{π j} u_{j+1}`, `u_j = &(j + 1 + σ)`), the certifications `shiftFact X_{π j} Y_j`, and the
base `setShiftFact 𝟎 𝟎`. -/
def ShIn (Γ q : V) : Prop :=
  (∀ j < qK' q, neg LAct (insFact (^&(j + 1 + qSig q)) (^&(shX q j)) (prevAt (qK' q + 1 + qSig q) (j + 1 + qSig q))) ∈ Γ) ∧
  (∀ j < qK' q, neg LAct (shiftFact (^&(shX q j)) (^&(shY q j))) ∈ Γ) ∧
  neg LAct (setShiftFact (𝟎 : V) (𝟎 : V)) ∈ Γ

lemma ShIn.mono {Γ Γ' q : V} (h : ∀ x ∈ Γ, x ∈ Γ') (hin : ShIn Γ q) : ShIn Γ' q :=
  ⟨fun j hj ↦ h _ (hin.1 j hj), fun j hj ↦ h _ (hin.2.1 j hj), h _ hin.2.2⟩

/-- The caps of the `shift` identification. -/
structure ShCap (D E i₂ σ : V) : Prop where
  hE : 13 * D + 18 * ‖D‖ + 12 ≤ E
  hi : i₂ + 8 * D + 3 ≤ E
  hσ : σ ≤ 6 * D + 1

set_option maxHeartbeats 4000000 in
/-- **Loop I is applicable**. -/
theorem loopI_ok {tbl N W Wc T s c i₂ σ D E Γ q : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hq : q = shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s)
      (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ)
    (hs : IsFormulaSet LAct s) (hc : IsFormulaSet LAct c) (hsc : s = setShift LAct c)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D) (hcap : ShCap D E i₂ σ) (hΓ : IsFormulaSet LAct Γ)
    (hCL : Layout walkPieces Wc T Γ c 0) (hin : ShIn Γ q) :
    ∀ m ≤ len (memberList c), IOut tbl E q Γ m := by
  have hW := hP.walkTable
  have hF2 := hP.frag2Table
  have e144 : ∀ ev : V, mkStep proPieces (144 : V) ev = mkStep frag2Pieces (144 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag2 144 (by decide) ev; simpa using this
  have hk'D : len (memberList c) ≤ D := le_trans (len_memberList_le_setLen hc) hcD
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    exact ⟨by rw [loopI_zero]; exact listOK_nil _ _ _ _, by rw [loopI_zero]; exact noDrop_nil,
      by rw [loopI_zero]; exact hornOnly_nil, by rw [loopI_zero, shiftsV_nil], by rw [loopI_zero, len_nil],
      fun h ↦ absurd h (not_le.mpr _root_.zero_lt_one)⟩
  | succ m ih =>
    intro hm
    obtain ⟨iok, ind, iho, ish, ilen, ifact⟩ := ih (le_trans le_self_add hm)
    have hmk : m < len (memberList c) := lt_of_lt_of_le (lt_add_one m) hm
    set Γm := finalCtx Γ (loopI q m) with hΓm
    have hΓmf : IsFormulaSet LAct Γm := finalCtx_isFormulaSet 8 htbl hΓ iok
    have tr : ∀ x ∈ Γ, x ∈ Γm := fun x hx ↦ tr_of_zero ind ish hx
    set j := jOf (len (memberList c)) m with hj
    have hjc : j + (m + 1) = len (memberList c) := jOf_add hm
    have hjk : j < len (memberList c) := by rw [← hjc]; exact lt_add_of_pos_right _ (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have hjD : j ≤ D := le_trans (le_of_lt hjk) hk'D
    have hxs : shift LAct (memberList c).[j] ∈ s := shift_mem_of_mem hsc (nth_memberList_mem hjk)
    obtain ⟨hlt', _⟩ := idxOf_spec hxs
    have hXle := mTop_le htbl hW hWc T hs hsD hlt' (i := i₂)
    have hYle := mTop_le htbl hW hWc T hc hcD hjk (i := 0)
    -- caps
    have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hcap.hE)
    have hXE : mTop i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) (shift LAct (memberList c).[j])] + 1 ≤ E := by
      calc _ ≤ i₂ + 6 * D + 1 + 1 := add_le_add hXle le_rfl
        _ = i₂ + (6 * D + 2) := by ring
        _ ≤ i₂ + (8 * D + 3) := add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num))
        _ = i₂ + 8 * D + 3 := by ring
        _ ≤ E := hcap.hi
    have hYE : mTop 0 (len (memberList c)) (offVec (memberList c) walkPieces Wc T).[j] + 1 ≤ E := by
      calc _ ≤ 0 + 6 * D + 1 + 1 := add_le_add hYle le_rfl
        _ = 6 * D + 2 := by ring
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
        _ ≤ E := hcap.hE
    have hsjE : 0 + (len (memberList c) + 1 + j) + 2 ≤ E := by
      calc 0 + (len (memberList c) + 1 + j) + 2 ≤ 0 + (D + 1 + D) + 2 := add_le_add (add_le_add le_rfl (add_le_add (add_le_add hk'D le_rfl) hjD)) le_rfl
        _ = 2 * D + 3 := by ring
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := add_le_add (le_trans (mul_le_mul_of_nonneg_right (by norm_num) zero_le) le_self_add) (by norm_num)
        _ ≤ E := hcap.hE
    have hsjE1 : 0 + (len (memberList c) + 1 + j) + 1 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hsjE
    have hujE : j + 1 + σ + 2 ≤ E := by
      calc j + 1 + σ + 2 ≤ D + 1 + (6 * D + 1) + 2 := add_le_add (add_le_add (add_le_add hjD le_rfl) hcap.hσ) le_rfl
        _ = 7 * D + 4 := by ring
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := add_le_add (le_trans (mul_le_mul_of_nonneg_right (by norm_num) zero_le) le_self_add) (by norm_num)
        _ ≤ E := hcap.hE
    have hujE1 : j + 1 + σ + 1 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hujE
    -- the facts
    obtain ⟨_, _, _, hins, _, _⟩ := hCL.1 j hjk
    have hjk' : j < qK' q := by rw [hq, qK'_shPack]; exact hjk
    have hsh := hin.2.1 j hjk'
    have hch := hin.1 j hjk'
    simp only [hq, qK'_shPack, qSig_shPack, shX_pack, shY_pack] at hsh hch
    have hbelow : neg LAct (setShiftFact (prevAt (len (memberList c) + 1 + σ) (j + 1 + σ)) (prevI 0 (len (memberList c)) j)) ∈ Γm := by
      by_cases hm0 : m = 0
      · have hj1 : j + 1 = len (memberList c) := by rw [← hjc, hm0, zero_add]
        rw [prevI_of_last hj1, prevAt_of_eq (by rw [← hj1]; ring)]
        exact tr _ hin.2.2
      · have hm1 : 1 ≤ m := by
          have : (0 : V) < m := pos_iff_ne_zero.mpr hm0
          rw [lt_iff_succ_le, zero_add] at this; exact this
        have hlt : j + 1 < len (memberList c) := by
          rw [← hjc]; exact (add_lt_add_iff_left j).mpr (lt_add_of_pos_left 1 (pos_iff_ne_zero.mpr hm0))
        have hlt' : j + 1 + σ + 1 < len (memberList c) + 1 + σ := by
          have := (add_lt_add_iff_right (σ + 1)).mpr hlt
          calc j + 1 + σ + 1 = j + 1 + (σ + 1) := by ring
            _ < len (memberList c) + (σ + 1) := this
            _ = len (memberList c) + 1 + σ := by ring
        rw [prevI_of_lt hlt, prevAt_of_lt hlt']
        have h2 : jOf (len (memberList c)) (m - 1) = j + 1 := by
          have h1 : m - 1 + 1 = m := tsub_add_cancel_of_le hm1
          have := jOf_add (k := len (memberList c)) (c := m - 1) (by rw [h1]; exact le_of_lt (lt_of_lt_of_le (lt_add_one m) hm))
          rw [h1] at this
          have h3 : jOf (len (memberList c)) (m - 1) + m = (j + 1) + m := by rw [this, ← hjc]; ring
          exact add_right_cancel h3
        have := ifact hm1
        rw [hq, qK'_shPack, qSig_shPack, h2] at this
        have e1 : j + 1 + 1 + σ = j + 1 + σ + 1 := by ring
        have e2 : 0 + (len (memberList c) + 1 + (j + 1)) = 0 + (len (memberList c) + 1 + j) + 1 := by ring
        rwa [e1, e2] at this
    rw [IOut, loopI_succ]
    have key : ListOK tbl E ((8 : ℕ) : V) Γm (blockI q m) ∧ NoDrop (blockI q m) ∧ HornOnly (blockI q m) ∧
        shiftsV (blockI q m) = 0 ∧ len (blockI q m) = 1 ∧
        neg LAct (setShiftFact (^&(jOf (qK' q) m + 1 + qSig q)) (^&(0 + (qK' q + 1 + jOf (qK' q) m)))) ∈ finalCtx Γm (blockI q m) := by
      subst hq
      unfold blockI
      simp only [shX_pack, shY_pack, qW_shPack, qK'_shPack, qSig_shPack]
      rw [← hj]
      obtain ⟨ok₁, tg₁, cx₁⟩ := gok_setShiftInsert htbl hF2 rfl hΓmf (by unfold prevI; exact isSemiterm_prevAt _ _)
        (by unfold prevI; exact termLen_prevAt_le hsjE) (by simp) (termLen_fvar_le' hsjE1) (by simp) (termLen_fvar_le' hYE)
        (by simp) (termLen_fvar_le' hXE) (isSemiterm_prevAt _ _) (termLen_prevAt_le hujE) (by simp) (termLen_fvar_le' hujE1)
        (tr _ hins) hbelow (tr _ hsh) (tr _ hch)
      rw [← e144, ← hWp] at ok₁ tg₁ cx₁
      refine ⟨listOK_single ok₁, noDrop_single (Or.inl tg₁), hornOnly_single (Or.inl tg₁), shiftsV_single_tag0 tg₁, len_vec1 _, ?_⟩
      rw [finalCtx_single, cx₁]; exact memInsSelf _ _
    obtain ⟨bok, bnd, bho, bsh, blen, bfact⟩ := key
    refine ⟨listOK_appendV iok (by rw [← hΓm]; exact bok), noDrop_appendV ind bnd, hornOnly_appendV iho bho,
      by rw [shiftsV_appendV, ish, bsh, add_zero], by rw [len_appendV, ilen, blen], fun _ ↦ ?_⟩
    rw [finalCtx_appendV, ← hΓm, add_tsub_cancel_right]
    exact bfact

/-! ### 10.6 Fold U: `u_0 ⊆ S` (`insertSubset` up the `u` chain, `emptySubsetC` at the bottom) -/

noncomputable def uLink (q c : V) : V :=
  mkStep (qW q) 112 ?[prevAt (qK' q + 1 + qSig q) (jOf (qK' q) c + 1 + qSig q), ^&(qI q + (qK q + 1)),
    ^&(shX q (jOf (qK' q) c)), ^&(jOf (qK' q) c + 1 + qSig q)]

noncomputable def uLinkDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y q c. ∃ Wl, !pi₁Def Wl q ∧ ∃ r1, !pi₂Def r1 q ∧ ∃ W, !pi₁Def W r1 ∧ ∃ r2, !pi₂Def r2 r1 ∧ ∃ i, !pi₁Def i r2 ∧ ∃ r3, !pi₂Def r3 r2 ∧ ∃ k, !pi₁Def k r3 ∧ ∃ r4, !pi₂Def r4 r3 ∧ ∃ os, !pi₁Def os r4 ∧ ∃ r5, !pi₂Def r5 r4 ∧ ∃ xs, !pi₁Def xs r5 ∧ ∃ r6, !pi₂Def r6 r5 ∧ ∃ ip, !pi₁Def ip r6 ∧ ∃ r7, !pi₂Def r7 r6 ∧ ∃ kk, !pi₁Def kk r7 ∧ ∃ r8, !pi₂Def r8 r7 ∧ ∃ oss, !pi₁Def oss r8 ∧ ∃ r9, !pi₂Def r9 r8 ∧ ∃ ys, !pi₁Def ys r9 ∧ ∃ r10, !pi₂Def r10 r9 ∧ ∃ p, !pi₁Def p r10 ∧ ∃ sg, !pi₂Def sg r10 ∧
    ∃ j, !jOfDef j kk c ∧ ∃ a2, a2 = kk + 1 + sg ∧ ∃ b2, b2 = j + 1 + sg ∧ ∃ pu, !prevAtDef pu a2 b2 ∧ ∃ zu, !qqFvarDef zu b2 ∧
    ∃ iS, iS = i + (k + 1) ∧ ∃ zS, !qqFvarDef zS iS ∧
    ∃ yj, !nthDef yj ys j ∧ ∃ sh, !(shiftGraph LAct) sh yj ∧ ∃ jx, !idxOfDef jx xs sh ∧ ∃ oo, !nthDef oo os jx ∧
    ∃ tx, tx = i + (2 * k + 1 + oo) ∧ ∃ zx, !qqFvarDef zx tx ∧
    ∃ e₁, !adjoinDef e₁ zu 0 ∧ ∃ e₂, !adjoinDef e₂ zx e₁ ∧ ∃ e₃, !adjoinDef e₃ zS e₂ ∧ ∃ e₄, !adjoinDef e₄ pu e₃ ∧
    !mkStepDef y W 112 e₄”

set_option maxHeartbeats 1000000 in
instance uLink_defined : 𝚺₁-Function₂ (uLink : V → V → V) via uLinkDef := .mk fun v ↦ by
  simp [uLinkDef, uLink, shX, qWl, qW, qI, qK, qOs, qXs, qIp, qK', qOs', qYs, qP, qSig, mTop,
    jOf_defined.iff, prevAt_defined.iff, shift.defined.iff, idxOf_defined.iff, mkStep_defined.iff, numeral_eq_natCast]
instance uLink_definable : 𝚺₁-Function₂ (uLink : V → V → V) := uLink_defined.to_definable

namespace USub

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y q. ∃ r1, !pi₂Def r1 q ∧ ∃ W, !pi₁Def W r1 ∧ ∃ r2, !pi₂Def r2 r1 ∧ ∃ i, !pi₁Def i r2 ∧ ∃ r3, !pi₂Def r3 r2 ∧ ∃ k, !pi₁Def k r3 ∧
    ∃ iS, iS = i + (k + 1) ∧ ∃ zS, !qqFvarDef zS iS ∧ ∃ e, !adjoinDef e zS 0 ∧ ∃ s, !mkStepDef s W 81 e ∧ !adjoinDef y s 0”
  succ := .mkSigma “y ih c q. ∃ l, !uLinkDef l q c ∧ ∃ e, !adjoinDef e l 0 ∧ !appendVDef y ih e”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun v ↦ ?[mkStep (qW (v 0)) 81 ?[^&(qI (v 0) + (qK (v 0) + 1))]]
  succ := fun v c ih ↦ appendV ih ?[uLink (v 0) c]
  zero_defined := .mk fun v ↦ by simp [blueprint, qW, qI, qK, mkStep_defined.iff, numeral_eq_natCast]
  succ_defined := .mk fun v ↦ by simp [blueprint, uLink_defined.iff, appendV_defined.iff]

end USub

noncomputable def uSubAux (q c : V) : V := USub.construction.result ![q] c

lemma uSubAux_zero (q : V) : uSubAux q 0 = ?[mkStep (qW q) 81 ?[^&(qI q + (qK q + 1))]] := by
  simp [uSubAux, USub.construction]
lemma uSubAux_succ (q c : V) : uSubAux q (c + 1) = appendV (uSubAux q c) ?[uLink q c] := by
  simp [uSubAux, USub.construction]

noncomputable def uSubAuxDef : 𝚺₁.Semisentence 3 := USub.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance uSubAux_defined : 𝚺₁-Function₂ (uSubAux : V → V → V) via uSubAuxDef := .mk
  fun v ↦ by simp [USub.construction.result_defined_iff, uSubAuxDef]; rfl
instance uSubAux_definable : 𝚺₁-Function₂ (uSubAux : V → V → V) := uSubAux_defined.to_definable

/-- **`uSub q`** — `subsetFact u_0 S` from the chain over the shifted members. -/
noncomputable def uSub (q : V) : V := uSubAux q (qK' q)

/-- Fold U's invariant. -/
def UOut (tbl E q Γ c : V) : Prop :=
  ListOK tbl E ((8 : ℕ) : V) Γ (uSubAux q c) ∧ NoDrop (uSubAux q c) ∧ HornOnly (uSubAux q c) ∧
  shiftsV (uSubAux q c) = 0 ∧ len (uSubAux q c) = c + 1 ∧
  (c = 0 → neg LAct (subsetFact (𝟎 : V) (^&(qI q + (qK q + 1)))) ∈ finalCtx Γ (uSubAux q c)) ∧
  (1 ≤ c → neg LAct (subsetFact (^&(jOf (qK' q) (c - 1) + 1 + qSig q)) (^&(qI q + (qK q + 1)))) ∈ finalCtx Γ (uSubAux q c))

set_option maxHeartbeats 1000000 in
instance uOut_definable : 𝚫₁-Relation₅ (UOut : V → V → V → V → V → Prop) := by
  unfold UOut qI qK qK' qSig; definability

set_option maxHeartbeats 4000000 in
/-- **Fold U is applicable**, link by link. -/
theorem uSubAux_ok {tbl N W Wc T s c i₂ σ D E Γ q : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hq : q = shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s)
      (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ)
    (hs : IsFormulaSet LAct s) (hc : IsFormulaSet LAct c) (hsc : s = setShift LAct c)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D) (hcap : ShCap D E i₂ σ) (hΓ : IsFormulaSet LAct Γ)
    (hPL : Layout walkPieces Wc T Γ s i₂) (hin : ShIn Γ q) :
    ∀ m ≤ len (memberList c), UOut tbl E q Γ m := by
  have hW := hP.walkTable
  have hL := hP.layoutTable
  have hF1 := hP.frag1Table
  have e81 : ∀ ev : V, mkStep proPieces (81 : V) ev = mkStep layoutPieces (81 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 81 (by decide) ev; simpa using this
  have e112 : ∀ ev : V, mkStep proPieces (112 : V) ev = mkStep frag1Pieces (112 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag1 112 (by decide) ev; simpa using this
  have hkD : len (memberList s) ≤ D := le_trans (len_memberList_le_setLen hs) hsD
  have hk'D : len (memberList c) ≤ D := le_trans (len_memberList_le_setLen hc) hcD
  have hSE : i₂ + (len (memberList s) + 1) + 1 ≤ E := by
    calc i₂ + (len (memberList s) + 1) + 1 = i₂ + (len (memberList s) + 2) := by ring
      _ ≤ i₂ + (8 * D + 3) := add_le_add le_rfl (add_le_add (le_trans hkD (le_mul_of_one_le_left zero_le (by norm_num))) (by norm_num))
      _ = i₂ + 8 * D + 3 := by ring
      _ ≤ E := hcap.hi
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    rw [UOut, uSubAux_zero, hq, qW_shPack, qI_shPack, qK_shPack]
    obtain ⟨ok₀, tg₀, cx₀⟩ := lok_emptySubsetC htbl hL rfl hΓ (by simp) (termLen_fvar_le' hSE)
    rw [← e81, ← hWp] at ok₀ tg₀ cx₀
    refine ⟨listOK_single ok₀, noDrop_single (Or.inl tg₀), hornOnly_single (Or.inl tg₀),
      shiftsV_single_tag0 tg₀, by rw [len_vec1, zero_add], fun _ ↦ ?_, fun h ↦ absurd h (not_le.mpr _root_.zero_lt_one)⟩
    rw [finalCtx_single, cx₀]; exact memInsSelf _ _
  | succ m ih =>
    intro hm
    obtain ⟨uok, und, uho, ush, ulen, u0, u1⟩ := ih (le_trans le_self_add hm)
    set Γm := finalCtx Γ (uSubAux q m) with hΓm
    have hΓmf : IsFormulaSet LAct Γm := finalCtx_isFormulaSet 8 htbl hΓ uok
    have tr : ∀ x ∈ Γ, x ∈ Γm := fun x hx ↦ tr_of_zero und ush hx
    set j := jOf (len (memberList c)) m with hj
    have hjc : j + (m + 1) = len (memberList c) := jOf_add hm
    have hjk : j < len (memberList c) := by rw [← hjc]; exact lt_add_of_pos_right _ (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have hjD : j ≤ D := le_trans (le_of_lt hjk) hk'D
    have hxs : shift LAct (memberList c).[j] ∈ s := shift_mem_of_mem hsc (nth_memberList_mem hjk)
    obtain ⟨hlt', _⟩ := idxOf_spec hxs
    have hXle := mTop_le htbl hW hWc T hs hsD hlt' (i := i₂)
    have hXE : mTop i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) (shift LAct (memberList c).[j])] + 1 ≤ E := by
      calc _ ≤ i₂ + 6 * D + 1 + 1 := add_le_add hXle le_rfl
        _ = i₂ + (6 * D + 2) := by ring
        _ ≤ i₂ + (8 * D + 3) := add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num))
        _ = i₂ + 8 * D + 3 := by ring
        _ ≤ E := hcap.hi
    have hujE : j + 1 + σ + 2 ≤ E := by
      calc j + 1 + σ + 2 ≤ D + 1 + (6 * D + 1) + 2 := add_le_add (add_le_add (add_le_add hjD le_rfl) hcap.hσ) le_rfl
        _ = 7 * D + 4 := by ring
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := add_le_add (le_trans (mul_le_mul_of_nonneg_right (by norm_num) zero_le) le_self_add) (by norm_num)
        _ ≤ E := hcap.hE
    have hujE1 : j + 1 + σ + 1 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hujE
    -- the member fact and the chain fact
    obtain ⟨_, _, _, _, _, hmX⟩ := hPL.1 _ hlt'
    have hjk' : j < qK' q := by rw [hq, qK'_shPack]; exact hjk
    have hch := hin.1 j hjk'
    simp only [hq, qK'_shPack, qSig_shPack, shX_pack] at hch
    -- the subset fact below
    have hbelow : neg LAct (subsetFact (prevAt (len (memberList c) + 1 + σ) (j + 1 + σ)) (^&(i₂ + (len (memberList s) + 1)))) ∈ Γm := by
      by_cases hm0 : m = 0
      · have hj1 : j + 1 = len (memberList c) := by rw [← hjc, hm0, zero_add]
        rw [prevAt_of_eq (by rw [← hj1]; ring)]
        have := u0 hm0; rwa [hq, qI_shPack, qK_shPack] at this
      · have hm1 : 1 ≤ m := by
          have : (0 : V) < m := pos_iff_ne_zero.mpr hm0
          rw [lt_iff_succ_le, zero_add] at this; exact this
        have hlt : j + 1 < len (memberList c) := by
          rw [← hjc]; exact (add_lt_add_iff_left j).mpr (lt_add_of_pos_left 1 (pos_iff_ne_zero.mpr hm0))
        have hlt' : j + 1 + σ + 1 < len (memberList c) + 1 + σ := by
          have := (add_lt_add_iff_right (σ + 1)).mpr hlt
          calc j + 1 + σ + 1 = j + 1 + (σ + 1) := by ring
            _ < len (memberList c) + (σ + 1) := this
            _ = len (memberList c) + 1 + σ := by ring
        rw [prevAt_of_lt hlt']
        have h2 : jOf (len (memberList c)) (m - 1) = j + 1 := by
          have h1 : m - 1 + 1 = m := tsub_add_cancel_of_le hm1
          have := jOf_add (k := len (memberList c)) (c := m - 1) (by rw [h1]; exact le_of_lt (lt_of_lt_of_le (lt_add_one m) hm))
          rw [h1] at this
          have h3 : jOf (len (memberList c)) (m - 1) + m = (j + 1) + m := by rw [this, ← hjc]; ring
          exact add_right_cancel h3
        have := u1 hm1
        rw [hq, qK'_shPack, qSig_shPack, qI_shPack, qK_shPack, h2] at this
        have e1 : j + 1 + 1 + σ = j + 1 + σ + 1 := by ring
        rwa [e1] at this
    rw [UOut, uSubAux_succ]
    have key : ListOK tbl E ((8 : ℕ) : V) Γm (?[uLink q m] : V) ∧ NoDrop (?[uLink q m] : V) ∧ HornOnly (?[uLink q m] : V) ∧
        shiftsV (?[uLink q m] : V) = 0 ∧
        neg LAct (subsetFact (^&(jOf (qK' q) m + 1 + qSig q)) (^&(qI q + (qK q + 1)))) ∈ finalCtx Γm (?[uLink q m] : V) := by
      subst hq
      unfold uLink
      simp only [shX_pack, qW_shPack, qI_shPack, qK_shPack, qK'_shPack, qSig_shPack]
      rw [← hj]
      obtain ⟨ok₁, tg₁, cx₁⟩ := fok_insertSubset htbl hF1 rfl hΓmf (isSemiterm_prevAt _ _) (termLen_prevAt_le hujE)
        (by simp) (termLen_fvar_le' hSE) (by simp) (termLen_fvar_le' hXE) (by simp) (termLen_fvar_le' hujE1)
        hbelow (tr _ hmX) (tr _ hch)
      rw [← e112, ← hWp] at ok₁ tg₁ cx₁
      refine ⟨listOK_single ok₁, noDrop_single (Or.inl tg₁), hornOnly_single (Or.inl tg₁), shiftsV_single_tag0 tg₁, ?_⟩
      rw [finalCtx_single, cx₁]; exact memInsSelf _ _
    obtain ⟨bok, bnd, bho, bsh, bfact⟩ := key
    refine ⟨listOK_appendV uok (by rw [← hΓm]; exact bok), noDrop_appendV und bnd, hornOnly_appendV uho bho,
      by rw [shiftsV_appendV, ush, bsh, add_zero], by rw [len_appendV, ulen, len_vec1],
      fun h ↦ absurd h (ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_add_self)), fun _ ↦ ?_⟩
    rw [finalCtx_appendV, ← hΓm, add_tsub_cancel_right]
    exact bfact

/-- **`uSub` is applicable** and leaves `subsetFact u_0 S` (`u_0 = &(0 + 1 + σ)`, `S = &(i₂ + (k + 1))`). -/
theorem uSub_ok {tbl N W Wc T s c i₂ σ D E Γ q : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hq : q = shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s)
      (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ)
    (hs : IsFormulaSet LAct s) (hc : IsFormulaSet LAct c) (hsc : s = setShift LAct c) (hk1 : 1 ≤ len (memberList c))
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D) (hcap : ShCap D E i₂ σ) (hΓ : IsFormulaSet LAct Γ)
    (hPL : Layout walkPieces Wc T Γ s i₂) (hin : ShIn Γ q) :
    ListOK tbl E ((8 : ℕ) : V) Γ (uSub q) ∧ NoDrop (uSub q) ∧ HornOnly (uSub q) ∧ shiftsV (uSub q) = 0 ∧
    len (uSub q) = len (memberList c) + 1 ∧
    neg LAct (subsetFact (^&(0 + 1 + σ)) (^&(i₂ + (len (memberList s) + 1)))) ∈ finalCtx Γ (uSub q) := by
  subst hq
  obtain ⟨uok, und, uho, ush, ulen, _, u1⟩ := uSubAux_ok htbl hP hWc hWp rfl hs hc hsc hsD hcD hcap hΓ hPL hin _ le_rfl
  have hj : jOf (len (memberList c)) (len (memberList c) - 1) = 0 := by
    have h1 : len (memberList c) - 1 + 1 = len (memberList c) := tsub_add_cancel_of_le hk1
    have := jOf_add (k := len (memberList c)) (c := len (memberList c) - 1) (by rw [h1])
    rw [h1] at this
    exact add_right_cancel (by rw [this, zero_add] : jOf (len (memberList c)) (len (memberList c) - 1) + len (memberList c) = 0 + len (memberList c))
  unfold uSub
  rw [qK'_shPack]
  refine ⟨uok, und, uho, ush, ulen, ?_⟩
  have h := u1 hk1
  rw [qK'_shPack, qSig_shPack, qI_shPack, qK_shPack, hj] at h
  exact h

/-! ### 10.7 Loop M: `memFact X_{π j} u_0` for every child member (`shiftMemSetShift`) -/

noncomputable def blockM (q j : V) : V :=
  ?[mkStep (qW q) 139 ?[^&(0 + (qK' q + 1)), ^&(shY q j), ^&(0 + 1 + qSig q), ^&(shX q j)]]

noncomputable def blockMDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y q j. ∃ Wl, !pi₁Def Wl q ∧ ∃ r1, !pi₂Def r1 q ∧ ∃ W, !pi₁Def W r1 ∧ ∃ r2, !pi₂Def r2 r1 ∧ ∃ i, !pi₁Def i r2 ∧ ∃ r3, !pi₂Def r3 r2 ∧ ∃ k, !pi₁Def k r3 ∧ ∃ r4, !pi₂Def r4 r3 ∧ ∃ os, !pi₁Def os r4 ∧ ∃ r5, !pi₂Def r5 r4 ∧ ∃ xs, !pi₁Def xs r5 ∧ ∃ r6, !pi₂Def r6 r5 ∧ ∃ ip, !pi₁Def ip r6 ∧ ∃ r7, !pi₂Def r7 r6 ∧ ∃ kk, !pi₁Def kk r7 ∧ ∃ r8, !pi₂Def r8 r7 ∧ ∃ oss, !pi₁Def oss r8 ∧ ∃ r9, !pi₂Def r9 r8 ∧ ∃ ys, !pi₁Def ys r9 ∧ ∃ r10, !pi₂Def r10 r9 ∧ ∃ p, !pi₁Def p r10 ∧ ∃ sg, !pi₂Def sg r10 ∧
    ∃ is, is = 0 + (kk + 1) ∧ ∃ zs, !qqFvarDef zs is ∧ ∃ oj, !nthDef oj oss j ∧ ∃ ty, ty = 0 + (2 * kk + 1 + oj) ∧ ∃ zy, !qqFvarDef zy ty ∧
    ∃ iu, iu = 0 + 1 + sg ∧ ∃ zu, !qqFvarDef zu iu ∧
    ∃ yj, !nthDef yj ys j ∧ ∃ sh, !(shiftGraph LAct) sh yj ∧ ∃ jx, !idxOfDef jx xs sh ∧ ∃ oo, !nthDef oo os jx ∧
    ∃ tx, tx = i + (2 * k + 1 + oo) ∧ ∃ zx, !qqFvarDef zx tx ∧
    ∃ e₁, !adjoinDef e₁ zx 0 ∧ ∃ e₂, !adjoinDef e₂ zu e₁ ∧ ∃ e₃, !adjoinDef e₃ zy e₂ ∧ ∃ e₄, !adjoinDef e₄ zs e₃ ∧
    ∃ st, !mkStepDef st W 139 e₄ ∧ !adjoinDef y st 0”

set_option maxHeartbeats 1000000 in
instance blockM_defined : 𝚺₁-Function₂ (blockM : V → V → V) via blockMDef := .mk fun v ↦ by
  simp [blockMDef, blockM, shX, shY, qWl, qW, qI, qK, qOs, qXs, qIp, qK', qOs', qYs, qP, qSig, mTop,
    shift.defined.iff, idxOf_defined.iff, mkStep_defined.iff, numeral_eq_natCast]
instance blockM_definable : 𝚺₁-Function₂ (blockM : V → V → V) := blockM_defined.to_definable

namespace LoopM

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y q. y = 0”
  succ := .mkSigma “y ih j q. ∃ b, !blockMDef b q j ∧ !appendVDef y ih b”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 0
  succ := fun v j ih ↦ appendV ih (blockM (v 0) j)
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, blockM_defined.iff, appendV_defined.iff]

end LoopM

noncomputable def loopM (q m : V) : V := LoopM.construction.result ![q] m

@[simp] lemma loopM_zero (q : V) : loopM q 0 = 0 := by simp [loopM, LoopM.construction]
lemma loopM_succ (q m : V) : loopM q (m + 1) = appendV (loopM q m) (blockM q m) := by simp [loopM, LoopM.construction]

noncomputable def loopMDef : 𝚺₁.Semisentence 3 := LoopM.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance loopM_defined : 𝚺₁-Function₂ (loopM : V → V → V) via loopMDef := .mk
  fun v ↦ by simp [LoopM.construction.result_defined_iff, loopMDef]; rfl
instance loopM_definable : 𝚺₁-Function₂ (loopM : V → V → V) := loopM_defined.to_definable

/-- Loop M's invariant. -/
def MOut (tbl E q Γ m : V) : Prop :=
  ListOK tbl E ((8 : ℕ) : V) Γ (loopM q m) ∧ NoDrop (loopM q m) ∧ HornOnly (loopM q m) ∧ shiftsV (loopM q m) = 0 ∧
  ∀ j < m, neg LAct (memFact (^&(shX q j)) (^&(0 + 1 + qSig q))) ∈ finalCtx Γ (loopM q m)

set_option maxHeartbeats 1000000 in
instance mOut_definable : 𝚫₁-Relation₅ (MOut : V → V → V → V → V → Prop) := by
  unfold MOut shX qI qK qOs qXs qYs qSig mTop; definability

set_option maxHeartbeats 4000000 in
/-- **Loop M is applicable**: every shifted member is in `u_0`. -/
theorem loopM_ok {tbl N W Wc T s c i₂ σ D E Γ q : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hq : q = shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s)
      (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ)
    (hs : IsFormulaSet LAct s) (hc : IsFormulaSet LAct c) (hsc : s = setShift LAct c)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D) (hcap : ShCap D E i₂ σ) (hΓ : IsFormulaSet LAct Γ)
    (hCL : Layout walkPieces Wc T Γ c 0) (hin : ShIn Γ q)
    (hss : neg LAct (setShiftFact (^&(0 + 1 + σ)) (^&(0 + (len (memberList c) + 1)))) ∈ Γ) :
    ∀ m ≤ len (memberList c), MOut tbl E q Γ m := by
  have hW := hP.walkTable
  have hF2 := hP.frag2Table
  have e139 : ∀ ev : V, mkStep proPieces (139 : V) ev = mkStep frag2Pieces (139 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag2 139 (by decide) ev; simpa using this
  have hk'D : len (memberList c) ≤ D := le_trans (len_memberList_le_setLen hc) hcD
  have hs''E : 0 + (len (memberList c) + 1) + 1 ≤ E := by
    calc 0 + (len (memberList c) + 1) + 1 ≤ 0 + (D + 1) + 1 := add_le_add (add_le_add le_rfl (add_le_add hk'D le_rfl)) le_rfl
      _ = D + 2 := by ring
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := add_le_add (le_trans le_thirteen_mul le_self_add) (by norm_num)
      _ ≤ E := hcap.hE
  have hu0E : 0 + 1 + σ + 1 ≤ E := by
    calc 0 + 1 + σ + 1 ≤ 0 + 1 + (6 * D + 1) + 1 := add_le_add (add_le_add le_rfl hcap.hσ) le_rfl
      _ = 6 * D + 3 := by ring
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
      _ ≤ E := hcap.hE
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    exact ⟨by rw [loopM_zero]; exact listOK_nil _ _ _ _, by rw [loopM_zero]; exact noDrop_nil,
      by rw [loopM_zero]; exact hornOnly_nil, by rw [loopM_zero, shiftsV_nil], fun j hj ↦ absurd hj (by simp)⟩
  | succ m ih =>
    intro hm
    obtain ⟨mok, mnd, mho, msh, mfacts⟩ := ih (le_trans le_self_add hm)
    have hmk : m < len (memberList c) := lt_of_lt_of_le (lt_add_one m) hm
    set Γm := finalCtx Γ (loopM q m) with hΓm
    have hΓmf : IsFormulaSet LAct Γm := finalCtx_isFormulaSet 8 htbl hΓ mok
    have tr : ∀ x ∈ Γ, x ∈ Γm := fun x hx ↦ tr_of_zero mnd msh hx
    have hxs : shift LAct (memberList c).[m] ∈ s := shift_mem_of_mem hsc (nth_memberList_mem hmk)
    obtain ⟨hlt', _⟩ := idxOf_spec hxs
    have hXle := mTop_le htbl hW hWc T hs hsD hlt' (i := i₂)
    have hYle := mTop_le htbl hW hWc T hc hcD hmk (i := 0)
    have hXE : mTop i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) (shift LAct (memberList c).[m])] + 1 ≤ E := by
      calc _ ≤ i₂ + 6 * D + 1 + 1 := add_le_add hXle le_rfl
        _ = i₂ + (6 * D + 2) := by ring
        _ ≤ i₂ + (8 * D + 3) := add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num))
        _ = i₂ + 8 * D + 3 := by ring
        _ ≤ E := hcap.hi
    have hYE : mTop 0 (len (memberList c)) (offVec (memberList c) walkPieces Wc T).[m] + 1 ≤ E := by
      calc _ ≤ 0 + 6 * D + 1 + 1 := add_le_add hYle le_rfl
        _ = 6 * D + 2 := by ring
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
        _ ≤ E := hcap.hE
    obtain ⟨_, _, _, _, _, hmY⟩ := hCL.1 m hmk
    have hmk' : m < qK' q := by rw [hq, qK'_shPack]; exact hmk
    have hsh := hin.2.1 m hmk'
    simp only [hq, shX_pack, shY_pack] at hsh
    rw [MOut, loopM_succ]
    have key : ListOK tbl E ((8 : ℕ) : V) Γm (blockM q m) ∧ NoDrop (blockM q m) ∧ HornOnly (blockM q m) ∧
        shiftsV (blockM q m) = 0 ∧ neg LAct (memFact (^&(shX q m)) (^&(0 + 1 + qSig q))) ∈ finalCtx Γm (blockM q m) := by
      subst hq
      unfold blockM
      simp only [shX_pack, shY_pack, qW_shPack, qK'_shPack, qSig_shPack]
      obtain ⟨ok₁, tg₁, cx₁⟩ := gok_shiftMemSetShift htbl hF2 rfl hΓmf (by simp) (termLen_fvar_le' hs''E)
        (by simp) (termLen_fvar_le' hYE) (by simp) (termLen_fvar_le' hu0E) (by simp) (termLen_fvar_le' hXE)
        (tr _ hmY) (tr _ hss) (tr _ hsh)
      rw [← e139, ← hWp] at ok₁ tg₁ cx₁
      refine ⟨listOK_single ok₁, noDrop_single (Or.inl tg₁), hornOnly_single (Or.inl tg₁), shiftsV_single_tag0 tg₁, ?_⟩
      rw [finalCtx_single, cx₁]; exact memInsSelf _ _
    obtain ⟨bok, bnd, bho, bsh, bfact⟩ := key
    refine ⟨listOK_appendV mok (by rw [← hΓm]; exact bok), noDrop_appendV mnd bnd, hornOnly_appendV mho bho,
      by rw [shiftsV_appendV, msh, bsh, add_zero], fun j hj ↦ ?_⟩
    rw [finalCtx_appendV, ← hΓm]
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hj) with h | rfl
    · exact tr_of_zero bnd bsh (mfacts j h)
    · exact bfact

/-! ### 10.8 The whole `shift` prologue -/

lemma jOf_last {k' : V} (hk1 : 1 ≤ k') : jOf k' (k' - 1) = 0 := by
  have h1 : k' - 1 + 1 = k' := tsub_add_cancel_of_le hk1
  have := jOf_add (k := k') (c := k' - 1) (by rw [h1])
  rw [h1] at this
  exact add_right_cancel (by rw [this, zero_add] : jOf k' (k' - 1) + k' = 0 + k')

/-- The Horn-only tail of the `shift` prologue at the frame `shPack Wc W i₂ k os xs k' os' ys σ`: Loop S, Loop I,
Fold U, Loop M, the parent's `subChain` against `u_0`, `subsetAntisymm [S, u_0]`, `congSetShiftL [u_0, S, s'']`. -/
noncomputable def shTail (Ww Wc W T s c i₂ σ : V) : V :=
  appendV (loopS (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) Ww Wc T) (memberList s) (len (memberList c))
      (offVec (memberList c) Ww Wc T) (memberList c) σ) (len (memberList c)))
    (appendV (loopI (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) Ww Wc T) (memberList s) (len (memberList c))
        (offVec (memberList c) Ww Wc T) (memberList c) σ) (len (memberList c)))
      (appendV (uSub (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) Ww Wc T) (memberList s) (len (memberList c))
          (offVec (memberList c) Ww Wc T) (memberList c) σ))
        (appendV (loopM (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) Ww Wc T) (memberList s) (len (memberList c))
            (offVec (memberList c) Ww Wc T) (memberList c) σ) (len (memberList c)))
          (appendV (subChain W i₂ (len (memberList s)) (offVec (memberList s) Ww Wc T) (^&(0 + 1 + σ)))
            ?[mkStep W 75 ?[^&(i₂ + (len (memberList s) + 1)), ^&(0 + 1 + σ)],
              mkStep W 148 ?[^&(0 + 1 + σ), ^&(i₂ + (len (memberList s) + 1)), ^&(0 + (len (memberList c) + 1))]]))))

noncomputable def shTailDef : 𝚺₁.Semisentence 9 := .mkSigma
  “y Ww Wc W T s c i σ. ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧ ∃ os, !offVecDef os xs Ww Wc T ∧
    ∃ ys, !memberListDef ys c ∧ ∃ kk, !lenDef kk ys ∧ ∃ oss, !offVecDef oss ys Ww Wc T ∧
    ∃ q₁₁, !pairDef q₁₁ 0 σ ∧ ∃ q₁₀, !pairDef q₁₀ ys q₁₁ ∧ ∃ q₉, !pairDef q₉ oss q₁₀ ∧ ∃ q₈, !pairDef q₈ kk q₉ ∧
    ∃ q₇, !pairDef q₇ 0 q₈ ∧ ∃ q₆, !pairDef q₆ xs q₇ ∧ ∃ q₅, !pairDef q₅ os q₆ ∧ ∃ q₄, !pairDef q₄ k q₅ ∧
    ∃ q₃, !pairDef q₃ i q₄ ∧ ∃ q₂, !pairDef q₂ W q₃ ∧ ∃ q, !pairDef q Wc q₂ ∧
    ∃ A, !loopSDef A q kk ∧ ∃ B, !loopIDef B q kk ∧ ∃ U, !uSubAuxDef U q kk ∧ ∃ M, !loopMDef M q kk ∧
    ∃ iu, iu = 0 + 1 + σ ∧ ∃ zu, !qqFvarDef zu iu ∧ ∃ C, !subChainDef C W i k os zu ∧
    ∃ iS, iS = i + (k + 1) ∧ ∃ zS, !qqFvarDef zS iS ∧ ∃ is, is = 0 + (kk + 1) ∧ ∃ zs, !qqFvarDef zs is ∧
    ∃ a₁, !adjoinDef a₁ zu 0 ∧ ∃ a₂, !adjoinDef a₂ zS a₁ ∧ ∃ s₁, !mkStepDef s₁ W 75 a₂ ∧
    ∃ b₁, !adjoinDef b₁ zs 0 ∧ ∃ b₂, !adjoinDef b₂ zS b₁ ∧ ∃ b₃, !adjoinDef b₃ zu b₂ ∧ ∃ s₂, !mkStepDef s₂ W 148 b₃ ∧
    ∃ l₂, !adjoinDef l₂ s₂ 0 ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧
    ∃ r₅, !appendVDef r₅ C l₁ ∧ ∃ r₄, !appendVDef r₄ M r₅ ∧ ∃ r₃, !appendVDef r₃ U r₄ ∧ ∃ r₂, !appendVDef r₂ B r₃ ∧
    !appendVDef y A r₂”

set_option maxHeartbeats 1000000 in
instance shTail_defined :
    𝚺₁.DefinedFunction (fun v : Fin 8 → V ↦ shTail (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) shTailDef := .mk
  fun v ↦ by
    simp [shTailDef, shTail, uSub, shPack, qPack, qK', memberList_defined.iff, offVec_defined.iff, loopS_defined.iff,
      loopI_defined.iff, uSubAux_defined.iff, loopM_defined.iff, subChain_defined.iff, mkStep_defined.iff,
      appendV_defined.iff, numeral_eq_natCast]

/-- **`proShift c`**: `shBase` (one eigenvariable, `setShiftFact 𝟎 𝟎`), the chain over the shifted members read at
the parent's layout at `i + 1` (`k' + 1` eigenvariables; `u_j = &(j + 1)`), the child's layout (`σ` eigenvariables),
then the Horn-only tail. -/
noncomputable def proShift (Ww Wl Wc W T s c i : V) : V :=
  appendV (shBase W)
    (appendV (chainSteps Wl (fvarVec (shPos (memberList c) (memberList s) (offVec (memberList s) Ww Wc T) (len (memberList s)) (i + 1))))
      (appendV (layoutSteps Ww Wl Wc W T c)
        (shTail Ww Wc W T s c (i + 1 + (len (memberList c) + 1) + proSig Ww Wl Wc W T c) (proSig Ww Wl Wc W T c))))

noncomputable def proShiftDef : 𝚺₁.Semisentence 9 := .mkSigma
  “y Ww Wl Wc W T s c i. ∃ Bs, !shBaseDef Bs W ∧ ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧ ∃ os, !offVecDef os xs Ww Wc T ∧
    ∃ ys, !memberListDef ys c ∧ ∃ kk, !lenDef kk ys ∧ ∃ i₁, i₁ = i + 1 ∧ ∃ ps, !shPosDef ps ys xs os k i₁ ∧
    ∃ fv, !fvarVecDef fv ps ∧ ∃ C, !chainStepsDef C Wl fv ∧ ∃ L, !layoutStepsDef L Ww Wl Wc W T c ∧ ∃ σ, !shiftsVDef σ L ∧
    ∃ i₂, i₂ = i + 1 + (kk + 1) + σ ∧ ∃ Tl, !shTailDef Tl Ww Wc W T s c i₂ σ ∧
    ∃ r₂, !appendVDef r₂ L Tl ∧ ∃ r₁, !appendVDef r₁ C r₂ ∧ !appendVDef y Bs r₁”

set_option maxHeartbeats 1000000 in
instance proShift_defined :
    𝚺₁.DefinedFunction (fun v : Fin 8 → V ↦ proShift (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) proShiftDef := .mk
  fun v ↦ by
    simp [proShiftDef, proShift, proSig, shBase_defined.iff, memberList_defined.iff, offVec_defined.iff, shPos_defined.iff,
      fvarVec_defined.iff, chainSteps_defined.iff, layoutSteps_defined.iff, shiftsV_defined.iff, shTail_defined.iff,
      appendV_defined.iff, numeral_eq_natCast]

/-- The nonempty shift of a nonempty sequent. -/
lemma one_le_len_memberList_setShift {s c : V} (hsc : s = setShift LAct c) (hk1 : 1 ≤ len (memberList c)) :
    1 ≤ len (memberList s) := by
  have hy : (memberList c).[0] ∈ c := nth_memberList_mem (lt_of_lt_of_le _root_.zero_lt_one hk1)
  obtain ⟨hlt, _⟩ := idxOf_spec (shift_mem_of_mem hsc hy)
  have := lt_iff_succ_le.mp (lt_of_le_of_lt zero_le hlt); rwa [zero_add] at this

/-- The state after the eigenvariable-introducing prefix `shBase ++ chainSteps ++ layoutSteps c ++ loopS`: both layouts
and the tail's inputs `ShIn` at the frame. -/
def ShState (Wc T Γ s c i₂ σ : V) : Prop :=
  IsFormulaSet LAct Γ ∧ Layout walkPieces Wc T Γ c 0 ∧ Layout walkPieces Wc T Γ s i₂ ∧
  ShIn Γ (shPack Wc (proPieces : V) i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s)
    (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ)

/-- The eigenvariable-introducing prefix of `proShift`. -/
noncomputable def proShiftPre (Ww Wl Wc W T s c i : V) : V :=
  appendV (shBase W)
    (appendV (chainSteps Wl (fvarVec (shPos (memberList c) (memberList s) (offVec (memberList s) Ww Wc T) (len (memberList s)) (i + 1))))
      (appendV (layoutSteps Ww Wl Wc W T c)
        (loopS (shPack Wc W (i + 1 + (len (memberList c) + 1) + proSig Ww Wl Wc W T c) (len (memberList s))
          (offVec (memberList s) Ww Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) Ww Wc T) (memberList c)
          (proSig Ww Wl Wc W T c)) (len (memberList c)))))

/-- The Horn-only tail after Loop S. -/
noncomputable def shTail2 (Ww Wc W T s c i₂ σ : V) : V :=
  appendV (loopI (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) Ww Wc T) (memberList s) (len (memberList c))
      (offVec (memberList c) Ww Wc T) (memberList c) σ) (len (memberList c)))
    (appendV (uSub (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) Ww Wc T) (memberList s) (len (memberList c))
        (offVec (memberList c) Ww Wc T) (memberList c) σ))
      (appendV (loopM (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) Ww Wc T) (memberList s) (len (memberList c))
          (offVec (memberList c) Ww Wc T) (memberList c) σ) (len (memberList c)))
        (appendV (subChain W i₂ (len (memberList s)) (offVec (memberList s) Ww Wc T) (^&(0 + 1 + σ)))
          ?[mkStep W 75 ?[^&(i₂ + (len (memberList s) + 1)), ^&(0 + 1 + σ)],
            mkStep W 148 ?[^&(0 + 1 + σ), ^&(i₂ + (len (memberList s) + 1)), ^&(0 + (len (memberList c) + 1))]])))

lemma shTail_eq (Ww Wc W T s c i₂ σ : V) :
    shTail Ww Wc W T s c i₂ σ = appendV (loopS (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) Ww Wc T) (memberList s)
      (len (memberList c)) (offVec (memberList c) Ww Wc T) (memberList c) σ) (len (memberList c))) (shTail2 Ww Wc W T s c i₂ σ) := rfl

lemma proShift_eq (Ww Wl Wc W T s c i : V) :
    proShift Ww Wl Wc W T s c i = appendV (proShiftPre Ww Wl Wc W T s c i)
      (shTail2 Ww Wc W T s c (i + 1 + (len (memberList c) + 1) + proSig Ww Wl Wc W T c) (proSig Ww Wl Wc W T c)) := by
  unfold proShift proShiftPre shTail2 shTail
  rw [appendV_assoc, appendV_assoc, appendV_assoc]

set_option maxHeartbeats 4000000 in
/-- **The prefix is applicable** and leaves the state `ShState` at `i₂ = i + 1 + (k' + 1) + σ`. -/
theorem proShiftPre_ok {tbl N N' B' Wl Wc W T s c i D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hs : IsFormulaSet LAct s) (hc : IsFormulaSet LAct c) (hsc : s = setShift LAct c) (hk1' : 1 ≤ (len (memberList c)))
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D) (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : i + 16 * D + 8 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s i) :
    ListOK tbl E ((8 : ℕ) : V) Γ (proShiftPre walkPieces Wl Wc W T s c i) ∧ NoDrop' (proShiftPre walkPieces Wl Wc W T s c i) ∧
    shiftsV (proShiftPre walkPieces Wl Wc W T s c i) = 1 + ((len (memberList c)) + 1) + proSig walkPieces Wl Wc W T c ∧
    ShState Wc T (finalCtx Γ (proShiftPre walkPieces Wl Wc W T s c i)) s c
      (i + 1 + ((len (memberList c)) + 1) + proSig walkPieces Wl Wc W T c) (proSig walkPieces Wl Wc W T c) ∧
    HornOnly (loopS (shPack Wc W (i + 1 + (len (memberList c) + 1) + proSig walkPieces Wl Wc W T c) (len (memberList s))
      (offVec (memberList s) walkPieces Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) walkPieces Wc T)
      (memberList c) (proSig walkPieces Wl Wc W T c)) (len (memberList c))) := by
  have hW := hP.walkTable
  have hL := hP.layoutTable
  have hkD : (len (memberList s)) ≤ D := le_trans (len_memberList_le_setLen hs) hsD
  have hk'D : (len (memberList c)) ≤ D := le_trans (len_memberList_le_setLen hc) hcD
  have hE8 : 13 * D + 18 * ‖D‖ + 8 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hE
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hE)
  set σ := proSig walkPieces Wl Wc W T c with hσ
  have hσle : σ ≤ 6 * D + 1 := proSig_le htbl hP hWc htblN hWl hWp hc hk1' hcD hE8 hΓ
  set i₂ := i + 1 + ((len (memberList c)) + 1) + σ with hi₂
  have hi₂le : i₂ + 8 * D + 3 ≤ E := by
    calc i₂ + 8 * D + 3 = i + 1 + ((len (memberList c)) + 1) + σ + 8 * D + 3 := by rw [hi₂]
      _ ≤ i + 1 + (D + 1) + (6 * D + 1) + 8 * D + 3 := add_le_add (add_le_add (add_le_add (add_le_add le_rfl (add_le_add hk'D le_rfl)) hσle) le_rfl) le_rfl
      _ = i + 15 * D + 6 := by ring
      _ ≤ i + 16 * D + 8 := add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) (by norm_num)
      _ ≤ E := hiE
  -- (1) the base
  obtain ⟨bok, bnd, bsh, _, bfact⟩ := shBase_ok htbl hP hWp hΓ hE1
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ (shBase W) := ⟨_, rfl⟩
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 8 htbl hΓ bok
  have hLay₁ : Layout walkPieces Wc T Γ₁ s (i + 1) := by rw [hΓ₁]; have := hLay.transport bnd; rwa [bsh] at this
  have hb₁ : neg LAct (setShiftFact (𝟎 : V) (𝟎 : V)) ∈ Γ₁ := by rw [hΓ₁]; exact bfact
  -- (2) the chain over the shifted members
  set ps := shPos (memberList c) (memberList s) (offVec (memberList s) walkPieces Wc T) (len (memberList s)) (i + 1) with hps
  have hps_len : len ps = (len (memberList c)) := by rw [hps, len_shPos]
  set xs₀ := fvarVec ps with hxs₀
  have hxs₀_len : len xs₀ = (len (memberList c)) := by rw [hxs₀, len_fvarVec, hps_len]
  have hnth₀ : ∀ j < (len (memberList c)), xs₀.[j] = ^&(mTop (i + 1) (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) (shift LAct (memberList c).[j])]) := fun j hj ↦ by
    rw [hxs₀, nth_fvarVec ps j (hps_len ▸ hj), hps, nth_shPos (memberList s) (offVec (memberList s) walkPieces Wc T) (len (memberList s)) (i + 1) (memberList c) j hj]
  have hπ : ∀ j < (len (memberList c)), idxOf (memberList s) (shift LAct (memberList c).[j]) < (len (memberList s)) := fun j hj ↦
    (idxOf_spec (shift_mem_of_mem hsc (nth_memberList_mem hj))).1
  have hkE : (len (memberList c)) + 2 ≤ E := le_trans (add_le_add (le_trans hk'D le_thirteen_mul) (by norm_num)) (le_trans (add_le_add le_self_add le_rfl) hE8)
  have hxs₀' : ∀ j < len xs₀, IsSemiterm LAct 0 xs₀.[j] ∧ termLen LAct (termShiftIterV xs₀.[j] (len xs₀ + 1)) ≤ E ∧
      neg LAct (piFact (𝟎 : V) xs₀.[j]) ∈ Γ₁ := fun j hj ↦ by
    rw [hxs₀_len] at hj ⊢
    rw [hnth₀ j hj, termShiftIterV_fvar, termLen_fvar]
    refine ⟨by simp, ?_, (hLay₁.1 _ (hπ j hj)).2.1⟩
    calc mTop (i + 1) (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) (shift LAct (memberList c).[j])] + ((len (memberList c)) + 1) + 1 ≤ (i + 1 + 6 * D + 1) + (D + 1) + 1 :=
          add_le_add (add_le_add (mTop_le htbl hW hWc T hs hsD (hπ j hj)) (add_le_add hk'D le_rfl)) le_rfl
      _ = i + 7 * D + 4 := by ring
      _ ≤ i + 16 * D + 8 := add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) (by norm_num)
      _ ≤ E := hiE
  obtain ⟨cok, cnd, cho, csh, clen, cfacts, _⟩ := chainSteps_ok htbl hL hWl hΓ₁f (by rw [hxs₀_len]; exact hk1') (by rw [hxs₀_len]; exact hkE) hxs₀'
  rw [hxs₀_len] at csh cfacts
  obtain ⟨Γ₂, hΓ₂⟩ : ∃ Γ', Γ' = finalCtx Γ₁ (chainSteps Wl xs₀) := ⟨_, rfl⟩
  have hΓ₂f : IsFormulaSet LAct Γ₂ := by rw [hΓ₂]; exact finalCtx_isFormulaSet 8 htbl hΓ₁f cok
  have hLay₂ : Layout walkPieces Wc T Γ₂ s (i + 1 + ((len (memberList c)) + 1)) := by
    rw [hΓ₂]; have := hLay₁.transport cnd.noDrop'; rwa [csh] at this
  have hb₂ : neg LAct (setShiftFact (𝟎 : V) (𝟎 : V)) ∈ Γ₂ := by
    rw [hΓ₂]
    have := mem_finalCtx_of_mem cnd hb₁
    rwa [shiftIterV_neg (isFormula_setShiftFact isSemiterm_zeroV isSemiterm_zeroV), shiftIterV_setShiftFact isSemiterm_zeroV isSemiterm_zeroV,
      termShiftIterV_zeroV] at this
  have hch₂ : ∀ j < (len (memberList c)), neg LAct (insFact (^&(j + 1)) (^&(mTop (i + 1) (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) (shift LAct (memberList c).[j])] + ((len (memberList c)) + 1)))
      (prevAt ((len (memberList c)) + 1) (j + 1))) ∈ Γ₂ := fun j hj ↦ by
    rw [hΓ₂]
    have := (cfacts j hj).1
    rwa [hnth₀ j hj, termShiftIterV_fvar] at this
  -- (3) the child's layout
  obtain ⟨lok, lnd, _, _, lLay⟩ := layoutSteps_ok htbl hP htblN hWl hWc hWp hc hk1' hcD hE8 hΓ₂f
  have lsh : shiftsV (layoutSteps walkPieces Wl Wc W T c) = σ := by rw [hσ, proSig]
  obtain ⟨Γ₃, hΓ₃⟩ : ∃ Γ', Γ' = finalCtx Γ₂ (layoutSteps walkPieces Wl Wc W T c) := ⟨_, rfl⟩
  have hΓ₃f : IsFormulaSet LAct Γ₃ := by rw [hΓ₃]; exact finalCtx_isFormulaSet 8 htbl hΓ₂f lok
  have lLay₃ : Layout walkPieces Wc T Γ₃ c 0 := by rw [hΓ₃]; exact lLay
  have hLay₃ : Layout walkPieces Wc T Γ₃ s i₂ := by rw [hΓ₃]; have := hLay₂.transport lnd; rwa [lsh] at this
  have hb₃ : neg LAct (setShiftFact (𝟎 : V) (𝟎 : V)) ∈ Γ₃ := by
    rw [hΓ₃]
    have := mem_finalCtx_of_mem' lnd hb₂
    rwa [shiftIterV_neg (isFormula_setShiftFact isSemiterm_zeroV isSemiterm_zeroV), shiftIterV_setShiftFact isSemiterm_zeroV isSemiterm_zeroV,
      termShiftIterV_zeroV] at this
  have hch₃ : ∀ j < (len (memberList c)), neg LAct (insFact (^&(j + 1 + σ)) (^&(mTop i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) (shift LAct (memberList c).[j])]))
      (prevAt ((len (memberList c)) + 1 + σ) (j + 1 + σ))) ∈ Γ₃ := fun j hj ↦ by
    rw [hΓ₃]
    have := mem_finalCtx_of_mem' lnd (hch₂ j hj)
    rw [lsh, shiftIterV_neg (isFormula_insFact (by simp) (by simp) (isSemiterm_prevAt _ _)),
      shiftIterV_insFact (by simp) (by simp) (isSemiterm_prevAt _ _), termShiftIterV_fvar, termShiftIterV_fvar,
      termShiftIterV_prevAt] at this
    have e : mTop (i + 1) (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) (shift LAct (memberList c).[j])] + ((len (memberList c)) + 1) + σ = mTop i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[idxOf (memberList s) (shift LAct (memberList c).[j])] := by
      rw [hi₂]; unfold mTop; ring
    rwa [e] at this
  -- (4) Loop S
  obtain ⟨sok, snd, sho, ssh, sfacts⟩ := loopS_ok htbl hP htblN hWc hWp rfl hs hc hsc hsD hcD hE hi₂le hΓ₃f lLay₃ hLay₃ _ le_rfl
  obtain ⟨Γ₄, hΓ₄⟩ : ∃ Γ', Γ' = finalCtx Γ₃ (loopS (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ) (len (memberList c))) := ⟨_, rfl⟩
  have hΓ₄f : IsFormulaSet LAct Γ₄ := by rw [hΓ₄]; exact finalCtx_isFormulaSet 8 htbl hΓ₃f sok
  have tr₄ : ∀ x ∈ Γ₃, x ∈ Γ₄ := fun x hx ↦ by rw [hΓ₄]; exact tr_of_zero snd ssh hx
  have lLay₄ : Layout walkPieces Wc T Γ₄ c 0 := by rw [hΓ₄]; have := lLay₃.transport snd.noDrop'; rwa [ssh, add_zero] at this
  have hLay₄ : Layout walkPieces Wc T Γ₄ s i₂ := by rw [hΓ₄]; have := hLay₃.transport snd.noDrop'; rwa [ssh, add_zero] at this
  have hin₄ : ShIn Γ₄ (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ) := by
    refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_, tr₄ _ hb₃⟩
    · rw [qK'_shPack] at hj; rw [qSig_shPack, qK'_shPack, shX_pack]; exact tr₄ _ (hch₃ j hj)
    · rw [qK'_shPack] at hj; rw [hΓ₄]; exact sfacts j hj
  -- assembly
  have hlist : proShiftPre walkPieces Wl Wc W T s c i = appendV (shBase W) (appendV (chainSteps Wl xs₀)
      (appendV (layoutSteps walkPieces Wl Wc W T c) (loopS (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ) (len (memberList c))))) := by
    unfold proShiftPre; rfl
  rw [hlist]
  refine ⟨listOK_appendV bok (by rw [← hΓ₁]; exact listOK_appendV cok (by rw [← hΓ₂]; exact listOK_appendV lok (by rw [← hΓ₃]; exact sok))),
    noDrop'_appendV bnd (noDrop'_appendV cnd.noDrop' (noDrop'_appendV lnd snd.noDrop')), ?_, ?_, sho⟩
  · rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, bsh, csh, lsh, ssh, add_zero]; ring
  · rw [finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂, ← hΓ₃, ← hΓ₄]
    rw [hWp] at hin₄
    exact ⟨hΓ₄f, lLay₄, hLay₄, hin₄⟩

set_option maxHeartbeats 4000000 in
/-- **The tail is applicable** from the state: Horn-only, no shifts, `setShiftFact S s''` afterwards. -/
theorem shTail2_ok {tbl N W Wc T s c i₂ σ D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hs : IsFormulaSet LAct s) (hc : IsFormulaSet LAct c) (hsc : s = setShift LAct c) (hk1' : 1 ≤ (len (memberList c)))
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D) (hcap : ShCap D E i₂ σ) (hSt : ShState Wc T Γ s c i₂ σ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (shTail2 walkPieces Wc W T s c i₂ σ) ∧ NoDrop (shTail2 walkPieces Wc W T s c i₂ σ) ∧
    HornOnly (shTail2 walkPieces Wc W T s c i₂ σ) ∧ shiftsV (shTail2 walkPieces Wc W T s c i₂ σ) = 0 ∧
    neg LAct (setShiftFact (^&(i₂ + ((len (memberList s)) + 1))) (^&(0 + ((len (memberList c)) + 1)))) ∈
      finalCtx Γ (shTail2 walkPieces Wc W T s c i₂ σ) := by
  have hW := hP.walkTable
  have hL := hP.layoutTable
  have hF2 := hP.frag2Table
  obtain ⟨hΓ, lLay₅, hLay₅, hin₅⟩ := hSt
  rw [← hWp] at hin₅
  have e75 : ∀ ev : V, mkStep proPieces (75 : V) ev = mkStep layoutPieces (75 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 75 (by decide) ev; simpa using this
  have e148 : ∀ ev : V, mkStep proPieces (148 : V) ev = mkStep frag2Pieces (148 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag2 148 (by decide) ev; simpa using this
  have hk1 : 1 ≤ (len (memberList s)) := one_le_len_memberList_setShift hsc hk1'
  have hkD : (len (memberList s)) ≤ D := le_trans (len_memberList_le_setLen hs) hsD
  have hk'D : (len (memberList c)) ≤ D := le_trans (len_memberList_le_setLen hc) hcD
  -- the caps
  have hu0E : 0 + 1 + σ + 1 ≤ E := by
    calc 0 + 1 + σ + 1 ≤ 0 + 1 + (6 * D + 1) + 1 := add_le_add (add_le_add le_rfl hcap.hσ) le_rfl
      _ = 6 * D + 3 := by ring
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
      _ ≤ E := hcap.hE
  have hkE₂ : i₂ + (2 * (len (memberList s)) + 2) ≤ E := by
    calc i₂ + (2 * (len (memberList s)) + 2) ≤ i₂ + (8 * D + 3) :=
          add_le_add le_rfl (add_le_add (le_trans (mul_le_mul_of_nonneg_left hkD zero_le) (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) (by norm_num))
      _ = i₂ + 8 * D + 3 := by ring
      _ ≤ E := hcap.hi
  have hosE : ∀ j < (len (memberList s)), mTop i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T).[j] + 1 ≤ E := fun j hj ↦ by
    calc _ ≤ i₂ + 6 * D + 1 + 1 := add_le_add (mTop_le htbl hW hWc T hs hsD hj) le_rfl
      _ = i₂ + (6 * D + 2) := by ring
      _ ≤ i₂ + (8 * D + 3) := add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num))
      _ = i₂ + 8 * D + 3 := by ring
      _ ≤ E := hcap.hi
  have hSE : i₂ + ((len (memberList s)) + 1) + 1 ≤ E := by
    calc i₂ + ((len (memberList s)) + 1) + 1 = i₂ + ((len (memberList s)) + 2) := by ring
      _ ≤ i₂ + (8 * D + 3) := add_le_add le_rfl (add_le_add (le_trans hkD (le_mul_of_one_le_left zero_le (by norm_num))) (by norm_num))
      _ = i₂ + 8 * D + 3 := by ring
      _ ≤ E := hcap.hi
  have hs''E : 0 + ((len (memberList c)) + 1) + 1 ≤ E := by
    calc 0 + ((len (memberList c)) + 1) + 1 ≤ 0 + (D + 1) + 1 := add_le_add (add_le_add le_rfl (add_le_add hk'D le_rfl)) le_rfl
      _ = D + 2 := by ring
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := add_le_add (le_trans le_thirteen_mul le_self_add) (by norm_num)
      _ ≤ E := hcap.hE
  -- (5) Loop I
  obtain ⟨iok, ind, iho, ish, _, ifact⟩ := loopI_ok htbl hP hWc hWp rfl hs hc hsc hsD hcD hcap hΓ lLay₅ hin₅ _ le_rfl
  obtain ⟨Γ₅, hΓ₅⟩ : ∃ Γ', Γ' = finalCtx Γ (loopI (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ) (len (memberList c))) := ⟨_, rfl⟩
  have hΓ₅f : IsFormulaSet LAct Γ₅ := by rw [hΓ₅]; exact finalCtx_isFormulaSet 8 htbl hΓ iok
  have tr₅ : ∀ x ∈ Γ, x ∈ Γ₅ := fun x hx ↦ by rw [hΓ₅]; exact tr_of_zero ind ish hx
  have lLay₆ : Layout walkPieces Wc T Γ₅ c 0 := by rw [hΓ₅]; have := lLay₅.transport ind.noDrop'; rwa [ish, add_zero] at this
  have hLay₆ : Layout walkPieces Wc T Γ₅ s i₂ := by rw [hΓ₅]; have := hLay₅.transport ind.noDrop'; rwa [ish, add_zero] at this
  have hin₆ : ShIn Γ₅ (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ) := hin₅.mono tr₅
  have hss₅ : neg LAct (setShiftFact (^&(0 + 1 + σ)) (^&(0 + ((len (memberList c)) + 1)))) ∈ Γ₅ := by
    rw [hΓ₅]
    have := ifact hk1'
    rw [qK'_shPack, qSig_shPack, jOf_last hk1', add_zero] at this
    exact this
  -- (6) Fold U
  obtain ⟨uok, und, uho, ush, _, ufact⟩ := uSub_ok htbl hP hWc hWp rfl hs hc hsc hk1' hsD hcD hcap hΓ₅f hLay₆ hin₆
  obtain ⟨Γ₆, hΓ₆⟩ : ∃ Γ', Γ' = finalCtx Γ₅ (uSub (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ)) := ⟨_, rfl⟩
  have hΓ₆f : IsFormulaSet LAct Γ₆ := by rw [hΓ₆]; exact finalCtx_isFormulaSet 8 htbl hΓ₅f uok
  have tr₆ : ∀ x ∈ Γ₅, x ∈ Γ₆ := fun x hx ↦ by rw [hΓ₆]; exact tr_of_zero und ush hx
  have lLay₇ : Layout walkPieces Wc T Γ₆ c 0 := by rw [hΓ₆]; have := lLay₆.transport und.noDrop'; rwa [ush, add_zero] at this
  have hLay₇ : Layout walkPieces Wc T Γ₆ s i₂ := by rw [hΓ₆]; have := hLay₆.transport und.noDrop'; rwa [ush, add_zero] at this
  have hin₇ : ShIn Γ₆ (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ) := hin₆.mono tr₆
  have ufact₆ : neg LAct (subsetFact (^&(0 + 1 + σ)) (^&(i₂ + ((len (memberList s)) + 1)))) ∈ Γ₆ := by rw [hΓ₆]; exact ufact
  -- (7) Loop M
  obtain ⟨mok, mnd, mho, msh, mfacts⟩ := loopM_ok htbl hP hWc hWp rfl hs hc hsc hsD hcD hcap hΓ₆f lLay₇ hin₇ (tr₆ _ hss₅) _ le_rfl
  obtain ⟨Γ₇, hΓ₇⟩ : ∃ Γ', Γ' = finalCtx Γ₆ (loopM (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ) (len (memberList c))) := ⟨_, rfl⟩
  have hΓ₇f : IsFormulaSet LAct Γ₇ := by rw [hΓ₇]; exact finalCtx_isFormulaSet 8 htbl hΓ₆f mok
  have tr₇ : ∀ x ∈ Γ₆, x ∈ Γ₇ := fun x hx ↦ by rw [hΓ₇]; exact tr_of_zero mnd msh hx
  have hLay₈ : Layout walkPieces Wc T Γ₇ s i₂ := by rw [hΓ₇]; have := hLay₇.transport mnd.noDrop'; rwa [msh, add_zero] at this
  -- (8) the parent's chain is in `u_0`: surjectivity of the shift onto the parent's members
  have hin₈ : SubIn Γ₇ i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (^&(0 + 1 + σ)) := fun j' hj' ↦ by
    refine ⟨(hLay₈.1 j' hj').2.2.2.1, ?_⟩
    have hx : (memberList s).[j'] ∈ s := nth_memberList_mem hj'
    have hx' : (memberList s).[j'] ∈ setShift LAct c := by rw [← hsc]; exact hx
    obtain ⟨y, hyc, hxy⟩ := mem_setShift_iff.mp hx'
    obtain ⟨hjlt, hjeq⟩ := idxOf_spec hyc
    have h1 := mfacts (idxOf (memberList c) y) hjlt
    rw [shX_pack, qSig_shPack, hjeq, ← hxy] at h1
    obtain ⟨hlt2, heq2⟩ := idxOf_spec hx
    have hidx : idxOf (memberList s) (memberList s).[j'] = j' := memberList_nodup hlt2 hj' heq2
    rw [hidx] at h1
    rw [hΓ₇]; exact h1
  obtain ⟨c2ok, c2nd, c2ho, c2sh, _, c2fact⟩ := subChain_ok htbl hP hWp hΓ₇f (by simp) (termLen_fvar_le' hu0E) hk1 hkE₂ hosE
    (by rw [len_offVec]) hin₈
  obtain ⟨Γ₈, hΓ₈⟩ : ∃ Γ', Γ' = finalCtx Γ₇ (subChain W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (^&(0 + 1 + σ))) := ⟨_, rfl⟩
  have hΓ₈f : IsFormulaSet LAct Γ₈ := by rw [hΓ₈]; exact finalCtx_isFormulaSet 8 htbl hΓ₇f c2ok
  have tr₈ : ∀ x ∈ Γ₇, x ∈ Γ₈ := fun x hx ↦ by rw [hΓ₈]; exact tr_of_zero c2nd c2sh hx
  have c2fact₈ : neg LAct (subsetFact (^&(i₂ + ((len (memberList s)) + 1))) (^&(0 + 1 + σ))) ∈ Γ₈ := by rw [hΓ₈]; exact c2fact
  -- (9) the two closing steps
  obtain ⟨ok₁, tg₁, cx₁⟩ := lok_subsetAntisymm htbl hL rfl hΓ₈f (by simp) (termLen_fvar_le' hSE) (by simp) (termLen_fvar_le' hu0E)
    c2fact₈ (tr₈ _ (tr₇ _ ufact₆))
  rw [← e75, ← hWp] at ok₁ tg₁ cx₁
  have hΓ₉f : IsFormulaSet LAct (insert (neg LAct (eqFactB (^&(i₂ + ((len (memberList s)) + 1))) (^&(0 + 1 + σ)))) Γ₈) := by
    rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  obtain ⟨ok₂, tg₂, cx₂⟩ := gok_congSetShiftL htbl hF2 rfl hΓ₉f (by simp) (termLen_fvar_le' hu0E) (by simp) (termLen_fvar_le' hSE)
    (by simp) (termLen_fvar_le' hs''E) (memInsSelf _ _) (memIns (tr₈ _ (tr₇ _ (tr₆ _ hss₅))))
  rw [← e148, ← hWp] at ok₂ tg₂ cx₂
  -- assembly
  have hlist : shTail2 walkPieces Wc W T s c i₂ σ =
      appendV (loopI (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ) (len (memberList c)))
        (appendV (uSub (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ)) (appendV (loopM (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ) (len (memberList c)))
          (appendV (subChain W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (^&(0 + 1 + σ)))
            ?[mkStep W 75 ?[^&(i₂ + ((len (memberList s)) + 1)), ^&(0 + 1 + σ)],
              mkStep W 148 ?[^&(0 + 1 + σ), ^&(i₂ + ((len (memberList s)) + 1)), ^&(0 + ((len (memberList c)) + 1))]]))) := by
    unfold shTail2; rfl
  rw [hlist]
  have hok : ListOK tbl E ((8 : ℕ) : V) Γ (appendV (loopI (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ) (len (memberList c)))
        (appendV (uSub (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ)) (appendV (loopM (shPack Wc W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) σ) (len (memberList c)))
          (appendV (subChain W i₂ (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (^&(0 + 1 + σ)))
            ?[mkStep W 75 ?[^&(i₂ + ((len (memberList s)) + 1)), ^&(0 + 1 + σ)],
              mkStep W 148 ?[^&(0 + 1 + σ), ^&(i₂ + ((len (memberList s)) + 1)), ^&(0 + ((len (memberList c)) + 1))]])))) := by
    refine listOK_appendV iok ?_
    rw [← hΓ₅]
    refine listOK_appendV uok ?_
    rw [← hΓ₆]
    refine listOK_appendV mok ?_
    rw [← hΓ₇]
    refine listOK_appendV c2ok ?_
    rw [← hΓ₈]
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    exact listOK_single ok₂
  refine ⟨hok,
    noDrop_appendV ind (noDrop_appendV und (noDrop_appendV mnd (noDrop_appendV c2nd
      (noDrop_cons (Or.inl tg₁) (noDrop_single (Or.inl tg₂)))))),
    hornOnly_appendV iho (hornOnly_appendV uho (hornOnly_appendV mho (hornOnly_appendV c2ho
      (hornOnly_cons (Or.inl tg₁) (hornOnly_single (Or.inl tg₂)))))), ?_, ?_⟩
  · rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, ish, ush, msh, c2sh, shiftsV_cons_tag0 tg₁,
      shiftsV_single_tag0 tg₂]
    simp
  · rw [finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, ← hΓ₅, ← hΓ₆, ← hΓ₇, ← hΓ₈,
      finalCtx_cons, cx₁, finalCtx_single, cx₂]
    exact memInsSelf _ _

set_option maxHeartbeats 2000000 in
/-- **The `shift` child's prologue is applicable**: afterwards the child's layout is at `0`, the parent's at
`i₂ = i + 1 + (k' + 1) + σ`, and `setShiftFact S s''` holds (`S = &(i₂ + (k + 1))`, `s'' = &(k' + 1)`) — the
`nodeShift_ok` hypothesis `hss`; its `hf` comes from `goalElim` on the child's goal (`ic = s'' + 2`, `id = &1`). -/
theorem proShift_ok {tbl N N' B' Wl Wc W T s c i D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hs : IsFormulaSet LAct s) (hc : IsFormulaSet LAct c) (hsc : s = setShift LAct c) (hk1' : 1 ≤ len (memberList c))
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D) (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : i + 16 * D + 8 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s i) :
    ListOK tbl E ((8 : ℕ) : V) Γ (proShift walkPieces Wl Wc W T s c i) ∧ NoDrop' (proShift walkPieces Wl Wc W T s c i) ∧
    shiftsV (proShift walkPieces Wl Wc W T s c i) = 1 + (len (memberList c) + 1) + proSig walkPieces Wl Wc W T c ∧
    Layout walkPieces Wc T (finalCtx Γ (proShift walkPieces Wl Wc W T s c i)) c 0 ∧
    Layout walkPieces Wc T (finalCtx Γ (proShift walkPieces Wl Wc W T s c i)) s
      (i + 1 + (len (memberList c) + 1) + proSig walkPieces Wl Wc W T c) ∧
    neg LAct (setShiftFact (^&(i + 1 + (len (memberList c) + 1) + proSig walkPieces Wl Wc W T c + (len (memberList s) + 1)))
      (^&(0 + (len (memberList c) + 1)))) ∈ finalCtx Γ (proShift walkPieces Wl Wc W T s c i) := by
  have hk'D : len (memberList c) ≤ D := le_trans (len_memberList_le_setLen hc) hcD
  have hE8 : 13 * D + 18 * ‖D‖ + 8 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hE
  have hσle : proSig walkPieces Wl Wc W T c ≤ 6 * D + 1 := proSig_le htbl hP hWc htblN hWl hWp hc hk1' hcD hE8 hΓ
  have hi₂le : i + 1 + (len (memberList c) + 1) + proSig walkPieces Wl Wc W T c + 8 * D + 3 ≤ E := by
    calc i + 1 + (len (memberList c) + 1) + proSig walkPieces Wl Wc W T c + 8 * D + 3
        ≤ i + 1 + (D + 1) + (6 * D + 1) + 8 * D + 3 := add_le_add (add_le_add (add_le_add (add_le_add le_rfl (add_le_add hk'D le_rfl)) hσle) le_rfl) le_rfl
      _ = i + 15 * D + 6 := by ring
      _ ≤ i + 16 * D + 8 := add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) (by norm_num)
      _ ≤ E := hiE
  have hcap : ShCap D E (i + 1 + (len (memberList c) + 1) + proSig walkPieces Wl Wc W T c) (proSig walkPieces Wl Wc W T c) :=
    ⟨hE, hi₂le, hσle⟩
  obtain ⟨pok, pnd, psh, pSt, _⟩ := proShiftPre_ok htbl hP htblN hWl hWc hWp hs hc hsc hk1' hsD hcD hE hiE hΓ hLay
  obtain ⟨tok, tnd, _, tsh, tfact⟩ := shTail2_ok htbl hP hWc hWp hs hc hsc hk1' hsD hcD hcap pSt
  rw [proShift_eq]
  refine ⟨listOK_appendV pok tok, noDrop'_appendV pnd tnd.noDrop', ?_, ?_, ?_, ?_⟩
  · rw [shiftsV_appendV, psh, tsh, add_zero]
  · rw [finalCtx_appendV]; have := pSt.2.1.transport tnd.noDrop'; rwa [tsh, add_zero] at this
  · rw [finalCtx_appendV]; have := pSt.2.2.1.transport tnd.noDrop'; rwa [tsh, add_zero] at this
  · rw [finalCtx_appendV]; exact tfact

end shiftChild


/-! ## 11. Sizes and costs of the prologues (`DESIGN_fragments.md` §5, `Frag1` §5's `costSum_le_of_sizeOK`)

Every prologue is a list at cap `8` whose only non-Horn steps are the closed lemmas of the `setLen` fold
(`sLemma (sum2Fact L' |x| L) (sum2Code T L' |x| L)`, `L ≤ setLen s`) and those of the re-indexed `lenSteps`
(`sizeOK_lenSteps`). So `SizeOK Q D` holds at `Q = layQ B B' Dz`, `D = layD N' B' Dz` (`Dz` a bound on the sequent
lengths), and `costSum_le_of_sizeOK` bounds the cost by `len · (costK N E B 8 Q D + 35 · (ctxBoundG … + …))`.
The Horn-only parts (loops, chains, certifications) are `HornOnly` by their `_ok` theorems; `chainSteps` and the
`lenFold` blocks get standalone tag censuses here. -/

section proSizes

/-! ### 11.1 The closed lemmas of the fold -/

/-- `|sum2Fact a b n| ≤ B·(18‖Dz‖ + 7)` for `a + b ≤ n ≤ Dz`. -/
noncomputable def sum2Q (B Dz : V) : V := B * (18 * ‖Dz‖ + 7)
/-- `dlen (sum2Code T a b n) ≤ 4·(‖Dz‖ + 1)(‖Dz‖ + 2)·nodeCost N' B' (18‖Dz‖ + 7)` for `a + b ≤ n ≤ Dz`. -/
noncomputable def sum2D (N' B' Dz : V) : V := 4 * ((‖Dz‖ + 1) * (‖Dz‖ + 2) * nodeCost N' B' (18 * ‖Dz‖ + 7))

lemma formulaLen_sum2Fact_le {B a b n Dz : V} (hPle : formulaLen LAct (Ple : V) ≤ B) (hab : a + b ≤ n) (hn : n ≤ Dz) :
    formulaLen LAct (sum2Fact a b n) ≤ sum2Q B Dz := by
  unfold sum2Fact sum2Q
  have hlen : ‖n‖ ≤ ‖Dz‖ := length_monotone hn
  have ht : termLen LAct (bnum a ^+ bnum b) ≤ 18 * ‖n‖ + 7 := by
    refine le_trans (termLen_qqAdd_le (isSemiterm_bnum0 _).isUTerm (isSemiterm_bnum0 _).isUTerm
      (termLen_bnum_le_bk (le_trans le_self_add hab)) (termLen_bnum_le_bk (le_trans le_add_self hab))) ?_
    calc 6 * ‖n‖ + 1 + (6 * ‖n‖ + 1) + 1 = 12 * ‖n‖ + 3 := by ring
      _ ≤ 18 * ‖n‖ + 7 := add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num)
  refine le_trans (formulaLen_leFact_bk hPle (isSemiterm_qqAdd_LAct (isSemiterm_bnum0 _) (isSemiterm_bnum0 _)) ht le_rfl) ?_
  exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hlen zero_le) le_rfl) zero_le

lemma dlen_sum2Code_le' {T N' B' a b n Dz : V} (htblN : NumTableOK T N' B') (hab : a + b ≤ n) (hn : n ≤ Dz) :
    dlen TAct (sum2Code T a b n) ≤ sum2D N' B' Dz := by
  set K := (‖Dz‖ + 1) * (‖Dz‖ + 2) * nodeCost N' B' (18 * ‖Dz‖ + 7) with hK
  have hlen : ‖n‖ ≤ ‖Dz‖ := length_monotone hn
  have hlab : ‖a + b‖ ≤ ‖Dz‖ := length_monotone (le_trans hab hn)
  have hla : ‖a‖ ≤ ‖Dz‖ := length_monotone (le_trans le_self_add (le_trans hab hn))
  have hnc : ∀ x, x ≤ ‖Dz‖ → nodeCost N' B' (12 * x + 3) ≤ nodeCost N' B' (18 * ‖Dz‖ + 7) := fun x hx ↦
    nodeCost_mono (add_le_add (le_trans (mul_le_mul_of_nonneg_left hx zero_le) (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) (by norm_num))
  have h1 : (1 : V) ≤ (‖Dz‖ + 1) * (‖Dz‖ + 2) :=
    le_trans (by norm_num : (1 : V) ≤ 1 * 2) (mul_le_mul (le_add_self) (le_add_self) zero_le zero_le)
  have hK1 : nodeCost N' B' (18 * ‖Dz‖ + 7) ≤ K := by
    rw [hK]; exact le_mul_of_one_le_left zero_le h1
  have hadd : dlen TAct (addCode T a b) ≤ K := by
    refine le_trans (dlen_addCode_le htblN a b) ?_
    rw [hK]
    exact mul_le_mul (mul_le_mul (add_le_add hla le_rfl) (add_le_add hlab le_rfl) zero_le zero_le) (hnc _ hlab) zero_le zero_le
  have hadd' : dlen TAct (addCode T (a + b) (n - (a + b))) ≤ K := by
    refine le_trans (dlen_addCode_le htblN (a + b) (n - (a + b))) ?_
    rw [add_tsub_cancel_of_le hab, hK]
    exact mul_le_mul (mul_le_mul (add_le_add hlab le_rfl) (add_le_add hlen le_rfl) zero_le zero_le) (hnc _ hlen) zero_le zero_le
  have hle : dlen TAct (leCode T (a + b) n) ≤ K + K :=
    le_trans (dlen_leCode_le htblN hab) (add_le_add hadd' (le_trans (hnc _ hlen) hK1))
  have hn' : nodeCost N' B' (18 * ‖n‖ + 7) ≤ K :=
    le_trans (nodeCost_mono (add_le_add (mul_le_mul_of_nonneg_left hlen zero_le) le_rfl)) hK1
  calc dlen TAct (sum2Code T a b n) ≤ K + (K + K) + K := le_trans (dlen_sum2Code_le htblN hab) (add_le_add (add_le_add hadd hle) hn')
    _ = sum2D N' B' Dz := by unfold sum2D; rw [← hK]; ring

/-! ### 11.2 The fold blocks -/

lemma stepSizeOK_of_tag {Q D s : V} (h : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2) : StepSizeOK Q D s := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

lemma sizeOK_foldBlock0 {W k c o x : V} (hWp : W = proPieces) (Q D : V) : SizeOK Q D (foldBlock0 W k c o x) := by
  subst hWp
  have e85 : ∀ ev : V, mkStep proPieces (85 : V) ev = mkStep layoutPieces (85 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 85 (by decide) ev; simpa using this
  unfold foldBlock0
  refine sizeOK_cons (stepSizeOK_of_tag ?_) (sizeOK_single (stepSizeOK_of_tag ?_))
  · rw [e85, ltag_setLenTotalC rfl]; simp
  · rw [ptag_setLenSingLe rfl]; simp

lemma sizeOK_foldBlockS {W T N' B' B k c o x L' L Dz : V} (hWp : W = proPieces) (htblN : NumTableOK T N' B')
    (hPle : formulaLen LAct (Ple : V) ≤ B) (hLL : L' + formulaLen LAct x ≤ L) (hL : L ≤ Dz) :
    SizeOK (sum2Q B Dz) (sum2D N' B' Dz) (foldBlockS W T k c o x L' L) := by
  subst hWp
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
  unfold foldBlockS
  refine sizeOK_cons (stepSizeOK_of_tag ?_) (sizeOK_cons (stepSizeOK_of_tag ?_) (sizeOK_cons (stepSizeOK_of_tag ?_)
    (sizeOK_cons (stepSizeOK_of_tag ?_) (sizeOK_cons ?_ (sizeOK_single (stepSizeOK_of_tag ?_))))))
  · rw [e85, ltag_setLenTotalC rfl]; simp
  · rw [e111, ftag_setLenInsertLe rfl]; simp
  · rw [e109, ftag_leRefl rfl]; simp
  · rw [e108, ftag_leAddLeAdd rfl]; simp
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp, ?_, ?_⟩)))))
    · rw [sLemA_sLemma]; exact formulaLen_sum2Fact_le hPle hLL hL
    · rw [sLemD_sLemma]; exact dlen_sum2Code_le' htblN hLL hL
  · rw [e110, ftag_leTrans rfl]; simp

/-- The fold's blocks are size-disciplined (the induction motive over the PACKED parameters). -/
theorem sizeOK_lenFoldAux {W T N' B' B s xs k os Dz : V} (hWp : W = proPieces) (htblN : NumTableOK T N' B')
    (hPle : formulaLen LAct (Ple : V) ≤ B) (hxs : xs = memberList s) (hk : k = len xs) (hsD : setLen LAct s ≤ Dz) :
    ∀ c ≤ k, SizeOK (sum2Q B Dz) (sum2D N' B' Dz) (lenFoldAuxP ⟪W, T, xs, os, k⟫ c) := by
  intro c
  induction c using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _; rw [show lenFoldAuxP ⟪W, T, xs, os, k⟫ 0 = lenFoldAux W T xs os k 0 from rfl, lenFoldAux_zero]; exact sizeOK_nil _ _
  | succ c ih =>
    intro hc
    rw [show lenFoldAuxP ⟪W, T, xs, os, k⟫ (c + 1) = lenFoldAux W T xs os k (c + 1) from rfl, lenFoldAux_succ]
    refine sizeOK_appendV (ih (le_trans le_self_add hc)) ?_
    have hck : c < len (memberList s) := by rw [← hxs, ← hk]; exact lt_of_lt_of_le (lt_add_one c) hc
    unfold foldBlock
    by_cases hc0 : c = 0
    · rw [if_pos hc0]; exact sizeOK_foldBlock0 hWp _ _
    · rw [if_neg hc0]
      have hLL : setLen LAct (psetAux xs c) + formulaLen LAct (nthFromEnd xs c) ≤ setLen LAct (psetAux xs (c + 1)) := by
        rw [hxs, setLen_psetAux_succ hck]
      have hL : setLen LAct (psetAux xs (c + 1)) ≤ Dz := by
        rw [hxs]; exact le_trans (setLen_psetAux_le (by rw [← hxs, ← hk]; exact hc)) hsD
      exact sizeOK_foldBlockS hWp htblN hPle hLL hL

theorem sizeOK_lenFold {W T N' B' B s Dz : V} (hWp : W = proPieces) (htblN : NumTableOK T N' B')
    (hPle : formulaLen LAct (Ple : V) ≤ B) (hsD : setLen LAct s ≤ Dz) (os : V) :
    SizeOK (sum2Q B Dz) (sum2D N' B' Dz) (lenFold W T (memberList s) os) :=
  sizeOK_lenFoldAux hWp htblN hPle rfl rfl hsD _ le_rfl

/-! ### 11.3 The member blocks and the chain -/

theorem sizeOK_memberBlock {Wc T N' B' x Dz : V} (hWc : Wc = certPieces) (htblN : NumTableOK T N' B')
    (hx : IsSemiformula LAct 0 x) (hxD : formulaLen LAct x ≤ Dz) (Q' D' : V) :
    SizeOK (lenQ B' Dz + Q') (lenD N' B' Dz + D') (memberBlock walkPieces Wc T x) := by
  unfold memberBlock
  refine sizeOK_appendV (sizeOK_of_hornOnly (hornOnly_describeF rfl hx)) (sizeOK_reidxL ?_)
  exact (lenFGraph_sizeOK hWc htblN Dz hx hxD 0 _ (lenSteps_graph hx)).mono le_self_add le_self_add

theorem sizeOK_memberBlocks {Wc T N' B' Dz : V} (hWc : Wc = certPieces) (htblN : NumTableOK T N' B') (Q' D' : V) :
    ∀ v : V, (∀ j < len v, IsSemiformula LAct 0 v.[j] ∧ formulaLen LAct v.[j] ≤ Dz) →
      SizeOK (lenQ B' Dz + Q') (lenD N' B' Dz + D') (memberBlocks v walkPieces Wc T) := by
  intro v
  induction v using adjoin_ISigma1.pi1_succ_induction with
  | hP => definability
  | nil => intro _; rw [memberBlocks_nil]; exact sizeOK_nil _ _
  | adjoin x v ih =>
    intro hv
    have hx := hv 0 (by simp)
    rw [nth_adjoin_zero] at hx
    have hv' : ∀ j < len v, IsSemiformula LAct 0 v.[j] ∧ formulaLen LAct v.[j] ≤ Dz := fun j hj ↦ by
      have := hv (j + 1) (by rw [len_adjoin]; exact (add_lt_add_iff_right 1).mpr hj)
      rwa [nth_adjoin_succ] at this
    rw [memberBlocks_adjoin]
    exact sizeOK_appendV (sizeOK_memberBlock hWc htblN hx.1 hx.2 Q' D') (ih hv')

lemma hornOnly_chainNodeA {W : V} (hWl : W = layoutPieces) (xs c : V) : HornOnly (chainNodeA W xs c) := by
  unfold chainNodeA
  exact hornOnly_cons (by rw [ltag_insertTotalC hWl]; simp) (hornOnly_cons (by rw [ltag_isFormulaSetInsertC hWl]; simp)
    (hornOnly_single (by rw [ltag_fsetSigmaPiC hWl]; simp)))

lemma hornOnly_chainA {W : V} (hWl : W = layoutPieces) (xs : V) : ∀ c : V, HornOnly (chainA W xs c) := by
  intro c
  induction c using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => rw [chainA_zero]; exact hornOnly_nil
  | succ c ih => rw [chainA_succ]; exact hornOnly_appendV ih (hornOnly_chainNodeA hWl xs c)

lemma hornOnly_chainNodeB {W : V} (hWl : W = layoutPieces) (xs k c : V) : HornOnly (chainNodeB W xs k c) := by
  unfold chainNodeB
  split_ifs
  · exact hornOnly_cons (by rw [ltag_subsetInsertC hWl]; simp) (hornOnly_cons (by rw [ltag_subsetTransC hWl]; simp)
      (hornOnly_cons (by rw [ltag_memInsertSelfC hWl]; simp) (hornOnly_single (by rw [ltag_subsetMemC hWl]; simp))))
  · exact hornOnly_nil

lemma hornOnly_chainB {W : V} (hWl : W = layoutPieces) (xs k : V) : ∀ c : V, HornOnly (chainB W xs k c) := by
  intro c
  induction c using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => rw [chainB_zero]; exact hornOnly_nil
  | succ c ih => rw [chainB_succ]; exact hornOnly_appendV ih (hornOnly_chainNodeB hWl xs k c)

/-- `chainSteps` is Horn-only by its rows alone. -/
theorem hornOnly_chainSteps {W : V} (hWl : W = layoutPieces) (xs : V) : HornOnly (chainSteps W xs) := by
  unfold chainSteps
  refine hornOnly_appendV ?_ (hornOnly_appendV (hornOnly_chainA hWl xs _) (hornOnly_appendV ?_
    (hornOnly_appendV (hornOnly_chainB hWl xs _ _) (hornOnly_single (by rw [ltag_setLenTotalC hWl]; simp)))))
  · unfold chainPre
    exact hornOnly_cons (by rw [ltag_emptySubsetC hWl]; simp) (hornOnly_cons (by rw [ltag_fsetOfSubsetZeroC hWl]; simp)
      (hornOnly_single (by rw [ltag_fsetSigmaPiC hWl]; simp)))
  · unfold chainBpre
    exact hornOnly_cons (by rw [ltag_subsetReflC hWl]; simp) (hornOnly_single (by rw [ltag_memInsertSelfC hWl]; simp))

/-! ### 11.4 The layout builder -/

/-- The size class of a layout: the `lenSteps` lemmas and the fold's `sum2` lemmas at `Dz ≥ setLen s`. -/
noncomputable def layQ (B B' Dz : V) : V := lenQ B' Dz + sum2Q B Dz
noncomputable def layD (N' B' Dz : V) : V := lenD N' B' Dz + sum2D N' B' Dz

/-- **`layoutSteps` is size-disciplined** by its structure alone (no applicability needed). -/
theorem sizeOK_layoutSteps {Wl Wc W T N' B' B s Dz : V} (hWl : Wl = layoutPieces) (hWc : Wc = certPieces)
    (hWp : W = proPieces) (htblN : NumTableOK T N' B') (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hsD : setLen LAct s ≤ Dz) :
    SizeOK (layQ B B' Dz) (layD N' B' Dz) (layoutSteps walkPieces Wl Wc W T s) := by
  unfold layoutSteps layQ layD
  refine sizeOK_appendV (sizeOK_memberBlocks hWc htblN _ _ _ ?_) (sizeOK_appendV (sizeOK_of_hornOnly (hornOnly_chainSteps hWl _))
    ((sizeOK_lenFold hWp htblN hPle hsD _).mono le_add_self le_add_self))
  intro j hj
  exact ⟨hs _ (nth_memberList_mem hj), le_trans (formulaLen_le_setLen_of_mem (nth_memberList_mem hj)) hsD⟩

/-- **The cost of `layoutSteps`**, in the shape of `costSum_le_of_sizeOK`: with `n = len (layoutSteps …) ≤ 26·setLen s +
13k + 6`, `costSum ≤ n·(costK N E B 8 (layQ B B' D) (layD N' B' D) + 35·(ctxBoundG (growK B E (layQ …)) Γ n + (fvOccS Γ + n·growK …)))`. -/
theorem costSum_layoutSteps_le {tbl N N' B' B Wl Wc W T s D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hk1 : 1 ≤ len (memberList s)) (hsD : setLen LAct s ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) :
    costSum N E Γ (layoutSteps walkPieces Wl Wc W T s) ≤ len (layoutSteps walkPieces Wl Wc W T s) *
      (costK N E B 8 (layQ B B' D) (layD N' B' D) + (3 * ((8 : ℕ) : V) + 11) *
        (ctxBoundG (growK B E (layQ B B' D)) Γ (len (layoutSteps walkPieces Wl Wc W T s)) +
          (fvOccS LAct Γ + len (layoutSteps walkPieces Wl Wc W T s) * growK B E (layQ B B' D)))) ∧
    len (layoutSteps walkPieces Wl Wc W T s) ≤ 26 * setLen LAct s + 13 * len (memberList s) + 6 := by
  obtain ⟨lok, _, _, llen, _⟩ := layoutSteps_ok htbl hP htblN hWl hWc hWp hs hk1 hsD hE hΓ
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hE)
  exact ⟨costSum_le_of_sizeOK 8 hE1 htbl hBt lok (sizeOK_layoutSteps hWl hWc hWp htblN hPle hs hsD), llen⟩

/-! ### 11.5 The per-tag prologues: sizes (`SizeOK`) and costs -/

/-- `proAxL` is Horn-only (by `proAxL_ok`), hence size-disciplined at any class. -/
theorem costSum_proAxL_le {tbl N N' B' B Wc T s p D E Γ i Q Dd : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWc : Wc = certPieces) (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B)
    (hs : IsFormulaSet LAct s) (hp : p ∈ s) (hnp : neg LAct p ∈ s) (hsD : setLen LAct s ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 8 ≤ E) (hiE : i + 8 * D + 3 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hLay : Layout walkPieces Wc T Γ s i) :
    costSum N E Γ (proAxL walkPieces Wc T s p i) ≤ len (proAxL walkPieces Wc T s p i) *
      (costK N E B 8 Q Dd + (3 * ((8 : ℕ) : V) + 11) * (ctxBoundG (growK B E Q) Γ (len (proAxL walkPieces Wc T s p i)) +
        (fvOccS LAct Γ + len (proAxL walkPieces Wc T s p i) * growK B E Q))) ∧
    len (proAxL walkPieces Wc T s p i) + 4 ≤ 12 * formulaLen LAct p := by
  obtain ⟨ok, _, ho, _, hlen, _⟩ := proAxL_ok htbl hP htblN hWc hs hp hnp hsD hE hiE hΓ hLay
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hE)
  exact ⟨costSum_le_of_sizeOK 8 hE1 htbl hBt ok (sizeOK_of_hornOnly ho), hlen⟩

/-- `postIns` carries one goal cut of size `|goalFact s'' (bnum n)|` and one Horn step. -/
theorem sizeOK_postIns {W s'' cp n : V} (hWp : W = proPieces) (Dd : V) :
    SizeOK (4 * formulaLen LAct (goalFact (^&s'') (bnum n))) Dd (postIns W s'' cp n) := by
  subst hWp
  have e122 : ∀ ev : V, mkStep proPieces (122 : V) ev = mkStep frag1Pieces (122 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag1 122 (by decide) ev; simpa using this
  unfold postIns
  refine sizeOK_appendV (sizeOK_goalElim (by simp) (isSemiterm_bnum0 n)) (sizeOK_single (stepSizeOK_of_tag ?_))
  rw [e122, ftag_congFstIdx rfl]; simp

theorem costSum_postIns_le {tbl N B W s'' cp n E Γ Dd : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (hWp : W = proPieces)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B)
    (hΓ : IsFormulaSet LAct Γ) (hsE : s'' + 3 ≤ E) (hcE : cp + 3 ≤ E)
    (hg : neg LAct (goalFact (^&s'') (bnum n)) ∈ Γ) (heq : neg LAct (eqFactB (^&cp) (^&s'')) ∈ Γ) :
    costSum N E Γ (postIns W s'' cp n) ≤ 6 *
      (costK N E B 8 (4 * formulaLen LAct (goalFact (^&s'') (bnum n))) Dd + (3 * ((8 : ℕ) : V) + 11) *
        (ctxBoundG (growK B E (4 * formulaLen LAct (goalFact (^&s'') (bnum n)))) Γ 6 +
          (fvOccS LAct Γ + 6 * growK B E (4 * formulaLen LAct (goalFact (^&s'') (bnum n)))))) := by
  obtain ⟨ok, _, _, hlen, _⟩ := postIns_ok htbl hP hWp hΓ hsE hcE hg heq
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hsE)
  have := costSum_le_of_sizeOK 8 hE1 htbl hBt ok (sizeOK_postIns hWp Dd)
  rwa [hlen] at this

set_option maxHeartbeats 4000000 in
/-- **`proIns` is size-disciplined** at the layout class (its identification is Horn-only by `identIns_ok`; the
hypotheses are those of `proIns_ok`). -/
theorem sizeOK_proIns {tbl N N' B' B Wl Wc W T s p i ip D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p) (hk1 : 1 ≤ len (memberList s))
    (hsD : setLen LAct (insert p s) ≤ D) (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : i + 14 * D + 5 ≤ E)
    (hipE : ip + 8 * D + 4 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hLay : Layout walkPieces Wc T Γ s i) (hDp : DossF walkPieces Γ 0 p ip) :
    SizeOK (layQ B B' D) (layD N' B' D) (proIns walkPieces Wl Wc W T s p i ip) := by
  have hL := hP.layoutTable
  have hcs : IsFormulaSet LAct (insert p s) := IsFormulaSet.insert_iff.mpr ⟨hp, hs⟩
  have hsD' : setLen LAct s ≤ D := le_trans (setLen_le_insert p s) hsD
  have hkD : len (memberList s) ≤ D := le_trans (len_memberList_le_setLen hs) hsD'
  have hk1' : 1 ≤ len (memberList (insert p s)) := one_le_len_memberList_insert p s
  have hE8 : 13 * D + 18 * ‖D‖ + 8 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hE
  have e76 : ∀ ev : V, mkStep proPieces (76 : V) ev = mkStep layoutPieces (76 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 76 (by decide) ev; simpa using this
  set σ := proSig walkPieces Wl Wc W T (insert p s) with hσ
  have hσle : σ ≤ 6 * D + 1 := proSig_le htbl hP hWc htblN hWl hWp hcs hk1' hsD hE8 hΓ
  have hipE1 : ip + 1 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) (le_trans (add_le_add le_self_add le_rfl) hipE)
  have hSE : i + (len (memberList s) + 1) + 1 ≤ E := by
    calc i + (len (memberList s) + 1) + 1 = i + (len (memberList s) + 2) := by ring
      _ ≤ i + (14 * D + 5) := add_le_add le_rfl (add_le_add (le_trans hkD (le_mul_of_one_le_left zero_le (by norm_num))) (by norm_num))
      _ = i + 14 * D + 5 := by ring
      _ ≤ E := hiE
  -- step 1: the insert object
  obtain ⟨ok₁, tg₁, cx₁⟩ := lok_insertTotalC htbl hL rfl hΓ (by simp) (termLen_fvar_le' hipE1) (by simp) (termLen_fvar_le' hSE)
  rw [← e76, ← hWp] at ok₁ tg₁ cx₁
  rw [Nat.cast_zero, termShift_fvar, termShift_fvar] at cx₁
  have h1sh : shiftsV (?[mkStep W 76 ?[^&ip, ^&(i + (len (memberList s) + 1))]] : V) = 1 := shiftsV_single_tag2 tg₁
  have h1nd : NoDrop' (?[mkStep W 76 ?[^&ip, ^&(i + (len (memberList s) + 1))]] : V) := noDrop'_single (Or.inr (Or.inr (Or.inl tg₁)))
  set Γ₁ := finalCtx Γ ?[mkStep W 76 ?[^&ip, ^&(i + (len (memberList s) + 1))]] with hΓ₁
  have hΓ₁e : Γ₁ = insert (neg LAct (insFact (^&0) (^&(ip + 1)) (^&(i + (len (memberList s) + 1) + 1)))) (setShift LAct Γ) := by
    rw [hΓ₁, finalCtx_single, cx₁]
  have hΓ₁f : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ (listOK_single ok₁)
  have hLay₁ : Layout walkPieces Wc T Γ₁ s (i + 1) := by have := hLay.transport h1nd; rwa [h1sh] at this
  have hDp₁ : DossF walkPieces Γ₁ 0 p (ip + 1) := by have := dossF_transport' h1nd hDp; rwa [h1sh] at this
  have hcp₁ : neg LAct (insFact (^&0) (^&(ip + 1)) (^&(i + (len (memberList s) + 1) + 1))) ∈ Γ₁ := by
    rw [hΓ₁e]; exact memInsSelf _ _
  -- step 2: the child's layout
  obtain ⟨lok, lnd, _, _, lLay⟩ := layoutSteps_ok htbl hP htblN hWl hWc hWp hcs hk1' hsD hE8 hΓ₁f
  have lsh : shiftsV (layoutSteps walkPieces Wl Wc W T (insert p s)) = σ := by rw [hσ, proSig]
  set Γ₂ := finalCtx Γ₁ (layoutSteps walkPieces Wl Wc W T (insert p s)) with hΓ₂
  have hΓ₂f : IsFormulaSet LAct Γ₂ := finalCtx_isFormulaSet 8 htbl hΓ₁f lok
  have hLay₂ : Layout walkPieces Wc T Γ₂ s (i + 1 + σ) := by have := hLay₁.transport lnd; rwa [lsh] at this
  have hDp₂ : DossF walkPieces Γ₂ 0 p (ip + 1 + σ) := by have := dossF_transport' lnd hDp₁; rwa [lsh] at this
  have hcp₂ : neg LAct (insFact (^&σ) (^&(ip + 1 + σ)) (^&(i + 1 + σ + (len (memberList s) + 1)))) ∈ Γ₂ := by
    have := mem_finalCtx_of_mem' lnd hcp₁
    rw [lsh, shiftIterV_neg (isFormula_insFact (by simp) (by simp) (by simp)), shiftIterV_insFact (by simp) (by simp) (by simp),
      termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar, zero_add] at this
    have e : i + (len (memberList s) + 1) + 1 + σ = i + 1 + σ + (len (memberList s) + 1) := by ring
    rwa [e] at this
  have hF₂ : IdFrame walkPieces Wc T Γ₂ s p (i + 1 + σ) (ip + 1 + σ) σ := ⟨lLay, hLay₂, hDp₂, hcp₂⟩
  -- step 3: the identification is Horn-only
  have hcap : IdCap D E (i + 1 + σ) (ip + 1 + σ) σ := ⟨hE, by
      calc i + 1 + σ + 8 * D + 3 ≤ i + 1 + (6 * D + 1) + 8 * D + 3 := add_le_add (add_le_add (add_le_add le_rfl hσle) le_rfl) le_rfl
        _ = i + 14 * D + 5 := by ring
        _ ≤ E := hiE, by
      calc ip + 1 + σ + 2 * D + 2 ≤ ip + 1 + (6 * D + 1) + 2 * D + 2 := add_le_add (add_le_add (add_le_add le_rfl hσle) le_rfl) le_rfl
        _ = ip + 8 * D + 4 := by ring
        _ ≤ E := hipE, by
      calc σ + 1 ≤ 6 * D + 1 + 1 := add_le_add hσle le_rfl
        _ = 6 * D + 2 := by ring
        _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
        _ ≤ E := hE⟩
  obtain ⟨_, _, iho, _, _⟩ := identIns_ok htbl hP hWl hWc hWp rfl hs hp hk1 hsD hcap hΓ₂f hF₂
  -- assembly
  have hlist : proIns walkPieces Wl Wc W T s p i ip = appendV ?[mkStep W 76 ?[^&ip, ^&(i + (len (memberList s) + 1))]]
      (appendV (layoutSteps walkPieces Wl Wc W T (insert p s))
        (identIns (qPack Wl W (i + 1 + σ) (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s)
          (ip + 1 + σ) (len (memberList (insert p s))) (offVec (memberList (insert p s)) walkPieces Wc T)
          (memberList (insert p s)) p σ))) := by
    unfold proIns; rw [← hσ]
  rw [hlist]
  exact sizeOK_appendV (sizeOK_single (stepSizeOK_of_tag (Or.inr (Or.inr tg₁))))
    (sizeOK_appendV (sizeOK_layoutSteps hWl hWc hWp htblN hPle hcs hsD) (sizeOK_of_hornOnly iho))

theorem costSum_proIns_le {tbl N N' B' B Wl Wc W T s p i ip D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p) (hk1 : 1 ≤ len (memberList s))
    (hsD : setLen LAct (insert p s) ≤ D) (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : i + 14 * D + 5 ≤ E)
    (hipE : ip + 8 * D + 4 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hLay : Layout walkPieces Wc T Γ s i) (hDp : DossF walkPieces Γ 0 p ip) :
    costSum N E Γ (proIns walkPieces Wl Wc W T s p i ip) ≤ len (proIns walkPieces Wl Wc W T s p i ip) *
      (costK N E B 8 (layQ B B' D) (layD N' B' D) + (3 * ((8 : ℕ) : V) + 11) *
        (ctxBoundG (growK B E (layQ B B' D)) Γ (len (proIns walkPieces Wl Wc W T s p i ip)) +
          (fvOccS LAct Γ + len (proIns walkPieces Wl Wc W T s p i ip) * growK B E (layQ B B' D)))) := by
  obtain ⟨ok, _, _, _, _, _⟩ := proIns_ok htbl hP htblN hWl hWc hWp hs hp hk1 hsD hE hiE hipE hΓ hLay hDp
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hE)
  exact costSum_le_of_sizeOK 8 hE1 htbl hBt ok (sizeOK_proIns htbl hP htblN hWl hWc hWp hPle hs hp hk1 hsD hE hiE hipE hΓ hLay hDp)

set_option maxHeartbeats 2000000 in
/-- **`proCutPre` is size-disciplined** at the `lenSteps` class (its `certNeg` is Horn-only by `certNeg_ok`). -/
theorem sizeOK_proCutPre {tbl N N' B' Wc T p D E Γ Q' D' : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWc : Wc = certPieces)
    (hp : IsSemiformula LAct 0 p) (hpD : formulaLen LAct p ≤ D) (hnpD : formulaLen LAct (neg LAct p) ≤ D)
    (hE : 13 * D + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) :
    SizeOK (lenQ B' D + Q') (lenD N' B' D + D') (proCutPre walkPieces Wc T p) := by
  have hW := hP.walkTable
  have hC := hP.certTable
  have htblC := hP.tableOK_certView htbl
  have hnp : IsSemiformula LAct 0 (neg LAct p) := hp.neg
  obtain ⟨b1ok, b1nd, b1sh, _, b1D, _, _⟩ := memberBlock_ok htbl hP htblN hWc hp hpD hE hΓ
  set Γ₁ := finalCtx Γ (memberBlock walkPieces Wc T p) with hΓ₁
  have hΓ₁f : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ b1ok
  obtain ⟨b2ok, b2nd, b2sh, _, b2D, _, _⟩ := memberBlock_ok htbl hP htblN hWc hnp hnpD hE hΓ₁f
  set Γ₂ := finalCtx Γ₁ (memberBlock walkPieces Wc T (neg LAct p)) with hΓ₂
  have hΓ₂f : IsFormulaSet LAct Γ₂ := finalCtx_isFormulaSet 8 htbl hΓ₁f b2ok
  have hD₁ : DossF walkPieces Γ₂ 0 p (mLen Wc T p + mShift walkPieces Wc T (neg LAct p)) := by
    have := dossF_transport' b2nd b1D; rwa [b2sh] at this
  have hml : mLen Wc T p ≤ 2 * D := le_trans le_self_add (le_trans (mLen_succ_le hWc T hp) (mul_le_mul_of_nonneg_left hpD zero_le))
  have hmn : mLen Wc T (neg LAct p) ≤ 2 * D :=
    le_trans le_self_add (le_trans (mLen_succ_le hWc T hnp) (mul_le_mul_of_nonneg_left hnpD zero_le))
  have hms : mShift walkPieces Wc T (neg LAct p) ≤ 4 * D := le_trans (mShift_le htbl hW hWc T hnp) (mul_le_mul_of_nonneg_left hnpD zero_le)
  have h2p : 2 * formulaLen LAct p ≤ 2 * D := mul_le_mul_of_nonneg_left hpD zero_le
  have hE1 : 2 * (0 : V) + 2 * formulaLen LAct p + 8 ≤ E := by
    rw [mul_zero, zero_add]
    exact le_trans (add_le_add (le_trans h2p (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) le_rfl) hE
  have hEi : mLen Wc T p + mShift walkPieces Wc T (neg LAct p) + 2 * formulaLen LAct p + 1 ≤ E := by
    calc mLen Wc T p + mShift walkPieces Wc T (neg LAct p) + 2 * formulaLen LAct p + 1 ≤ 2 * D + 4 * D + 2 * D + 1 :=
          add_le_add (add_le_add (add_le_add hml hms) h2p) le_rfl
      _ = 8 * D + 1 := by ring
      _ ≤ 13 * D + 8 := add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num)
      _ ≤ E := hE
  have hEj : mLen Wc T (neg LAct p) + 2 * formulaLen LAct p + 1 ≤ E := by
    calc mLen Wc T (neg LAct p) + 2 * formulaLen LAct p + 1 ≤ 2 * D + 2 * D + 1 := add_le_add (add_le_add hmn h2p) le_rfl
      _ = 4 * D + 1 := by ring
      _ ≤ 13 * D + 8 := add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num)
      _ ≤ E := hE
  obtain ⟨_, _, cho, _, _⟩ := certNeg_ok htblC hC rfl hWc hp hE1 hEi hEj hΓ₂f hD₁ b2D
  unfold proCutPre
  exact sizeOK_appendV (sizeOK_memberBlock hWc htblN hp hpD Q' D') (sizeOK_appendV (sizeOK_memberBlock hWc htblN hnp hnpD Q' D')
    (sizeOK_reidxL (sizeOK_of_hornOnly cho)))

theorem costSum_proCutPre_le {tbl N N' B' B Wc T p D E Γ Q' D' : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWc : Wc = certPieces) (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B)
    (hp : IsSemiformula LAct 0 p) (hpD : formulaLen LAct p ≤ D) (hnpD : formulaLen LAct (neg LAct p) ≤ D)
    (hE : 13 * D + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) :
    costSum N E Γ (proCutPre walkPieces Wc T p) ≤ len (proCutPre walkPieces Wc T p) *
      (costK N E B 8 (lenQ B' D + Q') (lenD N' B' D + D') + (3 * ((8 : ℕ) : V) + 11) *
        (ctxBoundG (growK B E (lenQ B' D + Q')) Γ (len (proCutPre walkPieces Wc T p)) +
          (fvOccS LAct Γ + len (proCutPre walkPieces Wc T p) * growK B E (lenQ B' D + Q')))) ∧
    len (proCutPre walkPieces Wc T p) ≤ 26 * formulaLen LAct p + (26 * formulaLen LAct (neg LAct p) + 12 * formulaLen LAct p) := by
  obtain ⟨ok, _, _, _, _, _, _, _⟩ := proCutPre_ok htbl hP htblN hWc hp hpD hnpD hE hΓ
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hE)
  refine ⟨costSum_le_of_sizeOK 8 hE1 htbl hBt ok (sizeOK_proCutPre htbl hP htblN hWc hp hpD hnpD hE hΓ), ?_⟩
  have hnp : IsSemiformula LAct 0 (neg LAct p) := hp.neg
  obtain ⟨_, _, _, l1, _, _, _⟩ := memberBlock_ok htbl hP htblN hWc hp hpD hE hΓ
  obtain ⟨_, _, _, l2, _, _, _⟩ := memberBlock_ok htbl hP htblN hWc hnp hnpD hE hΓ
  have l3 := len_certNeg_le (W := Wc) (i := mLen Wc T p + mShift walkPieces Wc T (neg LAct p)) (j := mLen Wc T (neg LAct p)) hp
  unfold proCutPre
  rw [len_appendV, len_appendV, len_reidxL]
  exact add_le_add l1 (add_le_add l2 (le_trans le_self_add l3))

set_option maxHeartbeats 4000000 in
/-- **`proWk` is size-disciplined** at the layout class (Loop W and the fold are Horn-only by their `_ok`). -/
theorem sizeOK_proWk {tbl N N' B' B Wl Wc W T s c i D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hc : c ⊆ s) (hk1 : 1 ≤ len (memberList c))
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D) (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : i + 14 * D + 5 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s i) :
    SizeOK (layQ B B' D) (layD N' B' D) (proWk walkPieces Wl Wc W T s c i) := by
  have hW := hP.walkTable
  have hcs : IsFormulaSet LAct c := fun x hx ↦ hs x (hc hx)
  have hkD : len (memberList s) ≤ D := le_trans (len_memberList_le_setLen hs) hsD
  have hk'D : len (memberList c) ≤ D := le_trans (len_memberList_le_setLen hcs) hcD
  have hE8 : 13 * D + 18 * ‖D‖ + 8 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hE
  set σ := proSig walkPieces Wl Wc W T c with hσ
  have hσle : σ ≤ 6 * D + 1 := proSig_le htbl hP hWc htblN hWl hWp hcs hk1 hcD hE8 hΓ
  have hi : i + σ + 8 * D + 3 ≤ E := by
    calc i + σ + 8 * D + 3 ≤ i + (6 * D + 1) + 8 * D + 3 := add_le_add (add_le_add (add_le_add le_rfl hσle) le_rfl) le_rfl
      _ = i + 14 * D + 4 := by ring
      _ ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hiE
  obtain ⟨lok, lnd, _, _, lLay⟩ := layoutSteps_ok htbl hP htblN hWl hWc hWp hcs hk1 hcD hE8 hΓ
  have lsh : shiftsV (layoutSteps walkPieces Wl Wc W T c) = σ := by rw [hσ, proSig]
  set Γ₁ := finalCtx Γ (layoutSteps walkPieces Wl Wc W T c) with hΓ₁
  have hΓ₁f : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ lok
  have hLay₁ : Layout walkPieces Wc T Γ₁ s (i + σ) := by have := hLay.transport lnd; rwa [lsh] at this
  obtain ⟨wok, wnd, who, wsh, wfacts⟩ := loopW_ok htbl hP hWl hWc hWp rfl hs hc hsD hcD hE hi hΓ₁f lLay hLay₁ _ le_rfl
  set Γ₂ := finalCtx Γ₁ (loopW (qPack Wl W (i + σ) (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) 0
    (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) 0 0) (len (memberList c))) with hΓ₂
  have hΓ₂f : IsFormulaSet LAct Γ₂ := finalCtx_isFormulaSet 8 htbl hΓ₁f wok
  have lLay₂ : Layout walkPieces Wc T Γ₂ c 0 := by have := lLay.transport wnd.noDrop'; rwa [wsh, add_zero] at this
  have hSE : i + σ + (len (memberList s) + 1) + 1 ≤ E := by
    calc i + σ + (len (memberList s) + 1) + 1 = i + σ + (len (memberList s) + 2) := by ring
      _ ≤ i + σ + (8 * D + 3) := add_le_add le_rfl (add_le_add (le_trans hkD (le_mul_of_one_le_left zero_le (by norm_num))) (by norm_num))
      _ = i + σ + 8 * D + 3 := by ring
      _ ≤ E := hi
  have hkE' : 0 + (2 * len (memberList c) + 2) ≤ E := by
    calc 0 + (2 * len (memberList c) + 2) ≤ 6 * D + 2 := by
          rw [zero_add]
          exact add_le_add (le_trans (mul_le_mul_of_nonneg_left hk'D zero_le) (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) le_rfl
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
      _ ≤ E := hE
  have hosE' : ∀ j < len (memberList c), mTop 0 (len (memberList c)) (offVec (memberList c) walkPieces Wc T).[j] + 1 ≤ E :=
    fun j hj ↦ by
    calc _ ≤ 0 + 6 * D + 1 + 1 := add_le_add (mTop_le htbl hW hWc T hcs hcD hj) le_rfl
      _ = 6 * D + 2 := by ring
      _ ≤ 13 * D + 18 * ‖D‖ + 12 := six_le_cap (by norm_num)
      _ ≤ E := hE
  have hin : SubIn Γ₂ 0 (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (^&(i + σ + (len (memberList s) + 1))) :=
    fun j hj ↦ ⟨(lLay₂.1 j hj).2.2.2.1, by have := wfacts j hj; rwa [qK'_pack, qOs'_pack, qI_pack, qK_pack] at this⟩
  obtain ⟨_, _, cho, _, _, _⟩ := subChain_ok htbl hP hWp hΓ₂f (by simp) (termLen_fvar_le' hSE) hk1 hkE' hosE'
    (len_offVec _ _ _ _) hin
  have hlist : proWk walkPieces Wl Wc W T s c i = appendV (layoutSteps walkPieces Wl Wc W T c)
      (appendV (loopW (qPack Wl W (i + σ) (len (memberList s)) (offVec (memberList s) walkPieces Wc T) (memberList s) 0
          (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (memberList c) 0 0) (len (memberList c)))
        (subChain W 0 (len (memberList c)) (offVec (memberList c) walkPieces Wc T) (^&(i + σ + (len (memberList s) + 1))))) := by
    unfold proWk; rw [← hσ]
  rw [hlist]
  exact sizeOK_appendV (sizeOK_layoutSteps hWl hWc hWp htblN hPle hcs hcD)
    (sizeOK_appendV (sizeOK_of_hornOnly who) (sizeOK_of_hornOnly cho))

theorem costSum_proWk_le {tbl N N' B' B Wl Wc W T s c i D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hc : c ⊆ s) (hk1 : 1 ≤ len (memberList c))
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D) (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : i + 14 * D + 5 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s i) :
    costSum N E Γ (proWk walkPieces Wl Wc W T s c i) ≤ len (proWk walkPieces Wl Wc W T s c i) *
      (costK N E B 8 (layQ B B' D) (layD N' B' D) + (3 * ((8 : ℕ) : V) + 11) *
        (ctxBoundG (growK B E (layQ B B' D)) Γ (len (proWk walkPieces Wl Wc W T s c i)) +
          (fvOccS LAct Γ + len (proWk walkPieces Wl Wc W T s c i) * growK B E (layQ B B' D)))) := by
  obtain ⟨ok, _, _, _, _, _⟩ := proWk_ok htbl hP htblN hWl hWc hWp hs hc hk1 hsD hcD hE hiE hΓ hLay
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hE)
  exact costSum_le_of_sizeOK 8 hE1 htbl hBt ok (sizeOK_proWk htbl hP htblN hWl hWc hWp hPle hs hc hk1 hsD hcD hE hiE hΓ hLay)

set_option maxHeartbeats 4000000 in
/-- **`proOr` is size-disciplined** at the layout class. -/
theorem sizeOK_proOr {tbl N N' B' B Wl Wc W T s p q i ip iq D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p) (hq : IsSemiformula LAct 0 q) (hk1 : 1 ≤ len (memberList s))
    (hsD : setLen LAct (insert p (insert q s)) ≤ D) (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : i + 14 * D + 5 ≤ E)
    (hipE : ip + 14 * D + 6 ≤ E) (hiqE : iq + 8 * D + 4 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hLay : Layout walkPieces Wc T Γ s i) (hDp : DossF walkPieces Γ 0 p ip) (hDq : DossF walkPieces Γ 0 q iq) :
    SizeOK (layQ B B' D) (layD N' B' D) (proOr walkPieces Wl Wc W T s p q i ip iq) := by
  have hqs : IsFormulaSet LAct (insert q s) := IsFormulaSet.insert_iff.mpr ⟨hq, hs⟩
  have hsD₁ : setLen LAct (insert q s) ≤ D := le_trans (setLen_le_insert p _) hsD
  have hkq1 : 1 ≤ len (memberList (insert q s)) := one_le_len_memberList_insert q s
  have hE8 : 13 * D + 18 * ‖D‖ + 8 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hE
  have e125 : ∀ ev : V, mkStep proPieces (125 : V) ev = mkStep frag1Pieces (125 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag1 125 (by decide) ev; simpa using this
  set σ₁ := proSig walkPieces Wl Wc W T (insert q s) with hσ₁
  have hσ₁le : σ₁ ≤ 6 * D + 1 := proSig_le htbl hP hWc htblN hWl hWp hqs hkq1 hsD₁ hE8 hΓ
  obtain ⟨ok₁, nd₁, sh₁, lay₁, fr₁, eq₁⟩ := proIns_ok htbl hP htblN hWl hWc hWp hs hq hk1 hsD₁ hE hiE hiqE hΓ hLay hDq
  rw [← hσ₁] at sh₁
  set Γ₁ := finalCtx Γ (proIns walkPieces Wl Wc W T s q i iq) with hΓ₁
  have hΓ₁f : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ ok₁
  have hDp₁ : DossF walkPieces Γ₁ 0 p (ip + 1 + σ₁) := by
    have := dossF_transport' nd₁ hDp; rwa [sh₁, ← add_assoc] at this
  have hiE₂ : (0 : V) + 14 * D + 5 ≤ E := by rw [zero_add]; exact le_trans (add_le_add le_add_self le_rfl) (le_trans (add_le_add le_rfl (by norm_num)) hipE)
  have hipE₂ : ip + 1 + σ₁ + 8 * D + 4 ≤ E := by
    calc ip + 1 + σ₁ + 8 * D + 4 ≤ ip + 1 + (6 * D + 1) + 8 * D + 4 := add_le_add (add_le_add (add_le_add le_rfl hσ₁le) le_rfl) le_rfl
      _ = ip + 14 * D + 6 := by ring
      _ ≤ E := hipE
  have h1 := sizeOK_proIns (B := B) htbl hP htblN hWl hWc hWp hPle hs hq hk1 hsD₁ hE hiE hiqE hΓ hLay hDq
  have h2 := sizeOK_proIns (B := B) htbl hP htblN hWl hWc hWp hPle hqs hp hkq1 hsD hE hiE₂ hipE₂ hΓ₁f lay₁ hDp₁
  unfold proOr
  rw [← hσ₁]
  refine sizeOK_appendV h1 (sizeOK_appendV h2 (sizeOK_single (stepSizeOK_of_tag ?_)))
  rw [hWp, e125, ftag_congInsertS rfl]; simp

theorem costSum_proOr_le {tbl N N' B' B Wl Wc W T s p q i ip iq D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p) (hq : IsSemiformula LAct 0 q) (hk1 : 1 ≤ len (memberList s))
    (hsD : setLen LAct (insert p (insert q s)) ≤ D) (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : i + 14 * D + 5 ≤ E)
    (hipE : ip + 14 * D + 6 ≤ E) (hiqE : iq + 8 * D + 4 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hLay : Layout walkPieces Wc T Γ s i) (hDp : DossF walkPieces Γ 0 p ip) (hDq : DossF walkPieces Γ 0 q iq) :
    costSum N E Γ (proOr walkPieces Wl Wc W T s p q i ip iq) ≤ len (proOr walkPieces Wl Wc W T s p q i ip iq) *
      (costK N E B 8 (layQ B B' D) (layD N' B' D) + (3 * ((8 : ℕ) : V) + 11) *
        (ctxBoundG (growK B E (layQ B B' D)) Γ (len (proOr walkPieces Wl Wc W T s p q i ip iq)) +
          (fvOccS LAct Γ + len (proOr walkPieces Wl Wc W T s p q i ip iq) * growK B E (layQ B B' D)))) := by
  obtain ⟨ok, _, _, _, _, _, _, _⟩ := proOr_ok htbl hP htblN hWl hWc hWp hs hp hq hk1 hsD hE hiE hipE hiqE hΓ hLay hDp hDq
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hE)
  exact costSum_le_of_sizeOK 8 hE1 htbl hBt ok
    (sizeOK_proOr htbl hP htblN hWl hWc hWp hPle hs hp hq hk1 hsD hE hiE hipE hiqE hΓ hLay hDp hDq)

/-! ### 11.6 `proShift`: the Horn-only loops by their rows, Loop S by `loopS_ok` -/

lemma hornOnly_subChainAux {W : V} (hWp : W = proPieces) (i' k' os A : V) : ∀ c : V, HornOnly (subChainAux ⟪W, i', k', os, A⟫ c) := by
  subst hWp
  have e81 : ∀ ev : V, mkStep proPieces (81 : V) ev = mkStep layoutPieces (81 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 81 (by decide) ev; simpa using this
  have e112 : ∀ ev : V, mkStep proPieces (112 : V) ev = mkStep frag1Pieces (112 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag1 112 (by decide) ev; simpa using this
  intro c
  induction c using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => rw [subChainAux_zero]; exact hornOnly_single (by rw [e81, ltag_emptySubsetC rfl]; simp)
  | succ c ih =>
    rw [subChainAux_succ]
    exact hornOnly_appendV ih (hornOnly_single (by unfold subLink; rw [e112, ftag_insertSubset rfl]; simp))

lemma hornOnly_subChain {W : V} (hWp : W = proPieces) (i' k' os A : V) : HornOnly (subChain W i' k' os A) :=
  hornOnly_subChainAux hWp i' k' os A k'

lemma hornOnly_shBase {W : V} (hWp : W = proPieces) : HornOnly (shBase W) := by
  subst hWp
  have e138 : ∀ ev : V, mkStep proPieces (138 : V) ev = mkStep frag2Pieces (138 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag2 138 (by decide) ev; simpa using this
  have e145 : ∀ ev : V, mkStep proPieces (145 : V) ev = mkStep frag2Pieces (145 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag2 145 (by decide) ev; simpa using this
  have e148 : ∀ ev : V, mkStep proPieces (148 : V) ev = mkStep frag2Pieces (148 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag2 148 (by decide) ev; simpa using this
  have e42 : ∀ ev : V, mkStep proPieces (42 : V) ev = mkStep layoutPieces (42 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 42 (by decide) ev; simpa using this
  unfold shBase
  exact hornOnly_cons (by rw [e138, gtag_setShiftTotal rfl]; simp) (hornOnly_cons (by rw [e145, gtag_setShiftEmpty rfl]; simp)
    (hornOnly_cons (by rw [e42, ltag_eqSymm rfl]; simp) (hornOnly_single (by rw [e148, gtag_congSetShiftL rfl]; simp))))

lemma hornOnly_loopI {Wc W i₂ k os xs k' os' ys σ : V} (hWp : W = proPieces) :
    ∀ m : V, HornOnly (loopI (shPack Wc W i₂ k os xs k' os' ys σ) m) := by
  subst hWp
  have e144 : ∀ ev : V, mkStep proPieces (144 : V) ev = mkStep frag2Pieces (144 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag2 144 (by decide) ev; simpa using this
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => rw [loopI_zero]; exact hornOnly_nil
  | succ m ih =>
    rw [loopI_succ]
    refine hornOnly_appendV ih (hornOnly_single ?_)
    rw [qW_shPack, e144, gtag_setShiftInsert rfl]; simp

lemma hornOnly_uSubAux {Wc W i₂ k os xs k' os' ys σ : V} (hWp : W = proPieces) :
    ∀ m : V, HornOnly (uSubAux (shPack Wc W i₂ k os xs k' os' ys σ) m) := by
  subst hWp
  have e81 : ∀ ev : V, mkStep proPieces (81 : V) ev = mkStep layoutPieces (81 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 81 (by decide) ev; simpa using this
  have e112 : ∀ ev : V, mkStep proPieces (112 : V) ev = mkStep frag1Pieces (112 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag1 112 (by decide) ev; simpa using this
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => rw [uSubAux_zero, qW_shPack]; exact hornOnly_single (by rw [e81, ltag_emptySubsetC rfl]; simp)
  | succ m ih =>
    rw [uSubAux_succ]
    refine hornOnly_appendV ih (hornOnly_single ?_)
    unfold uLink; rw [qW_shPack, e112, ftag_insertSubset rfl]; simp

lemma hornOnly_uSub {Wc W i₂ k os xs k' os' ys σ : V} (hWp : W = proPieces) :
    HornOnly (uSub (shPack Wc W i₂ k os xs k' os' ys σ)) := hornOnly_uSubAux hWp _

lemma hornOnly_loopM {Wc W i₂ k os xs k' os' ys σ : V} (hWp : W = proPieces) :
    ∀ m : V, HornOnly (loopM (shPack Wc W i₂ k os xs k' os' ys σ) m) := by
  subst hWp
  have e139 : ∀ ev : V, mkStep proPieces (139 : V) ev = mkStep frag2Pieces (139 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag2 139 (by decide) ev; simpa using this
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => rw [loopM_zero]; exact hornOnly_nil
  | succ m ih =>
    rw [loopM_succ]
    refine hornOnly_appendV ih (hornOnly_single ?_)
    rw [qW_shPack, e139, gtag_shiftMemSetShift rfl]; simp

/-- **`proShift` is size-disciplined** at the layout class (Loop S is Horn-only by `proShiftPre_ok`; the other loops by
their rows). The hypotheses are those of `proShift_ok`. -/
theorem sizeOK_proShift {tbl N N' B' B Wl Wc W T s c i D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hc : IsFormulaSet LAct c) (hsc : s = setShift LAct c) (hk1' : 1 ≤ len (memberList c))
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D) (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : i + 16 * D + 8 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s i) :
    SizeOK (layQ B B' D) (layD N' B' D) (proShift walkPieces Wl Wc W T s c i) := by
  obtain ⟨_, _, _, _, sho⟩ := proShiftPre_ok htbl hP htblN hWl hWc hWp hs hc hsc hk1' hsD hcD hE hiE hΓ hLay
  have e75 : ∀ ev : V, mkStep proPieces (75 : V) ev = mkStep layoutPieces (75 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 75 (by decide) ev; simpa using this
  have e148 : ∀ ev : V, mkStep proPieces (148 : V) ev = mkStep frag2Pieces (148 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag2 148 (by decide) ev; simpa using this
  rw [proShift_eq]
  refine sizeOK_appendV ?_ ?_
  · unfold proShiftPre
    exact sizeOK_appendV (sizeOK_of_hornOnly (hornOnly_shBase hWp)) (sizeOK_appendV (sizeOK_of_hornOnly (hornOnly_chainSteps hWl _))
      (sizeOK_appendV (sizeOK_layoutSteps hWl hWc hWp htblN hPle hc hcD) (sizeOK_of_hornOnly sho)))
  · unfold shTail2
    refine sizeOK_appendV (sizeOK_of_hornOnly (hornOnly_loopI hWp _)) (sizeOK_appendV (sizeOK_of_hornOnly (hornOnly_uSub hWp))
      (sizeOK_appendV (sizeOK_of_hornOnly (hornOnly_loopM hWp _)) (sizeOK_appendV (sizeOK_of_hornOnly (hornOnly_subChain hWp _ _ _ _))
        (sizeOK_cons (stepSizeOK_of_tag ?_) (sizeOK_single (stepSizeOK_of_tag ?_))))))
    · rw [hWp, e75, ltag_subsetAntisymm rfl]; simp
    · rw [hWp, e148, gtag_congSetShiftL rfl]; simp

theorem costSum_proShift_le {tbl N N' B' B Wl Wc W T s c i D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hc : IsFormulaSet LAct c) (hsc : s = setShift LAct c) (hk1' : 1 ≤ len (memberList c))
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D) (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : i + 16 * D + 8 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s i) :
    costSum N E Γ (proShift walkPieces Wl Wc W T s c i) ≤ len (proShift walkPieces Wl Wc W T s c i) *
      (costK N E B 8 (layQ B B' D) (layD N' B' D) + (3 * ((8 : ℕ) : V) + 11) *
        (ctxBoundG (growK B E (layQ B B' D)) Γ (len (proShift walkPieces Wl Wc W T s c i)) +
          (fvOccS LAct Γ + len (proShift walkPieces Wl Wc W T s c i) * growK B E (layQ B B' D)))) := by
  obtain ⟨ok, _, _, _, _, _⟩ := proShift_ok htbl hP htblN hWl hWc hWp hs hc hsc hk1' hsD hcD hE hiE hΓ hLay
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hE)
  exact costSum_le_of_sizeOK 8 hE1 htbl hBt ok
    (sizeOK_proShift htbl hP htblN hWl hWc hWp hPle hs hc hsc hk1' hsD hcD hE hiE hΓ hLay)

end proSizes


/-! ## 12. The EMPTY sequent (`DESIGN_fragments.md` §4.7/§4.8 at `∅`; a nonstandard derivation of `∅`)

`Derivation` admits `wkRule s d'` with `fstIdx d' ⊆ s` and `shiftRule s d'` with `s = setShift (fstIdx d')`, so in a
model `V ⊧ ¬Con(TAct)` a node's sequent may be EMPTY (as the child of `wk`, as both sides of `shift`, as the parent of
`cut`; never at a leaf, never as an `insert` child). "Every sequent of a derivation is nonempty" is therefore FALSE
in general, and the honest treatment is a `k = 0` layout: `Layout0` = the `Layout` predicate at `s = 0` (vacuous
members, `setLenFact &i &(i + 1)`, `leFact &i (bnum 0)`) TOGETHER WITH the identification `eqFactB &(i + 1) 𝟎` of the
sequent object — the fact every consumer needs in place of a chain. `layoutSteps0` builds it in five steps (rows
`eqTotal`, `setLenTotalC`, `eqSymm`, `congSetLenR`, and the prologue row `setLenEmptyLe` = 156); the table rows
`congSubsetL` (157) and `congSetShiftR` (158) move `emptySubsetC`/`setShiftFact` facts onto the object. -/

section emptySequent

/-- The reading of the prologue row `setLenEmptyLe` (156). -/
lemma ProTable.setLenEmptyLe {tbl : V} (h : ProTable tbl) :
    ((pIdx_setLenEmptyLe : ℕ) : V) < len tbl ∧
    rowM tbl.[((pIdx_setLenEmptyLe : ℕ) : V)] = ((1 : ℕ) : V) ∧
    rowB tbl.[((pIdx_setLenEmptyLe : ℕ) : V)] = impChainV LAct (vecOf row_setLenEmptyLe_as) row_setLenEmptyLe_c := by
  have hlt : pIdx_setLenEmptyLe < proRows.length := by
    rw [proRows_length]; simp only [proRowCount, proBase, pIdx_setLenEmptyLe, topRowCount, proExtraRowCount]; omega
  have hr := h.2 pIdx_setLenEmptyLe hlt
  have e' : proRows[pIdx_setLenEmptyLe]? = proExtraRows[1]? := by
    have h1 : pIdx_setLenEmptyLe < (topRows ++ proExtraRows).length := by
      rw [List.length_append]; simp only [pIdx_setLenEmptyLe, topRows_length, proExtraRows_length, topRowCount, proExtraRowCount]; omega
    have h2 : topRows.length ≤ pIdx_setLenEmptyLe := by rw [topRows_length]; simp only [pIdx_setLenEmptyLe, topRowCount]; omega
    unfold proRows
    rw [List.getElem?_append_left h1, List.getElem?_append_right h2]
    rfl
  have e : proRows[pIdx_setLenEmptyLe] = proExtraRows[1] := by
    rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem (by decide : 1 < proExtraRows.length)] at e'
    exact Option.some.inj e'
  rw [e] at hr
  refine ⟨lt_of_lt_of_le (by exact_mod_cast hlt) (proRows_length ▸ h.1), hr.1, ?_⟩
  rw [impChainV_vecOf, hr.2]
  exact quote_row_setLenEmptyLe

/-- The reading of the table row `congSubsetL` (157). -/
lemma ProTable.congSubsetL {tbl : V} (h : ProTable tbl) :
    ((pIdx_congSubsetL : ℕ) : V) < len tbl ∧
    rowM tbl.[((pIdx_congSubsetL : ℕ) : V)] = ((3 : ℕ) : V) ∧
    rowB tbl.[((pIdx_congSubsetL : ℕ) : V)] = impChainV LAct (vecOf row_congSubsetL_as) row_congSubsetL_c := by
  have hlt : pIdx_congSubsetL < proRows.length := by
    rw [proRows_length]; simp only [proRowCount, proBase, pIdx_congSubsetL, topRowCount, proExtraRowCount]; omega
  have hr := h.2 pIdx_congSubsetL hlt
  have e' : proRows[pIdx_congSubsetL]? = proExtraRows[2]? := by
    have h1 : pIdx_congSubsetL < (topRows ++ proExtraRows).length := by
      rw [List.length_append]; simp only [pIdx_congSubsetL, topRows_length, proExtraRows_length, topRowCount, proExtraRowCount]; omega
    have h2 : topRows.length ≤ pIdx_congSubsetL := by rw [topRows_length]; simp only [pIdx_congSubsetL, topRowCount]; omega
    unfold proRows
    rw [List.getElem?_append_left h1, List.getElem?_append_right h2]
    rfl
  have e : proRows[pIdx_congSubsetL] = proExtraRows[2] := by
    rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem (by decide : 2 < proExtraRows.length)] at e'
    exact Option.some.inj e'
  rw [e] at hr
  refine ⟨lt_of_lt_of_le (by exact_mod_cast hlt) (proRows_length ▸ h.1), hr.1, ?_⟩
  rw [impChainV_vecOf, hr.2]
  exact quote_row_congSubsetL

/-- The reading of the table row `congSetShiftR` (158). -/
lemma ProTable.congSetShiftR {tbl : V} (h : ProTable tbl) :
    ((pIdx_congSetShiftR : ℕ) : V) < len tbl ∧
    rowM tbl.[((pIdx_congSetShiftR : ℕ) : V)] = ((3 : ℕ) : V) ∧
    rowB tbl.[((pIdx_congSetShiftR : ℕ) : V)] = impChainV LAct (vecOf row_congSetShiftR_as) row_congSetShiftR_c := by
  have hlt : pIdx_congSetShiftR < proRows.length := by
    rw [proRows_length]; simp only [proRowCount, proBase, pIdx_congSetShiftR, topRowCount, proExtraRowCount]; omega
  have hr := h.2 pIdx_congSetShiftR hlt
  have e' : proRows[pIdx_congSetShiftR]? = proExtraRows[3]? := by
    have h1 : pIdx_congSetShiftR < (topRows ++ proExtraRows).length := by
      rw [List.length_append]; simp only [pIdx_congSetShiftR, topRows_length, proExtraRows_length, topRowCount, proExtraRowCount]; omega
    have h2 : topRows.length ≤ pIdx_congSetShiftR := by rw [topRows_length]; simp only [pIdx_congSetShiftR, topRowCount]; omega
    unfold proRows
    rw [List.getElem?_append_left h1, List.getElem?_append_right h2]
    rfl
  have e : proRows[pIdx_congSetShiftR] = proExtraRows[3] := by
    rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem (by decide : 3 < proExtraRows.length)] at e'
    exact Option.some.inj e'
  rw [e] at hr
  refine ⟨lt_of_lt_of_le (by exact_mod_cast hlt) (proRows_length ▸ h.1), hr.1, ?_⟩
  rw [impChainV_vecOf, hr.2]
  exact quote_row_congSetShiftR

/-- **The layout of the empty sequent at chain offset `i`**: the `Layout` predicate at `s = 0` and the identification
`eqFactB &(i + 1) 𝟎` of the sequent object. -/
def Layout0 (Ww Wc T Γ i : V) : Prop :=
  Layout Ww Wc T Γ 0 i ∧ neg LAct (eqFactB (^&(i + 1)) (𝟎 : V)) ∈ Γ

lemma len_memberList_zero : len (memberList (0 : V)) = 0 := by simp [memberList]

/-- A layout is monotone in the context (every conjunct is a membership). -/
lemma Layout.mono {Ww Wc T Γ Γ' s i : V} (h : ∀ x ∈ Γ, x ∈ Γ') (hL : Layout Ww Wc T Γ s i) : Layout Ww Wc T Γ' s i := by
  obtain ⟨hmem, hsl, hle⟩ := hL
  refine ⟨fun j hj ↦ ?_, h _ hsl, h _ hle⟩
  obtain ⟨hD, h1, h2, h3, h4, h5⟩ := hmem j hj
  exact ⟨hD.mono (fun x hx ↦ h x hx), h _ h1, h _ h2, h _ h3, h _ h4, h _ h5⟩

lemma Layout0.mono {Ww Wc T Γ Γ' i : V} (h : ∀ x ∈ Γ, x ∈ Γ') (hL : Layout0 Ww Wc T Γ i) : Layout0 Ww Wc T Γ' i :=
  ⟨hL.1.mono h, h _ hL.2⟩

theorem Layout0.transport {Ww Wc T Γ i S : V} (hS : NoDrop' S) (h : Layout0 Ww Wc T Γ i) :
    Layout0 Ww Wc T (finalCtx Γ S) (i + shiftsV S) := by
  refine ⟨h.1.transport hS, ?_⟩
  have := mem_finalCtx_of_mem' hS h.2
  rwa [shiftIterV_neg (isFormula_eqFactB (by simp) isSemiterm_zeroV), shiftIterV_eqFactB (by simp) isSemiterm_zeroV,
    termShiftIterV_fvar, termShiftIterV_zeroV, add_right_comm] at this

/-- **`layoutSteps0`**: `eqTotal [𝟎]` (the sequent object `&0 = 𝟎`), `setLenTotalC [&0]` (its length `&0`), `eqSymm [&1, 𝟎]`,
`congSetLenR [&1, 𝟎, &0]` (`setLenFact &0 𝟎`), `setLenEmptyLe [&0]` (`leFact &0 𝟎 = leFact &0 (bnum 0)`). -/
noncomputable def layoutSteps0 (W : V) : V :=
  mkStep W 40 ?[(𝟎 : V)] ∷ mkStep W 85 ?[^&0] ∷ mkStep W 42 ?[^&1, (𝟎 : V)] ∷ mkStep W 124 ?[^&1, (𝟎 : V), ^&0] ∷
    mkStep W 156 ?[^&0] ∷ (0 : V)

noncomputable def layoutSteps0Def : 𝚺₁.Semisentence 2 := .mkSigma
  “y W. ∃ z, !cTVGraph z 0 ∧ ∃ f0, !qqFvarDef f0 0 ∧ ∃ f1, !qqFvarDef f1 1 ∧
    ∃ e₁, !adjoinDef e₁ z 0 ∧ ∃ s₁, !mkStepDef s₁ W 40 e₁ ∧
    ∃ e₂, !adjoinDef e₂ f0 0 ∧ ∃ s₂, !mkStepDef s₂ W 85 e₂ ∧
    ∃ e₃, !adjoinDef e₃ f1 e₁ ∧ ∃ s₃, !mkStepDef s₃ W 42 e₃ ∧
    ∃ e₄', !adjoinDef e₄' z e₂ ∧ ∃ e₄, !adjoinDef e₄ f1 e₄' ∧ ∃ s₄, !mkStepDef s₄ W 124 e₄ ∧
    ∃ s₅, !mkStepDef s₅ W 156 e₂ ∧
    ∃ l₅, !adjoinDef l₅ s₅ 0 ∧ ∃ l₄, !adjoinDef l₄ s₄ l₅ ∧ ∃ l₃, !adjoinDef l₃ s₃ l₄ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧
    !adjoinDef y s₁ l₂”

instance layoutSteps0_defined : 𝚺₁-Function₁ (layoutSteps0 : V → V) via layoutSteps0Def := .mk fun v ↦ by
  simp [layoutSteps0Def, layoutSteps0, mkStep_defined.iff, cTV.defined.iff, cTV_zero, numeral_eq_natCast]
instance layoutSteps0_definable : 𝚺₁-Function₁ (layoutSteps0 : V → V) := layoutSteps0_defined.to_definable

set_option maxHeartbeats 2000000 in
/-- **`layoutSteps0` is applicable and leaves `Layout0` at offset `0`**: two eigenvariables, five steps. -/
theorem layoutSteps0_ok {tbl N W Wc T E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (hWp : W = proPieces)
    (hΓ : IsFormulaSet LAct Γ) (hE : (2 : V) ≤ E) :
    ListOK tbl E ((8 : ℕ) : V) Γ (layoutSteps0 W) ∧ NoDrop' (layoutSteps0 W) ∧ shiftsV (layoutSteps0 W) = 2 ∧
    len (layoutSteps0 W) = 5 ∧ Layout0 walkPieces Wc T (finalCtx Γ (layoutSteps0 W)) 0 := by
  have hL := hP.layoutTable
  have hF1 := hP.frag1Table
  have e40 : ∀ ev : V, mkStep proPieces (40 : V) ev = mkStep layoutPieces (40 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 40 (by decide) ev; simpa using this
  have e85 : ∀ ev : V, mkStep proPieces (85 : V) ev = mkStep layoutPieces (85 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 85 (by decide) ev; simpa using this
  have e42 : ∀ ev : V, mkStep proPieces (42 : V) ev = mkStep layoutPieces (42 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 42 (by decide) ev; simpa using this
  have e124 : ∀ ev : V, mkStep proPieces (124 : V) ev = mkStep frag1Pieces (124 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag1 124 (by decide) ev; simpa using this
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) hE
  have h0 : IsSemiterm LAct (0 : V) (𝟎 : V) := isSemiterm_zeroV
  have h0E : termLen LAct (𝟎 : V) ≤ E := termLen_zeroV_le hE1
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hf0E : termLen LAct (^&0 : V) ≤ E := termLen_fvar0_le hE1
  have hf1 : IsSemiterm LAct 0 (^&1 : V) := by simp
  have hf1E : termLen LAct (^&1 : V) ≤ E := termLen_fvar_le' (by rw [one_add_one_eq_two]; exact hE)
  -- step 1: the object `&0 = 𝟎`
  obtain ⟨ok₁, tg₁, cx₁⟩ := lok_eqTotal htbl hL rfl hΓ h0 h0E
  rw [← e40, ← hWp] at ok₁ tg₁ cx₁
  rw [Nat.cast_zero, termShift_zeroV] at cx₁
  have hΓ₁f : IsFormulaSet LAct (insert (neg LAct (eqFactB (^&0) (𝟎 : V))) (setShift LAct Γ)) := by
    rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  -- step 2: its length `&0`, with `setLenFact &0 &1`; the object moves to `&1`
  obtain ⟨ok₂, tg₂, cx₂⟩ := lok_setLenTotalC htbl hL rfl hΓ₁f hf0 hf0E
  rw [← e85, ← hWp] at ok₂ tg₂ cx₂
  rw [Nat.cast_zero, termShift_fvar, zero_add] at cx₂
  have heq₂ : neg LAct (eqFactB (^&1) (𝟎 : V)) ∈
      insert (neg LAct (setLenFact (^&0) (^&1))) (setShift LAct (insert (neg LAct (eqFactB (^&0) (𝟎 : V))) (setShift LAct Γ))) := by
    have := mem_shift_insert (f := neg LAct (setLenFact (^&0) (^&1))) (memInsSelf (neg LAct (eqFactB (^&0) (𝟎 : V))) (setShift LAct Γ))
    rwa [shift_neg (isFormula_eqFactB hf0 h0), shift_eqFactB hf0 h0, termShift_fvar, termShift_zeroV, zero_add] at this
  have hΓ₂f : IsFormulaSet LAct (insert (neg LAct (setLenFact (^&0) (^&1))) (setShift LAct (insert (neg LAct (eqFactB (^&0) (𝟎 : V))) (setShift LAct Γ)))) := by
    rw [← cx₂]; exact isFormulaSet_ctxAfter 8 htbl ok₂
  -- step 3: `eqSymm`
  obtain ⟨ok₃, tg₃, cx₃⟩ := lok_eqSymm htbl hL rfl hΓ₂f hf1 hf1E h0 h0E heq₂
  rw [← e42, ← hWp] at ok₃ tg₃ cx₃
  have hΓ₃f : IsFormulaSet LAct (insert (neg LAct (eqFactB (𝟎 : V) (^&1))) (insert (neg LAct (setLenFact (^&0) (^&1)))
      (setShift LAct (insert (neg LAct (eqFactB (^&0) (𝟎 : V))) (setShift LAct Γ))))) := by
    rw [← cx₃]; exact isFormulaSet_ctxAfter 8 htbl ok₃
  -- step 4: `congSetLenR`
  obtain ⟨ok₄, tg₄, cx₄⟩ := fok_congSetLenR htbl hF1 rfl hΓ₃f hf1 hf1E h0 h0E hf0 hf0E (memInsSelf _ _) (memIns (memInsSelf _ _))
  rw [← e124, ← hWp] at ok₄ tg₄ cx₄
  have hΓ₄f : IsFormulaSet LAct (insert (neg LAct (setLenFact (^&0) (𝟎 : V))) (insert (neg LAct (eqFactB (𝟎 : V) (^&1)))
      (insert (neg LAct (setLenFact (^&0) (^&1))) (setShift LAct (insert (neg LAct (eqFactB (^&0) (𝟎 : V))) (setShift LAct Γ)))))) := by
    rw [← cx₄]; exact isFormulaSet_ctxAfter 8 htbl ok₄
  -- step 5: `setLenEmptyLe`
  obtain ⟨hlen, hrow⟩ := hP.setLenEmptyLe
  obtain ⟨ok₅, tg₅, cx₅⟩ := pok_setLenEmptyLe htbl hWp hlen hrow hΓ₄f hf0 hf0E (memInsSelf _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold layoutSteps0
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    refine listOK_cons ok₄ ?_
    rw [cx₄]
    exact listOK_single ok₅
  · unfold layoutSteps0
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp) (noDrop'_cons (by rw [tg₃]; simp)
      (noDrop'_cons (by rw [tg₄]; simp) (noDrop'_single (by rw [tg₅]; simp)))))
  · unfold layoutSteps0
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₃, tg₄, tg₅]
    simp; norm_num
  · unfold layoutSteps0; simp [len_adjoin]; norm_num
  · unfold layoutSteps0
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_cons, cx₄, finalCtx_single, cx₅]
    refine ⟨⟨fun j hj ↦ ?_, ?_, ?_⟩, ?_⟩
    · rw [len_memberList_zero] at hj; exact absurd hj (by simp)
    · rw [len_memberList_zero, zero_add, zero_add]; exact memIns (memIns (memIns (memInsSelf _ _)))
    · rw [← emptyset_def, setLen_empty, bnum_zero]; exact memInsSelf _ _
    · rw [zero_add]; exact memIns (memIns (memIns heq₂))

/-- **`proWk0 s i`** — the `wk` child is EMPTY: `layoutSteps0` (the child's `Layout0` at `0`, its object `&1`), then
`emptySubsetC [S]` and `congSubsetL [𝟎, &1, S]` → `subsetFact &1 S` (`nodeWk_ok`'s `subsetFact &ic &is` with `ic = 1`;
`S = &(i + 2 + (k + 1))` the parent's chain top after the two eigenvariables). -/
noncomputable def proWk0 (W s i : V) : V :=
  appendV (layoutSteps0 W)
    ?[mkStep W 81 ?[^&(i + 2 + (len (memberList s) + 1))],
      mkStep W 157 ?[(𝟎 : V), ^&1, ^&(i + 2 + (len (memberList s) + 1))]]

noncomputable def proWk0Def : 𝚺₁.Semisentence 4 := .mkSigma
  “y W s i. ∃ L, !layoutSteps0Def L W ∧ ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧ ∃ iS, iS = i + 2 + (k + 1) ∧
    ∃ zS, !qqFvarDef zS iS ∧ ∃ z, !cTVGraph z 0 ∧ ∃ f1, !qqFvarDef f1 1 ∧
    ∃ e₁, !adjoinDef e₁ zS 0 ∧ ∃ s₁, !mkStepDef s₁ W 81 e₁ ∧
    ∃ e₂', !adjoinDef e₂' f1 e₁ ∧ ∃ e₂, !adjoinDef e₂ z e₂' ∧ ∃ s₂, !mkStepDef s₂ W 157 e₂ ∧
    ∃ l₂, !adjoinDef l₂ s₂ 0 ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧ !appendVDef y L l₁”

instance proWk0_defined : 𝚺₁-Function₃ (proWk0 : V → V → V → V) via proWk0Def := .mk fun v ↦ by
  simp [proWk0Def, proWk0, layoutSteps0_defined.iff, memberList_defined.iff, mkStep_defined.iff, cTV.defined.iff, cTV_zero,
    appendV_defined.iff, numeral_eq_natCast]
instance proWk0_definable : 𝚺₁-Function₃ (proWk0 : V → V → V → V) := proWk0_defined.to_definable

set_option maxHeartbeats 2000000 in
/-- **`proWk0` is applicable**: two eigenvariables; afterwards the child's `Layout0` at `0`, the parent's layout at `i + 2`,
and `subsetFact &1 &(i + 2 + (k + 1))`. -/
theorem proWk0_ok {tbl N W Wc T s i E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (hWp : W = proPieces)
    (hΓ : IsFormulaSet LAct Γ) (hiE : i + 2 + (len (memberList s) + 1) + 1 ≤ E) (hLay : Layout walkPieces Wc T Γ s i) :
    ListOK tbl E ((8 : ℕ) : V) Γ (proWk0 W s i) ∧ NoDrop' (proWk0 W s i) ∧ shiftsV (proWk0 W s i) = 2 ∧
    Layout0 walkPieces Wc T (finalCtx Γ (proWk0 W s i)) 0 ∧
    Layout walkPieces Wc T (finalCtx Γ (proWk0 W s i)) s (i + 2) ∧
    neg LAct (subsetFact (^&1) (^&(i + 2 + (len (memberList s) + 1)))) ∈ finalCtx Γ (proWk0 W s i) := by
  have hL := hP.layoutTable
  have e81 : ∀ ev : V, mkStep proPieces (81 : V) ev = mkStep layoutPieces (81 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 81 (by decide) ev; simpa using this
  have hE2 : (2 : V) ≤ E := le_trans le_add_self (le_trans le_self_add (le_trans le_self_add hiE))
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) hE2
  obtain ⟨lok, lnd, lsh, _, lLay⟩ := layoutSteps0_ok htbl hP hWp hΓ hE2
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ (layoutSteps0 W) := ⟨_, rfl⟩
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 8 htbl hΓ lok
  have hLay₁ : Layout walkPieces Wc T Γ₁ s (i + 2) := by rw [hΓ₁]; have := hLay.transport lnd; rwa [lsh] at this
  have lLay₁ : Layout0 walkPieces Wc T Γ₁ 0 := by rw [hΓ₁]; exact lLay
  have hSE : i + 2 + (len (memberList s) + 1) + 1 ≤ E := hiE
  obtain ⟨ok₁, tg₁, cx₁⟩ := lok_emptySubsetC htbl hL rfl hΓ₁f (by simp) (termLen_fvar_le' hSE)
  rw [← e81, ← hWp] at ok₁ tg₁ cx₁
  have hΓ₂f : IsFormulaSet LAct (insert (neg LAct (subsetFact (𝟎 : V) (^&(i + 2 + (len (memberList s) + 1))))) Γ₁) := by
    rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  obtain ⟨hlen, hrow⟩ := hP.congSubsetL
  obtain ⟨ok₂, tg₂, cx₂⟩ := pok_congSubsetL htbl hWp hlen hrow hΓ₂f isSemiterm_zeroV (termLen_zeroV_le hE1) (by simp)
    (termLen_fvar_le' (by rw [one_add_one_eq_two]; exact hE2)) (by simp) (termLen_fvar_le' hSE)
    (memIns (by have := lLay₁.2; rwa [zero_add] at this)) (memInsSelf _ _)
  have hnd : NoDrop' (?[mkStep W 81 ?[^&(i + 2 + (len (memberList s) + 1))],
      mkStep W 157 ?[(𝟎 : V), ^&1, ^&(i + 2 + (len (memberList s) + 1))]] : V) :=
    noDrop'_cons (Or.inl tg₁) (noDrop'_single (Or.inl tg₂))
  have hsh : shiftsV (?[mkStep W 81 ?[^&(i + 2 + (len (memberList s) + 1))],
      mkStep W 157 ?[(𝟎 : V), ^&1, ^&(i + 2 + (len (memberList s) + 1))]] : V) = 0 := by
    rw [shiftsV_cons_tag0 tg₁, shiftsV_single_tag0 tg₂]
  unfold proWk0
  refine ⟨listOK_appendV lok (by rw [← hΓ₁]; exact listOK_cons ok₁ (by rw [cx₁]; exact listOK_single ok₂)),
    noDrop'_appendV lnd hnd, ?_, ?_, ?_, ?_⟩
  · rw [shiftsV_appendV, lsh, hsh, add_zero]
  · rw [finalCtx_appendV, ← hΓ₁]; have := lLay₁.transport hnd; rwa [hsh, add_zero] at this
  · rw [finalCtx_appendV, ← hΓ₁]; have := hLay₁.transport hnd; rwa [hsh, add_zero] at this
  · rw [finalCtx_appendV, ← hΓ₁, finalCtx_cons, cx₁, finalCtx_single, cx₂]; exact memInsSelf _ _

/-- **`proShift0 i`** — BOTH sequents of a `shift` node are empty (`setShift ∅ = ∅`): `layoutSteps0` (the child at `0`), then
`setShiftTotal [𝟎]`, `setShiftEmpty [&0]`, `eqSymm [&0, 𝟎]`, `eqTrans [S, 𝟎, &0]` (`S = &(i + 3 + 1)` the parent's
object after the three eigenvariables), `congSetShiftL [&0, S, 𝟎]` → `setShiftFact S 𝟎`, `congSetShiftR [S, 𝟎, &2]`
→ `setShiftFact S s''` (`s'' = &2` the child's object) — `nodeShift_ok`'s `hss`. -/
noncomputable def proShift0 (W i : V) : V :=
  appendV (layoutSteps0 W)
    (mkStep W 138 ?[(𝟎 : V)] ∷ mkStep W 145 ?[^&0] ∷ mkStep W 42 ?[^&0, (𝟎 : V)] ∷
      mkStep W 43 ?[^&(i + 3 + 1), (𝟎 : V), ^&0] ∷ mkStep W 148 ?[^&0, ^&(i + 3 + 1), (𝟎 : V)] ∷
      mkStep W 158 ?[^&(i + 3 + 1), (𝟎 : V), ^&2] ∷ (0 : V))

noncomputable def proShift0Def : 𝚺₁.Semisentence 3 := .mkSigma
  “y W i. ∃ L, !layoutSteps0Def L W ∧ ∃ z, !cTVGraph z 0 ∧ ∃ f0, !qqFvarDef f0 0 ∧ ∃ f2, !qqFvarDef f2 2 ∧
    ∃ iS, iS = i + 3 + 1 ∧ ∃ zS, !qqFvarDef zS iS ∧
    ∃ e₁, !adjoinDef e₁ z 0 ∧ ∃ s₁, !mkStepDef s₁ W 138 e₁ ∧
    ∃ e₂, !adjoinDef e₂ f0 0 ∧ ∃ s₂, !mkStepDef s₂ W 145 e₂ ∧
    ∃ e₃, !adjoinDef e₃ f0 e₁ ∧ ∃ s₃, !mkStepDef s₃ W 42 e₃ ∧
    ∃ e₄', !adjoinDef e₄' z e₂ ∧ ∃ e₄, !adjoinDef e₄ zS e₄' ∧ ∃ s₄, !mkStepDef s₄ W 43 e₄ ∧
    ∃ e₅', !adjoinDef e₅' zS e₁ ∧ ∃ e₅, !adjoinDef e₅ f0 e₅' ∧ ∃ s₅, !mkStepDef s₅ W 148 e₅ ∧
    ∃ e₆'', !adjoinDef e₆'' f2 0 ∧ ∃ e₆', !adjoinDef e₆' z e₆'' ∧ ∃ e₆, !adjoinDef e₆ zS e₆' ∧ ∃ s₆, !mkStepDef s₆ W 158 e₆ ∧
    ∃ l₆, !adjoinDef l₆ s₆ 0 ∧ ∃ l₅, !adjoinDef l₅ s₅ l₆ ∧ ∃ l₄, !adjoinDef l₄ s₄ l₅ ∧ ∃ l₃, !adjoinDef l₃ s₃ l₄ ∧
    ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧ !appendVDef y L l₁”

instance proShift0_defined : 𝚺₁-Function₂ (proShift0 : V → V → V) via proShift0Def := .mk fun v ↦ by
  simp [proShift0Def, proShift0, layoutSteps0_defined.iff, mkStep_defined.iff, cTV.defined.iff, cTV_zero,
    appendV_defined.iff, numeral_eq_natCast]
instance proShift0_definable : 𝚺₁-Function₂ (proShift0 : V → V → V) := proShift0_defined.to_definable

set_option maxHeartbeats 4000000 in
/-- **`proShift0` is applicable**: three eigenvariables; afterwards the child's `Layout0` at `1`, the parent's `Layout0` at
`i + 3`, and `setShiftFact &(i + 3 + 1) &2` (`nodeShift_ok`'s `hss`). -/
theorem proShift0_ok {tbl N W Wc T i E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (hWp : W = proPieces)
    (hΓ : IsFormulaSet LAct Γ) (hiE : i + 3 + 1 + 1 ≤ E) (hLay : Layout0 walkPieces Wc T Γ i) :
    ListOK tbl E ((8 : ℕ) : V) Γ (proShift0 W i) ∧ NoDrop' (proShift0 W i) ∧ shiftsV (proShift0 W i) = 3 ∧
    Layout0 walkPieces Wc T (finalCtx Γ (proShift0 W i)) 1 ∧
    Layout0 walkPieces Wc T (finalCtx Γ (proShift0 W i)) (i + 3) ∧
    neg LAct (setShiftFact (^&(i + 3 + 1)) (^&2)) ∈ finalCtx Γ (proShift0 W i) := by
  have hL := hP.layoutTable
  have hF2 := hP.frag2Table
  have e138 : ∀ ev : V, mkStep proPieces (138 : V) ev = mkStep frag2Pieces (138 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag2 138 (by decide) ev; simpa using this
  have e145 : ∀ ev : V, mkStep proPieces (145 : V) ev = mkStep frag2Pieces (145 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag2 145 (by decide) ev; simpa using this
  have e148 : ∀ ev : V, mkStep proPieces (148 : V) ev = mkStep frag2Pieces (148 : V) ev := fun ev ↦ by
    have := mkStep_pro_frag2 148 (by decide) ev; simpa using this
  have e42 : ∀ ev : V, mkStep proPieces (42 : V) ev = mkStep layoutPieces (42 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 42 (by decide) ev; simpa using this
  have e43 : ∀ ev : V, mkStep proPieces (43 : V) ev = mkStep layoutPieces (43 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 43 (by decide) ev; simpa using this
  have hE3 : (3 : V) ≤ E := le_trans le_add_self (le_trans le_self_add (le_trans le_self_add hiE))
  have hE2 : (2 : V) ≤ E := le_trans (by norm_num) hE3
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) hE2
  have h0 : IsSemiterm LAct (0 : V) (𝟎 : V) := isSemiterm_zeroV
  have h0E : termLen LAct (𝟎 : V) ≤ E := termLen_zeroV_le hE1
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hf0E : termLen LAct (^&0 : V) ≤ E := termLen_fvar0_le hE1
  have hf2 : IsSemiterm LAct 0 (^&2 : V) := by simp
  have hf2E : termLen LAct (^&2 : V) ≤ E := termLen_fvar_le' (by rw [show (2 : V) + 1 = 3 by norm_num]; exact hE3)
  have hfS : IsSemiterm LAct 0 (^&(i + 3 + 1) : V) := by simp
  have hfSE : termLen LAct (^&(i + 3 + 1) : V) ≤ E := termLen_fvar_le' hiE
  -- the child's layout
  obtain ⟨lok, lnd, lsh, _, lLay⟩ := layoutSteps0_ok htbl hP hWp hΓ hE2
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ (layoutSteps0 W) := ⟨_, rfl⟩
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 8 htbl hΓ lok
  have hLay₁ : Layout0 walkPieces Wc T Γ₁ (i + 2) := by rw [hΓ₁]; have := hLay.transport lnd; rwa [lsh] at this
  have lLay₁ : Layout0 walkPieces Wc T Γ₁ 0 := by rw [hΓ₁]; exact lLay
  -- step 1: `setShiftTotal [𝟎]`
  obtain ⟨ok₁, tg₁, cx₁⟩ := gok_setShiftTotal htbl hF2 rfl hΓ₁f h0 h0E
  rw [← e138, ← hWp] at ok₁ tg₁ cx₁
  rw [Nat.cast_zero, termShift_zeroV] at cx₁
  have h1nd : NoDrop' (?[mkStep W 138 ?[(𝟎 : V)]] : V) := noDrop'_single (Or.inr (Or.inr (Or.inl tg₁)))
  have h1sh : shiftsV (?[mkStep W 138 ?[(𝟎 : V)]] : V) = 1 := shiftsV_single_tag2 tg₁
  obtain ⟨Γ₂, hΓ₂⟩ : ∃ Γ', Γ' = insert (neg LAct (setShiftFact (^&0) (𝟎 : V))) (setShift LAct Γ₁) := ⟨_, rfl⟩
  have hΓ₂e : Γ₂ = finalCtx Γ₁ ?[mkStep W 138 ?[(𝟎 : V)]] := by rw [hΓ₂, finalCtx_single, cx₁]
  have hΓ₂f : IsFormulaSet LAct Γ₂ := by rw [hΓ₂e]; exact finalCtx_isFormulaSet 8 htbl hΓ₁f (listOK_single ok₁)
  have hLay₂ : Layout0 walkPieces Wc T Γ₂ (i + 3) := by
    rw [hΓ₂e]; have := hLay₁.transport h1nd; rwa [h1sh, add_assoc, show (2 : V) + 1 = 3 by norm_num] at this
  have lLay₂ : Layout0 walkPieces Wc T Γ₂ 1 := by
    rw [hΓ₂e]; have := lLay₁.transport h1nd; rwa [h1sh, zero_add] at this
  have hss₂ : neg LAct (setShiftFact (^&0) (𝟎 : V)) ∈ Γ₂ := by rw [hΓ₂]; exact memInsSelf _ _
  have hS₂ : neg LAct (eqFactB (^&(i + 3 + 1)) (𝟎 : V)) ∈ Γ₂ := hLay₂.2
  have hs''₂ : neg LAct (eqFactB (^&2) (𝟎 : V)) ∈ Γ₂ := by have := lLay₂.2; rwa [one_add_one_eq_two] at this
  -- step 2: `setShiftEmpty [&0]` → `eqFactB &0 𝟎`
  obtain ⟨ok₂, tg₂, cx₂⟩ := gok_setShiftEmpty htbl hF2 rfl hΓ₂f hf0 hf0E hss₂
  rw [← e145, ← hWp] at ok₂ tg₂ cx₂
  have hΓ₃f : IsFormulaSet LAct (insert (neg LAct (eqFactB (^&0) (𝟎 : V))) Γ₂) := by rw [← cx₂]; exact isFormulaSet_ctxAfter 8 htbl ok₂
  -- step 3: `eqSymm [&0, 𝟎]` → `eqFactB 𝟎 &0`
  obtain ⟨ok₃, tg₃, cx₃⟩ := lok_eqSymm htbl hL rfl hΓ₃f hf0 hf0E h0 h0E (memInsSelf _ _)
  rw [← e42, ← hWp] at ok₃ tg₃ cx₃
  have hΓ₄f : IsFormulaSet LAct (insert (neg LAct (eqFactB (𝟎 : V) (^&0))) (insert (neg LAct (eqFactB (^&0) (𝟎 : V))) Γ₂)) := by
    rw [← cx₃]; exact isFormulaSet_ctxAfter 8 htbl ok₃
  -- step 4: `eqTrans [S, 𝟎, &0]` → `eqFactB S &0`
  obtain ⟨ok₄, tg₄, cx₄⟩ := lok_eqTrans htbl hL rfl hΓ₄f hfS hfSE h0 h0E hf0 hf0E (memIns (memIns hS₂)) (memInsSelf _ _)
  rw [← e43, ← hWp] at ok₄ tg₄ cx₄
  have hΓ₅f : IsFormulaSet LAct (insert (neg LAct (eqFactB (^&(i + 3 + 1)) (^&0))) (insert (neg LAct (eqFactB (𝟎 : V) (^&0)))
      (insert (neg LAct (eqFactB (^&0) (𝟎 : V))) Γ₂))) := by
    rw [← cx₄]; exact isFormulaSet_ctxAfter 8 htbl ok₄
  -- step 5: `congSetShiftL [&0, S, 𝟎]` → `setShiftFact S 𝟎`
  obtain ⟨ok₅, tg₅, cx₅⟩ := gok_congSetShiftL htbl hF2 rfl hΓ₅f hf0 hf0E hfS hfSE h0 h0E (memInsSelf _ _)
    (memIns (memIns (memIns hss₂)))
  rw [← e148, ← hWp] at ok₅ tg₅ cx₅
  have hΓ₆f : IsFormulaSet LAct (insert (neg LAct (setShiftFact (^&(i + 3 + 1)) (𝟎 : V))) (insert (neg LAct (eqFactB (^&(i + 3 + 1)) (^&0)))
      (insert (neg LAct (eqFactB (𝟎 : V) (^&0))) (insert (neg LAct (eqFactB (^&0) (𝟎 : V))) Γ₂)))) := by
    rw [← cx₅]; exact isFormulaSet_ctxAfter 8 htbl ok₅
  -- step 6: `congSetShiftR [S, 𝟎, &2]` → `setShiftFact S &2`
  obtain ⟨hlen, hrow⟩ := hP.congSetShiftR
  obtain ⟨ok₆, tg₆, cx₆⟩ := pok_congSetShiftR htbl hWp hlen hrow hΓ₆f hfS hfSE h0 h0E hf2 hf2E
    (memIns (memIns (memIns (memIns hs''₂)))) (memInsSelf _ _)
  -- assembly
  have hnd : NoDrop' (mkStep W 138 ?[(𝟎 : V)] ∷ mkStep W 145 ?[^&0] ∷ mkStep W 42 ?[^&0, (𝟎 : V)] ∷
      mkStep W 43 ?[^&(i + 3 + 1), (𝟎 : V), ^&0] ∷ mkStep W 148 ?[^&0, ^&(i + 3 + 1), (𝟎 : V)] ∷
      mkStep W 158 ?[^&(i + 3 + 1), (𝟎 : V), ^&2] ∷ (0 : V)) :=
    noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp) (noDrop'_cons (by rw [tg₃]; simp)
      (noDrop'_cons (by rw [tg₄]; simp) (noDrop'_cons (by rw [tg₅]; simp) (noDrop'_single (by rw [tg₆]; simp))))))
  have hsh : shiftsV (mkStep W 138 ?[(𝟎 : V)] ∷ mkStep W 145 ?[^&0] ∷ mkStep W 42 ?[^&0, (𝟎 : V)] ∷
      mkStep W 43 ?[^&(i + 3 + 1), (𝟎 : V), ^&0] ∷ mkStep W 148 ?[^&0, ^&(i + 3 + 1), (𝟎 : V)] ∷
      mkStep W 158 ?[^&(i + 3 + 1), (𝟎 : V), ^&2] ∷ (0 : V)) = 1 := by
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₃, tg₄, tg₅, tg₆]
    simp
  have hfin : finalCtx Γ₁ (mkStep W 138 ?[(𝟎 : V)] ∷ mkStep W 145 ?[^&0] ∷ mkStep W 42 ?[^&0, (𝟎 : V)] ∷
      mkStep W 43 ?[^&(i + 3 + 1), (𝟎 : V), ^&0] ∷ mkStep W 148 ?[^&0, ^&(i + 3 + 1), (𝟎 : V)] ∷
      mkStep W 158 ?[^&(i + 3 + 1), (𝟎 : V), ^&2] ∷ (0 : V)) =
      insert (neg LAct (setShiftFact (^&(i + 3 + 1)) (^&2))) (insert (neg LAct (setShiftFact (^&(i + 3 + 1)) (𝟎 : V)))
        (insert (neg LAct (eqFactB (^&(i + 3 + 1)) (^&0))) (insert (neg LAct (eqFactB (𝟎 : V) (^&0)))
          (insert (neg LAct (eqFactB (^&0) (𝟎 : V))) Γ₂)))) := by
    rw [finalCtx_cons, cx₁, ← hΓ₂, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_cons, cx₄, finalCtx_cons, cx₅,
      finalCtx_single, cx₆]
  have tr : ∀ x ∈ Γ₂, x ∈ insert (neg LAct (setShiftFact (^&(i + 3 + 1)) (^&2))) (insert (neg LAct (setShiftFact (^&(i + 3 + 1)) (𝟎 : V)))
        (insert (neg LAct (eqFactB (^&(i + 3 + 1)) (^&0))) (insert (neg LAct (eqFactB (𝟎 : V) (^&0)))
          (insert (neg LAct (eqFactB (^&0) (𝟎 : V))) Γ₂)))) := fun x hx ↦ memIns (memIns (memIns (memIns (memIns hx))))
  unfold proShift0
  refine ⟨listOK_appendV lok ?_, noDrop'_appendV lnd hnd, ?_, ?_, ?_, ?_⟩
  · rw [← hΓ₁]
    refine listOK_cons ok₁ ?_
    rw [cx₁, ← hΓ₂]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    refine listOK_cons ok₄ ?_
    rw [cx₄]
    refine listOK_cons ok₅ ?_
    rw [cx₅]
    exact listOK_single ok₆
  · rw [shiftsV_appendV, lsh, hsh]; norm_num
  · rw [finalCtx_appendV, ← hΓ₁, hfin]
    exact lLay₂.mono tr
  · rw [finalCtx_appendV, ← hΓ₁, hfin]
    exact hLay₂.mono tr
  · rw [finalCtx_appendV, ← hΓ₁, hfin]; exact memInsSelf _ _

end emptySequent

/-! ## 8. What remains (2026-09-15, evening) — recorded precisely

DELIVERED since the morning entry: §9 `proOr`/`proOr_ok` (two `proIns` + `congInsertS`); §10 `proShift`/`proShift_ok`
(`proShiftPre_ok` + `shTail2_ok`, with `loopS_ok`/`loopI_ok`/`uSub_ok`/`loopM_ok`); §11 the size classes `layQ`/`layD`
(`sum2Q`/`sum2D` for the fold's closed lemmas) with `sizeOK_layoutSteps` (STANDALONE: `hornOnly_chainSteps` by the rows,
`sizeOK_lenFoldAux` by the packed induction) and the per-tag `sizeOK_pro<Tag>`/`costSum_pro<Tag>_le` for `axL`, `postIns`,
`proIns`, `proCutPre`, `proWk`, `proOr`, `proShift`, all in the `costSum_le_of_sizeOK 8` shape
`len · (costK N E B 8 Q D + 35 · (ctxBoundG (growK B E Q) Γ len + (fvOccS Γ + len · growK B E Q)))`; the rows 156–158
(`setLenEmptyLe`, `congSubsetL`, `congSetShiftR`) for the empty sequent (§12 `Layout0`/`layoutSteps0` drafted).

* **The EMPTY sequent — DECISION: the `k = 0` case, not an invariant.** `Derivation` (Foundation `Proof/Basic.lean`)
  admits `wkRule s d'` with `fstIdx d' ⊆ s` and `shiftRule s d'` with `s = setShift (fstIdx d')`, so in a model of
  `¬Con(TAct)` (which `𝗜𝚺₁` cannot exclude) a derivation of `∅` exists and the empty sequent occurs as the child of `wk`,
  as both sides of `shift`, and as the PARENT of `cut` (its children `insert p ∅` are nonempty; leaves and the
  `and/or/all/exs` children are inserts, never empty). "Every node's sequent is nonempty" is FALSE. The honest
  treatment: `Layout0 Γ i := Layout … 0 i ∧ eqFactB &(i + 1) 𝟎` (§12; the object identified with `𝟎` replaces the
  chain), built by `layoutSteps0` (rows `eqTotal`, `setLenTotalC`, `eqSymm`, `congSetLenR`, `setLenEmptyLe`; 2
  eigenvariables; `layoutSteps0_ok`). DELIVERED on top of it (§12): `proWk0_ok` (child `∅`: `layoutSteps0 ++
  emptySubsetC [S] ++ congSubsetL [𝟎, &1, S]` → `subsetFact &1 S`) and `proShift0_ok` (both `∅`: `layoutSteps0 ++
  setShiftTotal [𝟎] ++ setShiftEmpty ++ eqSymm ++ eqTrans [S, 𝟎, &0] ++ congSetShiftL ++ congSetShiftR [S, 𝟎, &2]` →
  `setShiftFact S &2`). STILL TO WRITE: `proIns0` (parent `∅`, child `insert p ∅`: `identIns` WITHOUT Loop B and the
  parent `subChain` — direction `S ⊆ s''` from `emptySubsetC [s'']` + `congSubsetL [𝟎, S, s'']`, then `insertSubset`,
  `subsetAntisymm`), the costs of `layoutSteps0`/`proWk0`/`proShift0` (all Horn-only or tag-2 — `sizeOK_of_hornOnly` after
  a tag census), and the verify recursion must carry `Layout0` for `∅`-nodes (a per-node disjunction
  `1 ≤ k ∧ Layout … ∨ k = 0 ∧ Layout0 …`).
* **`all` (§4.5)**: every producer exists (`certFree_ok`, `certShift_ok`, `setShiftTotal`, `insertTotalC`). Plan on this
  file's producers: parent `s` at `i` with `∀p ∈ s` (`dossF_all` → `p`'s dossier at `n = 1`); child `c = insert (free p)
  (setShift s)` laid out by `layoutSteps c`; a fresh walk `describeF walkPieces 1 (shift p)`; `certFree` (cap 9 —
  `ListOK.mono` to lift the rest) → `freeFact FP P` with `FP` the child's dossier of `free p`; `setShiftTotal [S]` → `ss`
  with `setShiftFact ss S` (the `nodeAll_ok` `hsh`, no identification); `insertTotalC [FP, ss]` → `c'` with `insFact c'
  FP ss` (`hins`); the identification `eqFactB c' s''`: (a) `s'' ⊆ c'` by a Loop-A variant with the case split
  `y_j = free p` (`memInsertSelfC`) / `y_j = shift x` (`certShift` between the parent's `X` and the child's `Y_j`,
  `shiftMemSetShift [S, X, ss, Y_j]`, `memInsertOfMem`) — needs a Σ₁ "unshift index" (`idxAux` with the test
  `shift xs.[m] = t`); (b) `c' ⊆ s''` by the `u` chain of §10 in the PARENT's order (objects = the child's dossiers of
  the shifts), `setShiftInsert` up the chain → `setShiftFact u_0 S`, `setShiftFun [ss, S, u_0]` → `eqFactB ss u_0`,
  `insertSubset` up `u` against `s''` → `subsetFact u_0 s''`, `congInsertS` (`insFact c' FP u_0`), `insertSubset` →
  `subsetFact c' s''`; then `subsetAntisymm`, `postIns` for `hfst`. BLOCKER TO CLEAR FIRST: `certFree_ok`'s caps
  `SubFPre E Q 1 0 fvec (shift p) …` and `hL` need bounds on `listSum (termLenVec (1 + e) (qVecIterV fvec e))`
  (`= e + 1`, no lemma yet) and on `len (π₂ (qWalkP Wd e (1 + e) (qVecIterV fvec e)))` (no lemma yet) — a small
  `qVec` theory in `Cert`'s vocabulary, not this file's.
* **`exs` (§4.6)**: `describeT t` + the term `lenSteps` (`tPiFact`/`tlenFact`), `certSubst` at the singleton vector
  `?[t]` (its `SubFPre` needs the same `qVecIterV` bounds as `all`) + `substsSubsts1` → `substs1Fact PT T P`, then
  `proIns`/`postIns` for `insert (substs1 t p) s` — routine once the `qVec` bounds exist.
* **The splice**: `fragAxL_ok`/`node<Tag>_ok` are stated at `W = frag1Pieces`/`frag2Pieces`, the prologues at
  `proPieces`; the verify list reads fragment steps through `mkStep_pro_frag1`/`mkStep_pro_frag2` — bookkeeping.
* **`len` bounds of the loops** (`identIns`, `loopW`, `loopS/I/M`, `uSub`): not stated; `costSum_pro<Tag>_le` keeps
  `len (pro…)` symbolic. Each loop is `≤ m · (2·eqCount + 3)`-shaped; `len_eqSteps` is not exported by `Layout`.
* **Tables**: rows 155–158 in `PrologueRows.lean` (`proExtraRowCount = 4`); `certShiftN` moved with it (symbolic).

TRAPS (this session): `set Γ := finalCtx …` with MANY hypotheses in scope makes `kabstract` run `isDefEq` on every other
`finalCtx` application, which unfolds `finalCtx` — a whole-declaration `whnf` timeout at 4M heartbeats that no bisection
attributes to a line (the 40M run did not finish in an hour). Use `obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = finalCtx … := ⟨_, rfl⟩`
(an OPAQUE name) and prove facts about `Γ'` by `rw [hΓ']` on the goal. Likewise never `set k := len (memberList s)`
in a proof that instantiates lemmas stated with `len (memberList s)`: the defeq check `k =?= len (memberList s)` inside
a big unification is what times out — write the terms out. A loop's frame equation must take the shift `σ` as a
VARIABLE (`loopS_ok`'s first version hard-coded `proSig walkPieces layoutPieces …`, unprovable by `rfl` under
`hWl : Wl = layoutPieces`). `hornOnly_single`'s goal already has the `?[s]` unfolded — no `unfold blockI` before the
tag rewrite. `norm_num` cannot prove `6 * D + 1 + 1 ≤ 6 * D + 2` (V-arithmetic with a variable): `calc` with `ring`
equalities. A row not in any piece table (`congSubsetL`, `congSetShiftR`) is added to `PrologueRows` by the generator's
`EXISTING_ROWS` (table entries only; the `Lib`/`inst_` blocks stay in `Lib/Frag`/`RowInstB`). -/

end ArithS
