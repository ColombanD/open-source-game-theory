import ArithS.Necessitation.Pin
import ArithS.Necessitation.ProAxmRows

/-!
# ArithS.Necessitation.ProAxm — the `axm` prologue: `axchFact &ip` from the member's dossier

`DESIGN_fragments.md` §4.10, `Frag2.lean`'s ONE deliberate weakening: `nodeAxm_ok` takes the recognizer fact
`neg (axchFact (^&ip)) ∈ Γ` ("`p` is a `TAct`-axiom", `Paxch` = the code of `(Theory.Δ₁ch TAct).sigma`) as a
LAYOUT HYPOTHESIS. This file produces it, for the member `p` of the sequent whose dossier the layout holds at
`&ip = &(memTop s p i)`, from `Theory.Δ₁ch TAct p` (the axiom check of the derivation being verified).

## The two cases (the `V`-level case split is a THEOREM here: `mem_TAct_class_cases`, §1)

An axiom code `p ∈ TAct.Δ₁Class` is EITHER
* **(i)** `p = ⌜σ⌝` for one of the finitely many STANDARD non-schema axioms σ (`StdAxiom σ`: the four action
  sentences `axAct, axAct', axNe, axNe'` and every `𝗣𝗔⁻` axiom embedded along `emb` — `𝗣𝗔⁻` is finite,
  `PeanoMinus.finite`, its `Δ₁ch` is `Theory.Δ₁.ofFinite` = a disjunction of `x = ↑(encode σ)`, read off in
  `eval_ofList_ch`), OR
* **(ii)** an INDUCTION INSTANCE: `IsSemiformula ℒₒᵣ 0 p ∧ InductionR (fun _ ↦ True) p` (Foundation's `chUniv`
  recognizer: `p = qqAlls b m`, `b` closed, `bv b = m`, `subst (fvarVec m) b = indBodyVal K`), possibly NONSTANDARD.

## What is delivered

**Case (i) is FULLY discharged, per model, on NumId's route** (`numId_sentence σ`: the dossier of the STANDARD
code `⌜σ⌝` at `&ip` yields `eqFact &ip (numeral ⌜σ⌝)`, shift-free, with a per-σ standard constant), closed by
ONE `sLemma` — the closed `Lib` fact `axchNum ⌜σ⌝ = axchFact (numeral ⌜σ⌝)` ("the numeral of σ is an axiom
code", TRUE in every model by `Δ₁Class.mem_iff` since `σ ∈ TAct`) — and ONE Horn step at the NEW row `congAxch`
(`ProAxmRows.lean`: `!axch x → y = x → !axch y`, one row for EVERY σ; `Lib/Nodes.lean`'s `axiomRec σ` would need
one row per σ). Per standard axiom: `axmStd_ok` (at a dossier), `proAxmStd_ok` (at the `Layout`); UNIFORMLY over
`StdAxiom` with ONE constant by finiteness: `proAxm_std`. The cost is `NumInv`'s (`costSum_proAxmStd_le`,
`numInv_cost`'s shape). The table: `ProAxmTable` (`proAxmRows := numIdRows ++ [congAxch]`,
`exists_proAxmTableB`).

**Case (ii) is NOT discharged** — it is the explicitly named hypothesis `AxmIndOracle` (§5), and `proAxm_ok`
assembles both cases from the `V`-level split. What (ii) needs (all of it lemma-writing on existing rows, none
of it a wall): the `Lib/Frag.lean` §J rows `qqAllsZero/Succ`, `bv*`, `termBV*`, `listMax*`, `fvarVecTotal/Nth`,
the `max`/`−` glue — NONE of them is in any TABLE yet (no `inst_`/`nok_` blocks: `RowInstB` has no `qqAlls`,
`bv`, `fvarVec` row), a Σ₁ producer walking `p = qqAlls b m` down to `b` (`m` × `qqAllsSucc` from the dossier's
`allFact`s), `describeF`/`certShift`/`eqSteps` for `shift b = b`, a bottom-up `bv` pass over `b`'s dossier
(`bvGraph LAct`), `describeF W 0 (subst (fvarVec m) b)` + `certSubst` (Cert §6.7) for `substsGraph`, `totIndBody`
+ `indBodyValGraph` matching, and — the real obstacle — the ℒₒᵣ↔`LAct` BRIDGE: `indRec` (`Lib/Nodes.lean`) is
stated over the `ℒₒᵣ`-graphs (`(isUFormula ℒₒᵣ).pi`, `shiftGraph ℒₒᵣ`, `bvGraph ℒₒᵣ`, `substsGraph ℒₒᵣ`) while every
walked fact is an `LAct`-fact; the restriction rows (`Lib/Bridge.lean`'s closing docstring) exist as `Lib`
sentences for `isUFormula`/`shift`/`subst` but NOT for `bv`, and none is a table row. Estimated at Cert-scale
(a `Fixpoint` producer + its `_ok`), far beyond this file's budget.

## THE Σ₁ QUESTION (an honest weakening, stated once)

`proAxm` is NOT a Σ₁ function of the indices, and cannot be on NumId's route: NumId's lists carry `sLemma A dA`
steps whose derivations `dA` are PER-MODEL (`Lib.code`: `∃ d` in every model, not the cast of a standard
derivation) and whose witnesses depend on the eigenvariable `ip`; the closed-fact derivations live in no TABLE.
So case (i) is delivered as `∃ P` per model (exactly `Pin.pin_assembly`'s shape — the pin has the same
character, and `PinKit'` is stated that way). For `Verify`'s §3.6 clause edit this means the `axm` clause cannot
be `∃ pro, !proAxmDef pro …`; the two sound options are recorded in the closing docstring (§8): (A) a per-σ
GENERATED Σ₁ template on table rows (the design's `pinSteps σ`: closed-fact rows per σ-node, `O(|σ|)` each — a
re-run of NumId's meta-induction over rows instead of `sLemma`s), or (B) an `axm` clause `∃ pro ≤ L, AxmPro …`
with a Δ₁ check at the CANONICAL dossier context `finalCtx 0 (describeF …)` plus the context-monotonicity of
shift-free Horn/lemma lists — `listOK_mono_ctx` (§7) is proved here for that purpose.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open PeanoMinus ISigma0 ISigma1
open LAct

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

/-! ## 0. The `axm` table: the pin's rows, then `congAxch` -/

section proAxmTable

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The `axm` table: `proAxmRowCount` rows at least, the `i`-th with the arity and matrix of `proAxmRows[i]`. -/
def ProAxmTable (tbl : V) : Prop :=
  (proAxmRowCount : V) ≤ len tbl ∧
  ∀ (i : ℕ) (h : i < proAxmRows.length),
    rowM tbl.[(i : V)] = ((proAxmRows[i]).m : V) ∧ rowB tbl.[(i : V)] = ⌜Semiformula.lMap emb (proAxmRows[i]).B⌝

lemma ProAxmTable.numIdTable {tbl : V} (h : ProAxmTable tbl) : NumIdTable tbl := by
  refine ⟨le_trans (by exact_mod_cast (show numIdRowCount ≤ proAxmRowCount by simp only [proAxmRowCount]; omega)) h.1, ?_⟩
  intro i hi
  have hi' : i < proAxmRows.length := by
    rw [proAxmRows_length]; rw [numIdRows_length] at hi; simp only [proAxmRowCount]; omega
  have := h.2 i hi'
  rwa [show proAxmRows[i] = numIdRows[i] from List.getElem_append_left hi] at this

lemma ProAxmTable.proTable {tbl : V} (h : ProAxmTable tbl) : ProTable tbl := h.numIdTable.proTable
lemma ProAxmTable.layoutTable {tbl : V} (h : ProAxmTable tbl) : LayoutTable tbl := h.proTable.layoutTable
lemma ProAxmTable.walkTable {tbl : V} (h : ProAxmTable tbl) : WalkTable tbl := h.proTable.walkTable

/-- The reading of the `k`-th extra row (what `aok_<row>` takes). -/
lemma ProAxmTable.extra {tbl : V} (h : ProAxmTable tbl) (k : ℕ) (hk : k < proAxmExtraRowCount) :
    ((numIdRowCount + k : ℕ) : V) < len tbl ∧
    rowM tbl.[((numIdRowCount + k : ℕ) : V)] = ((proAxmExtraRows[k]'(by rw [proAxmExtraRows_length]; exact hk)).m : V) ∧
    rowB tbl.[((numIdRowCount + k : ℕ) : V)] =
      ⌜Semiformula.lMap emb (proAxmExtraRows[k]'(by rw [proAxmExtraRows_length]; exact hk)).B⌝ := by
  have hlt : numIdRowCount + k < proAxmRows.length := by rw [proAxmRows_length]; simp only [proAxmRowCount]; omega
  have hr := h.2 (numIdRowCount + k) hlt
  have hk' : k < proAxmExtraRows.length := by rw [proAxmExtraRows_length]; exact hk
  have e' : proAxmRows[numIdRowCount + k]? = proAxmExtraRows[k]? := by
    unfold proAxmRows
    rw [List.getElem?_append_right (by rw [numIdRows_length]; omega), numIdRows_length, Nat.add_sub_cancel_left]
  have e : proAxmRows[numIdRowCount + k]'hlt = proAxmExtraRows[k]'hk' := by
    rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hk'] at e'
    exact Option.some.inj e'
  rw [e] at hr
  exact ⟨lt_of_lt_of_le (by exact_mod_cast hlt) (proAxmRows_length ▸ h.1), hr.1, hr.2⟩

lemma ProAxmTable.congAxch {tbl : V} (h : ProAxmTable tbl) :
    ((aIdx_congAxch : ℕ) : V) < len tbl ∧
    rowM tbl.[((aIdx_congAxch : ℕ) : V)] = ((2 : ℕ) : V) ∧
    rowB tbl.[((aIdx_congAxch : ℕ) : V)] = impChainV LAct (vecOf row_congAxch_as) row_congAxch_c := by
  have := h.extra 0 (by decide)
  have e : ((aIdx_congAxch : ℕ) : V) = ((numIdRowCount + 0 : ℕ) : V) := rfl
  rw [e]
  refine ⟨this.1, this.2.1, ?_⟩
  rw [impChainV_vecOf, this.2.2]
  exact quote_row_congAxch

end proAxmTable

/-- **A sound `axm` table exists in every model**, with one standard length bound and a row-body bound
(the `Pin.exists_numIdTableB` shape, so `KitPackage'` can run every kit at ONE table). -/
theorem exists_proAxmTableB : ∃ N B : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∃ tbl : V, TableOK tbl (N : V) ∧ ProAxmTable tbl ∧ ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ (B : V) := by
  obtain ⟨N, hN⟩ := exists_rows proAxmRows
  refine ⟨N, rowsB proAxmRows, fun V _ _ ↦ ?_⟩
  obtain ⟨rows, hlen, hok, hidx⟩ := hN V
  refine ⟨vecOf rows, tableOK_vecOf rows hok, ⟨?_, ?_⟩, ?_⟩
  · rw [len_vecOf, hlen, proAxmRows_length]
  · intro i h
    have h' : i < rows.length := by rw [hlen]; exact h
    rw [nth_vecOf rows i h']
    exact hidx i h h'
  · intro j hj
    rw [len_vecOf] at hj
    obtain ⟨i, rfl⟩ := eq_nat_of_lt_nat hj
    have h' : i < rows.length := by exact_mod_cast hj
    have h'' : i < proAxmRows.length := by rw [← hlen]; exact h'
    rw [nth_vecOf rows i h', (hidx i h'' h').2, flN_pred]
    exact_mod_cast flN_le_rowsB proAxmRows i h''

/-! ## 1. The `V`-level case split of `Theory.Δ₁ch TAct` (a theorem, never `simp` on a closed quote) -/

section caseSplit

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The recognizer of a singleton theory `{φ}` accepts exactly the code of `φ` (stated for a VARIABLE `φ` over a
VARIABLE language — `axNe'` is a `Sentence LAct`, `𝗣𝗔⁻`'s axioms are `Sentence ℒₒᵣ`, and a `rw` across the two
languages whnf's the closed code; `encode` never appears in a statement for the same reason). -/
lemma eval_singleton_ch {L : Language} [L.Encodable] [L.LORDefinable] (φ : Sentence L) (p : V) :
    V ⊧/![p] (Theory.Δ₁.singleton φ).ch.val ↔ p = (⌜φ⌝ : V) := by
  rw [Sentence.quote_eq_encode]
  simp [Theory.Δ₁.singleton, numeral_eq_natCast]

/-- The recognizer of `Theory.Δ₁.ofList l` accepts exactly the codes of the listed sentences (`simp` does not
rewrite inside INSTANCE arguments — the unfolding of `ofList`/`ofEq`/`add` is done by `change`). -/
lemma eval_ofList_ch : ∀ (l : List (Sentence ℒₒᵣ)) (p : V),
    V ⊧/![p] (Theory.Δ₁.ofList l).ch.val ↔ ∃ σ ∈ l, p = (⌜σ⌝ : V)
  | [], p => by
    change V ⊧/![p] (⊥ : 𝚫₁.Semisentence 1).val ↔ _
    simp
  | φ :: l, p => by
    have ih := eval_ofList_ch l p
    change V ⊧/![p] ((Theory.Δ₁.singleton φ).ch ⋎ (Theory.Δ₁.ofList l).ch).val ↔ _
    rw [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
      eval_singleton_ch, ih]
    simp only [List.mem_cons, exists_eq_or_imp]

/-- `𝗣𝗔⁻`'s recognizer (`PeanoMinus.delta1 = Theory.Δ₁.ofFinite _ PeanoMinus.finite`) accepts exactly the
codes of its finitely many axioms. -/
lemma eval_paMinus_ch (p : V) :
    V ⊧/![p] PeanoMinus.delta1.ch.val ↔ ∃ σ ∈ 𝗣𝗔⁻, p = (⌜σ⌝ : V) := by
  have e : PeanoMinus.delta1.ch = (Theory.Δ₁.ofList PeanoMinus.finite.toFinset.toList).ch := rfl
  rw [e, eval_ofList_ch]
  simp only [Finset.mem_toList, Set.Finite.mem_toFinset]

/-- **The standard non-schema axioms of `TAct`**: the four action sentences and every `𝗣𝗔⁻` axiom along `emb`. -/
def StdAxiom (σ : Sentence LAct) : Prop :=
  σ = axAct ∨ σ = axAct' ∨ σ = axNe ∨ σ = axNe' ∨ ∃ σ₀ ∈ 𝗣𝗔⁻, Semiformula.lMap emb σ₀ = σ

lemma StdAxiom.mem_TAct {σ : Sentence LAct} (h : StdAxiom σ) : σ ∈ TAct := by
  rcases h with rfl | rfl | rfl | rfl | ⟨σ₀, h₀, rfl⟩
  · exact axAct_mem_TAct
  · exact axAct'_mem_TAct
  · exact axNe_mem_TAct
  · exact axNe'_mem_TAct
  · exact lMap_emb_mem_TAct (Set.mem_union_left _ h₀)

/-- The standard axioms form a FINITE set. -/
lemma stdAxiom_finite : Set.Finite {σ : Sentence LAct | StdAxiom σ} := by
  have e : {σ : Sentence LAct | StdAxiom σ} =
      insert axAct (insert axAct' (insert axNe (insert axNe' ((fun σ₀ ↦ Semiformula.lMap emb σ₀) '' 𝗣𝗔⁻)))) := by
    ext σ; simp [StdAxiom, Set.mem_image]
  rw [e]
  exact (((PeanoMinus.finite.image _).insert _).insert _).insert _ |>.insert _

/-- **THE CASE SPLIT.** A `TAct`-axiom code is the code of a standard axiom (case (i)) or an induction instance
(case (ii)). -/
theorem mem_TAct_class_cases {p : V} (h : p ∈ TAct.Δ₁Class) :
    (∃ σ : Sentence LAct, StdAxiom σ ∧ p = (⌜σ⌝ : V)) ∨
    (IsSemiformula ℒₒᵣ 0 p ∧ InductionR (fun _ ↦ True) p) := by
  rw [mem_TAct_class_iff, tact_ch_eq, pa_ch_eq] at h
  simp only [HierarchySymbol.Semiformula.val_or, HierarchySymbol.Semiformula.val_and,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.or_eq, LogicalConnective.Prop.and_eq] at h
  rcases h with ((((⟨hF, hpa | hind⟩ | hNe') | hNe) | hAct') | hAct)
  · rw [eval_paMinus_ch] at hpa
    obtain ⟨σ₀, h₀, rfl⟩ := hpa
    exact Or.inl ⟨Semiformula.lMap emb σ₀, Or.inr (Or.inr (Or.inr (Or.inr ⟨σ₀, h₀, rfl⟩))),
      (quote_sentence_lMap_emb σ₀).symm⟩
  · have hI : InductionR (fun _ ↦ True) p := by
      simpa [HierarchySymbol.Defined.iff] using hind
    exact Or.inr ⟨(eval_isFormulaOR' p).mp hF, hI⟩
  · rw [eval_singleton_ch] at hNe'
    exact Or.inl ⟨axNe', Or.inr (Or.inr (Or.inr (Or.inl rfl))), hNe'⟩
  · rw [eval_singleton_ch] at hNe
    exact Or.inl ⟨axNe, Or.inr (Or.inr (Or.inl rfl)), hNe⟩
  · rw [eval_singleton_ch] at hAct'
    exact Or.inl ⟨axAct', Or.inr (Or.inl rfl), hAct'⟩
  · rw [eval_singleton_ch] at hAct
    exact Or.inl ⟨axAct, Or.inl rfl, hAct⟩

end caseSplit

/-! ## 2. The closed fact `axchFact (numeral ⌜σ⌝)` — a `Lib` sentence for every `σ ∈ TAct` -/

section closedFact

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `(Theory.Δ₁ch TAct).sigma ⇜ ![↑c]`: "the numeral `c` is a `TAct`-axiom code". -/
noncomputable def axchNum (c : ℕ) : ArithmeticSentence :=
  cfact (↑(Theory.Δ₁ch TAct).sigma : ArithmeticSemisentence 1) ![↑c]

/-- For `σ ∈ TAct` the closed fact at `⌜σ⌝` is TRUE in every model (`Δ₁Class.mem_iff'`), hence `Lib`. -/
theorem lib_axchNum {σ : Sentence LAct} (h : σ ∈ TAct) : Lib (axchNum ⌜σ⌝) :=
  Lib.of_models fun V _ _ ↦ (models_cfact _ _).mpr (by
    have e : (fun i : Fin 1 ↦ Semiterm.valb (M := V) ![] ((![(↑(⌜σ⌝ : ℕ) : ClosedSemiterm ℒₒᵣ 0)] : Fin 1 → ClosedSemiterm ℒₒᵣ 0) i)) =
        ![(⌜σ⌝ : V)] := by
      funext i; fin_cases i; simp [natT_val, Sentence.coe_quote_eq_quote]
    rw [e]
    change V ⊧/![(⌜σ⌝ : V)] (Theory.Δ₁ch TAct).sigma.val
    rw [HierarchySymbol.Semiformula.val_sigma]
    exact Δ₁Class.mem_iff'.mpr h)

/-- The code of the closed fact is the `axch` fact at the numeral. -/
lemma code_axchNum (c : ℕ) :
    (⌜Semiformula.lMap emb (axchNum c)⌝ : V) = axchFact (numeral (c : V)) := by
  rw [axchNum, quote_cfact, matrixToVec_fin1]
  change subst LAct (listToVec [(⌜(↑c : ClosedSemiterm ℒₒᵣ 0)⌝ : V)]) _ = _
  rw [quote_natT]
  rfl

end closedFact

/-! ## 3. Case (i) at a dossier: `numId_sentence σ`, the closed fact, one `congAxch` step -/

section stdCase

/-- **`axchFact &i` from the dossier of a standard axiom code.** For every `σ ∈ TAct` (a Lean-level sentence —
the meta induction of `NumId` needs nothing else) there is a standard constant `C` such that, in every model,
from the walk dossier of `⌜σ⌝` at `&i` a shift-free list applicable at cap `9` under `C + i ≤ E`, of length
`≤ C`, `SizeOK C C`, leaves `axchFact (^&i)`. -/
theorem axmStd_ok (σ : Sentence LAct) (hσ : σ ∈ TAct) :
    ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N E Γ i : V},
      TableOK tbl N → ProAxmTable tbl → IsFormulaSet LAct Γ →
      DossF walkPieces Γ 0 (⌜σ⌝ : V) i → (C : V) + i ≤ E →
      ∃ P : V, NumInv tbl E Γ C P (axchFact (^&i)) := by
  obtain ⟨C₀, hC₀⟩ := numId_sentence (n := 0) σ
  obtain ⟨x, hx⟩ : ∃ x : ℕ, x = (⌜σ⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨Nd, hNd⟩ := closedDer_of_lib (lib_axchNum hσ)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = flN (Paxch : ℕ) * (2 * x + 1) := ⟨_, rfl⟩
  obtain ⟨Cn, hCn⟩ : ∃ Cn : ℕ, Cn = 2 * x + 1 + Q + Nd + 4 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = C₀ + Cn + 1 := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  intro V _ _ tbl N E Γ i htbl hT hΓ hD hE
  obtain ⟨dA, hdA, hdl⟩ := hNd V
  simp only at hdA hdl
  rw [← hx, code_axchNum] at hdA
  have hxV : ((x : ℕ) : V) = ⌜σ⌝ := by rw [hx]; exact Sentence.coe_quote_eq_quote _
  -- the numeral identification
  have hD' : DossF walkPieces Γ ((0 : ℕ) : V) (⌜σ⌝ : V) i := by rwa [Nat.cast_zero]
  obtain ⟨P₀, hP₀⟩ := hC₀ V htbl hT.layoutTable hΓ hD' (cap_mono (by omega) hE)
  have hΓ₁ := hP₀.isFormulaSet htbl hΓ
  have heq : neg LAct (eqFactB (^&i) (numeral (x : V))) ∈ finalCtx Γ P₀ := by
    have := hP₀.2.2.2.2.2
    rw [← hxV] at this
    exact this
  -- the closing two steps
  have hnx : IsSemiterm LAct 0 (numeral (x : V)) := isSemiterm_numeral_LAct _
  have h2x : ((2 * x + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * x + 1) (by omega) hE
  have hEx : termLen LAct (numeral (x : V)) ≤ E := termLen_numeral_le' (by push_cast at h2x; exact h2x)
  have hEi : i + 1 ≤ E := cap_fvar (a := 0) (by omega) hE
  have hA : IsFormula LAct (axchFact (numeral (x : V))) := isFormula_axchFact hnx
  have hQ' : formulaLen LAct (axchFact (numeral (x : V))) ≤ (Q : V) := by
    have hB : (1 : V) ≤ ((2 * x + 1 : ℕ) : V) := by exact_mod_cast (by omega : 1 ≤ 2 * x + 1)
    refine le_trans (formulaLen_axchFact_le hB hnx ?_) ?_
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_refl _)
    · rw [hQ]; unfold Paxch; rw [flN_pred]; push_cast; exact le_refl _
  obtain ⟨hlen, hrowM, hrowB⟩ := hT.congAxch
  have hres := lemmaThenHorn_ok
    (s := mkStep proAxmPieces ((aIdx_congAxch : ℕ) : V) ?[numeral (x : V), ^&i])
    (F := axchFact (^&i)) htbl hΓ₁ hA hdA hQ' hdl (fun hΓ' ↦ by
      obtain ⟨hok, htag, hctx⟩ := aok_congAxch htbl rfl hlen ⟨hrowM, hrowB⟩ hΓ' hnx hEx (by simp) (termLen_fvar_le hEi)
        mem_insert_self' (mem_insert_of_mem' heq)
      exact ⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), htag, hctx⟩)
  have hnode := pack2 (C := Cn) hres (by exact_mod_cast (by omega : Q ≤ Cn)) (by exact_mod_cast (by omega : Nd ≤ Cn)) (by omega)
  exact ⟨_, hP₀.append hnode (C := C) (by omega)⟩

end stdCase

/-! ## 4. Case (i) at the layout: the member `⌜σ⌝` of `s`, its dossier at `&(memTop s ⌜σ⌝ i)` -/

section stdLayout

/-- **The `axm` prologue for a standard axiom, at the layout** (`Layout.member` + `memTop_le`): from the
canonical layout of `s ∋ ⌜σ⌝` at chain offset `i`, under `C + (i + 6D + 1) ≤ E` (`setLen s ≤ D`), a shift-free
`NumInv` list leaving `axchFact &ip`, `ip = memTop s ⌜σ⌝ i` — exactly `nodeAxm_ok`'s `hax` after `Layout.transport`. -/
theorem proAxmStd_ok (σ : Sentence LAct) (hσ : σ ∈ TAct) :
    ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N Wc T s D E Γ i : V},
      TableOK tbl N → ProAxmTable tbl → Wc = certPieces →
      IsFormulaSet LAct s → (⌜σ⌝ : V) ∈ s → setLen LAct s ≤ D → (C : V) + (i + 6 * D + 1) ≤ E →
      IsFormulaSet LAct Γ → Layout walkPieces Wc T Γ s i →
      ∃ P : V, NumInv tbl E Γ C P (axchFact (^&(memTop walkPieces Wc T s (⌜σ⌝ : V) i))) := by
  obtain ⟨C, hC⟩ := axmStd_ok σ hσ
  refine ⟨C, fun V _ _ tbl N Wc T s D E Γ i htbl hT hWc hs hp hsD hE hΓ hLay ↦ ?_⟩
  obtain ⟨hDp, _, _, _⟩ := hLay.member hp
  have hle := memTop_le (i := i) htbl hT.walkTable hWc T hs hp hsD
  exact hC V htbl hT hΓ hDp (le_trans (add_le_add (le_refl _) hle) hE)

/-- **ONE constant for every standard axiom** (`stdAxiom_finite`: the per-σ constants of `proAxmStd_ok` are
bounded over the finite set). -/
theorem proAxm_std : ∃ C : ℕ, ∀ (σ : Sentence LAct), StdAxiom σ →
    ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N Wc T s D E Γ i : V},
      TableOK tbl N → ProAxmTable tbl → Wc = certPieces →
      IsFormulaSet LAct s → (⌜σ⌝ : V) ∈ s → setLen LAct s ≤ D → (C : V) + (i + 6 * D + 1) ≤ E →
      IsFormulaSet LAct Γ → Layout walkPieces Wc T Γ s i →
      ∃ P : V, NumInv tbl E Γ C P (axchFact (^&(memTop walkPieces Wc T s (⌜σ⌝ : V) i))) := by
  classical
  let Cf : Sentence LAct → ℕ := fun σ ↦ if h : σ ∈ TAct then Classical.choose (proAxmStd_ok σ h) else 0
  obtain ⟨C, hC⟩ := (stdAxiom_finite.image Cf).bddAbove
  refine ⟨C, fun σ hσ V _ _ tbl N Wc T s D E Γ i htbl hT hWc hs hp hsD hE hΓ hLay ↦ ?_⟩
  have hmem : σ ∈ TAct := hσ.mem_TAct
  have hCσ : Cf σ ≤ C := hC (Set.mem_image_of_mem Cf (show σ ∈ {σ : Sentence LAct | StdAxiom σ} from hσ))
  have e : Cf σ = Classical.choose (proAxmStd_ok σ hmem) := dif_pos hmem
  rw [e] at hCσ
  have hCV : ((Classical.choose (proAxmStd_ok σ hmem) : ℕ) : V) ≤ (C : V) := by exact_mod_cast hCσ
  obtain ⟨P, hP⟩ := Classical.choose_spec (proAxmStd_ok σ hmem) V htbl hT hWc hs hp hsD
    (le_trans (add_le_add hCV (le_refl _)) hE) hΓ hLay
  exact ⟨P, hP.mono hCσ⟩

end stdLayout

/-! ## 5. Case (ii) as an explicitly named, UNDISCHARGED hypothesis, and the assembly of both cases -/

section assembly

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Case (ii), NOT discharged here** (see the file docstring for exactly what it needs): for every member `p`
of `s` that is an induction instance, a shift-free `NumInv` list leaving `axchFact &(memTop s p i)`. -/
def AxmIndOracle (tbl E Wc T Γ s i : V) (C : ℕ) : Prop :=
  ∀ p ∈ s, IsSemiformula ℒₒᵣ 0 p → InductionR (fun _ ↦ True) p →
    ∃ P : V, NumInv tbl E Γ C P (axchFact (^&(memTop walkPieces Wc T s p i)))

/-- **The `axm` prologue** (`DESIGN_fragments.md` §4.10): for the member `p ∈ s` with `Theory.Δ₁ch TAct p`
(`p ∈ TAct.Δ₁Class`), a shift-free list applicable at cap `9`, of standard length, leaving `axchFact &ip` at
`ip = memTop s p i` — `nodeAxm_ok`'s `hax` — with the standard-axiom case (i) PROVED and the induction case (ii)
taken from `AxmIndOracle` (constant `Cind`). `NumInv tbl E Γ C P F` unfolds to `ListOK tbl E 9 Γ P ∧ NoDrop' P ∧
shiftsV P = 0 ∧ len P ≤ C ∧ SizeOK C C P ∧ neg F ∈ finalCtx Γ P` — shift-free, so the fact is at `&ip` itself. -/
theorem proAxm_ok : ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N Wc T s D E Γ i p : V}
    (Cind : ℕ), TableOK tbl N → ProAxmTable tbl → Wc = certPieces →
    IsFormulaSet LAct s → p ∈ s → p ∈ TAct.Δ₁Class → setLen LAct s ≤ D →
    ((C + Cind : ℕ) : V) + (i + 6 * D + 1) ≤ E → IsFormulaSet LAct Γ → Layout walkPieces Wc T Γ s i →
    AxmIndOracle tbl E Wc T Γ s i Cind →
    ∃ P : V, NumInv tbl E Γ (C + Cind) P (axchFact (^&(memTop walkPieces Wc T s p i))) := by
  obtain ⟨C, hC⟩ := proAxm_std
  refine ⟨C, fun V _ _ tbl N Wc T s D E Γ i p Cind htbl hT hWc hs hp hax hsD hE hΓ hLay hind ↦ ?_⟩
  have hC1 : ((C : ℕ) : V) ≤ ((C + Cind : ℕ) : V) := by exact_mod_cast (Nat.le_add_right C Cind)
  have hC2 : ((Cind : ℕ) : V) ≤ ((C + Cind : ℕ) : V) := by exact_mod_cast (Nat.le_add_left Cind C)
  rcases mem_TAct_class_cases hax with ⟨σ, hσ, rfl⟩ | ⟨hF, hI⟩
  · obtain ⟨P, hP⟩ := hC σ hσ V htbl hT hWc hs hp hsD (le_trans (add_le_add hC1 (le_refl _)) hE) hΓ hLay
    exact ⟨P, hP.mono (Nat.le_add_right C Cind)⟩
  · obtain ⟨P, hP⟩ := hind p hp hF hI
    exact ⟨P, hP.mono (Nat.le_add_left Cind C)⟩

/-- **The cost of the `axm` prologue** — `NumId.numInv_cost`'s shape (linear in `N`, `E`, `setLen Γ`, `fvOccS Γ`
for the standard `C` and the row-body bound `B`; `Prologue` §11's coarse shape with `len ≤ C`). -/
theorem costSum_proAxm_le {tbl N E B Γ P ip : V} {C : ℕ} (hE : 1 ≤ E) (htbl : TableOK tbl N)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (h : NumInv tbl E Γ C P (axchFact (^&ip))) :
    costSum N E Γ P ≤ (C : V) * (costK N E B ((9 : ℕ) : V) (C : V) (C : V) +
      38 * (ctxBoundG (growK B E (C : V)) Γ (C : V) + (fvOccS LAct Γ + (C : V) * growK B E (C : V)))) :=
  numInv_cost hE htbl hBt h

end assembly

end ArithS
