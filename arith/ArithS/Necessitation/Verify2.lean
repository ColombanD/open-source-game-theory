import ArithS.Necessitation.Verify
import ArithS.Necessitation.Prologue
import ArithS.Necessitation.ProAxm
import ArithS.Necessitation.Top
import ArithS.Necessitation.NodeSize
import ArithS.Necessitation.Pin

/-!
# ArithS.Necessitation.Verify2 — `VerifyGraph'`: the verification recursion with COMPUTED prologues

`Verify.lean` §3 defines `VerifyGraph` with every prologue and every fragment index EXISTENTIALLY free
(an explicit weakening, §3.6 there): the relation admits garbage lists, so `Top.lean` §9's
`VerifyKit'.ok` is FALSE for it. This file defines the relation the kit is really about,
`VerifyGraph'` (§6), on the same key `⟪ρ, L⟫` and with the same ten clause SHAPES, but with each
clause's list COMPUTED: the prologue of `Prologue.lean` (`proAxL`, `proIns`/`postIns`, `proOr`,
`proWk`/`proWk0`, `proShift`/`proShift0`, `proCutPre` + `proIns`/`proIns0`, `proAll`, `proExs`), the
children's lists spliced in, and the node fragment of `Frag1`/`Frag2` at the DETERMINED offsets
(§5, the per-tag assemblers `v<Tag>`). Every node is verified at the canonical offset `0` of its own
layout (`Layout … s 0`, or `Layout0 … 0` when the sequent is EMPTY — `Prologue.lean` §12's decision).

**The `axm` clause — option (B) (`BRIEF.md` §11, 2026-09-15), IMPLEMENTED AS A CERTIFICATE TABLE.**
`proAxm` is NOT Σ₁ (its `sLemma` steps carry per-model derivations, `ProAxm.lean`), so the `axm`
clause cannot compute its prologue. The brief's option (B) asks for `∃ pro ≤ L` constrained by a Δ₁
certificate `AxmPro` (`ListOK` at the CANONICAL dossier context + the fact) inside the blueprint.
`ListOK`/`StepOK` have `definability`-derived instances but NO named `𝚫₁.Semisentence`, and a
`Definable` instance yields only a formula WITH PARAMETERS — nothing a blueprint can call. So the
certificate is kept OUTSIDE the blueprint, as a Lean predicate on the entries of a PARAMETER `A` of
the recursion: the clause checks `⟪p, ip, pro⟫ ∈ A` (Δ₀), and `AxmTableOK tbl E Ww A C` (§3) says
every entry is a shift-free `NumInv` list at the canonical context `dossCtx Ww p ip`
(= the dossier of `p` shifted to `&ip`, §1). The context-MONOTONICITY lemmas of §2 transfer such a
list to the actual layout context. Existence (§7) builds `A` from `ProAxm`'s per-model case (i) and
the NAMED oracle `AxmIndOracleC` for case (ii) — the same undischarged hypothesis as
`ProAxm.AxmIndOracle`, restated at the canonical context.

Contents: §1 `setShiftIterV`, `dossCtx`; §2 `ctxAfter_mono'`/`ctxVec_mono'`/`listOK_mono_subset`/
`NumInv.mono_ctx`; §3 `AxmEntryOK`/`AxmTableOK`/`AxmIndOracleC`, `axmStd_uniform`,
`axmEntry_exists`; §4 the Σ₁ graphs of the index helpers (`memTop`, `proSig`, `allCf`, …);
§5 the ten assemblers; §6 `VerifyGraph'` (blueprint, construction, `StrongFinite`, definability,
`case_iff`, inversions); §7 monotonicity in `A` and `verifyGraph'_exists`; §8 `verifyGraph'_ok`.
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

/-! ## 1. Iterated set shifts and the canonical dossier context -/

section setShiftIter

namespace SetShiftIterV

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih i x. ∃ s, !(setShiftGraph LAct) s ih ∧ y = s”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun v ↦ v 0
  succ := fun _ _ ih ↦ setShift LAct ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, setShift.defined.iff]

end SetShiftIterV

/-- `setShiftIterV Γ k = setShift^[k] Γ`, `k : V`. -/
noncomputable def setShiftIterV (Γ k : V) : V := SetShiftIterV.construction.result ![Γ] k

@[simp] lemma setShiftIterV_zero (Γ : V) : setShiftIterV Γ 0 = Γ := by
  simp [setShiftIterV, SetShiftIterV.construction]
@[simp] lemma setShiftIterV_succ (Γ k : V) : setShiftIterV Γ (k + 1) = setShift LAct (setShiftIterV Γ k) := by
  simp [setShiftIterV, SetShiftIterV.construction]

noncomputable def setShiftIterVDef : 𝚺₁.Semisentence 3 :=
  SetShiftIterV.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance setShiftIterV_defined : 𝚺₁-Function₂ (setShiftIterV : V → V → V) via setShiftIterVDef := .mk
  fun v ↦ by simp [SetShiftIterV.construction.result_defined_iff, setShiftIterVDef]; rfl
instance setShiftIterV_definable : 𝚺₁-Function₂ (setShiftIterV : V → V → V) :=
  setShiftIterV_defined.to_definable

lemma mem_setShiftIterV_of_mem (Γ : V) : ∀ k : V, ∀ y ∈ Γ, shiftIterV y k ∈ setShiftIterV Γ k := by
  intro k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => intro y hy; simpa using hy
  | succ k ih =>
    intro y hy
    rw [setShiftIterV_succ, shiftIterV_succ]
    exact mem_setShift_iff.mpr ⟨shiftIterV y k, ih y hy, rfl⟩

lemma exists_of_mem_setShiftIterV (Γ : V) : ∀ k : V, ∀ x ∈ setShiftIterV Γ k, ∃ y ∈ Γ, x = shiftIterV y k := by
  intro k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => intro x hx; exact ⟨x, by simpa using hx, by simp⟩
  | succ k ih =>
    intro x hx
    rw [setShiftIterV_succ] at hx
    obtain ⟨z, hz, rfl⟩ := mem_setShift_iff.mp hx
    obtain ⟨y, hy, rfl⟩ := ih z hz
    exact ⟨y, hy, (shiftIterV_succ y k).symm⟩

lemma mem_setShiftIterV_iff (Γ k x : V) : x ∈ setShiftIterV Γ k ↔ ∃ y ∈ Γ, x = shiftIterV y k :=
  ⟨exists_of_mem_setShiftIterV Γ k x, fun ⟨y, hy, hx⟩ ↦ hx ▸ mem_setShiftIterV_of_mem Γ k y hy⟩

lemma isFormulaSet_setShiftIterV {Γ : V} (h : IsFormulaSet LAct Γ) : ∀ k : V, IsFormulaSet LAct (setShiftIterV Γ k) := by
  intro k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simpa using h
  | succ k ih => rw [setShiftIterV_succ]; exact ih.setShift

/-- **The canonical dossier context**: the dossier of `p` (the walk from the empty context) with every
fact shifted to offset `ip` — exactly the facts `DossF Ww Γ 0 p ip` puts into `Γ`. -/
noncomputable def dossCtx (Ww p ip : V) : V := setShiftIterV (finalCtx 0 (describeF Ww 0 p)) ip

noncomputable def dossCtxDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y Ww p ip. ∃ D, !describeFDef D Ww 0 p ∧ ∃ G, !finalCtxDef G 0 D ∧ !setShiftIterVDef y G ip”

instance dossCtx_defined : 𝚺₁-Function₃ (dossCtx : V → V → V → V) via dossCtxDef := .mk fun v ↦ by
  simp [dossCtxDef, dossCtx, describeF_defined.iff, finalCtx_defined.iff, setShiftIterV_defined.iff]
instance dossCtx_definable : 𝚺₁-Function₃ (dossCtx : V → V → V → V) := dossCtx_defined.to_definable

lemma dossCtx_subset {Ww Γ p ip : V} (h : DossF Ww Γ 0 p ip) : dossCtx Ww p ip ⊆ Γ := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_setShiftIterV_iff _ _ _).mp hx
  exact h y hy

lemma dossF_dossCtx (Ww p ip : V) : DossF Ww (dossCtx Ww p ip) 0 p ip :=
  fun f hf ↦ (mem_setShiftIterV_iff _ _ _).mpr ⟨f, hf, rfl⟩

lemma isFormulaSet_dossCtx {tbl N p : V} (htbl : TableOK tbl N) (hW : WalkTable tbl)
    (hp : IsSemiformula LAct 0 p) (ip : V) : IsFormulaSet LAct (dossCtx walkPieces p ip) := by
  obtain ⟨hok, -, -, -, -⟩ := describeF_ok htbl hW hp (E := 2 * 0 + 2 * formulaLen LAct p + 8) le_rfl
    (Γ := 0) IsFormulaSet.empty
  exact isFormulaSet_setShiftIterV (finalCtx_isFormulaSet 8 htbl IsFormulaSet.empty hok) ip

end setShiftIter

/-! ## 2. Context monotonicity for cut-admitting lists (`Cert` Part 0's `ctxAfter_mono`/`ctxVec_mono`,
extended to the goal cut `6` and the lemma cut `7`; `StepOK` itself is monotone in the context) -/

section mono

lemma ctxAfter_mono' {Γ Γ' s : V}
    (h : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2 ∨ sTag s = 3 ∨ sTag s = 4 ∨ sTag s = 6 ∨ sTag s = 7)
    (hsub : Γ ⊆ Γ') : ctxAfter Γ s ⊆ ctxAfter Γ' s := by
  rcases h with h | h | h | h | h | h | h
  · exact ctxAfter_mono (Or.inl h) hsub
  · exact ctxAfter_mono (Or.inr (Or.inl h)) hsub
  · exact ctxAfter_mono (Or.inr (Or.inr (Or.inl h))) hsub
  · exact ctxAfter_mono (Or.inr (Or.inr (Or.inr (Or.inl h)))) hsub
  · exact ctxAfter_mono (Or.inr (Or.inr (Or.inr (Or.inr h)))) hsub
  · intro x hx
    rw [ctxAfter_tag6 h] at hx ⊢
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · simp
    · exact mem_bitInsert_iff.mpr (Or.inr (hsub hx))
  · intro x hx
    rw [ctxAfter_tag7 h] at hx ⊢
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · simp
    · exact mem_bitInsert_iff.mpr (Or.inr (hsub hx))

lemma ctxVec_mono' {Γ Γ' S : V} (hS : NoDrop' S) (hsub : Γ ⊆ Γ') :
    ∀ j ≤ len S, (ctxVec Γ S).[j] ⊆ (ctxVec Γ' S).[j] := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _; simpa using hsub
  | succ j ih =>
    intro hj
    have hj' : j < len S := lt_of_lt_of_le (lt_add_one j) hj
    rw [nth_ctxVec_succ Γ S hj', nth_ctxVec_succ Γ' S hj']
    exact ctxAfter_mono' (hS j hj') (ih (le_of_lt hj'))

lemma finalCtx_mono' {Γ Γ' S : V} (hS : NoDrop' S) (hsub : Γ ⊆ Γ') : finalCtx Γ S ⊆ finalCtx Γ' S :=
  ctxVec_mono' hS hsub (len S) le_rfl

lemma HornOK.mono_ctx {tbl E M Γ Γ' s : V} (hsub : Γ ⊆ Γ') (h : HornOK tbl E M Γ s) : HornOK tbl E M Γ' s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun k hk ↦ hsub (h.2.2.2.2.2 k hk)⟩

lemma GoalOK.mono_ctx {E Γ Γ' s : V} (hsub : Γ ⊆ Γ') (h : GoalOK E Γ s) : GoalOK E Γ' s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    hsub h.2.2.2.2.2.2.2.2.1, hsub h.2.2.2.2.2.2.2.2.2.1, hsub h.2.2.2.2.2.2.2.2.2.2.1,
    hsub h.2.2.2.2.2.2.2.2.2.2.2⟩

/-- **A step stays applicable in a larger (formula-set) context.** -/
lemma StepOK.mono_ctx {tbl E M Γ Γ' s : V} (hΓ' : IsFormulaSet LAct Γ') (hsub : Γ ⊆ Γ')
    (h : StepOK tbl E M Γ s) : StepOK tbl E M Γ' s := by
  obtain ⟨-, h⟩ := h
  refine ⟨hΓ', ?_⟩
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | h
  · exact Or.inl ⟨h1, h2.mono_ctx hsub, h3⟩
  · exact Or.inr (Or.inl ⟨h1, h2.mono_ctx hsub, h3⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2.mono_ctx hsub, h3⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, hsub h3⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, hsub h4⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, fun x hx ↦ hsub (h2 hx)⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2.mono_ctx hsub⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-- The transfer, by induction along the list: the steps up to `j` are applicable at the larger
contexts, and the larger context at `j` is a formula set. -/
lemma listOK_mono_aux (M : ℕ) {tbl N E Γ Γ' S : V} (htbl : TableOK tbl N) (hΓ' : IsFormulaSet LAct Γ')
    (hS : NoDrop' S) (hsub : Γ ⊆ Γ') (h : ListOK tbl E (M : V) Γ S) :
    ∀ j ≤ len S, (∀ i < j, StepOK tbl E (M : V) (ctxVec Γ' S).[i] S.[i]) ∧ IsFormulaSet LAct (ctxVec Γ' S).[j] := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    refine ⟨fun i hi ↦ by simp at hi, ?_⟩
    simpa using hΓ'
  | succ j ih =>
    intro hj
    have hj' : j < len S := lt_of_lt_of_le (lt_add_one j) hj
    obtain ⟨ih₁, ih₂⟩ := ih (le_of_lt hj')
    have hstep : StepOK tbl E (M : V) (ctxVec Γ' S).[j] S.[j] :=
      (h j hj').mono_ctx ih₂ (ctxVec_mono' hS hsub j (le_of_lt hj'))
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with hlt | rfl
      · exact ih₁ i hlt
      · exact hstep
    · rw [nth_ctxVec_succ Γ' S hj']
      exact isFormulaSet_ctxAfter M htbl hstep

/-- **`ListOK` is monotone in the initial context** for cut-admitting lists. -/
theorem listOK_mono_subset (M : ℕ) {tbl N E Γ Γ' S : V} (htbl : TableOK tbl N) (hΓ' : IsFormulaSet LAct Γ')
    (hS : NoDrop' S) (hsub : Γ ⊆ Γ') (h : ListOK tbl E (M : V) Γ S) : ListOK tbl E (M : V) Γ' S :=
  fun i hi ↦ (listOK_mono_aux M htbl hΓ' hS hsub h (len S) le_rfl).1 i hi

/-- A `NumInv` list (`NumId.lean`) transfers to any larger formula-set context. -/
theorem NumInv.mono_ctx {tbl N E Γ Γ' P F : V} {C : ℕ} (htbl : TableOK tbl N) (hΓ' : IsFormulaSet LAct Γ')
    (hsub : Γ ⊆ Γ') (h : NumInv tbl E Γ C P F) : NumInv tbl E Γ' C P F := by
  obtain ⟨hok, hnd, hsh, hlen, hsz, hmem⟩ := h
  exact ⟨listOK_mono_subset 9 htbl hΓ' hnd hsub hok, hnd, hsh, hlen, hsz, finalCtx_mono' hnd hsub hmem⟩

end mono

/-! ## 3. The `axm` certificate table (option (B), as a parameter of the recursion) -/

section axmTable

/-- The `V`-constant form of `NumId.NumInv` (`C` a `V`-value, for the Δ₁ predicates below);
`NumInv tbl E Γ C P F = NumInvV tbl E Γ (C : V) P F` by `rfl`. -/
def NumInvV (tbl E Γ Cv P F : V) : Prop :=
  ListOK tbl E ((9 : ℕ) : V) Γ P ∧ NoDrop' P ∧ shiftsV P = 0 ∧ len P ≤ Cv ∧ SizeOK Cv Cv P ∧ neg LAct F ∈ finalCtx Γ P

lemma numInv_iff_numInvV {tbl E Γ P F : V} {C : ℕ} : NumInv tbl E Γ C P F ↔ NumInvV tbl E Γ (C : V) P F := Iff.rfl

instance numInvV_definable : 𝚫₁.Definable (fun v : Fin 6 → V ↦ NumInvV (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := by
  unfold NumInvV; definability

/-- **An `axm` certificate entry** `⟪p, ip, pro⟫`: `pro` is a shift-free `NumInv` list at the canonical
dossier context of `p` at `&ip`, leaving `axchFact &ip`. -/
def AxmEntryOK (tbl E Ww Cv e : V) : Prop :=
  ∃ p ≤ e, ∃ ip ≤ e, ∃ pro ≤ e, e = ⟪p, ip, pro⟫ ∧ NumInvV tbl E (dossCtx Ww p ip) Cv pro (axchFact (^&ip))

/-- **The certificate table**: every member of `A` is a certificate entry. -/
def AxmTableOK (tbl E Ww A Cv : V) : Prop := ∀ e ∈ A, AxmEntryOK tbl E Ww Cv e

instance axmEntryOK_definable : 𝚫₁-Relation₅ (AxmEntryOK : V → V → V → V → V → Prop) := by
  unfold AxmEntryOK; definability

instance axmTableOK_definable : 𝚫₁-Relation₅ (AxmTableOK : V → V → V → V → V → Prop) := by
  unfold AxmTableOK; definability

lemma AxmTableOK.mono {tbl E Ww A A' Cv : V} (h : AxmTableOK tbl E Ww A' Cv) (hAA : A ⊆ A') :
    AxmTableOK tbl E Ww A Cv := by
  intro e he
  exact h e (hAA he)

lemma AxmTableOK.mono_const {tbl E Ww A Cv Cv' : V} (hC : Cv ≤ Cv') (h : AxmTableOK tbl E Ww A Cv) :
    AxmTableOK tbl E Ww A Cv' := by
  intro e he
  obtain ⟨p, hp, ip, hip, pro, hpro, rfl, hok, hnd, hsh, hlen, hsz, hmem⟩ := h e he
  exact ⟨p, hp, ip, hip, pro, hpro, rfl, hok, hnd, hsh, le_trans hlen hC, hsz.mono hC hC, hmem⟩

lemma axmTableOK_empty (tbl E Ww Cv : V) : AxmTableOK tbl E Ww 0 Cv := fun e he ↦ by simp at he

lemma axmTableOK_insert {tbl E Ww A Cv p ip pro : V} (h : AxmTableOK tbl E Ww A Cv)
    (he : NumInvV tbl E (dossCtx Ww p ip) Cv pro (axchFact (^&ip))) :
    AxmTableOK tbl E Ww (insert ⟪p, ip, pro⟫ A) Cv := by
  intro e hemem
  rcases mem_bitInsert_iff.mp hemem with rfl | hemem
  · exact ⟨p, le_pair_left _ _, ip, le_trans (le_pair_left _ _) (le_pair_right _ _), pro,
      le_trans (le_pair_right _ _) (le_pair_right _ _), rfl, he⟩
  · exact h e hemem

lemma axmTableOK_union {tbl E Ww A A' Cv : V} (h : AxmTableOK tbl E Ww A Cv) (h' : AxmTableOK tbl E Ww A' Cv) :
    AxmTableOK tbl E Ww (A ∪ A') Cv := by
  intro e he
  rcases mem_cup_iff.mp he with he | he
  · exact h e he
  · exact h' e he

/-- **Case (ii) of `axm` at the canonical context — NOT discharged** (`ProAxm.lean`'s file docstring says
exactly what it needs): for every induction instance `p` and offset `ip` with room, a shift-free `NumInv`
list at `dossCtx walkPieces p ip` leaving `axchFact &ip`. -/
def AxmIndOracleC (tbl E : V) (C : ℕ) : Prop :=
  ∀ p ip : V, IsSemiformula ℒₒᵣ 0 p → InductionR (fun _ ↦ True) p → (C : V) + ip ≤ E →
    ∃ P : V, NumInv tbl E (dossCtx walkPieces p ip) C P (axchFact (^&ip))

/-- **ONE constant for every standard axiom at a dossier** (`ProAxm.axmStd_ok` over the finite
`StdAxiom` set — the dossier-based twin of `ProAxm.proAxm_std`). -/
theorem axmStd_uniform : ∃ C : ℕ, ∀ (σ : Sentence LAct), StdAxiom σ →
    ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N E Γ i : V},
      TableOK tbl N → ProAxmTable tbl → IsFormulaSet LAct Γ →
      DossF walkPieces Γ 0 (⌜σ⌝ : V) i → (C : V) + i ≤ E →
      ∃ P : V, NumInv tbl E Γ C P (axchFact (^&i)) := by
  classical
  let Cf : Sentence LAct → ℕ := fun σ ↦ if h : σ ∈ TAct then Classical.choose (axmStd_ok σ h) else 0
  obtain ⟨C, hC⟩ := (stdAxiom_finite.image Cf).bddAbove
  refine ⟨C, fun σ hσ V _ _ tbl N E Γ i htbl hT hΓ hD hE ↦ ?_⟩
  have hmem : σ ∈ TAct := hσ.mem_TAct
  have hCσ : Cf σ ≤ C := hC (Set.mem_image_of_mem Cf (show σ ∈ {σ : Sentence LAct | StdAxiom σ} from hσ))
  have e : Cf σ = Classical.choose (axmStd_ok σ hmem) := dif_pos hmem
  rw [e] at hCσ
  have hCV : ((Classical.choose (axmStd_ok σ hmem) : ℕ) : V) ≤ (C : V) := by exact_mod_cast hCσ
  obtain ⟨P, hP⟩ := Classical.choose_spec (axmStd_ok σ hmem) V htbl hT hΓ hD (le_trans (add_le_add hCV (le_refl _)) hE)
  exact ⟨P, hP.mono hCσ⟩

/-- **An `axm` certificate entry exists** for every `p ∈ TAct.Δ₁Class` (per model): case (i) by
`axmStd_uniform`, case (ii) by the oracle. -/
theorem axmEntry_exists : ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N E p ip : V}
    (Cind : ℕ), TableOK tbl N → ProAxmTable tbl → IsSemiformula LAct 0 p → p ∈ TAct.Δ₁Class →
    ((C + Cind : ℕ) : V) + ip ≤ E → AxmIndOracleC tbl E Cind →
    ∃ P : V, NumInv tbl E (dossCtx walkPieces p ip) (C + Cind) P (axchFact (^&ip)) := by
  obtain ⟨C, hC⟩ := axmStd_uniform
  refine ⟨C, fun V _ _ tbl N E p ip Cind htbl hT hp hax hE hind ↦ ?_⟩
  have hC1 : ((C : ℕ) : V) ≤ ((C + Cind : ℕ) : V) := by exact_mod_cast (Nat.le_add_right C Cind)
  have hC2 : ((Cind : ℕ) : V) ≤ ((C + Cind : ℕ) : V) := by exact_mod_cast (Nat.le_add_left Cind C)
  have hΓ : IsFormulaSet LAct (dossCtx walkPieces p ip) := isFormulaSet_dossCtx htbl hT.walkTable hp ip
  rcases mem_TAct_class_cases hax with ⟨σ, hσ, rfl⟩ | ⟨hF, hI⟩
  · obtain ⟨P, hP⟩ := hC σ hσ V htbl hT hΓ (dossF_dossCtx _ _ _) (le_trans (add_le_add hC1 (le_refl _)) hE)
    exact ⟨P, hP.mono (Nat.le_add_right C Cind)⟩
  · obtain ⟨P, hP⟩ := hind p ip hF hI (le_trans (add_le_add hC2 (le_refl _)) hE)
    exact ⟨P, hP.mono (Nat.le_add_left Cind C)⟩

end axmTable

/-! ## 4. The Σ₁ graphs of the index helpers of `Prologue.lean` (`memTop`, `proSig`, the `all`/`exs`
shift counts) — these carry no `Def` there; the assemblers of §5 call them. -/

section helperDefs

noncomputable def memTopDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y Ww Wc T s x i. ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧ ∃ os, !offVecDef os xs Ww Wc T ∧
    ∃ a, !idxOfDef a xs x ∧ ∃ oa, !nthDef oa os a ∧ y = i + (2 * k + 1 + oa)”

instance memTop_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ memTop (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) memTopDef := .mk
  fun v ↦ by
    simp [memTopDef, memTop, mTop, memberList_defined.iff, offVec_defined.iff, idxOf_defined.iff, numeral_eq_natCast]
instance memTop_definable :
    𝚺₁.DefinableFunction (fun v : Fin 6 → V ↦ memTop (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := memTop_defined.to_definable

noncomputable def proSigDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y Ww Wl Wc W T c. ∃ L, !layoutStepsDef L Ww Wl Wc W T c ∧ !shiftsVDef y L”

instance proSig_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ proSig (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) proSigDef := .mk
  fun v ↦ by simp [proSigDef, proSig, layoutSteps_defined.iff, shiftsV_defined.iff]
instance proSig_definable :
    𝚺₁.DefinableFunction (fun v : Fin 6 → V ↦ proSig (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := proSig_defined.to_definable

/-- `allCf Ww Wc p = freeCw Ww + freeS Wc Ww p (descCountF Ww 0 (free p)) 0` (`Prologue.lean` §13.3). -/
noncomputable def allCfDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y Ww Wc p. ∃ fp, !(freeGraph LAct) fp p ∧ ∃ c₂, !descCountFDef c₂ Ww 0 fp ∧
    ∃ z0, !qqFvarDef z0 0 ∧ ∃ fv, !adjoinDef fv z0 0 ∧ ∃ dv, !descTVecDef dv Ww 0 1 fv ∧ ∃ FW, !descVecAuxDef FW Ww 0 dv 1 ∧
    ∃ cw, !pi₁Def cw FW ∧ ∃ sp, !(shiftGraph LAct) sp p ∧ ∃ a, a = c₂ + cw ∧ ∃ b, b = 0 + cw ∧
    ∃ Ls, !certSubstDef Ls Wc Ww 1 0 fv 0 sp a b ∧ ∃ fs, !shiftsVDef fs Ls ∧ y = cw + fs”

instance allCf_defined : 𝚺₁-Function₃ (allCf : V → V → V → V) via allCfDef := .mk fun v ↦ by
  simp [allCfDef, allCf, freeS, freeCw, freeWalk, fvec, free.defined.iff, descCountF_defined.iff, descTVec_defined.iff,
    descVecAux_defined.iff, shift.defined.iff, certSubst_defined.iff, shiftsV_defined.iff, numeral_eq_natCast]
instance allCf_definable : 𝚺₁-Function₃ (allCf : V → V → V → V) := allCf_defined.to_definable

noncomputable def allCertSigDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y Ww Wc p. ∃ sp, !(shiftGraph LAct) sp p ∧ ∃ c₁, !descCountFDef c₁ Ww 1 sp ∧ ∃ fp, !(freeGraph LAct) fp p ∧
    ∃ c₂, !descCountFDef c₂ Ww 0 fp ∧ ∃ cf, !allCfDef cf Ww Wc p ∧ y = c₁ + c₂ + cf”

instance allCertSig_defined : 𝚺₁-Function₃ (allCertSig : V → V → V → V) via allCertSigDef := .mk fun v ↦ by
  simp [allCertSigDef, allCertSig, shift.defined.iff, descCountF_defined.iff, free.defined.iff, allCf_defined.iff,
    numeral_eq_natCast]
instance allCertSig_definable : 𝚺₁-Function₃ (allCertSig : V → V → V → V) := allCertSig_defined.to_definable

noncomputable def vecCwDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y Ww t. ∃ tv, !adjoinDef tv t 0 ∧ ∃ dv, !descTVecDef dv Ww 0 1 tv ∧ ∃ VW, !descVecAuxDef VW Ww 0 dv 1 ∧ !pi₁Def y VW”

instance vecCw_defined : 𝚺₁-Function₂ (vecCw : V → V → V) via vecCwDef := .mk fun v ↦ by
  simp [vecCwDef, vecCw, descTVec_defined.iff, descVecAux_defined.iff, numeral_eq_natCast]
instance vecCw_definable : 𝚺₁-Function₂ (vecCw : V → V → V) := vecCw_defined.to_definable

noncomputable def exsSlDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y Wc T t. ∃ Lt, !lenTDef Lt Wc T 0 t 1 ∧ !shiftsVDef y Lt”

instance exsSl_defined : 𝚺₁-Function₃ (exsSl : V → V → V → V) via exsSlDef := .mk fun v ↦ by
  simp [exsSlDef, exsSl, lenT_defined.iff, shiftsV_defined.iff, numeral_eq_natCast]
instance exsSl_definable : 𝚺₁-Function₃ (exsSl : V → V → V → V) := exsSl_defined.to_definable

noncomputable def exsC3Def : 𝚺₁.Semisentence 4 := .mkSigma
  “y Ww t p. ∃ pt, !(substs1Graph LAct) pt t p ∧ !descCountFDef y Ww 0 pt”

instance exsC3_defined : 𝚺₁-Function₃ (exsC3 : V → V → V → V) via exsC3Def := .mk fun v ↦ by
  simp [exsC3Def, exsC3, substs1.defined.iff, descCountF_defined.iff, numeral_eq_natCast]
instance exsC3_definable : 𝚺₁-Function₃ (exsC3 : V → V → V → V) := exsC3_defined.to_definable

noncomputable def exsIwDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y Ww Wc T t p. ∃ sl, !exsSlDef sl Wc T t ∧ ∃ c₃, !exsC3Def c₃ Ww t p ∧ y = sl + 1 + c₃”

instance exsIw_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → V ↦ exsIw (v 0) (v 1) (v 2) (v 3) (v 4)) exsIwDef := .mk fun v ↦ by
  simp [exsIwDef, exsIw, exsSl_defined.iff, exsC3_defined.iff]
instance exsIw_definable :
    𝚺₁.DefinableFunction (fun v : Fin 5 → V ↦ exsIw (v 0) (v 1) (v 2) (v 3) (v 4)) := exsIw_defined.to_definable

noncomputable def exsIpDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y Ww Wc T s p t i. ∃ cv, !vecCwDef cv Ww t ∧ ∃ sl, !exsSlDef sl Wc T t ∧ ∃ c₃, !exsC3Def c₃ Ww t p ∧
    ∃ r, !qqExsDef r p ∧ ∃ i'', i'' = i + cv + sl + 1 + c₃ ∧ ∃ m, !memTopDef m Ww Wc T s r i'' ∧ y = m + 1”

instance exsIp_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ exsIp (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) exsIpDef := .mk
  fun v ↦ by
    simp [exsIpDef, exsIp, vecCw_defined.iff, exsSl_defined.iff, exsC3_defined.iff, memTop_defined.iff, numeral_eq_natCast]
instance exsIp_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ exsIp (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := exsIp_defined.to_definable

noncomputable def exsScDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y Ww Wc T s p t i. ∃ tv, !adjoinDef tv t 0 ∧ ∃ iw, !exsIwDef iw Ww Wc T t p ∧ ∃ ip, !exsIpDef ip Ww Wc T s p t i ∧
    ∃ Ls, !certSubstDef Ls Wc Ww 1 0 tv iw p ip 0 ∧ !shiftsVDef y Ls”

instance exsSc_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ exsSc (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) exsScDef := .mk
  fun v ↦ by
    simp [exsScDef, exsSc, exsIw_defined.iff, exsIp_defined.iff, certSubst_defined.iff, shiftsV_defined.iff,
      numeral_eq_natCast]
instance exsSc_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ exsSc (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := exsSc_defined.to_definable

noncomputable def exsSigDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y Ww Wc T s p t i. ∃ cv, !vecCwDef cv Ww t ∧ ∃ sl, !exsSlDef sl Wc T t ∧ ∃ c₃, !exsC3Def c₃ Ww t p ∧
    ∃ sc, !exsScDef sc Ww Wc T s p t i ∧ y = cv + sl + 1 + c₃ + sc”

instance exsSig_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ exsSig (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) exsSigDef := .mk
  fun v ↦ by
    simp [exsSigDef, exsSig, vecCw_defined.iff, exsSl_defined.iff, exsC3_defined.iff, exsSc_defined.iff]
instance exsSig_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ exsSig (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := exsSig_defined.to_definable

end helperDefs

end ArithS
