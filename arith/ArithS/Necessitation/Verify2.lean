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

/-! ## 5. The per-tag assemblers `v<Tag>`: prologue ++ child ++ recovery ++ … ++ node, at the determined offsets

Every node is verified at offset `0` of its own layout; `k = len (memberList s)` is the parent's member count,
`σ = shiftsV` of a block, and each child list `L'` is spliced in after the prologue that lays the child out at `0`.
The recovery after a child is `postIns W s'' cp n` (`goalElim` + `congFstIdx`, 2 shifts) for the `insert` children
(`and`/`or`/`cut`/`all`/`exs`) and the bare `goalElim` (2 shifts) for `wk`/`shift`, whose child sequent IS the row
object. The EMPTY-sequent split (`Prologue.lean` §12) lives in the three selectors `wkPro`/`shiftPro`/`cutPro`; the
empty `shift` child comes out of `proShift0` at offset `1`, so `reset0` re-lays the empty child out at `0`
(`layoutSteps0` + the identification `eqSymm`/`eqTrans`/`congSetShiftR` of the fresh `∅`-object with the old one). -/

section assemblers

/-- The `axL` list: `proAxL` (shift-free), then `fragAxL` at `is = k + 1`, `il = 0`. -/
noncomputable def vAxL (Ww Wc W₁ T s p : V) : V :=
  appendV (proAxL Ww Wc T s p 0)
    (fragAxL W₁ T (len (memberList s) + 1) 0 (memTop Ww Wc T s p 0) (memTop Ww Wc T s (neg LAct p) 0)
      (setLen LAct s) (dlen TAct (axL s p)))

noncomputable def vAxLDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y Ww Wc W₁ T s p. ∃ P, !proAxLDef P Ww Wc T s p 0 ∧ ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧
    ∃ is, is = k + 1 ∧ ∃ ip, !memTopDef ip Ww Wc T s p 0 ∧ ∃ np, !(negGraph LAct) np p ∧ ∃ inp, !memTopDef inp Ww Wc T s np 0 ∧
    ∃ Ls, !(setLenDef LAct) Ls s ∧ ∃ d, !axLGraph d s p ∧ ∃ n, !(dlenDef TAct) n d ∧
    ∃ F, !fragAxLDef F W₁ T is 0 ip inp Ls n ∧ !appendVDef y P F”

instance vAxL_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ vAxL (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) vAxLDef := .mk fun v ↦ by
  simp [vAxLDef, vAxL, proAxL_defined.iff, memberList_defined.iff, memTop_defined.iff, neg.defined.iff,
    setLen_defined.iff, dlen_defined.iff, fragAxL_defined.iff, appendV_defined.iff, numeral_eq_natCast]
instance vAxL_definable :
    𝚺₁.DefinableFunction (fun v : Fin 6 → V ↦ vAxL (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := vAxL_defined.to_definable

/-- The `verumIntro` list: no prologue (`layout_verum`), `fragVerum` at `is = k + 1`, `il = 0`. -/
noncomputable def vVerum (Ww Wc W₁ T s : V) : V :=
  fragVerum W₁ T (len (memberList s) + 1) 0 (memTop Ww Wc T s (^⊤ : V) 0) (setLen LAct s) (dlen TAct (verumIntro s))

noncomputable def vVerumDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y Ww Wc W₁ T s. ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧ ∃ is, is = k + 1 ∧
    ∃ vt, !qqVerumDef vt ∧ ∃ iv, !memTopDef iv Ww Wc T s vt 0 ∧
    ∃ Ls, !(setLenDef LAct) Ls s ∧ ∃ d, !verumIntroGraph d s ∧ ∃ n, !(dlenDef TAct) n d ∧
    !fragVerumDef y W₁ T is 0 iv Ls n”

instance vVerum_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → V ↦ vVerum (v 0) (v 1) (v 2) (v 3) (v 4)) vVerumDef := .mk fun v ↦ by
  simp [vVerumDef, vVerum, memberList_defined.iff, memTop_defined.iff, setLen_defined.iff, dlen_defined.iff,
    fragVerum_defined.iff, numeral_eq_natCast]
instance vVerum_definable :
    𝚺₁.DefinableFunction (fun v : Fin 5 → V ↦ vVerum (v 0) (v 1) (v 2) (v 3) (v 4)) := vVerum_defined.to_definable

/-- The `andIntro` list. Block 1: `proIns s p 0 ip₀` (`σ₁ = 1 + proSig (insert p s)`), `L₁`, `postIns` at the child's
chain top `&(k₁ + 1 + s₁)` and the insert object `&(proSig (insert p s) + s₁)`; `τ₁ = σ₁ + s₁ + 2`. Block 2 the same
for `q` with the parent at `τ₁`; `τ = τ₁ + τ₂`. Then `nodeAnd` with the parent at `τ`, the block-1 facts moved by `τ₂`. -/
noncomputable def vAnd (Ww Wl Wc W₁ W T s p q dp dq L₁ L₂ : V) : V :=
  appendV (proIns Ww Wl Wc W T s p 0 (memTop Ww Wc T s (p ^⋏ q) 0 + descCountF Ww 0 q + 1))
  (appendV L₁
  (appendV (postIns W (len (memberList (insert p s)) + 1 + shiftsV L₁) (proSig Ww Wl Wc W T (insert p s) + shiftsV L₁)
      (dlen TAct dp))
  (appendV (proIns Ww Wl Wc W T s q (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2)
      (memTop Ww Wc T s (p ^⋏ q) 0 + 1 + (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2)))
  (appendV L₂
  (appendV (postIns W (len (memberList (insert q s)) + 1 + shiftsV L₂) (proSig Ww Wl Wc W T (insert q s) + shiftsV L₂)
      (dlen TAct dq))
    (nodeAnd W₁ T
      (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2 + (1 + proSig Ww Wl Wc W T (insert q s) + shiftsV L₂ + 2) +
        (len (memberList s) + 1))
      (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2 + (1 + proSig Ww Wl Wc W T (insert q s) + shiftsV L₂ + 2))
      (memTop Ww Wc T s (p ^⋏ q) 0 +
        (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2 + (1 + proSig Ww Wl Wc W T (insert q s) + shiftsV L₂ + 2)))
      (memTop Ww Wc T s (p ^⋏ q) 0 + descCountF Ww 0 q + 1 +
        (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2 + (1 + proSig Ww Wl Wc W T (insert q s) + shiftsV L₂ + 2)))
      (memTop Ww Wc T s (p ^⋏ q) 0 + 1 +
        (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2 + (1 + proSig Ww Wl Wc W T (insert q s) + shiftsV L₂ + 2)))
      (1 + (1 + proSig Ww Wl Wc W T (insert q s) + shiftsV L₂ + 2)) 1
      (proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2 + (1 + proSig Ww Wl Wc W T (insert q s) + shiftsV L₂ + 2))
      (proSig Ww Wl Wc W T (insert q s) + shiftsV L₂ + 2)
      (1 + proSig Ww Wl Wc W T (insert q s) + shiftsV L₂ + 2) 0
      (setLen LAct s) (dlen TAct dp) (dlen TAct dq) (dlen TAct (andIntro s p q dp dq))))))))

noncomputable def vAndDef : 𝚺₁.Semisentence 14 := .mkSigma
  “y Ww Wl Wc W₁ W T s p q dp dq L₁ L₂.
    ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧
    ∃ r, !qqAndDef r p q ∧ ∃ ir₀, !memTopDef ir₀ Ww Wc T s r 0 ∧ ∃ cq, !descCountFDef cq Ww 0 q ∧
    ∃ ip₀, ip₀ = ir₀ + cq + 1 ∧ ∃ iq₀, iq₀ = ir₀ + 1 ∧
    ∃ c₁, !insertDef c₁ p s ∧ ∃ xs₁, !memberListDef xs₁ c₁ ∧ ∃ k₁, !lenDef k₁ xs₁ ∧ ∃ σ₁, !proSigDef σ₁ Ww Wl Wc W T c₁ ∧
    ∃ c₂, !insertDef c₂ q s ∧ ∃ xs₂, !memberListDef xs₂ c₂ ∧ ∃ k₂, !lenDef k₂ xs₂ ∧ ∃ σ₂, !proSigDef σ₂ Ww Wl Wc W T c₂ ∧
    ∃ s₁, !shiftsVDef s₁ L₁ ∧ ∃ s₂, !shiftsVDef s₂ L₂ ∧
    ∃ m₁, !(dlenDef TAct) m₁ dp ∧ ∃ m₂, !(dlenDef TAct) m₂ dq ∧ ∃ d, !andIntroGraph d s p q dp dq ∧ ∃ n, !(dlenDef TAct) n d ∧
    ∃ Ls, !(setLenDef LAct) Ls s ∧
    ∃ τ₁, τ₁ = 1 + σ₁ + s₁ + 2 ∧ ∃ τ₂, τ₂ = 1 + σ₂ + s₂ + 2 ∧ ∃ τ, τ = τ₁ + τ₂ ∧
    ∃ P₁, !proInsDef P₁ Ww Wl Wc W T s p 0 ip₀ ∧
    ∃ a₁, a₁ = k₁ + 1 + s₁ ∧ ∃ b₁, b₁ = σ₁ + s₁ ∧ ∃ Q₁, !postInsDef Q₁ W a₁ b₁ m₁ ∧
    ∃ iq₁, iq₁ = iq₀ + τ₁ ∧ ∃ P₂, !proInsDef P₂ Ww Wl Wc W T s q τ₁ iq₁ ∧
    ∃ a₂, a₂ = k₂ + 1 + s₂ ∧ ∃ b₂, b₂ = σ₂ + s₂ ∧ ∃ Q₂, !postInsDef Q₂ W a₂ b₂ m₂ ∧
    ∃ is, is = τ + (k + 1) ∧ ∃ ir, ir = ir₀ + τ ∧ ∃ ip, ip = ip₀ + τ ∧ ∃ iq, iq = iq₀ + τ ∧ ∃ id₁, id₁ = 1 + τ₂ ∧
    ∃ icp, icp = σ₁ + s₁ + 2 + τ₂ ∧ ∃ icq, icq = σ₂ + s₂ + 2 ∧
    ∃ Nd, !nodeAndDef Nd W₁ T is τ ir ip iq id₁ 1 icp icq τ₂ 0 Ls m₁ m₂ n ∧
    ∃ r₆, !appendVDef r₆ Q₂ Nd ∧ ∃ r₅, !appendVDef r₅ L₂ r₆ ∧ ∃ r₄, !appendVDef r₄ P₂ r₅ ∧ ∃ r₃, !appendVDef r₃ Q₁ r₄ ∧
    ∃ r₂, !appendVDef r₂ L₁ r₃ ∧ !appendVDef y P₁ r₂”

set_option maxHeartbeats 2000000 in
instance vAnd_defined :
    𝚺₁.DefinedFunction (fun v : Fin 13 → V ↦ vAnd (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12))
      vAndDef := .mk fun v ↦ by
  simp [vAndDef, vAnd, memberList_defined.iff, memTop_defined.iff, descCountF_defined.iff, proSig_defined.iff,
    shiftsV_defined.iff, dlen_defined.iff, setLen_defined.iff, proIns_defined.iff, postIns_defined.iff,
    nodeAnd_defined.iff, appendV_defined.iff, numeral_eq_natCast]
instance vAnd_definable :
    𝚺₁.DefinableFunction (fun v : Fin 13 → V ↦ vAnd (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12)) :=
  vAnd_defined.to_definable

/-- The `orIntro` list: `proOr` (`σ = 1 + proSig (insert q s) + (1 + proSig c)`, `c = insert p (insert q s)`), `L'`,
`postIns`, `nodeOr` with `icq = proSig (insert q s) + (1 + proSig c) + s' + 2`, `ic = proSig c + s' + 2`. -/
noncomputable def vOr (Ww Wl Wc W₁ W T s p q d' L' : V) : V :=
  appendV (proOr Ww Wl Wc W T s p q 0 (memTop Ww Wc T s (p ^⋎ q) 0 + descCountF Ww 0 q + 1) (memTop Ww Wc T s (p ^⋎ q) 0 + 1))
  (appendV L'
  (appendV (postIns W (len (memberList (insert p (insert q s))) + 1 + shiftsV L')
      (proSig Ww Wl Wc W T (insert p (insert q s)) + shiftsV L') (dlen TAct d'))
    (nodeOr W₁ T
      (1 + proSig Ww Wl Wc W T (insert q s) + (1 + proSig Ww Wl Wc W T (insert p (insert q s))) + shiftsV L' + 2 +
        (len (memberList s) + 1))
      (1 + proSig Ww Wl Wc W T (insert q s) + (1 + proSig Ww Wl Wc W T (insert p (insert q s))) + shiftsV L' + 2)
      (memTop Ww Wc T s (p ^⋎ q) 0 +
        (1 + proSig Ww Wl Wc W T (insert q s) + (1 + proSig Ww Wl Wc W T (insert p (insert q s))) + shiftsV L' + 2))
      (memTop Ww Wc T s (p ^⋎ q) 0 + descCountF Ww 0 q + 1 +
        (1 + proSig Ww Wl Wc W T (insert q s) + (1 + proSig Ww Wl Wc W T (insert p (insert q s))) + shiftsV L' + 2))
      (memTop Ww Wc T s (p ^⋎ q) 0 + 1 +
        (1 + proSig Ww Wl Wc W T (insert q s) + (1 + proSig Ww Wl Wc W T (insert p (insert q s))) + shiftsV L' + 2))
      1
      (proSig Ww Wl Wc W T (insert q s) + (1 + proSig Ww Wl Wc W T (insert p (insert q s))) + shiftsV L' + 2)
      (proSig Ww Wl Wc W T (insert p (insert q s)) + shiftsV L' + 2)
      0 (setLen LAct s) (dlen TAct d') (dlen TAct (orIntro s p q d')))))

noncomputable def vOrDef : 𝚺₁.Semisentence 12 := .mkSigma
  “y Ww Wl Wc W₁ W T s p q d' L'.
    ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧
    ∃ r, !qqOrDef r p q ∧ ∃ ir₀, !memTopDef ir₀ Ww Wc T s r 0 ∧ ∃ cq, !descCountFDef cq Ww 0 q ∧
    ∃ ip₀, ip₀ = ir₀ + cq + 1 ∧ ∃ iq₀, iq₀ = ir₀ + 1 ∧
    ∃ cq', !insertDef cq' q s ∧ ∃ σq, !proSigDef σq Ww Wl Wc W T cq' ∧
    ∃ c, !insertDef c p cq' ∧ ∃ xsc, !memberListDef xsc c ∧ ∃ kc, !lenDef kc xsc ∧ ∃ σc, !proSigDef σc Ww Wl Wc W T c ∧
    ∃ s', !shiftsVDef s' L' ∧ ∃ m₁, !(dlenDef TAct) m₁ d' ∧ ∃ d, !orIntroGraph d s p q d' ∧ ∃ n, !(dlenDef TAct) n d ∧
    ∃ Ls, !(setLenDef LAct) Ls s ∧
    ∃ σ, σ = 1 + σq + (1 + σc) ∧ ∃ τ, τ = σ + s' + 2 ∧
    ∃ P, !proOrDef P Ww Wl Wc W T s p q 0 ip₀ iq₀ ∧
    ∃ a, a = kc + 1 + s' ∧ ∃ b, b = σc + s' ∧ ∃ Q, !postInsDef Q W a b m₁ ∧
    ∃ is, is = τ + (k + 1) ∧ ∃ ir, ir = ir₀ + τ ∧ ∃ ip, ip = ip₀ + τ ∧ ∃ iq, iq = iq₀ + τ ∧
    ∃ icq, icq = σq + (1 + σc) + s' + 2 ∧ ∃ ic, ic = σc + s' + 2 ∧
    ∃ Nd, !nodeOrDef Nd W₁ T is τ ir ip iq 1 icq ic 0 Ls m₁ n ∧
    ∃ r₃, !appendVDef r₃ Q Nd ∧ ∃ r₂, !appendVDef r₂ L' r₃ ∧ !appendVDef y P r₂”

set_option maxHeartbeats 2000000 in
instance vOr_defined :
    𝚺₁.DefinedFunction (fun v : Fin 11 → V ↦ vOr (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10))
      vOrDef := .mk fun v ↦ by
  simp [vOrDef, vOr, memberList_defined.iff, memTop_defined.iff, descCountF_defined.iff, proSig_defined.iff,
    shiftsV_defined.iff, dlen_defined.iff, setLen_defined.iff, proOr_defined.iff, postIns_defined.iff,
    nodeOr_defined.iff, appendV_defined.iff, numeral_eq_natCast]
instance vOr_definable :
    𝚺₁.DefinableFunction (fun v : Fin 11 → V ↦ vOr (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10)) :=
  vOr_defined.to_definable

/-- **`fsetPiFact` of the EMPTY sequent's object `&1`** (an empty layout at `0` has `eqFactB &1 𝟎`): `emptySubsetC [𝟎]`
(`𝟎 ⊆ 𝟎`), `congSubsetL [𝟎, &1, 𝟎]` (`&1 ⊆ 𝟎`), `fsetOfSubsetZeroC [&1]`, `fsetSigmaPiC [&1]`. Shift-free; it is what
`nodeWk` needs at an empty parent, so every producer of an empty layout at `0` appends it. -/
noncomputable def emptyFsetPi (W : V) : V :=
  mkStep W 81 ?[(𝟎 : V)] ∷ mkStep W 157 ?[(𝟎 : V), ^&1, (𝟎 : V)] ∷ mkStep W 82 ?[^&1] ∷ mkStep W 84 ?[^&1] ∷ (0 : V)

noncomputable def emptyFsetPiDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y W. ∃ z, !cTVGraph z 0 ∧ ∃ f1, !qqFvarDef f1 1 ∧
    ∃ e₁, !adjoinDef e₁ z 0 ∧ ∃ s₁, !mkStepDef s₁ W 81 e₁ ∧
    ∃ e₂'', !adjoinDef e₂'' z 0 ∧ ∃ e₂', !adjoinDef e₂' f1 e₂'' ∧ ∃ e₂, !adjoinDef e₂ z e₂' ∧ ∃ s₂, !mkStepDef s₂ W 157 e₂ ∧
    ∃ e₃, !adjoinDef e₃ f1 0 ∧ ∃ s₃, !mkStepDef s₃ W 82 e₃ ∧ ∃ s₄, !mkStepDef s₄ W 84 e₃ ∧
    ∃ l₄, !adjoinDef l₄ s₄ 0 ∧ ∃ l₃, !adjoinDef l₃ s₃ l₄ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ !adjoinDef y s₁ l₂”

instance emptyFsetPi_defined : 𝚺₁-Function₁ (emptyFsetPi : V → V) via emptyFsetPiDef := .mk fun v ↦ by
  simp [emptyFsetPiDef, emptyFsetPi, mkStep_defined.iff, cTV.defined.iff, cTV_zero, numeral_eq_natCast]
instance emptyFsetPi_definable : 𝚺₁-Function₁ (emptyFsetPi : V → V) := emptyFsetPi_defined.to_definable

/-- The `wk` prologue selector: `proWk` for a nonempty child, `proWk0 ++ emptyFsetPi` for the empty child. -/
noncomputable def wkPro (Ww Wl Wc W T s c : V) : V :=
  if memberList c = 0 then appendV (proWk0 W s 0) (emptyFsetPi W) else proWk Ww Wl Wc W T s c 0

noncomputable def wkProDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y Ww Wl Wc W T s c. ∃ xs, !memberListDef xs c ∧
    (xs = 0 → ∃ P, !proWk0Def P W s 0 ∧ ∃ F, !emptyFsetPiDef F W ∧ !appendVDef y P F) ∧
    (xs ≠ 0 → !proWkDef y Ww Wl Wc W T s c 0)”

instance wkPro_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ wkPro (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) wkProDef := .mk fun v ↦ by
  simp [wkProDef, wkPro, memberList_defined.iff, proWk_defined.iff, proWk0_defined.iff, emptyFsetPi_defined.iff,
    appendV_defined.iff, numeral_eq_natCast]
  by_cases h : memberList (v 7) = 0 <;> simp [h]
instance wkPro_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ wkPro (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := wkPro_defined.to_definable

/-- The `wkRule` list: the selector, `L'`, `goalElim` at the child's sequent object `&(k_c + 1 + s')`, `nodeWk` with
`ic = k_c + 1 + s' + 2`, `id = 1`, `in₁ = 0`. -/
noncomputable def vWk (Ww Wl Wc W₁ W T s d' L' : V) : V :=
  appendV (wkPro Ww Wl Wc W T s (fstIdx d'))
  (appendV L'
  (appendV (goalElim (^&(len (memberList (fstIdx d')) + 1 + shiftsV L')) (bnum (dlen TAct d')))
    (nodeWk W₁ T (shiftsV (wkPro Ww Wl Wc W T s (fstIdx d')) + shiftsV L' + 2 + (len (memberList s) + 1))
      (shiftsV (wkPro Ww Wl Wc W T s (fstIdx d')) + shiftsV L' + 2)
      (len (memberList (fstIdx d')) + 1 + shiftsV L' + 2) 1 0 (setLen LAct s) (dlen TAct d') (dlen TAct (wkRule s d')))))

noncomputable def vWkDef : 𝚺₁.Semisentence 10 := .mkSigma
  “y Ww Wl Wc W₁ W T s d' L'.
    ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧ ∃ c, !fstIdxDef c d' ∧ ∃ xsc, !memberListDef xsc c ∧ ∃ kc, !lenDef kc xsc ∧
    ∃ P, !wkProDef P Ww Wl Wc W T s c ∧ ∃ σ, !shiftsVDef σ P ∧ ∃ s', !shiftsVDef s' L' ∧
    ∃ m₁, !(dlenDef TAct) m₁ d' ∧ ∃ d, !wkRuleGraph d s d' ∧ ∃ n, !(dlenDef TAct) n d ∧ ∃ Ls, !(setLenDef LAct) Ls s ∧
    ∃ a, a = kc + 1 + s' ∧ ∃ za, !qqFvarDef za a ∧ ∃ bm, !bnumGraph bm m₁ ∧ ∃ G, !goalElimDef G za bm ∧
    ∃ τ, τ = σ + s' + 2 ∧ ∃ is, is = τ + (k + 1) ∧ ∃ ic, ic = a + 2 ∧
    ∃ Nd, !nodeWkDef Nd W₁ T is τ ic 1 0 Ls m₁ n ∧
    ∃ r₃, !appendVDef r₃ G Nd ∧ ∃ r₂, !appendVDef r₂ L' r₃ ∧ !appendVDef y P r₂”

set_option maxHeartbeats 2000000 in
instance vWk_defined :
    𝚺₁.DefinedFunction (fun v : Fin 9 → V ↦ vWk (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) vWkDef := .mk fun v ↦ by
  simp [vWkDef, vWk, memberList_defined.iff, fstIdx_defined.iff, wkPro_defined.iff, shiftsV_defined.iff, dlen_defined.iff,
    setLen_defined.iff, bnum.defined.iff, goalElim_defined.iff, nodeWk_defined.iff, appendV_defined.iff, numeral_eq_natCast]
instance vWk_definable :
    𝚺₁.DefinableFunction (fun v : Fin 9 → V ↦ vWk (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) := vWk_defined.to_definable

/-- **The reset of the empty `shift` child** (`proShift0` leaves it at offset `1`): `layoutSteps0` (a fresh `Layout0` at
`0`, `eqFactB &1 𝟎`), then `eqSymm [&4, 𝟎]` (`𝟎 = &4`, the old `∅`-object), `eqTrans [&1, 𝟎, &4]` (`&1 = &4`),
`congSetShiftR [&6, &4, &1]` (`setShiftFact S &4 → &1 = &4 → setShiftFact S &1`, `S = &6` the parent's object). -/
noncomputable def reset0 (W : V) : V :=
  appendV (layoutSteps0 W)
    (mkStep W 42 ?[^&4, (𝟎 : V)] ∷ mkStep W 43 ?[^&1, (𝟎 : V), ^&4] ∷ mkStep W 158 ?[^&6, ^&4, ^&1] ∷ (0 : V))

noncomputable def reset0Def : 𝚺₁.Semisentence 2 := .mkSigma
  “y W. ∃ L, !layoutSteps0Def L W ∧ ∃ z, !cTVGraph z 0 ∧ ∃ f1, !qqFvarDef f1 1 ∧ ∃ f4, !qqFvarDef f4 4 ∧ ∃ f6, !qqFvarDef f6 6 ∧
    ∃ e₁', !adjoinDef e₁' z 0 ∧ ∃ e₁, !adjoinDef e₁ f4 e₁' ∧ ∃ s₁, !mkStepDef s₁ W 42 e₁ ∧
    ∃ e₂'', !adjoinDef e₂'' f4 0 ∧ ∃ e₂', !adjoinDef e₂' z e₂'' ∧ ∃ e₂, !adjoinDef e₂ f1 e₂' ∧ ∃ s₂, !mkStepDef s₂ W 43 e₂ ∧
    ∃ e₃'', !adjoinDef e₃'' f1 0 ∧ ∃ e₃', !adjoinDef e₃' f4 e₃'' ∧ ∃ e₃, !adjoinDef e₃ f6 e₃' ∧ ∃ s₃, !mkStepDef s₃ W 158 e₃ ∧
    ∃ l₃, !adjoinDef l₃ s₃ 0 ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧ !appendVDef y L l₁”

instance reset0_defined : 𝚺₁-Function₁ (reset0 : V → V) via reset0Def := .mk fun v ↦ by
  simp [reset0Def, reset0, layoutSteps0_defined.iff, mkStep_defined.iff, cTV.defined.iff, cTV_zero, appendV_defined.iff,
    numeral_eq_natCast]
instance reset0_definable : 𝚺₁-Function₁ (reset0 : V → V) := reset0_defined.to_definable

/-- The `shift` prologue selector: `proShift` for a nonempty child, `proShift0 ++ reset0` for the empty one. -/
noncomputable def shiftPro (Ww Wl Wc W T s c : V) : V :=
  if memberList c = 0 then appendV (proShift0 W 0) (appendV (reset0 W) (emptyFsetPi W)) else proShift Ww Wl Wc W T s c 0

noncomputable def shiftProDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y Ww Wl Wc W T s c. ∃ xs, !memberListDef xs c ∧
    (xs = 0 → ∃ P, !proShift0Def P W 0 ∧ ∃ R, !reset0Def R W ∧ ∃ F, !emptyFsetPiDef F W ∧ ∃ RF, !appendVDef RF R F ∧
      !appendVDef y P RF) ∧
    (xs ≠ 0 → !proShiftDef y Ww Wl Wc W T s c 0)”

instance shiftPro_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ shiftPro (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) shiftProDef := .mk fun v ↦ by
  simp [shiftProDef, shiftPro, memberList_defined.iff, proShift_defined.iff, proShift0_defined.iff, reset0_defined.iff,
    emptyFsetPi_defined.iff, appendV_defined.iff, numeral_eq_natCast]
  by_cases h : memberList (v 7) = 0 <;> simp [h]
instance shiftPro_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ shiftPro (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := shiftPro_defined.to_definable

/-- The `shiftRule` list: as `vWk` with `shiftPro` and `nodeShift`. -/
noncomputable def vShift (Ww Wl Wc W₂ W T s d' L' : V) : V :=
  appendV (shiftPro Ww Wl Wc W T s (fstIdx d'))
  (appendV L'
  (appendV (goalElim (^&(len (memberList (fstIdx d')) + 1 + shiftsV L')) (bnum (dlen TAct d')))
    (nodeShift W₂ T (shiftsV (shiftPro Ww Wl Wc W T s (fstIdx d')) + shiftsV L' + 2 + (len (memberList s) + 1))
      (shiftsV (shiftPro Ww Wl Wc W T s (fstIdx d')) + shiftsV L' + 2)
      (len (memberList (fstIdx d')) + 1 + shiftsV L' + 2) 1 0 (setLen LAct s) (dlen TAct d') (dlen TAct (shiftRule s d')))))

noncomputable def vShiftDef : 𝚺₁.Semisentence 10 := .mkSigma
  “y Ww Wl Wc W₂ W T s d' L'.
    ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧ ∃ c, !fstIdxDef c d' ∧ ∃ xsc, !memberListDef xsc c ∧ ∃ kc, !lenDef kc xsc ∧
    ∃ P, !shiftProDef P Ww Wl Wc W T s c ∧ ∃ σ, !shiftsVDef σ P ∧ ∃ s', !shiftsVDef s' L' ∧
    ∃ m₁, !(dlenDef TAct) m₁ d' ∧ ∃ d, !shiftRuleGraph d s d' ∧ ∃ n, !(dlenDef TAct) n d ∧ ∃ Ls, !(setLenDef LAct) Ls s ∧
    ∃ a, a = kc + 1 + s' ∧ ∃ za, !qqFvarDef za a ∧ ∃ bm, !bnumGraph bm m₁ ∧ ∃ G, !goalElimDef G za bm ∧
    ∃ τ, τ = σ + s' + 2 ∧ ∃ is, is = τ + (k + 1) ∧ ∃ ic, ic = a + 2 ∧
    ∃ Nd, !nodeShiftDef Nd W₂ T is τ ic 1 0 Ls m₁ n ∧
    ∃ r₃, !appendVDef r₃ G Nd ∧ ∃ r₂, !appendVDef r₂ L' r₃ ∧ !appendVDef y P r₂”

set_option maxHeartbeats 2000000 in
instance vShift_defined :
    𝚺₁.DefinedFunction (fun v : Fin 9 → V ↦ vShift (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) vShiftDef := .mk
  fun v ↦ by
  simp [vShiftDef, vShift, memberList_defined.iff, fstIdx_defined.iff, shiftPro_defined.iff, shiftsV_defined.iff, dlen_defined.iff,
    setLen_defined.iff, bnum.defined.iff, goalElim_defined.iff, nodeShift_defined.iff, appendV_defined.iff, numeral_eq_natCast]
instance vShift_definable :
    𝚺₁.DefinableFunction (fun v : Fin 9 → V ↦ vShift (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) := vShift_defined.to_definable

/-- The `cut` insert selector: `proIns` for a nonempty parent, `proIns0` for the empty parent. -/
noncomputable def cutPro (Ww Wl Wc W T s p i ip : V) : V :=
  if memberList s = 0 then proIns0 Ww Wl Wc W T p i ip else proIns Ww Wl Wc W T s p i ip

noncomputable def cutProDef : 𝚺₁.Semisentence 10 := .mkSigma
  “y Ww Wl Wc W T s p i ip. ∃ xs, !memberListDef xs s ∧
    (xs = 0 → !proIns0Def y Ww Wl Wc W T p i ip) ∧ (xs ≠ 0 → !proInsDef y Ww Wl Wc W T s p i ip)”

instance cutPro_defined :
    𝚺₁.DefinedFunction (fun v : Fin 9 → V ↦ cutPro (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) cutProDef := .mk fun v ↦ by
  simp [cutProDef, cutPro, memberList_defined.iff, proIns_defined.iff, proIns0_defined.iff, numeral_eq_natCast]
  by_cases h : memberList (v 6) = 0 <;> simp [h]
instance cutPro_definable :
    𝚺₁.DefinableFunction (fun v : Fin 9 → V ↦ cutPro (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) := cutPro_defined.to_definable

/-- The `cutRule` list: `proCutPre` (`σc = mShift p + mShift (neg p)`; `p` at `ip₀ = mLen p + mShift (neg p)`, `neg p` at
`inp₀ = mLen (neg p)`), block 1 for `insert p s` (the parent at `σc`), block 2 for `insert (neg p) s` (the parent at
`σc + τ₁`), `nodeCut`. -/
noncomputable def vCut (Ww Wl Wc W₁ W T s p d₁ d₂ L₁ L₂ : V) : V :=
  appendV (proCutPre Ww Wc T p)
  (appendV (cutPro Ww Wl Wc W T s p (mShift Ww Wc T p + mShift Ww Wc T (neg LAct p)) (mLen Wc T p + mShift Ww Wc T (neg LAct p)))
  (appendV L₁
  (appendV (postIns W (len (memberList (insert p s)) + 1 + shiftsV L₁) (proSig Ww Wl Wc W T (insert p s) + shiftsV L₁)
      (dlen TAct d₁))
  (appendV (cutPro Ww Wl Wc W T s (neg LAct p)
      (mShift Ww Wc T p + mShift Ww Wc T (neg LAct p) + (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2))
      (mLen Wc T (neg LAct p) + (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2)))
  (appendV L₂
  (appendV (postIns W (len (memberList (insert (neg LAct p) s)) + 1 + shiftsV L₂)
      (proSig Ww Wl Wc W T (insert (neg LAct p) s) + shiftsV L₂) (dlen TAct d₂))
    (nodeCut W₁ T
      (mShift Ww Wc T p + mShift Ww Wc T (neg LAct p) + (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2) +
        (1 + proSig Ww Wl Wc W T (insert (neg LAct p) s) + shiftsV L₂ + 2) + (len (memberList s) + 1))
      (mShift Ww Wc T p + mShift Ww Wc T (neg LAct p) + (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2) +
        (1 + proSig Ww Wl Wc W T (insert (neg LAct p) s) + shiftsV L₂ + 2))
      (mLen Wc T p + mShift Ww Wc T (neg LAct p) + (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2) +
        (1 + proSig Ww Wl Wc W T (insert (neg LAct p) s) + shiftsV L₂ + 2))
      (mLen Wc T (neg LAct p) + (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2) +
        (1 + proSig Ww Wl Wc W T (insert (neg LAct p) s) + shiftsV L₂ + 2))
      (1 + (1 + proSig Ww Wl Wc W T (insert (neg LAct p) s) + shiftsV L₂ + 2)) 1
      (proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2 + (1 + proSig Ww Wl Wc W T (insert (neg LAct p) s) + shiftsV L₂ + 2))
      (proSig Ww Wl Wc W T (insert (neg LAct p) s) + shiftsV L₂ + 2)
      (1 + proSig Ww Wl Wc W T (insert (neg LAct p) s) + shiftsV L₂ + 2) 0
      (setLen LAct s) (dlen TAct d₁) (dlen TAct d₂) (dlen TAct (cutRule s p d₁ d₂)))))))))

noncomputable def vCutDef : 𝚺₁.Semisentence 13 := .mkSigma
  “y Ww Wl Wc W₁ W T s p d₁ d₂ L₁ L₂.
    ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧ ∃ np, !(negGraph LAct) np p ∧
    ∃ mp, !mShiftDef mp Ww Wc T p ∧ ∃ mnp, !mShiftDef mnp Ww Wc T np ∧ ∃ lp, !mLenDef lp Wc T p ∧ ∃ lnp, !mLenDef lnp Wc T np ∧
    ∃ σc, σc = mp + mnp ∧ ∃ ip₀, ip₀ = lp + mnp ∧
    ∃ c₁, !insertDef c₁ p s ∧ ∃ xs₁, !memberListDef xs₁ c₁ ∧ ∃ k₁, !lenDef k₁ xs₁ ∧ ∃ σ₁, !proSigDef σ₁ Ww Wl Wc W T c₁ ∧
    ∃ c₂, !insertDef c₂ np s ∧ ∃ xs₂, !memberListDef xs₂ c₂ ∧ ∃ k₂, !lenDef k₂ xs₂ ∧ ∃ σ₂, !proSigDef σ₂ Ww Wl Wc W T c₂ ∧
    ∃ s₁, !shiftsVDef s₁ L₁ ∧ ∃ s₂, !shiftsVDef s₂ L₂ ∧
    ∃ m₁, !(dlenDef TAct) m₁ d₁ ∧ ∃ m₂, !(dlenDef TAct) m₂ d₂ ∧ ∃ d, !cutRuleGraph d s p d₁ d₂ ∧ ∃ n, !(dlenDef TAct) n d ∧
    ∃ Ls, !(setLenDef LAct) Ls s ∧
    ∃ τ₁, τ₁ = 1 + σ₁ + s₁ + 2 ∧ ∃ τ₂, τ₂ = 1 + σ₂ + s₂ + 2 ∧ ∃ τ, τ = σc + τ₁ + τ₂ ∧
    ∃ P₀, !proCutPreDef P₀ Ww Wc T p ∧
    ∃ P₁, !cutProDef P₁ Ww Wl Wc W T s p σc ip₀ ∧
    ∃ a₁, a₁ = k₁ + 1 + s₁ ∧ ∃ b₁, b₁ = σ₁ + s₁ ∧ ∃ Q₁, !postInsDef Q₁ W a₁ b₁ m₁ ∧
    ∃ i₂, i₂ = σc + τ₁ ∧ ∃ inp₁, inp₁ = lnp + τ₁ ∧ ∃ P₂, !cutProDef P₂ Ww Wl Wc W T s np i₂ inp₁ ∧
    ∃ a₂, a₂ = k₂ + 1 + s₂ ∧ ∃ b₂, b₂ = σ₂ + s₂ ∧ ∃ Q₂, !postInsDef Q₂ W a₂ b₂ m₂ ∧
    ∃ is, is = τ + (k + 1) ∧ ∃ ip, ip = ip₀ + τ₁ + τ₂ ∧ ∃ inp, inp = lnp + τ₁ + τ₂ ∧ ∃ id₁, id₁ = 1 + τ₂ ∧
    ∃ ic₁, ic₁ = σ₁ + s₁ + 2 + τ₂ ∧ ∃ ic₂, ic₂ = σ₂ + s₂ + 2 ∧
    ∃ Nd, !nodeCutDef Nd W₁ T is τ ip inp id₁ 1 ic₁ ic₂ τ₂ 0 Ls m₁ m₂ n ∧
    ∃ r₇, !appendVDef r₇ Q₂ Nd ∧ ∃ r₆, !appendVDef r₆ L₂ r₇ ∧ ∃ r₅, !appendVDef r₅ P₂ r₆ ∧ ∃ r₄, !appendVDef r₄ Q₁ r₅ ∧
    ∃ r₃, !appendVDef r₃ L₁ r₄ ∧ ∃ r₂, !appendVDef r₂ P₁ r₃ ∧ !appendVDef y P₀ r₂”

set_option maxHeartbeats 2000000 in
instance vCut_defined :
    𝚺₁.DefinedFunction (fun v : Fin 12 → V ↦ vCut (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11))
      vCutDef := .mk fun v ↦ by
  simp [vCutDef, vCut, memberList_defined.iff, neg.defined.iff, mShift_defined.iff, mLen_defined.iff, proSig_defined.iff,
    shiftsV_defined.iff, dlen_defined.iff, setLen_defined.iff, proCutPre_defined.iff, cutPro_defined.iff, postIns_defined.iff,
    nodeCut_defined.iff, appendV_defined.iff, numeral_eq_natCast]
instance vCut_definable :
    𝚺₁.DefinableFunction (fun v : Fin 12 → V ↦ vCut (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11)) :=
  vCut_defined.to_definable

/-- The `allIntro` list: `proAll` (its shifts `σA`, the child `c = insert (free p) (setShift s)` at `0`, the insert object
at `σc = proSig c`, `free p` at `fp₀`, the `setShift` object at `iss₀`), `L'`, `postIns`, `nodeAll`. -/
noncomputable def vAll (Ww Wl Wc W₂ W T s p d' L' : V) : V :=
  appendV (proAll Ww Wl Wc W T s p 0)
  (appendV L'
  (appendV (postIns W (len (memberList (insert (free LAct p) (setShift LAct s))) + 1 + shiftsV L')
      (proSig Ww Wl Wc W T (insert (free LAct p) (setShift LAct s)) + shiftsV L') (dlen TAct d'))
    (nodeAll W₂ T
      (allCertSig Ww Wc p + (proSig Ww Wl Wc W T (setShift LAct s) + (1 + (len (memberList s) + 1) + proSig Ww Wl Wc W T s)) +
        (1 + proSig Ww Wl Wc W T (insert (free LAct p) (setShift LAct s))) + shiftsV L' + 2 + (len (memberList s) + 1))
      (allCertSig Ww Wc p + (proSig Ww Wl Wc W T (setShift LAct s) + (1 + (len (memberList s) + 1) + proSig Ww Wl Wc W T s)) +
        (1 + proSig Ww Wl Wc W T (insert (free LAct p) (setShift LAct s))) + shiftsV L' + 2)
      (memTop Ww Wc T s (^∀ p)
        (allCertSig Ww Wc p + (proSig Ww Wl Wc W T (setShift LAct s) + (1 + (len (memberList s) + 1) + proSig Ww Wl Wc W T s)) +
          (1 + proSig Ww Wl Wc W T (insert (free LAct p) (setShift LAct s))) + shiftsV L' + 2))
      (memTop Ww Wc T s (^∀ p)
        (allCertSig Ww Wc p + (proSig Ww Wl Wc W T (setShift LAct s) + (1 + (len (memberList s) + 1) + proSig Ww Wl Wc W T s)) +
          (1 + proSig Ww Wl Wc W T (insert (free LAct p) (setShift LAct s))) + shiftsV L' + 2) + 1)
      (allCf Ww Wc p + (proSig Ww Wl Wc W T (setShift LAct s) + (1 + (len (memberList s) + 1) + proSig Ww Wl Wc W T s)) + 1 +
        proSig Ww Wl Wc W T (insert (free LAct p) (setShift LAct s)) + shiftsV L' + 2)
      (0 + 1 + (len (memberList s) + 1) + proSig Ww Wl Wc W T s + 1 + proSig Ww Wl Wc W T (insert (free LAct p) (setShift LAct s)) +
        (len (memberList (setShift LAct s)) + 1) + shiftsV L' + 2)
      (proSig Ww Wl Wc W T (insert (free LAct p) (setShift LAct s)) + shiftsV L' + 2)
      1 0 (setLen LAct s) (dlen TAct d') (dlen TAct (allIntro s p d')))))

noncomputable def vAllDef : 𝚺₁.Semisentence 11 := .mkSigma
  “y Ww Wl Wc W₂ W T s p d' L'.
    ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧ ∃ fp, !(freeGraph LAct) fp p ∧ ∃ v, !(setShiftGraph LAct) v s ∧
    ∃ xsv, !memberListDef xsv v ∧ ∃ kv, !lenDef kv xsv ∧ ∃ c, !insertDef c fp v ∧ ∃ xsc, !memberListDef xsc c ∧ ∃ kc, !lenDef kc xsc ∧
    ∃ σv, !proSigDef σv Ww Wl Wc W T v ∧ ∃ σs, !proSigDef σs Ww Wl Wc W T s ∧ ∃ σc, !proSigDef σc Ww Wl Wc W T c ∧
    ∃ cA, !allCertSigDef cA Ww Wc p ∧ ∃ cf, !allCfDef cf Ww Wc p ∧ ∃ s', !shiftsVDef s' L' ∧
    ∃ m₁, !(dlenDef TAct) m₁ d' ∧ ∃ d, !allIntroGraph d s p d' ∧ ∃ n, !(dlenDef TAct) n d ∧ ∃ Ls, !(setLenDef LAct) Ls s ∧
    ∃ r, !qqAllDef r p ∧
    ∃ sSS, sSS = σv + (1 + (k + 1) + σs) ∧ ∃ σA, σA = cA + sSS + (1 + σc) ∧ ∃ τ, τ = σA + s' + 2 ∧
    ∃ P, !proAllDef P Ww Wl Wc W T s p 0 ∧
    ∃ a, a = kc + 1 + s' ∧ ∃ b, b = σc + s' ∧ ∃ Q, !postInsDef Q W a b m₁ ∧
    ∃ is, is = τ + (k + 1) ∧ ∃ ir, !memTopDef ir Ww Wc T s r τ ∧ ∃ ip, ip = ir + 1 ∧
    ∃ ifp, ifp = cf + sSS + 1 + σc + s' + 2 ∧ ∃ iss, iss = 0 + 1 + (k + 1) + σs + 1 + σc + (kv + 1) + s' + 2 ∧
    ∃ ic, ic = σc + s' + 2 ∧
    ∃ Nd, !nodeAllDef Nd W₂ T is τ ir ip ifp iss ic 1 0 Ls m₁ n ∧
    ∃ r₃, !appendVDef r₃ Q Nd ∧ ∃ r₂, !appendVDef r₂ L' r₃ ∧ !appendVDef y P r₂”

set_option maxHeartbeats 2000000 in
instance vAll_defined :
    𝚺₁.DefinedFunction (fun v : Fin 10 → V ↦ vAll (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) vAllDef := .mk
  fun v ↦ by
  simp [vAllDef, vAll, memberList_defined.iff, free.defined.iff, setShift.defined.iff, proSig_defined.iff, allCertSig_defined.iff,
    allCf_defined.iff, shiftsV_defined.iff, dlen_defined.iff, setLen_defined.iff, memTop_defined.iff, proAll_defined.iff,
    postIns_defined.iff, nodeAll_defined.iff, appendV_defined.iff, numeral_eq_natCast]
instance vAll_definable :
    𝚺₁.DefinableFunction (fun v : Fin 10 → V ↦ vAll (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) :=
  vAll_defined.to_definable

/-- The `exsIntro` list: `proExs` (shifts `exsSig + (1 + σc)`, `c = insert (substs1 t p) s`; `T̂` at `it₀`, `l` at `ilt₀`,
`PT` at `ipt₀`, the insert object at `σc`), `L'`, `postIns`, `nodeExs` with `Lt = termLen t`. -/
noncomputable def vExs (Ww Wl Wc W₂ W T s p t d' L' : V) : V :=
  appendV (proExs Ww Wl Wc W T s p t 0)
  (appendV L'
  (appendV (postIns W (len (memberList (insert (substs1 LAct t p) s)) + 1 + shiftsV L')
      (proSig Ww Wl Wc W T (insert (substs1 LAct t p) s) + shiftsV L') (dlen TAct d'))
    (nodeExs W₂ T
      (exsSig Ww Wc T s p t 0 + (1 + proSig Ww Wl Wc W T (insert (substs1 LAct t p) s)) + shiftsV L' + 2 + (len (memberList s) + 1))
      (exsSig Ww Wc T s p t 0 + (1 + proSig Ww Wl Wc W T (insert (substs1 LAct t p) s)) + shiftsV L' + 2)
      (memTop Ww Wc T s (^∃ p) (exsSig Ww Wc T s p t 0 + (1 + proSig Ww Wl Wc W T (insert (substs1 LAct t p) s)) + shiftsV L' + 2))
      (memTop Ww Wc T s (^∃ p) (exsSig Ww Wc T s p t 0 + (1 + proSig Ww Wl Wc W T (insert (substs1 LAct t p) s)) + shiftsV L' + 2) + 1)
      (exsIw Ww Wc T t p + exsSc Ww Wc T s p t 0 + 1 + 1 + proSig Ww Wl Wc W T (insert (substs1 LAct t p) s) + shiftsV L' + 2)
      (exsSc Ww Wc T s p t 0 + 1 + proSig Ww Wl Wc W T (insert (substs1 LAct t p) s) + shiftsV L' + 2)
      (proSig Ww Wl Wc W T (insert (substs1 LAct t p) s) + shiftsV L' + 2) 1
      (exsC3 Ww t p + exsSc Ww Wc T s p t 0 + 1 + proSig Ww Wl Wc W T (insert (substs1 LAct t p) s) + shiftsV L' + 2) 0
      (setLen LAct s) (termLen LAct t) (dlen TAct d') (dlen TAct (exsIntro s p t d')))))

noncomputable def vExsDef : 𝚺₁.Semisentence 12 := .mkSigma
  “y Ww Wl Wc W₂ W T s p t d' L'.
    ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧ ∃ pt, !(substs1Graph LAct) pt t p ∧ ∃ c, !insertDef c pt s ∧
    ∃ xsc, !memberListDef xsc c ∧ ∃ kc, !lenDef kc xsc ∧ ∃ σc, !proSigDef σc Ww Wl Wc W T c ∧
    ∃ eS, !exsSigDef eS Ww Wc T s p t 0 ∧ ∃ eIw, !exsIwDef eIw Ww Wc T t p ∧ ∃ eSc, !exsScDef eSc Ww Wc T s p t 0 ∧
    ∃ eC3, !exsC3Def eC3 Ww t p ∧ ∃ s', !shiftsVDef s' L' ∧
    ∃ m₁, !(dlenDef TAct) m₁ d' ∧ ∃ d, !exsIntroGraph d s p t d' ∧ ∃ n, !(dlenDef TAct) n d ∧ ∃ Ls, !(setLenDef LAct) Ls s ∧
    ∃ lt, !(termLenGraph LAct) lt t ∧ ∃ r, !qqExsDef r p ∧
    ∃ σE, σE = eS + (1 + σc) ∧ ∃ τ, τ = σE + s' + 2 ∧
    ∃ P, !proExsDef P Ww Wl Wc W T s p t 0 ∧
    ∃ a, a = kc + 1 + s' ∧ ∃ b, b = σc + s' ∧ ∃ Q, !postInsDef Q W a b m₁ ∧
    ∃ is, is = τ + (k + 1) ∧ ∃ ir, !memTopDef ir Ww Wc T s r τ ∧ ∃ ip, ip = ir + 1 ∧
    ∃ it, it = eIw + eSc + 1 + 1 + σc + s' + 2 ∧ ∃ ipt, ipt = eSc + 1 + σc + s' + 2 ∧ ∃ ic, ic = σc + s' + 2 ∧
    ∃ ilt, ilt = eC3 + eSc + 1 + σc + s' + 2 ∧
    ∃ Nd, !nodeExsDef Nd W₂ T is τ ir ip it ipt ic 1 ilt 0 Ls lt m₁ n ∧
    ∃ r₃, !appendVDef r₃ Q Nd ∧ ∃ r₂, !appendVDef r₂ L' r₃ ∧ !appendVDef y P r₂”

set_option maxHeartbeats 2000000 in
instance vExs_defined :
    𝚺₁.DefinedFunction (fun v : Fin 11 → V ↦ vExs (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10)) vExsDef := .mk
  fun v ↦ by
  simp [vExsDef, vExs, memberList_defined.iff, substs1.defined.iff, proSig_defined.iff, exsSig_defined.iff, exsIw_defined.iff,
    exsSc_defined.iff, exsC3_defined.iff, shiftsV_defined.iff, dlen_defined.iff, setLen_defined.iff, termLen.defined.iff,
    memTop_defined.iff, proExs_defined.iff, postIns_defined.iff, nodeExs_defined.iff, appendV_defined.iff, numeral_eq_natCast]
instance vExs_definable :
    𝚺₁.DefinableFunction (fun v : Fin 11 → V ↦ vExs (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10)) :=
  vExs_defined.to_definable

/-- The `axm` list: the certificate `pro` (shift-free), then `nodeAxm` at `is = k + 1`, `il = 0`, `ip = memTop s p 0`. -/
noncomputable def vAxm (Ww Wc W₂ T s p pro : V) : V :=
  appendV pro (nodeAxm W₂ T (len (memberList s) + 1) 0 (memTop Ww Wc T s p 0) (setLen LAct s) (dlen TAct (axm s p)))

noncomputable def vAxmDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y Ww Wc W₂ T s p pro. ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧ ∃ is, is = k + 1 ∧ ∃ ip, !memTopDef ip Ww Wc T s p 0 ∧
    ∃ Ls, !(setLenDef LAct) Ls s ∧ ∃ d, !axmGraph d s p ∧ ∃ n, !(dlenDef TAct) n d ∧
    ∃ F, !nodeAxmDef F W₂ T is 0 ip Ls n ∧ !appendVDef y pro F”

instance vAxm_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ vAxm (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) vAxmDef := .mk fun v ↦ by
  simp [vAxmDef, vAxm, memberList_defined.iff, memTop_defined.iff, setLen_defined.iff, dlen_defined.iff, nodeAxm_defined.iff,
    appendV_defined.iff, numeral_eq_natCast]
instance vAxm_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ vAxm (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := vAxm_defined.to_definable

end assemblers

/-! ## 6. `VerifyGraph'` — the Δ₁ fixpoint on the key `⟪ρ, L⟫` with COMPUTED lists

Parameters: the piece tables `Ww Wl Wc W₁ W₂ W` (walk, layout, cert, frag1, frag2, prologue), the numeral table
`T`, and the `axm` certificate table `A` (§3). Ten clauses, one per node tag; every child pair `⟪d', L'⟫` is
referenced through `C` with the bound `L' ≤ L` (`le_appendV_mid`: the child's list is spliced into the node's), so
`StrongFinite` holds exactly as in `Verify.lean` §3. -/

namespace Verify2

def Phi (Ww Wl Wc W₁ W₂ W T A : V) (C : Set V) (pr : V) : Prop :=
  ∃ d ≤ pr, ∃ L ≤ pr, pr = ⟪d, L⟫ ∧
  (
  (∃ s < d, ∃ p < d, d = axL s p ∧ L = vAxL Ww Wc W₁ T s p) ∨
  (∃ s < d, d = verumIntro s ∧ L = vVerum Ww Wc W₁ T s) ∨
  (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d, d = andIntro s p q dp dq ∧
    ∃ L₁ ≤ L, ⟪dp, L₁⟫ ∈ C ∧ ∃ L₂ ≤ L, ⟪dq, L₂⟫ ∈ C ∧ L = vAnd Ww Wl Wc W₁ W T s p q dp dq L₁ L₂) ∨
  (∃ s < d, ∃ p < d, ∃ q < d, ∃ d' < d, d = orIntro s p q d' ∧
    ∃ L' ≤ L, ⟪d', L'⟫ ∈ C ∧ L = vOr Ww Wl Wc W₁ W T s p q d' L') ∨
  (∃ s < d, ∃ p < d, ∃ d' < d, d = allIntro s p d' ∧
    ∃ L' ≤ L, ⟪d', L'⟫ ∈ C ∧ L = vAll Ww Wl Wc W₂ W T s p d' L') ∨
  (∃ s < d, ∃ p < d, ∃ t < d, ∃ d' < d, d = exsIntro s p t d' ∧
    ∃ L' ≤ L, ⟪d', L'⟫ ∈ C ∧ L = vExs Ww Wl Wc W₂ W T s p t d' L') ∨
  (∃ s < d, ∃ d' < d, d = wkRule s d' ∧ ∃ L' ≤ L, ⟪d', L'⟫ ∈ C ∧ L = vWk Ww Wl Wc W₁ W T s d' L') ∨
  (∃ s < d, ∃ d' < d, d = shiftRule s d' ∧ ∃ L' ≤ L, ⟪d', L'⟫ ∈ C ∧ L = vShift Ww Wl Wc W₂ W T s d' L') ∨
  (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d, d = cutRule s p d₁ d₂ ∧
    ∃ L₁ ≤ L, ⟪d₁, L₁⟫ ∈ C ∧ ∃ L₂ ≤ L, ⟪d₂, L₂⟫ ∈ C ∧ L = vCut Ww Wl Wc W₁ W T s p d₁ d₂ L₁ L₂) ∨
  (∃ s < d, ∃ p < d, d = axm s p ∧ ∃ pro ≤ L, ⟪p, memTop Ww Wc T s p 0, pro⟫ ∈ A ∧ L = vAxm Ww Wc W₂ T s p pro) )

noncomputable def blueprint : Fixpoint.Blueprint 8 := ⟨.mkDelta
  (.mkSigma “pr C Ww Wl Wc W₁ W₂ W T A.
    ∃ d <⁺ pr, ∃ L <⁺ pr, !pairDef pr d L ∧
    (
      (∃ s < d, ∃ p < d, !axLGraph d s p ∧ ∃ F, !vAxLDef F Ww Wc W₁ T s p ∧ L = F) ∨
      (∃ s < d, !verumIntroGraph d s ∧ ∃ F, !vVerumDef F Ww Wc W₁ T s ∧ L = F) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d, !andIntroGraph d s p q dp dq ∧
        ∃ L₁ <⁺ L, :⟪dp, L₁⟫:∈ C ∧ ∃ L₂ <⁺ L, :⟪dq, L₂⟫:∈ C ∧ ∃ F, !vAndDef F Ww Wl Wc W₁ W T s p q dp dq L₁ L₂ ∧ L = F) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ d' < d, !orIntroGraph d s p q d' ∧
        ∃ L' <⁺ L, :⟪d', L'⟫:∈ C ∧ ∃ F, !vOrDef F Ww Wl Wc W₁ W T s p q d' L' ∧ L = F) ∨
      (∃ s < d, ∃ p < d, ∃ d' < d, !allIntroGraph d s p d' ∧
        ∃ L' <⁺ L, :⟪d', L'⟫:∈ C ∧ ∃ F, !vAllDef F Ww Wl Wc W₂ W T s p d' L' ∧ L = F) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ d' < d, !exsIntroGraph d s p t d' ∧
        ∃ L' <⁺ L, :⟪d', L'⟫:∈ C ∧ ∃ F, !vExsDef F Ww Wl Wc W₂ W T s p t d' L' ∧ L = F) ∨
      (∃ s < d, ∃ d' < d, !wkRuleGraph d s d' ∧ ∃ L' <⁺ L, :⟪d', L'⟫:∈ C ∧ ∃ F, !vWkDef F Ww Wl Wc W₁ W T s d' L' ∧ L = F) ∨
      (∃ s < d, ∃ d' < d, !shiftRuleGraph d s d' ∧ ∃ L' <⁺ L, :⟪d', L'⟫:∈ C ∧ ∃ F, !vShiftDef F Ww Wl Wc W₂ W T s d' L' ∧ L = F) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d, !cutRuleGraph d s p d₁ d₂ ∧
        ∃ L₁ <⁺ L, :⟪d₁, L₁⟫:∈ C ∧ ∃ L₂ <⁺ L, :⟪d₂, L₂⟫:∈ C ∧ ∃ F, !vCutDef F Ww Wl Wc W₁ W T s p d₁ d₂ L₁ L₂ ∧ L = F) ∨
      (∃ s < d, ∃ p < d, !axmGraph d s p ∧ ∃ pro <⁺ L, ∃ ip, !memTopDef ip Ww Wc T s p 0 ∧ ∃ e₁, !pairDef e₁ ip pro ∧
        ∃ e, !pairDef e p e₁ ∧ e ∈ A ∧ ∃ F, !vAxmDef F Ww Wc W₂ T s p pro ∧ L = F) )”)
  (.mkPi “pr C Ww Wl Wc W₁ W₂ W T A.
    ∃ d <⁺ pr, ∃ L <⁺ pr, !pairDef pr d L ∧
    (
      (∃ s < d, ∃ p < d, !axLGraph d s p ∧ ∀ F, !vAxLDef F Ww Wc W₁ T s p → L = F) ∨
      (∃ s < d, !verumIntroGraph d s ∧ ∀ F, !vVerumDef F Ww Wc W₁ T s → L = F) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d, !andIntroGraph d s p q dp dq ∧
        ∃ L₁ <⁺ L, :⟪dp, L₁⟫:∈ C ∧ ∃ L₂ <⁺ L, :⟪dq, L₂⟫:∈ C ∧ ∀ F, !vAndDef F Ww Wl Wc W₁ W T s p q dp dq L₁ L₂ → L = F) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ d' < d, !orIntroGraph d s p q d' ∧
        ∃ L' <⁺ L, :⟪d', L'⟫:∈ C ∧ ∀ F, !vOrDef F Ww Wl Wc W₁ W T s p q d' L' → L = F) ∨
      (∃ s < d, ∃ p < d, ∃ d' < d, !allIntroGraph d s p d' ∧
        ∃ L' <⁺ L, :⟪d', L'⟫:∈ C ∧ ∀ F, !vAllDef F Ww Wl Wc W₂ W T s p d' L' → L = F) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ d' < d, !exsIntroGraph d s p t d' ∧
        ∃ L' <⁺ L, :⟪d', L'⟫:∈ C ∧ ∀ F, !vExsDef F Ww Wl Wc W₂ W T s p t d' L' → L = F) ∨
      (∃ s < d, ∃ d' < d, !wkRuleGraph d s d' ∧ ∃ L' <⁺ L, :⟪d', L'⟫:∈ C ∧ ∀ F, !vWkDef F Ww Wl Wc W₁ W T s d' L' → L = F) ∨
      (∃ s < d, ∃ d' < d, !shiftRuleGraph d s d' ∧ ∃ L' <⁺ L, :⟪d', L'⟫:∈ C ∧ ∀ F, !vShiftDef F Ww Wl Wc W₂ W T s d' L' → L = F) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d, !cutRuleGraph d s p d₁ d₂ ∧
        ∃ L₁ <⁺ L, :⟪d₁, L₁⟫:∈ C ∧ ∃ L₂ <⁺ L, :⟪d₂, L₂⟫:∈ C ∧ ∀ F, !vCutDef F Ww Wl Wc W₁ W T s p d₁ d₂ L₁ L₂ → L = F) ∨
      (∃ s < d, ∃ p < d, !axmGraph d s p ∧ ∃ pro <⁺ L, ∀ ip, !memTopDef ip Ww Wc T s p 0 → ∀ e₁, !pairDef e₁ ip pro →
        ∀ e, !pairDef e p e₁ → (e ∈ A ∧ ∀ F, !vAxmDef F Ww Wc W₂ T s p pro → L = F)) )”)⟩

set_option maxHeartbeats 4000000 in
noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun v ↦ Phi (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, vAxL_defined.iff, vVerum_defined.iff, vAnd_defined.iff, vOr_defined.iff, vAll_defined.iff,
        vExs_defined.iff, vWk_defined.iff, vShift_defined.iff, vCut_defined.iff, vAxm_defined.iff, memTop_defined.iff]
    · intro v
      simp [blueprint, Phi, vAxL_defined.iff, vVerum_defined.iff, vAnd_defined.iff, vOr_defined.iff, vAll_defined.iff,
        vExs_defined.iff, vWk_defined.iff, vShift_defined.iff, vCut_defined.iff, vAxm_defined.iff, memTop_defined.iff]
  monotone := by
    rintro C C' hC v pr ⟨d, hd, L, hL, rfl, h⟩
    refine ⟨d, hd, L, hL, rfl, ?_⟩
    rcases h with h | h | ⟨s, hs, p, hp, q, hq, dp, hdp, dq, hdq, he, L₁, hL₁, hm₁, L₂, hL₂, hm₂, hf⟩ |
      ⟨s, hs, p, hp, q, hq, d', hd', he, L', hL', hm, hf⟩ | ⟨s, hs, p, hp, d', hd', he, L', hL', hm, hf⟩ |
      ⟨s, hs, p, hp, t, ht, d', hd', he, L', hL', hm, hf⟩ | ⟨s, hs, d', hd', he, L', hL', hm, hf⟩ |
      ⟨s, hs, d', hd', he, L', hL', hm, hf⟩ | ⟨s, hs, p, hp, d₁, hd₁, d₂, hd₂, he, L₁, hL₁, hm₁, L₂, hL₂, hm₂, hf⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨s, hs, p, hp, q, hq, dp, hdp, dq, hdq, he, L₁, hL₁, hC hm₁, L₂, hL₂, hC hm₂, hf⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, p, hp, q, hq, d', hd', he, L', hL', hC hm, hf⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, p, hp, d', hd', he, L', hL', hC hm, hf⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, p, hp, t, ht, d', hd', he, L', hL', hC hm, hf⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, d', hd', he, L', hL', hC hm, hf⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, d', hd', he, L', hL', hC hm, hf⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, hs, p, hp, d₁, hd₁, d₂, hd₂, he, L₁, hL₁, hC hm₁, L₂, hL₂, hC hm₂, hf⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))

/-- Every referenced child pair `⟪d', L'⟫` is below `⟪d, L⟫`: `d' < d` and `L' ≤ L`. -/
instance : construction.StrongFinite V where
  strong_finite := by
    rintro C v pr ⟨d, hd, L, hL, rfl, h⟩
    refine ⟨d, hd, L, hL, rfl, ?_⟩
    have key : ∀ {d' L' : V}, d' < d → L' ≤ L → ⟪d', L'⟫ < ⟪d, L⟫ := fun hd' hL' ↦
      lt_of_lt_of_le (pair_lt_pair_left hd' _) (pair_le_pair_right _ hL')
    rcases h with h | h | ⟨s, hs, p, hp, q, hq, dp, hdp, dq, hdq, he, L₁, hL₁, hm₁, L₂, hL₂, hm₂, hf⟩ |
      ⟨s, hs, p, hp, q, hq, d', hd', he, L', hL', hm, hf⟩ | ⟨s, hs, p, hp, d', hd', he, L', hL', hm, hf⟩ |
      ⟨s, hs, p, hp, t, ht, d', hd', he, L', hL', hm, hf⟩ | ⟨s, hs, d', hd', he, L', hL', hm, hf⟩ |
      ⟨s, hs, d', hd', he, L', hL', hm, hf⟩ | ⟨s, hs, p, hp, d₁, hd₁, d₂, hd₂, he, L₁, hL₁, hm₁, L₂, hL₂, hm₂, hf⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨s, hs, p, hp, q, hq, dp, hdp, dq, hdq, he, L₁, hL₁, ⟨hm₁, key hdp hL₁⟩,
        L₂, hL₂, ⟨hm₂, key hdq hL₂⟩, hf⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, p, hp, q, hq, d', hd', he, L', hL', ⟨hm, key hd' hL'⟩, hf⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, p, hp, d', hd', he, L', hL', ⟨hm, key hd' hL'⟩, hf⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, p, hp, t, ht, d', hd', he, L', hL', ⟨hm, key hd' hL'⟩, hf⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, d', hd', he, L', hL', ⟨hm, key hd' hL'⟩, hf⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, d', hd', he, L', hL', ⟨hm, key hd' hL'⟩, hf⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, hs, p, hp, d₁, hd₁, d₂, hd₂, he, L₁, hL₁, ⟨hm₁, key hd₁ hL₁⟩, L₂, hL₂, ⟨hm₂, key hd₂ hL₂⟩, hf⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))

end Verify2

/-! ### 6.2 `VerifyGraph'` and its definability (the PACKED-parameter pattern of `BnumSteps.lean`) -/

/-- The fixpoint at the packed parameter `P = ⟪Ww, Wl, Wc, W₁, W₂, W, T, A⟫`. -/
def VPackedP (P pr : V) : Prop :=
  Verify2.construction.Fixpoint
    ![π₁ P, π₁ (π₂ P), π₁ (π₂ (π₂ P)), π₁ (π₂ (π₂ (π₂ P))), π₁ (π₂ (π₂ (π₂ (π₂ P)))),
      π₁ (π₂ (π₂ (π₂ (π₂ (π₂ P))))), π₁ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ P)))))), π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ P))))))] pr

/-- **The verification graph with computed lists**: `VerifyGraph' Ww Wl Wc W₁ W₂ W T A ρ L` — the derivation code
`ρ` (its sequent laid out at offset `0`) is verified by the list `L`, with the `axm` certificates taken from `A`. -/
def VerifyGraph' (Ww Wl Wc W₁ W₂ W T A ρ L : V) : Prop := VPackedP ⟪Ww, Wl, Wc, W₁, W₂, W, T, A⟫ ⟪ρ, L⟫

noncomputable def vPackedPDef : 𝚺₁.Semisentence 2 := .mkSigma
  “P pr. ∃ a, !pi₁Def a P ∧ ∃ r₁, !pi₂Def r₁ P ∧ ∃ b, !pi₁Def b r₁ ∧ ∃ r₂, !pi₂Def r₂ r₁ ∧ ∃ c, !pi₁Def c r₂ ∧
    ∃ r₃, !pi₂Def r₃ r₂ ∧ ∃ d, !pi₁Def d r₃ ∧ ∃ r₄, !pi₂Def r₄ r₃ ∧ ∃ e, !pi₁Def e r₄ ∧ ∃ r₅, !pi₂Def r₅ r₄ ∧
    ∃ f, !pi₁Def f r₅ ∧ ∃ r₆, !pi₂Def r₆ r₅ ∧ ∃ g, !pi₁Def g r₆ ∧ ∃ h, !pi₂Def h r₆ ∧
    !Verify2.blueprint.fixpointDef pr a b c d e f g h”

instance vPackedP_defined : 𝚺₁-Relation (VPackedP : V → V → Prop) via vPackedPDef := .mk
  fun v ↦ by
    simp [vPackedPDef, VPackedP, Verify2.construction.eval_fixpointDef]
    first
    | exact Iff.rfl
    | (constructor <;> intro h <;> convert h using 2 <;> funext i <;> fin_cases i <;> rfl)
instance vPackedP_definable : 𝚺₁-Relation (VPackedP : V → V → Prop) := vPackedP_defined.to_definable

noncomputable def verifyGraph'Def : 𝚺₁.Semisentence 10 := .mkSigma
  “Ww Wl Wc W₁ W₂ W T A ρ L. ∃ pr, !pairDef pr ρ L ∧ ∃ p₇, !pairDef p₇ T A ∧ ∃ p₆, !pairDef p₆ W p₇ ∧
    ∃ p₅, !pairDef p₅ W₂ p₆ ∧ ∃ p₄, !pairDef p₄ W₁ p₅ ∧ ∃ p₃, !pairDef p₃ Wc p₄ ∧ ∃ p₂, !pairDef p₂ Wl p₃ ∧
    ∃ P, !pairDef P Ww p₂ ∧ !vPackedPDef P pr”

instance verifyGraph'_defined :
    𝚺₁.Defined (fun v : Fin 10 → V ↦ VerifyGraph' (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9))
      verifyGraph'Def := .mk
  fun v ↦ by simp [verifyGraph'Def, vPackedP_defined.iff, VerifyGraph']
instance verifyGraph'_definable :
    𝚺₁.Definable (fun v : Fin 10 → V ↦ VerifyGraph' (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) :=
  verifyGraph'_defined.to_definable

/-! ### 6.3 Case analysis and the ten inversions -/

lemma VerifyGraph'.case_iff {Ww Wl Wc W₁ W₂ W T A ρ L : V} :
    VerifyGraph' Ww Wl Wc W₁ W₂ W T A ρ L ↔
    (
    (∃ s < ρ, ∃ p < ρ, ρ = axL s p ∧ L = vAxL Ww Wc W₁ T s p) ∨
    (∃ s < ρ, ρ = verumIntro s ∧ L = vVerum Ww Wc W₁ T s) ∨
    (∃ s < ρ, ∃ p < ρ, ∃ q < ρ, ∃ dp < ρ, ∃ dq < ρ, ρ = andIntro s p q dp dq ∧
      ∃ L₁ ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A dp L₁ ∧ ∃ L₂ ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A dq L₂ ∧
      L = vAnd Ww Wl Wc W₁ W T s p q dp dq L₁ L₂) ∨
    (∃ s < ρ, ∃ p < ρ, ∃ q < ρ, ∃ d' < ρ, ρ = orIntro s p q d' ∧
      ∃ L' ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vOr Ww Wl Wc W₁ W T s p q d' L') ∨
    (∃ s < ρ, ∃ p < ρ, ∃ d' < ρ, ρ = allIntro s p d' ∧
      ∃ L' ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vAll Ww Wl Wc W₂ W T s p d' L') ∨
    (∃ s < ρ, ∃ p < ρ, ∃ t < ρ, ∃ d' < ρ, ρ = exsIntro s p t d' ∧
      ∃ L' ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vExs Ww Wl Wc W₂ W T s p t d' L') ∨
    (∃ s < ρ, ∃ d' < ρ, ρ = wkRule s d' ∧
      ∃ L' ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vWk Ww Wl Wc W₁ W T s d' L') ∨
    (∃ s < ρ, ∃ d' < ρ, ρ = shiftRule s d' ∧
      ∃ L' ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vShift Ww Wl Wc W₂ W T s d' L') ∨
    (∃ s < ρ, ∃ p < ρ, ∃ d₁ < ρ, ∃ d₂ < ρ, ρ = cutRule s p d₁ d₂ ∧
      ∃ L₁ ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A d₁ L₁ ∧ ∃ L₂ ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A d₂ L₂ ∧
      L = vCut Ww Wl Wc W₁ W T s p d₁ d₂ L₁ L₂) ∨
    (∃ s < ρ, ∃ p < ρ, ρ = axm s p ∧ ∃ pro ≤ L, ⟪p, memTop Ww Wc T s p 0, pro⟫ ∈ A ∧ L = vAxm Ww Wc W₂ T s p pro) ) := by
  unfold VerifyGraph' VPackedP
  simp only [pi₁_pair, pi₂_pair]
  rw [Verify2.construction.case]
  show Verify2.Phi _ _ _ _ _ _ _ _ _ _ ↔ _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Verify2.Phi]
  constructor
  · rintro ⟨d, _, L', _, hpr, h⟩
    obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp hpr
    exact h
  · intro h
    exact ⟨ρ, by simp, L, by simp, rfl, h⟩

section inversion

attribute [local simp] axL verumIntro andIntro orIntro allIntro exsIntro wkRule shiftRule cutRule axm

variable {Ww Wl Wc W₁ W₂ W T A : V}

lemma VerifyGraph'.axL_iff {s p L : V} :
    VerifyGraph' Ww Wl Wc W₁ W₂ W T A (axL s p) L ↔ L = vAxL Ww Wc W₁ T s p := by
  rw [VerifyGraph'.case_iff]
  simp
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [axL] using seq_lt_axL s p, by simpa [axL] using arity_lt_axL s p, h⟩

lemma VerifyGraph'.verumIntro_iff {s L : V} :
    VerifyGraph' Ww Wl Wc W₁ W₂ W T A (verumIntro s) L ↔ L = vVerum Ww Wc W₁ T s := by
  rw [VerifyGraph'.case_iff]
  simp
  intros
  simpa [verumIntro] using seq_lt_verumIntro s

lemma VerifyGraph'.andIntro_iff {s p q dp dq L : V} :
    VerifyGraph' Ww Wl Wc W₁ W₂ W T A (andIntro s p q dp dq) L ↔
    ∃ L₁ ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A dp L₁ ∧ ∃ L₂ ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A dq L₂ ∧
      L = vAnd Ww Wl Wc W₁ W T s p q dp dq L₁ L₂ := by
  rw [VerifyGraph'.case_iff]
  simp
  constructor
  · rintro ⟨-, -, -, -, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [andIntro] using seq_lt_andIntro s p q dp dq, by simpa [andIntro] using p_lt_andIntro s p q dp dq,
      by simpa [andIntro] using q_lt_andIntro s p q dp dq, by simpa [andIntro] using dp_lt_andIntro s p q dp dq,
      by simpa [andIntro] using dq_lt_andIntro s p q dp dq, h⟩

lemma VerifyGraph'.orIntro_iff {s p q d' L : V} :
    VerifyGraph' Ww Wl Wc W₁ W₂ W T A (orIntro s p q d') L ↔
    ∃ L' ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vOr Ww Wl Wc W₁ W T s p q d' L' := by
  rw [VerifyGraph'.case_iff]
  simp
  constructor
  · rintro ⟨-, -, -, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [orIntro] using seq_lt_orIntro s p q d', by simpa [orIntro] using p_lt_orIntro s p q d',
      by simpa [orIntro] using q_lt_orIntro s p q d', by simpa [orIntro] using d_lt_orIntro s p q d', h⟩

lemma VerifyGraph'.allIntro_iff {s p d' L : V} :
    VerifyGraph' Ww Wl Wc W₁ W₂ W T A (allIntro s p d') L ↔
    ∃ L' ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vAll Ww Wl Wc W₂ W T s p d' L' := by
  rw [VerifyGraph'.case_iff]
  simp
  constructor
  · rintro ⟨-, -, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [allIntro] using seq_lt_allIntro s p d', by simpa [allIntro] using p_lt_allIntro s p d',
      by simpa [allIntro] using s_lt_allIntro s p d', h⟩

lemma VerifyGraph'.exsIntro_iff {s p t d' L : V} :
    VerifyGraph' Ww Wl Wc W₁ W₂ W T A (exsIntro s p t d') L ↔
    ∃ L' ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vExs Ww Wl Wc W₂ W T s p t d' L' := by
  rw [VerifyGraph'.case_iff]
  simp
  constructor
  · rintro ⟨-, -, -, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [exsIntro] using seq_lt_exsIntro s p t d', by simpa [exsIntro] using p_lt_exsIntro s p t d',
      by simpa [exsIntro] using t_lt_exsIntro s p t d', by simpa [exsIntro] using d_lt_exsIntro s p t d', h⟩

lemma VerifyGraph'.wkRule_iff {s d' L : V} :
    VerifyGraph' Ww Wl Wc W₁ W₂ W T A (wkRule s d') L ↔
    ∃ L' ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vWk Ww Wl Wc W₁ W T s d' L' := by
  rw [VerifyGraph'.case_iff]
  simp
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [wkRule] using seq_lt_wkRule s d', by simpa [wkRule] using d_lt_wkRule s d', h⟩

lemma VerifyGraph'.shiftRule_iff {s d' L : V} :
    VerifyGraph' Ww Wl Wc W₁ W₂ W T A (shiftRule s d') L ↔
    ∃ L' ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vShift Ww Wl Wc W₂ W T s d' L' := by
  rw [VerifyGraph'.case_iff]
  simp
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [shiftRule] using seq_lt_shiftRule s d', by simpa [shiftRule] using d_lt_shiftRule s d', h⟩

lemma VerifyGraph'.cutRule_iff {s p d₁ d₂ L : V} :
    VerifyGraph' Ww Wl Wc W₁ W₂ W T A (cutRule s p d₁ d₂) L ↔
    ∃ L₁ ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A d₁ L₁ ∧ ∃ L₂ ≤ L, VerifyGraph' Ww Wl Wc W₁ W₂ W T A d₂ L₂ ∧
      L = vCut Ww Wl Wc W₁ W T s p d₁ d₂ L₁ L₂ := by
  rw [VerifyGraph'.case_iff]
  simp
  constructor
  · rintro ⟨-, -, -, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [cutRule] using seq_lt_cutRule s p d₁ d₂, by simpa [cutRule] using p_lt_cutRule s p d₁ d₂,
      by simpa [cutRule] using d₁_lt_cutRule s p d₁ d₂, by simpa [cutRule] using d₂_lt_cutRule s p d₁ d₂, h⟩

lemma VerifyGraph'.axm_iff {s p L : V} :
    VerifyGraph' Ww Wl Wc W₁ W₂ W T A (axm s p) L ↔
    ∃ pro ≤ L, ⟪p, memTop Ww Wc T s p 0, pro⟫ ∈ A ∧ L = vAxm Ww Wc W₂ T s p pro := by
  rw [VerifyGraph'.case_iff]
  simp
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [axm] using seq_lt_axm s p, by simpa [axm] using p_lt_axm s p, h⟩

end inversion

/-! ## 7. Monotonicity in the certificate table and existence -/

section existence

/-- The children's lists sit inside the assembled lists (the bounds the clauses carry). -/
lemma le_vAnd_left (Ww Wl Wc W₁ W T s p q dp dq L₁ L₂ : V) : L₁ ≤ vAnd Ww Wl Wc W₁ W T s p q dp dq L₁ L₂ := by
  unfold vAnd; exact le_appendV_mid _ _ _
lemma le_vAnd_right (Ww Wl Wc W₁ W T s p q dp dq L₁ L₂ : V) : L₂ ≤ vAnd Ww Wl Wc W₁ W T s p q dp dq L₁ L₂ := by
  unfold vAnd
  exact le_trans (le_appendV_mid _ _ _) (le_trans (le_appendV_self _ _) (le_trans (le_appendV_self _ _) (le_appendV_self _ _)))
lemma le_vOr (Ww Wl Wc W₁ W T s p q d' L' : V) : L' ≤ vOr Ww Wl Wc W₁ W T s p q d' L' := by
  unfold vOr; exact le_appendV_mid _ _ _
lemma le_vAll (Ww Wl Wc W₂ W T s p d' L' : V) : L' ≤ vAll Ww Wl Wc W₂ W T s p d' L' := by
  unfold vAll; exact le_appendV_mid _ _ _
lemma le_vExs (Ww Wl Wc W₂ W T s p t d' L' : V) : L' ≤ vExs Ww Wl Wc W₂ W T s p t d' L' := by
  unfold vExs; exact le_appendV_mid _ _ _
lemma le_vWk (Ww Wl Wc W₁ W T s d' L' : V) : L' ≤ vWk Ww Wl Wc W₁ W T s d' L' := by
  unfold vWk; exact le_appendV_mid _ _ _
lemma le_vShift (Ww Wl Wc W₂ W T s d' L' : V) : L' ≤ vShift Ww Wl Wc W₂ W T s d' L' := by
  unfold vShift; exact le_appendV_mid _ _ _
lemma le_vCut_left (Ww Wl Wc W₁ W T s p d₁ d₂ L₁ L₂ : V) : L₁ ≤ vCut Ww Wl Wc W₁ W T s p d₁ d₂ L₁ L₂ := by
  unfold vCut; exact le_trans (le_appendV_mid _ _ _) (le_appendV_self _ _)
lemma le_vCut_right (Ww Wl Wc W₁ W T s p d₁ d₂ L₁ L₂ : V) : L₂ ≤ vCut Ww Wl Wc W₁ W T s p d₁ d₂ L₁ L₂ := by
  unfold vCut
  exact le_trans (le_appendV_mid _ _ _) (le_trans (le_appendV_self _ _) (le_trans (le_appendV_self _ _)
    (le_trans (le_appendV_self _ _) (le_appendV_self _ _))))
lemma le_vAxm (Ww Wc W₂ T s p pro : V) : pro ≤ vAxm Ww Wc W₂ T s p pro := by
  unfold vAxm; exact le_appendV_prefix _ _

/-- **`VerifyGraph'` is monotone in the certificate table** (by `Fixpoint.induction` on the key). -/
theorem VerifyGraph'.mono_A {Ww Wl Wc W₁ W₂ W T A A' : V} (hAA : A ⊆ A') {ρ L : V}
    (h : VerifyGraph' Ww Wl Wc W₁ W₂ W T A ρ L) : VerifyGraph' Ww Wl Wc W₁ W₂ W T A' ρ L := by
  have key : ∀ pr, VPackedP ⟪Ww, Wl, Wc, W₁, W₂, W, T, A⟫ pr → VPackedP ⟪Ww, Wl, Wc, W₁, W₂, W, T, A'⟫ pr := by
    intro pr
    unfold VPackedP
    simp only [pi₁_pair, pi₂_pair]
    apply Verify2.construction.induction (Γ := 𝚺)
      (P := fun pr ↦ Verify2.construction.Fixpoint ![Ww, Wl, Wc, W₁, W₂, W, T, A'] pr)
      (HierarchySymbol.Definable.of_iff (Q := fun v ↦ VPackedP ⟪Ww, Wl, Wc, W₁, W₂, W, T, A'⟫ (v 0))
        (by definability) (fun v ↦ by simp only [VPackedP, pi₁_pair, pi₂_pair]))
    intro C hC x hx
    rw [Verify2.construction.case]
    show Verify2.Phi _ _ _ _ _ _ _ _ _ _
    have hx' : Verify2.Phi Ww Wl Wc W₁ W₂ W T A C x := hx
    obtain ⟨d, hd, L, hL, rfl, h⟩ := hx'
    refine ⟨d, hd, L, hL, rfl, ?_⟩
    have tr : ∀ {z : V}, z ∈ C → z ∈ {z | Verify2.construction.Fixpoint ![Ww, Wl, Wc, W₁, W₂, W, T, A'] z} :=
      fun hz ↦ (hC _ hz).2
    rcases h with h | h | ⟨s, hs, p, hp, q, hq, dp, hdp, dq, hdq, he, L₁, hL₁, hm₁, L₂, hL₂, hm₂, hf⟩ |
      ⟨s, hs, p, hp, q, hq, d', hd', he, L', hL', hm, hf⟩ | ⟨s, hs, p, hp, d', hd', he, L', hL', hm, hf⟩ |
      ⟨s, hs, p, hp, t, ht, d', hd', he, L', hL', hm, hf⟩ | ⟨s, hs, d', hd', he, L', hL', hm, hf⟩ |
      ⟨s, hs, d', hd', he, L', hL', hm, hf⟩ | ⟨s, hs, p, hp, d₁, hd₁, d₂, hd₂, he, L₁, hL₁, hm₁, L₂, hL₂, hm₂, hf⟩ |
      ⟨s, hs, p, hp, he, pro, hpro, hmem, hf⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨s, hs, p, hp, q, hq, dp, hdp, dq, hdq, he, L₁, hL₁, tr hm₁, L₂, hL₂, tr hm₂, hf⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, p, hp, q, hq, d', hd', he, L', hL', tr hm, hf⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, p, hp, d', hd', he, L', hL', tr hm, hf⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, p, hp, t, ht, d', hd', he, L', hL', tr hm, hf⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, d', hd', he, L', hL', tr hm, hf⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, d', hd', he, L', hL', tr hm, hf⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, hs, p, hp, d₁, hd₁, d₂, hd₂, he, L₁, hL₁, tr hm₁, L₂, hL₂, tr hm₂, hf⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨s, hs, p, hp, he, pro, hpro, hAA hmem, hf⟩))))))))
  exact key _ h

lemma subset_cup_left (A A' : V) : A ⊆ A ∪ A' := fun x hx ↦ mem_cup_iff.mpr (Or.inl hx)
lemma subset_cup_right (A A' : V) : A' ⊆ A ∪ A' := fun x hx ↦ mem_cup_iff.mpr (Or.inr hx)

/-- The E-room passes to a child: `dlen d' + 1 ≤ dlen ρ`. -/
lemma eroom_child {Cv E a b : V} (h : Cv + 6 * a + 1 ≤ E) (hab : b + 1 ≤ a) : Cv + 6 * b + 1 ≤ E :=
  le_trans (add_le_add (add_le_add (le_refl Cv) (mul_le_mul_of_nonneg_left (le_trans le_self_add hab) zero_le)) (le_refl 1)) h

set_option maxHeartbeats 2000000 in
/-- **Every internal derivation has a verification list** (per model), with a certificate table `A` built from
`ProAxm`'s case (i) and the oracle `AxmIndOracleC` (case (ii), NOT discharged): by `Derivation.induction1 𝚺`, the
children's tables united, the children's lists spliced by the assemblers; the E-room `C + 6·dlen ρ + 1 ≤ E`
is what the `axm` entries need (`memTop ≤ 6·setLen s + 1 ≤ 6·dlen ρ + 1`). -/
theorem verifyGraph'_exists : ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {tbl N E Ww Wl Wc W₁ W₂ W T ρ Cv : V} (Cind : ℕ), TableOK tbl N → ProAxmTable tbl → Ww = walkPieces → Wc = certPieces →
    Cv = ((C + Cind : ℕ) : V) → Derivation TAct ρ → Cv + 6 * dlen TAct ρ + 1 ≤ E → AxmIndOracleC tbl E Cind →
    ∃ A L : V, AxmTableOK tbl E Ww A Cv ∧ VerifyGraph' Ww Wl Wc W₁ W₂ W T A ρ L := by
  obtain ⟨C, hC⟩ := axmEntry_exists
  refine ⟨C, fun V _ _ tbl N E Ww Wl Wc W₁ W₂ W T ρ Cv Cind htbl hT hWw hWc hCv hd hE hind ↦ ?_⟩
  revert hE
  apply Derivation.induction1 𝚺 (T := TAct)
    (P := fun ρ ↦ Cv + 6 * dlen TAct ρ + 1 ≤ E → ∃ A L : V, AxmTableOK tbl E Ww A Cv ∧ VerifyGraph' Ww Wl Wc W₁ W₂ W T A ρ L)
    (by simp only [VerifyGraph']; definability) hd
  · intro s _ p _ _ _
    exact ⟨0, _, axmTableOK_empty _ _ _ _, VerifyGraph'.axL_iff.mpr rfl⟩
  · intro s _ _ _
    exact ⟨0, _, axmTableOK_empty _ _ _ _, VerifyGraph'.verumIntro_iff.mpr rfl⟩
  · intro s _ p q dp dq hpq hdp hdq ih₁ ih₂ hE
    have hD : Derivation TAct (andIntro s p q dp dq) := Derivation.andIntro hpq hdp hdq
    obtain ⟨A₁, L₁, h₁, g₁⟩ := ih₁ (eroom_child hE (dlen_dp_succ_le_andIntro hD))
    obtain ⟨A₂, L₂, h₂, g₂⟩ := ih₂ (eroom_child hE (dlen_dq_succ_le_andIntro hD))
    exact ⟨A₁ ∪ A₂, _, axmTableOK_union h₁ h₂, VerifyGraph'.andIntro_iff.mpr
      ⟨L₁, le_vAnd_left _ _ _ _ _ _ _ _ _ _ _ _ _, g₁.mono_A (subset_cup_left _ _),
       L₂, le_vAnd_right _ _ _ _ _ _ _ _ _ _ _ _ _, g₂.mono_A (subset_cup_right _ _), rfl⟩⟩
  · intro s _ p q d' hpq hd' ih hE
    have hD : Derivation TAct (orIntro s p q d') := Derivation.orIntro hpq hd'
    obtain ⟨A', L', h', g'⟩ := ih (eroom_child hE (dlen_d_succ_le_orIntro hD))
    exact ⟨A', _, h', VerifyGraph'.orIntro_iff.mpr ⟨L', le_vOr _ _ _ _ _ _ _ _ _ _ _, g', rfl⟩⟩
  · intro s _ p d' hp hd' ih hE
    have hD : Derivation TAct (allIntro s p d') := Derivation.allIntro hp hd'
    obtain ⟨A', L', h', g'⟩ := ih (eroom_child hE (dlen_d_succ_le_allIntro hD))
    exact ⟨A', _, h', VerifyGraph'.allIntro_iff.mpr ⟨L', le_vAll _ _ _ _ _ _ _ _ _ _, g', rfl⟩⟩
  · intro s _ p t d' hp ht hd' ih hE
    have hD : Derivation TAct (exsIntro s p t d') := Derivation.exsIntro hp ht hd'
    obtain ⟨A', L', h', g'⟩ := ih (eroom_child hE (dlen_d_succ_le_exsIntro hD))
    exact ⟨A', _, h', VerifyGraph'.exsIntro_iff.mpr ⟨L', le_vExs _ _ _ _ _ _ _ _ _ _ _, g', rfl⟩⟩
  · intro s hs d' hsub hd' ih hE
    have hD : Derivation TAct (wkRule s d') := Derivation.wkRule hs hsub ⟨rfl, hd'⟩
    obtain ⟨A', L', h', g'⟩ := ih (eroom_child hE (dlen_d_succ_le_wkRule hD))
    exact ⟨A', _, h', VerifyGraph'.wkRule_iff.mpr ⟨L', le_vWk _ _ _ _ _ _ _ _ _, g', rfl⟩⟩
  · rintro s _ d' rfl hd' ih hE
    have hD : Derivation TAct (shiftRule (setShift LAct (fstIdx d')) d') := Derivation.shiftRule ⟨rfl, hd'⟩
    obtain ⟨A', L', h', g'⟩ := ih (eroom_child hE (dlen_d_succ_le_shiftRule hD))
    exact ⟨A', _, h', VerifyGraph'.shiftRule_iff.mpr ⟨L', le_vShift _ _ _ _ _ _ _ _ _, g', rfl⟩⟩
  · intro s _ p d₁ d₂ hd₁ hd₂ ih₁ ih₂ hE
    have hD : Derivation TAct (cutRule s p d₁ d₂) := Derivation.cutRule hd₁ hd₂
    obtain ⟨A₁, L₁, h₁, g₁⟩ := ih₁ (eroom_child hE (dlen_d₁_succ_le_cutRule hD))
    obtain ⟨A₂, L₂, h₂, g₂⟩ := ih₂ (eroom_child hE (dlen_d₂_succ_le_cutRule hD))
    exact ⟨A₁ ∪ A₂, _, axmTableOK_union h₁ h₂, VerifyGraph'.cutRule_iff.mpr
      ⟨L₁, le_vCut_left _ _ _ _ _ _ _ _ _ _ _ _, g₁.mono_A (subset_cup_left _ _),
       L₂, le_vCut_right _ _ _ _ _ _ _ _ _ _ _ _, g₂.mono_A (subset_cup_right _ _), rfl⟩⟩
  · intro s hs p hp hax hE
    have hD : Derivation TAct (axm s p) := Derivation.axm hs hp hax
    have hpf : IsSemiformula LAct 0 p := hs p hp
    have hip : memTop Ww Wc T s p 0 ≤ 6 * setLen LAct s + 1 := by
      rw [hWw]
      have := memTop_le htbl hT.walkTable hWc T hs hp (le_refl (setLen LAct s)) (i := 0)
      rwa [zero_add] at this
    have hEip : ((C + Cind : ℕ) : V) + memTop Ww Wc T s p 0 ≤ E := by
      rw [← hCv]
      refine le_trans ?_ hE
      rw [dlen_axm hD]
      calc Cv + memTop Ww Wc T s p 0 ≤ Cv + (6 * setLen LAct s + 1) := add_le_add (le_refl Cv) hip
        _ = Cv + 6 * setLen LAct s + 1 := by ring
        _ ≤ Cv + 6 * (setLen LAct s + 1) + 1 := by
          exact add_le_add (add_le_add (le_refl Cv) (mul_le_mul_of_nonneg_left le_self_add zero_le)) (le_refl 1)
    obtain ⟨pro, hpro⟩ := hC V Cind htbl hT hpf hax hEip hind
    have hentry : NumInvV tbl E (dossCtx Ww p (memTop Ww Wc T s p 0)) Cv pro (axchFact (^&(memTop Ww Wc T s p 0))) := by
      subst hCv hWw
      exact numInv_iff_numInvV.mp hpro
    exact ⟨insert ⟪p, memTop Ww Wc T s p 0, pro⟫ (0 : V), vAxm Ww Wc W₂ T s p pro,
      axmTableOK_insert (axmTableOK_empty _ _ _ _) hentry,
      VerifyGraph'.axm_iff.mpr ⟨pro, le_vAxm _ _ _ _ _ _ _, mem_bitInsert_iff.mpr (Or.inl rfl), rfl⟩⟩

end existence

/-! ## 8. The node invariant `verifyGraph'_ok` -/

/-! ### 8.0 Small transports and the layout predicates' definability -/

section okPrelude

instance layout_definable : 𝚫₁.Definable (fun v : Fin 6 → V ↦ Layout (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := by
  unfold Layout; definability

instance layout0_definable : 𝚫₁-Relation₅ (Layout0 : V → V → V → V → V → Prop) := by
  unfold Layout0; definability

lemma shiftIterV_derFact {e : V} (he : IsSemiterm LAct 0 e) :
    ∀ c : V, shiftIterV (derFact e) c = derFact (termShiftIterV e c) := by
  intro c
  induction c using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ c ih => rw [shiftIterV_succ, ih, shift_derFact (isSemiterm_termShiftIterV he c), termShiftIterV_succ]

lemma shiftIterV_fstIdxFact {s e : V} (hs : IsSemiterm LAct 0 s) (he : IsSemiterm LAct 0 e) :
    ∀ c : V, shiftIterV (fstIdxFact s e) c = fstIdxFact (termShiftIterV s c) (termShiftIterV e c) := by
  intro c
  induction c using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ c ih =>
    rw [shiftIterV_succ, ih, shift_fstIdxFact (isSemiterm_termShiftIterV hs c) (isSemiterm_termShiftIterV he c),
      termShiftIterV_succ, termShiftIterV_succ]

lemma shiftIterV_dlenFact {e n : V} (he : IsSemiterm LAct 0 e) (hn : IsSemiterm LAct 0 n) :
    ∀ c : V, shiftIterV (dlenFact e n) c = dlenFact (termShiftIterV e c) (termShiftIterV n c) := by
  intro c
  induction c using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ c ih =>
    rw [shiftIterV_succ, ih, shift_dlenFact (isSemiterm_termShiftIterV he c) (isSemiterm_termShiftIterV hn c),
      termShiftIterV_succ, termShiftIterV_succ]

lemma one_le_len_memberList_of_mem {s x : V} (hx : x ∈ s) : 1 ≤ len (memberList s) := by
  obtain ⟨m, hm, -⟩ := mem_memberList_iff.mpr hx
  exact pos_iff_one_le.mp (lt_of_le_of_lt (zero_le) hm)

lemma eq_zero_of_memberList_eq_zero {s : V} (h : memberList s = 0) : s = 0 := by
  apply mem_ext
  intro x
  constructor
  · intro hx
    obtain ⟨m, hm, -⟩ := mem_memberList_iff.mpr hx
    rw [h] at hm; simp at hm
  · intro hx; simp at hx

end okPrelude

/-! ### 8.1 The leaves: `axL`, `verumIntro`, `axm` -/

section leaves

/-- **The `axL` list is applicable** at the node's layout (offset `0`): one eigenvariable, the goal at `&(k + 2)`. -/
theorem vAxL_ok {tbl N N' B' Wc W₁ T s p D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWc : Wc = certPieces) (hW₁ : W₁ = frag1Pieces)
    (hs : IsFormulaSet LAct s) (hp : p ∈ s) (hnp : neg LAct p ∈ s) (hsD : setLen LAct s ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 8 ≤ E) (hiE : 8 * D + 3 ≤ E) (hkE : len (memberList s) + 3 ≤ E)
    (hn : 18 * ‖setLen LAct s + 1‖ + 7 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s 0) :
    ListOK tbl E ((9 : ℕ) : V) Γ (vAxL walkPieces Wc W₁ T s p) ∧ NoDrop' (vAxL walkPieces Wc W₁ T s p) ∧
    shiftsV (vAxL walkPieces Wc W₁ T s p) = 1 ∧
    neg LAct (goalFact (^&(len (memberList s) + 1 + 1)) (bnum (dlen TAct (axL s p)))) ∈
      finalCtx Γ (vAxL walkPieces Wc W₁ T s p) := by
  have hW : WalkTable tbl := hP.walkTable
  have hD : Derivation TAct (axL s p) := Derivation.axL hs hp hnp
  have hdl : dlen TAct (axL s p) = setLen LAct s + 1 := dlen_axL hD
  obtain ⟨pok, pnd, -, psh, -, hfs, hmp, hneg, hmnp, hsl, hle⟩ :=
    proAxL_ok htbl hP htblN hWc hs hp hnp hsD hE (by rw [zero_add]; exact hiE) hΓ hLay
  simp only [zero_add] at hfs hmp hneg hmnp hsl hle
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ (proAxL walkPieces Wc T s p 0) := ⟨_, rfl⟩
  rw [← hΓ₁] at hfs hmp hneg hmnp hsl hle
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 8 htbl hΓ pok
  have hmt : memTop walkPieces Wc T s p 0 ≤ 6 * D + 1 := by
    have := memTop_le htbl hW hWc T hs hp hsD (i := 0); rwa [zero_add] at this
  have hmt' : memTop walkPieces Wc T s (neg LAct p) 0 ≤ 6 * D + 1 := by
    have := memTop_le htbl hW hWc T hs hnp hsD (i := 0); rwa [zero_add] at this
  have hE6 : 6 * D + 3 ≤ E :=
    le_trans (add_le_add (mul_le_mul_of_nonneg_right (by norm_num : (6 : V) ≤ 8) zero_le) (le_refl 3)) hiE
  have e12 : (1 : V) + 2 = 3 := by norm_num
  have hn' : 18 * ‖dlen TAct (axL s p)‖ + 7 ≤ E := by rw [hdl]; exact hn
  have hLn' : setLen LAct s + 1 ≤ dlen TAct (axL s p) := by rw [hdl]
  have h4E : (0 : V) + 4 ≤ E := by
    rw [zero_add, show (4 : V) = 1 + 3 by norm_num]
    exact le_trans (add_le_add (one_le_len_memberList_of_mem hp) (le_refl 3)) hkE
  obtain ⟨fok, fnd, fsh, -, fgoal⟩ := fragAxL_ok (E := E) (is := len (memberList s) + 1) (il := 0)
    (ip := memTop walkPieces Wc T s p 0) (inp := memTop walkPieces Wc T s (neg LAct p) 0) (L := setLen LAct s)
    (n := dlen TAct (axL s p)) htbl hP.frag1Table hW₁ htblN hΓ₁f
    (by rw [add_assoc, e12]; exact hkE) h4E
    (le_trans (add_le_add hmt (le_refl 2)) (by rw [add_assoc, e12]; exact hE6))
    (le_trans (add_le_add hmt' (le_refl 2)) (by rw [add_assoc, e12]; exact hE6))
    hn' hLn' hfs hmp hneg hmnp hsl hle
  unfold vAxL
  refine ⟨listOK_appendV (pok.mono h89) (by rw [← hΓ₁]; exact fok.mono h89), noDrop'_appendV pnd.noDrop' fnd, ?_, ?_⟩
  · rw [shiftsV_appendV, psh, fsh, zero_add]
  · rw [finalCtx_appendV, ← hΓ₁]; exact fgoal

/-- **The `verumIntro` list is applicable**. -/
theorem vVerum_ok {tbl N N' B' Wc W₁ T s D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWc : Wc = certPieces) (hW₁ : W₁ = frag1Pieces)
    (hs : IsFormulaSet LAct s) (hv : (^⊤ : V) ∈ s) (hsD : setLen LAct s ≤ D)
    (hiE : 6 * D + 3 ≤ E) (hkE : len (memberList s) + 3 ≤ E) (hn : 18 * ‖setLen LAct s + 1‖ + 7 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s 0) :
    ListOK tbl E ((9 : ℕ) : V) Γ (vVerum walkPieces Wc W₁ T s) ∧ NoDrop' (vVerum walkPieces Wc W₁ T s) ∧
    shiftsV (vVerum walkPieces Wc W₁ T s) = 1 ∧
    neg LAct (goalFact (^&(len (memberList s) + 1 + 1)) (bnum (dlen TAct (verumIntro s)))) ∈
      finalCtx Γ (vVerum walkPieces Wc W₁ T s) := by
  have hW : WalkTable tbl := hP.walkTable
  have hD : Derivation TAct (verumIntro s) := Derivation.verumIntro hs hv
  have hdl : dlen TAct (verumIntro s) = setLen LAct s + 1 := dlen_verumIntro hD
  obtain ⟨hfs, hvf, hmv, hsl, hle⟩ := layout_verum htbl hP hv hLay
  simp only [zero_add] at hfs hvf hmv hsl hle
  have hmt : memTop walkPieces Wc T s (^⊤ : V) 0 ≤ 6 * D + 1 := by
    have := memTop_le htbl hW hWc T hs hv hsD (i := 0); rwa [zero_add] at this
  have e12 : (1 : V) + 2 = 3 := by norm_num
  have hn' : 18 * ‖dlen TAct (verumIntro s)‖ + 7 ≤ E := by rw [hdl]; exact hn
  have hLn' : setLen LAct s + 1 ≤ dlen TAct (verumIntro s) := by rw [hdl]
  have h4E : (0 : V) + 4 ≤ E := by
    rw [zero_add, show (4 : V) = 1 + 3 by norm_num]
    exact le_trans (add_le_add (one_le_len_memberList_of_mem hv) (le_refl 3)) hkE
  obtain ⟨fok, fnd, fsh, -, fgoal⟩ := fragVerum_ok (E := E) (is := len (memberList s) + 1) (il := 0)
    (iv := memTop walkPieces Wc T s (^⊤ : V) 0) (L := setLen LAct s) (n := dlen TAct (verumIntro s))
    htbl hP.frag1Table hW₁ htblN hΓ
    (by rw [add_assoc, e12]; exact hkE) h4E
    (le_trans (add_le_add hmt (le_refl 2)) (by rw [add_assoc, e12]; exact hiE))
    hn' hLn' hfs hvf hmv hsl hle
  exact ⟨fok.mono h89, fnd, fsh, fgoal⟩

/-- **The `axm` list is applicable**, given a certificate entry for `p` at `ip = memTop s p 0` (transferred from the
canonical dossier context by `listOK_mono_subset`). -/
theorem vAxm_ok {tbl N N' B' Wc W₂ T s p pro D E Γ Cv : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWc : Wc = certPieces) (hW₂ : W₂ = frag2Pieces)
    (hs : IsFormulaSet LAct s) (hp : p ∈ s) (hax : p ∈ TAct.Δ₁Class) (hsD : setLen LAct s ≤ D)
    (hiE : 6 * D + 3 ≤ E) (hkE : len (memberList s) + 3 ≤ E) (hn : 18 * ‖setLen LAct s + 1‖ + 7 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s 0)
    (hpro : NumInvV tbl E (dossCtx walkPieces p (memTop walkPieces Wc T s p 0)) Cv pro
      (axchFact (^&(memTop walkPieces Wc T s p 0)))) :
    ListOK tbl E ((9 : ℕ) : V) Γ (vAxm walkPieces Wc W₂ T s p pro) ∧ NoDrop' (vAxm walkPieces Wc W₂ T s p pro) ∧
    shiftsV (vAxm walkPieces Wc W₂ T s p pro) = 1 ∧
    neg LAct (goalFact (^&(len (memberList s) + 1 + 1)) (bnum (dlen TAct (axm s p)))) ∈
      finalCtx Γ (vAxm walkPieces Wc W₂ T s p pro) := by
  have hW : WalkTable tbl := hP.walkTable
  have hD : Derivation TAct (axm s p) := Derivation.axm hs hp hax
  have hdl : dlen TAct (axm s p) = setLen LAct s + 1 := dlen_axm hD
  obtain ⟨pok, pnd, psh, -, -, pax⟩ := hpro
  obtain ⟨hDp, -, -, hmp⟩ := Layout.member hLay hp
  have hsub : dossCtx walkPieces p (memTop walkPieces Wc T s p 0) ⊆ Γ := dossCtx_subset hDp
  have pok' : ListOK tbl E ((9 : ℕ) : V) Γ pro := listOK_mono_subset 9 htbl hΓ pnd hsub pok
  have pax' : neg LAct (axchFact (^&(memTop walkPieces Wc T s p 0))) ∈ finalCtx Γ pro := finalCtx_mono' pnd hsub pax
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ pro := ⟨_, rfl⟩
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 9 htbl hΓ pok'
  have tr : ∀ {x : V}, x ∈ Γ → x ∈ Γ₁ := fun hx ↦ by
    rw [hΓ₁]; have := mem_finalCtx_of_mem' pnd hx; rwa [psh, shiftIterV_zero] at this
  have hfs := tr (hLay.fsetPi (one_le_len_memberList_of_mem hp))
  have hsl := tr hLay.2.1
  have hle := tr hLay.2.2
  have hmp' := tr hmp
  simp only [zero_add] at hfs hsl hle hmp'
  rw [← hΓ₁] at pax'
  have hmt : memTop walkPieces Wc T s p 0 ≤ 6 * D + 1 := by
    have := memTop_le htbl hW hWc T hs hp hsD (i := 0); rwa [zero_add] at this
  have e12 : (1 : V) + 2 = 3 := by norm_num
  have hn' : 18 * ‖dlen TAct (axm s p)‖ + 7 ≤ E := by rw [hdl]; exact hn
  have hLn' : setLen LAct s + 1 ≤ dlen TAct (axm s p) := by rw [hdl]
  have h4E : (0 : V) + 4 ≤ E := by
    rw [zero_add, show (4 : V) = 1 + 3 by norm_num]
    exact le_trans (add_le_add (one_le_len_memberList_of_mem hp) (le_refl 3)) hkE
  obtain ⟨fok, fnd, fsh, -, fgoal⟩ := nodeAxm_ok (E := E) (is := len (memberList s) + 1) (il := 0)
    (ip := memTop walkPieces Wc T s p 0) (L := setLen LAct s) (n := dlen TAct (axm s p))
    htbl hP.frag2Table hW₂ htblN hΓ₁f
    (by rw [add_assoc, e12]; exact hkE) h4E
    (le_trans (add_le_add hmt (le_refl 2)) (by rw [add_assoc, e12]; exact hiE))
    hn' hLn' hfs hmp' pax' hsl hle
  unfold vAxm
  refine ⟨listOK_appendV pok' (by rw [← hΓ₁]; exact fok.mono h89), noDrop'_appendV pnd fnd, ?_, ?_⟩
  · rw [shiftsV_appendV, psh, fsh, zero_add]
  · rw [finalCtx_appendV, ← hΓ₁]; exact fgoal

end leaves

/-! ### 8.2 The node-layout invariant, the two mini-lists of the empty sequent, and `wk`/`shift` -/

section wkShift

/-- **The node-layout invariant** at offset `0`: the canonical layout of a nonempty sequent, or — for the EMPTY sequent
(`Prologue.lean` §12) — `Layout0` plus `fsetPiFact` of the `∅`-object `&1` (what `nodeWk` needs at an empty parent). -/
def NodeLay (Ww Wc T Γ s : V) : Prop :=
  (1 ≤ len (memberList s) ∧ Layout Ww Wc T Γ s 0) ∨
  (s = 0 ∧ Layout0 Ww Wc T Γ 0 ∧ neg LAct (fsetPiFact (^&1)) ∈ Γ)

/-- The layout at offset `0`, as a 5-ary predicate (`definability`'s composition rules stop at arity 5, so the
6-ary `Layout` cannot be composed as a black box). -/
def Layout' (Ww Wc T Γ s : V) : Prop := Layout Ww Wc T Γ s 0

instance layout'_definable : 𝚫₁-Relation₅ (Layout' : V → V → V → V → V → Prop) := by
  have h := HierarchySymbol.Definable.substitution (Γ := 𝚫) (m := 0) (layout_definable (V := V))
    (f := ![fun v : Fin 5 → V ↦ v 0, fun v ↦ v 1, fun v ↦ v 2, fun v ↦ v 3, fun v ↦ v 4, fun _ ↦ (0 : V)])
    (fun i ↦ by fin_cases i <;> (try simp) <;> definability)
  exact HierarchySymbol.Definable.of_iff h (fun v ↦ by simp [Layout'])

/-- `NodeLay` through `Layout'` (what `definability` composes). -/
def NodeLayQ (Ww Wc T Γ s : V) : Prop :=
  (1 ≤ len (memberList s) ∧ Layout' Ww Wc T Γ s) ∨
  (s = 0 ∧ (Layout' Ww Wc T Γ 0 ∧ neg LAct (eqFactB (^&(0 + 1)) (𝟎 : V)) ∈ Γ) ∧ neg LAct (fsetPiFact (^&1)) ∈ Γ)

lemma nodeLay_iff_q {Ww Wc T Γ s : V} : NodeLay Ww Wc T Γ s ↔ NodeLayQ Ww Wc T Γ s := Iff.rfl

instance nodeLayQ_definable : 𝚫₁-Relation₅ (NodeLayQ : V → V → V → V → V → Prop) := by
  unfold NodeLayQ; definability

instance nodeLay_definable : 𝚫₁-Relation₅ (NodeLay : V → V → V → V → V → Prop) :=
  HierarchySymbol.Definable.of_iff (Q := fun v ↦ NodeLayQ (v 0) (v 1) (v 2) (v 3) (v 4)) nodeLayQ_definable
    (fun v ↦ nodeLay_iff_q)

lemma NodeLay.layout {Ww Wc T Γ s : V} (h : NodeLay Ww Wc T Γ s) : Layout Ww Wc T Γ s 0 := by
  rcases h with ⟨-, h⟩ | ⟨rfl, h, -⟩
  · exact h
  · exact h.1

lemma NodeLay.fsetPi {Ww Wc T Γ s : V} (h : NodeLay Ww Wc T Γ s) :
    neg LAct (fsetPiFact (^&(len (memberList s) + 1))) ∈ Γ := by
  rcases h with ⟨hk, h⟩ | ⟨rfl, -, h⟩
  · have := h.fsetPi hk; rwa [zero_add] at this
  · rwa [len_memberList_zero, zero_add]

lemma NodeLay.mono {Ww Wc T Γ Γ' s : V} (hsub : ∀ x ∈ Γ, x ∈ Γ') (h : NodeLay Ww Wc T Γ s) : NodeLay Ww Wc T Γ' s := by
  rcases h with ⟨hk, h⟩ | ⟨rfl, h, hf⟩
  · exact Or.inl ⟨hk, h.mono hsub⟩
  · exact Or.inr ⟨rfl, h.mono hsub, hsub _ hf⟩

/-- A transported (negated) fact. -/
lemma tr_fact {Γ S x : V} (hS : NoDrop' S) (hxf : IsFormula LAct x) (hx : neg LAct x ∈ Γ) :
    neg LAct (shiftIterV x (shiftsV S)) ∈ finalCtx Γ S := by
  have := mem_finalCtx_of_mem' hS hx
  rwa [shiftIterV_neg hxf] at this

lemma hf_ (i : V) : IsSemiterm LAct 0 (^&i : V) := by simp
lemma h0_ : IsSemiterm LAct (0 : V) (𝟎 : V) := isSemiterm_zeroV

/-- **`emptyFsetPi` is applicable** after an empty layout at `0` (`eqFactB &1 𝟎`): shift-free, leaves `fsetPiFact &1`. -/
theorem emptyFsetPi_ok {tbl N W E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (hWp : W = proPieces)
    (hΓ : IsFormulaSet LAct Γ) (hE : (2 : V) ≤ E) (heq : neg LAct (eqFactB (^&1) (𝟎 : V)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (emptyFsetPi W) ∧ NoDrop' (emptyFsetPi W) ∧ shiftsV (emptyFsetPi W) = 0 ∧
    neg LAct (fsetPiFact (^&1)) ∈ finalCtx Γ (emptyFsetPi W) ∧ ∀ x ∈ Γ, x ∈ finalCtx Γ (emptyFsetPi W) := by
  have hL := hP.layoutTable
  have e81 : ∀ ev : V, mkStep proPieces (81 : V) ev = mkStep layoutPieces (81 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 81 (by decide) ev; simpa using this
  have e82 : ∀ ev : V, mkStep proPieces (82 : V) ev = mkStep layoutPieces (82 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 82 (by decide) ev; simpa using this
  have e84 : ∀ ev : V, mkStep proPieces (84 : V) ev = mkStep layoutPieces (84 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 84 (by decide) ev; simpa using this
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) hE
  have h0E : termLen LAct (𝟎 : V) ≤ E := termLen_zeroV_le hE1
  have hf1E : termLen LAct (^&1 : V) ≤ E := termLen_fvar_le' (by rw [one_add_one_eq_two]; exact hE)
  -- step 1: `emptySubsetC [𝟎]` → `subsetFact 𝟎 𝟎`
  obtain ⟨ok₁, tg₁, cx₁⟩ := lok_emptySubsetC htbl hL rfl hΓ h0_ h0E
  rw [← e81, ← hWp] at ok₁ tg₁ cx₁
  have hΓ₁f : IsFormulaSet LAct (insert (neg LAct (subsetFact (𝟎 : V) (𝟎 : V))) Γ) := by
    rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  -- step 2: `congSubsetL [𝟎, &1, 𝟎]` → `subsetFact &1 𝟎`
  obtain ⟨hlen, hrow⟩ := hP.congSubsetL
  obtain ⟨ok₂, tg₂, cx₂⟩ := pok_congSubsetL htbl hWp hlen hrow hΓ₁f h0_ h0E (hf_ 1) hf1E h0_ h0E (memIns heq) (memInsSelf _ _)
  have hΓ₂f : IsFormulaSet LAct (insert (neg LAct (subsetFact (^&1) (𝟎 : V))) (insert (neg LAct (subsetFact (𝟎 : V) (𝟎 : V))) Γ)) := by
    rw [← cx₂]; exact isFormulaSet_ctxAfter 8 htbl ok₂
  -- step 3: `fsetOfSubsetZeroC [&1]` → `fsetSigmaFact &1`
  obtain ⟨ok₃, tg₃, cx₃⟩ := lok_fsetOfSubsetZeroC htbl hL rfl hΓ₂f (hf_ 1) hf1E (memInsSelf _ _)
  rw [← e82, ← hWp] at ok₃ tg₃ cx₃
  have hΓ₃f : IsFormulaSet LAct (insert (neg LAct (fsetSigmaFact (^&1))) (insert (neg LAct (subsetFact (^&1) (𝟎 : V)))
      (insert (neg LAct (subsetFact (𝟎 : V) (𝟎 : V))) Γ))) := by
    rw [← cx₃]; exact isFormulaSet_ctxAfter 8 htbl ok₃
  -- step 4: `fsetSigmaPiC [&1]` → `fsetPiFact &1`
  obtain ⟨ok₄, tg₄, cx₄⟩ := lok_fsetSigmaPiC htbl hL rfl hΓ₃f (hf_ 1) hf1E (memInsSelf _ _)
  rw [← e84, ← hWp] at ok₄ tg₄ cx₄
  have hfin : finalCtx Γ (emptyFsetPi W) = insert (neg LAct (fsetPiFact (^&1))) (insert (neg LAct (fsetSigmaFact (^&1)))
      (insert (neg LAct (subsetFact (^&1) (𝟎 : V))) (insert (neg LAct (subsetFact (𝟎 : V) (𝟎 : V))) Γ))) := by
    unfold emptyFsetPi
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_single, cx₄]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold emptyFsetPi
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    exact listOK_single ok₄
  · unfold emptyFsetPi
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp) (noDrop'_cons (by rw [tg₃]; simp)
      (noDrop'_single (by rw [tg₄]; simp))))
  · unfold emptyFsetPi
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₃, tg₄]; simp
  · rw [hfin]; exact memInsSelf _ _
  · rw [hfin]; intro x hx; exact memIns (memIns (memIns (memIns hx)))

/-- **`reset0` is applicable** after `proShift0` (the empty child at `1`, the empty parent at `3`, `setShiftFact &4 &2`):
two eigenvariables; afterwards the child's `Layout0` at `0`, the parent's at `5`, `setShiftFact &6 &1`. -/
theorem reset0_ok {tbl N W Wc T E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (hWp : W = proPieces)
    (hΓ : IsFormulaSet LAct Γ) (hE : (7 : V) ≤ E)
    (hLayC : Layout0 walkPieces Wc T Γ 1) (hLayP : Layout0 walkPieces Wc T Γ 3)
    (hss : neg LAct (setShiftFact (^&4) (^&2)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (reset0 W) ∧ NoDrop' (reset0 W) ∧ shiftsV (reset0 W) = 2 ∧
    Layout0 walkPieces Wc T (finalCtx Γ (reset0 W)) 0 ∧ Layout0 walkPieces Wc T (finalCtx Γ (reset0 W)) 5 ∧
    neg LAct (setShiftFact (^&6) (^&1)) ∈ finalCtx Γ (reset0 W) := by
  have hL := hP.layoutTable
  have e42 : ∀ ev : V, mkStep proPieces (42 : V) ev = mkStep layoutPieces (42 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 42 (by decide) ev; simpa using this
  have e43 : ∀ ev : V, mkStep proPieces (43 : V) ev = mkStep layoutPieces (43 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 43 (by decide) ev; simpa using this
  have hE2 : (2 : V) ≤ E := le_trans (by norm_num) hE
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) hE
  have h0E : termLen LAct (𝟎 : V) ≤ E := termLen_zeroV_le hE1
  have hf1E : termLen LAct (^&1 : V) ≤ E := termLen_fvar_le' (le_trans (by norm_num) hE)
  have hf4E : termLen LAct (^&4 : V) ≤ E := termLen_fvar_le' (le_trans (by norm_num) hE)
  have hf6E : termLen LAct (^&6 : V) ≤ E := termLen_fvar_le' (by rw [show (6 : V) + 1 = 7 by norm_num]; exact hE)
  -- the fresh empty layout
  obtain ⟨lok, lnd, lsh, -, lLay⟩ := layoutSteps0_ok htbl hP hWp hΓ hE2
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ (layoutSteps0 W) := ⟨_, rfl⟩
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 8 htbl hΓ lok
  have lLay₁ : Layout0 walkPieces Wc T Γ₁ 0 := by rw [hΓ₁]; exact lLay
  have hLayC₁ : Layout0 walkPieces Wc T Γ₁ 3 := by
    rw [hΓ₁]; have := hLayC.transport lnd; rwa [lsh, show (1 : V) + 2 = 3 by norm_num] at this
  have hLayP₁ : Layout0 walkPieces Wc T Γ₁ 5 := by
    rw [hΓ₁]; have := hLayP.transport lnd; rwa [lsh, show (3 : V) + 2 = 5 by norm_num] at this
  have hss₁ : neg LAct (setShiftFact (^&6) (^&4)) ∈ Γ₁ := by
    rw [hΓ₁]
    have := tr_fact lnd (isFormula_setShiftFact (hf_ 4) (hf_ 2)) hss
    rwa [lsh, shiftIterV_setShiftFact (hf_ 4) (hf_ 2), termShiftIterV_fvar, termShiftIterV_fvar,
      show (4 : V) + 2 = 6 by norm_num, show (2 : V) + 2 = 4 by norm_num] at this
  have h1 : neg LAct (eqFactB (^&1) (𝟎 : V)) ∈ Γ₁ := by have := lLay₁.2; rwa [zero_add] at this
  have h4 : neg LAct (eqFactB (^&4) (𝟎 : V)) ∈ Γ₁ := by have := hLayC₁.2; rwa [show (3 : V) + 1 = 4 by norm_num] at this
  -- step 1: `eqSymm [&4, 𝟎]` → `eqFactB 𝟎 &4`
  obtain ⟨ok₁, tg₁, cx₁⟩ := lok_eqSymm htbl hL rfl hΓ₁f (hf_ 4) hf4E h0_ h0E h4
  rw [← e42, ← hWp] at ok₁ tg₁ cx₁
  have hΓ₂f : IsFormulaSet LAct (insert (neg LAct (eqFactB (𝟎 : V) (^&4))) Γ₁) := by
    rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  -- step 2: `eqTrans [&1, 𝟎, &4]` → `eqFactB &1 &4`
  obtain ⟨ok₂, tg₂, cx₂⟩ := lok_eqTrans htbl hL rfl hΓ₂f (hf_ 1) hf1E h0_ h0E (hf_ 4) hf4E (memIns h1) (memInsSelf _ _)
  rw [← e43, ← hWp] at ok₂ tg₂ cx₂
  have hΓ₃f : IsFormulaSet LAct (insert (neg LAct (eqFactB (^&1) (^&4))) (insert (neg LAct (eqFactB (𝟎 : V) (^&4))) Γ₁)) := by
    rw [← cx₂]; exact isFormulaSet_ctxAfter 8 htbl ok₂
  -- step 3: `congSetShiftR [&6, &4, &1]` → `setShiftFact &6 &1`
  obtain ⟨hlen, hrow⟩ := hP.congSetShiftR
  obtain ⟨ok₃, tg₃, cx₃⟩ := pok_congSetShiftR htbl hWp hlen hrow hΓ₃f (hf_ 6) hf6E (hf_ 4) hf4E (hf_ 1) hf1E
    (memInsSelf _ _) (memIns (memIns hss₁))
  have hfin : finalCtx Γ₁ (mkStep W 42 ?[^&4, (𝟎 : V)] ∷ mkStep W 43 ?[^&1, (𝟎 : V), ^&4] ∷ mkStep W 158 ?[^&6, ^&4, ^&1] ∷ (0 : V)) =
      insert (neg LAct (setShiftFact (^&6) (^&1))) (insert (neg LAct (eqFactB (^&1) (^&4)))
        (insert (neg LAct (eqFactB (𝟎 : V) (^&4))) Γ₁)) := by
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_single, cx₃]
  have tr : ∀ x ∈ Γ₁, x ∈ insert (neg LAct (setShiftFact (^&6) (^&1))) (insert (neg LAct (eqFactB (^&1) (^&4)))
        (insert (neg LAct (eqFactB (𝟎 : V) (^&4))) Γ₁)) := fun x hx ↦ memIns (memIns (memIns hx))
  have hnd : NoDrop' (mkStep W 42 ?[^&4, (𝟎 : V)] ∷ mkStep W 43 ?[^&1, (𝟎 : V), ^&4] ∷ mkStep W 158 ?[^&6, ^&4, ^&1] ∷ (0 : V)) :=
    noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp) (noDrop'_single (by rw [tg₃]; simp)))
  have hsh : shiftsV (mkStep W 42 ?[^&4, (𝟎 : V)] ∷ mkStep W 43 ?[^&1, (𝟎 : V), ^&4] ∷ mkStep W 158 ?[^&6, ^&4, ^&1] ∷ (0 : V)) = 0 := by
    rw [shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₃]; simp
  unfold reset0
  refine ⟨listOK_appendV lok ?_, noDrop'_appendV lnd hnd, ?_, ?_, ?_, ?_⟩
  · rw [← hΓ₁]
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    exact listOK_single ok₃
  · rw [shiftsV_appendV, lsh, hsh]; norm_num
  · rw [finalCtx_appendV, ← hΓ₁, hfin]; exact lLay₁.mono tr
  · rw [finalCtx_appendV, ← hΓ₁, hfin]; exact hLayP₁.mono tr
  · rw [finalCtx_appendV, ← hΓ₁, hfin]; exact memInsSelf _ _

end wkShift

/-! ### 8.3 `wk` and `shift`: the common tails and the two selectors -/

section wkShiftOk

/-- `a ≤ b` from `a + c = b` (the residual of a linear cap is a polynomial with nonnegative coefficients). -/
lemma le_of_add_eq' {a b c : V} (h : a + c = b) : a ≤ b := h ▸ le_self_add

lemma len_memberList_le_of_setLen {s D : V} (hs : IsFormulaSet LAct s) (hsD : setLen LAct s ≤ D) :
    len (memberList s) ≤ D := le_trans (len_memberList_le_setLen hs) hsD

lemma one_le_len_memberList_of_ne {c : V} (h : memberList c ≠ 0) : 1 ≤ len (memberList c) :=
  pos_iff_one_le.mp (pos_iff_ne_zero.mpr (fun h0 ↦ h (len_zero_iff_eq_nil.mp h0)))

/-- The child's facts, as the inductive hypothesis delivers them (any context with the child's node layout). -/
def ChildOK (tbl Wc T E L' d' B : V) : Prop :=
  ∀ Γ' : V, IsFormulaSet LAct Γ' → NodeLay walkPieces Wc T Γ' (fstIdx d') →
    ListOK tbl E ((9 : ℕ) : V) Γ' L' ∧ NoDrop' L' ∧ shiftsV L' ≤ B ∧
    neg LAct (goalFact (^&(len (memberList (fstIdx d')) + 1 + shiftsV L')) (bnum (dlen TAct d'))) ∈ finalCtx Γ' L'

set_option maxHeartbeats 2000000 in
/-- **The tail of `wk`** after a prologue `pro` (shifts `σ`; the child at `0`, the parent at `σ` with its `fsetPiFact`,
`subsetFact s''_child S`): the child's list, `goalElim`, `nodeWk`. -/
theorem wkTail_ok {tbl N N' B' Wc W₁ T s d' L' pro σ D B E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWc : Wc = certPieces) (hW₁ : W₁ = frag1Pieces)
    (hs : IsFormulaSet LAct s) (hd' : Derivation TAct d') (hsub : fstIdx d' ⊆ s)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (fstIdx d') ≤ D) (hmD : dlen TAct d' ≤ D) (hσ : σ ≤ 7 * D + 5)
    (hE : 40 * D + B + 40 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (pok : ListOK tbl E ((8 : ℕ) : V) Γ pro) (pnd : NoDrop' pro) (psh : shiftsV pro = σ)
    (layC : NodeLay walkPieces Wc T (finalCtx Γ pro) (fstIdx d'))
    (layS : Layout walkPieces Wc T (finalCtx Γ pro) s σ)
    (hfsS : neg LAct (fsetPiFact (^&(σ + (len (memberList s) + 1)))) ∈ finalCtx Γ pro)
    (hsubf : neg LAct (subsetFact (^&(len (memberList (fstIdx d')) + 1)) (^&(σ + (len (memberList s) + 1)))) ∈ finalCtx Γ pro)
    (hch : ChildOK tbl Wc T E L' d' B) :
    ListOK tbl E ((9 : ℕ) : V) Γ (appendV pro (appendV L' (appendV
        (goalElim (^&(len (memberList (fstIdx d')) + 1 + shiftsV L')) (bnum (dlen TAct d')))
        (nodeWk W₁ T (σ + shiftsV L' + 2 + (len (memberList s) + 1)) (σ + shiftsV L' + 2)
          (len (memberList (fstIdx d')) + 1 + shiftsV L' + 2) 1 0 (setLen LAct s) (dlen TAct d') (dlen TAct (wkRule s d')))))) ∧
    NoDrop' (appendV pro (appendV L' (appendV
        (goalElim (^&(len (memberList (fstIdx d')) + 1 + shiftsV L')) (bnum (dlen TAct d')))
        (nodeWk W₁ T (σ + shiftsV L' + 2 + (len (memberList s) + 1)) (σ + shiftsV L' + 2)
          (len (memberList (fstIdx d')) + 1 + shiftsV L' + 2) 1 0 (setLen LAct s) (dlen TAct d') (dlen TAct (wkRule s d')))))) ∧
    shiftsV (appendV pro (appendV L' (appendV
        (goalElim (^&(len (memberList (fstIdx d')) + 1 + shiftsV L')) (bnum (dlen TAct d')))
        (nodeWk W₁ T (σ + shiftsV L' + 2 + (len (memberList s) + 1)) (σ + shiftsV L' + 2)
          (len (memberList (fstIdx d')) + 1 + shiftsV L' + 2) 1 0 (setLen LAct s) (dlen TAct d') (dlen TAct (wkRule s d')))))) =
      σ + shiftsV L' + 3 ∧
    neg LAct (goalFact (^&(len (memberList s) + 1 + (σ + shiftsV L' + 3))) (bnum (dlen TAct (wkRule s d')))) ∈
      finalCtx Γ (appendV pro (appendV L' (appendV
        (goalElim (^&(len (memberList (fstIdx d')) + 1 + shiftsV L')) (bnum (dlen TAct d')))
        (nodeWk W₁ T (σ + shiftsV L' + 2 + (len (memberList s) + 1)) (σ + shiftsV L' + 2)
          (len (memberList (fstIdx d')) + 1 + shiftsV L' + 2) 1 0 (setLen LAct s) (dlen TAct d') (dlen TAct (wkRule s d')))))) := by
  have hD : Derivation TAct (wkRule s d') := Derivation.wkRule hs hsub ⟨rfl, hd'⟩
  have hdl : dlen TAct (wkRule s d') = setLen LAct s + dlen TAct d' + 1 := dlen_wkRule hD
  have hcs : IsFormulaSet LAct (fstIdx d') := DerivationOf.isFormulaSet ⟨rfl, hd'⟩
  have hkD : len (memberList s) ≤ D := len_memberList_le_of_setLen hs hsD
  have hkcD : len (memberList (fstIdx d')) ≤ D := len_memberList_le_of_setLen hcs hcD
  obtain ⟨k, hk⟩ : ∃ k, k = len (memberList s) := ⟨_, rfl⟩
  obtain ⟨kc, hkc⟩ : ∃ kc, kc = len (memberList (fstIdx d')) := ⟨_, rfl⟩
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ pro := ⟨_, rfl⟩
  rw [← hΓ₁] at layC layS hfsS hsubf
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 8 htbl hΓ pok
  obtain ⟨cok, cnd, csh, cgoal⟩ := hch Γ₁ hΓ₁f layC
  obtain ⟨s', hs'⟩ : ∃ s', s' = shiftsV L' := ⟨_, rfl⟩
  obtain ⟨Γ₂, hΓ₂⟩ : ∃ Γ', Γ' = finalCtx Γ₁ L' := ⟨_, rfl⟩
  rw [← hΓ₂, ← hs', ← hkc] at cgoal
  rw [← hs'] at csh
  have hΓ₂f : IsFormulaSet LAct Γ₂ := by rw [hΓ₂]; exact finalCtx_isFormulaSet 9 htbl hΓ₁f cok
  have layS₂ : Layout walkPieces Wc T Γ₂ s (σ + s') := by rw [hΓ₂, hs']; exact layS.transport cnd
  have hfsS₂ : neg LAct (fsetPiFact (^&(σ + (k + 1) + s'))) ∈ Γ₂ := by
    rw [hΓ₂, hs', hk]
    have := tr_fact cnd (isFormula_fsetPiFact (hf_ _)) hfsS
    rwa [shiftIterV_fsetPiFact (hf_ _), termShiftIterV_fvar] at this
  have hsubf₂ : neg LAct (subsetFact (^&(kc + 1 + s')) (^&(σ + (k + 1) + s'))) ∈ Γ₂ := by
    rw [hΓ₂, hs', hk, hkc]
    have := tr_fact cnd (isFormula_subsetFact (hf_ _) (hf_ _)) hsubf
    rwa [shiftIterV_subsetFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
  -- `goalElim`
  obtain ⟨gok, gnd, gsh, -, gder, gfst, gdlen, gle⟩ :=
    goalElim_ok 9 htbl hΓ₂f (hf_ (kc + 1 + s')) (isSemiterm_bnum_LAct 0 _) cgoal
  rw [termShift_fvar, termShift_fvar] at gfst
  rw [termShift_bnum, termShift_bnum] at gle
  obtain ⟨Γ₃, hΓ₃⟩ : ∃ Γ', Γ' = finalCtx Γ₂ (goalElim (^&(kc + 1 + s')) (bnum (dlen TAct d'))) := ⟨_, rfl⟩
  rw [← hΓ₃] at gder gfst gdlen gle
  have hΓ₃f : IsFormulaSet LAct Γ₃ := by rw [hΓ₃]; exact finalCtx_isFormulaSet 9 htbl hΓ₂f gok
  have layS₃ : Layout walkPieces Wc T Γ₃ s (σ + s' + 2) := by
    rw [hΓ₃]; have := layS₂.transport gnd; rwa [gsh] at this
  have hfsS₃ : neg LAct (fsetPiFact (^&(σ + s' + 2 + (k + 1)))) ∈ Γ₃ := by
    rw [hΓ₃]
    have := tr_fact gnd (isFormula_fsetPiFact (hf_ _)) hfsS₂
    rw [gsh, shiftIterV_fsetPiFact (hf_ _), termShiftIterV_fvar] at this
    rwa [show σ + (k + 1) + s' + 2 = σ + s' + 2 + (k + 1) by ring] at this
  have hsubf₃ : neg LAct (subsetFact (^&(kc + 1 + s' + 2)) (^&(σ + s' + 2 + (k + 1)))) ∈ Γ₃ := by
    rw [hΓ₃]
    have := tr_fact gnd (isFormula_subsetFact (hf_ _) (hf_ _)) hsubf₂
    rw [gsh, shiftIterV_subsetFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show σ + (k + 1) + s' + 2 = σ + s' + 2 + (k + 1) by ring] at this
  rw [show kc + 1 + s' + 1 + 1 = kc + 1 + s' + 2 by ring] at gfst
  -- the caps (each from `40·D + B + 40 ≤ E`)
  have hn1 : ‖dlen TAct (wkRule s d')‖ ≤ 2 * D + 1 := by
    refine le_trans (length_le _) ?_
    rw [hdl]
    exact le_trans (add_le_add (add_le_add hsD hmD) (le_refl 1)) (le_of_add_eq' (c := 0) (by ring))
  have his : σ + s' + 2 + (k + 1) + 2 ≤ E := by
    refine le_trans ?_ hE
    calc σ + s' + 2 + (k + 1) + 2 ≤ (7 * D + 5) + B + 2 + (D + 1) + 2 :=
          add_le_add (add_le_add (add_le_add (add_le_add hσ csh) (le_refl 2)) (add_le_add (hk ▸ hkD) (le_refl 1))) (le_refl 2)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 32 * D + 30) (by ring)
  have hic : kc + 1 + s' + 2 + 2 ≤ E := by
    refine le_trans ?_ hE
    calc kc + 1 + s' + 2 + 2 ≤ D + 1 + B + 2 + 2 :=
          add_le_add (add_le_add (add_le_add (add_le_add (hkc ▸ hkcD) (le_refl 1)) csh) (le_refl 2)) (le_refl 2)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 39 * D + 35) (by ring)
  have hid : (1 : V) + 2 ≤ E := le_trans (le_of_add_eq' (c := 40 * D + B + 37) (by ring)) hE
  have hT : σ + s' + 2 + 0 + 7 ≤ E := by
    refine le_trans ?_ hE
    calc σ + s' + 2 + 0 + 7 ≤ (7 * D + 5) + B + 2 + 0 + 7 :=
          add_le_add (add_le_add (add_le_add (add_le_add hσ csh) (le_refl 2)) (le_refl 0)) (le_refl 7)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 33 * D + 26) (by ring)
  have hn : 18 * ‖dlen TAct (wkRule s d')‖ + 7 ≤ E := by
    refine le_trans ?_ hE
    calc 18 * ‖dlen TAct (wkRule s d')‖ + 7 ≤ 18 * (2 * D + 1) + 7 :=
          add_le_add (mul_le_mul_of_nonneg_left hn1 zero_le) (le_refl 7)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 4 * D + B + 15) (by ring)
  have hLn : setLen LAct s + dlen TAct d' + 1 ≤ dlen TAct (wkRule s d') := by rw [hdl]
  -- the node
  obtain ⟨nok, nnd, nsh, -, ngoal⟩ := nodeWk_ok (E := E) (is := σ + s' + 2 + (k + 1)) (il := σ + s' + 2)
    (ic := kc + 1 + s' + 2) (id := 1) (in₁ := 0) (L := setLen LAct s) (m₁ := dlen TAct d') (n := dlen TAct (wkRule s d'))
    htbl hP.frag1Table hW₁ htblN hΓ₃f his hic hid hT hn hLn hfsS₃ gfst hsubf₃ gder gdlen gle
    (by have := layS₃.2.1; rwa [← hk] at this) layS₃.2.2
  -- assembly
  rw [← hs', ← hk, ← hkc]
  have ok₃ : ListOK tbl E ((9 : ℕ) : V) Γ₂ (appendV (goalElim (^&(kc + 1 + s')) (bnum (dlen TAct d')))
      (nodeWk W₁ T (σ + s' + 2 + (k + 1)) (σ + s' + 2) (kc + 1 + s' + 2) 1 0 (setLen LAct s) (dlen TAct d')
        (dlen TAct (wkRule s d')))) := listOK_appendV gok (by rw [← hΓ₃]; exact nok.mono h89)
  have ok₂ := listOK_appendV cok (by rw [← hΓ₂]; exact ok₃)
  have ok₁ := listOK_appendV (pok.mono h89) (by rw [← hΓ₁]; exact ok₂)
  refine ⟨ok₁, noDrop'_appendV pnd (noDrop'_appendV cnd (noDrop'_appendV gnd nnd)), ?_, ?_⟩
  · rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, psh, ← hs', gsh, nsh]; ring
  · rw [finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂, ← hΓ₃,
      show k + 1 + (σ + s' + 3) = σ + s' + 2 + (k + 1) + 1 by ring]
    exact ngoal

/-- **The `wk` list is applicable** at the node's layout: the selector's two cases, then the common tail. -/
theorem vWk_ok {tbl N N' B' Wl Wc W₁ W T s d' L' D B E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces) (hW₁ : W₁ = frag1Pieces)
    (hs : IsFormulaSet LAct s) (hd' : Derivation TAct d') (hsub : fstIdx d' ⊆ s)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (fstIdx d') ≤ D) (hmD : dlen TAct d' ≤ D)
    (hE : 40 * D + 18 * ‖D‖ + B + 40 ≤ E) (hΓ : IsFormulaSet LAct Γ) (hLay : NodeLay walkPieces Wc T Γ s)
    (hch : ChildOK tbl Wc T E L' d' B) :
    ListOK tbl E ((9 : ℕ) : V) Γ (vWk walkPieces Wl Wc W₁ W T s d' L') ∧ NoDrop' (vWk walkPieces Wl Wc W₁ W T s d' L') ∧
    shiftsV (vWk walkPieces Wl Wc W₁ W T s d' L') ≤ 7 * D + B + 8 ∧
    neg LAct (goalFact (^&(len (memberList s) + 1 + shiftsV (vWk walkPieces Wl Wc W₁ W T s d' L')))
      (bnum (dlen TAct (wkRule s d')))) ∈ finalCtx Γ (vWk walkPieces Wl Wc W₁ W T s d' L') := by
  have hcs : IsFormulaSet LAct (fstIdx d') := DerivationOf.isFormulaSet ⟨rfl, hd'⟩
  have hE' : 40 * D + B + 40 ≤ E := le_trans (le_of_add_eq' (c := 18 * ‖D‖) (by ring)) hE
  have hE13 : 13 * D + 18 * ‖D‖ + 12 ≤ E := le_trans (le_of_add_eq' (c := 27 * D + B + 28) (by ring)) hE
  have hE14 : 0 + 14 * D + 5 ≤ E := le_trans (le_of_add_eq' (c := 26 * D + 18 * ‖D‖ + B + 35) (by ring)) hE
  have hE8 : 13 * D + 18 * ‖D‖ + 8 ≤ E := le_trans (le_of_add_eq' (c := 27 * D + B + 32) (by ring)) hE
  have hkD : len (memberList s) ≤ D := len_memberList_le_of_setLen hs hsD
  unfold vWk
  obtain ⟨pro, hpro⟩ : ∃ pro, pro = wkPro walkPieces Wl Wc W T s (fstIdx d') := ⟨_, rfl⟩
  rw [← hpro]
  -- the prologue's facts, by the selector's case
  have key : ∃ σ, ListOK tbl E ((8 : ℕ) : V) Γ pro ∧ NoDrop' pro ∧ shiftsV pro = σ ∧ σ ≤ 7 * D + 5 ∧
      NodeLay walkPieces Wc T (finalCtx Γ pro) (fstIdx d') ∧ Layout walkPieces Wc T (finalCtx Γ pro) s σ ∧
      neg LAct (fsetPiFact (^&(σ + (len (memberList s) + 1)))) ∈ finalCtx Γ pro ∧
      neg LAct (subsetFact (^&(len (memberList (fstIdx d')) + 1)) (^&(σ + (len (memberList s) + 1)))) ∈ finalCtx Γ pro := by
    by_cases hc0 : memberList (fstIdx d') = 0
    · -- the empty child: `proWk0 ++ emptyFsetPi`
      have hc : fstIdx d' = 0 := eq_zero_of_memberList_eq_zero hc0
      rw [hpro, wkPro, if_pos hc0]
      have hiE : 0 + 2 + (len (memberList s) + 1) + 1 ≤ E := by
        refine le_trans ?_ hE'
        calc 0 + 2 + (len (memberList s) + 1) + 1 ≤ 0 + 2 + (D + 1) + 1 :=
              add_le_add (add_le_add (le_refl _) (add_le_add hkD (le_refl 1))) (le_refl 1)
          _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 39 * D + B + 36) (by ring)
      obtain ⟨ok0, nd0, sh0, lay0, layS0, hsub0⟩ := proWk0_ok htbl hP hWp hΓ hiE hLay.layout
      obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ (proWk0 W s 0) := ⟨_, rfl⟩
      rw [← hΓ₁] at lay0 layS0 hsub0
      have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 8 htbl hΓ ok0
      have hE2 : (2 : V) ≤ E := le_trans (le_of_add_eq' (c := 40 * D + B + 38) (by ring)) hE'
      have heq1 : neg LAct (eqFactB (^&1) (𝟎 : V)) ∈ Γ₁ := by have := lay0.2; rwa [zero_add] at this
      obtain ⟨fok, fnd, fsh, ffs, fsup⟩ := emptyFsetPi_ok htbl hP hWp hΓ₁f hE2 heq1
      have hfsS : neg LAct (fsetPiFact (^&(2 + (len (memberList s) + 1)))) ∈ Γ₁ := by
        rw [hΓ₁]
        have := tr_fact nd0 (isFormula_fsetPiFact (hf_ _)) hLay.fsetPi
        rwa [sh0, shiftIterV_fsetPiFact (hf_ _), termShiftIterV_fvar, add_comm] at this
      refine ⟨2, listOK_appendV ok0 (by rw [← hΓ₁]; exact fok), noDrop'_appendV nd0 fnd,
        by rw [shiftsV_appendV, sh0, fsh, add_zero], le_of_add_eq' (c := 7 * D + 3) (by ring), ?_, ?_, ?_, ?_⟩
      · rw [finalCtx_appendV, ← hΓ₁, hc]
        exact Or.inr ⟨rfl, lay0.mono fsup, ffs⟩
      · rw [finalCtx_appendV, ← hΓ₁]
        exact (by rwa [zero_add] at layS0 : Layout walkPieces Wc T Γ₁ s 2).mono fsup
      · rw [finalCtx_appendV, ← hΓ₁]; exact fsup _ hfsS
      · rw [finalCtx_appendV, ← hΓ₁, hc, len_memberList_zero, zero_add]
        have := fsup _ hsub0
        rwa [zero_add] at this
    · -- the nonempty child: `proWk`
      have hk1 : 1 ≤ len (memberList (fstIdx d')) := one_le_len_memberList_of_ne hc0
      rw [hpro, wkPro, if_neg hc0]
      obtain ⟨pok, pnd, psh, layC, layS, hsubf⟩ :=
        proWk_ok htbl hP htblN hWl hWc hWp hs hsub hk1 hsD hcD hE13 hE14 hΓ hLay.layout
      have hσ : proSig walkPieces Wl Wc W T (fstIdx d') ≤ 6 * D + 1 :=
        proSig_le htbl hP hWc htblN hWl hWp hcs hk1 hcD hE8 hΓ
      have hk1s : 1 ≤ len (memberList s) :=
        one_le_len_memberList_of_mem (hsub (mem_memberList_iff.mp ⟨0, lt_of_lt_of_le (by simp) hk1, rfl⟩))
      refine ⟨proSig walkPieces Wl Wc W T (fstIdx d'), pok, pnd, psh, le_trans hσ (le_of_add_eq' (c := D + 4) (by ring)),
        Or.inl ⟨hk1, layC⟩, by rwa [zero_add] at layS, ?_, by rwa [zero_add, zero_add] at hsubf⟩
      have := (by rwa [zero_add] at layS : Layout walkPieces Wc T (finalCtx Γ (proWk walkPieces Wl Wc W T s (fstIdx d') 0)) s
        (proSig walkPieces Wl Wc W T (fstIdx d'))).fsetPi hk1s
      exact this
  obtain ⟨σ, pok, pnd, psh, hσ, layC, layS, hfsS, hsubf⟩ := key
  rw [psh]
  obtain ⟨ok, nd, sh, goal⟩ := wkTail_ok htbl hP htblN hWc hW₁ hs hd' hsub hsD hcD hmD hσ hE' hΓ pok pnd psh layC layS hfsS hsubf hch
  refine ⟨ok, nd, ?_, ?_⟩
  · rw [sh]
    obtain ⟨cok, cnd, csh, -⟩ := hch (finalCtx Γ pro) (finalCtx_isFormulaSet 8 htbl hΓ pok) layC
    calc σ + shiftsV L' + 3 ≤ 7 * D + 5 + B + 3 := add_le_add (add_le_add hσ csh) (le_refl 3)
      _ = 7 * D + B + 8 := by ring
  · rw [sh]; exact goal

end wkShiftOk

/-! ### 8.4 `shift`: the tail and the selector -/

section shiftOk

set_option maxHeartbeats 2000000 in
/-- **The tail of `shift`** after a prologue `pro` (shifts `σ`; the child at `0`, the parent at `σ`, `setShiftFact S s''_child`):
the child's list, `goalElim`, `nodeShift`. -/
theorem shiftTail_ok {tbl N N' B' Wc W₂ T s d' L' pro σ D B E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWc : Wc = certPieces) (hW₂ : W₂ = frag2Pieces)
    (hs : IsFormulaSet LAct s) (hd' : Derivation TAct d') (hsc : s = setShift LAct (fstIdx d'))
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (fstIdx d') ≤ D) (hmD : dlen TAct d' ≤ D) (hσ : σ ≤ 7 * D + 5)
    (hE : 40 * D + B + 40 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (pok : ListOK tbl E ((8 : ℕ) : V) Γ pro) (pnd : NoDrop' pro) (psh : shiftsV pro = σ)
    (layC : NodeLay walkPieces Wc T (finalCtx Γ pro) (fstIdx d'))
    (layS : Layout walkPieces Wc T (finalCtx Γ pro) s σ)
    (hss : neg LAct (setShiftFact (^&(σ + (len (memberList s) + 1))) (^&(len (memberList (fstIdx d')) + 1))) ∈ finalCtx Γ pro)
    (hch : ChildOK tbl Wc T E L' d' B) :
    ListOK tbl E ((9 : ℕ) : V) Γ (appendV pro (appendV L' (appendV
        (goalElim (^&(len (memberList (fstIdx d')) + 1 + shiftsV L')) (bnum (dlen TAct d')))
        (nodeShift W₂ T (σ + shiftsV L' + 2 + (len (memberList s) + 1)) (σ + shiftsV L' + 2)
          (len (memberList (fstIdx d')) + 1 + shiftsV L' + 2) 1 0 (setLen LAct s) (dlen TAct d') (dlen TAct (shiftRule s d')))))) ∧
    NoDrop' (appendV pro (appendV L' (appendV
        (goalElim (^&(len (memberList (fstIdx d')) + 1 + shiftsV L')) (bnum (dlen TAct d')))
        (nodeShift W₂ T (σ + shiftsV L' + 2 + (len (memberList s) + 1)) (σ + shiftsV L' + 2)
          (len (memberList (fstIdx d')) + 1 + shiftsV L' + 2) 1 0 (setLen LAct s) (dlen TAct d') (dlen TAct (shiftRule s d')))))) ∧
    shiftsV (appendV pro (appendV L' (appendV
        (goalElim (^&(len (memberList (fstIdx d')) + 1 + shiftsV L')) (bnum (dlen TAct d')))
        (nodeShift W₂ T (σ + shiftsV L' + 2 + (len (memberList s) + 1)) (σ + shiftsV L' + 2)
          (len (memberList (fstIdx d')) + 1 + shiftsV L' + 2) 1 0 (setLen LAct s) (dlen TAct d') (dlen TAct (shiftRule s d')))))) =
      σ + shiftsV L' + 3 ∧
    neg LAct (goalFact (^&(len (memberList s) + 1 + (σ + shiftsV L' + 3))) (bnum (dlen TAct (shiftRule s d')))) ∈
      finalCtx Γ (appendV pro (appendV L' (appendV
        (goalElim (^&(len (memberList (fstIdx d')) + 1 + shiftsV L')) (bnum (dlen TAct d')))
        (nodeShift W₂ T (σ + shiftsV L' + 2 + (len (memberList s) + 1)) (σ + shiftsV L' + 2)
          (len (memberList (fstIdx d')) + 1 + shiftsV L' + 2) 1 0 (setLen LAct s) (dlen TAct d') (dlen TAct (shiftRule s d')))))) := by
  have hD : Derivation TAct (shiftRule s d') := by rw [hsc]; exact Derivation.shiftRule ⟨rfl, hd'⟩
  have hdl : dlen TAct (shiftRule s d') = setLen LAct s + dlen TAct d' + 1 := dlen_shiftRule hD
  have hcs : IsFormulaSet LAct (fstIdx d') := DerivationOf.isFormulaSet ⟨rfl, hd'⟩
  have hkD : len (memberList s) ≤ D := len_memberList_le_of_setLen hs hsD
  have hkcD : len (memberList (fstIdx d')) ≤ D := len_memberList_le_of_setLen hcs hcD
  obtain ⟨k, hk⟩ : ∃ k, k = len (memberList s) := ⟨_, rfl⟩
  obtain ⟨kc, hkc⟩ : ∃ kc, kc = len (memberList (fstIdx d')) := ⟨_, rfl⟩
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ pro := ⟨_, rfl⟩
  rw [← hΓ₁] at layC layS hss
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 8 htbl hΓ pok
  obtain ⟨cok, cnd, csh, cgoal⟩ := hch Γ₁ hΓ₁f layC
  obtain ⟨s', hs'⟩ : ∃ s', s' = shiftsV L' := ⟨_, rfl⟩
  obtain ⟨Γ₂, hΓ₂⟩ : ∃ Γ', Γ' = finalCtx Γ₁ L' := ⟨_, rfl⟩
  rw [← hΓ₂, ← hs', ← hkc] at cgoal
  rw [← hs'] at csh
  have hΓ₂f : IsFormulaSet LAct Γ₂ := by rw [hΓ₂]; exact finalCtx_isFormulaSet 9 htbl hΓ₁f cok
  have layS₂ : Layout walkPieces Wc T Γ₂ s (σ + s') := by rw [hΓ₂, hs']; exact layS.transport cnd
  have hss₂ : neg LAct (setShiftFact (^&(σ + (k + 1) + s')) (^&(kc + 1 + s'))) ∈ Γ₂ := by
    rw [hΓ₂, hs', hk, hkc]
    have := tr_fact cnd (isFormula_setShiftFact (hf_ _) (hf_ _)) hss
    rwa [shiftIterV_setShiftFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
  -- `goalElim`
  obtain ⟨gok, gnd, gsh, -, gder, gfst, gdlen, gle⟩ :=
    goalElim_ok 9 htbl hΓ₂f (hf_ (kc + 1 + s')) (isSemiterm_bnum_LAct 0 _) cgoal
  rw [termShift_fvar, termShift_fvar] at gfst
  rw [termShift_bnum, termShift_bnum] at gle
  obtain ⟨Γ₃, hΓ₃⟩ : ∃ Γ', Γ' = finalCtx Γ₂ (goalElim (^&(kc + 1 + s')) (bnum (dlen TAct d'))) := ⟨_, rfl⟩
  rw [← hΓ₃] at gder gfst gdlen gle
  have hΓ₃f : IsFormulaSet LAct Γ₃ := by rw [hΓ₃]; exact finalCtx_isFormulaSet 9 htbl hΓ₂f gok
  have layS₃ : Layout walkPieces Wc T Γ₃ s (σ + s' + 2) := by
    rw [hΓ₃]; have := layS₂.transport gnd; rwa [gsh] at this
  have hss₃ : neg LAct (setShiftFact (^&(σ + s' + 2 + (k + 1))) (^&(kc + 1 + s' + 2))) ∈ Γ₃ := by
    rw [hΓ₃]
    have := tr_fact gnd (isFormula_setShiftFact (hf_ _) (hf_ _)) hss₂
    rw [gsh, shiftIterV_setShiftFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show σ + (k + 1) + s' + 2 = σ + s' + 2 + (k + 1) by ring] at this
  rw [show kc + 1 + s' + 1 + 1 = kc + 1 + s' + 2 by ring] at gfst
  -- the caps (each from `40·D + B + 40 ≤ E`)
  have hn1 : ‖dlen TAct (shiftRule s d')‖ ≤ 2 * D + 1 := by
    refine le_trans (length_le _) ?_
    rw [hdl]
    exact le_trans (add_le_add (add_le_add hsD hmD) (le_refl 1)) (le_of_add_eq' (c := 0) (by ring))
  have his : σ + s' + 2 + (k + 1) + 2 ≤ E := by
    refine le_trans ?_ hE
    calc σ + s' + 2 + (k + 1) + 2 ≤ (7 * D + 5) + B + 2 + (D + 1) + 2 :=
          add_le_add (add_le_add (add_le_add (add_le_add hσ csh) (le_refl 2)) (add_le_add (hk ▸ hkD) (le_refl 1))) (le_refl 2)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 32 * D + 30) (by ring)
  have hic : kc + 1 + s' + 2 + 2 ≤ E := by
    refine le_trans ?_ hE
    calc kc + 1 + s' + 2 + 2 ≤ D + 1 + B + 2 + 2 :=
          add_le_add (add_le_add (add_le_add (add_le_add (hkc ▸ hkcD) (le_refl 1)) csh) (le_refl 2)) (le_refl 2)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 39 * D + 35) (by ring)
  have hid : (1 : V) + 2 ≤ E := le_trans (le_of_add_eq' (c := 40 * D + B + 37) (by ring)) hE
  have hT : σ + s' + 2 + 0 + 7 ≤ E := by
    refine le_trans ?_ hE
    calc σ + s' + 2 + 0 + 7 ≤ (7 * D + 5) + B + 2 + 0 + 7 :=
          add_le_add (add_le_add (add_le_add (add_le_add hσ csh) (le_refl 2)) (le_refl 0)) (le_refl 7)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 33 * D + 26) (by ring)
  have hn : 18 * ‖dlen TAct (shiftRule s d')‖ + 7 ≤ E := by
    refine le_trans ?_ hE
    calc 18 * ‖dlen TAct (shiftRule s d')‖ + 7 ≤ 18 * (2 * D + 1) + 7 :=
          add_le_add (mul_le_mul_of_nonneg_left hn1 zero_le) (le_refl 7)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 4 * D + B + 15) (by ring)
  have hLn : setLen LAct s + dlen TAct d' + 1 ≤ dlen TAct (shiftRule s d') := by rw [hdl]
  -- the node
  obtain ⟨nok, nnd, nsh, -, ngoal⟩ := nodeShift_ok (E := E) (is := σ + s' + 2 + (k + 1)) (il := σ + s' + 2)
    (ic := kc + 1 + s' + 2) (id := 1) (in₁ := 0) (L := setLen LAct s) (m₁ := dlen TAct d') (n := dlen TAct (shiftRule s d'))
    htbl hP.frag2Table hW₂ htblN hΓ₃f his hic hid hT hn hLn gfst hss₃ gder gdlen gle
    (by have := layS₃.2.1; rwa [← hk] at this) layS₃.2.2
  -- assembly
  rw [← hs', ← hk, ← hkc]
  have ok₃ : ListOK tbl E ((9 : ℕ) : V) Γ₂ (appendV (goalElim (^&(kc + 1 + s')) (bnum (dlen TAct d')))
      (nodeShift W₂ T (σ + s' + 2 + (k + 1)) (σ + s' + 2) (kc + 1 + s' + 2) 1 0 (setLen LAct s) (dlen TAct d')
        (dlen TAct (shiftRule s d')))) := listOK_appendV gok (by rw [← hΓ₃]; exact nok.mono h89)
  have ok₂ := listOK_appendV cok (by rw [← hΓ₂]; exact ok₃)
  have ok₁ := listOK_appendV (pok.mono h89) (by rw [← hΓ₁]; exact ok₂)
  refine ⟨ok₁, noDrop'_appendV pnd (noDrop'_appendV cnd (noDrop'_appendV gnd nnd)), ?_, ?_⟩
  · rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, psh, ← hs', gsh, nsh]; ring
  · rw [finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂, ← hΓ₃,
      show k + 1 + (σ + s' + 3) = σ + s' + 2 + (k + 1) + 1 by ring]
    exact ngoal


/-- **The `shift` list is applicable** at the node's layout: the selector's two cases, then the common tail. -/
theorem vShift_ok {tbl N N' B' Wl Wc W₂ W T s d' L' D B E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces) (hW₂ : W₂ = frag2Pieces)
    (hs : IsFormulaSet LAct s) (hd' : Derivation TAct d') (hsc : s = setShift LAct (fstIdx d'))
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (fstIdx d') ≤ D) (hmD : dlen TAct d' ≤ D)
    (hE : 40 * D + 18 * ‖D‖ + B + 40 ≤ E) (hΓ : IsFormulaSet LAct Γ) (hLay : NodeLay walkPieces Wc T Γ s)
    (hch : ChildOK tbl Wc T E L' d' B) :
    ListOK tbl E ((9 : ℕ) : V) Γ (vShift walkPieces Wl Wc W₂ W T s d' L') ∧ NoDrop' (vShift walkPieces Wl Wc W₂ W T s d' L') ∧
    shiftsV (vShift walkPieces Wl Wc W₂ W T s d' L') ≤ 7 * D + B + 8 ∧
    neg LAct (goalFact (^&(len (memberList s) + 1 + shiftsV (vShift walkPieces Wl Wc W₂ W T s d' L')))
      (bnum (dlen TAct (shiftRule s d')))) ∈ finalCtx Γ (vShift walkPieces Wl Wc W₂ W T s d' L') := by
  have hcs : IsFormulaSet LAct (fstIdx d') := DerivationOf.isFormulaSet ⟨rfl, hd'⟩
  have hE' : 40 * D + B + 40 ≤ E := le_trans (le_of_add_eq' (c := 18 * ‖D‖) (by ring)) hE
  have hE13 : 13 * D + 18 * ‖D‖ + 12 ≤ E := le_trans (le_of_add_eq' (c := 27 * D + B + 28) (by ring)) hE
  have hE16 : 0 + 16 * D + 8 ≤ E := le_trans (le_of_add_eq' (c := 24 * D + 18 * ‖D‖ + B + 32) (by ring)) hE
  have hE8 : 13 * D + 18 * ‖D‖ + 8 ≤ E := le_trans (le_of_add_eq' (c := 27 * D + B + 32) (by ring)) hE
  have hE7 : (7 : V) ≤ E := le_trans (le_of_add_eq' (c := 40 * D + B + 33) (by ring)) hE'
  have hkcD : len (memberList (fstIdx d')) ≤ D := len_memberList_le_of_setLen hcs hcD
  unfold vShift
  obtain ⟨pro, hpro⟩ : ∃ pro, pro = shiftPro walkPieces Wl Wc W T s (fstIdx d') := ⟨_, rfl⟩
  rw [← hpro]
  have key : ∃ σ, ListOK tbl E ((8 : ℕ) : V) Γ pro ∧ NoDrop' pro ∧ shiftsV pro = σ ∧ σ ≤ 7 * D + 5 ∧
      NodeLay walkPieces Wc T (finalCtx Γ pro) (fstIdx d') ∧ Layout walkPieces Wc T (finalCtx Γ pro) s σ ∧
      neg LAct (setShiftFact (^&(σ + (len (memberList s) + 1))) (^&(len (memberList (fstIdx d')) + 1))) ∈ finalCtx Γ pro := by
    by_cases hc0 : memberList (fstIdx d') = 0
    · -- the empty child (hence the empty parent): `proShift0 ++ reset0 ++ emptyFsetPi`
      have hc : fstIdx d' = 0 := eq_zero_of_memberList_eq_zero hc0
      have hs0 : s = 0 := by rw [hsc, hc]; exact setShift_empty
      have hLay0 : Layout0 walkPieces Wc T Γ 0 := by
        rcases hLay with ⟨hk, -⟩ | ⟨-, h, -⟩
        · exfalso; rw [hs0, len_memberList_zero] at hk; exact absurd hk (by simp)
        · exact h
      rw [hpro, shiftPro, if_pos hc0]
      have hiE : (0 : V) + 3 + 1 + 1 ≤ E := le_trans (by norm_num) hE7
      obtain ⟨ok0, nd0, sh0, layC1, layP3, hss0⟩ := proShift0_ok htbl hP hWp hΓ hiE hLay0
      obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ (proShift0 W 0) := ⟨_, rfl⟩
      rw [← hΓ₁] at layC1 layP3 hss0
      have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 8 htbl hΓ ok0
      rw [zero_add] at layP3
      rw [show (0 : V) + 3 + 1 = 4 by norm_num] at hss0
      obtain ⟨rok, rnd, rsh, layC0, layP5, hss1⟩ := reset0_ok htbl hP hWp hΓ₁f hE7 layC1 layP3 hss0
      obtain ⟨Γ₂, hΓ₂⟩ : ∃ Γ', Γ' = finalCtx Γ₁ (reset0 W) := ⟨_, rfl⟩
      rw [← hΓ₂] at layC0 layP5 hss1
      have hΓ₂f : IsFormulaSet LAct Γ₂ := by rw [hΓ₂]; exact finalCtx_isFormulaSet 8 htbl hΓ₁f rok
      have hE2 : (2 : V) ≤ E := le_trans (by norm_num) hE7
      have heq1 : neg LAct (eqFactB (^&1) (𝟎 : V)) ∈ Γ₂ := by have := layC0.2; rwa [zero_add] at this
      obtain ⟨fok, fnd, fsh, ffs, fsup⟩ := emptyFsetPi_ok htbl hP hWp hΓ₂f hE2 heq1
      refine ⟨5, listOK_appendV ok0 (by rw [← hΓ₁]; exact listOK_appendV rok (by rw [← hΓ₂]; exact fok)),
        noDrop'_appendV nd0 (noDrop'_appendV rnd fnd),
        by rw [shiftsV_appendV, shiftsV_appendV, sh0, rsh, fsh]; norm_num,
        le_of_add_eq' (c := 7 * D) (by ring), ?_, ?_, ?_⟩
      · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂, hc]
        exact Or.inr ⟨rfl, layC0.mono fsup, ffs⟩
      · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂, hs0]
        exact layP5.1.mono fsup
      · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂, hs0, hc, len_memberList_zero,
          show (5 : V) + (0 + 1) = 6 by norm_num, zero_add]
        exact fsup _ hss1
    · -- the nonempty child: `proShift`
      have hk1 : 1 ≤ len (memberList (fstIdx d')) := one_le_len_memberList_of_ne hc0
      rw [hpro, shiftPro, if_neg hc0]
      obtain ⟨pok, pnd, psh, layC, layS, hss⟩ :=
        proShift_ok htbl hP htblN hWl hWc hWp hs hcs hsc hk1 hsD hcD hE13 hE16 hΓ hLay.layout
      have hσ : proSig walkPieces Wl Wc W T (fstIdx d') ≤ 6 * D + 1 :=
        proSig_le htbl hP hWc htblN hWl hWp hcs hk1 hcD hE8 hΓ
      refine ⟨1 + (len (memberList (fstIdx d')) + 1) + proSig walkPieces Wl Wc W T (fstIdx d'), pok, pnd, psh, ?_,
        Or.inl ⟨hk1, layC⟩, by rwa [zero_add] at layS, by rwa [zero_add, zero_add] at hss⟩
      calc 1 + (len (memberList (fstIdx d')) + 1) + proSig walkPieces Wl Wc W T (fstIdx d') ≤ 1 + (D + 1) + (6 * D + 1) :=
            add_le_add (add_le_add (le_refl 1) (add_le_add hkcD (le_refl 1))) hσ
        _ ≤ 7 * D + 5 := le_of_add_eq' (c := 2) (by ring)
  obtain ⟨σ, pok, pnd, psh, hσ, layC, layS, hss⟩ := key
  rw [psh]
  obtain ⟨ok, nd, sh, goal⟩ := shiftTail_ok htbl hP htblN hWc hW₂ hs hd' hsc hsD hcD hmD hσ hE' hΓ pok pnd psh layC layS hss hch
  refine ⟨ok, nd, ?_, ?_⟩
  · rw [sh]
    obtain ⟨cok, cnd, csh, -⟩ := hch (finalCtx Γ pro) (finalCtx_isFormulaSet 8 htbl hΓ pok) layC
    calc σ + shiftsV L' + 3 ≤ 7 * D + 5 + B + 3 := add_le_add (add_le_add hσ csh) (le_refl 3)
      _ = 7 * D + B + 8 := by ring
  · rw [sh]; exact goal

end shiftOk

/-! ### 8.5 `or`: `proOr`, the child, `postIns`, `nodeOr` -/

section orOk

lemma descCountF_le_of_len {tbl N q D : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hq : IsSemiformula LAct 0 q)
    (hqD : formulaLen LAct q ≤ D) : descCountF walkPieces 0 q ≤ 2 * D := by
  obtain ⟨-, -, -, h, -⟩ := describeF_ok htbl hW hq (E := 2 * 0 + 2 * formulaLen LAct q + 8) le_rfl (Γ := 0) IsFormulaSet.empty
  exact le_trans le_self_add (le_trans h (mul_le_mul_of_nonneg_left hqD zero_le))

set_option maxHeartbeats 4000000 in
/-- **The `or` list is applicable** at the node's layout. -/
theorem vOr_ok {tbl N N' B' Wl Wc W₁ W T s p q d' L' D B E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces) (hW₁ : W₁ = frag1Pieces)
    (hs : IsFormulaSet LAct s) (hpq : p ^⋎ q ∈ s) (hd' : DerivationOf TAct d' (insert p (insert q s)))
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (insert p (insert q s)) ≤ D) (hmD : dlen TAct d' ≤ D)
    (hE : 40 * D + 18 * ‖D‖ + B + 40 ≤ E) (hΓ : IsFormulaSet LAct Γ) (hLay : NodeLay walkPieces Wc T Γ s)
    (hch : ChildOK tbl Wc T E L' d' B) :
    ListOK tbl E ((9 : ℕ) : V) Γ (vOr walkPieces Wl Wc W₁ W T s p q d' L') ∧ NoDrop' (vOr walkPieces Wl Wc W₁ W T s p q d' L') ∧
    shiftsV (vOr walkPieces Wl Wc W₁ W T s p q d' L') ≤ 12 * D + B + 7 ∧
    neg LAct (goalFact (^&(len (memberList s) + 1 + shiftsV (vOr walkPieces Wl Wc W₁ W T s p q d' L')))
      (bnum (dlen TAct (orIntro s p q d')))) ∈ finalCtx Γ (vOr walkPieces Wl Wc W₁ W T s p q d' L') := by
  have hW : WalkTable tbl := hP.walkTable
  have hpqf : IsSemiformula LAct 0 (p ^⋎ q) := hs _ hpq
  obtain ⟨hp, hq⟩ := IsSemiformula.or.mp hpqf
  have hD : Derivation TAct (orIntro s p q d') := Derivation.orIntro hpq hd'
  have hdl : dlen TAct (orIntro s p q d') = setLen LAct s + dlen TAct d' + 1 := dlen_orIntro hD
  have hk1 : 1 ≤ len (memberList s) := one_le_len_memberList_of_mem hpq
  have hLayS : Layout walkPieces Wc T Γ s 0 := hLay.layout
  have hcfst : fstIdx d' = insert p (insert q s) := hd'.1
  have hkD : len (memberList s) ≤ D := len_memberList_le_of_setLen hs hsD
  have hcs : IsFormulaSet LAct (insert p (insert q s)) := DerivationOf.isFormulaSet hd'
  have hkcD : len (memberList (insert p (insert q s))) ≤ D := len_memberList_le_of_setLen hcs hcD
  have hqD : formulaLen LAct q ≤ D := le_trans (formulaLen_le_setLen_of_mem (by simp)) hcD
  have hqs : IsFormulaSet LAct (insert q s) := IsFormulaSet.insert_iff.mpr ⟨hq, hs⟩
  have hqsD : setLen LAct (insert q s) ≤ D := le_trans (setLen_le_insert _ _) hcD
  -- the parent's dossiers of `p`, `q` and the `or` fact
  obtain ⟨hor, hDp, hDq, hmr⟩ := layout_or htbl hP hp hq hpq hLayS
  rw [zero_add] at hmr
  obtain ⟨ir₀, hir₀⟩ : ∃ x, x = memTop walkPieces Wc T s (p ^⋎ q) 0 := ⟨_, rfl⟩
  have hir₀D : ir₀ ≤ 6 * D + 1 := by
    rw [hir₀]; have := memTop_le htbl hW hWc T hs hpq hsD (i := 0); rwa [zero_add] at this
  have hcq : descCountF walkPieces 0 q ≤ 2 * D := descCountF_le_of_len htbl hW hq hqD
  rw [← hir₀] at hor hDp hDq hmr
  -- the caps
  have hE' : 40 * D + B + 40 ≤ E := le_trans (le_of_add_eq' (c := 18 * ‖D‖) (by ring)) hE
  have hE13 : 13 * D + 18 * ‖D‖ + 12 ≤ E := le_trans (le_of_add_eq' (c := 27 * D + B + 28) (by ring)) hE
  have hE8 : 13 * D + 18 * ‖D‖ + 8 ≤ E := le_trans (le_of_add_eq' (c := 27 * D + B + 32) (by ring)) hE
  have hiE : 0 + 14 * D + 5 ≤ E := le_trans (le_of_add_eq' (c := 26 * D + 18 * ‖D‖ + B + 35) (by ring)) hE
  have hipE : ir₀ + descCountF walkPieces 0 q + 1 + 14 * D + 6 ≤ E := by
    refine le_trans ?_ hE'
    calc ir₀ + descCountF walkPieces 0 q + 1 + 14 * D + 6 ≤ (6 * D + 1) + 2 * D + 1 + 14 * D + 6 :=
          add_le_add (add_le_add (add_le_add (add_le_add hir₀D hcq) (le_refl 1)) (le_refl _)) (le_refl 6)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 18 * D + B + 32) (by ring)
  have hiqE : ir₀ + 1 + 8 * D + 4 ≤ E := by
    refine le_trans ?_ hE'
    calc ir₀ + 1 + 8 * D + 4 ≤ (6 * D + 1) + 1 + 8 * D + 4 := add_le_add (add_le_add (add_le_add hir₀D (le_refl 1)) (le_refl _)) (le_refl 4)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 26 * D + B + 34) (by ring)
  -- the prologue
  obtain ⟨pok, pnd, psh, layC, layS, hiq', hip', heq⟩ :=
    proOr_ok htbl hP htblN hWl hWc hWp hs hp hq hk1 hcD hE13 hiE hipE hiqE hΓ hLayS hDp hDq
  obtain ⟨σq, hσq⟩ : ∃ x, x = proSig walkPieces Wl Wc W T (insert q s) := ⟨_, rfl⟩
  obtain ⟨σc, hσc⟩ : ∃ x, x = proSig walkPieces Wl Wc W T (insert p (insert q s)) := ⟨_, rfl⟩
  have hσqD : σq ≤ 6 * D + 1 := by
    rw [hσq]; exact proSig_le htbl hP hWc htblN hWl hWp hqs (one_le_len_memberList_insert _ _) hqsD hE8 hΓ
  have hσcD : σc ≤ 6 * D + 1 := by
    rw [hσc]; exact proSig_le htbl hP hWc htblN hWl hWp hcs (one_le_len_memberList_insert _ _) hcD hE8 hΓ
  obtain ⟨k, hk⟩ : ∃ k, k = len (memberList s) := ⟨_, rfl⟩
  obtain ⟨kc, hkc⟩ : ∃ kc, kc = len (memberList (insert p (insert q s))) := ⟨_, rfl⟩
  rw [← hσq, ← hσc] at psh layS hiq' hip'
  rw [← hσc, ← hkc] at heq
  rw [← hk] at hiq'
  simp only [zero_add] at layS hiq' hip' heq
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ (proOr walkPieces Wl Wc W T s p q 0 (ir₀ + descCountF walkPieces 0 q + 1) (ir₀ + 1)) := ⟨_, rfl⟩
  rw [← hΓ₁] at layC layS hiq' hip' heq
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 8 htbl hΓ pok
  have layC' : NodeLay walkPieces Wc T Γ₁ (fstIdx d') := by rw [hcfst]; exact Or.inl ⟨one_le_len_memberList_insert _ _, layC⟩
  -- the child
  obtain ⟨cok, cnd, csh, cgoal⟩ := hch Γ₁ hΓ₁f layC'
  obtain ⟨s', hs'⟩ : ∃ s', s' = shiftsV L' := ⟨_, rfl⟩
  obtain ⟨Γ₂, hΓ₂⟩ : ∃ Γ', Γ' = finalCtx Γ₁ L' := ⟨_, rfl⟩
  rw [← hΓ₂, ← hs', hcfst, ← hkc] at cgoal
  rw [← hs'] at csh
  have hΓ₂f : IsFormulaSet LAct Γ₂ := by rw [hΓ₂]; exact finalCtx_isFormulaSet 9 htbl hΓ₁f cok
  have heq₂ : neg LAct (eqFactB (^&(σc + s')) (^&(kc + 1 + s'))) ∈ Γ₂ := by
    rw [hΓ₂, hs']
    have := tr_fact cnd (isFormula_eqFactB (hf_ _) (hf_ _)) heq
    rwa [shiftIterV_eqFactB (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
  -- `postIns`
  have hsE : kc + 1 + s' + 3 ≤ E := by
    refine le_trans ?_ hE'
    calc kc + 1 + s' + 3 ≤ D + 1 + B + 3 := add_le_add (add_le_add (add_le_add (hkc ▸ hkcD) (le_refl 1)) csh) (le_refl 3)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 39 * D + 36) (by ring)
  have hcE : σc + s' + 3 ≤ E := by
    refine le_trans ?_ hE'
    calc σc + s' + 3 ≤ (6 * D + 1) + B + 3 := add_le_add (add_le_add hσcD csh) (le_refl 3)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 34 * D + 36) (by ring)
  obtain ⟨qok, qnd, qsh, -, qder, qfst, qdlen, qle⟩ := postIns_ok htbl hP hWp hΓ₂f hsE hcE cgoal heq₂
  obtain ⟨Γ₃, hΓ₃⟩ : ∃ Γ', Γ' = finalCtx Γ₂ (postIns W (kc + 1 + s') (σc + s') (dlen TAct d')) := ⟨_, rfl⟩
  rw [← hΓ₃] at qder qfst qdlen qle
  have hΓ₃f : IsFormulaSet LAct Γ₃ := by rw [hΓ₃]; exact finalCtx_isFormulaSet 8 htbl hΓ₂f qok
  -- transports Γ₁ → Γ₃ (through `L' ++ postIns`, `s' + 2` shifts) and Γ → Γ₁ → Γ₃
  have hΓ₃e : Γ₃ = finalCtx Γ₁ (appendV L' (postIns W (kc + 1 + s') (σc + s') (dlen TAct d'))) := by
    rw [finalCtx_appendV, ← hΓ₂, hΓ₃]
  have hnd₂ : NoDrop' (appendV L' (postIns W (kc + 1 + s') (σc + s') (dlen TAct d'))) := noDrop'_appendV cnd qnd
  have hsh₂ : shiftsV (appendV L' (postIns W (kc + 1 + s') (σc + s') (dlen TAct d'))) = s' + 2 := by
    rw [shiftsV_appendV, qsh, hs']
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = 1 + σq + (1 + σc) + s' + 2 := ⟨_, rfl⟩
  have layS₃ : Layout walkPieces Wc T Γ₃ s τ := by
    rw [hΓ₃e, hτ]; have := layS.transport hnd₂; rwa [hsh₂, ← add_assoc] at this
  have hiq'₃ : neg LAct (insFact (^&(σq + (1 + σc) + s' + 2)) (^&(ir₀ + 1 + τ)) (^&(τ + (k + 1)))) ∈ Γ₃ := by
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_insFact (hf_ _) (hf_ _) (hf_ _)) hiq'
    rw [hsh₂, shiftIterV_insFact (hf_ _) (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show σq + (1 + σc) + (s' + 2) = σq + (1 + σc) + s' + 2 by ring,
      show ir₀ + 1 + 1 + σq + (1 + σc) + (s' + 2) = ir₀ + 1 + τ by rw [hτ]; ring,
      show 1 + σq + (k + 1) + (1 + σc) + (s' + 2) = τ + (k + 1) by rw [hτ]; ring] at this
  have hip'₃ : neg LAct (insFact (^&(σc + s' + 2)) (^&(ir₀ + descCountF walkPieces 0 q + 1 + τ)) (^&(σq + (1 + σc) + s' + 2))) ∈ Γ₃ := by
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_insFact (hf_ _) (hf_ _) (hf_ _)) hip'
    rw [hsh₂, shiftIterV_insFact (hf_ _) (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show σc + (s' + 2) = σc + s' + 2 by ring,
      show ir₀ + descCountF walkPieces 0 q + 1 + 1 + σq + 1 + σc + (s' + 2) = ir₀ + descCountF walkPieces 0 q + 1 + τ by rw [hτ]; ring,
      show σq + (1 + σc) + (s' + 2) = σq + (1 + σc) + s' + 2 by ring] at this
  have hor₃ : neg LAct (orFact (^&(ir₀ + τ)) (^&(ir₀ + descCountF walkPieces 0 q + 1 + τ)) (^&(ir₀ + 1 + τ))) ∈ Γ₃ := by
    have h1 := tr_fact pnd (isFormula_orFact (hf_ _) (hf_ _) (hf_ _)) hor
    rw [psh, shiftIterV_orFact (hf_ _) (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar, ← hΓ₁] at h1
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_orFact (hf_ _) (hf_ _) (hf_ _)) h1
    rw [hsh₂, shiftIterV_orFact (hf_ _) (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show ir₀ + (1 + σq + (1 + σc)) + (s' + 2) = ir₀ + τ by rw [hτ]; ring,
      show ir₀ + descCountF walkPieces 0 q + 1 + (1 + σq + (1 + σc)) + (s' + 2) = ir₀ + descCountF walkPieces 0 q + 1 + τ by rw [hτ]; ring,
      show ir₀ + 1 + (1 + σq + (1 + σc)) + (s' + 2) = ir₀ + 1 + τ by rw [hτ]; ring] at this
  have hmr₃ : neg LAct (memFact (^&(ir₀ + τ)) (^&(τ + (k + 1)))) ∈ Γ₃ := by
    have h1 := tr_fact pnd (isFormula_memFact (hf_ _) (hf_ _)) hmr
    rw [psh, shiftIterV_memFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, ← hΓ₁] at h1
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_memFact (hf_ _) (hf_ _)) h1
    rw [hsh₂, shiftIterV_memFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show ir₀ + (1 + σq + (1 + σc)) + (s' + 2) = ir₀ + τ by rw [hτ]; ring,
      show len (memberList s) + 1 + (1 + σq + (1 + σc)) + (s' + 2) = τ + (k + 1) by rw [hτ, hk]; ring] at this
  -- the node's caps
  have hτD : τ ≤ 12 * D + B + 6 := by
    rw [hτ]
    calc 1 + σq + (1 + σc) + s' + 2 ≤ 1 + (6 * D + 1) + (1 + (6 * D + 1)) + B + 2 :=
          add_le_add (add_le_add (add_le_add (add_le_add (le_refl 1) hσqD) (add_le_add (le_refl 1) hσcD)) csh) (le_refl 2)
      _ = 12 * D + B + 6 := by ring
  have his : τ + (k + 1) + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc τ + (k + 1) + 2 ≤ (12 * D + B + 6) + (D + 1) + 2 := add_le_add (add_le_add hτD (add_le_add (hk ▸ hkD) (le_refl 1))) (le_refl 2)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 27 * D + 31) (by ring)
  have hir : ir₀ + τ + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc ir₀ + τ + 2 ≤ (6 * D + 1) + (12 * D + B + 6) + 2 := add_le_add (add_le_add hir₀D hτD) (le_refl 2)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 22 * D + 31) (by ring)
  have hip : ir₀ + descCountF walkPieces 0 q + 1 + τ + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc ir₀ + descCountF walkPieces 0 q + 1 + τ + 2 ≤ (6 * D + 1) + 2 * D + 1 + (12 * D + B + 6) + 2 :=
          add_le_add (add_le_add (add_le_add (add_le_add hir₀D hcq) (le_refl 1)) hτD) (le_refl 2)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 20 * D + 30) (by ring)
  have hiq : ir₀ + 1 + τ + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc ir₀ + 1 + τ + 2 ≤ (6 * D + 1) + 1 + (12 * D + B + 6) + 2 := add_le_add (add_le_add (add_le_add hir₀D (le_refl 1)) hτD) (le_refl 2)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 22 * D + 30) (by ring)
  have hid : (1 : V) + 2 ≤ E := le_trans (le_of_add_eq' (c := 40 * D + B + 37) (by ring)) hE'
  have hicq : σq + (1 + σc) + s' + 2 + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc σq + (1 + σc) + s' + 2 + 2 ≤ (6 * D + 1) + (1 + (6 * D + 1)) + B + 2 + 2 :=
          add_le_add (add_le_add (add_le_add (add_le_add hσqD (add_le_add (le_refl 1) hσcD)) csh) (le_refl 2)) (le_refl 2)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 28 * D + 33) (by ring)
  have hic : σc + s' + 2 + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc σc + s' + 2 + 2 ≤ (6 * D + 1) + B + 2 + 2 := add_le_add (add_le_add (add_le_add hσcD csh) (le_refl 2)) (le_refl 2)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 34 * D + 35) (by ring)
  have hT : τ + 0 + 7 ≤ E := by
    refine le_trans ?_ hE'
    calc τ + 0 + 7 ≤ (12 * D + B + 6) + 0 + 7 := add_le_add (add_le_add hτD (le_refl 0)) (le_refl 7)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 28 * D + 27) (by ring)
  have hn : 18 * ‖dlen TAct (orIntro s p q d')‖ + 7 ≤ E := by
    have hn1 : ‖dlen TAct (orIntro s p q d')‖ ≤ 2 * D + 1 := by
      refine le_trans (length_le _) ?_
      rw [hdl]
      exact le_trans (add_le_add (add_le_add hsD hmD) (le_refl 1)) (le_of_add_eq' (c := 0) (by ring))
    refine le_trans ?_ hE'
    calc 18 * ‖dlen TAct (orIntro s p q d')‖ + 7 ≤ 18 * (2 * D + 1) + 7 :=
          add_le_add (mul_le_mul_of_nonneg_left hn1 zero_le) (le_refl 7)
      _ ≤ 40 * D + B + 40 := le_of_add_eq' (c := 4 * D + B + 15) (by ring)
  have hLn : setLen LAct s + dlen TAct d' + 1 ≤ dlen TAct (orIntro s p q d') := by rw [hdl]
  -- the node
  obtain ⟨nok, nnd, nsh, -, ngoal⟩ := nodeOr_ok (E := E) (is := τ + (k + 1)) (il := τ) (ir := ir₀ + τ)
    (ip := ir₀ + descCountF walkPieces 0 q + 1 + τ) (iq := ir₀ + 1 + τ) (id := 1) (icq := σq + (1 + σc) + s' + 2)
    (ic := σc + s' + 2) (in₁ := 0) (L := setLen LAct s) (m₁ := dlen TAct d') (n := dlen TAct (orIntro s p q d'))
    htbl hP.frag1Table hW₁ htblN hΓ₃f his hir hip hiq hid hicq hic hT hn hLn hor₃ hmr₃ qfst hiq'₃ hip'₃ qder qdlen qle
    (by have := layS₃.2.1; rwa [← hk] at this) layS₃.2.2
  -- assembly
  unfold vOr
  rw [← hir₀, ← hσq, ← hσc, ← hs', ← hk, ← hkc]
  rw [show 1 + σq + (1 + σc) + s' + 2 = τ by rw [hτ]]
  have ok₃ : ListOK tbl E ((9 : ℕ) : V) Γ₂ (appendV (postIns W (kc + 1 + s') (σc + s') (dlen TAct d'))
      (nodeOr W₁ T (τ + (k + 1)) τ (ir₀ + τ) (ir₀ + descCountF walkPieces 0 q + 1 + τ) (ir₀ + 1 + τ) 1
        (σq + (1 + σc) + s' + 2) (σc + s' + 2) 0 (setLen LAct s) (dlen TAct d') (dlen TAct (orIntro s p q d')))) :=
    listOK_appendV (qok.mono h89) (by rw [← hΓ₃]; exact nok.mono h89)
  have ok₂ := listOK_appendV cok (by rw [← hΓ₂]; exact ok₃)
  have ok₁ := listOK_appendV (pok.mono h89) (by rw [← hΓ₁]; exact ok₂)
  refine ⟨ok₁, noDrop'_appendV pnd (noDrop'_appendV cnd (noDrop'_appendV qnd nnd)), ?_, ?_⟩
  · rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, psh, ← hs', qsh, nsh]
    calc 1 + σq + (1 + σc) + (s' + (2 + 1)) ≤ 1 + (6 * D + 1) + (1 + (6 * D + 1)) + (B + (2 + 1)) :=
          add_le_add (add_le_add (add_le_add (le_refl 1) hσqD) (add_le_add (le_refl 1) hσcD)) (add_le_add csh (le_refl _))
      _ = 12 * D + B + 7 := by ring
  · rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, psh, ← hs', qsh, nsh,
      finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂, ← hΓ₃,
      show k + 1 + (1 + σq + (1 + σc) + (s' + (2 + 1))) = τ + (k + 1) + 1 by rw [hτ]; ring]
    exact ngoal

end orOk

/-! ### 8.6 `and`: two `proIns`/child/`postIns` blocks, then `nodeAnd` -/

section andOk

set_option maxHeartbeats 6000000 in
/-- **The `and` list is applicable** at the node's layout (both children's lists bounded by `B`). -/
theorem vAnd_ok {tbl N N' B' Wl Wc W₁ W T s p q dp dq L₁ L₂ D B₁ B₂ E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces) (hW₁ : W₁ = frag1Pieces)
    (hs : IsFormulaSet LAct s) (hpq : p ^⋏ q ∈ s)
    (hdp : DerivationOf TAct dp (insert p s)) (hdq : DerivationOf TAct dq (insert q s))
    (hsD : setLen LAct s ≤ D) (hc₁D : setLen LAct (insert p s) ≤ D) (hc₂D : setLen LAct (insert q s) ≤ D)
    (hm₁D : dlen TAct dp ≤ D) (hm₂D : dlen TAct dq ≤ D)
    (hE : 60 * D + 18 * ‖D‖ + B₁ + 2 * B₂ + 60 ≤ E) (hΓ : IsFormulaSet LAct Γ) (hLay : NodeLay walkPieces Wc T Γ s)
    (hch₁ : ChildOK tbl Wc T E L₁ dp B₁) (hch₂ : ChildOK tbl Wc T E L₂ dq B₂) :
    ListOK tbl E ((9 : ℕ) : V) Γ (vAnd walkPieces Wl Wc W₁ W T s p q dp dq L₁ L₂) ∧
    NoDrop' (vAnd walkPieces Wl Wc W₁ W T s p q dp dq L₁ L₂) ∧
    shiftsV (vAnd walkPieces Wl Wc W₁ W T s p q dp dq L₁ L₂) ≤ 12 * D + B₁ + B₂ + 9 ∧
    neg LAct (goalFact (^&(len (memberList s) + 1 + shiftsV (vAnd walkPieces Wl Wc W₁ W T s p q dp dq L₁ L₂)))
      (bnum (dlen TAct (andIntro s p q dp dq)))) ∈ finalCtx Γ (vAnd walkPieces Wl Wc W₁ W T s p q dp dq L₁ L₂) := by
  have hW : WalkTable tbl := hP.walkTable
  have hpqf : IsSemiformula LAct 0 (p ^⋏ q) := hs _ hpq
  obtain ⟨hp, hq⟩ := IsSemiformula.and.mp hpqf
  have hD : Derivation TAct (andIntro s p q dp dq) := Derivation.andIntro hpq hdp hdq
  have hdl : dlen TAct (andIntro s p q dp dq) = setLen LAct s + dlen TAct dp + dlen TAct dq + 1 := dlen_andIntro hD
  have hk1 : 1 ≤ len (memberList s) := one_le_len_memberList_of_mem hpq
  have hLayS : Layout walkPieces Wc T Γ s 0 := hLay.layout
  have hfst₁ : fstIdx dp = insert p s := hdp.1
  have hfst₂ : fstIdx dq = insert q s := hdq.1
  have hkD : len (memberList s) ≤ D := len_memberList_le_of_setLen hs hsD
  have hc₁ : IsFormulaSet LAct (insert p s) := DerivationOf.isFormulaSet hdp
  have hc₂ : IsFormulaSet LAct (insert q s) := DerivationOf.isFormulaSet hdq
  have hk₁D : len (memberList (insert p s)) ≤ D := len_memberList_le_of_setLen hc₁ hc₁D
  have hk₂D : len (memberList (insert q s)) ≤ D := len_memberList_le_of_setLen hc₂ hc₂D
  have hqD : formulaLen LAct q ≤ D := le_trans (formulaLen_le_setLen_of_mem (by simp)) hc₂D
  -- the parent's dossiers and the `and` fact
  obtain ⟨hand, hDp, hDq, hmr⟩ := layout_and htbl hP hp hq hpq hLayS
  rw [zero_add] at hmr
  obtain ⟨ir₀, hir₀⟩ : ∃ x, x = memTop walkPieces Wc T s (p ^⋏ q) 0 := ⟨_, rfl⟩
  have hir₀D : ir₀ ≤ 6 * D + 1 := by
    rw [hir₀]; have := memTop_le htbl hW hWc T hs hpq hsD (i := 0); rwa [zero_add] at this
  have hcq : descCountF walkPieces 0 q ≤ 2 * D := descCountF_le_of_len htbl hW hq hqD
  rw [← hir₀] at hand hDp hDq hmr
  obtain ⟨cq, hcqd⟩ : ∃ x, x = descCountF walkPieces 0 q := ⟨_, rfl⟩
  rw [← hcqd] at hand hDp hcq
  -- the caps
  have hE' : 40 * D + B₁ + 40 ≤ E := le_trans (le_of_add_eq' (c := 20 * D + 18 * ‖D‖ + 2 * B₂ + 20) (by ring)) hE
  have hE₂' : 40 * D + B₂ + 40 ≤ E := le_trans (le_of_add_eq' (c := 20 * D + 18 * ‖D‖ + B₁ + B₂ + 20) (by ring)) hE
  have hE'' : 60 * D + B₁ + 2 * B₂ + 60 ≤ E := le_trans (le_of_add_eq' (c := 18 * ‖D‖) (by ring)) hE
  have hE13 : 13 * D + 18 * ‖D‖ + 12 ≤ E := le_trans (le_of_add_eq' (c := 47 * D + B₁ + 2 * B₂ + 48) (by ring)) hE
  have hE8 : 13 * D + 18 * ‖D‖ + 8 ≤ E := le_trans (le_of_add_eq' (c := 47 * D + B₁ + 2 * B₂ + 52) (by ring)) hE
  have hiE₁ : 0 + 14 * D + 5 ≤ E := le_trans (le_of_add_eq' (c := 26 * D + B₁ + 35) (by ring)) hE'
  have hipE₁ : ir₀ + cq + 1 + 8 * D + 4 ≤ E := by
    refine le_trans ?_ hE'
    calc ir₀ + cq + 1 + 8 * D + 4 ≤ (6 * D + 1) + 2 * D + 1 + 8 * D + 4 :=
          add_le_add (add_le_add (add_le_add (add_le_add hir₀D hcq) (le_refl 1)) (le_refl _)) (le_refl 4)
      _ ≤ 40 * D + B₁ + 40 := le_of_add_eq' (c := 24 * D + B₁ + 34) (by ring)
  -- block 1: `proIns s p 0 ip₀`
  obtain ⟨pok₁, pnd₁, psh₁, layC₁, fr₁, heq₁⟩ :=
    proIns_ok htbl hP htblN hWl hWc hWp hs hp hk1 hc₁D hE13 hiE₁ hipE₁ hΓ hLayS hDp
  obtain ⟨σ₁, hσ₁⟩ : ∃ x, x = proSig walkPieces Wl Wc W T (insert p s) := ⟨_, rfl⟩
  obtain ⟨σ₂, hσ₂⟩ : ∃ x, x = proSig walkPieces Wl Wc W T (insert q s) := ⟨_, rfl⟩
  have hσ₁D : σ₁ ≤ 6 * D + 1 := by
    rw [hσ₁]; exact proSig_le htbl hP hWc htblN hWl hWp hc₁ (one_le_len_memberList_insert _ _) hc₁D hE8 hΓ
  have hσ₂D : σ₂ ≤ 6 * D + 1 := by
    rw [hσ₂]; exact proSig_le htbl hP hWc htblN hWl hWp hc₂ (one_le_len_memberList_insert _ _) hc₂D hE8 hΓ
  obtain ⟨k, hk⟩ : ∃ k, k = len (memberList s) := ⟨_, rfl⟩
  obtain ⟨k₁, hk₁⟩ : ∃ x, x = len (memberList (insert p s)) := ⟨_, rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ x, x = len (memberList (insert q s)) := ⟨_, rfl⟩
  rw [← hσ₁] at psh₁ fr₁ heq₁
  obtain ⟨-, layS₁, -, hcp₁⟩ := fr₁
  rw [← hk] at hcp₁
  rw [← hk₁] at heq₁
  simp only [zero_add] at layS₁ hcp₁ heq₁
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ (proIns walkPieces Wl Wc W T s p 0 (ir₀ + cq + 1)) := ⟨_, rfl⟩
  rw [← hΓ₁] at layC₁ layS₁ hcp₁ heq₁
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 8 htbl hΓ pok₁
  have layC₁' : NodeLay walkPieces Wc T Γ₁ (fstIdx dp) := by rw [hfst₁]; exact Or.inl ⟨one_le_len_memberList_insert _ _, layC₁⟩
  have hDq₁ : DossF walkPieces Γ₁ 0 q (ir₀ + 1 + (1 + σ₁)) := by
    rw [hΓ₁]; have := dossF_transport' pnd₁ hDq; rwa [psh₁] at this
  -- child 1
  obtain ⟨cok₁, cnd₁, csh₁, cgoal₁⟩ := hch₁ Γ₁ hΓ₁f layC₁'
  obtain ⟨s₁, hs₁⟩ : ∃ x, x = shiftsV L₁ := ⟨_, rfl⟩
  obtain ⟨Γ₂, hΓ₂⟩ : ∃ Γ', Γ' = finalCtx Γ₁ L₁ := ⟨_, rfl⟩
  rw [← hΓ₂, ← hs₁, hfst₁, ← hk₁] at cgoal₁
  rw [← hs₁] at csh₁
  have hΓ₂f : IsFormulaSet LAct Γ₂ := by rw [hΓ₂]; exact finalCtx_isFormulaSet 9 htbl hΓ₁f cok₁
  have heq₁₂ : neg LAct (eqFactB (^&(σ₁ + s₁)) (^&(k₁ + 1 + s₁))) ∈ Γ₂ := by
    rw [hΓ₂, hs₁]
    have := tr_fact cnd₁ (isFormula_eqFactB (hf_ _) (hf_ _)) heq₁
    rwa [shiftIterV_eqFactB (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
  -- `postIns` 1
  have hsE₁ : k₁ + 1 + s₁ + 3 ≤ E := by
    refine le_trans ?_ hE'
    calc k₁ + 1 + s₁ + 3 ≤ D + 1 + B₁ + 3 := add_le_add (add_le_add (add_le_add (hk₁ ▸ hk₁D) (le_refl 1)) csh₁) (le_refl 3)
      _ ≤ 40 * D + B₁ + 40 := le_of_add_eq' (c := 39 * D + 36) (by ring)
  have hcE₁ : σ₁ + s₁ + 3 ≤ E := by
    refine le_trans ?_ hE'
    calc σ₁ + s₁ + 3 ≤ (6 * D + 1) + B₁ + 3 := add_le_add (add_le_add hσ₁D csh₁) (le_refl 3)
      _ ≤ 40 * D + B₁ + 40 := le_of_add_eq' (c := 34 * D + 36) (by ring)
  obtain ⟨qok₁, qnd₁, qsh₁, -, qder₁, qfst₁, qdlen₁, qle₁⟩ := postIns_ok htbl hP hWp hΓ₂f hsE₁ hcE₁ cgoal₁ heq₁₂
  obtain ⟨Γ₃, hΓ₃⟩ : ∃ Γ', Γ' = finalCtx Γ₂ (postIns W (k₁ + 1 + s₁) (σ₁ + s₁) (dlen TAct dp)) := ⟨_, rfl⟩
  rw [← hΓ₃] at qder₁ qfst₁ qdlen₁ qle₁
  have hΓ₃f : IsFormulaSet LAct Γ₃ := by rw [hΓ₃]; exact finalCtx_isFormulaSet 8 htbl hΓ₂f qok₁
  have hΓ₃e : Γ₃ = finalCtx Γ₁ (appendV L₁ (postIns W (k₁ + 1 + s₁) (σ₁ + s₁) (dlen TAct dp))) := by
    rw [finalCtx_appendV, ← hΓ₂, hΓ₃]
  have hndB : NoDrop' (appendV L₁ (postIns W (k₁ + 1 + s₁) (σ₁ + s₁) (dlen TAct dp))) := noDrop'_appendV cnd₁ qnd₁
  have hshB : shiftsV (appendV L₁ (postIns W (k₁ + 1 + s₁) (σ₁ + s₁) (dlen TAct dp))) = s₁ + 2 := by
    rw [shiftsV_appendV, qsh₁, hs₁]
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ, τ = 1 + σ₁ + s₁ + 2 := ⟨_, rfl⟩
  have layS₃ : Layout walkPieces Wc T Γ₃ s τ₁ := by
    rw [hΓ₃e, hτ₁]; have := layS₁.transport hndB; rwa [hshB, ← add_assoc] at this
  have hcp₃ : neg LAct (insFact (^&(σ₁ + s₁ + 2)) (^&(ir₀ + cq + 1 + τ₁)) (^&(τ₁ + (k + 1)))) ∈ Γ₃ := by
    rw [hΓ₃e]
    have := tr_fact hndB (isFormula_insFact (hf_ _) (hf_ _) (hf_ _)) hcp₁
    rw [hshB, shiftIterV_insFact (hf_ _) (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show σ₁ + (s₁ + 2) = σ₁ + s₁ + 2 by ring, show ir₀ + cq + 1 + 1 + σ₁ + (s₁ + 2) = ir₀ + cq + 1 + τ₁ by rw [hτ₁]; ring,
      show 1 + σ₁ + (k + 1) + (s₁ + 2) = τ₁ + (k + 1) by rw [hτ₁]; ring] at this
  have hDq₃ : DossF walkPieces Γ₃ 0 q (ir₀ + 1 + τ₁) := by
    rw [hΓ₃e]; have := dossF_transport' hndB hDq₁; rwa [hshB, show ir₀ + 1 + (1 + σ₁) + (s₁ + 2) = ir₀ + 1 + τ₁ by rw [hτ₁]; ring] at this
  have hτ₁D : τ₁ ≤ 6 * D + B₁ + 4 := by
    rw [hτ₁]
    calc 1 + σ₁ + s₁ + 2 ≤ 1 + (6 * D + 1) + B₁ + 2 := add_le_add (add_le_add (add_le_add (le_refl 1) hσ₁D) csh₁) (le_refl 2)
      _ = 6 * D + B₁ + 4 := by ring
  -- block 2: `proIns s q τ₁ (iq₀ + τ₁)`
  have hiE₂ : τ₁ + 14 * D + 5 ≤ E := by
    refine le_trans ?_ hE'
    calc τ₁ + 14 * D + 5 ≤ (6 * D + B₁ + 4) + 14 * D + 5 := add_le_add (add_le_add hτ₁D (le_refl _)) (le_refl 5)
      _ ≤ 40 * D + B₁ + 40 := le_of_add_eq' (c := 20 * D + 31) (by ring)
  have hipE₂ : ir₀ + 1 + τ₁ + 8 * D + 4 ≤ E := by
    refine le_trans ?_ hE'
    calc ir₀ + 1 + τ₁ + 8 * D + 4 ≤ (6 * D + 1) + 1 + (6 * D + B₁ + 4) + 8 * D + 4 :=
          add_le_add (add_le_add (add_le_add (add_le_add hir₀D (le_refl 1)) hτ₁D) (le_refl _)) (le_refl 4)
      _ ≤ 40 * D + B₁ + 40 := le_of_add_eq' (c := 20 * D + 30) (by ring)
  obtain ⟨pok₂, pnd₂, psh₂, layC₂, fr₂, heq₂⟩ :=
    proIns_ok htbl hP htblN hWl hWc hWp hs hq hk1 hc₂D hE13 hiE₂ hipE₂ hΓ₃f layS₃ hDq₃
  rw [← hσ₂] at psh₂ fr₂ heq₂
  obtain ⟨-, layS₄, -, hcq₄⟩ := fr₂
  rw [← hk] at hcq₄
  rw [← hk₂] at heq₂
  simp only [zero_add] at layS₄ hcq₄ heq₂
  obtain ⟨Γ₄, hΓ₄⟩ : ∃ Γ', Γ' = finalCtx Γ₃ (proIns walkPieces Wl Wc W T s q τ₁ (ir₀ + 1 + τ₁)) := ⟨_, rfl⟩
  rw [← hΓ₄] at layC₂ layS₄ hcq₄ heq₂
  have hΓ₄f : IsFormulaSet LAct Γ₄ := by rw [hΓ₄]; exact finalCtx_isFormulaSet 8 htbl hΓ₃f pok₂
  have layC₂' : NodeLay walkPieces Wc T Γ₄ (fstIdx dq) := by rw [hfst₂]; exact Or.inl ⟨one_le_len_memberList_insert _ _, layC₂⟩
  -- child 2
  obtain ⟨cok₂, cnd₂, csh₂, cgoal₂⟩ := hch₂ Γ₄ hΓ₄f layC₂'
  obtain ⟨s₂, hs₂⟩ : ∃ x, x = shiftsV L₂ := ⟨_, rfl⟩
  obtain ⟨Γ₅, hΓ₅⟩ : ∃ Γ', Γ' = finalCtx Γ₄ L₂ := ⟨_, rfl⟩
  rw [← hΓ₅, ← hs₂, hfst₂, ← hk₂] at cgoal₂
  rw [← hs₂] at csh₂
  have hΓ₅f : IsFormulaSet LAct Γ₅ := by rw [hΓ₅]; exact finalCtx_isFormulaSet 9 htbl hΓ₄f cok₂
  have heq₂₅ : neg LAct (eqFactB (^&(σ₂ + s₂)) (^&(k₂ + 1 + s₂))) ∈ Γ₅ := by
    rw [hΓ₅, hs₂]
    have := tr_fact cnd₂ (isFormula_eqFactB (hf_ _) (hf_ _)) heq₂
    rwa [shiftIterV_eqFactB (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
  -- `postIns` 2
  have hsE₂ : k₂ + 1 + s₂ + 3 ≤ E := by
    refine le_trans ?_ hE₂'
    calc k₂ + 1 + s₂ + 3 ≤ D + 1 + B₂ + 3 := add_le_add (add_le_add (add_le_add (hk₂ ▸ hk₂D) (le_refl 1)) csh₂) (le_refl 3)
      _ ≤ 40 * D + B₂ + 40 := le_of_add_eq' (c := 39 * D + 36) (by ring)
  have hcE₂ : σ₂ + s₂ + 3 ≤ E := by
    refine le_trans ?_ hE₂'
    calc σ₂ + s₂ + 3 ≤ (6 * D + 1) + B₂ + 3 := add_le_add (add_le_add hσ₂D csh₂) (le_refl 3)
      _ ≤ 40 * D + B₂ + 40 := le_of_add_eq' (c := 34 * D + 36) (by ring)
  obtain ⟨qok₂, qnd₂, qsh₂, -, qder₂, qfst₂, qdlen₂, qle₂⟩ := postIns_ok htbl hP hWp hΓ₅f hsE₂ hcE₂ cgoal₂ heq₂₅
  obtain ⟨Γ₆, hΓ₆⟩ : ∃ Γ', Γ' = finalCtx Γ₅ (postIns W (k₂ + 1 + s₂) (σ₂ + s₂) (dlen TAct dq)) := ⟨_, rfl⟩
  rw [← hΓ₆] at qder₂ qfst₂ qdlen₂ qle₂
  have hΓ₆f : IsFormulaSet LAct Γ₆ := by rw [hΓ₆]; exact finalCtx_isFormulaSet 8 htbl hΓ₅f qok₂
  -- the whole block 2 as one list `C = pro₂ ++ L₂ ++ post₂` (shifts `τ₂`), from Γ₃ to Γ₆
  obtain ⟨τ₂, hτ₂⟩ : ∃ τ, τ = 1 + σ₂ + s₂ + 2 := ⟨_, rfl⟩
  have hΓ₆e : Γ₆ = finalCtx Γ₃ (appendV (proIns walkPieces Wl Wc W T s q τ₁ (ir₀ + 1 + τ₁))
      (appendV L₂ (postIns W (k₂ + 1 + s₂) (σ₂ + s₂) (dlen TAct dq)))) := by
    rw [finalCtx_appendV, finalCtx_appendV, ← hΓ₄, ← hΓ₅, hΓ₆]
  have hndC : NoDrop' (appendV (proIns walkPieces Wl Wc W T s q τ₁ (ir₀ + 1 + τ₁))
      (appendV L₂ (postIns W (k₂ + 1 + s₂) (σ₂ + s₂) (dlen TAct dq)))) := noDrop'_appendV pnd₂ (noDrop'_appendV cnd₂ qnd₂)
  have hshC : shiftsV (appendV (proIns walkPieces Wl Wc W T s q τ₁ (ir₀ + 1 + τ₁))
      (appendV L₂ (postIns W (k₂ + 1 + s₂) (σ₂ + s₂) (dlen TAct dq)))) = τ₂ := by
    rw [shiftsV_appendV, shiftsV_appendV, psh₂, qsh₂, ← hs₂, hτ₂]; ring
  have hndBC : NoDrop' (appendV L₂ (postIns W (k₂ + 1 + s₂) (σ₂ + s₂) (dlen TAct dq))) := noDrop'_appendV cnd₂ qnd₂
  have hshBC : shiftsV (appendV L₂ (postIns W (k₂ + 1 + s₂) (σ₂ + s₂) (dlen TAct dq))) = s₂ + 2 := by
    rw [shiftsV_appendV, qsh₂, hs₂]
  have hΓ₆e' : Γ₆ = finalCtx Γ₄ (appendV L₂ (postIns W (k₂ + 1 + s₂) (σ₂ + s₂) (dlen TAct dq))) := by
    rw [finalCtx_appendV, ← hΓ₅, hΓ₆]
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = τ₁ + τ₂ := ⟨_, rfl⟩
  -- the facts at Γ₆
  have layS₆ : Layout walkPieces Wc T Γ₆ s τ := by
    rw [hΓ₆e', hτ, hτ₂]; have := layS₄.transport hndBC
    rwa [hshBC, show τ₁ + 1 + σ₂ + (s₂ + 2) = τ₁ + (1 + σ₂ + s₂ + 2) by ring] at this
  have hcp₆ : neg LAct (insFact (^&(σ₁ + s₁ + 2 + τ₂)) (^&(ir₀ + cq + 1 + τ)) (^&(τ + (k + 1)))) ∈ Γ₆ := by
    rw [hΓ₆e]
    have := tr_fact hndC (isFormula_insFact (hf_ _) (hf_ _) (hf_ _)) hcp₃
    rw [hshC, shiftIterV_insFact (hf_ _) (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show ir₀ + cq + 1 + τ₁ + τ₂ = ir₀ + cq + 1 + τ by rw [hτ]; ring, show τ₁ + (k + 1) + τ₂ = τ + (k + 1) by rw [hτ]; ring] at this
  have hcq₆ : neg LAct (insFact (^&(σ₂ + s₂ + 2)) (^&(ir₀ + 1 + τ)) (^&(τ + (k + 1)))) ∈ Γ₆ := by
    rw [hΓ₆e']
    have := tr_fact hndBC (isFormula_insFact (hf_ _) (hf_ _) (hf_ _)) hcq₄
    rw [hshBC, shiftIterV_insFact (hf_ _) (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show σ₂ + (s₂ + 2) = σ₂ + s₂ + 2 by ring, show ir₀ + 1 + τ₁ + 1 + σ₂ + (s₂ + 2) = ir₀ + 1 + τ by rw [hτ, hτ₂]; ring,
      show τ₁ + 1 + σ₂ + (k + 1) + (s₂ + 2) = τ + (k + 1) by rw [hτ, hτ₂]; ring] at this
  have qder₁₆ : neg LAct (derFact (^&(1 + τ₂) : V)) ∈ Γ₆ := by
    rw [hΓ₆e]; have := tr_fact hndC (isFormula_derFact (hf_ _)) qder₁
    rwa [hshC, shiftIterV_derFact (hf_ _), termShiftIterV_fvar] at this
  have qfst₁₆ : neg LAct (fstIdxFact (^&(σ₁ + s₁ + 2 + τ₂)) (^&(1 + τ₂))) ∈ Γ₆ := by
    rw [hΓ₆e]; have := tr_fact hndC (isFormula_fstIdxFact (hf_ _) (hf_ _)) qfst₁
    rwa [hshC, shiftIterV_fstIdxFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
  have qdlen₁₆ : neg LAct (dlenFact (^&(1 + τ₂) : V) (^&(0 + τ₂))) ∈ Γ₆ := by
    rw [hΓ₆e]; have := tr_fact hndC (isFormula_dlenFact (hf_ _) (hf_ _)) qdlen₁
    rwa [hshC, shiftIterV_dlenFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
  have qle₁₆ : neg LAct (leFact (^&(0 + τ₂)) (bnum (dlen TAct dp))) ∈ Γ₆ := by
    rw [hΓ₆e]; have := tr_fact hndC (isFormula_leFact (hf_ _) (isSemiterm_bnum_LAct 0 _)) qle₁
    rwa [hshC, shiftIterV_leFact (hf_ _) (isSemiterm_bnum_LAct 0 _), termShiftIterV_fvar, termShiftIterV_bnum'] at this
  have hand₆ : neg LAct (andFact (^&(ir₀ + τ)) (^&(ir₀ + cq + 1 + τ)) (^&(ir₀ + 1 + τ))) ∈ Γ₆ := by
    have h1 := tr_fact pnd₁ (isFormula_andFact (hf_ _) (hf_ _) (hf_ _)) hand
    rw [psh₁, shiftIterV_andFact (hf_ _) (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar, ← hΓ₁] at h1
    have h2 := tr_fact hndB (isFormula_andFact (hf_ _) (hf_ _) (hf_ _)) h1
    rw [hshB, shiftIterV_andFact (hf_ _) (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar, ← hΓ₃e] at h2
    rw [hΓ₆e]
    have := tr_fact hndC (isFormula_andFact (hf_ _) (hf_ _) (hf_ _)) h2
    rw [hshC, shiftIterV_andFact (hf_ _) (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show ir₀ + (1 + σ₁) + (s₁ + 2) + τ₂ = ir₀ + τ by rw [hτ, hτ₁]; ring,
      show ir₀ + cq + 1 + (1 + σ₁) + (s₁ + 2) + τ₂ = ir₀ + cq + 1 + τ by rw [hτ, hτ₁]; ring,
      show ir₀ + 1 + (1 + σ₁) + (s₁ + 2) + τ₂ = ir₀ + 1 + τ by rw [hτ, hτ₁]; ring] at this
  have hmr₆ : neg LAct (memFact (^&(ir₀ + τ)) (^&(τ + (k + 1)))) ∈ Γ₆ := by
    have h1 := tr_fact pnd₁ (isFormula_memFact (hf_ _) (hf_ _)) hmr
    rw [psh₁, shiftIterV_memFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, ← hΓ₁] at h1
    have h2 := tr_fact hndB (isFormula_memFact (hf_ _) (hf_ _)) h1
    rw [hshB, shiftIterV_memFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, ← hΓ₃e] at h2
    rw [hΓ₆e]
    have := tr_fact hndC (isFormula_memFact (hf_ _) (hf_ _)) h2
    rw [hshC, shiftIterV_memFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show ir₀ + (1 + σ₁) + (s₁ + 2) + τ₂ = ir₀ + τ by rw [hτ, hτ₁]; ring,
      show len (memberList s) + 1 + (1 + σ₁) + (s₁ + 2) + τ₂ = τ + (k + 1) by rw [hτ, hτ₁, hk]; ring] at this
  -- the node's caps
  have hτ₂D : τ₂ ≤ 6 * D + B₂ + 4 := by
    rw [hτ₂]
    calc 1 + σ₂ + s₂ + 2 ≤ 1 + (6 * D + 1) + B₂ + 2 := add_le_add (add_le_add (add_le_add (le_refl 1) hσ₂D) csh₂) (le_refl 2)
      _ = 6 * D + B₂ + 4 := by ring
  have hτD : τ ≤ 12 * D + B₁ + B₂ + 8 := by
    rw [hτ]; exact le_trans (add_le_add hτ₁D hτ₂D) (le_of_add_eq' (c := 0) (by ring))
  have his : τ + (k + 1) + 2 ≤ E := by
    refine le_trans ?_ hE''
    calc τ + (k + 1) + 2 ≤ (12 * D + B₁ + B₂ + 8) + (D + 1) + 2 := add_le_add (add_le_add hτD (add_le_add (hk ▸ hkD) (le_refl 1))) (le_refl 2)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 47 * D + B₂ + 49) (by ring)
  have hir : ir₀ + τ + 2 ≤ E := by
    refine le_trans ?_ hE''
    calc ir₀ + τ + 2 ≤ (6 * D + 1) + (12 * D + B₁ + B₂ + 8) + 2 := add_le_add (add_le_add hir₀D hτD) (le_refl 2)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 42 * D + B₂ + 49) (by ring)
  have hip : ir₀ + cq + 1 + τ + 2 ≤ E := by
    refine le_trans ?_ hE''
    calc ir₀ + cq + 1 + τ + 2 ≤ (6 * D + 1) + 2 * D + 1 + (12 * D + B₁ + B₂ + 8) + 2 :=
          add_le_add (add_le_add (add_le_add (add_le_add hir₀D hcq) (le_refl 1)) hτD) (le_refl 2)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 40 * D + B₂ + 48) (by ring)
  have hiq : ir₀ + 1 + τ + 2 ≤ E := by
    refine le_trans ?_ hE''
    calc ir₀ + 1 + τ + 2 ≤ (6 * D + 1) + 1 + (12 * D + B₁ + B₂ + 8) + 2 := add_le_add (add_le_add (add_le_add hir₀D (le_refl 1)) hτD) (le_refl 2)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 42 * D + B₂ + 48) (by ring)
  have hid₁ : 1 + τ₂ + 2 ≤ E := by
    refine le_trans ?_ hE''
    calc 1 + τ₂ + 2 ≤ 1 + (6 * D + B₂ + 4) + 2 := add_le_add (add_le_add (le_refl 1) hτ₂D) (le_refl 2)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 54 * D + B₁ + B₂ + 53) (by ring)
  have hid₂ : (1 : V) + 2 ≤ E := le_trans (le_of_add_eq' (c := 60 * D + B₁ + 2 * B₂ + 57) (by ring)) hE''
  have hicp : σ₁ + s₁ + 2 + τ₂ + 2 ≤ E := by
    refine le_trans ?_ hE''
    calc σ₁ + s₁ + 2 + τ₂ + 2 ≤ (6 * D + 1) + B₁ + 2 + (6 * D + B₂ + 4) + 2 :=
          add_le_add (add_le_add (add_le_add (add_le_add hσ₁D csh₁) (le_refl 2)) hτ₂D) (le_refl 2)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 48 * D + B₂ + 51) (by ring)
  have hicq : σ₂ + s₂ + 2 + 2 ≤ E := by
    refine le_trans ?_ hE''
    calc σ₂ + s₂ + 2 + 2 ≤ (6 * D + 1) + B₂ + 2 + 2 := add_le_add (add_le_add (add_le_add hσ₂D csh₂) (le_refl 2)) (le_refl 2)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 54 * D + B₁ + B₂ + 55) (by ring)
  have hT : τ + τ₂ + 0 + 10 ≤ E := by
    refine le_trans ?_ hE''
    calc τ + τ₂ + 0 + 10 ≤ (12 * D + B₁ + B₂ + 8) + (6 * D + B₂ + 4) + 0 + 10 :=
          add_le_add (add_le_add (add_le_add hτD hτ₂D) (le_refl 0)) (le_refl 10)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 42 * D + 38) (by ring)
  have hn : 18 * ‖dlen TAct (andIntro s p q dp dq)‖ + 7 ≤ E := by
    have hn1 : ‖dlen TAct (andIntro s p q dp dq)‖ ≤ 3 * D + 1 := by
      refine le_trans (length_le _) ?_
      rw [hdl]
      exact le_trans (add_le_add (add_le_add (add_le_add hsD hm₁D) hm₂D) (le_refl 1)) (le_of_add_eq' (c := 0) (by ring))
    refine le_trans ?_ hE''
    calc 18 * ‖dlen TAct (andIntro s p q dp dq)‖ + 7 ≤ 18 * (3 * D + 1) + 7 :=
          add_le_add (mul_le_mul_of_nonneg_left hn1 zero_le) (le_refl 7)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 6 * D + B₁ + 2 * B₂ + 35) (by ring)
  have hLn : setLen LAct s + dlen TAct dp + dlen TAct dq + 1 ≤ dlen TAct (andIntro s p q dp dq) := by rw [hdl]
  -- the node
  obtain ⟨nok, nnd, nsh, -, ngoal⟩ := nodeAnd_ok (E := E) (is := τ + (k + 1)) (il := τ) (ir := ir₀ + τ)
    (ip := ir₀ + cq + 1 + τ) (iq := ir₀ + 1 + τ) (id₁ := 1 + τ₂) (id₂ := 1) (icp := σ₁ + s₁ + 2 + τ₂) (icq := σ₂ + s₂ + 2)
    (in₁ := τ₂) (in₂ := 0) (L := setLen LAct s) (m₁ := dlen TAct dp) (m₂ := dlen TAct dq) (n := dlen TAct (andIntro s p q dp dq))
    htbl hP.frag1Table hW₁ htblN hΓ₆f his hir hip hiq hid₁ hid₂ hicp hicq hT hn hLn hand₆ hmr₆ qfst₁₆ hcp₆ qder₁₆
    (by rwa [zero_add] at qdlen₁₆) (by rwa [zero_add] at qle₁₆) qfst₂ hcq₆ qder₂ qdlen₂ qle₂
    (by have := layS₆.2.1; rwa [← hk] at this) layS₆.2.2
  -- assembly
  unfold vAnd
  rw [← hir₀, ← hcqd, ← hσ₁, ← hσ₂, ← hs₁, ← hs₂, ← hk, ← hk₁, ← hk₂]
  rw [show 1 + σ₁ + s₁ + 2 = τ₁ by rw [hτ₁], show 1 + σ₂ + s₂ + 2 = τ₂ by rw [hτ₂], show τ₁ + τ₂ = τ by rw [hτ]]
  have ok₆ : ListOK tbl E ((9 : ℕ) : V) Γ₅ (appendV (postIns W (k₂ + 1 + s₂) (σ₂ + s₂) (dlen TAct dq))
      (nodeAnd W₁ T (τ + (k + 1)) τ (ir₀ + τ) (ir₀ + cq + 1 + τ) (ir₀ + 1 + τ) (1 + τ₂) 1 (σ₁ + s₁ + 2 + τ₂) (σ₂ + s₂ + 2) τ₂ 0
        (setLen LAct s) (dlen TAct dp) (dlen TAct dq) (dlen TAct (andIntro s p q dp dq)))) :=
    listOK_appendV (qok₂.mono h89) (by rw [← hΓ₆]; exact nok)
  have ok₅ := listOK_appendV cok₂ (by rw [← hΓ₅]; exact ok₆)
  have ok₄ := listOK_appendV (pok₂.mono h89) (by rw [← hΓ₄]; exact ok₅)
  have ok₃ := listOK_appendV (qok₁.mono h89) (by rw [← hΓ₃]; exact ok₄)
  have ok₂ := listOK_appendV cok₁ (by rw [← hΓ₂]; exact ok₃)
  have ok₁ := listOK_appendV (pok₁.mono h89) (by rw [← hΓ₁]; exact ok₂)
  refine ⟨ok₁, noDrop'_appendV pnd₁ (noDrop'_appendV cnd₁ (noDrop'_appendV qnd₁ (noDrop'_appendV pnd₂
    (noDrop'_appendV cnd₂ (noDrop'_appendV qnd₂ nnd))))), ?_, ?_⟩
  · rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV,
      psh₁, ← hs₁, qsh₁, psh₂, ← hs₂, qsh₂, nsh]
    calc 1 + σ₁ + (s₁ + (2 + (1 + σ₂ + (s₂ + (2 + 1))))) ≤ 1 + (6 * D + 1) + (B₁ + (2 + (1 + (6 * D + 1) + (B₂ + (2 + 1))))) :=
          add_le_add (add_le_add (le_refl 1) hσ₁D) (add_le_add csh₁ (add_le_add (le_refl 2)
            (add_le_add (add_le_add (le_refl 1) hσ₂D) (add_le_add csh₂ (le_refl _)))))
      _ = 12 * D + B₁ + B₂ + 9 := by ring
  · rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV,
      psh₁, ← hs₁, qsh₁, psh₂, ← hs₂, qsh₂, nsh,
      finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, finalCtx_appendV,
      ← hΓ₁, ← hΓ₂, ← hΓ₃, ← hΓ₄, ← hΓ₅, ← hΓ₆,
      show k + 1 + (1 + σ₁ + (s₁ + (2 + (1 + σ₂ + (s₂ + (2 + 1)))))) = τ + (k + 1) + 1 by rw [hτ, hτ₁, hτ₂]; ring]
    exact ngoal

end andOk

/-! ### 8.7 `cut`: the cut prefix, two `cutPro`/child/`postIns` blocks (the parent possibly EMPTY), `nodeCut` -/

section cutOk

/-- The parent's layout at an offset `i`, in either form (the empty sequent as `Layout0`). -/
def PLay (Wc T Γ s i : V) : Prop :=
  (1 ≤ len (memberList s) ∧ Layout walkPieces Wc T Γ s i) ∨ (s = 0 ∧ Layout0 walkPieces Wc T Γ i)

lemma PLay.layout {Wc T Γ s i : V} (h : PLay Wc T Γ s i) : Layout walkPieces Wc T Γ s i := by
  rcases h with ⟨-, h⟩ | ⟨rfl, h⟩
  · exact h
  · exact h.1

lemma PLay.transport {Wc T Γ s i S : V} (hS : NoDrop' S) (h : PLay Wc T Γ s i) : PLay Wc T (finalCtx Γ S) s (i + shiftsV S) := by
  rcases h with ⟨hk, h⟩ | ⟨rfl, h⟩
  · exact Or.inl ⟨hk, h.transport hS⟩
  · exact Or.inr ⟨rfl, h.transport hS⟩

lemma NodeLay.play {Wc T Γ s : V} (h : NodeLay walkPieces Wc T Γ s) : PLay Wc T Γ s 0 := by
  rcases h with ⟨hk, h⟩ | ⟨rfl, h, -⟩
  · exact Or.inl ⟨hk, h⟩
  · exact Or.inr ⟨rfl, h⟩

set_option maxHeartbeats 4000000 in
/-- **One `cut` block**: `cutPro s r i ip` (`proIns` or `proIns0` by the parent's emptiness), the child's list, `postIns`.
Afterwards (shifts `τ = 1 + σ + s' + 2`, `σ = proSig (insert r s)`): the parent at `i + τ`, the insert object
`insFact &(σ + s' + 2) &(ip + τ) &(i + τ + (k + 1))`, and the child's four row facts. -/
theorem cutBlock_ok {tbl N N' B' Wl Wc W T s r d L i ip D B Bi E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hs : IsFormulaSet LAct s) (hr : IsSemiformula LAct 0 r) (hd : DerivationOf TAct d (insert r s))
    (hcD : setLen LAct (insert r s) ≤ D) (hmD : dlen TAct d ≤ D) (hiB : i ≤ Bi) (hipB : ip ≤ Bi)
    (hE : 40 * D + 18 * ‖D‖ + B + Bi + 40 ≤ E) (hΓ : IsFormulaSet LAct Γ) (hLay : PLay Wc T Γ s i)
    (hDr : DossF walkPieces Γ 0 r ip) (hch : ChildOK tbl Wc T E L d B) :
    ∃ σ : V, σ = proSig walkPieces Wl Wc W T (insert r s) ∧ σ ≤ 6 * D + 1 ∧
      ListOK tbl E ((9 : ℕ) : V) Γ (appendV (cutPro walkPieces Wl Wc W T s r i ip)
        (appendV L (postIns W (len (memberList (insert r s)) + 1 + shiftsV L) (σ + shiftsV L) (dlen TAct d)))) ∧
      NoDrop' (appendV (cutPro walkPieces Wl Wc W T s r i ip)
        (appendV L (postIns W (len (memberList (insert r s)) + 1 + shiftsV L) (σ + shiftsV L) (dlen TAct d)))) ∧
      shiftsV (appendV (cutPro walkPieces Wl Wc W T s r i ip)
        (appendV L (postIns W (len (memberList (insert r s)) + 1 + shiftsV L) (σ + shiftsV L) (dlen TAct d)))) =
        1 + σ + shiftsV L + 2 ∧
      shiftsV L ≤ B ∧
      PLay Wc T (finalCtx Γ (appendV (cutPro walkPieces Wl Wc W T s r i ip)
        (appendV L (postIns W (len (memberList (insert r s)) + 1 + shiftsV L) (σ + shiftsV L) (dlen TAct d))))) s
        (i + (1 + σ + shiftsV L + 2)) ∧
      neg LAct (insFact (^&(σ + shiftsV L + 2)) (^&(ip + (1 + σ + shiftsV L + 2))) (^&(i + (1 + σ + shiftsV L + 2) + (len (memberList s) + 1)))) ∈
        finalCtx Γ (appendV (cutPro walkPieces Wl Wc W T s r i ip)
          (appendV L (postIns W (len (memberList (insert r s)) + 1 + shiftsV L) (σ + shiftsV L) (dlen TAct d)))) ∧
      neg LAct (derFact (^&1 : V)) ∈ finalCtx Γ (appendV (cutPro walkPieces Wl Wc W T s r i ip)
          (appendV L (postIns W (len (memberList (insert r s)) + 1 + shiftsV L) (σ + shiftsV L) (dlen TAct d)))) ∧
      neg LAct (fstIdxFact (^&(σ + shiftsV L + 2)) (^&1)) ∈ finalCtx Γ (appendV (cutPro walkPieces Wl Wc W T s r i ip)
          (appendV L (postIns W (len (memberList (insert r s)) + 1 + shiftsV L) (σ + shiftsV L) (dlen TAct d)))) ∧
      neg LAct (dlenFact (^&1 : V) (^&0)) ∈ finalCtx Γ (appendV (cutPro walkPieces Wl Wc W T s r i ip)
          (appendV L (postIns W (len (memberList (insert r s)) + 1 + shiftsV L) (σ + shiftsV L) (dlen TAct d)))) ∧
      neg LAct (leFact (^&0) (bnum (dlen TAct d))) ∈ finalCtx Γ (appendV (cutPro walkPieces Wl Wc W T s r i ip)
          (appendV L (postIns W (len (memberList (insert r s)) + 1 + shiftsV L) (σ + shiftsV L) (dlen TAct d)))) := by
  have hfst : fstIdx d = insert r s := hd.1
  have hc : IsFormulaSet LAct (insert r s) := DerivationOf.isFormulaSet hd
  have hkcD : len (memberList (insert r s)) ≤ D := len_memberList_le_of_setLen hc hcD
  have hE' : 40 * D + B + Bi + 40 ≤ E := le_trans (le_of_add_eq' (c := 18 * ‖D‖) (by ring)) hE
  have hE13 : 13 * D + 18 * ‖D‖ + 12 ≤ E := le_trans (le_of_add_eq' (c := 27 * D + B + Bi + 28) (by ring)) hE
  have hE8 : 13 * D + 18 * ‖D‖ + 8 ≤ E := le_trans (le_of_add_eq' (c := 27 * D + B + Bi + 32) (by ring)) hE
  have hiE : i + 14 * D + 5 ≤ E := by
    refine le_trans ?_ hE'
    calc i + 14 * D + 5 ≤ Bi + 14 * D + 5 := add_le_add (add_le_add hiB (le_refl _)) (le_refl 5)
      _ ≤ 40 * D + B + Bi + 40 := le_of_add_eq' (c := 26 * D + B + 35) (by ring)
  have hipE : ip + 8 * D + 4 ≤ E := by
    refine le_trans ?_ hE'
    calc ip + 8 * D + 4 ≤ Bi + 8 * D + 4 := add_le_add (add_le_add hipB (le_refl _)) (le_refl 4)
      _ ≤ 40 * D + B + Bi + 40 := le_of_add_eq' (c := 32 * D + B + 36) (by ring)
  obtain ⟨σ, hσ⟩ : ∃ x, x = proSig walkPieces Wl Wc W T (insert r s) := ⟨_, rfl⟩
  have hσD : σ ≤ 6 * D + 1 := by
    rw [hσ]; exact proSig_le htbl hP hWc htblN hWl hWp hc (one_le_len_memberList_insert _ _) hcD hE8 hΓ
  obtain ⟨k, hk⟩ : ∃ k, k = len (memberList s) := ⟨_, rfl⟩
  obtain ⟨kc, hkc⟩ : ∃ x, x = len (memberList (insert r s)) := ⟨_, rfl⟩
  -- the prologue: the selector's two cases give the same interface
  have key : ListOK tbl E ((8 : ℕ) : V) Γ (cutPro walkPieces Wl Wc W T s r i ip) ∧ NoDrop' (cutPro walkPieces Wl Wc W T s r i ip) ∧
      shiftsV (cutPro walkPieces Wl Wc W T s r i ip) = 1 + σ ∧
      Layout walkPieces Wc T (finalCtx Γ (cutPro walkPieces Wl Wc W T s r i ip)) (insert r s) 0 ∧
      PLay Wc T (finalCtx Γ (cutPro walkPieces Wl Wc W T s r i ip)) s (i + (1 + σ)) ∧
      neg LAct (insFact (^&σ) (^&(ip + (1 + σ))) (^&(i + (1 + σ) + (k + 1)))) ∈ finalCtx Γ (cutPro walkPieces Wl Wc W T s r i ip) ∧
      neg LAct (eqFactB (^&σ) (^&(kc + 1))) ∈ finalCtx Γ (cutPro walkPieces Wl Wc W T s r i ip) := by
    by_cases hs0 : memberList s = 0
    · have hs0' : s = 0 := eq_zero_of_memberList_eq_zero hs0
      have hLay0 : Layout0 walkPieces Wc T Γ i := by
        rcases hLay with ⟨hk1, -⟩ | ⟨-, h⟩
        · exfalso; rw [hs0', len_memberList_zero] at hk1; exact absurd hk1 (by simp)
        · exact h
      rw [cutPro, if_pos hs0]
      subst hs0'
      obtain ⟨pok, pnd, psh, layC, layP, hins, heq⟩ := proIns0_ok htbl hP htblN hWl hWc hWp hr hcD hE13 hiE hipE hΓ hLay0 hDr
      rw [← hσ] at psh layP hins heq
      rw [← hkc] at heq
      rw [len_memberList_zero] at hins hk
      subst hk
      refine ⟨pok, pnd, psh, layC, Or.inr ⟨rfl, by rwa [add_assoc] at layP⟩, ?_, by rwa [zero_add] at heq⟩
      rwa [add_assoc i 1 σ, add_assoc ip 1 σ] at hins
    · have hk1 : 1 ≤ len (memberList s) := one_le_len_memberList_of_ne hs0
      rw [cutPro, if_neg hs0]
      obtain ⟨pok, pnd, psh, layC, fr, heq⟩ := proIns_ok htbl hP htblN hWl hWc hWp hs hr hk1 hcD hE13 hiE hipE hΓ hLay.layout hDr
      rw [← hσ] at psh fr heq
      rw [← hkc] at heq
      obtain ⟨-, layP, -, hins⟩ := fr
      rw [← hk] at hins
      refine ⟨pok, pnd, psh, layC, Or.inl ⟨hk1, by rwa [add_assoc] at layP⟩, ?_, by rwa [zero_add] at heq⟩
      rwa [add_assoc i 1 σ, add_assoc ip 1 σ] at hins
  obtain ⟨pok, pnd, psh, layC, layP, hins, heq⟩ := key
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ (cutPro walkPieces Wl Wc W T s r i ip) := ⟨_, rfl⟩
  rw [← hΓ₁] at layC layP hins heq
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 8 htbl hΓ pok
  have layC' : NodeLay walkPieces Wc T Γ₁ (fstIdx d) := by rw [hfst]; exact Or.inl ⟨one_le_len_memberList_insert _ _, layC⟩
  -- the child
  obtain ⟨cok, cnd, csh, cgoal⟩ := hch Γ₁ hΓ₁f layC'
  obtain ⟨s', hs'⟩ : ∃ x, x = shiftsV L := ⟨_, rfl⟩
  obtain ⟨Γ₂, hΓ₂⟩ : ∃ Γ', Γ' = finalCtx Γ₁ L := ⟨_, rfl⟩
  rw [← hΓ₂, ← hs', hfst, ← hkc] at cgoal
  rw [← hs'] at csh
  have hΓ₂f : IsFormulaSet LAct Γ₂ := by rw [hΓ₂]; exact finalCtx_isFormulaSet 9 htbl hΓ₁f cok
  have heq₂ : neg LAct (eqFactB (^&(σ + s')) (^&(kc + 1 + s'))) ∈ Γ₂ := by
    rw [hΓ₂, hs']
    have := tr_fact cnd (isFormula_eqFactB (hf_ _) (hf_ _)) heq
    rwa [shiftIterV_eqFactB (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
  -- `postIns`
  have hsE : kc + 1 + s' + 3 ≤ E := by
    refine le_trans ?_ hE'
    calc kc + 1 + s' + 3 ≤ D + 1 + B + 3 := add_le_add (add_le_add (add_le_add (hkc ▸ hkcD) (le_refl 1)) csh) (le_refl 3)
      _ ≤ 40 * D + B + Bi + 40 := le_of_add_eq' (c := 39 * D + Bi + 36) (by ring)
  have hcE : σ + s' + 3 ≤ E := by
    refine le_trans ?_ hE'
    calc σ + s' + 3 ≤ (6 * D + 1) + B + 3 := add_le_add (add_le_add hσD csh) (le_refl 3)
      _ ≤ 40 * D + B + Bi + 40 := le_of_add_eq' (c := 34 * D + Bi + 36) (by ring)
  obtain ⟨qok, qnd, qsh, -, qder, qfst, qdlen, qle⟩ := postIns_ok htbl hP hWp hΓ₂f hsE hcE cgoal heq₂
  obtain ⟨Γ₃, hΓ₃⟩ : ∃ Γ', Γ' = finalCtx Γ₂ (postIns W (kc + 1 + s') (σ + s') (dlen TAct d)) := ⟨_, rfl⟩
  rw [← hΓ₃] at qder qfst qdlen qle
  have hΓ₃e : Γ₃ = finalCtx Γ₁ (appendV L (postIns W (kc + 1 + s') (σ + s') (dlen TAct d))) := by
    rw [finalCtx_appendV, ← hΓ₂, hΓ₃]
  have hndB : NoDrop' (appendV L (postIns W (kc + 1 + s') (σ + s') (dlen TAct d))) := noDrop'_appendV cnd qnd
  have hshB : shiftsV (appendV L (postIns W (kc + 1 + s') (σ + s') (dlen TAct d))) = s' + 2 := by
    rw [shiftsV_appendV, qsh, hs']
  have layP₃ : PLay Wc T Γ₃ s (i + (1 + σ + s' + 2)) := by
    rw [hΓ₃e]; have := layP.transport hndB
    rwa [hshB, show i + (1 + σ) + (s' + 2) = i + (1 + σ + s' + 2) by ring] at this
  have hins₃ : neg LAct (insFact (^&(σ + s' + 2)) (^&(ip + (1 + σ + s' + 2))) (^&(i + (1 + σ + s' + 2) + (k + 1)))) ∈ Γ₃ := by
    rw [hΓ₃e]
    have := tr_fact hndB (isFormula_insFact (hf_ _) (hf_ _) (hf_ _)) hins
    rw [hshB, shiftIterV_insFact (hf_ _) (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show σ + (s' + 2) = σ + s' + 2 by ring, show ip + (1 + σ) + (s' + 2) = ip + (1 + σ + s' + 2) by ring,
      show i + (1 + σ) + (k + 1) + (s' + 2) = i + (1 + σ + s' + 2) + (k + 1) by ring] at this
  -- assembly
  refine ⟨σ, hσ, hσD, ?_, ?_, ?_, (by rw [← hs']; exact csh), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← hs', ← hkc]
  · exact listOK_appendV (pok.mono h89) (by rw [← hΓ₁]; exact listOK_appendV cok (by rw [← hΓ₂]; exact qok.mono h89))
  · exact noDrop'_appendV pnd hndB
  · rw [shiftsV_appendV, psh, hshB]; ring
  · rw [finalCtx_appendV, ← hΓ₁, ← hΓ₃e]; exact layP₃
  · rw [finalCtx_appendV, ← hΓ₁, ← hΓ₃e, ← hk]; exact hins₃
  · rw [finalCtx_appendV, ← hΓ₁, ← hΓ₃e]; exact qder
  · rw [finalCtx_appendV, ← hΓ₁, ← hΓ₃e]; exact qfst
  · rw [finalCtx_appendV, ← hΓ₁, ← hΓ₃e]; exact qdlen
  · rw [finalCtx_appendV, ← hΓ₁, ← hΓ₃e]; exact qle

end cutOk

section cutOk2

lemma appendV_regroup8 (a b c d e f g h : V) :
    appendV a (appendV b (appendV c (appendV d (appendV e (appendV f (appendV g h)))))) =
    appendV a (appendV (appendV b (appendV c d)) (appendV (appendV e (appendV f g)) h)) := by
  simp only [appendV_assoc]

set_option maxHeartbeats 6000000 in
/-- **The `cut` list is applicable** at the node's layout (the parent possibly empty): `proCutPre`, the two blocks, `nodeCut`. -/
theorem vCut_ok {tbl N N' B' Wl Wc W₁ W T s p d₁ d₂ L₁ L₂ D B₁ B₂ E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces) (hW₁ : W₁ = frag1Pieces)
    (hs : IsFormulaSet LAct s) (hd₁ : DerivationOf TAct d₁ (insert p s)) (hd₂ : DerivationOf TAct d₂ (insert (neg LAct p) s))
    (hsD : setLen LAct s ≤ D) (hc₁D : setLen LAct (insert p s) ≤ D) (hc₂D : setLen LAct (insert (neg LAct p) s) ≤ D)
    (hm₁D : dlen TAct d₁ ≤ D) (hm₂D : dlen TAct d₂ ≤ D)
    (hE : 60 * D + 18 * ‖D‖ + B₁ + 2 * B₂ + 60 ≤ E) (hΓ : IsFormulaSet LAct Γ) (hLay : NodeLay walkPieces Wc T Γ s)
    (hch₁ : ChildOK tbl Wc T E L₁ d₁ B₁) (hch₂ : ChildOK tbl Wc T E L₂ d₂ B₂) :
    ListOK tbl E ((9 : ℕ) : V) Γ (vCut walkPieces Wl Wc W₁ W T s p d₁ d₂ L₁ L₂) ∧
    NoDrop' (vCut walkPieces Wl Wc W₁ W T s p d₁ d₂ L₁ L₂) ∧
    shiftsV (vCut walkPieces Wl Wc W₁ W T s p d₁ d₂ L₁ L₂) ≤ 20 * D + B₁ + B₂ + 9 ∧
    neg LAct (goalFact (^&(len (memberList s) + 1 + shiftsV (vCut walkPieces Wl Wc W₁ W T s p d₁ d₂ L₁ L₂)))
      (bnum (dlen TAct (cutRule s p d₁ d₂)))) ∈ finalCtx Γ (vCut walkPieces Wl Wc W₁ W T s p d₁ d₂ L₁ L₂) := by
  have hW : WalkTable tbl := hP.walkTable
  have hc₁ : IsFormulaSet LAct (insert p s) := DerivationOf.isFormulaSet hd₁
  have hp : IsSemiformula LAct 0 p := hc₁ p (by simp)
  have hnp : IsSemiformula LAct 0 (neg LAct p) := hp.neg
  have hD : Derivation TAct (cutRule s p d₁ d₂) := Derivation.cutRule hd₁ hd₂
  have hdl : dlen TAct (cutRule s p d₁ d₂) = setLen LAct s + dlen TAct d₁ + dlen TAct d₂ + 1 := dlen_cutRule hD
  have hkD : len (memberList s) ≤ D := len_memberList_le_of_setLen hs hsD
  have hpD : formulaLen LAct p ≤ D := le_trans (formulaLen_le_setLen_of_mem (by simp)) hc₁D
  have hnpD : formulaLen LAct (neg LAct p) ≤ D := le_trans (formulaLen_le_setLen_of_mem (by simp)) hc₂D
  -- the caps
  have hE' : 60 * D + B₁ + 2 * B₂ + 60 ≤ E := le_trans (le_of_add_eq' (c := 18 * ‖D‖) (by ring)) hE
  have hEc : 13 * D + 8 ≤ E := le_trans (le_of_add_eq' (c := 47 * D + B₁ + 2 * B₂ + 52) (by ring)) hE'
  -- the cut prefix
  obtain ⟨c0ok, c0nd, c0sh, hDp, -, hDnp, -, hneg⟩ := proCutPre_ok htbl hP htblN hWc hp hpD hnpD hEc hΓ
  obtain ⟨σc, hσc⟩ : ∃ x, x = mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) := ⟨_, rfl⟩
  obtain ⟨ip₀, hip₀⟩ : ∃ x, x = mLen Wc T p + mShift walkPieces Wc T (neg LAct p) := ⟨_, rfl⟩
  obtain ⟨inp₀, hinp₀⟩ : ∃ x, x = mLen Wc T (neg LAct p) := ⟨_, rfl⟩
  have hml : mLen Wc T p ≤ 2 * D := le_trans le_self_add (le_trans (mLen_succ_le hWc T hp) (mul_le_mul_of_nonneg_left hpD zero_le))
  have hmn : mLen Wc T (neg LAct p) ≤ 2 * D :=
    le_trans le_self_add (le_trans (mLen_succ_le hWc T hnp) (mul_le_mul_of_nonneg_left hnpD zero_le))
  have hmsp : mShift walkPieces Wc T p ≤ 4 * D := le_trans (mShift_le htbl hW hWc T hp) (mul_le_mul_of_nonneg_left hpD zero_le)
  have hmsn : mShift walkPieces Wc T (neg LAct p) ≤ 4 * D := le_trans (mShift_le htbl hW hWc T hnp) (mul_le_mul_of_nonneg_left hnpD zero_le)
  have hσcD : σc ≤ 8 * D := by rw [hσc]; exact le_trans (add_le_add hmsp hmsn) (le_of_add_eq' (c := 0) (by ring))
  have hip₀D : ip₀ ≤ 6 * D := by rw [hip₀]; exact le_trans (add_le_add hml hmsn) (le_of_add_eq' (c := 0) (by ring))
  have hinp₀D : inp₀ ≤ 2 * D := by rw [hinp₀]; exact hmn
  rw [← hσc] at c0sh
  rw [← hip₀] at hDp hneg
  rw [← hinp₀] at hDnp hneg
  obtain ⟨Γ₀, hΓ₀⟩ : ∃ Γ', Γ' = finalCtx Γ (proCutPre walkPieces Wc T p) := ⟨_, rfl⟩
  rw [← hΓ₀] at hDp hDnp hneg
  have hΓ₀f : IsFormulaSet LAct Γ₀ := by rw [hΓ₀]; exact finalCtx_isFormulaSet 8 htbl hΓ c0ok
  have layP₀ : PLay Wc T Γ₀ s σc := by rw [hΓ₀]; have := hLay.play.transport c0nd; rwa [c0sh, zero_add] at this
  obtain ⟨k, hk⟩ : ∃ k, k = len (memberList s) := ⟨_, rfl⟩
  -- block 1 (at `Bi = 8 D`)
  have hE₁ : 40 * D + 18 * ‖D‖ + B₁ + 8 * D + 40 ≤ E := le_trans (le_of_add_eq' (c := 12 * D + 2 * B₂ + 20) (by ring)) hE
  obtain ⟨σ₁, hσ₁, hσ₁D, b1ok, b1nd, b1sh, csh₁, layP₃, hins₃, der₃, fst₃, dlen₃, le₃⟩ :=
    cutBlock_ok (Bi := 8 * D) htbl hP htblN hWl hWc hWp hs hp hd₁ hc₁D hm₁D hσcD (le_trans hip₀D (le_of_add_eq' (c := 2 * D) (by ring)))
      hE₁ hΓ₀f layP₀ hDp hch₁
  obtain ⟨s₁, hs₁⟩ : ∃ x, x = shiftsV L₁ := ⟨_, rfl⟩
  rw [← hs₁] at b1ok b1nd b1sh csh₁ layP₃ hins₃ der₃ fst₃ dlen₃ le₃
  rw [← hk] at hins₃
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ, τ = 1 + σ₁ + s₁ + 2 := ⟨_, rfl⟩
  rw [← hτ₁] at b1sh layP₃ hins₃
  obtain ⟨Γ₃, hΓ₃⟩ : ∃ Γ', Γ' = finalCtx Γ₀ (appendV (cutPro walkPieces Wl Wc W T s p σc ip₀)
    (appendV L₁ (postIns W (len (memberList (insert p s)) + 1 + s₁) (σ₁ + s₁) (dlen TAct d₁)))) := ⟨_, rfl⟩
  rw [← hΓ₃] at layP₃ hins₃ der₃ fst₃ dlen₃ le₃
  have hΓ₃f : IsFormulaSet LAct Γ₃ := by rw [hΓ₃]; exact finalCtx_isFormulaSet 9 htbl hΓ₀f b1ok
  have hτ₁D : τ₁ ≤ 6 * D + B₁ + 4 := by
    rw [hτ₁]
    calc 1 + σ₁ + s₁ + 2 ≤ 1 + (6 * D + 1) + B₁ + 2 := add_le_add (add_le_add (add_le_add (le_refl 1) hσ₁D) csh₁) (le_refl 2)
      _ = 6 * D + B₁ + 4 := by ring
  -- the negation's dossier and `negFact`, moved through block 1
  have hDnp₃ : DossF walkPieces Γ₃ 0 (neg LAct p) (inp₀ + τ₁) := by
    rw [hΓ₃]; have := dossF_transport' b1nd hDnp; rwa [b1sh] at this
  have hneg₃ : neg LAct (negFact (^&(inp₀ + τ₁)) (^&(ip₀ + τ₁))) ∈ Γ₃ := by
    rw [hΓ₃]
    have := tr_fact b1nd (isFormula_negFact (hf_ _) (hf_ _)) hneg
    rwa [b1sh, shiftIterV_negFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
  -- block 2 (at `i = σc + τ₁`, `ip = inp₀ + τ₁`, `Bi = 14 D + B + 4`)
  have hE₂ : 40 * D + 18 * ‖D‖ + B₂ + (14 * D + B₁ + 4) + 40 ≤ E := le_trans (le_of_add_eq' (c := 6 * D + B₂ + 16) (by ring)) hE
  have hiB₂ : σc + τ₁ ≤ 14 * D + B₁ + 4 := le_trans (add_le_add hσcD hτ₁D) (le_of_add_eq' (c := 0) (by ring))
  have hipB₂ : inp₀ + τ₁ ≤ 14 * D + B₁ + 4 :=
    le_trans (add_le_add hinp₀D hτ₁D) (le_of_add_eq' (c := 6 * D) (by ring))
  obtain ⟨σ₂, hσ₂, hσ₂D, b2ok, b2nd, b2sh, csh₂, layP₆, hins₆, der₆, fst₆, dlen₆, le₆⟩ :=
    cutBlock_ok (Bi := 14 * D + B₁ + 4) htbl hP htblN hWl hWc hWp hs hnp hd₂ hc₂D hm₂D hiB₂ hipB₂ hE₂ hΓ₃f layP₃ hDnp₃ hch₂
  obtain ⟨s₂, hs₂⟩ : ∃ x, x = shiftsV L₂ := ⟨_, rfl⟩
  rw [← hs₂] at b2ok b2nd b2sh csh₂ layP₆ hins₆ der₆ fst₆ dlen₆ le₆
  rw [← hk] at hins₆
  obtain ⟨τ₂, hτ₂⟩ : ∃ τ, τ = 1 + σ₂ + s₂ + 2 := ⟨_, rfl⟩
  rw [← hτ₂] at b2sh layP₆ hins₆
  obtain ⟨Γ₆, hΓ₆⟩ : ∃ Γ', Γ' = finalCtx Γ₃ (appendV (cutPro walkPieces Wl Wc W T s (neg LAct p) (σc + τ₁) (inp₀ + τ₁))
    (appendV L₂ (postIns W (len (memberList (insert (neg LAct p) s)) + 1 + s₂) (σ₂ + s₂) (dlen TAct d₂)))) := ⟨_, rfl⟩
  rw [← hΓ₆] at layP₆ hins₆ der₆ fst₆ dlen₆ le₆
  have hΓ₆f : IsFormulaSet LAct Γ₆ := by rw [hΓ₆]; exact finalCtx_isFormulaSet 9 htbl hΓ₃f b2ok
  have hτ₂D : τ₂ ≤ 6 * D + B₂ + 4 := by
    rw [hτ₂]
    calc 1 + σ₂ + s₂ + 2 ≤ 1 + (6 * D + 1) + B₂ + 2 := add_le_add (add_le_add (add_le_add (le_refl 1) hσ₂D) csh₂) (le_refl 2)
      _ = 6 * D + B₂ + 4 := by ring
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = σc + τ₁ + τ₂ := ⟨_, rfl⟩
  -- block-1 facts moved through block 2
  have hins₆' : neg LAct (insFact (^&(σ₁ + s₁ + 2 + τ₂)) (^&(ip₀ + τ₁ + τ₂)) (^&(τ + (k + 1)))) ∈ Γ₆ := by
    rw [hΓ₆]
    have := tr_fact b2nd (isFormula_insFact (hf_ _) (hf_ _) (hf_ _)) hins₃
    rw [b2sh, shiftIterV_insFact (hf_ _) (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show σc + τ₁ + (k + 1) + τ₂ = τ + (k + 1) by rw [hτ]; ring] at this
  have der₆' : neg LAct (derFact (^&(1 + τ₂) : V)) ∈ Γ₆ := by
    rw [hΓ₆]; have := tr_fact b2nd (isFormula_derFact (hf_ _)) der₃
    rwa [b2sh, shiftIterV_derFact (hf_ _), termShiftIterV_fvar] at this
  have fst₆' : neg LAct (fstIdxFact (^&(σ₁ + s₁ + 2 + τ₂)) (^&(1 + τ₂))) ∈ Γ₆ := by
    rw [hΓ₆]; have := tr_fact b2nd (isFormula_fstIdxFact (hf_ _) (hf_ _)) fst₃
    rwa [b2sh, shiftIterV_fstIdxFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
  have dlen₆' : neg LAct (dlenFact (^&(1 + τ₂) : V) (^&(0 + τ₂))) ∈ Γ₆ := by
    rw [hΓ₆]; have := tr_fact b2nd (isFormula_dlenFact (hf_ _) (hf_ _)) dlen₃
    rwa [b2sh, shiftIterV_dlenFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
  have le₆' : neg LAct (leFact (^&(0 + τ₂)) (bnum (dlen TAct d₁))) ∈ Γ₆ := by
    rw [hΓ₆]; have := tr_fact b2nd (isFormula_leFact (hf_ _) (isSemiterm_bnum_LAct 0 _)) le₃
    rwa [b2sh, shiftIterV_leFact (hf_ _) (isSemiterm_bnum_LAct 0 _), termShiftIterV_fvar, termShiftIterV_bnum'] at this
  have hneg₆ : neg LAct (negFact (^&(inp₀ + τ₁ + τ₂)) (^&(ip₀ + τ₁ + τ₂))) ∈ Γ₆ := by
    rw [hΓ₆]; have := tr_fact b2nd (isFormula_negFact (hf_ _) (hf_ _)) hneg₃
    rwa [b2sh, shiftIterV_negFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
  have layS₆ : Layout walkPieces Wc T Γ₆ s τ := by
    have := layP₆.layout; rwa [show σc + τ₁ + τ₂ = τ by rw [hτ]] at this
  have hins₆'' : neg LAct (insFact (^&(σ₂ + s₂ + 2)) (^&(inp₀ + τ₁ + τ₂)) (^&(τ + (k + 1)))) ∈ Γ₆ := by
    rwa [show σc + τ₁ + τ₂ = τ by rw [hτ]] at hins₆
  -- the node's caps
  have hτD : τ ≤ 20 * D + B₁ + B₂ + 8 := by
    rw [hτ]; exact le_trans (add_le_add (add_le_add hσcD hτ₁D) hτ₂D) (le_of_add_eq' (c := 0) (by ring))
  have his : τ + (k + 1) + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc τ + (k + 1) + 2 ≤ (20 * D + B₁ + B₂ + 8) + (D + 1) + 2 := add_le_add (add_le_add hτD (add_le_add (hk ▸ hkD) (le_refl 1))) (le_refl 2)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 39 * D + B₂ + 49) (by ring)
  have hip : ip₀ + τ₁ + τ₂ + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc ip₀ + τ₁ + τ₂ + 2 ≤ 6 * D + (6 * D + B₁ + 4) + (6 * D + B₂ + 4) + 2 :=
          add_le_add (add_le_add (add_le_add hip₀D hτ₁D) hτ₂D) (le_refl 2)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 42 * D + B₂ + 50) (by ring)
  have hinp : inp₀ + τ₁ + τ₂ + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc inp₀ + τ₁ + τ₂ + 2 ≤ 2 * D + (6 * D + B₁ + 4) + (6 * D + B₂ + 4) + 2 :=
          add_le_add (add_le_add (add_le_add hinp₀D hτ₁D) hτ₂D) (le_refl 2)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 46 * D + B₂ + 50) (by ring)
  have hid₁ : 1 + τ₂ + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc 1 + τ₂ + 2 ≤ 1 + (6 * D + B₂ + 4) + 2 := add_le_add (add_le_add (le_refl 1) hτ₂D) (le_refl 2)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 54 * D + B₁ + B₂ + 53) (by ring)
  have hid₂ : (1 : V) + 2 ≤ E := le_trans (le_of_add_eq' (c := 60 * D + B₁ + 2 * B₂ + 57) (by ring)) hE'
  have hic₁ : σ₁ + s₁ + 2 + τ₂ + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc σ₁ + s₁ + 2 + τ₂ + 2 ≤ (6 * D + 1) + B₁ + 2 + (6 * D + B₂ + 4) + 2 :=
          add_le_add (add_le_add (add_le_add (add_le_add hσ₁D csh₁) (le_refl 2)) hτ₂D) (le_refl 2)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 48 * D + B₂ + 51) (by ring)
  have hic₂ : σ₂ + s₂ + 2 + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc σ₂ + s₂ + 2 + 2 ≤ (6 * D + 1) + B₂ + 2 + 2 := add_le_add (add_le_add (add_le_add hσ₂D csh₂) (le_refl 2)) (le_refl 2)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 54 * D + B₁ + B₂ + 55) (by ring)
  have hT : τ + τ₂ + 0 + 10 ≤ E := by
    refine le_trans ?_ hE'
    calc τ + τ₂ + 0 + 10 ≤ (20 * D + B₁ + B₂ + 8) + (6 * D + B₂ + 4) + 0 + 10 :=
          add_le_add (add_le_add (add_le_add hτD hτ₂D) (le_refl 0)) (le_refl 10)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 34 * D + 38) (by ring)
  have hn : 18 * ‖dlen TAct (cutRule s p d₁ d₂)‖ + 7 ≤ E := by
    have hn1 : ‖dlen TAct (cutRule s p d₁ d₂)‖ ≤ 3 * D + 1 := by
      refine le_trans (length_le _) ?_
      rw [hdl]
      exact le_trans (add_le_add (add_le_add (add_le_add hsD hm₁D) hm₂D) (le_refl 1)) (le_of_add_eq' (c := 0) (by ring))
    refine le_trans ?_ hE'
    calc 18 * ‖dlen TAct (cutRule s p d₁ d₂)‖ + 7 ≤ 18 * (3 * D + 1) + 7 :=
          add_le_add (mul_le_mul_of_nonneg_left hn1 zero_le) (le_refl 7)
      _ ≤ 60 * D + B₁ + 2 * B₂ + 60 := le_of_add_eq' (c := 6 * D + B₁ + 2 * B₂ + 35) (by ring)
  have hLn : setLen LAct s + dlen TAct d₁ + dlen TAct d₂ + 1 ≤ dlen TAct (cutRule s p d₁ d₂) := by rw [hdl]
  -- the node
  obtain ⟨nok, nnd, nsh, -, ngoal⟩ := nodeCut_ok (E := E) (is := τ + (k + 1)) (il := τ) (ip := ip₀ + τ₁ + τ₂)
    (inp := inp₀ + τ₁ + τ₂) (id₁ := 1 + τ₂) (id₂ := 1) (ic₁ := σ₁ + s₁ + 2 + τ₂) (ic₂ := σ₂ + s₂ + 2) (in₁ := τ₂) (in₂ := 0)
    (L := setLen LAct s) (m₁ := dlen TAct d₁) (m₂ := dlen TAct d₂) (n := dlen TAct (cutRule s p d₁ d₂))
    htbl hP.frag1Table hW₁ htblN hΓ₆f his hip hinp hid₁ hid₂ hic₁ hic₂ hT hn hLn fst₆' hins₆' der₆'
    (by rwa [zero_add] at dlen₆') (by rwa [zero_add] at le₆') fst₆ hneg₆ hins₆'' der₆ dlen₆ le₆
    (by have := layS₆.2.1; rwa [← hk] at this) layS₆.2.2
  -- assembly
  unfold vCut
  rw [← hσc, ← hip₀, ← hinp₀, ← hσ₁, ← hσ₂, ← hs₁, ← hs₂, ← hk]
  rw [show 1 + σ₁ + s₁ + 2 = τ₁ by rw [hτ₁], show 1 + σ₂ + s₂ + 2 = τ₂ by rw [hτ₂], show σc + τ₁ + τ₂ = τ by rw [hτ]]
  rw [appendV_regroup8]
  have ok₂ : ListOK tbl E ((9 : ℕ) : V) Γ₃ (appendV (appendV (cutPro walkPieces Wl Wc W T s (neg LAct p) (σc + τ₁) (inp₀ + τ₁))
      (appendV L₂ (postIns W (len (memberList (insert (neg LAct p) s)) + 1 + s₂) (σ₂ + s₂) (dlen TAct d₂))))
      (nodeCut W₁ T (τ + (k + 1)) τ (ip₀ + τ₁ + τ₂) (inp₀ + τ₁ + τ₂) (1 + τ₂) 1 (σ₁ + s₁ + 2 + τ₂) (σ₂ + s₂ + 2) τ₂ 0
        (setLen LAct s) (dlen TAct d₁) (dlen TAct d₂) (dlen TAct (cutRule s p d₁ d₂)))) :=
    listOK_appendV b2ok (by rw [← hΓ₆]; exact nok)
  have ok₁ := listOK_appendV b1ok (by rw [← hΓ₃]; exact ok₂)
  have ok₀ := listOK_appendV (c0ok.mono h89) (by rw [← hΓ₀]; exact ok₁)
  refine ⟨ok₀, noDrop'_appendV c0nd (noDrop'_appendV b1nd (noDrop'_appendV b2nd nnd)), ?_, ?_⟩
  · rw [shiftsV_appendV, c0sh, shiftsV_appendV, b1sh, shiftsV_appendV, b2sh, nsh]
    calc σc + (τ₁ + (τ₂ + 1)) ≤ 8 * D + ((6 * D + B₁ + 4) + ((6 * D + B₂ + 4) + 1)) :=
          add_le_add hσcD (add_le_add hτ₁D (add_le_add hτ₂D (le_refl 1)))
      _ = 20 * D + B₁ + B₂ + 9 := by ring
  · rw [shiftsV_appendV, c0sh, shiftsV_appendV, b1sh, shiftsV_appendV, b2sh, nsh,
      finalCtx_appendV, ← hΓ₀, finalCtx_appendV, ← hΓ₃, finalCtx_appendV, ← hΓ₆,
      show k + 1 + (σc + (τ₁ + (τ₂ + 1))) = τ + (k + 1) + 1 by rw [hτ]; ring]
    exact ngoal

end cutOk2

/-! ### 8.8 `all` and `exs`: `proAll`/`proExs`, the child, `postIns`, `nodeAll`/`nodeExs`

The prologue's shift count is taken as an abstract bound `SA` (`hSA`), so that the best available bound
(`Prologue.shiftsV_proAll_le`, quintic in `D`; the linear-`certSubst` forms via `Pin` when restated) can be plugged in by the
caller; the E-room is `hE : SA + 40·D + 18‖D‖ + B + 40 ≤ E` plus the quadratic-cubic caps the prologue itself needs. -/

section allExsOk

lemma memTop_add (Ww Wc T s y i : V) : memTop Ww Wc T s y i = memTop Ww Wc T s y 0 + i := by
  simp only [memTop, mTop]; ring

set_option maxHeartbeats 6000000 in
/-- **The `all` list is applicable** at the node's layout. -/
theorem vAll_ok {tbl N N' B' Wl Wc W₂ W T s p d' L' D B SA E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces) (hW₂ : W₂ = frag2Pieces)
    (hs : IsFormulaSet LAct s) (hr : (^∀ p) ∈ s) (hd' : DerivationOf TAct d' (insert (free LAct p) (setShift LAct s)))
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (insert (free LAct p) (setShift LAct s)) ≤ D)
    (hspD : formulaLen LAct (shift LAct p) ≤ D) (hmD : dlen TAct d' ≤ D)
    (hSA : shiftsV (proAll walkPieces Wl Wc W T s p 0) ≤ SA)
    (hE : SA + 40 * D + 18 * ‖D‖ + B + 40 ≤ E)
    (hEQ : 2 * ((1 + D) * (1 + D + 1)) * (D + 1) + 4 * D + 11 ≤ E)
    (hiE : 0 + 2 * ((1 + D) * (1 + D + 1)) * D + 40 * D + 20 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : NodeLay walkPieces Wc T Γ s) (hch : ChildOK tbl Wc T E L' d' B) :
    ListOK tbl E ((9 : ℕ) : V) Γ (vAll walkPieces Wl Wc W₂ W T s p d' L') ∧ NoDrop' (vAll walkPieces Wl Wc W₂ W T s p d' L') ∧
    shiftsV (vAll walkPieces Wl Wc W₂ W T s p d' L') ≤ SA + B + 3 ∧
    neg LAct (goalFact (^&(len (memberList s) + 1 + shiftsV (vAll walkPieces Wl Wc W₂ W T s p d' L')))
      (bnum (dlen TAct (allIntro s p d')))) ∈ finalCtx Γ (vAll walkPieces Wl Wc W₂ W T s p d' L') := by
  have hW : WalkTable tbl := hP.walkTable
  have hp : IsSemiformula LAct 1 p := by have := IsSemiformula.all.mp (hs _ hr); simpa using this
  have hD : Derivation TAct (allIntro s p d') := Derivation.allIntro hr hd'
  have hdl : dlen TAct (allIntro s p d') = setLen LAct s + dlen TAct d' + 1 := dlen_allIntro hD
  have hk1 : 1 ≤ len (memberList s) := one_le_len_memberList_of_mem hr
  have hLayS : Layout walkPieces Wc T Γ s 0 := hLay.layout
  have hcfst : fstIdx d' = insert (free LAct p) (setShift LAct s) := hd'.1
  have hkD : len (memberList s) ≤ D := len_memberList_le_of_setLen hs hsD
  have hcs : IsFormulaSet LAct (insert (free LAct p) (setShift LAct s)) := DerivationOf.isFormulaSet hd'
  have hkcD : len (memberList (insert (free LAct p) (setShift LAct s))) ≤ D := len_memberList_le_of_setLen hcs hcD
  have hE13 : 13 * D + 18 * ‖D‖ + 12 ≤ E := le_trans (le_of_add_eq' (c := SA + 27 * D + B + 28) (by ring)) hE
  have hE' : SA + 40 * D + B + 40 ≤ E := le_trans (le_of_add_eq' (c := 18 * ‖D‖) (by ring)) hE
  -- the layout's `all` facts
  obtain ⟨hall, -, hmr⟩ := layout_all htbl hP hp hr hLayS
  rw [zero_add] at hmr
  obtain ⟨ir₀, hir₀⟩ : ∃ x, x = memTop walkPieces Wc T s (^∀ p) 0 := ⟨_, rfl⟩
  have hir₀D : ir₀ ≤ 6 * D + 1 := by
    rw [hir₀]; have := memTop_le htbl hW hWc T hs hr hsD (i := 0); rwa [zero_add] at this
  rw [← hir₀] at hall hmr
  -- the prologue
  obtain ⟨pok, pnd, psh, layC, layS, hfree, hsh, hins, heq⟩ :=
    proAll_ok htbl hP htblN hWl hWc hWp hs hp hr hsD hcD hspD hE13 hEQ hiE hΓ hLayS
  obtain ⟨σA, hσA⟩ : ∃ x, x = shiftsV (proAll walkPieces Wl Wc W T s p 0) := ⟨_, rfl⟩
  have hσAB : σA ≤ SA := by rw [hσA]; exact hSA
  obtain ⟨σc, hσc⟩ : ∃ x, x = proSig walkPieces Wl Wc W T (insert (free LAct p) (setShift LAct s)) := ⟨_, rfl⟩
  obtain ⟨ifp₀, hifp₀⟩ : ∃ x, x = allCf walkPieces Wc p +
    (proSig walkPieces Wl Wc W T (setShift LAct s) + (1 + (len (memberList s) + 1) + proSig walkPieces Wl Wc W T s)) + 1 + σc := ⟨_, rfl⟩
  obtain ⟨iss₀, hiss₀⟩ : ∃ x, x = 1 + (len (memberList s) + 1) + proSig walkPieces Wl Wc W T s + 1 + σc +
    (len (memberList (setShift LAct s)) + 1) := ⟨_, rfl⟩
  have hσAe : σA = allCertSig walkPieces Wc p +
      (proSig walkPieces Wl Wc W T (setShift LAct s) + (1 + (len (memberList s) + 1) + proSig walkPieces Wl Wc W T s)) + (1 + σc) := by
    rw [hσA, psh, hσc]
  rw [← hσc] at layS hfree hsh hins heq
  simp only [zero_add] at layS hfree hsh hins heq
  rw [← hσAe] at layS hfree hsh
  rw [← hifp₀] at hfree hins
  rw [← hiss₀] at hsh hins
  rw [memTop_add, ← hir₀] at hfree
  obtain ⟨k, hk⟩ : ∃ k, k = len (memberList s) := ⟨_, rfl⟩
  obtain ⟨kc, hkc⟩ : ∃ x, x = len (memberList (insert (free LAct p) (setShift LAct s))) := ⟨_, rfl⟩
  rw [← hk] at hsh
  rw [← hkc] at heq
  -- bounds on the partial offsets
  have hσcD : σc ≤ 6 * D + 1 := by
    rw [hσc]; exact proSig_le htbl hP hWc htblN hWl hWp hcs (one_le_len_memberList_insert _ _) hcD
      (le_trans (le_of_add_eq' (c := SA + 27 * D + B + 32) (by ring)) hE) hΓ
  have hifp₀A : ifp₀ ≤ σA := by
    rw [hifp₀, hσAe, allCertSig]
    exact le_of_add_eq' (c := descCountF walkPieces 1 (shift LAct p) + descCountF walkPieces 0 (free LAct p)) (by ring)
  have hkv : len (memberList (setShift LAct s)) ≤ D :=
    le_trans (len_memberList_le_setLen (hs.setShift)) (le_trans (setLen_le_insert _ _) hcD)
  have hσA_lb : proSig walkPieces Wl Wc W T (setShift LAct s) + (1 + (len (memberList s) + 1) + proSig walkPieces Wl Wc W T s) + (1 + σc) ≤ σA := by
    rw [hσAe]; exact le_of_add_eq' (c := allCertSig walkPieces Wc p) (by ring)
  have hiss₀A : iss₀ ≤ σA + D + 1 := by
    rw [hiss₀]
    calc 1 + (len (memberList s) + 1) + proSig walkPieces Wl Wc W T s + 1 + σc + (len (memberList (setShift LAct s)) + 1)
        ≤ 1 + (len (memberList s) + 1) + proSig walkPieces Wl Wc W T s + 1 + σc + (D + 1) :=
          add_le_add (le_refl _) (add_le_add hkv (le_refl 1))
      _ ≤ σA + D + 1 := by
          refine le_trans ?_ (add_le_add (add_le_add hσA_lb (le_refl D)) (le_refl 1))
          exact le_of_add_eq' (c := proSig walkPieces Wl Wc W T (setShift LAct s)) (by ring)
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ (proAll walkPieces Wl Wc W T s p 0) := ⟨_, rfl⟩
  rw [← hΓ₁] at layC layS hfree hsh hins heq
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 9 htbl hΓ pok
  have layC' : NodeLay walkPieces Wc T Γ₁ (fstIdx d') := by rw [hcfst]; exact Or.inl ⟨one_le_len_memberList_insert _ _, layC⟩
  -- the child
  obtain ⟨cok, cnd, csh, cgoal⟩ := hch Γ₁ hΓ₁f layC'
  obtain ⟨s', hs'⟩ : ∃ s', s' = shiftsV L' := ⟨_, rfl⟩
  obtain ⟨Γ₂, hΓ₂⟩ : ∃ Γ', Γ' = finalCtx Γ₁ L' := ⟨_, rfl⟩
  rw [← hΓ₂, ← hs', hcfst, ← hkc] at cgoal
  rw [← hs'] at csh
  have hΓ₂f : IsFormulaSet LAct Γ₂ := by rw [hΓ₂]; exact finalCtx_isFormulaSet 9 htbl hΓ₁f cok
  have heq₂ : neg LAct (eqFactB (^&(σc + s')) (^&(kc + 1 + s'))) ∈ Γ₂ := by
    rw [hΓ₂, hs']
    have := tr_fact cnd (isFormula_eqFactB (hf_ _) (hf_ _)) heq
    rwa [shiftIterV_eqFactB (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
  -- `postIns`
  have hsE : kc + 1 + s' + 3 ≤ E := by
    refine le_trans ?_ hE'
    calc kc + 1 + s' + 3 ≤ D + 1 + B + 3 := add_le_add (add_le_add (add_le_add (hkc ▸ hkcD) (le_refl 1)) csh) (le_refl 3)
      _ ≤ SA + 40 * D + B + 40 := le_of_add_eq' (c := SA + 39 * D + 36) (by ring)
  have hcE : σc + s' + 3 ≤ E := by
    refine le_trans ?_ hE'
    calc σc + s' + 3 ≤ (6 * D + 1) + B + 3 := add_le_add (add_le_add hσcD csh) (le_refl 3)
      _ ≤ SA + 40 * D + B + 40 := le_of_add_eq' (c := SA + 34 * D + 36) (by ring)
  obtain ⟨qok, qnd, qsh, -, qder, qfst, qdlen, qle⟩ := postIns_ok htbl hP hWp hΓ₂f hsE hcE cgoal heq₂
  obtain ⟨Γ₃, hΓ₃⟩ : ∃ Γ', Γ' = finalCtx Γ₂ (postIns W (kc + 1 + s') (σc + s') (dlen TAct d')) := ⟨_, rfl⟩
  rw [← hΓ₃] at qder qfst qdlen qle
  have hΓ₃f : IsFormulaSet LAct Γ₃ := by rw [hΓ₃]; exact finalCtx_isFormulaSet 8 htbl hΓ₂f qok
  have hΓ₃e : Γ₃ = finalCtx Γ₁ (appendV L' (postIns W (kc + 1 + s') (σc + s') (dlen TAct d'))) := by
    rw [finalCtx_appendV, ← hΓ₂, hΓ₃]
  have hnd₂ : NoDrop' (appendV L' (postIns W (kc + 1 + s') (σc + s') (dlen TAct d'))) := noDrop'_appendV cnd qnd
  have hsh₂ : shiftsV (appendV L' (postIns W (kc + 1 + s') (σc + s') (dlen TAct d'))) = s' + 2 := by
    rw [shiftsV_appendV, qsh, hs']
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = σA + s' + 2 := ⟨_, rfl⟩
  have layS₃ : Layout walkPieces Wc T Γ₃ s τ := by
    rw [hΓ₃e, hτ]; have := layS.transport hnd₂; rwa [hsh₂, ← add_assoc] at this
  have hfree₃ : neg LAct (freeFact (^&(ifp₀ + s' + 2)) (^&(ir₀ + τ + 1))) ∈ Γ₃ := by
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_freeFact (hf_ _) (hf_ _)) hfree
    rw [hsh₂, shiftIterV_freeFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show ifp₀ + (s' + 2) = ifp₀ + s' + 2 by ring, show ir₀ + σA + 1 + (s' + 2) = ir₀ + τ + 1 by rw [hτ]; ring] at this
  have hsh₃ : neg LAct (setShiftFact (^&(iss₀ + s' + 2)) (^&(τ + (k + 1)))) ∈ Γ₃ := by
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_setShiftFact (hf_ _) (hf_ _)) hsh
    rw [hsh₂, shiftIterV_setShiftFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show iss₀ + (s' + 2) = iss₀ + s' + 2 by ring, show σA + (k + 1) + (s' + 2) = τ + (k + 1) by rw [hτ]; ring] at this
  have hins₃ : neg LAct (insFact (^&(σc + s' + 2)) (^&(ifp₀ + s' + 2)) (^&(iss₀ + s' + 2))) ∈ Γ₃ := by
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_insFact (hf_ _) (hf_ _) (hf_ _)) hins
    rw [hsh₂, shiftIterV_insFact (hf_ _) (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show σc + (s' + 2) = σc + s' + 2 by ring, show ifp₀ + (s' + 2) = ifp₀ + s' + 2 by ring,
      show iss₀ + (s' + 2) = iss₀ + s' + 2 by ring] at this
  have hall₃ : neg LAct (allFact (^&(ir₀ + τ)) (^&(ir₀ + τ + 1))) ∈ Γ₃ := by
    have h1 := tr_fact pnd (isFormula_allFact (hf_ _) (hf_ _)) hall
    rw [← hσA, shiftIterV_allFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, ← hΓ₁] at h1
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_allFact (hf_ _) (hf_ _)) h1
    rw [hsh₂, shiftIterV_allFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show ir₀ + σA + (s' + 2) = ir₀ + τ by rw [hτ]; ring, show ir₀ + 1 + σA + (s' + 2) = ir₀ + τ + 1 by rw [hτ]; ring] at this
  have hmr₃ : neg LAct (memFact (^&(ir₀ + τ)) (^&(τ + (k + 1)))) ∈ Γ₃ := by
    have h1 := tr_fact pnd (isFormula_memFact (hf_ _) (hf_ _)) hmr
    rw [← hσA, shiftIterV_memFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, ← hΓ₁] at h1
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_memFact (hf_ _) (hf_ _)) h1
    rw [hsh₂, shiftIterV_memFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show ir₀ + σA + (s' + 2) = ir₀ + τ by rw [hτ]; ring,
      show len (memberList s) + 1 + σA + (s' + 2) = τ + (k + 1) by rw [hτ, hk]; ring] at this
  -- the node's caps
  have hτD : τ ≤ SA + B + 2 := by
    rw [hτ]; exact add_le_add (add_le_add hσAB csh) (le_refl 2)
  have his : τ + (k + 1) + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc τ + (k + 1) + 2 ≤ (SA + B + 2) + (D + 1) + 2 := add_le_add (add_le_add hτD (add_le_add (hk ▸ hkD) (le_refl 1))) (le_refl 2)
      _ ≤ SA + 40 * D + B + 40 := le_of_add_eq' (c := 39 * D + 35) (by ring)
  have hir : ir₀ + τ + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc ir₀ + τ + 2 ≤ (6 * D + 1) + (SA + B + 2) + 2 := add_le_add (add_le_add hir₀D hτD) (le_refl 2)
      _ ≤ SA + 40 * D + B + 40 := le_of_add_eq' (c := 34 * D + 35) (by ring)
  have hip : ir₀ + τ + 1 + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc ir₀ + τ + 1 + 2 ≤ (6 * D + 1) + (SA + B + 2) + 1 + 2 := add_le_add (add_le_add (add_le_add hir₀D hτD) (le_refl 1)) (le_refl 2)
      _ ≤ SA + 40 * D + B + 40 := le_of_add_eq' (c := 34 * D + 34) (by ring)
  have hifp : ifp₀ + s' + 2 + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc ifp₀ + s' + 2 + 2 ≤ SA + B + 2 + 2 := add_le_add (add_le_add (add_le_add (le_trans hifp₀A hσAB) csh) (le_refl 2)) (le_refl 2)
      _ ≤ SA + 40 * D + B + 40 := le_of_add_eq' (c := 40 * D + 36) (by ring)
  have hiss : iss₀ + s' + 2 + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc iss₀ + s' + 2 + 2 ≤ (SA + D + 1) + B + 2 + 2 :=
          add_le_add (add_le_add (add_le_add (le_trans hiss₀A (add_le_add (add_le_add hσAB (le_refl D)) (le_refl 1))) csh) (le_refl 2)) (le_refl 2)
      _ ≤ SA + 40 * D + B + 40 := le_of_add_eq' (c := 39 * D + 35) (by ring)
  have hic : σc + s' + 2 + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc σc + s' + 2 + 2 ≤ (6 * D + 1) + B + 2 + 2 := add_le_add (add_le_add (add_le_add hσcD csh) (le_refl 2)) (le_refl 2)
      _ ≤ SA + 40 * D + B + 40 := le_of_add_eq' (c := SA + 34 * D + 35) (by ring)
  have hid : (1 : V) + 2 ≤ E := le_trans (le_of_add_eq' (c := SA + 40 * D + B + 37) (by ring)) hE'
  have hT : τ + 0 + 7 ≤ E := by
    refine le_trans ?_ hE'
    calc τ + 0 + 7 ≤ (SA + B + 2) + 0 + 7 := add_le_add (add_le_add hτD (le_refl 0)) (le_refl 7)
      _ ≤ SA + 40 * D + B + 40 := le_of_add_eq' (c := 40 * D + 31) (by ring)
  have hn : 18 * ‖dlen TAct (allIntro s p d')‖ + 7 ≤ E := by
    have hn1 : ‖dlen TAct (allIntro s p d')‖ ≤ 2 * D + 1 := by
      refine le_trans (length_le _) ?_
      rw [hdl]
      exact le_trans (add_le_add (add_le_add hsD hmD) (le_refl 1)) (le_of_add_eq' (c := 0) (by ring))
    refine le_trans ?_ hE'
    calc 18 * ‖dlen TAct (allIntro s p d')‖ + 7 ≤ 18 * (2 * D + 1) + 7 :=
          add_le_add (mul_le_mul_of_nonneg_left hn1 zero_le) (le_refl 7)
      _ ≤ SA + 40 * D + B + 40 := le_of_add_eq' (c := SA + 4 * D + B + 15) (by ring)
  have hLn : setLen LAct s + dlen TAct d' + 1 ≤ dlen TAct (allIntro s p d') := by rw [hdl]
  -- the node
  obtain ⟨nok, nnd, nsh, -, ngoal⟩ := nodeAll_ok (E := E) (is := τ + (k + 1)) (il := τ) (ir := ir₀ + τ) (ip := ir₀ + τ + 1)
    (ifp := ifp₀ + s' + 2) (iss := iss₀ + s' + 2) (ic := σc + s' + 2) (id := 1) (in₁ := 0) (L := setLen LAct s)
    (m₁ := dlen TAct d') (n := dlen TAct (allIntro s p d'))
    htbl hP.frag2Table hW₂ htblN hΓ₃f his hir hip hifp hiss hic hid hT hn hLn hall₃ hmr₃ qfst hfree₃ hsh₃ hins₃ qder qdlen qle
    (by have := layS₃.2.1; rwa [← hk] at this) layS₃.2.2
  -- assembly
  unfold vAll
  rw [← hσc, ← hs', ← hk, ← hkc]
  rw [show allCertSig walkPieces Wc p + (proSig walkPieces Wl Wc W T (setShift LAct s) + (1 + (k + 1) + proSig walkPieces Wl Wc W T s)) +
      (1 + σc) + s' + 2 = τ by rw [hτ, hσAe, hk]]
  rw [memTop_add, ← hir₀]
  rw [show allCf walkPieces Wc p + (proSig walkPieces Wl Wc W T (setShift LAct s) + (1 + (k + 1) + proSig walkPieces Wl Wc W T s)) + 1 +
      σc + s' + 2 = ifp₀ + s' + 2 by rw [hifp₀, hk]]
  rw [show 0 + 1 + (k + 1) + proSig walkPieces Wl Wc W T s + 1 + σc + (len (memberList (setShift LAct s)) + 1) + s' + 2 =
      iss₀ + s' + 2 by rw [hiss₀, hk]; ring]
  have ok₃ : ListOK tbl E ((9 : ℕ) : V) Γ₂ (appendV (postIns W (kc + 1 + s') (σc + s') (dlen TAct d'))
      (nodeAll W₂ T (τ + (k + 1)) τ (ir₀ + τ) (ir₀ + τ + 1) (ifp₀ + s' + 2) (iss₀ + s' + 2) (σc + s' + 2) 1 0
        (setLen LAct s) (dlen TAct d') (dlen TAct (allIntro s p d')))) :=
    listOK_appendV (qok.mono h89) (by rw [← hΓ₃]; exact nok.mono h89)
  have ok₂ := listOK_appendV cok (by rw [← hΓ₂]; exact ok₃)
  have ok₁ := listOK_appendV pok (by rw [← hΓ₁]; exact ok₂)
  refine ⟨ok₁, noDrop'_appendV pnd (noDrop'_appendV cnd (noDrop'_appendV qnd nnd)), ?_, ?_⟩
  · rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, ← hσA, ← hs', qsh, nsh]
    calc σA + (s' + (2 + 1)) ≤ SA + (B + (2 + 1)) := add_le_add hσAB (add_le_add csh (le_refl _))
      _ = SA + B + 3 := by ring
  · rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, ← hσA, ← hs', qsh, nsh,
      finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂, ← hΓ₃,
      show k + 1 + (σA + (s' + (2 + 1))) = τ + (k + 1) + 1 by rw [hτ]; ring]
    exact ngoal

end allExsOk

section exsOk

set_option maxHeartbeats 6000000 in
/-- **The `exs` list is applicable** at the node's layout (the prologue's shift count as the abstract bound `SA`). -/
theorem vExs_ok {tbl N N' B' Wl Wc W₂ W T s p t d' L' D B SA E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces) (hW₂ : W₂ = frag2Pieces)
    (hs : IsFormulaSet LAct s) (hr : (^∃ p) ∈ s) (ht : IsSemiterm LAct 0 t) (hd' : DerivationOf TAct d' (insert (substs1 LAct t p) s))
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (insert (substs1 LAct t p) s) ≤ D) (htD : termLen LAct t ≤ D) (hmD : dlen TAct d' ≤ D)
    (hSA : shiftsV (proExs walkPieces Wl Wc W T s p t 0) ≤ SA)
    (hE : 2 * SA + 60 * D + 18 * ‖D‖ + 2 * B + 60 ≤ E)
    (hEQ : 2 * ((1 + D) * (1 + D + D)) * (D + 1) + 4 * D + 11 ≤ E)
    (hiE : 0 + 2 * ((1 + D) * (1 + D + D)) * D + 40 * D + 20 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : NodeLay walkPieces Wc T Γ s) (hch : ChildOK tbl Wc T E L' d' B) :
    ListOK tbl E ((9 : ℕ) : V) Γ (vExs walkPieces Wl Wc W₂ W T s p t d' L') ∧ NoDrop' (vExs walkPieces Wl Wc W₂ W T s p t d' L') ∧
    shiftsV (vExs walkPieces Wl Wc W₂ W T s p t d' L') ≤ SA + B + 3 ∧
    neg LAct (goalFact (^&(len (memberList s) + 1 + shiftsV (vExs walkPieces Wl Wc W₂ W T s p t d' L')))
      (bnum (dlen TAct (exsIntro s p t d')))) ∈ finalCtx Γ (vExs walkPieces Wl Wc W₂ W T s p t d' L') := by
  have hW : WalkTable tbl := hP.walkTable
  have hp : IsSemiformula LAct 1 p := by have := IsSemiformula.exs.mp (hs _ hr); simpa using this
  have hD : Derivation TAct (exsIntro s p t d') := Derivation.exsIntro hr ht hd'
  have hdl : dlen TAct (exsIntro s p t d') = setLen LAct s + termLen LAct t + dlen TAct d' + 1 := dlen_exsIntro hD
  have hk1 : 1 ≤ len (memberList s) := one_le_len_memberList_of_mem hr
  have hLayS : Layout walkPieces Wc T Γ s 0 := hLay.layout
  have hcfst : fstIdx d' = insert (substs1 LAct t p) s := hd'.1
  have hkD : len (memberList s) ≤ D := len_memberList_le_of_setLen hs hsD
  have hcs : IsFormulaSet LAct (insert (substs1 LAct t p) s) := DerivationOf.isFormulaSet hd'
  have hkcD : len (memberList (insert (substs1 LAct t p) s)) ≤ D := len_memberList_le_of_setLen hcs hcD
  have hE13 : 13 * D + 18 * ‖D‖ + 12 ≤ E := le_trans (le_of_add_eq' (c := 2 * SA + 47 * D + 2 * B + 48) (by ring)) hE
  have hE' : 2 * SA + 60 * D + 2 * B + 60 ≤ E := le_trans (le_of_add_eq' (c := 18 * ‖D‖) (by ring)) hE
  -- the layout's `exs` facts
  obtain ⟨hexs, -, hmr⟩ := layout_exs htbl hP hp hr hLayS
  rw [zero_add] at hmr
  obtain ⟨ir₀, hir₀⟩ : ∃ x, x = memTop walkPieces Wc T s (^∃ p) 0 := ⟨_, rfl⟩
  have hir₀D : ir₀ ≤ 6 * D + 1 := by
    rw [hir₀]; have := memTop_le htbl hW hWc T hs hr hsD (i := 0); rwa [zero_add] at this
  rw [← hir₀] at hexs hmr
  -- the prologue
  obtain ⟨pok, pnd, psh, layC, layS, htpi, htl, hlet, hsub, hins, heq⟩ :=
    proExs_ok htbl hP htblN hWl hWc hWp hs hp hr ht hsD hcD htD hE13 hEQ hiE hΓ hLayS
  obtain ⟨σA, hσA⟩ : ∃ x, x = shiftsV (proExs walkPieces Wl Wc W T s p t 0) := ⟨_, rfl⟩
  have hσAB : σA ≤ SA := by rw [hσA]; exact hSA
  obtain ⟨σc, hσc⟩ : ∃ x, x = proSig walkPieces Wl Wc W T (insert (substs1 LAct t p) s) := ⟨_, rfl⟩
  obtain ⟨eS, heS⟩ : ∃ x, x = exsSig walkPieces Wc T s p t 0 := ⟨_, rfl⟩
  obtain ⟨eIw, heIw⟩ : ∃ x, x = exsIw walkPieces Wc T t p := ⟨_, rfl⟩
  obtain ⟨eSc, heSc⟩ : ∃ x, x = exsSc walkPieces Wc T s p t 0 := ⟨_, rfl⟩
  obtain ⟨eC3, heC3⟩ : ∃ x, x = exsC3 walkPieces t p := ⟨_, rfl⟩
  have hσAe : σA = eS + (1 + σc) := by rw [hσA, psh, hσc, heS]
  simp only [← hσc, ← heS, ← heIw, ← heSc, ← heC3] at layS htpi htl hlet hsub hins heq
  have hσAe' : 0 + eS + 1 + σc = σA := by rw [hσAe]; ring
  rw [hσAe'] at layS hsub hins
  rw [memTop_add, ← hir₀] at hsub
  obtain ⟨k, hk⟩ : ∃ k, k = len (memberList s) := ⟨_, rfl⟩
  obtain ⟨kc, hkc⟩ : ∃ x, x = len (memberList (insert (substs1 LAct t p) s)) := ⟨_, rfl⟩
  rw [← hk] at hins
  rw [← hkc] at heq
  simp only [zero_add] at heq
  -- the partial offsets are below `σA`
  have hσcD : σc ≤ 6 * D + 1 := by
    rw [hσc]; exact proSig_le htbl hP hWc htblN hWl hWp hcs (one_le_len_memberList_insert _ _) hcD
      (le_trans (le_of_add_eq' (c := 2 * SA + 47 * D + 2 * B + 52) (by ring)) hE) hΓ
  have heSA : eS = vecCw walkPieces t + exsSl Wc T t + 1 + eC3 + eSc := by rw [heS, heC3, heSc, exsSig]
  have heIwA : eIw = exsSl Wc T t + 1 + eC3 := by rw [heIw, heC3, exsIw]
  have hit₀A : eIw + eSc + 1 + 1 + σc ≤ σA + 1 := by
    rw [hσAe, heSA, heIwA]; exact le_of_add_eq' (c := vecCw walkPieces t) (by ring)
  have hilt₀A : eC3 + eSc + 1 + σc ≤ σA := by
    rw [hσAe, heSA]; exact le_of_add_eq' (c := vecCw walkPieces t + exsSl Wc T t + 1) (by ring)
  have hipt₀A : eSc + 1 + σc ≤ σA := by
    rw [hσAe, heSA]; exact le_of_add_eq' (c := vecCw walkPieces t + exsSl Wc T t + 1 + eC3) (by ring)
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ (proExs walkPieces Wl Wc W T s p t 0) := ⟨_, rfl⟩
  rw [← hΓ₁] at layC layS htpi htl hlet hsub hins heq
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 9 htbl hΓ pok
  have layC' : NodeLay walkPieces Wc T Γ₁ (fstIdx d') := by rw [hcfst]; exact Or.inl ⟨one_le_len_memberList_insert _ _, layC⟩
  -- the child
  obtain ⟨cok, cnd, csh, cgoal⟩ := hch Γ₁ hΓ₁f layC'
  obtain ⟨s', hs'⟩ : ∃ s', s' = shiftsV L' := ⟨_, rfl⟩
  obtain ⟨Γ₂, hΓ₂⟩ : ∃ Γ', Γ' = finalCtx Γ₁ L' := ⟨_, rfl⟩
  rw [← hΓ₂, ← hs', hcfst, ← hkc] at cgoal
  rw [← hs'] at csh
  have hΓ₂f : IsFormulaSet LAct Γ₂ := by rw [hΓ₂]; exact finalCtx_isFormulaSet 9 htbl hΓ₁f cok
  have heq₂ : neg LAct (eqFactB (^&(σc + s')) (^&(kc + 1 + s'))) ∈ Γ₂ := by
    rw [hΓ₂, hs']
    have := tr_fact cnd (isFormula_eqFactB (hf_ _) (hf_ _)) heq
    rwa [shiftIterV_eqFactB (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
  -- `postIns`
  have hsE : kc + 1 + s' + 3 ≤ E := by
    refine le_trans ?_ hE'
    calc kc + 1 + s' + 3 ≤ D + 1 + B + 3 := add_le_add (add_le_add (add_le_add (hkc ▸ hkcD) (le_refl 1)) csh) (le_refl 3)
      _ ≤ 2 * SA + 60 * D + 2 * B + 60 := le_of_add_eq' (c := 2 * SA + 59 * D + B + 56) (by ring)
  have hcE : σc + s' + 3 ≤ E := by
    refine le_trans ?_ hE'
    calc σc + s' + 3 ≤ (6 * D + 1) + B + 3 := add_le_add (add_le_add hσcD csh) (le_refl 3)
      _ ≤ 2 * SA + 60 * D + 2 * B + 60 := le_of_add_eq' (c := 2 * SA + 54 * D + B + 56) (by ring)
  obtain ⟨qok, qnd, qsh, -, qder, qfst, qdlen, qle⟩ := postIns_ok htbl hP hWp hΓ₂f hsE hcE cgoal heq₂
  obtain ⟨Γ₃, hΓ₃⟩ : ∃ Γ', Γ' = finalCtx Γ₂ (postIns W (kc + 1 + s') (σc + s') (dlen TAct d')) := ⟨_, rfl⟩
  rw [← hΓ₃] at qder qfst qdlen qle
  have hΓ₃f : IsFormulaSet LAct Γ₃ := by rw [hΓ₃]; exact finalCtx_isFormulaSet 8 htbl hΓ₂f qok
  have hΓ₃e : Γ₃ = finalCtx Γ₁ (appendV L' (postIns W (kc + 1 + s') (σc + s') (dlen TAct d'))) := by
    rw [finalCtx_appendV, ← hΓ₂, hΓ₃]
  have hnd₂ : NoDrop' (appendV L' (postIns W (kc + 1 + s') (σc + s') (dlen TAct d'))) := noDrop'_appendV cnd qnd
  have hsh₂ : shiftsV (appendV L' (postIns W (kc + 1 + s') (σc + s') (dlen TAct d'))) = s' + 2 := by
    rw [shiftsV_appendV, qsh, hs']
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = σA + s' + 2 := ⟨_, rfl⟩
  have layS₃ : Layout walkPieces Wc T Γ₃ s τ := by
    rw [hΓ₃e, hτ]; have := layS.transport hnd₂; rwa [hsh₂, ← add_assoc] at this
  have htpi₃ : neg LAct (tPiFact (𝟎 : V) (^&(eIw + eSc + 1 + 1 + σc + s' + 2))) ∈ Γ₃ := by
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_tPiFact h0_ (hf_ _)) htpi
    rw [hsh₂, shiftIterV_tPiFact h0_ (hf_ _), termShiftIterV_qqZero, termShiftIterV_fvar] at this
    rwa [show eIw + eSc + 1 + 1 + σc + (s' + 2) = eIw + eSc + 1 + 1 + σc + s' + 2 by ring] at this
  have htl₃ : neg LAct (tlenFact (^&(eC3 + eSc + 1 + σc + s' + 2)) (^&(eIw + eSc + 1 + 1 + σc + s' + 2))) ∈ Γ₃ := by
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_tlenFact (hf_ _) (hf_ _)) htl
    rw [hsh₂, shiftIterV_tlenFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show eC3 + eSc + 1 + σc + (s' + 2) = eC3 + eSc + 1 + σc + s' + 2 by ring,
      show eIw + eSc + 1 + 1 + σc + (s' + 2) = eIw + eSc + 1 + 1 + σc + s' + 2 by ring] at this
  have hlet₃ : neg LAct (leFact (^&(eC3 + eSc + 1 + σc + s' + 2)) (bnum (termLen LAct t))) ∈ Γ₃ := by
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_leFact (hf_ _) (isSemiterm_bnum_LAct 0 _)) hlet
    rw [hsh₂, shiftIterV_leFact (hf_ _) (isSemiterm_bnum_LAct 0 _), termShiftIterV_fvar, termShiftIterV_bnum'] at this
    rwa [show eC3 + eSc + 1 + σc + (s' + 2) = eC3 + eSc + 1 + σc + s' + 2 by ring] at this
  have hsub₃ : neg LAct (substs1Fact (^&(eSc + 1 + σc + s' + 2)) (^&(eIw + eSc + 1 + 1 + σc + s' + 2)) (^&(ir₀ + τ + 1))) ∈ Γ₃ := by
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_substs1Fact (hf_ _) (hf_ _) (hf_ _)) hsub
    rw [hsh₂, shiftIterV_substs1Fact (hf_ _) (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show eSc + 1 + σc + (s' + 2) = eSc + 1 + σc + s' + 2 by ring,
      show eIw + eSc + 1 + 1 + σc + (s' + 2) = eIw + eSc + 1 + 1 + σc + s' + 2 by ring,
      show ir₀ + σA + 1 + (s' + 2) = ir₀ + τ + 1 by rw [hτ]; ring] at this
  have hins₃ : neg LAct (insFact (^&(σc + s' + 2)) (^&(eSc + 1 + σc + s' + 2)) (^&(τ + (k + 1)))) ∈ Γ₃ := by
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_insFact (hf_ _) (hf_ _) (hf_ _)) hins
    rw [hsh₂, shiftIterV_insFact (hf_ _) (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show σc + (s' + 2) = σc + s' + 2 by ring, show eSc + 1 + σc + (s' + 2) = eSc + 1 + σc + s' + 2 by ring,
      show σA + (k + 1) + (s' + 2) = τ + (k + 1) by rw [hτ]; ring] at this
  have hexs₃ : neg LAct (exsFact (^&(ir₀ + τ)) (^&(ir₀ + τ + 1))) ∈ Γ₃ := by
    have h1 := tr_fact pnd (isFormula_exsFact (hf_ _) (hf_ _)) hexs
    rw [← hσA, shiftIterV_exsFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, ← hΓ₁] at h1
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_exsFact (hf_ _) (hf_ _)) h1
    rw [hsh₂, shiftIterV_exsFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show ir₀ + σA + (s' + 2) = ir₀ + τ by rw [hτ]; ring, show ir₀ + 1 + σA + (s' + 2) = ir₀ + τ + 1 by rw [hτ]; ring] at this
  have hmr₃ : neg LAct (memFact (^&(ir₀ + τ)) (^&(τ + (k + 1)))) ∈ Γ₃ := by
    have h1 := tr_fact pnd (isFormula_memFact (hf_ _) (hf_ _)) hmr
    rw [← hσA, shiftIterV_memFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, ← hΓ₁] at h1
    rw [hΓ₃e]
    have := tr_fact hnd₂ (isFormula_memFact (hf_ _) (hf_ _)) h1
    rw [hsh₂, shiftIterV_memFact (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar] at this
    rwa [show ir₀ + σA + (s' + 2) = ir₀ + τ by rw [hτ]; ring,
      show len (memberList s) + 1 + σA + (s' + 2) = τ + (k + 1) by rw [hτ, hk]; ring] at this
  -- the node's caps
  have hτD : τ ≤ SA + B + 2 := by rw [hτ]; exact add_le_add (add_le_add hσAB csh) (le_refl 2)
  have his : τ + (k + 1) + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc τ + (k + 1) + 2 ≤ (SA + B + 2) + (D + 1) + 2 := add_le_add (add_le_add hτD (add_le_add (hk ▸ hkD) (le_refl 1))) (le_refl 2)
      _ ≤ 2 * SA + 60 * D + 2 * B + 60 := le_of_add_eq' (c := SA + 59 * D + B + 55) (by ring)
  have hir : ir₀ + τ + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc ir₀ + τ + 2 ≤ (6 * D + 1) + (SA + B + 2) + 2 := add_le_add (add_le_add hir₀D hτD) (le_refl 2)
      _ ≤ 2 * SA + 60 * D + 2 * B + 60 := le_of_add_eq' (c := SA + 54 * D + B + 55) (by ring)
  have hip : ir₀ + τ + 1 + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc ir₀ + τ + 1 + 2 ≤ (6 * D + 1) + (SA + B + 2) + 1 + 2 := add_le_add (add_le_add (add_le_add hir₀D hτD) (le_refl 1)) (le_refl 2)
      _ ≤ 2 * SA + 60 * D + 2 * B + 60 := le_of_add_eq' (c := SA + 54 * D + B + 54) (by ring)
  have hit : eIw + eSc + 1 + 1 + σc + s' + 2 + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc eIw + eSc + 1 + 1 + σc + s' + 2 + 2 ≤ (SA + 1) + B + 2 + 2 :=
          add_le_add (add_le_add (add_le_add (le_trans hit₀A (add_le_add hσAB (le_refl 1))) csh) (le_refl 2)) (le_refl 2)
      _ ≤ 2 * SA + 60 * D + 2 * B + 60 := le_of_add_eq' (c := SA + 60 * D + B + 55) (by ring)
  have hipt : eSc + 1 + σc + s' + 2 + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc eSc + 1 + σc + s' + 2 + 2 ≤ SA + B + 2 + 2 := add_le_add (add_le_add (add_le_add (le_trans hipt₀A hσAB) csh) (le_refl 2)) (le_refl 2)
      _ ≤ 2 * SA + 60 * D + 2 * B + 60 := le_of_add_eq' (c := SA + 60 * D + B + 56) (by ring)
  have hic : σc + s' + 2 + 2 ≤ E := by
    refine le_trans ?_ hE'
    calc σc + s' + 2 + 2 ≤ (6 * D + 1) + B + 2 + 2 := add_le_add (add_le_add (add_le_add hσcD csh) (le_refl 2)) (le_refl 2)
      _ ≤ 2 * SA + 60 * D + 2 * B + 60 := le_of_add_eq' (c := 2 * SA + 54 * D + B + 55) (by ring)
  have hid : (1 : V) + 2 ≤ E := le_trans (le_of_add_eq' (c := 2 * SA + 60 * D + 2 * B + 57) (by ring)) hE'
  have hT : τ + (eC3 + eSc + 1 + σc + s' + 2) + 0 + 10 ≤ E := by
    refine le_trans ?_ hE'
    calc τ + (eC3 + eSc + 1 + σc + s' + 2) + 0 + 10 ≤ (SA + B + 2) + (SA + B + 2) + 0 + 10 :=
          add_le_add (add_le_add (add_le_add hτD (add_le_add (add_le_add (le_trans hilt₀A hσAB) csh) (le_refl 2))) (le_refl 0)) (le_refl 10)
      _ ≤ 2 * SA + 60 * D + 2 * B + 60 := le_of_add_eq' (c := 60 * D + 46) (by ring)
  have hn : 18 * ‖dlen TAct (exsIntro s p t d')‖ + 7 ≤ E := by
    have hn1 : ‖dlen TAct (exsIntro s p t d')‖ ≤ 3 * D + 1 := by
      refine le_trans (length_le _) ?_
      rw [hdl]
      exact le_trans (add_le_add (add_le_add (add_le_add hsD htD) hmD) (le_refl 1)) (le_of_add_eq' (c := 0) (by ring))
    refine le_trans ?_ hE'
    calc 18 * ‖dlen TAct (exsIntro s p t d')‖ + 7 ≤ 18 * (3 * D + 1) + 7 :=
          add_le_add (mul_le_mul_of_nonneg_left hn1 zero_le) (le_refl 7)
      _ ≤ 2 * SA + 60 * D + 2 * B + 60 := le_of_add_eq' (c := 2 * SA + 6 * D + 2 * B + 35) (by ring)
  have hLn : setLen LAct s + termLen LAct t + dlen TAct d' + 1 ≤ dlen TAct (exsIntro s p t d') := by rw [hdl]
  -- the node
  obtain ⟨nok, nnd, nsh, -, ngoal⟩ := nodeExs_ok (E := E) (is := τ + (k + 1)) (il := τ) (ir := ir₀ + τ) (ip := ir₀ + τ + 1)
    (it := eIw + eSc + 1 + 1 + σc + s' + 2) (ipt := eSc + 1 + σc + s' + 2) (ic := σc + s' + 2) (id := 1)
    (ilt := eC3 + eSc + 1 + σc + s' + 2) (in₁ := 0) (L := setLen LAct s) (Lt := termLen LAct t) (m₁ := dlen TAct d')
    (n := dlen TAct (exsIntro s p t d'))
    htbl hP.frag2Table hW₂ htblN hΓ₃f his hir hip hit hipt hic hid hT hn hLn hexs₃ hmr₃ htpi₃ qfst hsub₃ hins₃ qder qdlen qle
    htl₃ hlet₃ (by have := layS₃.2.1; rwa [← hk] at this) layS₃.2.2
  -- assembly
  unfold vExs
  rw [← hσc, ← heS, ← heIw, ← heSc, ← heC3, ← hs', ← hk, ← hkc]
  rw [show eS + (1 + σc) + s' + 2 = τ by rw [hτ, hσAe]]
  rw [memTop_add, ← hir₀]
  have ok₃ : ListOK tbl E ((9 : ℕ) : V) Γ₂ (appendV (postIns W (kc + 1 + s') (σc + s') (dlen TAct d'))
      (nodeExs W₂ T (τ + (k + 1)) τ (ir₀ + τ) (ir₀ + τ + 1) (eIw + eSc + 1 + 1 + σc + s' + 2) (eSc + 1 + σc + s' + 2)
        (σc + s' + 2) 1 (eC3 + eSc + 1 + σc + s' + 2) 0 (setLen LAct s) (termLen LAct t) (dlen TAct d')
        (dlen TAct (exsIntro s p t d')))) :=
    listOK_appendV (qok.mono h89) (by rw [← hΓ₃]; exact nok)
  have ok₂ := listOK_appendV cok (by rw [← hΓ₂]; exact ok₃)
  have ok₁ := listOK_appendV pok (by rw [← hΓ₁]; exact ok₂)
  refine ⟨ok₁, noDrop'_appendV pnd (noDrop'_appendV cnd (noDrop'_appendV qnd nnd)), ?_, ?_⟩
  · rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, ← hσA, ← hs', qsh, nsh]
    calc σA + (s' + (2 + 1)) ≤ SA + (B + (2 + 1)) := add_le_add hσAB (add_le_add csh (le_refl _))
      _ = SA + B + 3 := by ring
  · rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, ← hσA, ← hs', qsh, nsh,
      finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂, ← hΓ₃,
      show k + 1 + (σA + (s' + (2 + 1))) = τ + (k + 1) + 1 by rw [hτ]; ring]
    exact ngoal

end exsOk

/-! ### 8.9 The node invariant, glued by `Derivation.induction1 𝚷`

`verifyGraph'_ok`: every list of `VerifyGraph'` at a node laid out at `0` is applicable, cut-admitting, has at most
`Cs · (dlen ρ)^6` eigenvariables, and leaves the node's goal fact. The DEGREE 6 is forced by the per-node shift bounds
available today (`Prologue.shiftsV_proAll_le`/`_proExs_le`, quintic in a size `D` that is only GLOBALLY bounded by
`dlen ρ`): with per-node terms `≤ c·(dlen ρ)^5` the recursion closes at `Cs·(dlen ρ)^6` via
`(y + m)^6 ≥ y^6 + m·(y + m)^5`. It drops by one for every degree the prologue bounds lose (cubic bounds ⇒ degree 4;
LOCAL bounds ⇒ degree 3). Powers are written as explicit products (`p5`, `p6`) so that the motive stays `definability`-friendly. -/

section glue

/-- `x^5` and `x^6` as explicit products (definability-friendly). -/
def p5 (x : V) : V := x * x * x * x * x
def p6 (x : V) : V := x * x * x * x * x * x

lemma p6_eq (x : V) : p6 x = x * p5 x := by simp only [p5, p6]; ring

lemma p5_mono {a b : V} (h : a ≤ b) : p5 a ≤ p5 b := by
  simp only [p5]
  exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h h zero_le zero_le) h zero_le zero_le) h zero_le zero_le) h zero_le zero_le

lemma p6_mono {a b : V} (h : a ≤ b) : p6 a ≤ p6 b := by
  simp only [p6]
  exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h h zero_le zero_le) h zero_le zero_le) h zero_le zero_le)
    h zero_le zero_le) h zero_le zero_le

lemma le_p5_self {d : V} (hd : 1 ≤ d) : d ≤ p5 d := by
  simp only [p5]
  calc d = 1 * 1 * 1 * 1 * d := by ring
    _ ≤ d * d * d * d * d :=
      mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul hd hd zero_le zero_le) hd zero_le zero_le) hd zero_le zero_le) (le_refl d)
        zero_le zero_le

lemma one_le_p5 {d : V} (hd : 1 ≤ d) : 1 ≤ p5 d := le_trans hd (le_p5_self hd)

lemma le_p6_self {d : V} (hd : 1 ≤ d) : d ≤ p6 d := by
  rw [p6_eq]; calc d = d * 1 := by ring
    _ ≤ d * p5 d := mul_le_mul_of_nonneg_left (one_le_p5 hd) zero_le

lemma p5_le_p6 {d : V} (hd : 1 ≤ d) : p5 d ≤ p6 d := by
  rw [p6_eq]; calc p5 d = 1 * p5 d := by ring
    _ ≤ d * p5 d := mul_le_mul_of_nonneg_right hd zero_le

/-- `(y + m)^6 ≥ y^6 + m·(y + m)^5`. -/
lemma p6_split (y m : V) : p6 y + m * p5 (y + m) ≤ p6 (y + m) := by
  rw [p6_eq (y + m), p6_eq y, add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (p5_mono le_self_add) zero_le) (le_refl _)

lemma p6_add_le (y₁ y₂ : V) : p6 y₁ + p6 y₂ ≤ p6 (y₁ + y₂) := by
  simp only [p6]
  exact le_of_add_eq' (c := 6 * (y₁ * y₁ * y₁ * y₁ * y₁) * y₂ + 15 * (y₁ * y₁ * y₁ * y₁) * (y₂ * y₂) +
    20 * (y₁ * y₁ * y₁) * (y₂ * y₂ * y₂) + 15 * (y₁ * y₁) * (y₂ * y₂ * y₂ * y₂) + 6 * y₁ * (y₂ * y₂ * y₂ * y₂ * y₂)) (by ring)

/-- The one-child recursion step: `X + Cs·y^6 ≤ Cs·d^6` when `d = y + m`, `m ≥ 1`, `X ≤ Cs·d^5`. -/
lemma rec1 {Cs X y m d : V} (hm : 1 ≤ m) (hd : d = y + m) (hX : X ≤ Cs * p5 d) : X + Cs * p6 y ≤ Cs * p6 d := by
  have h := p6_split y m
  rw [← hd] at h
  calc X + Cs * p6 y ≤ Cs * p5 d + Cs * p6 y := add_le_add hX (le_refl _)
    _ = Cs * (p6 y + 1 * p5 d) := by ring
    _ ≤ Cs * (p6 y + m * p5 d) := mul_le_mul_of_nonneg_left (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hm zero_le)) zero_le
    _ ≤ Cs * p6 d := mul_le_mul_of_nonneg_left h zero_le

/-- The two-children recursion step. -/
lemma rec2 {Cs X y₁ y₂ m d : V} (hm : 1 ≤ m) (hd : d = y₁ + y₂ + m) (hX : X ≤ Cs * p5 d) :
    X + Cs * p6 y₁ + Cs * p6 y₂ ≤ Cs * p6 d := by
  have h := rec1 (Cs := Cs) (X := X) (y := y₁ + y₂) hm hd hX
  calc X + Cs * p6 y₁ + Cs * p6 y₂ = X + Cs * (p6 y₁ + p6 y₂) := by ring
    _ ≤ X + Cs * p6 (y₁ + y₂) := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (p6_add_le _ _) zero_le)
    _ ≤ Cs * p6 d := h

/-- A linear cap sits under `Cs·d^5` for `d ≥ 1` and `Cs ≥ a + b`. -/
lemma lin_le_p5 {a b Cs d : V} (hd : 1 ≤ d) (hab : a + b ≤ Cs) : a * d + b ≤ Cs * p5 d := by
  calc a * d + b ≤ a * p5 d + b * p5 d := add_le_add (mul_le_mul_of_nonneg_left (le_p5_self hd) zero_le)
        (le_mul_of_one_le_right zero_le (one_le_p5 hd))
    _ = (a + b) * p5 d := by ring
    _ ≤ Cs * p5 d := mul_le_mul_of_nonneg_right hab zero_le

end glue

section glueMain

lemma cube_le_p6 {e : V} (he : 1 ≤ e) : e * e * e ≤ p6 e := by
  simp only [p6]
  calc e * e * e = e * e * e * 1 * 1 * 1 := by ring
    _ ≤ e * e * e * e * e * e :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left he zero_le) he zero_le zero_le) he zero_le zero_le

lemma pow5_eq_p5 (x : V) : x ^ 5 = p5 x := by simp only [p5]; ring

lemma p5_two_mul (x : V) : p5 (2 * x) = 32 * p5 x := by simp only [p5]; ring

lemma p5_succ_le {d : V} (hd : 1 ≤ d) : p5 (d + 1) ≤ 32 * p5 d := by
  rw [← p5_two_mul]
  exact p5_mono (by calc d + 1 ≤ d + d := add_le_add (le_refl d) hd
    _ = 2 * d := by ring)

lemma capE {Ckv E e X a : V} (hE : Ckv * p6 e ≤ E) (he : 1 ≤ e) (ha : a ≤ Ckv) (hX : X ≤ a * e) : X ≤ E :=
  le_trans hX (le_trans (mul_le_mul ha (le_p6_self he) zero_le zero_le) hE)

lemma capE6 {Ckv E e X a : V} (hE : Ckv * p6 e ≤ E) (ha : a ≤ Ckv) (hX : X ≤ a * p6 e) : X ≤ E :=
  le_trans hX (le_trans (mul_le_mul_of_nonneg_right ha zero_le) hE)

/-- `a·D + b·‖D‖ + c ≤ (a + b + c)·(D + 1)`. -/
lemma lin_cap (a b c D : V) : a * D + b * ‖D‖ + c ≤ (a + b + c) * (D + 1) := by
  calc a * D + b * ‖D‖ + c ≤ a * D + b * D + c :=
        add_le_add (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (length_le D) zero_le)) (le_refl c)
    _ ≤ (a + b + c) * (D + 1) := le_of_add_eq' (c := c * D + a + b) (by ring)

/-- `Cs·y^6 ≤ Cs·d^6` for `y ≤ d`. -/
lemma child_bound {Cs y d : V} (h : y ≤ d) : Cs * p6 y ≤ Cs * p6 d := mul_le_mul_of_nonneg_left (p6_mono h) zero_le

/-- The cubic prologue caps: `2·(a·b)·c ≤ 2·ka·kb·kc·e^6` for `a ≤ ka·e`, … -/
lemma quad_cap {e a b c ka kb kc : V} (he : 1 ≤ e) (ha : a ≤ ka * e) (hb : b ≤ kb * e) (hc : c ≤ kc * e) :
    2 * (a * b) * c ≤ 2 * ka * kb * kc * p6 e := by
  calc 2 * (a * b) * c ≤ 2 * (ka * e * (kb * e)) * (kc * e) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul ha hb zero_le zero_le) zero_le) hc zero_le zero_le
    _ = 2 * ka * kb * kc * (e * e * e) := by ring
    _ ≤ 2 * ka * kb * kc * p6 e := mul_le_mul_of_nonneg_left (cube_le_p6 he) zero_le

/-- The leaf shift `1 ≤ Cs·d^6`. -/
lemma one_le_Cs_p6 {Cs d : V} (hCs : 1 ≤ Cs) (hd : 1 ≤ d) : 1 ≤ Cs * p6 d :=
  le_trans hCs (le_mul_of_one_le_right zero_le (le_trans hd (le_p6_self hd)))

/-- The uniform prologue shift bound used for `all`/`exs`: `450·(2(d+1))^5 = 14400·(d+1)^5`. -/
lemma proSA_le_p6 {d : V} (hd : 1 ≤ d) : 450 * p5 (2 * (d + 1)) ≤ 14400 * p6 (d + 1) := by
  rw [p5_two_mul]
  calc 450 * (32 * p5 (d + 1)) = 14400 * p5 (d + 1) := by ring
    _ ≤ 14400 * p6 (d + 1) := mul_le_mul_of_nonneg_left (p5_le_p6 le_add_self) zero_le

lemma proSA_add_le_p5 {Csv d : V} (hd : 1 ≤ d) (hCs : 460803 ≤ Csv) : 450 * p5 (2 * (d + 1)) + 3 ≤ Csv * p5 d := by
  rw [p5_two_mul]
  have h1 : p5 (d + 1) ≤ 32 * p5 d := p5_succ_le hd
  calc 450 * (32 * p5 (d + 1)) + 3 ≤ 450 * (32 * (32 * p5 d)) + 3 * p5 d :=
        add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 zero_le) zero_le)
          (le_mul_of_one_le_right zero_le (one_le_p5 hd))
    _ = 460803 * p5 d := by ring
    _ ≤ Csv * p5 d := mul_le_mul_of_nonneg_right hCs zero_le

set_option maxHeartbeats 20000000 in
/-- **The node invariant** (`DESIGN_fragments.md` §6.3 for `VerifyGraph'`): at a node laid out at offset `0`, every
verification list is applicable at cap `9`, cut-admitting, has at most `Cs·(dlen ρ)^6` eigenvariables, and leaves the
node's goal fact at `&(k + 1 + shiftsV L)`. The E-room is `Ck·(dlen ρ + 1)^6 ≤ E`. The degree is 6, forced by the
quintic `shiftsV_proAll_le`/`shiftsV_proExs_le` (see the section docstring). -/
theorem verifyGraph'_ok : ∃ Cs Ck : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {tbl N N' B' Ww Wl Wc W₁ W₂ W T A Cv E ρ : V},
    TableOK tbl N → ProTable tbl → NumTableOK T N' B' → Ww = walkPieces → Wl = layoutPieces → Wc = certPieces →
    W₁ = frag1Pieces → W₂ = frag2Pieces → W = proPieces → AxmTableOK tbl E Ww A Cv → Derivation TAct ρ →
    ((Ck : ℕ) : V) * p6 (dlen TAct ρ + 1) ≤ E →
    ∀ L Γ : V, VerifyGraph' Ww Wl Wc W₁ W₂ W T A ρ L → IsFormulaSet LAct Γ → NodeLay Ww Wc T Γ (fstIdx ρ) →
      ListOK tbl E ((9 : ℕ) : V) Γ L ∧ NoDrop' L ∧ shiftsV L ≤ ((Cs : ℕ) : V) * p6 (dlen TAct ρ) ∧
      neg LAct (goalFact (^&(len (memberList (fstIdx ρ)) + 1 + shiftsV L)) (bnum (dlen TAct ρ))) ∈ finalCtx Γ L := by
  refine ⟨500000, 2500000, fun V _ _ tbl N N' B' Ww Wl Wc W₁ W₂ W T A Cv E ρ htbl hP htblN hWw hWl hWc hW₁ hW₂ hWp hA hd ↦ ?_⟩
  obtain ⟨Csv, hCsv⟩ : ∃ x : V, x = ((500000 : ℕ) : V) := ⟨_, rfl⟩
  obtain ⟨Ckv, hCkv⟩ : ∃ x : V, x = ((2500000 : ℕ) : V) := ⟨_, rfl⟩
  rw [← hCsv, ← hCkv]
  have hCs1 : (1 : V) ≤ Csv := by rw [hCsv]; exact_mod_cast (by norm_num : 1 ≤ 500000)
  have hCs' : (460803 : V) ≤ Csv := by rw [hCsv]; exact_mod_cast (by norm_num : 460803 ≤ 500000)
  have hCk : ∀ a : ℕ, a ≤ 2500000 → ((a : ℕ) : V) ≤ Ckv := fun a ha ↦ by rw [hCkv]; exact_mod_cast ha
  have hCsCk : 5 * Csv ≤ Ckv := by rw [hCsv, hCkv]; exact_mod_cast (by norm_num : 5 * 500000 ≤ 2500000)
  subst hWw
  apply Derivation.induction1 𝚷 (T := TAct)
    (P := fun ρ ↦ Ckv * p6 (dlen TAct ρ + 1) ≤ E → ∀ L Γ : V, VerifyGraph' walkPieces Wl Wc W₁ W₂ W T A ρ L →
      IsFormulaSet LAct Γ → NodeLay walkPieces Wc T Γ (fstIdx ρ) →
      ListOK tbl E ((9 : ℕ) : V) Γ L ∧ NoDrop' L ∧ shiftsV L ≤ Csv * p6 (dlen TAct ρ) ∧
      neg LAct (goalFact (^&(len (memberList (fstIdx ρ)) + 1 + shiftsV L)) (bnum (dlen TAct ρ))) ∈ finalCtx Γ L)
    (by simp only [VerifyGraph', p6]; definability) hd
  · -- axL
    intro s hs p hp hnp hE L Γ hL hΓ hLay
    rw [VerifyGraph'.axL_iff] at hL; subst hL
    rw [fstIdx_axL] at hLay ⊢
    have hD : Derivation TAct (axL s p) := Derivation.axL hs hp hnp
    have hd1 : 1 ≤ dlen TAct (axL s p) := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (axL s p) := by have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_axL] at this
    have hkD : len (memberList s) ≤ dlen TAct (axL s p) := le_trans (len_memberList_le_setLen hs) hsD
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (axL s p) := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hkD
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hn : 18 * ‖setLen LAct s + 1‖ + 7 ≤ 43 * (d + 1) := by
      have h1 : ‖setLen LAct s + 1‖ ≤ d + 1 := le_trans (length_le _) (add_le_add hsD (le_refl 1))
      calc 18 * ‖setLen LAct s + 1‖ + 7 ≤ 18 * (d + 1) + 7 := add_le_add (mul_le_mul_of_nonneg_left h1 zero_le) (le_refl 7)
        _ ≤ 43 * (d + 1) := le_of_add_eq' (c := 25 * d + 18) (by ring)
    obtain ⟨ok, nd, sh, goal⟩ := vAxL_ok (D := d) htbl hP htblN hWc hW₁ hs hp hnp hsD
      (capE hE he1 (hCk 39 (by norm_num)) (by
        calc 13 * d + 18 * ‖d‖ + 8 ≤ (13 + 18 + 8) * (d + 1) := lin_cap 13 18 8 d
          _ = ((39 : ℕ) : V) * (d + 1) := by push_cast; ring))
      (capE hE he1 (hCk 11 (by norm_num)) (by push_cast; exact le_of_add_eq' (c := 3 * d + 8) (by ring)))
      (capE hE he1 (hCk 3 (by norm_num)) (by
        push_cast; exact le_trans (add_le_add hkD (le_refl 3)) (le_of_add_eq' (c := 2 * d) (by ring))))
      (capE hE he1 (hCk 43 (by norm_num)) (by push_cast; exact hn))
      hΓ hLay.layout
    refine ⟨ok, nd, ?_, by rw [sh]; exact goal⟩
    rw [sh, ← hdd]
    exact one_le_Cs_p6 hCs1 hd1
  · -- verumIntro
    intro s hs hv hE L Γ hL hΓ hLay
    rw [VerifyGraph'.verumIntro_iff] at hL; subst hL
    rw [fstIdx_verumIntro] at hLay ⊢
    have hD : Derivation TAct (verumIntro s) := Derivation.verumIntro hs hv
    have hd1 : 1 ≤ dlen TAct (verumIntro s) := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (verumIntro s) := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_verumIntro] at this
    have hkD : len (memberList s) ≤ dlen TAct (verumIntro s) := le_trans (len_memberList_le_setLen hs) hsD
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (verumIntro s) := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hkD
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hn : 18 * ‖setLen LAct s + 1‖ + 7 ≤ 43 * (d + 1) := by
      have h1 : ‖setLen LAct s + 1‖ ≤ d + 1 := le_trans (length_le _) (add_le_add hsD (le_refl 1))
      calc 18 * ‖setLen LAct s + 1‖ + 7 ≤ 18 * (d + 1) + 7 := add_le_add (mul_le_mul_of_nonneg_left h1 zero_le) (le_refl 7)
        _ ≤ 43 * (d + 1) := le_of_add_eq' (c := 25 * d + 18) (by ring)
    obtain ⟨ok, nd, sh, goal⟩ := vVerum_ok (D := d) htbl hP htblN hWc hW₁ hs hv hsD
      (capE hE he1 (hCk 9 (by norm_num)) (by push_cast; exact le_of_add_eq' (c := 3 * d + 6) (by ring)))
      (capE hE he1 (hCk 3 (by norm_num)) (by
        push_cast; exact le_trans (add_le_add hkD (le_refl 3)) (le_of_add_eq' (c := 2 * d) (by ring))))
      (capE hE he1 (hCk 43 (by norm_num)) (by push_cast; exact hn))
      hΓ hLay.layout
    refine ⟨ok, nd, ?_, by rw [sh]; exact goal⟩
    rw [sh, ← hdd]
    exact one_le_Cs_p6 hCs1 hd1
  · -- andIntro
    intro s hs p q dp dq hpq hdp hdq ih₁ ih₂ hE L Γ hL hΓ hLay
    rw [VerifyGraph'.andIntro_iff] at hL
    obtain ⟨L₁, -, hL₁, L₂, -, hL₂, rfl⟩ := hL
    rw [fstIdx_andIntro] at hLay ⊢
    have hD : Derivation TAct (andIntro s p q dp dq) := Derivation.andIntro hpq hdp hdq
    have hd1 : 1 ≤ dlen TAct (andIntro s p q dp dq) := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (andIntro s p q dp dq) := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_andIntro] at this
    have hc₁D := setLen_child_le_dlen_andIntro_left hD
    have hc₂D := setLen_child_le_dlen_andIntro_right hD
    have hy₁ := dlen_dp_succ_le_andIntro hD
    have hy₂ := dlen_dq_succ_le_andIntro hD
    have hdl := dlen_andIntro hD
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (andIntro s p q dp dq) := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hc₁D hc₂D hy₁ hy₂ hdl
    obtain ⟨y₁, hy₁d⟩ : ∃ x, x = dlen TAct dp := ⟨_, rfl⟩
    obtain ⟨y₂, hy₂d⟩ : ∃ x, x = dlen TAct dq := ⟨_, rfl⟩
    rw [← hy₁d] at hy₁ hdl; rw [← hy₂d] at hy₂ hdl
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hm₁D : y₁ ≤ d := le_trans le_self_add hy₁
    have hm₂D : y₂ ≤ d := le_trans le_self_add hy₂
    have hch₁ : ChildOK tbl Wc T E L₁ dp (Csv * p6 y₁) := fun Γ' hΓ' hLay' ↦ by
      rw [hy₁d]
      exact ih₁ (le_trans (child_bound (by rw [← hy₁d]; exact le_trans hy₁ le_self_add)) hE) L₁ Γ' hL₁ hΓ' hLay'
    have hch₂ : ChildOK tbl Wc T E L₂ dq (Csv * p6 y₂) := fun Γ' hΓ' hLay' ↦ by
      rw [hy₂d]
      exact ih₂ (le_trans (child_bound (by rw [← hy₂d]; exact le_trans hy₂ le_self_add)) hE) L₂ Γ' hL₂ hΓ' hLay'
    have hlin : 60 * d + 18 * ‖d‖ + 60 ≤ 138 * p6 (d + 1) := by
      calc 60 * d + 18 * ‖d‖ + 60 ≤ (60 + 18 + 60) * (d + 1) := lin_cap 60 18 60 d
        _ = 138 * (d + 1) := by ring
        _ ≤ 138 * p6 (d + 1) := mul_le_mul_of_nonneg_left (le_p6_self he1) zero_le
    have h138 : (138 : V) ≤ 2 * Csv := by rw [hCsv]; exact_mod_cast (by norm_num : 138 ≤ 2 * 500000)
    obtain ⟨ok, nd, sh, goal⟩ := vAnd_ok (D := d) htbl hP htblN hWl hWc hWp hW₁ hs hpq hdp hdq hsD hc₁D hc₂D
      (by rw [← hy₁d]; exact hm₁D) (by rw [← hy₂d]; exact hm₂D)
      (capE6 hE hCsCk (by
        calc 60 * d + 18 * ‖d‖ + Csv * p6 y₁ + 2 * (Csv * p6 y₂) + 60
            = (60 * d + 18 * ‖d‖ + 60) + Csv * p6 y₁ + 2 * (Csv * p6 y₂) := by ring
          _ ≤ 138 * p6 (d + 1) + Csv * p6 (d + 1) + 2 * (Csv * p6 (d + 1)) :=
              add_le_add (add_le_add hlin (child_bound (le_trans hm₁D le_self_add)))
                (mul_le_mul_of_nonneg_left (child_bound (le_trans hm₂D le_self_add)) zero_le)
          _ = (138 + 3 * Csv) * p6 (d + 1) := by ring
          _ ≤ (2 * Csv + 3 * Csv) * p6 (d + 1) := mul_le_mul_of_nonneg_right (add_le_add h138 (le_refl _)) zero_le
          _ = 5 * Csv * p6 (d + 1) := by ring))
      hΓ hLay hch₁ hch₂
    refine ⟨ok, nd, ?_, goal⟩
    rw [← hdd]
    refine le_trans sh ?_
    have hdeq : d = y₁ + y₂ + (setLen LAct s + 1) := by rw [hdl]; ring
    have hX : 12 * d + 9 ≤ Csv * p5 d := lin_le_p5 hd1 (by
      rw [hCsv]; exact_mod_cast (by norm_num : 12 + 9 ≤ 500000))
    calc 12 * d + Csv * p6 y₁ + Csv * p6 y₂ + 9 = (12 * d + 9) + Csv * p6 y₁ + Csv * p6 y₂ := by ring
      _ ≤ Csv * p6 d := rec2 le_add_self hdeq hX
  · -- orIntro
    intro s hs p q d' hpq hd' ih hE L Γ hL hΓ hLay
    rw [VerifyGraph'.orIntro_iff] at hL
    obtain ⟨L', -, hL', rfl⟩ := hL
    rw [fstIdx_orIntro] at hLay ⊢
    have hD : Derivation TAct (orIntro s p q d') := Derivation.orIntro hpq hd'
    have hd1 : 1 ≤ dlen TAct (orIntro s p q d') := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (orIntro s p q d') := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_orIntro] at this
    have hcD := setLen_child_le_dlen_orIntro hD
    have hy := dlen_d_succ_le_orIntro hD
    have hdl := dlen_orIntro hD
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (orIntro s p q d') := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hcD hy hdl
    obtain ⟨y, hyd⟩ : ∃ x, x = dlen TAct d' := ⟨_, rfl⟩
    rw [← hyd] at hy hdl
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hmD : y ≤ d := le_trans le_self_add hy
    have hch : ChildOK tbl Wc T E L' d' (Csv * p6 y) := fun Γ' hΓ' hLay' ↦ by
      rw [hyd]
      exact ih (le_trans (child_bound (by rw [← hyd]; exact le_trans hy le_self_add)) hE) L' Γ' hL' hΓ' hLay'
    have hlin : 40 * d + 18 * ‖d‖ + 40 ≤ 98 * p6 (d + 1) := by
      calc 40 * d + 18 * ‖d‖ + 40 ≤ (40 + 18 + 40) * (d + 1) := lin_cap 40 18 40 d
        _ = 98 * (d + 1) := by ring
        _ ≤ 98 * p6 (d + 1) := mul_le_mul_of_nonneg_left (le_p6_self he1) zero_le
    have h98 : (98 : V) ≤ 4 * Csv := by rw [hCsv]; exact_mod_cast (by norm_num : 98 ≤ 4 * 500000)
    obtain ⟨ok, nd, sh, goal⟩ := vOr_ok (D := d) htbl hP htblN hWl hWc hWp hW₁ hs hpq hd' hsD hcD (by rw [← hyd]; exact hmD)
      (capE6 hE hCsCk (by
        calc 40 * d + 18 * ‖d‖ + Csv * p6 y + 40 = (40 * d + 18 * ‖d‖ + 40) + Csv * p6 y := by ring
          _ ≤ 98 * p6 (d + 1) + Csv * p6 (d + 1) := add_le_add hlin (child_bound (le_trans hmD le_self_add))
          _ = (98 + Csv) * p6 (d + 1) := by ring
          _ ≤ (4 * Csv + Csv) * p6 (d + 1) := mul_le_mul_of_nonneg_right (add_le_add h98 (le_refl _)) zero_le
          _ = 5 * Csv * p6 (d + 1) := by ring))
      hΓ hLay hch
    refine ⟨ok, nd, ?_, goal⟩
    rw [← hdd]
    refine le_trans sh ?_
    have hdeq : d = y + (setLen LAct s + 1) := by rw [hdl]; ring
    have hX : 12 * d + 7 ≤ Csv * p5 d := lin_le_p5 hd1 (by
      rw [hCsv]; exact_mod_cast (by norm_num : 12 + 7 ≤ 500000))
    calc 12 * d + Csv * p6 y + 7 = (12 * d + 7) + Csv * p6 y := by ring
      _ ≤ Csv * p6 d := rec1 le_add_self hdeq hX
  · -- allIntro
    intro s hs p d' hr hd' ih hE L Γ hL hΓ hLay
    rw [VerifyGraph'.allIntro_iff] at hL
    obtain ⟨L', -, hL', rfl⟩ := hL
    rw [fstIdx_allIntro] at hLay ⊢
    have hD : Derivation TAct (allIntro s p d') := Derivation.allIntro hr hd'
    have hd1 : 1 ≤ dlen TAct (allIntro s p d') := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (allIntro s p d') := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_allIntro] at this
    have hcD := setLen_child_le_dlen_allIntro hD
    have hy := dlen_d_succ_le_allIntro hD
    have hdl := dlen_allIntro hD
    have hp1 : IsSemiformula LAct 1 p := by have := IsSemiformula.all.mp (hs _ hr); simpa using this
    have hspD : formulaLen LAct (shift LAct p) ≤ 2 * dlen TAct (allIntro s p d') := by
      refine le_trans (formulaLen_shift_le hp1) (mul_le_mul_of_nonneg_left ?_ zero_le)
      have := formulaLen_all_le_dlen_allIntro hD
      rw [formulaLen_all hp1.isUFormula] at this
      exact le_trans le_self_add this
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (allIntro s p d') := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hcD hy hdl hspD
    obtain ⟨y, hyd⟩ : ∃ x, x = dlen TAct d' := ⟨_, rfl⟩
    rw [← hyd] at hy hdl
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hmD : y ≤ d := le_trans le_self_add hy
    have hch : ChildOK tbl Wc T E L' d' (Csv * p6 y) := fun Γ' hΓ' hLay' ↦ by
      rw [hyd]
      exact ih (le_trans (child_bound (by rw [← hyd]; exact le_trans hy le_self_add)) hE) L' Γ' hL' hΓ' hLay'
    obtain ⟨D, hDe⟩ : ∃ x : V, x = 2 * d := ⟨_, rfl⟩
    have hDd : d ≤ D := by rw [hDe]; exact le_of_add_eq' (c := d) (by ring)
    have hD0 : D ≤ 2 * (d + 1) := le_of_add_eq' (c := 2) (by rw [hDe]; ring)
    have hD1 : 1 + D ≤ 2 * (d + 1) := le_of_add_eq' (c := 1) (by rw [hDe]; ring)
    have hD2 : 1 + D + 1 ≤ 2 * (d + 1) := le_of_add_eq' (c := 0) (by rw [hDe]; ring)
    have hD3 : D + 1 ≤ 2 * (d + 1) := le_of_add_eq' (c := 1) (by rw [hDe]; ring)
    have hSA : shiftsV (proAll walkPieces Wl Wc W T s p 0) ≤ 450 * p5 (2 * (d + 1)) := by
      refine le_trans (shiftsV_proAll_le htbl hP hWl hWc walkPieces W T 0 hs hp1 hr (le_trans hsD hDd)
        (le_trans hcD hDd) (by rw [hDe]; exact hspD)) ?_
      rw [pow5_eq_p5]
      exact mul_le_mul_of_nonneg_left (p5_mono hD3) zero_le
    have hlin : 40 * D + 18 * ‖D‖ + 40 ≤ 196 * p6 (d + 1) := by
      calc 40 * D + 18 * ‖D‖ + 40 ≤ (40 + 18 + 40) * (D + 1) := lin_cap 40 18 40 D
        _ ≤ (40 + 18 + 40) * (2 * (d + 1)) := mul_le_mul_of_nonneg_left hD3 zero_le
        _ = 196 * (d + 1) := by ring
        _ ≤ 196 * p6 (d + 1) := mul_le_mul_of_nonneg_left (le_p6_self he1) zero_le
    have h14596 : (14596 : V) ≤ 4 * Csv := by rw [hCsv]; exact_mod_cast (by norm_num : 14596 ≤ 4 * 500000)
    have hEQ : 2 * ((1 + D) * (1 + D + 1)) * (D + 1) + 4 * D + 11 ≤ 27 * p6 (d + 1) := by
      have h1 := quad_cap he1 hD1 hD2 hD3
      have h2 : 4 * D + 11 ≤ 11 * (d + 1) := le_of_add_eq' (c := 3 * d) (by rw [hDe]; ring)
      calc 2 * ((1 + D) * (1 + D + 1)) * (D + 1) + 4 * D + 11
          = 2 * ((1 + D) * (1 + D + 1)) * (D + 1) + (4 * D + 11) := by ring
        _ ≤ 2 * 2 * 2 * 2 * p6 (d + 1) + 11 * (d + 1) := add_le_add h1 h2
        _ ≤ 2 * 2 * 2 * 2 * p6 (d + 1) + 11 * p6 (d + 1) :=
            add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (le_p6_self he1) zero_le)
        _ = 27 * p6 (d + 1) := by ring
    have hiE : 0 + 2 * ((1 + D) * (1 + D + 1)) * D + 40 * D + 20 ≤ 96 * p6 (d + 1) := by
      have h1 := quad_cap he1 hD1 hD2 hD0
      have h2 : 40 * D + 20 ≤ 80 * (d + 1) := le_of_add_eq' (c := 60) (by rw [hDe]; ring)
      calc 0 + 2 * ((1 + D) * (1 + D + 1)) * D + 40 * D + 20 = 2 * ((1 + D) * (1 + D + 1)) * D + (40 * D + 20) := by ring
        _ ≤ 2 * 2 * 2 * 2 * p6 (d + 1) + 80 * (d + 1) := add_le_add h1 h2
        _ ≤ 2 * 2 * 2 * 2 * p6 (d + 1) + 80 * p6 (d + 1) :=
            add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (le_p6_self he1) zero_le)
        _ = 96 * p6 (d + 1) := by ring
    obtain ⟨ok, nd, sh, goal⟩ := vAll_ok (D := D) htbl hP htblN hWl hWc hWp hW₂ hs hr hd' (le_trans hsD hDd)
      (le_trans hcD hDd) (by rw [hDe]; exact hspD) (by rw [← hyd]; exact le_trans hmD hDd) hSA
      (capE6 hE hCsCk (by
        calc 450 * p5 (2 * (d + 1)) + 40 * D + 18 * ‖D‖ + Csv * p6 y + 40
            = 450 * p5 (2 * (d + 1)) + (40 * D + 18 * ‖D‖ + 40) + Csv * p6 y := by ring
          _ ≤ 14400 * p6 (d + 1) + 196 * p6 (d + 1) + Csv * p6 (d + 1) :=
              add_le_add (add_le_add (proSA_le_p6 hd1) hlin) (child_bound (le_trans hmD le_self_add))
          _ = (14596 + Csv) * p6 (d + 1) := by ring
          _ ≤ (4 * Csv + Csv) * p6 (d + 1) := mul_le_mul_of_nonneg_right (add_le_add h14596 (le_refl _)) zero_le
          _ = 5 * Csv * p6 (d + 1) := by ring))
      (capE6 hE (by have := hCk 27 (by norm_num); push_cast at this; exact this) hEQ)
      (capE6 hE (by have := hCk 96 (by norm_num); push_cast at this; exact this) hiE)
      hΓ hLay hch
    refine ⟨ok, nd, ?_, goal⟩
    rw [← hdd]
    refine le_trans sh ?_
    have hdeq : d = y + (setLen LAct s + 1) := by rw [hdl]; ring
    calc 450 * p5 (2 * (d + 1)) + Csv * p6 y + 3 = (450 * p5 (2 * (d + 1)) + 3) + Csv * p6 y := by ring
      _ ≤ Csv * p6 d := rec1 le_add_self hdeq (proSA_add_le_p5 hd1 hCs')
  · -- exsIntro
    intro s hs p t d' hr ht hd' ih hE L Γ hL hΓ hLay
    rw [VerifyGraph'.exsIntro_iff] at hL
    obtain ⟨L', -, hL', rfl⟩ := hL
    rw [fstIdx_exsIntro] at hLay ⊢
    have hD : Derivation TAct (exsIntro s p t d') := Derivation.exsIntro hr ht hd'
    have hd1 : 1 ≤ dlen TAct (exsIntro s p t d') := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (exsIntro s p t d') := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_exsIntro] at this
    have hcD := setLen_child_le_dlen_exsIntro hD
    have htD := termLen_le_dlen_exsIntro hD
    have hy := dlen_d_succ_le_exsIntro hD
    have hdl := dlen_exsIntro hD
    have hp1 : IsSemiformula LAct 1 p := by have := IsSemiformula.exs.mp (hs _ hr); simpa using this
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (exsIntro s p t d') := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hcD htD hy hdl
    obtain ⟨y, hyd⟩ : ∃ x, x = dlen TAct d' := ⟨_, rfl⟩
    rw [← hyd] at hy hdl
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hmD : y ≤ d := le_trans le_self_add hy
    have hch : ChildOK tbl Wc T E L' d' (Csv * p6 y) := fun Γ' hΓ' hLay' ↦ by
      rw [hyd]
      exact ih (le_trans (child_bound (by rw [← hyd]; exact le_trans hy le_self_add)) hE) L' Γ' hL' hΓ' hLay'
    obtain ⟨D, hDe⟩ : ∃ x : V, x = 2 * d := ⟨_, rfl⟩
    have hDd : d ≤ D := by rw [hDe]; exact le_of_add_eq' (c := d) (by ring)
    have hD0 : D ≤ 2 * (d + 1) := le_of_add_eq' (c := 2) (by rw [hDe]; ring)
    have hD1 : 1 + D ≤ 2 * (d + 1) := le_of_add_eq' (c := 1) (by rw [hDe]; ring)
    have hD2 : 1 + D + D ≤ 4 * (d + 1) := le_of_add_eq' (c := 3) (by rw [hDe]; ring)
    have hD3 : D + 1 ≤ 2 * (d + 1) := le_of_add_eq' (c := 1) (by rw [hDe]; ring)
    have hSA : shiftsV (proExs walkPieces Wl Wc W T s p t 0) ≤ 450 * p5 (2 * (d + 1)) := by
      refine le_trans (shiftsV_proExs_le htbl hP hWl hWc walkPieces W T 0 hs hp1 hr ht (le_trans hsD hDd)
        (le_trans hcD hDd) (le_trans htD hDd)) ?_
      rw [pow5_eq_p5]
      have h310 : (310 : V) ≤ 450 := by exact_mod_cast (by norm_num : (310 : ℕ) ≤ 450)
      exact mul_le_mul h310 (p5_mono hD3) zero_le zero_le
    have hlin : 60 * D + 18 * ‖D‖ + 60 ≤ 276 * p6 (d + 1) := by
      calc 60 * D + 18 * ‖D‖ + 60 ≤ (60 + 18 + 60) * (D + 1) := lin_cap 60 18 60 D
        _ ≤ (60 + 18 + 60) * (2 * (d + 1)) := mul_le_mul_of_nonneg_left hD3 zero_le
        _ = 276 * (d + 1) := by ring
        _ ≤ 276 * p6 (d + 1) := mul_le_mul_of_nonneg_left (le_p6_self he1) zero_le
    have h29076 : (29076 : V) ≤ 3 * Csv := by rw [hCsv]; exact_mod_cast (by norm_num : 29076 ≤ 3 * 500000)
    have hEQ : 2 * ((1 + D) * (1 + D + D)) * (D + 1) + 4 * D + 11 ≤ 43 * p6 (d + 1) := by
      have h1 := quad_cap he1 hD1 hD2 hD3
      have h2 : 4 * D + 11 ≤ 11 * (d + 1) := le_of_add_eq' (c := 3 * d) (by rw [hDe]; ring)
      calc 2 * ((1 + D) * (1 + D + D)) * (D + 1) + 4 * D + 11
          = 2 * ((1 + D) * (1 + D + D)) * (D + 1) + (4 * D + 11) := by ring
        _ ≤ 2 * 2 * 4 * 2 * p6 (d + 1) + 11 * (d + 1) := add_le_add h1 h2
        _ ≤ 2 * 2 * 4 * 2 * p6 (d + 1) + 11 * p6 (d + 1) :=
            add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (le_p6_self he1) zero_le)
        _ = 43 * p6 (d + 1) := by ring
    have hiE : 0 + 2 * ((1 + D) * (1 + D + D)) * D + 40 * D + 20 ≤ 112 * p6 (d + 1) := by
      have h1 := quad_cap he1 hD1 hD2 hD0
      have h2 : 40 * D + 20 ≤ 80 * (d + 1) := le_of_add_eq' (c := 60) (by rw [hDe]; ring)
      calc 0 + 2 * ((1 + D) * (1 + D + D)) * D + 40 * D + 20 = 2 * ((1 + D) * (1 + D + D)) * D + (40 * D + 20) := by ring
        _ ≤ 2 * 2 * 4 * 2 * p6 (d + 1) + 80 * (d + 1) := add_le_add h1 h2
        _ ≤ 2 * 2 * 4 * 2 * p6 (d + 1) + 80 * p6 (d + 1) :=
            add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (le_p6_self he1) zero_le)
        _ = 112 * p6 (d + 1) := by ring
    obtain ⟨ok, nd, sh, goal⟩ := vExs_ok (D := D) htbl hP htblN hWl hWc hWp hW₂ hs hr ht hd' (le_trans hsD hDd)
      (le_trans hcD hDd) (le_trans htD hDd) (by rw [← hyd]; exact le_trans hmD hDd) hSA
      (capE6 hE hCsCk (by
        calc 2 * (450 * p5 (2 * (d + 1))) + 60 * D + 18 * ‖D‖ + 2 * (Csv * p6 y) + 60
            = 2 * (450 * p5 (2 * (d + 1))) + (60 * D + 18 * ‖D‖ + 60) + 2 * (Csv * p6 y) := by ring
          _ ≤ 2 * (14400 * p6 (d + 1)) + 276 * p6 (d + 1) + 2 * (Csv * p6 (d + 1)) :=
              add_le_add (add_le_add (mul_le_mul_of_nonneg_left (proSA_le_p6 hd1) zero_le) hlin)
                (mul_le_mul_of_nonneg_left (child_bound (le_trans hmD le_self_add)) zero_le)
          _ = (29076 + 2 * Csv) * p6 (d + 1) := by ring
          _ ≤ (3 * Csv + 2 * Csv) * p6 (d + 1) := mul_le_mul_of_nonneg_right (add_le_add h29076 (le_refl _)) zero_le
          _ = 5 * Csv * p6 (d + 1) := by ring))
      (capE6 hE (by have := hCk 43 (by norm_num); push_cast at this; exact this) hEQ)
      (capE6 hE (by have := hCk 112 (by norm_num); push_cast at this; exact this) hiE)
      hΓ hLay hch
    refine ⟨ok, nd, ?_, goal⟩
    rw [← hdd]
    refine le_trans sh ?_
    have hdeq : d = y + (setLen LAct s + termLen LAct t + 1) := by rw [hdl]; ring
    calc 450 * p5 (2 * (d + 1)) + Csv * p6 y + 3 = (450 * p5 (2 * (d + 1)) + 3) + Csv * p6 y := by ring
      _ ≤ Csv * p6 d := rec1 le_add_self hdeq (proSA_add_le_p5 hd1 hCs')
  · -- wkRule
    intro s hs d' hsub hd' ih hE L Γ hL hΓ hLay
    rw [VerifyGraph'.wkRule_iff] at hL
    obtain ⟨L', -, hL', rfl⟩ := hL
    rw [fstIdx_wkRule] at hLay ⊢
    have hD : Derivation TAct (wkRule s d') := Derivation.wkRule hs hsub ⟨rfl, hd'⟩
    have hd1 : 1 ≤ dlen TAct (wkRule s d') := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (wkRule s d') := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_wkRule] at this
    have hcD := setLen_child_le_dlen_wkRule hD
    have hy := dlen_d_succ_le_wkRule hD
    have hdl := dlen_wkRule hD
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (wkRule s d') := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hcD hy hdl
    obtain ⟨y, hyd⟩ : ∃ x, x = dlen TAct d' := ⟨_, rfl⟩
    rw [← hyd] at hy hdl
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hmD : y ≤ d := le_trans le_self_add hy
    have hch : ChildOK tbl Wc T E L' d' (Csv * p6 y) := fun Γ' hΓ' hLay' ↦ by
      rw [hyd]
      exact ih (le_trans (child_bound (by rw [← hyd]; exact le_trans hy le_self_add)) hE) L' Γ' hL' hΓ' hLay'
    have hlin : 40 * d + 18 * ‖d‖ + 40 ≤ 98 * p6 (d + 1) := by
      calc 40 * d + 18 * ‖d‖ + 40 ≤ (40 + 18 + 40) * (d + 1) := lin_cap 40 18 40 d
        _ = 98 * (d + 1) := by ring
        _ ≤ 98 * p6 (d + 1) := mul_le_mul_of_nonneg_left (le_p6_self he1) zero_le
    have h98 : (98 : V) ≤ 4 * Csv := by rw [hCsv]; exact_mod_cast (by norm_num : 98 ≤ 4 * 500000)
    obtain ⟨ok, nd, sh, goal⟩ := vWk_ok (D := d) htbl hP htblN hWl hWc hWp hW₁ hs hd' hsub hsD hcD (by rw [← hyd]; exact hmD)
      (capE6 hE hCsCk (by
        calc 40 * d + 18 * ‖d‖ + Csv * p6 y + 40 = (40 * d + 18 * ‖d‖ + 40) + Csv * p6 y := by ring
          _ ≤ 98 * p6 (d + 1) + Csv * p6 (d + 1) := add_le_add hlin (child_bound (le_trans hmD le_self_add))
          _ = (98 + Csv) * p6 (d + 1) := by ring
          _ ≤ (4 * Csv + Csv) * p6 (d + 1) := mul_le_mul_of_nonneg_right (add_le_add h98 (le_refl _)) zero_le
          _ = 5 * Csv * p6 (d + 1) := by ring))
      hΓ hLay hch
    refine ⟨ok, nd, ?_, goal⟩
    rw [← hdd]
    refine le_trans sh ?_
    have hdeq : d = y + (setLen LAct s + 1) := by rw [hdl]; ring
    have hX : 7 * d + 8 ≤ Csv * p5 d := lin_le_p5 hd1 (by
      rw [hCsv]; exact_mod_cast (by norm_num : 7 + 8 ≤ 500000))
    calc 7 * d + Csv * p6 y + 8 = (7 * d + 8) + Csv * p6 y := by ring
      _ ≤ Csv * p6 d := rec1 le_add_self hdeq hX
  · -- shiftRule
    intro s hs d' hsc hd' ih hE L Γ hL hΓ hLay
    rw [VerifyGraph'.shiftRule_iff] at hL
    obtain ⟨L', -, hL', rfl⟩ := hL
    rw [fstIdx_shiftRule] at hLay ⊢
    have hD : Derivation TAct (shiftRule s d') := by
      have := Derivation.shiftRule (T := TAct) ⟨rfl, hd'⟩; rwa [← hsc] at this
    have hd1 : 1 ≤ dlen TAct (shiftRule s d') := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (shiftRule s d') := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_shiftRule] at this
    have hcD := setLen_child_le_dlen_shiftRule hD
    have hy := dlen_d_succ_le_shiftRule hD
    have hdl := dlen_shiftRule hD
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (shiftRule s d') := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hcD hy hdl
    obtain ⟨y, hyd⟩ : ∃ x, x = dlen TAct d' := ⟨_, rfl⟩
    rw [← hyd] at hy hdl
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hmD : y ≤ d := le_trans le_self_add hy
    have hch : ChildOK tbl Wc T E L' d' (Csv * p6 y) := fun Γ' hΓ' hLay' ↦ by
      rw [hyd]
      exact ih (le_trans (child_bound (by rw [← hyd]; exact le_trans hy le_self_add)) hE) L' Γ' hL' hΓ' hLay'
    have hlin : 40 * d + 18 * ‖d‖ + 40 ≤ 98 * p6 (d + 1) := by
      calc 40 * d + 18 * ‖d‖ + 40 ≤ (40 + 18 + 40) * (d + 1) := lin_cap 40 18 40 d
        _ = 98 * (d + 1) := by ring
        _ ≤ 98 * p6 (d + 1) := mul_le_mul_of_nonneg_left (le_p6_self he1) zero_le
    have h98 : (98 : V) ≤ 4 * Csv := by rw [hCsv]; exact_mod_cast (by norm_num : 98 ≤ 4 * 500000)
    obtain ⟨ok, nd, sh, goal⟩ := vShift_ok (D := d) htbl hP htblN hWl hWc hWp hW₂ hs hd' hsc hsD hcD (by rw [← hyd]; exact hmD)
      (capE6 hE hCsCk (by
        calc 40 * d + 18 * ‖d‖ + Csv * p6 y + 40 = (40 * d + 18 * ‖d‖ + 40) + Csv * p6 y := by ring
          _ ≤ 98 * p6 (d + 1) + Csv * p6 (d + 1) := add_le_add hlin (child_bound (le_trans hmD le_self_add))
          _ = (98 + Csv) * p6 (d + 1) := by ring
          _ ≤ (4 * Csv + Csv) * p6 (d + 1) := mul_le_mul_of_nonneg_right (add_le_add h98 (le_refl _)) zero_le
          _ = 5 * Csv * p6 (d + 1) := by ring))
      hΓ hLay hch
    refine ⟨ok, nd, ?_, goal⟩
    rw [← hdd]
    refine le_trans sh ?_
    have hdeq : d = y + (setLen LAct s + 1) := by rw [hdl]; ring
    have hX : 7 * d + 8 ≤ Csv * p5 d := lin_le_p5 hd1 (by
      rw [hCsv]; exact_mod_cast (by norm_num : 7 + 8 ≤ 500000))
    calc 7 * d + Csv * p6 y + 8 = (7 * d + 8) + Csv * p6 y := by ring
      _ ≤ Csv * p6 d := rec1 le_add_self hdeq hX
  · -- cutRule
    intro s hs p d₁ d₂ hd₁ hd₂ ih₁ ih₂ hE L Γ hL hΓ hLay
    rw [VerifyGraph'.cutRule_iff] at hL
    obtain ⟨L₁, -, hL₁, L₂, -, hL₂, rfl⟩ := hL
    rw [fstIdx_cutRule] at hLay ⊢
    have hD : Derivation TAct (cutRule s p d₁ d₂) := Derivation.cutRule hd₁ hd₂
    have hd1 : 1 ≤ dlen TAct (cutRule s p d₁ d₂) := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (cutRule s p d₁ d₂) := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_cutRule] at this
    have hc₁D := setLen_child_le_dlen_cutRule_left hD
    have hc₂D := setLen_child_le_dlen_cutRule_right hD
    have hy₁ := dlen_d₁_succ_le_cutRule hD
    have hy₂ := dlen_d₂_succ_le_cutRule hD
    have hdl := dlen_cutRule hD
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (cutRule s p d₁ d₂) := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hc₁D hc₂D hy₁ hy₂ hdl
    obtain ⟨y₁, hy₁d⟩ : ∃ x, x = dlen TAct d₁ := ⟨_, rfl⟩
    obtain ⟨y₂, hy₂d⟩ : ∃ x, x = dlen TAct d₂ := ⟨_, rfl⟩
    rw [← hy₁d] at hy₁ hdl; rw [← hy₂d] at hy₂ hdl
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hm₁D : y₁ ≤ d := le_trans le_self_add hy₁
    have hm₂D : y₂ ≤ d := le_trans le_self_add hy₂
    have hch₁ : ChildOK tbl Wc T E L₁ d₁ (Csv * p6 y₁) := fun Γ' hΓ' hLay' ↦ by
      rw [hy₁d]
      exact ih₁ (le_trans (child_bound (by rw [← hy₁d]; exact le_trans hy₁ le_self_add)) hE) L₁ Γ' hL₁ hΓ' hLay'
    have hch₂ : ChildOK tbl Wc T E L₂ d₂ (Csv * p6 y₂) := fun Γ' hΓ' hLay' ↦ by
      rw [hy₂d]
      exact ih₂ (le_trans (child_bound (by rw [← hy₂d]; exact le_trans hy₂ le_self_add)) hE) L₂ Γ' hL₂ hΓ' hLay'
    have hlin : 60 * d + 18 * ‖d‖ + 60 ≤ 138 * p6 (d + 1) := by
      calc 60 * d + 18 * ‖d‖ + 60 ≤ (60 + 18 + 60) * (d + 1) := lin_cap 60 18 60 d
        _ = 138 * (d + 1) := by ring
        _ ≤ 138 * p6 (d + 1) := mul_le_mul_of_nonneg_left (le_p6_self he1) zero_le
    have h138 : (138 : V) ≤ 2 * Csv := by rw [hCsv]; exact_mod_cast (by norm_num : 138 ≤ 2 * 500000)
    obtain ⟨ok, nd, sh, goal⟩ := vCut_ok (D := d) htbl hP htblN hWl hWc hWp hW₁ hs hd₁ hd₂ hsD hc₁D hc₂D
      (by rw [← hy₁d]; exact hm₁D) (by rw [← hy₂d]; exact hm₂D)
      (capE6 hE hCsCk (by
        calc 60 * d + 18 * ‖d‖ + Csv * p6 y₁ + 2 * (Csv * p6 y₂) + 60
            = (60 * d + 18 * ‖d‖ + 60) + Csv * p6 y₁ + 2 * (Csv * p6 y₂) := by ring
          _ ≤ 138 * p6 (d + 1) + Csv * p6 (d + 1) + 2 * (Csv * p6 (d + 1)) :=
              add_le_add (add_le_add hlin (child_bound (le_trans hm₁D le_self_add)))
                (mul_le_mul_of_nonneg_left (child_bound (le_trans hm₂D le_self_add)) zero_le)
          _ = (138 + 3 * Csv) * p6 (d + 1) := by ring
          _ ≤ (2 * Csv + 3 * Csv) * p6 (d + 1) := mul_le_mul_of_nonneg_right (add_le_add h138 (le_refl _)) zero_le
          _ = 5 * Csv * p6 (d + 1) := by ring))
      hΓ hLay hch₁ hch₂
    refine ⟨ok, nd, ?_, goal⟩
    rw [← hdd]
    refine le_trans sh ?_
    have hdeq : d = y₁ + y₂ + (setLen LAct s + 1) := by rw [hdl]; ring
    have hX : 20 * d + 9 ≤ Csv * p5 d := lin_le_p5 hd1 (by
      rw [hCsv]; exact_mod_cast (by norm_num : 20 + 9 ≤ 500000))
    calc 20 * d + Csv * p6 y₁ + Csv * p6 y₂ + 9 = (20 * d + 9) + Csv * p6 y₁ + Csv * p6 y₂ := by ring
      _ ≤ Csv * p6 d := rec2 le_add_self hdeq hX
  · -- axm
    intro s hs p hps hpT hE L Γ hL hΓ hLay
    rw [VerifyGraph'.axm_iff] at hL
    obtain ⟨pro, -, hmem, rfl⟩ := hL
    rw [fstIdx_axm] at hLay ⊢
    obtain ⟨p', -, ip', -, pro', -, heq, hinv⟩ := hA _ hmem
    obtain ⟨e₁, heq₂⟩ := pair_ext_iff.mp heq
    obtain ⟨e₂, e₃⟩ := pair_ext_iff.mp heq₂
    rw [← e₁, ← e₂, ← e₃] at hinv
    have hD : Derivation TAct (axm s p) := Derivation.axm hs hps hpT
    have hd1 : 1 ≤ dlen TAct (axm s p) := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (axm s p) := by have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_axm] at this
    have hkD : len (memberList s) ≤ dlen TAct (axm s p) := le_trans (len_memberList_le_setLen hs) hsD
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (axm s p) := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hkD
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hn : 18 * ‖setLen LAct s + 1‖ + 7 ≤ 43 * (d + 1) := by
      have h1 : ‖setLen LAct s + 1‖ ≤ d + 1 := le_trans (length_le _) (add_le_add hsD (le_refl 1))
      calc 18 * ‖setLen LAct s + 1‖ + 7 ≤ 18 * (d + 1) + 7 := add_le_add (mul_le_mul_of_nonneg_left h1 zero_le) (le_refl 7)
        _ ≤ 43 * (d + 1) := le_of_add_eq' (c := 25 * d + 18) (by ring)
    obtain ⟨ok, nd, sh, goal⟩ := vAxm_ok (D := d) htbl hP htblN hWc hW₂ hs hps hpT hsD
      (capE hE he1 (hCk 9 (by norm_num)) (by push_cast; exact le_of_add_eq' (c := 3 * d + 6) (by ring)))
      (capE hE he1 (hCk 3 (by norm_num)) (by
        push_cast; exact le_trans (add_le_add hkD (le_refl 3)) (le_of_add_eq' (c := 2 * d) (by ring))))
      (capE hE he1 (hCk 43 (by norm_num)) (by push_cast; exact hn))
      hΓ hLay.layout hinv
    refine ⟨ok, nd, ?_, by rw [sh]; exact goal⟩
    rw [sh, ← hdd]
    exact one_le_Cs_p6 hCs1 hd1

end glueMain

end ArithS
