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

/-- The `wk` prologue selector: `proWk` for a nonempty child, `proWk0` for the empty child. -/
noncomputable def wkPro (Ww Wl Wc W T s c : V) : V :=
  if memberList c = 0 then proWk0 W s 0 else proWk Ww Wl Wc W T s c 0

noncomputable def wkProDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y Ww Wl Wc W T s c. ∃ xs, !memberListDef xs c ∧
    (xs = 0 → !proWk0Def y W s 0) ∧ (xs ≠ 0 → !proWkDef y Ww Wl Wc W T s c 0)”

instance wkPro_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ wkPro (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) wkProDef := .mk fun v ↦ by
  simp [wkProDef, wkPro, memberList_defined.iff, proWk_defined.iff, proWk0_defined.iff, numeral_eq_natCast]
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
  if memberList c = 0 then appendV (proShift0 W 0) (reset0 W) else proShift Ww Wl Wc W T s c 0

noncomputable def shiftProDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y Ww Wl Wc W T s c. ∃ xs, !memberListDef xs c ∧
    (xs = 0 → ∃ P, !proShift0Def P W 0 ∧ ∃ R, !reset0Def R W ∧ !appendVDef y P R) ∧
    (xs ≠ 0 → !proShiftDef y Ww Wl Wc W T s c 0)”

instance shiftPro_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ shiftPro (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) shiftProDef := .mk fun v ↦ by
  simp [shiftProDef, shiftPro, memberList_defined.iff, proShift_defined.iff, proShift0_defined.iff, reset0_defined.iff,
    appendV_defined.iff, numeral_eq_natCast]
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

end ArithS
