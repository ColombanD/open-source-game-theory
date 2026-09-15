import ArithS.Necessitation.Verify2
import ArithS.Necessitation.IndRec
import ArithS.Necessitation.Pin

/-!
# ArithS.Necessitation.Verify3 — `VerifyGraph''`: the verification recursion with SHIFTED `axm` certificates

`Verify2.lean`'s `VerifyGraph'` takes its `axm` certificates from a table `A` whose entries are SHIFT-FREE `NumInv` lists
(`AxmEntryOK`): the node fragment `nodeAxm` in `vAxm` reads the recognizer fact at the UNMOVED offset `memTop s p 0`
and the layout indices `is = k + 1`, `il = 0`. `IndRec.lean` (case (ii) of `axm`, the induction-instance recognizer)
produces lists WITH eigenvariables — `shiftsV P = σ ≤ 100 (D+1)³`, the fact at `&(ip + σ)` — and for NONSTANDARD `p` no
shift-free list of standard length exists (`IndRec.lean`'s docstring). So `VerifyGraph'` CANNOT be reused unchanged:
its `axm` clause bakes the offset `0` into `vAxm`. This file is the seam (2026-09-15):

* §1 `AxmEntryOK' tbl E Ww Cv e` — a SHIFTED entry `⟪p, ip, pro⟫`: `pro` applicable at cap `9` at the canonical dossier
  context `dossCtx Ww p ip`, `NoDrop'`, with `shiftsV pro`, `len pro` and `SizeOK` all bounded by `Cv · (|p| + 1)³`
  (the bound is INTRINSIC to `p`, so that a small leaf deep in a big derivation still fits its own budget), leaving
  `axchFact &(ip + shiftsV pro)` — the fact at `p`'s MOVED offset. `AxmTableOK'` and its algebra.
* §2 `vAxm'` — `pro` then `nodeAxm` at `is = k + 1 + σ`, `il = σ`, `ip = memTop s p σ` (`σ = shiftsV pro`): exactly how
  `vAll`/`vExs` read their eigenvariable prologues.
* §3 `VerifyGraph''` — `Verify2.VerifyGraph'` with the `axm` clause's list `vAxm'` (the OTHER nine clauses are
  byte-identical: `Verify3.Phi`/blueprint/construction, `VPackedP'`, definability, `case_iff`, the ten inversions,
  `mono_A`). The blueprint never mentions `AxmEntryOK` — the table is a parameter; only the assembler changed.
* §4 existence, UNCONDITIONAL: `axmEntry_exists'` (case (i) `Verify2.axmStd_uniform`, case (ii) `IndRec.axmInd_ok'`
  at the canonical context) and `verifyGraph''_exists` — no oracle hypothesis (`Verify2.AxmIndOracleC` and
  `ProAxm.AxmIndOracle` are RETIRED as hypotheses).
* §5 `vAxm_ok'` (the transported layout, `Layout.transport`) and `verifyGraph''_ok`/`verifyGraph''_ok_pow` — the glue of
  `Verify2.lean` §8.9 re-run with the `axm` case's shift budget `Cv·(|p|+1)³ + 1 ≤ (Cs + Cv)·(dlen ρ)^6`; the degree
  stays 6 (`m = 6`) and the constants become `Cs + Cv`, `Ck + 5·Cv`.
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

/-! ## 1. Shifted certificate entries -/

section axmTable'

/-- `x³` as an explicit product (definability-friendly, like `Verify2.p5`/`p6`). -/
def p3 (x : V) : V := x * x * x

lemma p3_mono {a b : V} (h : a ≤ b) : p3 a ≤ p3 b := by
  simp only [p3]
  exact mul_le_mul (mul_le_mul h h zero_le zero_le) h zero_le zero_le

lemma p3_le_p6 {d : V} (hd : 1 ≤ d) : p3 d ≤ p6 d := cube_le_p6 hd

lemma one_le_p3 {d : V} (hd : 1 ≤ d) : 1 ≤ p3 d := by
  simp only [p3]; exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hd hd) hd

/-- The per-entry bound: `Cv · (|p| + 1)³`. -/
noncomputable def entryB (Cv p : V) : V := Cv * p3 (formulaLen LAct p + 1)

/-- **A SHIFTED `axm` certificate entry** `⟪p, ip, pro⟫`: `pro` is applicable at cap `9` at the canonical dossier context of
`p` at `&ip`, cut-admitting, with `shiftsV`, `len` and sizes bounded by `entryB Cv p = Cv·(|p|+1)³`, and leaves
`axchFact &(ip + shiftsV pro)` — the fact at `p`'s MOVED offset. -/
def AxmEntryOK' (tbl E Ww Cv e : V) : Prop :=
  ∃ p ≤ e, ∃ ip ≤ e, ∃ pro ≤ e, e = ⟪p, ip, pro⟫ ∧
    ListOK tbl E ((9 : ℕ) : V) (dossCtx Ww p ip) pro ∧ NoDrop' pro ∧
    shiftsV pro ≤ entryB Cv p ∧ len pro ≤ entryB Cv p ∧ SizeOK (entryB Cv p) (entryB Cv p) pro ∧
    neg LAct (axchFact (^&(ip + shiftsV pro))) ∈ finalCtx (dossCtx Ww p ip) pro

/-- **The shifted certificate table**: every member of `A` is a shifted certificate entry. -/
def AxmTableOK' (tbl E Ww A Cv : V) : Prop := ∀ e ∈ A, AxmEntryOK' tbl E Ww Cv e

instance entryB_definable : 𝚺₁.DefinableFunction (fun v : Fin 2 → V ↦ entryB (v 0) (v 1)) := by
  unfold entryB p3; definability

instance axmEntryOK'_definable : 𝚫₁-Relation₅ (AxmEntryOK' : V → V → V → V → V → Prop) := by
  unfold AxmEntryOK'; definability

instance axmTableOK'_definable : 𝚫₁-Relation₅ (AxmTableOK' : V → V → V → V → V → Prop) := by
  unfold AxmTableOK'; definability

lemma AxmTableOK'.mono {tbl E Ww A A' Cv : V} (h : AxmTableOK' tbl E Ww A' Cv) (hAA : A ⊆ A') :
    AxmTableOK' tbl E Ww A Cv := by
  intro e he
  exact h e (hAA he)

lemma entryB_mono {Cv Cv' : V} (hC : Cv ≤ Cv') (p : V) : entryB Cv p ≤ entryB Cv' p :=
  mul_le_mul_of_nonneg_right hC zero_le

lemma AxmTableOK'.mono_const {tbl E Ww A Cv Cv' : V} (hC : Cv ≤ Cv') (h : AxmTableOK' tbl E Ww A Cv) :
    AxmTableOK' tbl E Ww A Cv' := by
  intro e he
  obtain ⟨p, hp, ip, hip, pro, hpro, rfl, hok, hnd, hsh, hlen, hsz, hmem⟩ := h e he
  exact ⟨p, hp, ip, hip, pro, hpro, rfl, hok, hnd, le_trans hsh (entryB_mono hC p), le_trans hlen (entryB_mono hC p),
    hsz.mono (entryB_mono hC p) (entryB_mono hC p), hmem⟩

lemma axmTableOK'_empty (tbl E Ww Cv : V) : AxmTableOK' tbl E Ww 0 Cv := fun e he ↦ by simp at he

lemma axmTableOK'_insert {tbl E Ww A Cv p ip pro : V} (h : AxmTableOK' tbl E Ww A Cv)
    (he : ListOK tbl E ((9 : ℕ) : V) (dossCtx Ww p ip) pro ∧ NoDrop' pro ∧
      shiftsV pro ≤ entryB Cv p ∧ len pro ≤ entryB Cv p ∧ SizeOK (entryB Cv p) (entryB Cv p) pro ∧
      neg LAct (axchFact (^&(ip + shiftsV pro))) ∈ finalCtx (dossCtx Ww p ip) pro) :
    AxmTableOK' tbl E Ww (insert ⟪p, ip, pro⟫ A) Cv := by
  intro e hemem
  rcases mem_bitInsert_iff.mp hemem with rfl | hemem
  · exact ⟨p, le_pair_left _ _, ip, le_trans (le_pair_left _ _) (le_pair_right _ _), pro,
      le_trans (le_pair_right _ _) (le_pair_right _ _), rfl, he⟩
  · exact h e hemem

lemma axmTableOK'_union {tbl E Ww A A' Cv : V} (h : AxmTableOK' tbl E Ww A Cv) (h' : AxmTableOK' tbl E Ww A' Cv) :
    AxmTableOK' tbl E Ww (A ∪ A') Cv := by
  intro e he
  rcases mem_cup_iff.mp he with he | he
  · exact h e he
  · exact h' e he

end axmTable'

/-! ## 2. The shifted `axm` assembler `vAxm'` -/

section assembler'

/-- The shifted `axm` list: the certificate `pro` (`σ = shiftsV pro` eigenvariables), then `nodeAxm` at the MOVED layout
`is = k + 1 + σ`, `il = σ`, `ip = memTop s p σ` — the `vAll`/`vExs` reading of an eigenvariable prologue. -/
noncomputable def vAxm' (Ww Wc W₂ T s p pro : V) : V :=
  appendV pro (nodeAxm W₂ T (len (memberList s) + 1 + shiftsV pro) (shiftsV pro) (memTop Ww Wc T s p (shiftsV pro))
    (setLen LAct s) (dlen TAct (axm s p)))

noncomputable def vAxm'Def : 𝚺₁.Semisentence 8 := .mkSigma
  “y Ww Wc W₂ T s p pro. ∃ xs, !memberListDef xs s ∧ ∃ k, !lenDef k xs ∧ ∃ σ, !shiftsVDef σ pro ∧ ∃ is, is = k + 1 + σ ∧
    ∃ ip, !memTopDef ip Ww Wc T s p σ ∧ ∃ Ls, !(setLenDef LAct) Ls s ∧ ∃ d, !axmGraph d s p ∧ ∃ n, !(dlenDef TAct) n d ∧
    ∃ F, !nodeAxmDef F W₂ T is σ ip Ls n ∧ !appendVDef y pro F”

instance vAxm'_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ vAxm' (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) vAxm'Def := .mk fun v ↦ by
  simp [vAxm'Def, vAxm', memberList_defined.iff, shiftsV_defined.iff, memTop_defined.iff, setLen_defined.iff, dlen_defined.iff,
    nodeAxm_defined.iff, appendV_defined.iff, numeral_eq_natCast]
instance vAxm'_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ vAxm' (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := vAxm'_defined.to_definable

lemma le_vAxm' (Ww Wc W₂ T s p pro : V) : pro ≤ vAxm' Ww Wc W₂ T s p pro := by
  unfold vAxm'; exact le_appendV_prefix _ _

end assembler'

/-! ## 3. `VerifyGraph''` — the Δ₁ fixpoint on the key `⟪ρ, L⟫`, the `axm` clause with `vAxm'`

Everything but the last clause is `Verify2.lean` §6 verbatim (the same key, the same nine assemblers, the same
`StrongFinite` argument); the `axm` clause is `∃ pro ≤ L, ⟪p, memTop Ww Wc T s p 0, pro⟫ ∈ A ∧ L = vAxm' Ww Wc W₂ T s p pro`
— the table is still keyed at the base offset `memTop s p 0`, and the node reads at `memTop s p (shiftsV pro)`. -/

namespace Verify3

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
  (∃ s < d, ∃ p < d, d = axm s p ∧ ∃ pro ≤ L, ⟪p, memTop Ww Wc T s p 0, pro⟫ ∈ A ∧ L = vAxm' Ww Wc W₂ T s p pro) )

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
        ∃ e, !pairDef e p e₁ ∧ e ∈ A ∧ ∃ F, !vAxm'Def F Ww Wc W₂ T s p pro ∧ L = F) )”)
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
        ∀ e, !pairDef e p e₁ → (e ∈ A ∧ ∀ F, !vAxm'Def F Ww Wc W₂ T s p pro → L = F)) )”)⟩

set_option maxHeartbeats 4000000 in
noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun v ↦ Phi (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, vAxL_defined.iff, vVerum_defined.iff, vAnd_defined.iff, vOr_defined.iff, vAll_defined.iff,
        vExs_defined.iff, vWk_defined.iff, vShift_defined.iff, vCut_defined.iff, vAxm'_defined.iff, memTop_defined.iff]
    · intro v
      simp [blueprint, Phi, vAxL_defined.iff, vVerum_defined.iff, vAnd_defined.iff, vOr_defined.iff, vAll_defined.iff,
        vExs_defined.iff, vWk_defined.iff, vShift_defined.iff, vCut_defined.iff, vAxm'_defined.iff, memTop_defined.iff]
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

end Verify3

/-! ### 3.2 `VerifyGraph''` and its definability (the PACKED-parameter pattern of `Verify2.lean` §6.2) -/

/-- The fixpoint at the packed parameter `P = ⟪Ww, Wl, Wc, W₁, W₂, W, T, A⟫` (shifted-`axm` variant). -/
def VPackedP' (P pr : V) : Prop :=
  Verify3.construction.Fixpoint
    ![π₁ P, π₁ (π₂ P), π₁ (π₂ (π₂ P)), π₁ (π₂ (π₂ (π₂ P))), π₁ (π₂ (π₂ (π₂ (π₂ P)))),
      π₁ (π₂ (π₂ (π₂ (π₂ (π₂ P))))), π₁ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ P)))))), π₂ (π₂ (π₂ (π₂ (π₂ (π₂ (π₂ P))))))] pr

/-- **The verification graph with computed lists and SHIFTED `axm` certificates**: `VerifyGraph'' Ww Wl Wc W₁ W₂ W T A ρ L`
— `Verify2.VerifyGraph'` with the `axm` clause's list `vAxm'` (the node at `p`'s MOVED offset). -/
def VerifyGraph'' (Ww Wl Wc W₁ W₂ W T A ρ L : V) : Prop := VPackedP' ⟪Ww, Wl, Wc, W₁, W₂, W, T, A⟫ ⟪ρ, L⟫

noncomputable def vPackedP'Def : 𝚺₁.Semisentence 2 := .mkSigma
  “P pr. ∃ a, !pi₁Def a P ∧ ∃ r₁, !pi₂Def r₁ P ∧ ∃ b, !pi₁Def b r₁ ∧ ∃ r₂, !pi₂Def r₂ r₁ ∧ ∃ c, !pi₁Def c r₂ ∧
    ∃ r₃, !pi₂Def r₃ r₂ ∧ ∃ d, !pi₁Def d r₃ ∧ ∃ r₄, !pi₂Def r₄ r₃ ∧ ∃ e, !pi₁Def e r₄ ∧ ∃ r₅, !pi₂Def r₅ r₄ ∧
    ∃ f, !pi₁Def f r₅ ∧ ∃ r₆, !pi₂Def r₆ r₅ ∧ ∃ g, !pi₁Def g r₆ ∧ ∃ h, !pi₂Def h r₆ ∧
    !Verify3.blueprint.fixpointDef pr a b c d e f g h”

instance vPackedP'_defined : 𝚺₁-Relation (VPackedP' : V → V → Prop) via vPackedP'Def := .mk
  fun v ↦ by
    simp [vPackedP'Def, VPackedP', Verify3.construction.eval_fixpointDef]
    first
    | exact Iff.rfl
    | (constructor <;> intro h <;> convert h using 2 <;> funext i <;> fin_cases i <;> rfl)
instance vPackedP'_definable : 𝚺₁-Relation (VPackedP' : V → V → Prop) := vPackedP'_defined.to_definable

noncomputable def verifyGraph''Def : 𝚺₁.Semisentence 10 := .mkSigma
  “Ww Wl Wc W₁ W₂ W T A ρ L. ∃ pr, !pairDef pr ρ L ∧ ∃ p₇, !pairDef p₇ T A ∧ ∃ p₆, !pairDef p₆ W p₇ ∧
    ∃ p₅, !pairDef p₅ W₂ p₆ ∧ ∃ p₄, !pairDef p₄ W₁ p₅ ∧ ∃ p₃, !pairDef p₃ Wc p₄ ∧ ∃ p₂, !pairDef p₂ Wl p₃ ∧
    ∃ P, !pairDef P Ww p₂ ∧ !vPackedP'Def P pr”

instance verifyGraph''_defined :
    𝚺₁.Defined (fun v : Fin 10 → V ↦ VerifyGraph'' (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9))
      verifyGraph''Def := .mk
  fun v ↦ by simp [verifyGraph''Def, vPackedP'_defined.iff, VerifyGraph'']
instance verifyGraph''_definable :
    𝚺₁.Definable (fun v : Fin 10 → V ↦ VerifyGraph'' (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) :=
  verifyGraph''_defined.to_definable

/-! ### 3.3 Case analysis and the ten inversions -/

lemma VerifyGraph''.case_iff {Ww Wl Wc W₁ W₂ W T A ρ L : V} :
    VerifyGraph'' Ww Wl Wc W₁ W₂ W T A ρ L ↔
    (
    (∃ s < ρ, ∃ p < ρ, ρ = axL s p ∧ L = vAxL Ww Wc W₁ T s p) ∨
    (∃ s < ρ, ρ = verumIntro s ∧ L = vVerum Ww Wc W₁ T s) ∨
    (∃ s < ρ, ∃ p < ρ, ∃ q < ρ, ∃ dp < ρ, ∃ dq < ρ, ρ = andIntro s p q dp dq ∧
      ∃ L₁ ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A dp L₁ ∧ ∃ L₂ ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A dq L₂ ∧
      L = vAnd Ww Wl Wc W₁ W T s p q dp dq L₁ L₂) ∨
    (∃ s < ρ, ∃ p < ρ, ∃ q < ρ, ∃ d' < ρ, ρ = orIntro s p q d' ∧
      ∃ L' ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vOr Ww Wl Wc W₁ W T s p q d' L') ∨
    (∃ s < ρ, ∃ p < ρ, ∃ d' < ρ, ρ = allIntro s p d' ∧
      ∃ L' ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vAll Ww Wl Wc W₂ W T s p d' L') ∨
    (∃ s < ρ, ∃ p < ρ, ∃ t < ρ, ∃ d' < ρ, ρ = exsIntro s p t d' ∧
      ∃ L' ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vExs Ww Wl Wc W₂ W T s p t d' L') ∨
    (∃ s < ρ, ∃ d' < ρ, ρ = wkRule s d' ∧
      ∃ L' ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vWk Ww Wl Wc W₁ W T s d' L') ∨
    (∃ s < ρ, ∃ d' < ρ, ρ = shiftRule s d' ∧
      ∃ L' ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vShift Ww Wl Wc W₂ W T s d' L') ∨
    (∃ s < ρ, ∃ p < ρ, ∃ d₁ < ρ, ∃ d₂ < ρ, ρ = cutRule s p d₁ d₂ ∧
      ∃ L₁ ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A d₁ L₁ ∧ ∃ L₂ ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A d₂ L₂ ∧
      L = vCut Ww Wl Wc W₁ W T s p d₁ d₂ L₁ L₂) ∨
    (∃ s < ρ, ∃ p < ρ, ρ = axm s p ∧ ∃ pro ≤ L, ⟪p, memTop Ww Wc T s p 0, pro⟫ ∈ A ∧ L = vAxm' Ww Wc W₂ T s p pro) ) := by
  unfold VerifyGraph'' VPackedP'
  simp only [pi₁_pair, pi₂_pair]
  rw [Verify3.construction.case]
  show Verify3.Phi _ _ _ _ _ _ _ _ _ _ ↔ _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Verify3.Phi]
  constructor
  · rintro ⟨d, _, L', _, hpr, h⟩
    obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp hpr
    exact h
  · intro h
    exact ⟨ρ, by simp, L, by simp, rfl, h⟩

section inversion

attribute [local simp] axL verumIntro andIntro orIntro allIntro exsIntro wkRule shiftRule cutRule axm

variable {Ww Wl Wc W₁ W₂ W T A : V}

lemma VerifyGraph''.axL_iff {s p L : V} :
    VerifyGraph'' Ww Wl Wc W₁ W₂ W T A (axL s p) L ↔ L = vAxL Ww Wc W₁ T s p := by
  rw [VerifyGraph''.case_iff]
  simp
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [axL] using seq_lt_axL s p, by simpa [axL] using arity_lt_axL s p, h⟩

lemma VerifyGraph''.verumIntro_iff {s L : V} :
    VerifyGraph'' Ww Wl Wc W₁ W₂ W T A (verumIntro s) L ↔ L = vVerum Ww Wc W₁ T s := by
  rw [VerifyGraph''.case_iff]
  simp
  intros
  simpa [verumIntro] using seq_lt_verumIntro s

lemma VerifyGraph''.andIntro_iff {s p q dp dq L : V} :
    VerifyGraph'' Ww Wl Wc W₁ W₂ W T A (andIntro s p q dp dq) L ↔
    ∃ L₁ ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A dp L₁ ∧ ∃ L₂ ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A dq L₂ ∧
      L = vAnd Ww Wl Wc W₁ W T s p q dp dq L₁ L₂ := by
  rw [VerifyGraph''.case_iff]
  simp
  constructor
  · rintro ⟨-, -, -, -, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [andIntro] using seq_lt_andIntro s p q dp dq, by simpa [andIntro] using p_lt_andIntro s p q dp dq,
      by simpa [andIntro] using q_lt_andIntro s p q dp dq, by simpa [andIntro] using dp_lt_andIntro s p q dp dq,
      by simpa [andIntro] using dq_lt_andIntro s p q dp dq, h⟩

lemma VerifyGraph''.orIntro_iff {s p q d' L : V} :
    VerifyGraph'' Ww Wl Wc W₁ W₂ W T A (orIntro s p q d') L ↔
    ∃ L' ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vOr Ww Wl Wc W₁ W T s p q d' L' := by
  rw [VerifyGraph''.case_iff]
  simp
  constructor
  · rintro ⟨-, -, -, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [orIntro] using seq_lt_orIntro s p q d', by simpa [orIntro] using p_lt_orIntro s p q d',
      by simpa [orIntro] using q_lt_orIntro s p q d', by simpa [orIntro] using d_lt_orIntro s p q d', h⟩

lemma VerifyGraph''.allIntro_iff {s p d' L : V} :
    VerifyGraph'' Ww Wl Wc W₁ W₂ W T A (allIntro s p d') L ↔
    ∃ L' ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vAll Ww Wl Wc W₂ W T s p d' L' := by
  rw [VerifyGraph''.case_iff]
  simp
  constructor
  · rintro ⟨-, -, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [allIntro] using seq_lt_allIntro s p d', by simpa [allIntro] using p_lt_allIntro s p d',
      by simpa [allIntro] using s_lt_allIntro s p d', h⟩

lemma VerifyGraph''.exsIntro_iff {s p t d' L : V} :
    VerifyGraph'' Ww Wl Wc W₁ W₂ W T A (exsIntro s p t d') L ↔
    ∃ L' ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vExs Ww Wl Wc W₂ W T s p t d' L' := by
  rw [VerifyGraph''.case_iff]
  simp
  constructor
  · rintro ⟨-, -, -, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [exsIntro] using seq_lt_exsIntro s p t d', by simpa [exsIntro] using p_lt_exsIntro s p t d',
      by simpa [exsIntro] using t_lt_exsIntro s p t d', by simpa [exsIntro] using d_lt_exsIntro s p t d', h⟩

lemma VerifyGraph''.wkRule_iff {s d' L : V} :
    VerifyGraph'' Ww Wl Wc W₁ W₂ W T A (wkRule s d') L ↔
    ∃ L' ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vWk Ww Wl Wc W₁ W T s d' L' := by
  rw [VerifyGraph''.case_iff]
  simp
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [wkRule] using seq_lt_wkRule s d', by simpa [wkRule] using d_lt_wkRule s d', h⟩

lemma VerifyGraph''.shiftRule_iff {s d' L : V} :
    VerifyGraph'' Ww Wl Wc W₁ W₂ W T A (shiftRule s d') L ↔
    ∃ L' ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A d' L' ∧ L = vShift Ww Wl Wc W₂ W T s d' L' := by
  rw [VerifyGraph''.case_iff]
  simp
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [shiftRule] using seq_lt_shiftRule s d', by simpa [shiftRule] using d_lt_shiftRule s d', h⟩

lemma VerifyGraph''.cutRule_iff {s p d₁ d₂ L : V} :
    VerifyGraph'' Ww Wl Wc W₁ W₂ W T A (cutRule s p d₁ d₂) L ↔
    ∃ L₁ ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A d₁ L₁ ∧ ∃ L₂ ≤ L, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A d₂ L₂ ∧
      L = vCut Ww Wl Wc W₁ W T s p d₁ d₂ L₁ L₂ := by
  rw [VerifyGraph''.case_iff]
  simp
  constructor
  · rintro ⟨-, -, -, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [cutRule] using seq_lt_cutRule s p d₁ d₂, by simpa [cutRule] using p_lt_cutRule s p d₁ d₂,
      by simpa [cutRule] using d₁_lt_cutRule s p d₁ d₂, by simpa [cutRule] using d₂_lt_cutRule s p d₁ d₂, h⟩

lemma VerifyGraph''.axm_iff {s p L : V} :
    VerifyGraph'' Ww Wl Wc W₁ W₂ W T A (axm s p) L ↔
    ∃ pro ≤ L, ⟪p, memTop Ww Wc T s p 0, pro⟫ ∈ A ∧ L = vAxm' Ww Wc W₂ T s p pro := by
  rw [VerifyGraph''.case_iff]
  simp
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · intro h
    exact ⟨by simpa [axm] using seq_lt_axm s p, by simpa [axm] using p_lt_axm s p, h⟩

end inversion

/-! ### 3.4 Monotonicity in the certificate table -/

section mono'

/-- **`VerifyGraph''` is monotone in the certificate table** (by `Fixpoint.induction` on the key). -/
theorem VerifyGraph''.mono_A {Ww Wl Wc W₁ W₂ W T A A' : V} (hAA : A ⊆ A') {ρ L : V}
    (h : VerifyGraph'' Ww Wl Wc W₁ W₂ W T A ρ L) : VerifyGraph'' Ww Wl Wc W₁ W₂ W T A' ρ L := by
  have key : ∀ pr, VPackedP' ⟪Ww, Wl, Wc, W₁, W₂, W, T, A⟫ pr → VPackedP' ⟪Ww, Wl, Wc, W₁, W₂, W, T, A'⟫ pr := by
    intro pr
    unfold VPackedP'
    simp only [pi₁_pair, pi₂_pair]
    apply Verify3.construction.induction (Γ := 𝚺)
      (P := fun pr ↦ Verify3.construction.Fixpoint ![Ww, Wl, Wc, W₁, W₂, W, T, A'] pr)
      (HierarchySymbol.Definable.of_iff (Q := fun v ↦ VPackedP' ⟪Ww, Wl, Wc, W₁, W₂, W, T, A'⟫ (v 0))
        (by definability) (fun v ↦ by simp only [VPackedP', pi₁_pair, pi₂_pair]))
    intro C hC x hx
    rw [Verify3.construction.case]
    show Verify3.Phi _ _ _ _ _ _ _ _ _ _
    have hx' : Verify3.Phi Ww Wl Wc W₁ W₂ W T A C x := hx
    obtain ⟨d, hd, L, hL, rfl, h⟩ := hx'
    refine ⟨d, hd, L, hL, rfl, ?_⟩
    have tr : ∀ {z : V}, z ∈ C → z ∈ {z | Verify3.construction.Fixpoint ![Ww, Wl, Wc, W₁, W₂, W, T, A'] z} :=
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

end mono'

end ArithS
