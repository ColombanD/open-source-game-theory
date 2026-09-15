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


/-! ## 4. Existence: the oracle-shaped form, the oracle DISCHARGED, and the UNCONDITIONAL theorem -/

section existence'

lemma gp_three_eq_p3 (x : V) : gp x 3 = p3 x := by simp [gp, p3]

/-- **Case (ii) at the canonical context** (`IndRec.axmInd_ok'` at `Γ = dossCtx walkPieces p ip`): for every induction
instance `p` with `|p| ≤ D` and the room `ip + 200 (D+1)³ ≤ E`, a shifted certificate list with every bound `1400 (D+1)³`. -/
theorem axmIndEntry_of_indRec {tbl N E p ip D : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl)
    (hF : IsSemiformula ℒₒᵣ 0 p) (hI : InductionR (fun _ ↦ True) p) (hpD : formulaLen LAct p ≤ D)
    (hE : ip + 200 * gp (D + 1) 3 ≤ E) :
    ∃ P : V, ListOK tbl E ((9 : ℕ) : V) (dossCtx walkPieces p ip) P ∧ NoDrop' P ∧
      shiftsV P ≤ 1400 * gp (D + 1) 3 ∧ len P ≤ 1400 * gp (D + 1) 3 ∧
      SizeOK (1400 * gp (D + 1) 3) (1400 * gp (D + 1) 3) P ∧
      neg LAct (axchFact (^&(ip + shiftsV P))) ∈ finalCtx (dossCtx walkPieces p ip) P := by
  have hΓ : IsFormulaSet LAct (dossCtx walkPieces p ip) :=
    isFormulaSet_dossCtx htbl hT.walkTable (IsSemiformula.LAct_of_LOR hF) ip
  obtain ⟨P, h1, h2, h3, h4, h5, h6⟩ := axmInd_ok' htbl hT hΓ hI hpD hE (dossF_dossCtx walkPieces p ip)
  exact ⟨P, h1, h2, le_trans h4 (mul_le_mul_of_nonneg_right (by norm_num) zero_le), h5, sizeOK_of_hornOnly h3, h6⟩

/-- **The `AxmIndOracle'`-shaped oracle at the canonical context**: for every induction instance `p` and offset `ip` with
room `C·(|p|+1)³ + ip ≤ E`, a SHIFTED certificate list at `dossCtx walkPieces p ip` with every bound `entryB C p`
(`Verify2.AxmIndOracleC` with eigenvariables and the fact at the moved offset). Discharged by `axmIndOracleC'_of_indRec`. -/
def AxmIndOracleC' (tbl E : V) (C : ℕ) : Prop :=
  ∀ p ip : V, IsSemiformula ℒₒᵣ 0 p → InductionR (fun _ ↦ True) p → (C : V) * p3 (formulaLen LAct p + 1) + ip ≤ E →
    ∃ P : V, ListOK tbl E ((9 : ℕ) : V) (dossCtx walkPieces p ip) P ∧ NoDrop' P ∧
      shiftsV P ≤ entryB (C : V) p ∧ len P ≤ entryB (C : V) p ∧ SizeOK (entryB (C : V) p) (entryB (C : V) p) P ∧
      neg LAct (axchFact (^&(ip + shiftsV P))) ∈ finalCtx (dossCtx walkPieces p ip) P

/-- **The oracle DISCHARGED** (the seam's `axmTable_of_indRec`): at any `IndRecTable`, `AxmIndOracleC'` holds with `C = 1400`. -/
theorem axmIndOracleC'_of_indRec {tbl N E : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) :
    AxmIndOracleC' tbl E 1400 := by
  intro p ip hF hI hE
  have hE' : ip + 200 * gp (formulaLen LAct p + 1) 3 ≤ E := by
    refine le_trans ?_ hE
    rw [add_comm, gp_three_eq_p3]
    exact add_le_add (mul_le_mul_of_nonneg_right (by push_cast; norm_num) zero_le) le_rfl
  obtain ⟨P, hok, hnd, hsh, hlen, hsz, hmem⟩ := axmIndEntry_of_indRec htbl hT hF hI le_rfl hE'
  have e : (1400 : V) * gp (formulaLen LAct p + 1) 3 = entryB ((1400 : ℕ) : V) p := by
    unfold entryB; rw [gp_three_eq_p3]; push_cast; rfl
  rw [e] at hsh hlen hsz
  exact ⟨P, hok, hnd, hsh, hlen, hsz, hmem⟩

/-- **A shifted `axm` certificate entry exists for every `p ∈ TAct.Δ₁Class`** (per model): case (i) by
`axmStd_uniform` (shift-free, standard length), case (ii) by the oracle `AxmIndOracleC' tbl E Cind`; ONE constant
`C + Cind`, the entry bound `entryB (C + Cind) p`, the room `(C + Cind)·(|p|+1)³ + ip ≤ E`. -/
theorem axmEntry_exists' : ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N E p ip : V}
    (Cind : ℕ), TableOK tbl N → ProAxmTable tbl → IsSemiformula LAct 0 p → p ∈ TAct.Δ₁Class →
    ((C + Cind : ℕ) : V) * p3 (formulaLen LAct p + 1) + ip ≤ E → AxmIndOracleC' tbl E Cind →
    ∃ P : V, ListOK tbl E ((9 : ℕ) : V) (dossCtx walkPieces p ip) P ∧ NoDrop' P ∧
      shiftsV P ≤ entryB ((C + Cind : ℕ) : V) p ∧ len P ≤ entryB ((C + Cind : ℕ) : V) p ∧
      SizeOK (entryB ((C + Cind : ℕ) : V) p) (entryB ((C + Cind : ℕ) : V) p) P ∧
      neg LAct (axchFact (^&(ip + shiftsV P))) ∈ finalCtx (dossCtx walkPieces p ip) P := by
  obtain ⟨C₀, hC⟩ := axmStd_uniform
  refine ⟨C₀, fun V _ _ tbl N E p ip Cind htbl hT hp hax hE hind ↦ ?_⟩
  have h1p : (1 : V) ≤ p3 (formulaLen LAct p + 1) := one_le_p3 le_add_self
  have hC1 : ((C₀ : ℕ) : V) ≤ ((C₀ + Cind : ℕ) : V) := by exact_mod_cast Nat.le_add_right C₀ Cind
  have hC2 : ((Cind : ℕ) : V) ≤ ((C₀ + Cind : ℕ) : V) := by exact_mod_cast Nat.le_add_left Cind C₀
  have hC0 : ((C₀ : ℕ) : V) ≤ entryB ((C₀ + Cind : ℕ) : V) p := by
    unfold entryB; exact le_trans hC1 (le_mul_of_one_le_right zero_le h1p)
  have hCi : entryB ((Cind : ℕ) : V) p ≤ entryB ((C₀ + Cind : ℕ) : V) p := entryB_mono hC2 p
  have hΓ : IsFormulaSet LAct (dossCtx walkPieces p ip) := isFormulaSet_dossCtx htbl hT.walkTable hp ip
  rcases mem_TAct_class_cases hax with ⟨σ, hσ, rfl⟩ | ⟨hF, hI⟩
  · have hE₀ : ((C₀ : ℕ) : V) + ip ≤ E :=
      le_trans (add_le_add (by unfold entryB at hC0; exact hC0) le_rfl) hE
    obtain ⟨P, hok, hnd, hsh, hlen, hsz, hmem⟩ := hC σ hσ V htbl hT hΓ (dossF_dossCtx _ _ _) hE₀
    refine ⟨P, hok, hnd, ?_, le_trans hlen hC0, hsz.mono hC0 hC0, ?_⟩
    · rw [hsh]; exact zero_le
    · rw [hsh, add_zero]; exact hmem
  · have hE₁ : ((Cind : ℕ) : V) * p3 (formulaLen LAct p + 1) + ip ≤ E :=
      le_trans (add_le_add (mul_le_mul_of_nonneg_right hC2 zero_le) le_rfl) hE
    obtain ⟨P, hok, hnd, hsh, hlen, hsz, hmem⟩ := hind p ip hF hI hE₁
    exact ⟨P, hok, hnd, le_trans hsh hCi, le_trans hlen hCi, hsz.mono hCi hCi, hmem⟩

/-- The E-room passes to a child: `dlen d' + 1 ≤ dlen ρ`. -/
lemma eroom_child' {Cv E a b : V} (h : Cv * p3 (a + 1) + 6 * a + 1 ≤ E) (hab : b + 1 ≤ a) :
    Cv * p3 (b + 1) + 6 * b + 1 ≤ E :=
  le_trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (p3_mono (le_trans hab le_self_add)) zero_le)
    (mul_le_mul_of_nonneg_left (le_trans le_self_add hab) zero_le)) (le_refl 1)) h

set_option maxHeartbeats 2000000 in
/-- **Every internal derivation has a verification list** (per model), the certificate table `A` built from case (i) and
the oracle `AxmIndOracleC' tbl E Cind` (case (ii)): by `Derivation.induction1 𝚺`, the children's tables united
(`mono_A`), the children's lists spliced by the assemblers; the E-room `Cv·(dlen ρ + 1)³ + 6·dlen ρ + 1 ≤ E` is what the
`axm` entries need (`memTop ≤ 6·setLen s + 1`, `|p| + 1 ≤ setLen s + 1 = dlen (axm s p)`). -/
theorem verifyGraph''_exists' : ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {tbl N E Ww Wl Wc W₁ W₂ W T ρ Cv : V} (Cind : ℕ), TableOK tbl N → ProAxmTable tbl → Ww = walkPieces → Wc = certPieces →
    Cv = ((C + Cind : ℕ) : V) → Derivation TAct ρ → Cv * p3 (dlen TAct ρ + 1) + 6 * dlen TAct ρ + 1 ≤ E →
    AxmIndOracleC' tbl E Cind →
    ∃ A L : V, AxmTableOK' tbl E Ww A Cv ∧ VerifyGraph'' Ww Wl Wc W₁ W₂ W T A ρ L := by
  obtain ⟨C, hC⟩ := axmEntry_exists'
  refine ⟨C, fun V _ _ tbl N E Ww Wl Wc W₁ W₂ W T ρ Cv Cind htbl hT hWw hWc hCv hd hE hind ↦ ?_⟩
  revert hE
  apply Derivation.induction1 𝚺 (T := TAct)
    (P := fun ρ ↦ Cv * p3 (dlen TAct ρ + 1) + 6 * dlen TAct ρ + 1 ≤ E →
      ∃ A L : V, AxmTableOK' tbl E Ww A Cv ∧ VerifyGraph'' Ww Wl Wc W₁ W₂ W T A ρ L)
    (by simp only [VerifyGraph'', p3]; definability) hd
  · intro s _ p _ _ _
    exact ⟨0, _, axmTableOK'_empty _ _ _ _, VerifyGraph''.axL_iff.mpr rfl⟩
  · intro s _ _ _
    exact ⟨0, _, axmTableOK'_empty _ _ _ _, VerifyGraph''.verumIntro_iff.mpr rfl⟩
  · intro s _ p q dp dq hpq hdp hdq ih₁ ih₂ hE
    have hD : Derivation TAct (andIntro s p q dp dq) := Derivation.andIntro hpq hdp hdq
    obtain ⟨A₁, L₁, h₁, g₁⟩ := ih₁ (eroom_child' hE (dlen_dp_succ_le_andIntro hD))
    obtain ⟨A₂, L₂, h₂, g₂⟩ := ih₂ (eroom_child' hE (dlen_dq_succ_le_andIntro hD))
    exact ⟨A₁ ∪ A₂, _, axmTableOK'_union h₁ h₂, VerifyGraph''.andIntro_iff.mpr
      ⟨L₁, le_vAnd_left _ _ _ _ _ _ _ _ _ _ _ _ _, g₁.mono_A (subset_cup_left _ _),
       L₂, le_vAnd_right _ _ _ _ _ _ _ _ _ _ _ _ _, g₂.mono_A (subset_cup_right _ _), rfl⟩⟩
  · intro s _ p q d' hpq hd' ih hE
    have hD : Derivation TAct (orIntro s p q d') := Derivation.orIntro hpq hd'
    obtain ⟨A', L', h', g'⟩ := ih (eroom_child' hE (dlen_d_succ_le_orIntro hD))
    exact ⟨A', _, h', VerifyGraph''.orIntro_iff.mpr ⟨L', le_vOr _ _ _ _ _ _ _ _ _ _ _, g', rfl⟩⟩
  · intro s _ p d' hp hd' ih hE
    have hD : Derivation TAct (allIntro s p d') := Derivation.allIntro hp hd'
    obtain ⟨A', L', h', g'⟩ := ih (eroom_child' hE (dlen_d_succ_le_allIntro hD))
    exact ⟨A', _, h', VerifyGraph''.allIntro_iff.mpr ⟨L', le_vAll _ _ _ _ _ _ _ _ _ _, g', rfl⟩⟩
  · intro s _ p t d' hp ht hd' ih hE
    have hD : Derivation TAct (exsIntro s p t d') := Derivation.exsIntro hp ht hd'
    obtain ⟨A', L', h', g'⟩ := ih (eroom_child' hE (dlen_d_succ_le_exsIntro hD))
    exact ⟨A', _, h', VerifyGraph''.exsIntro_iff.mpr ⟨L', le_vExs _ _ _ _ _ _ _ _ _ _ _, g', rfl⟩⟩
  · intro s hs d' hsub hd' ih hE
    have hD : Derivation TAct (wkRule s d') := Derivation.wkRule hs hsub ⟨rfl, hd'⟩
    obtain ⟨A', L', h', g'⟩ := ih (eroom_child' hE (dlen_d_succ_le_wkRule hD))
    exact ⟨A', _, h', VerifyGraph''.wkRule_iff.mpr ⟨L', le_vWk _ _ _ _ _ _ _ _ _, g', rfl⟩⟩
  · rintro s _ d' rfl hd' ih hE
    have hD : Derivation TAct (shiftRule (setShift LAct (fstIdx d')) d') := Derivation.shiftRule ⟨rfl, hd'⟩
    obtain ⟨A', L', h', g'⟩ := ih (eroom_child' hE (dlen_d_succ_le_shiftRule hD))
    exact ⟨A', _, h', VerifyGraph''.shiftRule_iff.mpr ⟨L', le_vShift _ _ _ _ _ _ _ _ _, g', rfl⟩⟩
  · intro s _ p d₁ d₂ hd₁ hd₂ ih₁ ih₂ hE
    have hD : Derivation TAct (cutRule s p d₁ d₂) := Derivation.cutRule hd₁ hd₂
    obtain ⟨A₁, L₁, h₁, g₁⟩ := ih₁ (eroom_child' hE (dlen_d₁_succ_le_cutRule hD))
    obtain ⟨A₂, L₂, h₂, g₂⟩ := ih₂ (eroom_child' hE (dlen_d₂_succ_le_cutRule hD))
    exact ⟨A₁ ∪ A₂, _, axmTableOK'_union h₁ h₂, VerifyGraph''.cutRule_iff.mpr
      ⟨L₁, le_vCut_left _ _ _ _ _ _ _ _ _ _ _ _, g₁.mono_A (subset_cup_left _ _),
       L₂, le_vCut_right _ _ _ _ _ _ _ _ _ _ _ _, g₂.mono_A (subset_cup_right _ _), rfl⟩⟩
  · intro s hs p hp hax hE
    have hD : Derivation TAct (axm s p) := Derivation.axm hs hp hax
    have hpf : IsSemiformula LAct 0 p := hs p hp
    have hip : memTop Ww Wc T s p 0 ≤ 6 * setLen LAct s + 1 := by
      rw [hWw]
      have := memTop_le htbl hT.walkTable hWc T hs hp (le_refl (setLen LAct s)) (i := 0)
      rwa [zero_add] at this
    have hpd : formulaLen LAct p + 1 ≤ dlen TAct (axm s p) + 1 := by
      rw [dlen_axm hD]; exact add_le_add (le_trans (formulaLen_le_setLen_of_mem (L := LAct) hp) le_self_add) le_rfl
    have hmt : memTop Ww Wc T s p 0 ≤ 6 * dlen TAct (axm s p) + 1 := by
      rw [dlen_axm hD]
      exact le_trans hip (add_le_add (mul_le_mul_of_nonneg_left le_self_add zero_le) (le_refl 1))
    have hEip : ((C + Cind : ℕ) : V) * p3 (formulaLen LAct p + 1) + memTop Ww Wc T s p 0 ≤ E := by
      rw [← hCv]
      calc Cv * p3 (formulaLen LAct p + 1) + memTop Ww Wc T s p 0
          ≤ Cv * p3 (dlen TAct (axm s p) + 1) + (6 * dlen TAct (axm s p) + 1) :=
            add_le_add (mul_le_mul_of_nonneg_left (p3_mono hpd) zero_le) hmt
        _ = Cv * p3 (dlen TAct (axm s p) + 1) + 6 * dlen TAct (axm s p) + 1 := by ring
        _ ≤ E := hE
    obtain ⟨pro, hok, hnd, hsh, hlen, hsz, hmem⟩ := hC V Cind htbl hT hpf hax hEip hind
    have hentry : ListOK tbl E ((9 : ℕ) : V) (dossCtx Ww p (memTop Ww Wc T s p 0)) pro ∧ NoDrop' pro ∧
        shiftsV pro ≤ entryB Cv p ∧ len pro ≤ entryB Cv p ∧ SizeOK (entryB Cv p) (entryB Cv p) pro ∧
        neg LAct (axchFact (^&(memTop Ww Wc T s p 0 + shiftsV pro))) ∈ finalCtx (dossCtx Ww p (memTop Ww Wc T s p 0)) pro := by
      subst hCv hWw
      exact ⟨hok, hnd, hsh, hlen, hsz, hmem⟩
    exact ⟨insert ⟪p, memTop Ww Wc T s p 0, pro⟫ (0 : V), vAxm' Ww Wc W₂ T s p pro,
      axmTableOK'_insert (axmTableOK'_empty _ _ _ _) hentry,
      VerifyGraph''.axm_iff.mpr ⟨pro, le_vAxm' _ _ _ _ _ _ _, mem_bitInsert_iff.mpr (Or.inl rfl), rfl⟩⟩

/-- **THE UNCONDITIONAL EXISTENCE THEOREM**: at any `IndRecTable`, every internal derivation has a shifted certificate
table and a verification list — NO oracle hypothesis (`Verify2.AxmIndOracleC` and `ProAxm.AxmIndOracle` retired:
`axmIndOracleC'_of_indRec` discharges case (ii) from the recognizer). -/
theorem verifyGraph''_exists_unconditional : ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {tbl N E Ww Wl Wc W₁ W₂ W T ρ Cv : V}, TableOK tbl N → IndRecTable tbl → Ww = walkPieces → Wc = certPieces →
    Cv = (C : V) → Derivation TAct ρ → Cv * p3 (dlen TAct ρ + 1) + 6 * dlen TAct ρ + 1 ≤ E →
    ∃ A L : V, AxmTableOK' tbl E Ww A Cv ∧ VerifyGraph'' Ww Wl Wc W₁ W₂ W T A ρ L := by
  obtain ⟨C, hC⟩ := verifyGraph''_exists'
  exact ⟨C + 1400, fun V _ _ tbl N E Ww Wl Wc W₁ W₂ W T ρ Cv htbl hT hWw hWc hCv hd hE ↦
    hC V 1400 htbl hT.proAxmTable hWw hWc hCv hd hE (axmIndOracleC'_of_indRec htbl hT)⟩

end existence'

/-! ## 5. The node invariant: `vAxm_ok'` and the glue `verifyGraph''_ok` -/

section leaves'

/-- **The shifted `axm` list is applicable**, given a shifted certificate for `p` at `ip = memTop s p 0` (transferred
from the canonical dossier context by `listOK_mono_subset`; the layout carried to the moved offset `shiftsV pro` by
`Layout.transport`, the `vAll`/`vExs` reading). -/
theorem vAxm_ok' {tbl N N' B' Wc W₂ T s p pro D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWc : Wc = certPieces) (hW₂ : W₂ = frag2Pieces)
    (hs : IsFormulaSet LAct s) (hp : p ∈ s) (hax : p ∈ TAct.Δ₁Class) (hsD : setLen LAct s ≤ D)
    (hiE : shiftsV pro + 6 * D + 3 ≤ E) (hkE : shiftsV pro + len (memberList s) + 3 ≤ E) (hlE : shiftsV pro + 4 ≤ E)
    (hn : 18 * ‖setLen LAct s + 1‖ + 7 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s 0)
    (hpro : ListOK tbl E ((9 : ℕ) : V) (dossCtx walkPieces p (memTop walkPieces Wc T s p 0)) pro ∧ NoDrop' pro ∧
      neg LAct (axchFact (^&(memTop walkPieces Wc T s p 0 + shiftsV pro))) ∈
        finalCtx (dossCtx walkPieces p (memTop walkPieces Wc T s p 0)) pro) :
    ListOK tbl E ((9 : ℕ) : V) Γ (vAxm' walkPieces Wc W₂ T s p pro) ∧ NoDrop' (vAxm' walkPieces Wc W₂ T s p pro) ∧
    shiftsV (vAxm' walkPieces Wc W₂ T s p pro) = shiftsV pro + 1 ∧
    neg LAct (goalFact (^&(len (memberList s) + 1 + shiftsV pro + 1)) (bnum (dlen TAct (axm s p)))) ∈
      finalCtx Γ (vAxm' walkPieces Wc W₂ T s p pro) := by
  have hW : WalkTable tbl := hP.walkTable
  have hD : Derivation TAct (axm s p) := Derivation.axm hs hp hax
  have hdl : dlen TAct (axm s p) = setLen LAct s + 1 := dlen_axm hD
  obtain ⟨pok, pnd, pax⟩ := hpro
  obtain ⟨hDp, -, -, -⟩ := Layout.member hLay hp
  have hsub : dossCtx walkPieces p (memTop walkPieces Wc T s p 0) ⊆ Γ := dossCtx_subset hDp
  have pok' : ListOK tbl E ((9 : ℕ) : V) Γ pro := listOK_mono_subset 9 htbl hΓ pnd hsub pok
  have pax' : neg LAct (axchFact (^&(memTop walkPieces Wc T s p 0 + shiftsV pro))) ∈ finalCtx Γ pro :=
    finalCtx_mono' pnd hsub pax
  rw [← memTop_add] at pax'
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ pro := ⟨_, rfl⟩
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 9 htbl hΓ pok'
  have hLay₁ : Layout walkPieces Wc T Γ₁ s (shiftsV pro) := by
    rw [hΓ₁]; have := Layout.transport pnd hLay; rwa [zero_add] at this
  have hfs := hLay₁.fsetPi (one_le_len_memberList_of_mem hp)
  have hsl := hLay₁.2.1
  have hle := hLay₁.2.2
  obtain ⟨-, -, -, hmp'⟩ := Layout.member hLay₁ hp
  rw [add_comm (shiftsV pro) (len (memberList s) + 1)] at hfs hsl hmp'
  rw [← hΓ₁] at pax'
  have hmt : memTop walkPieces Wc T s p (shiftsV pro) ≤ shiftsV pro + 6 * D + 1 := memTop_le htbl hW hWc T hs hp hsD
  have hn' : 18 * ‖dlen TAct (axm s p)‖ + 7 ≤ E := by rw [hdl]; exact hn
  have hLn' : setLen LAct s + 1 ≤ dlen TAct (axm s p) := by rw [hdl]
  obtain ⟨fok, fnd, fsh, -, fgoal⟩ := nodeAxm_ok (E := E) (is := len (memberList s) + 1 + shiftsV pro) (il := shiftsV pro)
    (ip := memTop walkPieces Wc T s p (shiftsV pro)) (L := setLen LAct s) (n := dlen TAct (axm s p))
    htbl hP.frag2Table hW₂ htblN hΓ₁f
    (le_trans (le_of_eq (by ring)) hkE) hlE
    (le_trans (add_le_add hmt (le_refl 2)) (le_trans (le_of_eq (by ring)) hiE))
    hn' hLn' hfs hmp' pax' hsl hle
  unfold vAxm'
  refine ⟨listOK_appendV pok' (by rw [← hΓ₁]; exact fok.mono h89), noDrop'_appendV pnd fnd, ?_, ?_⟩
  · rw [shiftsV_appendV, fsh]
  · rw [finalCtx_appendV, ← hΓ₁]; exact fgoal

end leaves'

section glueMain'

set_option maxHeartbeats 20000000 in
/-- **The node invariant for `VerifyGraph''`** (`Verify2.verifyGraph'_ok` with SHIFTED `axm` certificates): at a node laid
out at offset `0`, every verification list is applicable at cap `9`, cut-admitting, has at most `(Cs + Cv)·(dlen ρ)^6`
eigenvariables, and leaves the node's goal fact at `&(k + 1 + shiftsV L)`. The E-room is `(Ck + 5·Cv)·(dlen ρ + 1)^6 ≤ E`.
The degree stays 6 (`m = 6`): the `axm` leaf's shift `shiftsV pro + 1 ≤ Cv·(|p|+1)³ + 1 ≤ (Cv + 1)·d^6` (`|p| + 1 ≤ d =
setLen s + 1`) fits the budget once the shift constant absorbs `Cv`; the other nine cases are `Verify2.lean` §8.9 verbatim
at the constants `Csv = 500000 + Cv`, `Ckv = 2500000 + 5·Cv`. -/
theorem verifyGraph''_ok : ∃ Cs Ck : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {tbl N N' B' Ww Wl Wc W₁ W₂ W T A Cv E ρ : V},
    TableOK tbl N → ProTable tbl → NumTableOK T N' B' → Ww = walkPieces → Wl = layoutPieces → Wc = certPieces →
    W₁ = frag1Pieces → W₂ = frag2Pieces → W = proPieces → AxmTableOK' tbl E Ww A Cv → Derivation TAct ρ →
    (((Ck : ℕ) : V) + 5 * Cv) * p6 (dlen TAct ρ + 1) ≤ E →
    ∀ L Γ : V, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A ρ L → IsFormulaSet LAct Γ → NodeLay Ww Wc T Γ (fstIdx ρ) →
      ListOK tbl E ((9 : ℕ) : V) Γ L ∧ NoDrop' L ∧ shiftsV L ≤ (((Cs : ℕ) : V) + Cv) * p6 (dlen TAct ρ) ∧
      neg LAct (goalFact (^&(len (memberList (fstIdx ρ)) + 1 + shiftsV L)) (bnum (dlen TAct ρ))) ∈ finalCtx Γ L := by
  refine ⟨500000, 2500000, fun V _ _ tbl N N' B' Ww Wl Wc W₁ W₂ W T A Cv E ρ htbl hP htblN hWw hWl hWc hW₁ hW₂ hWp hA hd ↦ ?_⟩
  obtain ⟨Csv, hCsv⟩ : ∃ x : V, x = ((500000 : ℕ) : V) + Cv := ⟨_, rfl⟩
  obtain ⟨Ckv, hCkv⟩ : ∃ x : V, x = ((2500000 : ℕ) : V) + 5 * Cv := ⟨_, rfl⟩
  rw [← hCsv, ← hCkv]
  have hCs1 : (1 : V) ≤ Csv := by
    rw [hCsv]; exact le_trans (b := ((500000 : ℕ) : V)) (by exact_mod_cast (by norm_num : 1 ≤ 500000)) le_self_add
  have hCs' : (460803 : V) ≤ Csv := by
    rw [hCsv]; exact le_trans (b := ((500000 : ℕ) : V)) (by exact_mod_cast (by norm_num : 460803 ≤ 500000)) le_self_add
  have hCk : ∀ a : ℕ, a ≤ 2500000 → ((a : ℕ) : V) ≤ Ckv := fun a ha ↦ by
    rw [hCkv]; exact le_trans (b := ((2500000 : ℕ) : V)) (by exact_mod_cast ha) le_self_add
  have hCsCk : 5 * Csv ≤ Ckv := by rw [hCsv, hCkv]; exact le_of_eq (by push_cast; ring)
  have hCv1 : Cv + 1 ≤ Csv := by
    rw [hCsv]
    calc Cv + 1 ≤ Cv + ((500000 : ℕ) : V) := add_le_add le_rfl (by exact_mod_cast (by norm_num : 1 ≤ 500000))
      _ = ((500000 : ℕ) : V) + Cv := add_comm _ _
  have hCv9 : Cv + 9 ≤ Ckv := by
    rw [hCkv]
    calc Cv + 9 ≤ 5 * Cv + ((2500000 : ℕ) : V) :=
          add_le_add (le_mul_of_one_le_left zero_le (by norm_num : (1 : V) ≤ 5)) (by exact_mod_cast (by norm_num : 9 ≤ 2500000))
      _ = ((2500000 : ℕ) : V) + 5 * Cv := add_comm _ _
  subst hWw
  apply Derivation.induction1 𝚷 (T := TAct)
    (P := fun ρ ↦ Ckv * p6 (dlen TAct ρ + 1) ≤ E → ∀ L Γ : V, VerifyGraph'' walkPieces Wl Wc W₁ W₂ W T A ρ L →
      IsFormulaSet LAct Γ → NodeLay walkPieces Wc T Γ (fstIdx ρ) →
      ListOK tbl E ((9 : ℕ) : V) Γ L ∧ NoDrop' L ∧ shiftsV L ≤ Csv * p6 (dlen TAct ρ) ∧
      neg LAct (goalFact (^&(len (memberList (fstIdx ρ)) + 1 + shiftsV L)) (bnum (dlen TAct ρ))) ∈ finalCtx Γ L)
    (by simp only [VerifyGraph'', p6]; definability) hd
  · -- axL
    intro s hs p hp hnp hE L Γ hL hΓ hLay
    rw [VerifyGraph''.axL_iff] at hL; subst hL
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
    rw [VerifyGraph''.verumIntro_iff] at hL; subst hL
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
    rw [VerifyGraph''.andIntro_iff] at hL
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
    have h138 : (138 : V) ≤ 2 * Csv := by rw [hCsv]; exact le_trans (b := 2 * ((500000 : ℕ) : V)) (by exact_mod_cast (by norm_num : 138 ≤ 2 * 500000)) (mul_le_mul_of_nonneg_left le_self_add zero_le)
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
      rw [hCsv]; exact le_trans (b := ((500000 : ℕ) : V)) (by exact_mod_cast (by norm_num : 12 + 9 ≤ 500000)) le_self_add)
    calc 12 * d + Csv * p6 y₁ + Csv * p6 y₂ + 9 = (12 * d + 9) + Csv * p6 y₁ + Csv * p6 y₂ := by ring
      _ ≤ Csv * p6 d := rec2 le_add_self hdeq hX
  · -- orIntro
    intro s hs p q d' hpq hd' ih hE L Γ hL hΓ hLay
    rw [VerifyGraph''.orIntro_iff] at hL
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
    have h98 : (98 : V) ≤ 4 * Csv := by rw [hCsv]; exact le_trans (b := 4 * ((500000 : ℕ) : V)) (by exact_mod_cast (by norm_num : 98 ≤ 4 * 500000)) (mul_le_mul_of_nonneg_left le_self_add zero_le)
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
      rw [hCsv]; exact le_trans (b := ((500000 : ℕ) : V)) (by exact_mod_cast (by norm_num : 12 + 7 ≤ 500000)) le_self_add)
    calc 12 * d + Csv * p6 y + 7 = (12 * d + 7) + Csv * p6 y := by ring
      _ ≤ Csv * p6 d := rec1 le_add_self hdeq hX
  · -- allIntro
    intro s hs p d' hr hd' ih hE L Γ hL hΓ hLay
    rw [VerifyGraph''.allIntro_iff] at hL
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
    have h14596 : (14596 : V) ≤ 4 * Csv := by rw [hCsv]; exact le_trans (b := 4 * ((500000 : ℕ) : V)) (by exact_mod_cast (by norm_num : 14596 ≤ 4 * 500000)) (mul_le_mul_of_nonneg_left le_self_add zero_le)
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
    rw [VerifyGraph''.exsIntro_iff] at hL
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
    have h29076 : (29076 : V) ≤ 3 * Csv := by rw [hCsv]; exact le_trans (b := 3 * ((500000 : ℕ) : V)) (by exact_mod_cast (by norm_num : 29076 ≤ 3 * 500000)) (mul_le_mul_of_nonneg_left le_self_add zero_le)
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
    rw [VerifyGraph''.wkRule_iff] at hL
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
    have h98 : (98 : V) ≤ 4 * Csv := by rw [hCsv]; exact le_trans (b := 4 * ((500000 : ℕ) : V)) (by exact_mod_cast (by norm_num : 98 ≤ 4 * 500000)) (mul_le_mul_of_nonneg_left le_self_add zero_le)
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
      rw [hCsv]; exact le_trans (b := ((500000 : ℕ) : V)) (by exact_mod_cast (by norm_num : 7 + 8 ≤ 500000)) le_self_add)
    calc 7 * d + Csv * p6 y + 8 = (7 * d + 8) + Csv * p6 y := by ring
      _ ≤ Csv * p6 d := rec1 le_add_self hdeq hX
  · -- shiftRule
    intro s hs d' hsc hd' ih hE L Γ hL hΓ hLay
    rw [VerifyGraph''.shiftRule_iff] at hL
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
    have h98 : (98 : V) ≤ 4 * Csv := by rw [hCsv]; exact le_trans (b := 4 * ((500000 : ℕ) : V)) (by exact_mod_cast (by norm_num : 98 ≤ 4 * 500000)) (mul_le_mul_of_nonneg_left le_self_add zero_le)
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
      rw [hCsv]; exact le_trans (b := ((500000 : ℕ) : V)) (by exact_mod_cast (by norm_num : 7 + 8 ≤ 500000)) le_self_add)
    calc 7 * d + Csv * p6 y + 8 = (7 * d + 8) + Csv * p6 y := by ring
      _ ≤ Csv * p6 d := rec1 le_add_self hdeq hX
  · -- cutRule
    intro s hs p d₁ d₂ hd₁ hd₂ ih₁ ih₂ hE L Γ hL hΓ hLay
    rw [VerifyGraph''.cutRule_iff] at hL
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
    have h138 : (138 : V) ≤ 2 * Csv := by rw [hCsv]; exact le_trans (b := 2 * ((500000 : ℕ) : V)) (by exact_mod_cast (by norm_num : 138 ≤ 2 * 500000)) (mul_le_mul_of_nonneg_left le_self_add zero_le)
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
      rw [hCsv]; exact le_trans (b := ((500000 : ℕ) : V)) (by exact_mod_cast (by norm_num : 20 + 9 ≤ 500000)) le_self_add)
    calc 20 * d + Csv * p6 y₁ + Csv * p6 y₂ + 9 = (20 * d + 9) + Csv * p6 y₁ + Csv * p6 y₂ := by ring
      _ ≤ Csv * p6 d := rec2 le_add_self hdeq hX
  · -- axm
    intro s hs p hps hpT hE L Γ hL hΓ hLay
    rw [VerifyGraph''.axm_iff] at hL
    obtain ⟨pro, -, hmem, rfl⟩ := hL
    rw [fstIdx_axm] at hLay ⊢
    obtain ⟨p', -, ip', -, pro', -, heq, hok, hnd, hsh, -, -, hfact⟩ := hA _ hmem
    obtain ⟨e₁, heq₂⟩ := pair_ext_iff.mp heq
    obtain ⟨e₂, e₃⟩ := pair_ext_iff.mp heq₂
    subst e₁; subst e₂; subst e₃
    have hD : Derivation TAct (axm s p) := Derivation.axm hs hps hpT
    have hd1 : 1 ≤ dlen TAct (axm s p) := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (axm s p) := by have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_axm] at this
    have hkD : len (memberList s) ≤ dlen TAct (axm s p) := le_trans (len_memberList_le_setLen hs) hsD
    have hpd : formulaLen LAct p + 1 ≤ dlen TAct (axm s p) := by
      rw [dlen_axm hD]; exact add_le_add (formulaLen_le_setLen_of_mem (L := LAct) hps) le_rfl
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (axm s p) := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hkD hpd
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    -- the entry's shift under the budget
    have hσ : shiftsV pro ≤ Cv * p6 d := le_trans hsh (by
      unfold entryB; exact mul_le_mul_of_nonneg_left (le_trans (p3_mono hpd) (p3_le_p6 hd1)) zero_le)
    have hσE : shiftsV pro ≤ Cv * p6 (d + 1) := le_trans hσ (child_bound le_self_add)
    have capσ : ∀ {X c : V}, c ≤ 9 → X ≤ shiftsV pro + c * (d + 1) → X ≤ E := fun {X c} hc hX ↦ by
      refine le_trans hX (le_trans ?_ hE)
      calc shiftsV pro + c * (d + 1) ≤ Cv * p6 (d + 1) + 9 * p6 (d + 1) :=
            add_le_add hσE (mul_le_mul hc (le_p6_self he1) zero_le zero_le)
        _ = (Cv + 9) * p6 (d + 1) := by ring
        _ ≤ Ckv * p6 (d + 1) := mul_le_mul_of_nonneg_right hCv9 zero_le
    have hn : 18 * ‖setLen LAct s + 1‖ + 7 ≤ 43 * (d + 1) := by
      have h1 : ‖setLen LAct s + 1‖ ≤ d + 1 := le_trans (length_le _) (add_le_add hsD (le_refl 1))
      calc 18 * ‖setLen LAct s + 1‖ + 7 ≤ 18 * (d + 1) + 7 := add_le_add (mul_le_mul_of_nonneg_left h1 zero_le) (le_refl 7)
        _ ≤ 43 * (d + 1) := le_of_add_eq' (c := 25 * d + 18) (by ring)
    have hiE' : shiftsV pro + 6 * d + 3 ≤ E := capσ (c := 9) le_rfl (by
      rw [add_assoc]; exact add_le_add le_rfl (le_of_add_eq' (c := 3 * d + 6) (by ring)))
    have hkE' : shiftsV pro + len (memberList s) + 3 ≤ E := capσ (c := 9) le_rfl (by
      rw [add_assoc]; exact add_le_add le_rfl (le_trans (add_le_add hkD le_rfl) (le_of_add_eq' (c := 8 * d + 6) (by ring))))
    have hlE' : shiftsV pro + 4 ≤ E := capσ (c := 9) le_rfl (add_le_add le_rfl (le_of_add_eq' (c := 9 * d + 5) (by ring)))
    obtain ⟨ok, nd, sh, goal⟩ := vAxm_ok' (D := d) htbl hP htblN hWc hW₂ hs hps hpT hsD hiE' hkE' hlE'
      (capE hE he1 (hCk 43 (by norm_num)) (by push_cast; exact hn)) hΓ hLay.layout ⟨hok, hnd, hfact⟩
    refine ⟨ok, nd, ?_, ?_⟩
    · rw [sh, ← hdd]
      calc shiftsV pro + 1 ≤ Cv * p6 d + 1 * p6 d :=
            add_le_add hσ (le_mul_of_one_le_right zero_le (le_trans hd1 (le_p6_self hd1)))
        _ = (Cv + 1) * p6 d := by ring
        _ ≤ Csv * p6 d := mul_le_mul_of_nonneg_right hCv1 zero_le
    · rw [sh, ← add_assoc]; exact goal


end glueMain'

/-! ### 5.1 The kit-facing form: `(dlen ρ + 1)^6`, the constant `Ck·(Cv + 1)` -/

section kitForm'

/-- `verifyGraph''_ok` restated with the `VerifyKit''`-style multiplier `(dlen ρ + 1)^6` and ONE constant `Ck·(Cv + 1)`
(`Cv` the table's constant; `verifyGraph''_exists_unconditional` supplies a standard one). -/
theorem verifyGraph''_ok_pow : ∃ Ck : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {tbl N N' B' Ww Wl Wc W₁ W₂ W T A Cv E ρ : V},
    TableOK tbl N → ProTable tbl → NumTableOK T N' B' → Ww = walkPieces → Wl = layoutPieces → Wc = certPieces →
    W₁ = frag1Pieces → W₂ = frag2Pieces → W = proPieces → AxmTableOK' tbl E Ww A Cv → Derivation TAct ρ →
    (Ck : V) * (Cv + 1) * (dlen TAct ρ + 1) ^ 6 ≤ E →
    ∀ L Γ : V, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A ρ L → IsFormulaSet LAct Γ → NodeLay Ww Wc T Γ (fstIdx ρ) →
      ListOK tbl E ((9 : ℕ) : V) Γ L ∧ NoDrop' L ∧ shiftsV L ≤ (Ck : V) * (Cv + 1) * (dlen TAct ρ + 1) ^ 6 ∧
      neg LAct (goalFact (^&(len (memberList (fstIdx ρ)) + 1 + shiftsV L)) (bnum (dlen TAct ρ))) ∈ finalCtx Γ L := by
  obtain ⟨Cs, Ck, h⟩ := verifyGraph''_ok
  refine ⟨Cs + Ck + 5, fun V _ _ tbl N N' B' Ww Wl Wc W₁ W₂ W T A Cv E ρ htbl hP htblN hWw hWl hWc hW₁ hW₂ hWp hA hd hE
    L Γ hL hΓ hLay ↦ ?_⟩
  have hp : (dlen TAct ρ + 1) ^ 6 = p6 (dlen TAct ρ + 1) := by simp only [p6]; ring
  rw [hp] at hE ⊢
  have hE' : (((Ck : ℕ) : V) + 5 * Cv) * p6 (dlen TAct ρ + 1) ≤ E := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ zero_le) hE
    push_cast
    exact le_of_add_eq' (c := ((Cs : V) + Ck) * Cv + Cs + 5) (by ring)
  obtain ⟨ok, nd, sh, goal⟩ := h V htbl hP htblN hWw hWl hWc hW₁ hW₂ hWp hA hd hE' L Γ hL hΓ hLay
  refine ⟨ok, nd, ?_, goal⟩
  refine le_trans sh (mul_le_mul ?_ (p6_mono le_self_add) zero_le zero_le)
  push_cast
  exact le_of_add_eq' (c := ((Cs : V) + Ck + 4) * Cv + Ck + 5) (by ring)

end kitForm'

end ArithS
