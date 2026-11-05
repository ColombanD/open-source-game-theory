import ArithS.Cells.Dimdid

/-!
# ArithS.Cells.SelfDual — two floors closed by τ-symmetry: `DIMDID × CIMCIC = (C, D)`, and one question for two

`DIMDID k` is the C/D transposition of `CIMCIC k` (`(CIMCIC k).transpose = DIMDID k`, by `rfl`), and the box does
not see τ (`Theory/Symmetry.lenBoxNat_swap_iff`: a proof transposes into a proof of the same length). On the
engine's guard codes that is `lenBox_guardCode_transpose`: the guard `φ` is found in the frame `(me, opp)` iff
`φ.transpose` is found in the frame `(me.transpose, opp.transpose)`, at the same budget.

1. **`DIMDID × CIMCIC = (C, D)` at EVERY budget — the red cell's argument** (`snd_DIMDID_vs_CIMCIC`). The pair is
   self-dual, so DIMDID's guard `A` ("if I defect, CIMCIC defects") and CIMCIC's guard `B` ("if I cooperate, DIMDID
   cooperates") are τ-images of each other: `A ↔ B` (`guard_DIMDID_iff_guard_CIMCIC`). If both were found, DIMDID
   would defect (its then-branch), and CIMCIC's guard against a defector is self-refuting
   (`cimcic_selfref_not_found`: a proof of it makes CIMCIC cooperate, and by soundness DIMDID then cooperates).
   So NEITHER is found; both play their else-branch: DIMDID cooperates, CIMCIC defects. No Löb, no threshold.
   Until 2026-11-05 this was a two-hinge floor (`dich_DIMDID_vs_CIMCIC`, three outcomes); its value is the one the
   ledger already carried on the engine side, now a theorem.

2. **`DIMDID × Dupoc` and `CIMCIC × Cupod` are ONE floor** (`guards_DIMDID_DupocBot_iff_CIMCIC_CupodBot`,
   `outcomeAtA_DIMDID_vs_DupocBot_iff`): the second pair is the transposition of the first, so their two hinges
   coincide pairwise and their outcomes are transposes of each other at every budget. Neither is decided here —
   there is no symmetry BETWEEN the two hinges of one pair — but whatever settles one settles the other.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct
open PD.Bots

/-! ### 1. The box does not see τ, on the engine's guard codes -/

/-- τ on a realized fragment formula (`Tau/Columns.lMap_swap_sentenceAt`, restated below the tau layer). -/
theorem lMap_swap_sentenceAt_frag {me opp : PD.Prog} (hme : fragP me = true) (hopp : fragP opp = true)
    (φ : PD.Formula) (hφ : fragF φ = true) :
    Semiformula.lMap swap (sentenceAt me opp φ) = sentenceAt me.transpose opp.transpose φ.transpose := by
  unfold sentenceAt
  rw [Semiformula.lMap_subst, lMap_swap_template φ hφ]
  congr 1
  funext i
  fin_cases i <;> simp [descriptionTerms, lMap_swap_canonicalMeta, lMap_swap_revalueUMeta, lMap_swap_revalueWMeta,
    transposeCode_progCode me hme, transposeCode_progCode opp hopp]

/-- **A guard is found iff its transposition is found in the transposed frame**, at the same budget. -/
theorem lenBox_guardCode_transpose {me opp : PD.Prog} (hme : fragP me = true) (hopp : fragP opp = true)
    (φ : PD.Formula) (hφ : fragF φ = true) (hns : noSelfIdxF φ = true) (hnsT : noSelfIdxF φ.transpose = true)
    (k : ℕ) :
    LenBox TAct k (guardCode (templateCode φ) (progCode me) (progCode opp)) ↔
    LenBox TAct k (guardCode (templateCode φ.transpose) (progCode me.transpose) (progCode opp.transpose)) := by
  rw [← quote_sentenceAt me opp φ hns, ← quote_sentenceAt me.transpose opp.transpose φ.transpose hnsT,
    lenBox_nat, lenBox_nat, lenBoxNat_swap_iff, lMap_swap_sentenceAt_frag hme hopp φ hφ]

/-! ### 2. `DIMDID × CIMCIC = (C, D)` at every budget -/

theorem fragP_DIMDID (k : ℕ) : fragP (DIMDID k) = true := rfl

lemma transpose_DIMDID (k : ℕ) : (DIMDID k).transpose = CIMCIC k := rfl
lemma transpose_CIMCIC (k : ℕ) : (CIMCIC k).transpose = DIMDID k := rfl
lemma transpose_phiDd : phiDd.transpose = phiC := rfl
lemma transpose_phiC : phiC.transpose = phiDd := rfl

/-- **Symmetry of the guards**: DIMDID's guard against CIMCIC is found within `k` iff CIMCIC's guard against DIMDID
is. -/
theorem guard_DIMDID_iff_guard_CIMCIC (k : ℕ) :
    LenBox TAct k (guardCode (templateCode phiDd) (progCode (DIMDID k)) (progCode (CIMCIC k))) ↔
    LenBox TAct k (guardCode (templateCode phiC) (progCode (CIMCIC k)) (progCode (DIMDID k))) := by
  have h := lenBox_guardCode_transpose (fragP_DIMDID k) (fragP_CIMCIC k) phiDd rfl rfl rfl k
  rwa [transpose_phiDd, transpose_DIMDID, transpose_CIMCIC] at h

/-- **Neither guard is found**, at any budget: found, DIMDID's guard makes it defect, and CIMCIC's guard against a
defector is self-refuting — but the two guards are found together. -/
theorem guard_DIMDID_vs_CIMCIC_not_found (k : ℕ) :
    ¬ LenBox TAct k (guardCode (templateCode phiDd) (progCode (DIMDID k)) (progCode (CIMCIC k))) := by
  intro hA
  exact cimcic_selfref_not_found k (properPlayer_DIMDID k) (dimdid_D_of_found k hA)
    ((guard_DIMDID_iff_guard_CIMCIC k).mp hA)

/-- **`DIMDID × CIMCIC = (C, D)`** at every shared budget `k`, on the engine's own codes: DIMDID cooperates and
CIMCIC defects. -/
theorem snd_DIMDID_vs_CIMCIC (k : ℕ) :
    EvalGraph 2 (progCode (DIMDID k)) (progCode (CIMCIC k)) (progCode (DIMDID k)) (actCode .C) ∧
    EvalGraph 2 (progCode (CIMCIC k)) (progCode (DIMDID k)) (progCode (CIMCIC k)) (actCode .D) := by
  have hA := guard_DIMDID_vs_CIMCIC_not_found k
  have hB : ¬ LenBox TAct k (guardCode (templateCode phiC) (progCode (CIMCIC k)) (progCode (DIMDID k))) :=
    fun h ↦ hA ((guard_DIMDID_iff_guard_CIMCIC k).mpr h)
  refine ⟨dimdid_C_of_not_found k hA, ?_⟩
  rw [progCode_CIMCIC_search] at hB ⊢
  exact search_else phiC hB (const_play 0 _ _ _)

/-! ### 3. `DIMDID × Dupoc` is the transposition of `CIMCIC × Cupod`: one floor, not two -/

lemma transpose_phiDu : phiDu.transpose = phiCu := rfl

/-- **The two hinges coincide pairwise**: DIMDID's guard against Dupoc is found iff CIMCIC's guard against Cupod is,
and Dupoc's guard against DIMDID is found iff Cupod's guard against CIMCIC is — at the same budget. -/
theorem guards_DIMDID_DupocBot_iff_CIMCIC_CupodBot (k : ℕ) :
    (LenBox TAct k (guardCode (templateCode phiDd) (progCode (DIMDID k)) (progCode (DupocBot k))) ↔
      LenBox TAct k (guardCode (templateCode phiC) (progCode (CIMCIC k)) (progCode (CupodBot k)))) ∧
    (LenBox TAct k (guardCode (templateCode phiDu) (progCode (DupocBot k)) (progCode (DIMDID k))) ↔
      LenBox TAct k (guardCode (templateCode phiCu) (progCode (CupodBot k)) (progCode (CIMCIC k)))) := by
  constructor
  · have h := lenBox_guardCode_transpose (fragP_DIMDID k) (fragP_DupocBot k) phiDd rfl rfl rfl k
    rwa [transpose_phiDd, transpose_DIMDID, transpose_DupocBot] at h
  · have h := lenBox_guardCode_transpose (fragP_DupocBot k) (fragP_DIMDID k) phiDu rfl rfl rfl k
    rwa [transpose_phiDu, transpose_DIMDID, transpose_DupocBot] at h

/-- **The outcomes are transposes of each other, at every budget**: `DIMDID × Dupoc` is `(a, b)` iff
`CIMCIC × Cupod` is the transposed pair. -/
theorem outcomeAtA_DIMDID_vs_DupocBot_iff (k : ℕ) (r : Option PD.Outcome) :
    OutcomeAtA (progCode (DIMDID k)) (progCode (DupocBot k)) r ↔
    OutcomeAtA (progCode (CIMCIC k)) (progCode (CupodBot k)) (transposeOutcome r) := by
  have h := outcomeAtA_transpose (fragP_DIMDID k) (fragP_DupocBot k) r
  rwa [transpose_DIMDID, transpose_DupocBot] at h

end ArithS
