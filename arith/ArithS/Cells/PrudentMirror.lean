import ArithS.Cells.DIMCID
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot

/-!
# ArithS.Cells.PrudentMirror — PrudentBot × Mirror `(C, C)` in PA-`S'` (the nested-search family)

`Research/Notes/ROUTE_B_SCOPE.md` §3 Phase 2 (2026-09-23): the arithmetized twin of the engine's
`outcome_PrudentBot_vs_MirrorBot = (C, C)` (`Theorems/PrudentBot/vs_MirrorBot.lean`, `pblt_engine_id`
on `prudent_mirror_loeb_premise`, whose leg 1 is `searchThenSearch_t` CITING the search-free prudence
certificate `⊢_33 (Mirror plays D vs .bot DefectBot)`). V-generic unless a statement says `ℕ`.

**STEP 0 (the §7 test).** `PrudentBot k = .search k g₁ (.search k g₂ (const C) (const D)) (const D)`
with `g₁ = plays opp self C` and `g₂ = plays opp (.bot DefectBot) D`. Both STORED TEMPLATES are
budget-free constants (`⌜tmpl g₁⌝`, `⌜tmpl g₂⌝`: neither formula mentions `k`; `.bot DefectBot` is
closed), and `k` sits only in the two `pSearch` budget slots, which `progT` renders as `bnum k` leaves
(`progT_search`). So `PrudentV k` IS the `bnum k`-instance of a fixed two-`#0` term — NOT the JustBot
obstruction. What the nested search DOES cost: the canonical description compares two `k`-DEPENDENT
codes (`PrudentV k` vs its transposition `PrudentTV k`, whose then-branches carry `k`), so `dnum`,
`dU`, `dW` are `k`-uniform only ABOVE A STANDARD THRESHOLD `KP` (§2: `nested_search_lt`, an
ordered-semiring argument on `ppair`; below it the order could in principle depend on `k`). Every
description/instance/truth equation below therefore carries `hk : (KP : V) ≤ k`, and the family's
slack `S₀ = 14 + KP` supplies it inside the Löb premise.

1. **The two templates** `tmplP1 := tmpl (plays opp self C)`, `tmplP2 := tmpl (plays opp (.bot
   DefectBot) D)` and their transpositions; `PrudentV k`, `PrudentTV k = swapcode (PrudentV k)`; the
   bridge `pcode_PrudentBot : pcode (PD.Bots.PrudentBot k) = Prudent k`.
2. **The canonical description above `KP`**: `dnum_PrudentV`, `dU_PrudentV`, `dW_PrudentV` (constants
   `gPo gPi pPi qPi qPo`, `uP wP`, decided by the never-evaluated case split `innerP2 < innerT2` on
   the INNER searchers' budget-free parts — the two are distinct by `ppair` injectivity); the
   two-level description tower `searchT1'`/`TP` (`termSubst_tower'`, `termSubst_TP`, `val_TP_V`).
3. **Generic template instances** `qT g X U W X' U' W'` for an ARBITRARY six-variable template
   (`guardCode_qT_eq_instB`, its swap, `eval_qT_iff`), and the truth of `tmpl (plays opp q a)` for a
   CLOSED `q` (`eval_tmpl_plays_opp_closed_V`, via `Det.eval_closedDesc_V`).
4. **The four fixed formulas** `qPM` ("Mirror plays C against Prudent k"), `qPP` ("Mirror plays D
   against `.bot DefectBot`" — the PRUDENCE conjunct: a CLOSED true Σ₁ fact, constant in `k` up to the
   inert me-slots), and their transpositions `qPMT`/`qPPT`; instance equations and truth equations.
5. **The family** `pPM := (qPM ⋏ qPP) ⋏ (qPMT ⋏ qPPT)` (DIMCID × Cupod's two-level shape, slack
   `(14 + KP, 16)`): the engine's INNER-SEARCH CITATION (`searchThenSearch_t` + `prudence_provable`)
   is replaced by ∧-ELIMINATION — the prudence box is a conjunct of the family's box, so both of
   Prudent's searches fire from ONE Löb fixed point (`pPM_all_V`, `prudent_search_V` at fuel 3), and
   Mirror copies at fuel 4. "Prudence" in `S'` is thus neither a `SND` soundness fact nor a separate
   Σ₁-completeness/instantiation certificate: it is the truth of a closed Σ₁ sentence in every model
   (`mirror_bot_defect_V`, fuel 3), carried by the family (`loebSound_pPM`).
6. **The cells at ℕ**: `family_found pPM` then the eliminations — `prudent_mirror_coop` (conditional)
   and **`prudent_mirror_coop_unconditional`**: for all large `k`, `EvalGraph 3 (Prudent k) Mirror
   (Prudent k) 0 ∧ EvalGraph 4 Mirror (Prudent k) Mirror 0` — the `(C, C)` cell; the transposed
   searcher's `(D, D)` twin `prudentT_mirror_defect_unconditional`; the box forms.

Conventions (`HANDOVER_ARITHMETIZED_S.md` §5–6): thresholds and constants are named `ℕ`-constants
or existentials and NEVER evaluated (`KP`, `innerP2`, `innerT2` are irreducible; `simp` never sees a
closed quote); `omega` is never asked about `V`; at `V = ℕ` the thresholds are strict (`k₀ < k`) and
`≤` is bridged by `le_def` (`Cell.cell_core`'s idiom).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The templates, the programs, the bridge -/

section programs

/-- PrudentBot's outer guard: "opp cooperates with me". -/
def phiP1 : PD.Formula := .plays .opp .self .C
/-- PrudentBot's inner (prudence) guard: "opp defects against `.bot DefectBot`". -/
def phiP2 : PD.Formula := .plays .opp (.bot PD.Bots.DefectBot) .D

lemma phiP1_transpose : phiP1.transpose = .plays .opp .self .D := rfl
lemma phiP2_transpose : phiP2.transpose = .plays .opp (.bot (.const .C)) .C := rfl
lemma fragF_phiP1 : fragF phiP1 = true := rfl
lemma fragF_phiP2 : fragF phiP2 = true := rfl

/-- The outer template (a closed constant, never evaluated). -/
noncomputable def tmplP1 : Semisentence LAct 6 := tmpl phiP1
/-- The inner (prudence) template. -/
noncomputable def tmplP2 : Semisentence LAct 6 := tmpl phiP2
/-- The transposed outer template: "opp defects against me". -/
noncomputable def tmplP1T : Semisentence LAct 6 := tmpl (.plays .opp .self .D)
/-- The transposed inner template: "opp cooperates with `.bot CooperateBot`". -/
noncomputable def tmplP2T : Semisentence LAct 6 := tmpl (.plays .opp (.bot (.const .C)) .C)

lemma lMap_swap_tmplP1 : Semiformula.lMap swap tmplP1 = tmplP1T := lMap_swap_tmpl phiP1 fragF_phiP1
lemma lMap_swap_tmplP2 : Semiformula.lMap swap tmplP2 = tmplP2T := lMap_swap_tmpl phiP2 fragF_phiP2
lemma lMap_swap_tmplP1T : Semiformula.lMap swap tmplP1T = tmplP1 := by
  rw [← lMap_swap_tmplP1, lMap_swap_swap]
lemma lMap_swap_tmplP2T : Semiformula.lMap swap tmplP2T = tmplP2 := by
  rw [← lMap_swap_tmplP2, lMap_swap_swap]

/-- `PrudentBot k` in an arbitrary model: the cooperation search at the root, the prudence search in
its then-branch (found-found ⇒ `C`, else `D`). -/
noncomputable def PrudentV (k : V) : V :=
  pSearch k (⌜tmplP1⌝ : V) (pSearch k (⌜tmplP2⌝ : V) (pConst 0) (pConst 1)) (pConst 1)

/-- The transposed searcher τ(PrudentBot): defect iff (opp defects against me AND opp cooperates
with CooperateBot). -/
noncomputable def PrudentTV (k : V) : V :=
  pSearch k (⌜tmplP1T⌝ : V) (pSearch k (⌜tmplP2T⌝ : V) (pConst 1) (pConst 0)) (pConst 0)

/-- `PrudentBot k` at `ℕ`. -/
noncomputable def Prudent (k : ℕ) : ℕ := PrudentV (V := ℕ) k
/-- τ(PrudentBot) at `ℕ`. -/
noncomputable def PrudentT (k : ℕ) : ℕ := PrudentTV (V := ℕ) k

lemma PrudentV_nat (k : ℕ) : PrudentV (V := ℕ) k = Prudent k := rfl
lemma PrudentTV_nat (k : ℕ) : PrudentTV (V := ℕ) k = PrudentT k := rfl

/-- **The bridge to the engine**: the code of the engine's `PrudentBot k` is `Prudent k`. -/
theorem pcode_PrudentBot (k : ℕ) : pcode (PD.Bots.PrudentBot k) = Prudent k := by
  simp only [PD.Bots.PrudentBot, pcode_search, pcode_const, actCode]; rfl

theorem swapcode_PrudentV (k : V) : swapcode (PrudentV k) = PrudentTV k := by
  unfold PrudentV PrudentTV swapcode
  rw [relabel_search, relabel_search, relabel_const, relabel_const,
    relabelTemplate_quote_sentence₆_V, relabelTemplate_quote_sentence₆_V, lMap_swap_tmplP1, lMap_swap_tmplP2]
  simp [relabelAct]

theorem swapcode_PrudentTV (k : V) : swapcode (PrudentTV k) = PrudentV k := by
  rw [← swapcode_PrudentV, swapcode_swapcode]

end programs

/-! ### 2. The canonical description above a standard threshold -/

section order

/-- `ppair` grows by at least `2x + 1` when the sum of the arguments grows by one:
`(x' + y')² ≥ (x + y + 1)² = (x + y)² + 2(x + y) + 1 ≥ (x + y)² + y + 2x + 1`. -/
lemma ppair_add_le_of_add_succ_le {x y x' y' : V} (h : x + y + 1 ≤ x' + y') :
    ppair x y + (2 * x + 1) ≤ ppair x' y' := by
  have h1 : (x + y + 1) * (x + y + 1) ≤ (x' + y') * (x' + y') := mul_le_mul h h (by simp) (by simp)
  have h2 : ppair x y + (2 * x + 1) ≤ (x + y + 1) * (x + y + 1) := by
    have e : (x + y + 1) * (x + y + 1) = ppair x y + (2 * x + 1) + y := by unfold ppair; ring
    rw [e]; exact le_self_add
  refine le_trans h2 (le_trans h1 ?_)
  unfold ppair; exact le_self_add

/-- `ppair` is strictly monotone in the SUM of its arguments. -/
lemma ppair_lt_of_add_lt {x y x' y' : V} (h : x + y < x' + y') : ppair x y < ppair x' y' :=
  lt_of_lt_of_le (lt_of_lt_of_le (lt_iff_succ_le.mpr le_rfl)
    (_root_.add_le_add_right (le_add_self : 1 ≤ 2 * x + 1) _))
    (ppair_add_le_of_add_succ_le (lt_iff_succ_le.mp h))

/-- Raising the second argument by one raises `ppair x ·` by at least `2(x + y) + 2`. -/
lemma ppair_add_le_of_succ_le (x : V) {y y' : V} (h : y + 1 ≤ y') :
    ppair x y + (2 * (x + y) + 2) ≤ ppair x y' := by
  have h1 : (x + y + 1) * (x + y + 1) ≤ (x + y') * (x + y') :=
    mul_le_mul (by rw [add_assoc]; exact _root_.add_le_add_right h x) (by rw [add_assoc]; exact _root_.add_le_add_right h x)
      (by simp) (by simp)
  unfold ppair
  calc (x + y) * (x + y) + y + (2 * (x + y) + 2) = (x + y + 1) * (x + y + 1) + (y + 1) := by ring
    _ ≤ (x + y') * (x + y') + y' := add_le_add h1 h

/-- **The nested-searcher comparison**: two searchers of budget `k` whose then-branches are
themselves `k`-searchers with budget-free parts `a < b` compare as `a < b` as soon as the budget
dominates the stored template `g` (the inner difference `≥ 2A + 1 > g` swamps the outer constants),
whatever the else-branches `c, c'` (with `c + 1 ≤ 14`). -/
lemma nested_search_lt {k g g' a b c c' : V} (hab : a + 1 ≤ b) (hgk : g ≤ k) (hc : c + 1 ≤ 14) :
    ppair 6 (ppair k (ppair g (ppair (ppair 6 (ppair k a) + 1) c))) + 1 <
    ppair 6 (ppair k (ppair g' (ppair (ppair 6 (ppair k b) + 1) c'))) + 1 := by
  set A := ppair 6 (ppair k a) + 1 with hA
  set B := ppair 6 (ppair k b) + 1 with hB
  have hAB : A + 14 ≤ B := by
    have h1 : ppair k a + 1 ≤ ppair k b :=
      le_trans (_root_.add_le_add_right
        (show (1 : V) ≤ 2 * (k + a) + 2 from le_trans (by norm_num : (1 : V) ≤ 2) le_add_self) _)
        (ppair_add_le_of_succ_le k hab)
    have h2 := ppair_add_le_of_succ_le 6 h1
    have h3 : ppair 6 (ppair k a) + 14 ≤ ppair 6 (ppair k b) := by
      refine le_trans ?_ h2
      refine _root_.add_le_add_right ?_ _
      calc (14 : V) = 2 * 6 + 2 := by norm_num
        _ ≤ 2 * (6 + ppair k a) + 2 := by gcongr; exact le_self_add
    rw [hA, hB]
    calc ppair 6 (ppair k a) + 1 + 14 = ppair 6 (ppair k a) + 14 + 1 := by ring
      _ ≤ ppair 6 (ppair k b) + 1 := _root_.add_le_add_left h3 1
  have hkA : k ≤ A := by
    rw [hA]
    exact le_trans (le_ppair_left k a) (le_trans (le_ppair_right 6 _) le_self_add)
  have h3 : ppair A c + (2 * A + 1) ≤ ppair B c' := by
    apply ppair_add_le_of_add_succ_le
    calc A + c + 1 = A + (c + 1) := by ring
      _ ≤ A + 14 := _root_.add_le_add_right hc A
      _ ≤ B := hAB
      _ ≤ B + c' := le_self_add
  have hsum : g + ppair A c < g' + ppair B c' := by
    rw [lt_iff_succ_le]
    calc g + ppair A c + 1 = ppair A c + (g + 1) := by ring
      _ ≤ ppair A c + (2 * A + 1) := by
          refine _root_.add_le_add_right (_root_.add_le_add_left ?_ 1) _
          calc g ≤ A := le_trans hgk hkA
            _ ≤ 2 * A := by rw [two_mul]; exact le_self_add
      _ ≤ ppair B c' := h3
      _ ≤ g' + ppair B c' := le_add_self
  exact _root_.add_lt_add_left (ppair_lt_ppair_right 6 (ppair_lt_ppair_right k (ppair_lt_of_add_lt hsum))) 1

end order

section canonical

/-- The budget-free part of the INNER searcher of `PrudentV k`. -/
noncomputable def innerP2 : ℕ := ppair (⌜tmplP2⌝ : ℕ) (ppair (pConst 0) (pConst 1))
/-- The budget-free part of the inner searcher of `PrudentTV k`. -/
noncomputable def innerT2 : ℕ := ppair (⌜tmplP2T⌝ : ℕ) (ppair (pConst 1) (pConst 0))
/-- **The threshold** above which the order of `PrudentV k` and `PrudentTV k` is `k`-uniform: the sum
of the two outer template codes (never evaluated). -/
noncomputable def KP : ℕ := (⌜tmplP1⌝ : ℕ) + (⌜tmplP1T⌝ : ℕ)

lemma innerP2_def : innerP2 = ppair (⌜tmplP2⌝ : ℕ) (ppair (pConst 0) (pConst 1)) := rfl
lemma innerT2_def : innerT2 = ppair (⌜tmplP2T⌝ : ℕ) (ppair (pConst 1) (pConst 0)) := rfl
lemma KP_def : KP = (⌜tmplP1⌝ : ℕ) + (⌜tmplP1T⌝ : ℕ) := rfl

attribute [irreducible] innerP2 innerT2 KP

/-- The two inner parts differ (`ppair` is injective and `pConst 0 ≠ pConst 1`). -/
lemma innerP2_ne_innerT2 : innerP2 ≠ innerT2 := by
  intro h
  rw [innerP2_def, innerT2_def] at h
  obtain ⟨_, h2⟩ := ppair_inj h
  obtain ⟨h3, _⟩ := ppair_inj h2
  exact absurd (pConst_inj h3) (by decide)

lemma cast_innerP2 : ((innerP2 : ℕ) : V) = ppair (⌜tmplP2⌝ : V) (ppair (pConst 0) (pConst 1)) := by
  rw [innerP2_def, cast_ppair, cast_ppair, cast_pConst, cast_pConst, coe_quote_sentence₆]
  push_cast
  rfl

lemma cast_innerT2 : ((innerT2 : ℕ) : V) = ppair (⌜tmplP2T⌝ : V) (ppair (pConst 1) (pConst 0)) := by
  rw [innerT2_def, cast_ppair, cast_ppair, cast_pConst, cast_pConst, coe_quote_sentence₆]
  push_cast
  rfl

lemma PrudentV_eq_inner (k : V) :
    PrudentV k = ppair 6 (ppair k (ppair (⌜tmplP1⌝ : V) (ppair (ppair 6 (ppair k (innerP2 : V)) + 1) (pConst 1)))) + 1 := by
  rw [cast_innerP2]; rfl

lemma PrudentTV_eq_inner (k : V) :
    PrudentTV k = ppair 6 (ppair k (ppair (⌜tmplP1T⌝ : V) (ppair (ppair 6 (ppair k (innerT2 : V)) + 1) (pConst 0)))) + 1 := by
  rw [cast_innerT2]; rfl

lemma quote_tmplP1_le_of_KP {k : V} (hk : (KP : V) ≤ k) : (⌜tmplP1⌝ : V) ≤ k := by
  rw [KP_def, Nat.cast_add, coe_quote_sentence₆, coe_quote_sentence₆] at hk
  exact le_trans le_self_add hk

lemma quote_tmplP1T_le_of_KP {k : V} (hk : (KP : V) ≤ k) : (⌜tmplP1T⌝ : V) ≤ k := by
  rw [KP_def, Nat.cast_add, coe_quote_sentence₆, coe_quote_sentence₆] at hk
  exact le_trans le_add_self hk

lemma pConst_zero_succ_le : pConst (0 : V) + 1 ≤ 14 := by
  unfold pConst ppair; norm_num

lemma pConst_one_succ_le : pConst (1 : V) + 1 ≤ 14 := by
  unfold pConst ppair; norm_num

/-- Above the threshold, `innerP2 < innerT2` puts `PrudentV k` below its transposition. -/
theorem PrudentV_lt_PrudentTV {k : V} (hk : (KP : V) ≤ k) (h : innerP2 < innerT2) :
    PrudentV k < PrudentTV k := by
  rw [PrudentV_eq_inner, PrudentTV_eq_inner]
  exact nested_search_lt (lt_iff_succ_le.mp (Nat.cast_lt.mpr h)) (quote_tmplP1_le_of_KP hk) pConst_one_succ_le

/-- Above the threshold, `innerT2 < innerP2` puts the transposition below `PrudentV k`. -/
theorem PrudentTV_lt_PrudentV {k : V} (hk : (KP : V) ≤ k) (h : innerT2 < innerP2) :
    PrudentTV k < PrudentV k := by
  rw [PrudentV_eq_inner, PrudentTV_eq_inner]
  exact nested_search_lt (lt_iff_succ_le.mp (Nat.cast_lt.mpr h)) (quote_tmplP1T_le_of_KP hk) pConst_zero_succ_le

/-- The stored OUTER template of the canonical searcher. -/
noncomputable def gPo : ℕ := if innerP2 < innerT2 then (⌜tmplP1⌝ : ℕ) else (⌜tmplP1T⌝ : ℕ)
/-- The stored INNER template. -/
noncomputable def gPi : ℕ := if innerP2 < innerT2 then (⌜tmplP2⌝ : ℕ) else (⌜tmplP2T⌝ : ℕ)
/-- The inner then-branch. -/
noncomputable def pPi : ℕ := if innerP2 < innerT2 then pConst 0 else pConst 1
/-- The inner else-branch. -/
noncomputable def qPi : ℕ := if innerP2 < innerT2 then pConst 1 else pConst 0
/-- The outer else-branch. -/
noncomputable def qPo : ℕ := if innerP2 < innerT2 then pConst 1 else pConst 0
/-- The first re-valuation term of the description of `PrudentV k` (no tie: the inner parts differ). -/
noncomputable def uP : ClosedSemiterm LAct 0 := if innerP2 < innerT2 then cterm Act.C else cterm Act.D
/-- The second re-valuation term. -/
noncomputable def wP : ClosedSemiterm LAct 0 := if innerP2 < innerT2 then cterm Act.D else cterm Act.C

lemma PrudentV_eq_cast (k : V) :
    PrudentV k = pSearch k ((⌜tmplP1⌝ : ℕ) : V)
      (pSearch k ((⌜tmplP2⌝ : ℕ) : V) ((pConst 0 : ℕ) : V) ((pConst 1 : ℕ) : V)) ((pConst 1 : ℕ) : V) := by
  unfold PrudentV; rw [coe_quote_sentence₆, coe_quote_sentence₆, cast_pConst, cast_pConst]; push_cast; rfl

lemma PrudentTV_eq_cast (k : V) :
    PrudentTV k = pSearch k ((⌜tmplP1T⌝ : ℕ) : V)
      (pSearch k ((⌜tmplP2T⌝ : ℕ) : V) ((pConst 1 : ℕ) : V) ((pConst 0 : ℕ) : V)) ((pConst 0 : ℕ) : V) := by
  unfold PrudentTV; rw [coe_quote_sentence₆, coe_quote_sentence₆, cast_pConst, cast_pConst]; push_cast; rfl

lemma innerT2_lt_of_not_lt (h : ¬ innerP2 < innerT2) : innerT2 < innerP2 :=
  lt_of_le_of_ne (not_lt.mp h) (Ne.symm innerP2_ne_innerT2)

/-- **The canonical code of `PrudentV k` above the threshold**: a two-level searcher with (cast)
`k`-independent stored parts. -/
theorem dnum_PrudentV {k : V} (hk : (KP : V) ≤ k) :
    dnum (PrudentV k) = pSearch k (gPo : V) (pSearch k (gPi : V) (pPi : V) (qPi : V)) (qPo : V) := by
  by_cases h : innerP2 < innerT2
  · simp only [gPo, gPi, pPi, qPi, qPo, if_pos h]
    rw [dnum_of_lt (by rw [swapcode_PrudentV]; exact PrudentV_lt_PrudentTV hk h)]
    exact PrudentV_eq_cast k
  · simp only [gPo, gPi, pPi, qPi, qPo, if_neg h]
    rw [dnum_of_gt (by rw [swapcode_PrudentV]; exact PrudentTV_lt_PrudentV hk (innerT2_lt_of_not_lt h)),
      swapcode_PrudentV]
    exact PrudentTV_eq_cast k

theorem dU_PrudentV {k : V} (hk : (KP : V) ≤ k) : dU (PrudentV k) = (⌜uP⌝ : V) := by
  unfold dU uP
  rw [swapcode_PrudentV]
  by_cases h : innerP2 < innerT2
  · rw [if_pos (PrudentV_lt_PrudentTV hk h), if_pos h, quote_cterm_C]
  · have h' := PrudentTV_lt_PrudentV hk (innerT2_lt_of_not_lt h)
    rw [if_neg (lt_asymm h'), if_pos h', if_neg h, quote_cterm_D]

theorem dW_PrudentV {k : V} (hk : (KP : V) ≤ k) : dW (PrudentV k) = (⌜wP⌝ : V) := by
  unfold dW wP
  rw [swapcode_PrudentV]
  by_cases h : innerP2 < innerT2
  · rw [if_pos (PrudentV_lt_PrudentTV hk h), if_pos h, quote_cterm_D]
  · have h' := PrudentTV_lt_PrudentV hk (innerT2_lt_of_not_lt h)
    rw [if_neg (lt_asymm h'), if_pos h', if_neg h, quote_cterm_C]

/-- The re-valuation terms reconstruct `PrudentV k` from its canonical code (above the threshold). -/
theorem relabel_val_uP_wP_V {k : V} (hk : (KP : V) ≤ k) :
    relabel (uP.val (s := stdActV V) ![] Empty.elim) (wP.val (s := stdActV V) ![] Empty.elim)
      (dnum (PrudentV k)) = PrudentV k := by
  unfold uP wP
  by_cases h : innerP2 < innerT2
  · rw [if_pos h, if_pos h, val_cterm_C_V, val_cterm_D_V,
      dnum_of_lt (by rw [swapcode_PrudentV]; exact PrudentV_lt_PrudentTV hk h), relabel_zero_one]
  · rw [if_neg h, if_neg h, val_cterm_D_V, val_cterm_C_V,
      dnum_of_gt (by rw [swapcode_PrudentV]; exact PrudentTV_lt_PrudentV hk (innerT2_lt_of_not_lt h))]
    exact swapcode_swapcode _

/-- The transposed re-valuation terms. -/
noncomputable def uPT : ClosedSemiterm LAct 0 := Semiterm.lMap swap uP
noncomputable def wPT : ClosedSemiterm LAct 0 := Semiterm.lMap swap wP

/-- The transposed re-valuation terms reconstruct `PrudentTV k` from the canonical code of `PrudentV k`. -/
theorem relabel_val_uPT_wPT_V {k : V} (hk : (KP : V) ≤ k) :
    relabel (uPT.val (s := stdActV V) ![] Empty.elim) (wPT.val (s := stdActV V) ![] Empty.elim)
      (dnum (PrudentV k)) = PrudentTV k := by
  unfold uPT wPT uP wP
  by_cases h : innerP2 < innerT2
  · rw [if_pos h, if_pos h, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V,
      dnum_of_lt (by rw [swapcode_PrudentV]; exact PrudentV_lt_PrudentTV hk h)]
    exact swapcode_PrudentV k
  · rw [if_neg h, if_neg h, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
      dnum_of_gt (by rw [swapcode_PrudentV]; exact PrudentTV_lt_PrudentV hk (innerT2_lt_of_not_lt h)),
      swapcode_PrudentV, relabel_zero_one]

end canonical

/-! ### 2b. The two-level description tower -/

section tower

/-- The one-variable structural term of a searcher whose THEN-branch is itself a one-variable term
`P` (the else-branch and the template closed). `searchT1 g p q = searchT1' g (bShift (progTT p)) q`
up to the shift. -/
noncomputable def searchT1' (g : ℕ) (P : Semiterm ℒₒᵣ Empty 1) (q : ℕ) : Semiterm ℒₒᵣ Empty 1 :=
  succT1 (ppairT1 (Rew.bShift (bnumT 6)) (ppairT1 #0
    (ppairT1 (Rew.bShift (bnumT g)) (ppairT1 P (Rew.bShift (progTT q))))))

lemma val_searchT1'_V (g : ℕ) (P : Semiterm ℒₒᵣ Empty 1) (q : ℕ) (k : V) :
    (searchT1' g P q).val (s := standardModel V) ![k] Empty.elim =
      pSearch k (g : V) (P.val (s := standardModel V) ![k] Empty.elim) (q : V) := by
  rw [searchT1', val_succT1_V, val_ppairT1_V, val_ppairT1_V, val_bShift₁_V, val_ppairT1_V, val_bShift₁_V,
    val_ppairT1_V, val_bShift₁_V, val_bnumT_V, val_bnumT_V, val_progTT_V]
  unfold pSearch
  push_cast
  rfl

lemma quote_emb_searchT1' (g : ℕ) (P : Semiterm ℒₒᵣ Empty 1) (q : ℕ) :
    (⌜(Rew.emb (searchT1' g P q) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
    ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (g : V))
      (ppairT (⌜(Rew.emb P : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) (progT (q : V))))) ^+ 𝟏 := by
  rw [searchT1', quote_emb_succT1, quote_emb_ppairT1, quote_emb_ppairT1, quote_emb_bShift, quote_emb_ppairT1,
    quote_emb_bShift, quote_emb_ppairT1, quote_emb_bShift, quote_emb_bvar_zero, ← Semiterm.empty_quote_def,
    ← Semiterm.empty_quote_def, ← Semiterm.empty_quote_def, ← Semiterm.empty_quote_def, quote_bnumT, quote_bnumT,
    quote_progTT]
  push_cast
  rfl


/-- **The one-variable description term of `PrudentV k`**, over `LAct`: the searcher tower whose
then-slot is the inner searcher tower. -/
noncomputable def TP : Semiterm LAct Empty 1 := Semiterm.lMap emb (searchT1' gPo (searchT1 gPi pPi qPi) qPo)

lemma lMap_swap_TP : Semiterm.lMap swap TP = TP := term_lMap_swap_emb _

/-- `TP` at a budget `k` above the threshold denotes the canonical code of `PrudentV k`. -/
theorem val_TP_V {k : V} (hk : (KP : V) ≤ k) : TP.val (s := stdActV V) ![k] Empty.elim = dnum (PrudentV k) := by
  unfold TP
  rw [Semiterm.val_lMap, stdActV_lMap_emb, val_searchT1'_V, val_searchT1_V, dnum_PrudentV hk]

theorem quote_emb_TP :
    (⌜(Rew.emb TP : SyntacticSemiterm LAct 1)⌝ : V) =
    ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (gPo : V))
      (ppairT (ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (gPi : V)) (ppairT (progT (pPi : V)) (progT (qPi : V))))) ^+ 𝟏)
        (progT (qPo : V))))) ^+ 𝟏 := by
  unfold TP
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, quote_emb_searchT1', quote_emb_searchT1]

/-- **Filling the budget slot of `TP`** (above the threshold): the structural term of the canonical
code of `PrudentV k`. -/
theorem termSubst_TP {k : V} (hk : (KP : V) ≤ k) :
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb TP : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (PrudentV k)) := by
  have hb6 : IsUTerm LAct (bnum (6 : V)) := (bnum_semiterm_LAct 0 _).isUTerm
  have hbg : IsUTerm LAct (bnum (gPi : V)) := (bnum_semiterm_LAct 0 _).isUTerm
  have hp : IsUTerm LAct (progT (pPi : V)) := (progT_semiterm_LAct 0 _).isUTerm
  have hq : IsUTerm LAct (progT (qPi : V)) := (progT_semiterm_LAct 0 _).isUTerm
  have hone : IsUTerm LAct (𝟏 : V) := (IsSemiterm.LAct_of_LOR (one_semiterm (n := 0))).isUTerm
  have h1 : IsUTerm LAct (ppairT (progT (pPi : V)) (progT (qPi : V))) := ppairT_uterm_LAct hp hq
  have h2 : IsUTerm LAct (ppairT (bnum (gPi : V)) (ppairT (progT (pPi : V)) (progT (qPi : V)))) := ppairT_uterm_LAct hbg h1
  have h3 : IsUTerm LAct (ppairT (^#0) (ppairT (bnum (gPi : V)) (ppairT (progT (pPi : V)) (progT (qPi : V))))) :=
    ppairT_uterm_LAct bvar_zero_uterm h2
  have h4 : IsUTerm LAct (ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (gPi : V)) (ppairT (progT (pPi : V)) (progT (qPi : V)))))) :=
    ppairT_uterm_LAct hb6 h3
  have h5 : IsUTerm LAct (ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (gPi : V)) (ppairT (progT (pPi : V)) (progT (qPi : V))))) ^+ 𝟏) :=
    qqAdd_uterm_LAct h4 hone
  rw [quote_emb_TP, termSubst_tower' k _ _ h5 (termSubst_tower k _ _ _), dnum_PrudentV hk]

end tower

/-! ### 3. Generic template instances, and the atom over a closed program -/

section generic

end generic

/-! ### 4. The four fixed formulas: instance equations and truth equations -/

section fixedFormulas

lemma hX_prudent {k : V} (hk : (KP : V) ≤ k) :
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb TP : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum (PrudentV k)) :=
  termSubst_TP hk
lemma hU_prudent {k : V} (hk : (KP : V) ≤ k) : (⌜uP⌝ : V) = dU (PrudentV k) := (dU_PrudentV hk).symm
lemma hW_prudent {k : V} (hk : (KP : V) ≤ k) : (⌜wP⌝ : V) = dW (PrudentV k) := (dW_PrudentV hk).symm

/-- **The outer fixed formula**: `qPM(k)` says "Mirror plays C against `PrudentV k`". -/
noncomputable def qPM : Semisentence LAct 1 := qT tmplP1 TP uP wP (cl TM) (numT 0) (numT 1)
/-- **The prudence fixed formula**: `qPP(k)` says "Mirror plays D against `.bot DefectBot`" (the
me-slots are inert: a closed Σ₁ fact carried at every `k`). -/
noncomputable def qPP : Semisentence LAct 1 := qT tmplP2 TP uP wP (cl TM) (numT 0) (numT 1)
/-- The transposed outer formula: "Mirror plays D against `PrudentTV k`". -/
noncomputable def qPMT : Semisentence LAct 1 := Semiformula.lMap swap qPM
/-- The transposed prudence formula: "Mirror plays C against `.bot CooperateBot`". -/
noncomputable def qPPT : Semisentence LAct 1 := Semiformula.lMap swap qPP

lemma lMap_swap_qPM : Semiformula.lMap swap qPM = qPMT := rfl
lemma lMap_swap_qPP : Semiformula.lMap swap qPP = qPPT := rfl
lemma lMap_swap_qPMT : Semiformula.lMap swap qPMT = qPM := lMap_swap_swap _
lemma lMap_swap_qPPT : Semiformula.lMap swap qPPT = qPP := lMap_swap_swap _

theorem qPMT_eq : qPMT = qT tmplP1T TP uPT wPT (cl TM) (numT 0) (numT 1) := by
  unfold qPMT qPM
  rw [lMap_swap_qT, lMap_swap_tmplP1, lMap_swap_TP, lMap_swap_cl, lMap_swap_TM, lMap_swap_numT, lMap_swap_numT]
  rfl

theorem qPPT_eq : qPPT = qT tmplP2T TP uPT wPT (cl TM) (numT 0) (numT 1) := by
  unfold qPPT qPP
  rw [lMap_swap_qT, lMap_swap_tmplP2, lMap_swap_TP, lMap_swap_cl, lMap_swap_TM, lMap_swap_numT, lMap_swap_numT]
  rfl

/-- **The instance equation on codes** (above the threshold): Prudent's outer guard code against
Mirror is the `bnum k`-instance of `⌜qPM⌝`. -/
theorem guardCode_PrudentV_MirrorV_eq_instB {k : V} (hk : (KP : V) ≤ k) :
    guardCode (⌜tmplP1⌝ : V) (PrudentV k) MirrorV = instB (⌜qPM⌝ : V) k :=
  guardCode_qT_eq_instB tmplP1 k TP uP wP (cl TM) (numT 0) (numT 1) (hX_prudent hk) (hU_prudent hk)
    (hW_prudent hk) (hX_mirror k) hU_mirror hW_mirror

/-- The prudence guard code is the `bnum k`-instance of `⌜qPP⌝`. -/
theorem guardCode_PrudentV_MirrorV_inner_eq_instB {k : V} (hk : (KP : V) ≤ k) :
    guardCode (⌜tmplP2⌝ : V) (PrudentV k) MirrorV = instB (⌜qPP⌝ : V) k :=
  guardCode_qT_eq_instB tmplP2 k TP uP wP (cl TM) (numT 0) (numT 1) (hX_prudent hk) (hU_prudent hk)
    (hW_prudent hk) (hX_mirror k) hU_mirror hW_mirror

/-- The transposed searcher's outer guard code against Mirror is the `bnum k`-instance of `⌜qPMT⌝`. -/
theorem guardCode_PrudentTV_MirrorV_eq_instB {k : V} (hk : (KP : V) ≤ k) :
    guardCode (⌜tmplP1T⌝ : V) (PrudentTV k) MirrorV = instB (⌜qPMT⌝ : V) k := by
  have h := guardCode_qT_swap_eq_instB tmplP1 k TP uP wP (cl TM) (numT 0) (numT 1) (hX_prudent hk) (hU_prudent hk)
    (hW_prudent hk) (hX_mirror k) hU_mirror hW_mirror
  rw [lMap_swap_tmplP1, swapcode_PrudentV, swapcode_MirrorV] at h
  exact h

theorem guardCode_PrudentTV_MirrorV_inner_eq_instB {k : V} (hk : (KP : V) ≤ k) :
    guardCode (⌜tmplP2T⌝ : V) (PrudentTV k) MirrorV = instB (⌜qPPT⌝ : V) k := by
  have h := guardCode_qT_swap_eq_instB tmplP2 k TP uP wP (cl TM) (numT 0) (numT 1) (hX_prudent hk) (hU_prudent hk)
    (hW_prudent hk) (hX_mirror k) hU_mirror hW_mirror
  rw [lMap_swap_tmplP2, swapcode_PrudentV, swapcode_MirrorV] at h
  exact h

/-! #### The truth equations (standard reading) -/

/-- `qPM(k)` holds in `stdActV V` iff Mirror plays C against `PrudentV k` (above the threshold). -/
theorem eval_qPM_iff_V {k : V} (hk : (KP : V) ≤ k) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qPM ↔
      ∃ n, EvalGraph n MirrorV (PrudentV k) MirrorV 0 := by
  unfold qPM tmplP1 phiP1
  rw [eval_qT_iff, eval_tmpl_plays_opp_self_V]
  simp only [Matrix.cons_val, actCode, Nat.cast_zero]
  rw [val_TP_V hk, relabel_val_uP_wP_V hk, hopp_mirror k]

/-- `qPP(k)` holds in `stdActV V` iff Mirror plays D against `.bot DefectBot` (`pBot (pConst 1)`). -/
theorem eval_qPP_iff_V (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qPP ↔
      ∃ n, EvalGraph n (MirrorV : V) (pBot (pConst 1)) MirrorV 1 := by
  unfold qPP tmplP2 phiP2
  rw [eval_qT_iff, eval_tmpl_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
  simp only [Matrix.cons_val, actCode, Nat.cast_one, pcode_bot, pcode_const, PD.Bots.DefectBot, cast_pBot,
    cast_pConst]
  rw [hopp_mirror k]

/-- `qPMT(k)` holds in `stdActV V` iff Mirror plays D against `PrudentTV k`. -/
theorem eval_qPMT_iff_V {k : V} (hk : (KP : V) ≤ k) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qPMT ↔
      ∃ n, EvalGraph n MirrorV (PrudentTV k) MirrorV 1 := by
  rw [qPMT_eq]
  unfold tmplP1T
  rw [eval_qT_iff, eval_tmpl_plays_opp_self_V]
  simp only [Matrix.cons_val, actCode, Nat.cast_one]
  rw [val_TP_V hk, relabel_val_uPT_wPT_V hk, hopp_mirror k]

/-- `qPPT(k)` holds in `stdActV V` iff Mirror plays C against `.bot CooperateBot` (`pBot (pConst 0)`). -/
theorem eval_qPPT_iff_V (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qPPT ↔
      ∃ n, EvalGraph n (MirrorV : V) (pBot (pConst 0)) MirrorV 0 := by
  rw [qPPT_eq]
  unfold tmplP2T
  rw [eval_qT_iff, eval_tmpl_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
  simp only [Matrix.cons_val, actCode, Nat.cast_zero, pcode_bot, pcode_const, cast_pBot, cast_pConst]
  rw [hopp_mirror k]

/-! #### The prudence facts, the search clauses, Mirror's copy -/

/-- **Prudence is a true closed Σ₁ fact in every model**: Mirror plays D against `.bot DefectBot`
(fuel 3: the sim step, the bot step, the constant). -/
theorem mirror_bot_defect_V : EvalGraph 3 MirrorV (pBot (pConst 1)) MirrorV (1 : V) := by
  have e0 : EvalGraph (0 + 1) (pBot (pConst 1)) MirrorV (pConst 1) (1 : V) := EvalGraph.const_iff.mpr rfl
  rw [zero_add] at e0
  have e1 : EvalGraph (1 + 1) (pBot (pConst 1)) MirrorV (pBot (pConst 1)) (1 : V) := EvalGraph.bot_iff.mpr e0
  rw [one_add_one_eq_two] at e1
  have e2 := (mirror_step_V 2 (pBot (pConst 1)) 1).mpr e1
  rwa [two_add_one_eq_three] at e2

/-- The transposed prudence fact: Mirror plays C against `.bot CooperateBot`. -/
theorem mirror_bot_coop_V : EvalGraph 3 MirrorV (pBot (pConst 0)) MirrorV (0 : V) := by
  have e0 : EvalGraph (0 + 1) (pBot (pConst 0)) MirrorV (pConst 0) (0 : V) := EvalGraph.const_iff.mpr rfl
  rw [zero_add] at e0
  have e1 : EvalGraph (1 + 1) (pBot (pConst 0)) MirrorV (pBot (pConst 0)) (0 : V) := EvalGraph.bot_iff.mpr e0
  rw [one_add_one_eq_two] at e1
  have e2 := (mirror_step_V 2 (pBot (pConst 0)) 0).mpr e1
  rwa [two_add_one_eq_three] at e2

/-- **Prudent's search clause against Mirror** (fuel 3): both guards provable within `k` ⇒ `C`. -/
theorem prudent_search_V (k : V)
    (h1 : LenProvableV TAct k (guardCode (⌜tmplP1⌝ : V) (PrudentV k) MirrorV))
    (h2 : LenProvableV TAct k (guardCode (⌜tmplP2⌝ : V) (PrudentV k) MirrorV)) :
    EvalGraph 3 (PrudentV k) MirrorV (PrudentV k) 0 := by
  have e0 : EvalGraph (0 + 1) (PrudentV k) MirrorV (pConst 0) (0 : V) := EvalGraph.const_iff.mpr rfl
  have e1 : EvalGraph (0 + 1 + 1) (PrudentV k) MirrorV (pSearch k (⌜tmplP2⌝ : V) (pConst 0) (pConst 1)) 0 :=
    (EvalGraph.search_iff₆ (isSemiformula_quote₆ tmplP2)).mpr (Or.inl ⟨h2, e0⟩)
  have e2 : EvalGraph (0 + 1 + 1 + 1) (PrudentV k) MirrorV
      (pSearch k (⌜tmplP1⌝ : V) (pSearch k (⌜tmplP2⌝ : V) (pConst 0) (pConst 1)) (pConst 1)) 0 :=
    (EvalGraph.search_iff₆ (isSemiformula_quote₆ tmplP1)).mpr (Or.inl ⟨h1, e1⟩)
  rwa [show (0 : V) + 1 + 1 + 1 = 3 by norm_num] at e2

/-- **The transposed searcher's search clause against Mirror** (fuel 3): both guards ⇒ `D`. -/
theorem prudentT_search_V (k : V)
    (h1 : LenProvableV TAct k (guardCode (⌜tmplP1T⌝ : V) (PrudentTV k) MirrorV))
    (h2 : LenProvableV TAct k (guardCode (⌜tmplP2T⌝ : V) (PrudentTV k) MirrorV)) :
    EvalGraph 3 (PrudentTV k) MirrorV (PrudentTV k) 1 := by
  have e0 : EvalGraph (0 + 1) (PrudentTV k) MirrorV (pConst 1) (1 : V) := EvalGraph.const_iff.mpr rfl
  have e1 : EvalGraph (0 + 1 + 1) (PrudentTV k) MirrorV (pSearch k (⌜tmplP2T⌝ : V) (pConst 1) (pConst 0)) 1 :=
    (EvalGraph.search_iff₆ (isSemiformula_quote₆ tmplP2T)).mpr (Or.inl ⟨h2, e0⟩)
  have e2 : EvalGraph (0 + 1 + 1 + 1) (PrudentTV k) MirrorV
      (pSearch k (⌜tmplP1T⌝ : V) (pSearch k (⌜tmplP2T⌝ : V) (pConst 1) (pConst 0)) (pConst 0)) 1 :=
    (EvalGraph.search_iff₆ (isSemiformula_quote₆ tmplP1T)).mpr (Or.inl ⟨h1, e1⟩)
  rwa [show (0 : V) + 1 + 1 + 1 = 3 by norm_num] at e2

/-- Mirror copies a fuel-3 play at fuel 4. -/
theorem mirror_copies3_V (opp a : V) (h : EvalGraph 3 opp MirrorV opp a) :
    EvalGraph 4 MirrorV opp MirrorV a := by
  rw [show (4 : V) = 3 + 1 by norm_num]
  exact (mirror_step_V 3 opp a).mpr h

end fixedFormulas

/-! ### 5. The family, its Löb premise -/

section family

/-- Prudent's half of the family: the outer guard and the prudence guard. -/
noncomputable def pPMa : Semisentence LAct 1 := qPM ⋏ qPP
/-- The transposed searcher's half. -/
noncomputable def pPMb : Semisentence LAct 1 := qPMT ⋏ qPPT
/-- **The Löb family of the Prudent × Mirror cell**: the four guards (DIMCID × Cupod's two-level
shape); the prudence conjuncts make the INNER search's box a by-product of the outer Löb box. -/
noncomputable def pPM : Semisentence LAct 1 := pPMa ⋏ pPMb

lemma pPMa_def : pPMa = qPM ⋏ qPP := rfl
lemma pPMb_def : pPMb = qPMT ⋏ qPPT := rfl
lemma pPM_def : pPM = pPMa ⋏ pPMb := rfl

lemma lMap_swap_pPMa : Semiformula.lMap swap pPMa = pPMb := by
  rw [pPMa_def, pPMb_def, LogicalConnective.HomClass.map_and, lMap_swap_qPM, lMap_swap_qPP]
lemma lMap_swap_pPMb : Semiformula.lMap swap pPMb = pPMa := by
  rw [← lMap_swap_pPMa, lMap_swap_swap]
lemma lMap_swap_pPM : Semiformula.lMap swap pPM = pPMb ⋏ pPMa := by
  rw [pPM_def, LogicalConnective.HomClass.map_and, lMap_swap_pPMa, lMap_swap_pPMb]

theorem instB_quote_pPMa (k : V) :
    instB (⌜pPMa⌝ : V) k = instB (⌜qPM⌝ : V) k ^⋏ instB (⌜qPP⌝ : V) k := instB_quote_and _ _ k
theorem instB_quote_pPMb (k : V) :
    instB (⌜pPMb⌝ : V) k = instB (⌜qPMT⌝ : V) k ^⋏ instB (⌜qPPT⌝ : V) k := instB_quote_and _ _ k
theorem instB_quote_pPM (k : V) :
    instB (⌜pPM⌝ : V) k = instB (⌜pPMa⌝ : V) k ^⋏ instB (⌜pPMb⌝ : V) k := instB_quote_and _ _ k

lemma formulaLen_instB_pPMa (k : V) :
    formulaLen LAct (instB (⌜pPMa⌝ : V) k) =
      formulaLen LAct (instB (⌜qPM⌝ : V) k) + formulaLen LAct (instB (⌜qPP⌝ : V) k) + 1 := by
  rw [instB_quote_pPMa,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]
lemma formulaLen_instB_pPMb (k : V) :
    formulaLen LAct (instB (⌜pPMb⌝ : V) k) =
      formulaLen LAct (instB (⌜qPMT⌝ : V) k) + formulaLen LAct (instB (⌜qPPT⌝ : V) k) + 1 := by
  rw [instB_quote_pPMb,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]
lemma formulaLen_instB_pPM (k : V) :
    formulaLen LAct (instB (⌜pPM⌝ : V) k) =
      formulaLen LAct (instB (⌜pPMa⌝ : V) k) + formulaLen LAct (instB (⌜pPMb⌝ : V) k) + 1 := by
  rw [instB_quote_pPM,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

/-- **Both searchers play from a box of the family** (fuel 3): the two-level ∧-elimination hands
each searcher BOTH its guards — the inner (prudence) search fires from the SAME box as the outer
one, which is what replaces the engine's `searchThenSearch_t` citation. -/
theorem pPM_all_V (k a : V) (hk : (KP : V) ≤ k)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pPMa⌝ : V) k) + formulaLen LAct (instB (⌜pPMb⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qPM⌝ : V) k) + formulaLen LAct (instB (⌜qPP⌝ : V) k)) + 7 ≤ k)
    (ha₂ : a + 8 * (formulaLen LAct (instB (⌜pPMa⌝ : V) k) + formulaLen LAct (instB (⌜pPMb⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qPMT⌝ : V) k) + formulaLen LAct (instB (⌜qPPT⌝ : V) k)) + 7 ≤ k)
    (h : LenDerivable TAct a (instB (⌜pPM⌝ : V) k)) :
    EvalGraph 3 (PrudentV k) MirrorV (PrudentV k) 0 ∧ EvalGraph 3 (PrudentTV k) MirrorV (PrudentTV k) 1 := by
  rw [instB_quote_pPM] at h
  have hx := isFormula_instB_quote pPMa k
  have hy := isFormula_instB_quote pPMb k
  have h₁ : LenDerivable TAct
      (a + 8 * (formulaLen LAct (instB (⌜pPMa⌝ : V) k) + formulaLen LAct (instB (⌜pPMb⌝ : V) k)) + 7)
      (instB (⌜qPM⌝ : V) k ^⋏ instB (⌜qPP⌝ : V) k) := by
    rw [← instB_quote_pPMa]; exact lenDerivable_andL_V hx hy h
  have h₂ : LenDerivable TAct
      (a + 8 * (formulaLen LAct (instB (⌜pPMa⌝ : V) k) + formulaLen LAct (instB (⌜pPMb⌝ : V) k)) + 7)
      (instB (⌜qPMT⌝ : V) k ^⋏ instB (⌜qPPT⌝ : V) k) := by
    rw [← instB_quote_pPMb]; exact lenDerivable_andR_V hx hy h
  have hx₁ := isFormula_instB_quote qPM k
  have hy₁ := isFormula_instB_quote qPP k
  have hx₂ := isFormula_instB_quote qPMT k
  have hy₂ := isFormula_instB_quote qPPT k
  have g1 := lenDerivable_mono_V ha₁ (lenDerivable_andL_V hx₁ hy₁ h₁)
  have g2 := lenDerivable_mono_V ha₁ (lenDerivable_andR_V hx₁ hy₁ h₁)
  have g3 := lenDerivable_mono_V ha₂ (lenDerivable_andL_V hx₂ hy₂ h₂)
  have g4 := lenDerivable_mono_V ha₂ (lenDerivable_andR_V hx₂ hy₂ h₂)
  rw [lenDerivable_iff_lenProvableV, ← guardCode_PrudentV_MirrorV_eq_instB hk] at g1
  rw [lenDerivable_iff_lenProvableV, ← guardCode_PrudentV_MirrorV_inner_eq_instB hk] at g2
  rw [lenDerivable_iff_lenProvableV, ← guardCode_PrudentTV_MirrorV_eq_instB hk] at g3
  rw [lenDerivable_iff_lenProvableV, ← guardCode_PrudentTV_MirrorV_inner_eq_instB hk] at g4
  exact ⟨prudent_search_V k g1 g2, prudentT_search_V k g3 g4⟩

/-- **The box form**: Prudent's two guards against Mirror are provable within `k`. -/
theorem pPM_guards_V (k a : V) (hk : (KP : V) ≤ k)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pPMa⌝ : V) k) + formulaLen LAct (instB (⌜pPMb⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qPM⌝ : V) k) + formulaLen LAct (instB (⌜qPP⌝ : V) k)) + 7 ≤ k)
    (h : LenDerivable TAct a (instB (⌜pPM⌝ : V) k)) :
    LenProvableV TAct k (guardCode (⌜tmplP1⌝ : V) (PrudentV k) MirrorV) ∧
    LenProvableV TAct k (guardCode (⌜tmplP2⌝ : V) (PrudentV k) MirrorV) := by
  rw [instB_quote_pPM] at h
  have hx := isFormula_instB_quote pPMa k
  have hy := isFormula_instB_quote pPMb k
  have h₁ : LenDerivable TAct
      (a + 8 * (formulaLen LAct (instB (⌜pPMa⌝ : V) k) + formulaLen LAct (instB (⌜pPMb⌝ : V) k)) + 7)
      (instB (⌜qPM⌝ : V) k ^⋏ instB (⌜qPP⌝ : V) k) := by
    rw [← instB_quote_pPMa]; exact lenDerivable_andL_V hx hy h
  have hx₁ := isFormula_instB_quote qPM k
  have hy₁ := isFormula_instB_quote qPP k
  have g1 := lenDerivable_mono_V ha₁ (lenDerivable_andL_V hx₁ hy₁ h₁)
  have g2 := lenDerivable_mono_V ha₁ (lenDerivable_andR_V hx₁ hy₁ h₁)
  rw [lenDerivable_iff_lenProvableV, ← guardCode_PrudentV_MirrorV_eq_instB hk] at g1
  rw [lenDerivable_iff_lenProvableV, ← guardCode_PrudentV_MirrorV_inner_eq_instB hk] at g2
  exact ⟨g1, g2⟩

/-! #### `pPM` in both readings -/

/-- `pPM(k)` in the standard reading (above the threshold). -/
theorem eval_pPM_iff_std {k : V} (hk : (KP : V) ≤ k) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim pPM ↔
      ((∃ n, EvalGraph n MirrorV (PrudentV k) MirrorV 0) ∧ (∃ n, EvalGraph n (MirrorV : V) (pBot (pConst 1)) MirrorV 1)) ∧
      ((∃ n, EvalGraph n MirrorV (PrudentTV k) MirrorV 1) ∧ (∃ n, EvalGraph n (MirrorV : V) (pBot (pConst 0)) MirrorV 0)) := by
  rw [pPM_def, pPMa_def, pPMb_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qPM_iff_V hk, eval_qPP_iff_V, eval_qPMT_iff_V hk, eval_qPPT_iff_V]

/-- `pPM(k)` in the swapped reading: the SAME four facts (the halves exchange roles). -/
theorem eval_pPM_iff_swap {k : V} (hk : (KP : V) ≤ k) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim pPM ↔
      ((∃ n, EvalGraph n MirrorV (PrudentTV k) MirrorV 1) ∧ (∃ n, EvalGraph n (MirrorV : V) (pBot (pConst 0)) MirrorV 0)) ∧
      ((∃ n, EvalGraph n MirrorV (PrudentV k) MirrorV 0) ∧ (∃ n, EvalGraph n (MirrorV : V) (pBot (pConst 1)) MirrorV 1)) := by
  rw [eval_swapActS, lMap_swap_pPM, ← stdActV_eq_stdActS, pPMa_def, pPMb_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qPM_iff_V hk, eval_qPP_iff_V, eval_qPMT_iff_V hk, eval_qPPT_iff_V]

theorem eval_pPM_iff_stdActS {k : V} (hk : (KP : V) ≤ k) :
    Semiformula.Eval (s := stdActS V) ![k] Empty.elim pPM ↔
      ((∃ n, EvalGraph n MirrorV (PrudentV k) MirrorV 0) ∧ (∃ n, EvalGraph n (MirrorV : V) (pBot (pConst 1)) MirrorV 1)) ∧
      ((∃ n, EvalGraph n MirrorV (PrudentTV k) MirrorV 1) ∧ (∃ n, EvalGraph n (MirrorV : V) (pBot (pConst 0)) MirrorV 0)) := by
  rw [← stdActV_eq_stdActS]; exact eval_pPM_iff_std hk

/-- **The bounded Löb premise of the Prudent × Mirror family, slack `(14 + KP, 16)`**: a box of
`pPM(k)` with the slack (which also puts `k` above the description threshold) makes both searchers
play at fuel 3 (`pPM_all_V`), Mirror copies at fuel 4, and the two prudence facts hold outright —
so `pPM(k)` is TRUE in both readings. -/
theorem loebSound_pPM : LoebSound pPM (14 + KP) 16 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have hk : (KP : V) ≤ k :=
    le_trans (Nat.cast_le.mpr (Nat.le_add_left KP 14)) (le_trans le_add_self (le_trans le_self_add ha))
  have h14 : ((14 : ℕ) : V) ≤ ((14 + KP : ℕ) : V) := Nat.cast_le.mpr (Nat.le_add_right 14 KP)
  have hb : a + ((14 : ℕ) : V) + ((16 : ℕ) : V) * formulaLen LAct (instB (⌜pPM⌝ : V) k) ≤
      a + ((14 + KP : ℕ) : V) + ((16 : ℕ) : V) * formulaLen LAct (instB (⌜pPM⌝ : V) k) :=
    _root_.add_le_add_left (_root_.add_le_add_right h14 a) _
  have ha₁ := le_trans (slack4_le a _ _ _ _ _ (formulaLen_instB_pPMa k) (formulaLen_instB_pPM k)) (le_trans hb ha)
  have ha₂ := le_trans (slack4_le' a _ _ _ _ _ (formulaLen_instB_pPMb k) (formulaLen_instB_pPM k)) (le_trans hb ha)
  obtain ⟨g1, g2⟩ := pPM_all_V k a hk ha₁ ha₂ h
  exact ⟨(eval_pPM_iff_stdActS hk).mpr
      ⟨⟨⟨4, mirror_copies3_V _ _ g1⟩, ⟨3, mirror_bot_defect_V⟩⟩, ⟨⟨4, mirror_copies3_V _ _ g2⟩, ⟨3, mirror_bot_coop_V⟩⟩⟩,
    (eval_pPM_iff_swap hk).mpr
      ⟨⟨⟨4, mirror_copies3_V _ _ g2⟩, ⟨3, mirror_bot_coop_V⟩⟩, ⟨⟨4, mirror_copies3_V _ _ g1⟩, ⟨3, mirror_bot_defect_V⟩⟩⟩⟩

end family

/-! ### 6. The cells at ℕ -/

section cells

/-- **The Prudent × Mirror cell, packaged**: for all large `k`, Prudent cooperates with Mirror and
its transposition defects (fuel 3), and both of Prudent's guard boxes hold — `family_found pPM` then
the two-level ∧-elimination. -/
theorem prudent_mirror_cell_core {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 3 (Prudent k) Mirror (Prudent k) 0 ∧ EvalGraph 3 (PrudentT k) Mirror (PrudentT k) 1) ∧
      (LenProvableV TAct k (guardCode (⌜tmplP1⌝ : ℕ) (Prudent k) Mirror) ∧
        LenProvableV TAct k (guardCode (⌜tmplP2⌝ : ℕ) (Prudent k) Mirror)) := by
  obtain ⟨k₀, h⟩ := family_found pPM hE loebSound_pPM
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha₁ := le_def.mpr (slack4_nat a _ _ _ _ _ k (formulaLen_instB_pPMa (V := ℕ) k)
    (formulaLen_instB_pPM (V := ℕ) k) (by omega))
  have ha₂ := le_def.mpr (slack4_nat' a _ _ _ _ _ k (formulaLen_instB_pPMb (V := ℕ) k)
    (formulaLen_instB_pPM (V := ℕ) k) (by omega))
  refine ⟨pPM_all_V (V := ℕ) k a ?_ ha₁ ha₂ hpc, pPM_guards_V (V := ℕ) k a ?_ ha₁ hpc⟩ <;>
    (rw [natCast_nat]; exact le_def.mpr (Nat.eq_or_lt_of_le (by omega)))

/-- **PrudentBot × Mirror is `(C, C)` in PA-`S'`, conditional on bounded inner necessitation**: for
all large `k`, `Prudent k` cooperates with Mirror (fuel 3) and Mirror copies (fuel 4). -/
theorem prudent_mirror_coop {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 3 (Prudent k) Mirror (Prudent k) 0 ∧ EvalGraph 4 Mirror (Prudent k) Mirror 0 := by
  obtain ⟨k₀, h⟩ := prudent_mirror_cell_core hE
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1.1, mirror_copies3_V (V := ℕ) _ _ (h k hk).1.1⟩⟩

/-- **τ(PrudentBot) × Mirror is `(D, D)`**, conditional: the transposed searcher defects against
Mirror (fuel 3) and Mirror copies (fuel 4). -/
theorem prudentT_mirror_defect {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 3 (PrudentT k) Mirror (PrudentT k) 1 ∧ EvalGraph 4 Mirror (PrudentT k) Mirror 1 := by
  obtain ⟨k₀, h⟩ := prudent_mirror_cell_core hE
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1.2, mirror_copies3_V (V := ℕ) _ _ (h k hk).1.2⟩⟩

/-- **The box form**: for all large `k`, Prudent FINDS proofs of BOTH its guards against Mirror
within its budget `k` (conditional). -/
theorem prudent_finds_guards_vs_mirror {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (⌜tmplP1⌝ : ℕ) (Prudent k) Mirror) ∧
      LenProvableV TAct k (guardCode (⌜tmplP2⌝ : ℕ) (Prudent k) Mirror) := by
  obtain ⟨k₀, h⟩ := prudent_mirror_cell_core hE
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

/-! #### Unconditional, at `boundedInnerNec_sixteen` -/

/-- **PrudentBot × Mirror `(C, C)` in PA-`S'`, unconditional**: for all large `k`, `Prudent k`
cooperates with Mirror (fuel 3: outer search, inner search, constant) and Mirror copies (fuel 4). -/
theorem prudent_mirror_coop_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 3 (Prudent k) Mirror (Prudent k) 0 ∧ EvalGraph 4 Mirror (Prudent k) Mirror 0 :=
  prudent_mirror_coop boundedInnerNec_sixteen

/-- **τ(PrudentBot) × Mirror `(D, D)` in PA-`S'`, unconditional.** -/
theorem prudentT_mirror_defect_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 3 (PrudentT k) Mirror (PrudentT k) 1 ∧ EvalGraph 4 Mirror (PrudentT k) Mirror 1 :=
  prudentT_mirror_defect boundedInnerNec_sixteen

/-- **Prudent finds both its guards against Mirror, unconditional.** -/
theorem prudent_finds_guards_vs_mirror_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (⌜tmplP1⌝ : ℕ) (Prudent k) Mirror) ∧
      LenProvableV TAct k (guardCode (⌜tmplP2⌝ : ℕ) (Prudent k) Mirror) :=
  prudent_finds_guards_vs_mirror boundedInnerNec_sixteen

end cells

end ArithS
