import ArithS.Cells.FloorVerdicts

/-!
# ArithS.Cells.FloorDichotomy — the genuine floors as DICHOTOMIES, hypothesis-free

`Research/Notes/ROUTE_B_SCOPE.md` §6 and `ROUTE_B_CENSUS.md` "S' status per cell". The floor
verdict pass (`Cells/FloorVerdicts`) classified 26 engine cells as GENUINE floors in PA-`S'`: the floor side's
guard is TRUE in ℕ, and its only evaluation witness runs through the ELSE branch of a search node whose guard
σ is FALSE in ℕ — so its provability within the budget `k` is inter-derivable, up to additive overhead, with the
bounded consistency statement `Con_TAct(k ± c)`, the LINEAR-regime finite-consistency question that is OPEN in
both directions (Pudlák). The engine's `+k` floor (`search_f`) STIPULATES the negative side; `S'` takes no side.

This module states, for each of the 26 cells, what `S'` CAN prove without taking a side: a **dichotomy**. With
`A_k` the cell's HINGE — the Lean proposition `LenBox TAct k (guardCodeB (templateCode φ) (progCode me) (progCode opp) k)`,
the evaluator's literal guard clause for the floor side's outermost search node at its own budget, written
INLINE in every statement (no structure, no named hypothesis, no conditional value in the ledger) —

  `dich_<L>_vs_<R> : ∃ k₀, ∀ k > k₀, (¬ A_k → ⟨the engine's value⟩) ∧ (A_k → ⟨the found-branch value⟩)`,

both worlds at the engine's fuel on the engine's own codes. The ELSE world is the verdict pass's settled half
plus the search-else clause; the THEN world is the then-branch plus the partner's play, which the same probers
determine — and where the partner is itself a searcher whose guard speaks about the floor side, SOUNDNESS of the
found hinge (`models_sentenceAt_of_lenBox`) plus the evaluator's determinism recover the partner's verdict
(`found_of_search_play`, `play_of_found_opp_self`). Cells with TWO or THREE hinges (the bistable-modulo-reflection
pairs Wary × Dupoc/Just/Prudent, Cupod × Prudent both ways, Just × Cupod, CIMCIC × Cupod, and the prudence floors
Just/CIMCIC/Guardian × Prudent) are stated as NESTED dichotomies: the outer case split on the hinge that settles
the most, the inner one on the remaining hinge(s); every case whose plays are determined is proved, and the
inconsistent combinations (both guards found when each refutes the other) are absorbed by soundness — e.g.
Wary × Dupoc: `W → (D, D)` (Wary's found `.neg` guard refutes Dupoc's), `¬W → Wary C ∧ (¬A → Dupoc D) ∧ (A → Dupoc C)`.
Prudent's PRUDENCE guard `B_k` ("opp defects against `.bot DefectBot`") is a hinge of its own in five cells (Just/
CIMCIC/Guardian/Wary/Cupod × Prudent): the verdict pass rates it (P) — found for large `k` — but that `k̂`-chain
is not built here, so it stays a hinge; against EBot it IS proved found (`prudence_found_vs_EBot`: a closed
search-free atom), so Prudent × EBot has one hinge, and its ELSE world settles only Prudent's side (EBot's C there
is Prudent's Löb cooperation with `.bot MirrorBot`, not built — `FloorVerdicts` §3).

**The reduction theorem** (`hinge_reduces_to_bounded_consistency_DupocBot_vs_DBot`, §4): for the simplest cell, the
hinge `A_k` = "DBot plays C against `DupocBot k`" provable within `k` yields a `TAct`-proof, within
`k + C₀ + C₁·size k`, of the sentence "`σ_k` or its τ-twin is NOT provable within `k`", where `σ_k` is Dupoc's guard
against `.bot DefectBot` ("`.bot DefectBot` plays C against `DupocBot k`", FALSE in ℕ) — the τ-symmetrized bounded
consistency instance (`TAct ⊢ ¬σ_k` cheaply, so `□_k σ_k → □_{k+c} ⊥`); the disjunction is what `TAct`, which cannot
tell its two standard readings apart, proves uniformly (its two disjuncts are equivalent at ℕ:
`negTwin_true_iff`). The CONVERSE (`bounded_consistency_reduces_to_hinge_DupocBot_vs_DBot`): a proof within `m` of
the CONJUNCTION "neither `σ_k` nor its twin is provable within `k`" yields the hinge within `m + C₀ + C₁·size k`, by
the evaluator's determinism inside `TAct` (`EvalGraph.search_iff₆` in every model). The additive overhead is the
cost of one instantiation and one modus ponens, whose cut formulas carry the binary numeral of `k`.

Naming: `dich_<L>_vs_<R>` on the engine's constructors; the hinge lemmas `found_of_search_play`
(a play through a search node with a constant else-branch that differs from it: the guard was FOUND, the
then-branch played), `not_found_of_search_play`, `play_of_found_opp_self/_opp_bot/_cimcic/_neg` (soundness of a
found guard as the partner's play); totality `prudent_total`, `ebot_total`, `cimcic_total`.

Conventions: every threshold EXISTENTIAL; `simp` never sees a closed quote; statements pin the fuel to the engine's
pad (`EvalGraph.mono_le` lifts); no `sorry`, no `axiom`, no `native_decide`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

/-! ### 1. The hinge lemmas -/

section hinge

/-- The evaluator's literal guard clause on a six-variable engine template is the pre-route-(c) guard code
(`guardCodeB_of_template`): the hinge as written in every statement, unfolded in every proof. -/
lemma hingeB (φ : PD.Formula) (x y k : ℕ) (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    guardCodeB (templateCode φ) x y k = guardCode (templateCode φ) x y :=
  guardCodeB_of_template (isSemiformula_templateCode φ) x y k

/-- **A play through a search node whose else-branch is a constant it differs from is a FOUND guard**: the
then-branch played it (determinism of the evaluator, `EvalGraph.search_iff₆` + `EvalGraph.const_iff`). -/
theorem found_of_search_play {N k x y a b : ℕ} (φ : PD.Formula) {p : ℕ}
    (h : EvalGraph N x y (pSearch k (templateCode φ) p (pConst b)) a) (hab : a ≠ b)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    LenBox TAct k (guardCode (templateCode φ) x y) ∧ ∃ N', EvalGraph N' x y p a := by
  obtain ⟨N', rfl, _⟩ := EvalGraph.case_iff.mp h
  rcases (EvalGraph.search_iff₆ (isSemiformula_templateCode φ)).mp h with ⟨hf, hp⟩ | ⟨_, hq⟩
  · exact ⟨hf, N', hp⟩
  · exfalso
    obtain ⟨N'', rfl, _⟩ := EvalGraph.case_iff.mp hq
    exact hab (EvalGraph.const_iff.mp hq)

/-- The dual: a play through a search node whose THEN-branch is a constant it differs from is a guard NOT
found; the else-branch played it. -/
theorem not_found_of_search_play {N k x y a b : ℕ} (φ : PD.Formula) {q : ℕ}
    (h : EvalGraph N x y (pSearch k (templateCode φ) (pConst b) q) a) (hab : a ≠ b)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    ¬ LenBox TAct k (guardCode (templateCode φ) x y) ∧ ∃ N', EvalGraph N' x y q a := by
  obtain ⟨N', rfl, _⟩ := EvalGraph.case_iff.mp h
  rcases (EvalGraph.search_iff₆ (isSemiformula_templateCode φ)).mp h with ⟨_, hp⟩ | ⟨hn, hq⟩
  · exfalso
    obtain ⟨N'', rfl, _⟩ := EvalGraph.case_iff.mp hp
    exact hab (EvalGraph.const_iff.mp hp)
  · exact ⟨hn, N', hq⟩

/-- **Soundness of a found `.plays .opp .self a` guard**: the opponent plays `a` against `me`
(`models_sentenceAt_of_lenBox` + the truth equation). -/
theorem play_of_found_opp_self {me opp : PD.Prog} (hme : ProperPlayer me) (hopp : ProperPlayer opp) (a : PD.Action) {k : ℕ}
    (h : LenBox TAct k (guardCode (templateCode (.plays .opp .self a)) (progCode me) (progCode opp))) :
    ∃ N, EvalGraph N (progCode opp) (progCode me) (progCode opp) (actCode a) := by
  have hT := models_sentenceAt_of_lenBox (φ := .plays .opp .self a) (me := me) (opp := opp) h
  rw [← sentenceAt_subst me opp hme hopp _ rfl] at hT
  change ℕ↓[LAct] ⊧ sentenceAt me opp (.plays opp me a) at hT
  rwa [models_sentenceAt_plays me opp opp me a hopp hme] at hT

/-- Soundness of a found `.plays .opp (.bot P) a` guard: the opponent plays `a` against the frozen `.bot P`. -/
theorem play_of_found_opp_bot {me opp : PD.Prog} (hme : ProperPlayer me) (hopp : ProperPlayer opp) {P : PD.Prog}
    (hfP : fragP P = true) (a : PD.Action) {k : ℕ}
    (h : LenBox TAct k (guardCode (templateCode (.plays .opp (.bot P) a)) (progCode me) (progCode opp))) :
    ∃ N, EvalGraph N (progCode opp) (pBot (progCode P)) (progCode opp) (actCode a) := by
  have hT := models_sentenceAt_of_lenBox (φ := .plays .opp (.bot P) a) (me := me) (opp := opp) h
  rw [← sentenceAt_subst me opp hme hopp _ (by simp [fragF, fragP, atomicP, closedP, hfP])] at hT
  change ℕ↓[LAct] ⊧ sentenceAt me opp (.plays opp (.bot P) a) at hT
  rwa [models_sentenceAt_plays me opp opp (.bot P) a hopp (properPlayer_bot P), progCode_bot] at hT

/-- Soundness of a found `.neg (.plays .opp .self a)` guard: the opponent does NOT play `a` against `me`. -/
theorem play_of_found_neg {me opp : PD.Prog} (hme : ProperPlayer me) (hopp : ProperPlayer opp) (a : PD.Action) {k : ℕ}
    (h : LenBox TAct k (guardCode (templateCode (.neg (.plays .opp .self a))) (progCode me) (progCode opp))) :
    ¬ ∃ N, EvalGraph N (progCode opp) (progCode me) (progCode opp) (actCode a) := by
  have hT := models_sentenceAt_of_lenBox (φ := .neg (.plays .opp .self a)) (me := me) (opp := opp) h
  rw [← sentenceAt_subst me opp hme hopp _ rfl] at hT
  change ℕ↓[LAct] ⊧ sentenceAt me opp (.neg (.plays opp me a)) at hT
  rwa [models_sentenceAt_neg, models_sentenceAt_plays me opp opp me a hopp hme] at hT

/-- **Soundness of CIMCIC's found guard**: CIMCIC cooperates (the then-branch) and, the implication being
true, so does the opponent. -/
theorem play_of_found_cimcic (k : ℕ) {opp : PD.Prog} (hopp : ProperPlayer opp)
    (h : LenBox TAct k (guardCode (templateCode phiC) (progCode (CIMCIC k)) (progCode opp))) :
    EvalGraph 2 (progCode (CIMCIC k)) (progCode opp) (progCode (CIMCIC k)) 0 ∧
    ∃ N, EvalGraph N (progCode opp) (progCode (CIMCIC k)) (progCode opp) 0 := by
  have hC : EvalGraph 2 (progCode (CIMCIC k)) (progCode opp) (progCode (CIMCIC k)) 0 := by
    rw [progCode_CIMCIC_search] at h ⊢
    exact search_then phiC h (const_play _ _ _ _)
  have hT : ℕ↓[LAct] ⊧ sentenceAt (CIMCIC k) opp phiC :=
    models_sentenceAt_of_lenBox (φ := phiC) (me := CIMCIC k) (opp := opp) h
  rw [← sentenceAt_subst (CIMCIC k) opp (properPlayer_CIMCIC k) hopp phiC rfl] at hT
  change ℕ↓[LAct] ⊧ sentenceAt (CIMCIC k) opp (.impl (.plays (CIMCIC k) opp .C) (.plays opp (CIMCIC k) .C)) at hT
  rw [models_sentenceAt_impl, models_sentenceAt_plays _ _ _ _ _ (properPlayer_CIMCIC k) hopp,
    models_sentenceAt_plays _ _ _ _ _ hopp (properPlayer_CIMCIC k)] at hT
  exact ⟨hC, hT ⟨2, hC⟩⟩

/-- Prudent always plays in a proper frame (fuel 3), whatever the two verdicts. -/
theorem prudent_total (k x : ℕ) : ∃ r, EvalGraph 3 (progCode (PrudentBot k)) x (progCode (PrudentBot k)) r := by
  rw [progCode_PrudentBot_search]
  by_cases ho : LenBox TAct k (guardCode (templateCode phiPo)
      (pSearch k (templateCode phiPo) (pSearch k (templateCode phiPi) (pConst 0) (pConst 1)) (pConst 1)) x)
  · by_cases hi : LenBox TAct k (guardCode (templateCode phiPi)
        (pSearch k (templateCode phiPo) (pSearch k (templateCode phiPi) (pConst 0) (pConst 1)) (pConst 1)) x)
    · exact ⟨0, search_then phiPo ho (search_then phiPi hi (const_play 0 _ _ _))⟩
    · exact ⟨1, search_then phiPo ho (search_else phiPi hi (const_play 0 _ _ _))⟩
  · exact ⟨1, search_else phiPo ho (const_play 1 _ _ _)⟩

/-- CIMCIC always plays in a proper frame (fuel 2). -/
theorem cimcic_total (k x : ℕ) : ∃ r, EvalGraph 2 (progCode (CIMCIC k)) x (progCode (CIMCIC k)) r := by
  rw [progCode_CIMCIC_search]
  by_cases hg : LenBox TAct k (guardCode (templateCode phiC) (pSearch k (templateCode phiC) (pConst 0) (pConst 1)) x)
  · exact ⟨0, search_then phiC hg (const_play 0 _ _ _)⟩
  · exact ⟨1, search_else phiC hg (const_play 0 _ _ _)⟩

/-- EBot always plays against an opponent that plays against its three frozen probes (fuel `+4`). -/
theorem ebot_total {x n r₁ r₂ r₃ : ℕ} (h1 : EvalGraph n x (pBot (pConst 1)) x r₁)
    (h2 : EvalGraph n x (pBot (pConst 0)) x r₂) (h3 : EvalGraph n x (pBot Mirror) x r₃) :
    ∃ r, EvalGraph (n + 1 + 1 + 1 + 1) (progCode EBot) x (progCode EBot) r := by
  simp only [EBot, CooperateBot, DefectBot, MirrorBot, progCode_ite, progCode_sim, progCode_opp, progCode_self, progCode_bot,
    progCode_const, actCode]
  by_cases e1 : r₁ = 0
  · refine ⟨1, ?_⟩
    rw [EvalGraph.ite_iff]
    refine ⟨r₁, ?_, Or.inl ⟨e1, const_play _ _ _ _⟩⟩
    rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
    exact EvalGraph.mono_le (by omega) h1
  · by_cases e2 : r₂ = 0
    · refine ⟨0, ?_⟩
      rw [EvalGraph.ite_iff]
      refine ⟨r₁, ?_, Or.inr ⟨e1, ?_⟩⟩
      · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
        exact EvalGraph.mono_le (by omega) h1
      · rw [EvalGraph.ite_iff]
        refine ⟨r₂, ?_, Or.inl ⟨e2, const_play _ _ _ _⟩⟩
        rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
        exact EvalGraph.mono_le (by omega) h2
    · by_cases e3 : r₃ = 0
      · refine ⟨0, ?_⟩
        rw [EvalGraph.ite_iff]
        refine ⟨r₁, ?_, Or.inr ⟨e1, ?_⟩⟩
        · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
          exact EvalGraph.mono_le (by omega) h1
        · rw [EvalGraph.ite_iff]
          refine ⟨r₂, ?_, Or.inr ⟨e2, ?_⟩⟩
          · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
            exact EvalGraph.mono_le (by omega) h2
          · rw [EvalGraph.ite_iff]
            refine ⟨r₃, ?_, Or.inl ⟨e3, const_play _ _ _ _⟩⟩
            rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
            exact h3
      · refine ⟨1, ?_⟩
        rw [EvalGraph.ite_iff]
        refine ⟨r₁, ?_, Or.inr ⟨e1, ?_⟩⟩
        · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
          exact EvalGraph.mono_le (by omega) h1
        · rw [EvalGraph.ite_iff]
          refine ⟨r₂, ?_, Or.inr ⟨e2, ?_⟩⟩
          · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
            exact EvalGraph.mono_le (by omega) h2
          · rw [EvalGraph.ite_iff]
            refine ⟨r₃, ?_, Or.inr ⟨e3, const_play _ _ _ _⟩⟩
            rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
            exact h3

end hinge

/-! ### 2. The thirteen single-hinge cells: a settled search-free or SND partner -/

section single

/-- **Dupoc × DBot** (engine `outcome_DupocBot_vs_DBot = (D, C)`, pad 4). Hinge: Dupoc's guard "DBot plays C
against me" (TRUE, `floor_DupocBot_vs_DBot_true`). Not found ⇒ `(D, C)`; found ⇒ `(C, C)`. DBot's C is settled
either way (`floor_DupocBot_vs_DBot_right`). -/
theorem dich_DupocBot_vs_DBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode DBot) k) →
        EvalGraph 4 (progCode (DupocBot k)) (progCode DBot) (progCode (DupocBot k)) (actCode .D) ∧
        EvalGraph 4 (progCode DBot) (progCode (DupocBot k)) (progCode DBot) (actCode .C)) ∧
      (LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode DBot) k) →
        EvalGraph 4 (progCode (DupocBot k)) (progCode DBot) (progCode (DupocBot k)) (actCode .C) ∧
        EvalGraph 4 (progCode DBot) (progCode (DupocBot k)) (progCode DBot) (actCode .C)) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiDu]
  constructor
  · intro hn
    refine ⟨?_, floor_DupocBot_vs_DBot_right k⟩
    rw [progCode_DupocBot_search] at hn ⊢
    exact EvalGraph.mono_le (by omega) (search_else phiDu hn (const_play 0 _ _ _))
  · intro hf
    refine ⟨?_, floor_DupocBot_vs_DBot_right k⟩
    rw [progCode_DupocBot_search] at hf ⊢
    exact EvalGraph.mono_le (by omega) (search_then phiDu hf (const_play 0 _ _ _))

/-- **Dupoc × EBot** (engine `(D, C)`, pad 5). Hinge: Dupoc's guard "EBot plays C against me". -/
theorem dich_DupocBot_vs_EBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode EBot) k) →
        EvalGraph 5 (progCode (DupocBot k)) (progCode EBot) (progCode (DupocBot k)) (actCode .D) ∧
        EvalGraph 5 (progCode EBot) (progCode (DupocBot k)) (progCode EBot) (actCode .C)) ∧
      (LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode EBot) k) →
        EvalGraph 5 (progCode (DupocBot k)) (progCode EBot) (progCode (DupocBot k)) (actCode .C) ∧
        EvalGraph 5 (progCode EBot) (progCode (DupocBot k)) (progCode EBot) (actCode .C)) := by
  obtain ⟨k₀, hE⟩ := floor_DupocBot_vs_EBot_right
  refine ⟨k₀, fun k hk ↦ ?_⟩
  simp only [hingeB phiDu]
  constructor
  · intro hn
    refine ⟨?_, hE k hk⟩
    rw [progCode_DupocBot_search] at hn ⊢
    exact EvalGraph.mono_le (by omega) (search_else phiDu hn (const_play 0 _ _ _))
  · intro hf
    refine ⟨?_, hE k hk⟩
    rw [progCode_DupocBot_search] at hf ⊢
    exact EvalGraph.mono_le (by omega) (search_then phiDu hf (const_play 0 _ _ _))

/-- **Dupoc × CupodTroll** (engine `(D, C)`, pad 2). Hinge: Dupoc's guard "CupodTroll plays C against me". -/
theorem dich_DupocBot_vs_CupodTrollBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (CupodTrollBot k)) k) →
        EvalGraph 2 (progCode (DupocBot k)) (progCode (CupodTrollBot k)) (progCode (DupocBot k)) (actCode .D) ∧
        EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (DupocBot k)) (progCode (CupodTrollBot k)) (actCode .C)) ∧
      (LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (CupodTrollBot k)) k) →
        EvalGraph 2 (progCode (DupocBot k)) (progCode (CupodTrollBot k)) (progCode (DupocBot k)) (actCode .C) ∧
        EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (DupocBot k)) (progCode (CupodTrollBot k)) (actCode .C)) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiDu]
  constructor
  · intro hn
    refine ⟨?_, floor_DupocBot_vs_CupodTrollBot_right k⟩
    rw [progCode_DupocBot_search] at hn ⊢
    exact search_else phiDu hn (const_play 0 _ _ _)
  · intro hf
    refine ⟨?_, floor_DupocBot_vs_CupodTrollBot_right k⟩
    rw [progCode_DupocBot_search] at hf ⊢
    exact search_then phiDu hf (const_play 0 _ _ _)

/-- **Just × DBot** (engine `(D, C)`, pad 4). Hinge: Just's guard "DBot plays C against `.bot (DupocBot k)`". -/
theorem dich_JustBot_vs_DBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode DBot) k) →
        EvalGraph 4 (progCode (JustBot k)) (progCode DBot) (progCode (JustBot k)) (actCode .D) ∧
        EvalGraph 4 (progCode DBot) (progCode (JustBot k)) (progCode DBot) (actCode .C)) ∧
      (LenBox TAct k (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode DBot) k) →
        EvalGraph 4 (progCode (JustBot k)) (progCode DBot) (progCode (JustBot k)) (actCode .C) ∧
        EvalGraph 4 (progCode DBot) (progCode (JustBot k)) (progCode DBot) (actCode .C)) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB (phiJ k)]
  constructor
  · intro hn
    refine ⟨?_, floor_JustBot_vs_DBot_right k⟩
    rw [progCode_JustBot] at hn ⊢
    exact EvalGraph.mono_le (by omega) (search_else_at (phiJ k) hn (const_play 0 _ _ _))
  · intro hf
    refine ⟨?_, floor_JustBot_vs_DBot_right k⟩
    rw [progCode_JustBot] at hf ⊢
    exact EvalGraph.mono_le (by omega) (search_then_at (phiJ k) hf (const_play 0 _ _ _))

/-- **Just × EBot** (engine `(D, C)`, pad 5). Hinge: Just's guard "EBot plays C against `.bot (DupocBot k)`". -/
theorem dich_JustBot_vs_EBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode EBot) k) →
        EvalGraph 5 (progCode (JustBot k)) (progCode EBot) (progCode (JustBot k)) (actCode .D) ∧
        EvalGraph 5 (progCode EBot) (progCode (JustBot k)) (progCode EBot) (actCode .C)) ∧
      (LenBox TAct k (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode EBot) k) →
        EvalGraph 5 (progCode (JustBot k)) (progCode EBot) (progCode (JustBot k)) (actCode .C) ∧
        EvalGraph 5 (progCode EBot) (progCode (JustBot k)) (progCode EBot) (actCode .C)) := by
  obtain ⟨k₀, hE⟩ := floor_JustBot_vs_EBot_right
  refine ⟨k₀, fun k hk ↦ ?_⟩
  simp only [hingeB (phiJ k)]
  constructor
  · intro hn
    refine ⟨?_, hE k hk⟩
    rw [progCode_JustBot] at hn ⊢
    exact EvalGraph.mono_le (by omega) (search_else_at (phiJ k) hn (const_play 0 _ _ _))
  · intro hf
    refine ⟨?_, hE k hk⟩
    rw [progCode_JustBot] at hf ⊢
    exact EvalGraph.mono_le (by omega) (search_then_at (phiJ k) hf (const_play 0 _ _ _))

/-- **Just × CupodTroll** (engine `(D, C)`, pad 2). Hinge: Just's guard "CupodTroll plays C against the snapshot". -/
theorem dich_JustBot_vs_CupodTrollBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode (CupodTrollBot k)) k) →
        EvalGraph 2 (progCode (JustBot k)) (progCode (CupodTrollBot k)) (progCode (JustBot k)) (actCode .D) ∧
        EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (JustBot k)) (progCode (CupodTrollBot k)) (actCode .C)) ∧
      (LenBox TAct k (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode (CupodTrollBot k)) k) →
        EvalGraph 2 (progCode (JustBot k)) (progCode (CupodTrollBot k)) (progCode (JustBot k)) (actCode .C) ∧
        EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (JustBot k)) (progCode (CupodTrollBot k)) (actCode .C)) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB (phiJ k)]
  constructor
  · intro hn
    refine ⟨?_, floor_JustBot_vs_CupodTrollBot_right k⟩
    rw [progCode_JustBot] at hn ⊢
    exact search_else_at (phiJ k) hn (const_play 0 _ _ _)
  · intro hf
    refine ⟨?_, floor_JustBot_vs_CupodTrollBot_right k⟩
    rw [progCode_JustBot] at hf ⊢
    exact search_then_at (phiJ k) hf (const_play 0 _ _ _)

/-- **CIMCIC × CupodTroll** (engine `(D, C)`, pad 2). Hinge: CIMCIC's guard "I cooperate with CupodTroll ⇒ it
cooperates with me" (TRUE: its consequent is CupodTroll's else-play). -/
theorem dich_CIMCIC_vs_CupodTrollBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (CupodTrollBot k)) k) →
        EvalGraph 2 (progCode (CIMCIC k)) (progCode (CupodTrollBot k)) (progCode (CIMCIC k)) (actCode .D) ∧
        EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (CIMCIC k)) (progCode (CupodTrollBot k)) (actCode .C)) ∧
      (LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (CupodTrollBot k)) k) →
        EvalGraph 2 (progCode (CIMCIC k)) (progCode (CupodTrollBot k)) (progCode (CIMCIC k)) (actCode .C) ∧
        EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (CIMCIC k)) (progCode (CupodTrollBot k)) (actCode .C)) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiC]
  constructor
  · intro hn
    refine ⟨?_, floor_CIMCIC_vs_CupodTrollBot_right k⟩
    rw [progCode_CIMCIC_search] at hn ⊢
    exact search_else phiC hn (const_play 0 _ _ _)
  · intro hf
    refine ⟨?_, floor_CIMCIC_vs_CupodTrollBot_right k⟩
    rw [progCode_CIMCIC_search] at hf ⊢
    exact search_then phiC hf (const_play 0 _ _ _)

/-- **CIMCIC × DBot** (engine `(D, C)`, pad 4; the `cenU` cell). Hinge: CIMCIC's guard against DBot. -/
theorem dich_CIMCIC_vs_DBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode DBot) k) →
        EvalGraph 4 (progCode (CIMCIC k)) (progCode DBot) (progCode (CIMCIC k)) (actCode .D) ∧
        EvalGraph 4 (progCode DBot) (progCode (CIMCIC k)) (progCode DBot) (actCode .C)) ∧
      (LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode DBot) k) →
        EvalGraph 4 (progCode (CIMCIC k)) (progCode DBot) (progCode (CIMCIC k)) (actCode .C) ∧
        EvalGraph 4 (progCode DBot) (progCode (CIMCIC k)) (progCode DBot) (actCode .C)) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiC]
  constructor
  · intro hn
    refine ⟨?_, floor_CIMCIC_vs_DBot_right k⟩
    rw [progCode_CIMCIC_search] at hn ⊢
    exact EvalGraph.mono_le (by omega) (search_else phiC hn (const_play 0 _ _ _))
  · intro hf
    refine ⟨?_, floor_CIMCIC_vs_DBot_right k⟩
    rw [progCode_CIMCIC_search] at hf ⊢
    exact EvalGraph.mono_le (by omega) (search_then phiC hf (const_play 0 _ _ _))

/-- **CIMCIC × EBot** (engine `(D, C)`, pad 5; the `cenU` cell). Hinge: CIMCIC's guard against EBot. -/
theorem dich_CIMCIC_vs_EBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode EBot) k) →
        EvalGraph 5 (progCode (CIMCIC k)) (progCode EBot) (progCode (CIMCIC k)) (actCode .D) ∧
        EvalGraph 5 (progCode EBot) (progCode (CIMCIC k)) (progCode EBot) (actCode .C)) ∧
      (LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode EBot) k) →
        EvalGraph 5 (progCode (CIMCIC k)) (progCode EBot) (progCode (CIMCIC k)) (actCode .C) ∧
        EvalGraph 5 (progCode EBot) (progCode (CIMCIC k)) (progCode EBot) (actCode .C)) := by
  obtain ⟨k₀, hE⟩ := floor_CIMCIC_vs_EBot_right
  refine ⟨k₀, fun k hk ↦ ?_⟩
  simp only [hingeB phiC]
  constructor
  · intro hn
    refine ⟨?_, hE k hk⟩
    rw [progCode_CIMCIC_search] at hn ⊢
    exact EvalGraph.mono_le (by omega) (search_else phiC hn (const_play 0 _ _ _))
  · intro hf
    refine ⟨?_, hE k hk⟩
    rw [progCode_CIMCIC_search] at hf ⊢
    exact EvalGraph.mono_le (by omega) (search_then phiC hf (const_play 0 _ _ _))

/-- **Guardian × CIMCIC** (engine `(C, D)`, pad 2). Guardian's C is settled (its guard is FALSE,
`floor_GuardianBot_vs_CIMCIC_left`); hinge: CIMCIC's guard "I cooperate with Guardian ⇒ Guardian cooperates with
me" (TRUE, Guardian's else-play). -/
theorem dich_GuardianBot_vs_CIMCIC :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (GuardianBot k)) k) →
        EvalGraph 2 (progCode (GuardianBot k)) (progCode (CIMCIC k)) (progCode (GuardianBot k)) (actCode .C) ∧
        EvalGraph 2 (progCode (CIMCIC k)) (progCode (GuardianBot k)) (progCode (CIMCIC k)) (actCode .D)) ∧
      (LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (GuardianBot k)) k) →
        EvalGraph 2 (progCode (GuardianBot k)) (progCode (CIMCIC k)) (progCode (GuardianBot k)) (actCode .C) ∧
        EvalGraph 2 (progCode (CIMCIC k)) (progCode (GuardianBot k)) (progCode (CIMCIC k)) (actCode .C)) := by
  obtain ⟨k₀, hG⟩ := floor_GuardianBot_vs_CIMCIC_left
  refine ⟨k₀, fun k hk ↦ ?_⟩
  simp only [hingeB phiC]
  constructor
  · intro hn
    refine ⟨hG k hk, ?_⟩
    rw [progCode_CIMCIC_search] at hn ⊢
    exact search_else phiC hn (const_play 0 _ _ _)
  · intro hf
    refine ⟨hG k hk, ?_⟩
    rw [progCode_CIMCIC_search] at hf ⊢
    exact search_then phiC hf (const_play 0 _ _ _)

/-- **Guardian × Dupoc** (engine `(C, D)`, pad 2). Guardian's C is settled; hinge: Dupoc's guard "Guardian plays C
against me". -/
theorem dich_GuardianBot_vs_DupocBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (GuardianBot k)) k) →
        EvalGraph 2 (progCode (GuardianBot k)) (progCode (DupocBot k)) (progCode (GuardianBot k)) (actCode .C) ∧
        EvalGraph 2 (progCode (DupocBot k)) (progCode (GuardianBot k)) (progCode (DupocBot k)) (actCode .D)) ∧
      (LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (GuardianBot k)) k) →
        EvalGraph 2 (progCode (GuardianBot k)) (progCode (DupocBot k)) (progCode (GuardianBot k)) (actCode .C) ∧
        EvalGraph 2 (progCode (DupocBot k)) (progCode (GuardianBot k)) (progCode (DupocBot k)) (actCode .C)) := by
  obtain ⟨k₀, hG⟩ := floor_GuardianBot_vs_DupocBot_left
  refine ⟨k₀, fun k hk ↦ ?_⟩
  simp only [hingeB phiDu]
  constructor
  · intro hn
    refine ⟨hG k hk, ?_⟩
    rw [progCode_DupocBot_search] at hn ⊢
    exact search_else phiDu hn (const_play 0 _ _ _)
  · intro hf
    refine ⟨hG k hk, ?_⟩
    rw [progCode_DupocBot_search] at hf ⊢
    exact search_then phiDu hf (const_play 0 _ _ _)

/-- **Guardian × Just** (engine `(C, D)`, pad 2). Guardian's C is settled; hinge: Just's guard "Guardian plays C
against `.bot (DupocBot k)`". -/
theorem dich_GuardianBot_vs_JustBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode (GuardianBot k)) k) →
        EvalGraph 2 (progCode (GuardianBot k)) (progCode (JustBot k)) (progCode (GuardianBot k)) (actCode .C) ∧
        EvalGraph 2 (progCode (JustBot k)) (progCode (GuardianBot k)) (progCode (JustBot k)) (actCode .D)) ∧
      (LenBox TAct k (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode (GuardianBot k)) k) →
        EvalGraph 2 (progCode (GuardianBot k)) (progCode (JustBot k)) (progCode (GuardianBot k)) (actCode .C) ∧
        EvalGraph 2 (progCode (JustBot k)) (progCode (GuardianBot k)) (progCode (JustBot k)) (actCode .C)) := by
  obtain ⟨k₀, hG⟩ := floor_GuardianBot_vs_JustBot_left
  refine ⟨k₀, fun k hk ↦ ?_⟩
  simp only [hingeB (phiJ k)]
  constructor
  · intro hn
    refine ⟨hG k hk, ?_⟩
    rw [progCode_JustBot] at hn ⊢
    exact search_else_at (phiJ k) hn (const_play 0 _ _ _)
  · intro hf
    refine ⟨hG k hk, ?_⟩
    rw [progCode_JustBot] at hf ⊢
    exact search_then_at (phiJ k) hf (const_play 0 _ _ _)

/-- **Cupod × OBot** (engine `(C, D)`, pad 5). OBot's D is settled (`floor_CupodBot_vs_OBot_right`); hinge: Cupod's
guard "OBot plays D against me" (TRUE). Not found ⇒ Cupod's else-branch C, `(C, D)`; found ⇒ `(D, D)`. -/
theorem dich_CupodBot_vs_OBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode OBot) k) →
        EvalGraph 5 (progCode (CupodBot k)) (progCode OBot) (progCode (CupodBot k)) (actCode .C) ∧
        EvalGraph 5 (progCode OBot) (progCode (CupodBot k)) (progCode OBot) (actCode .D)) ∧
      (LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode OBot) k) →
        EvalGraph 5 (progCode (CupodBot k)) (progCode OBot) (progCode (CupodBot k)) (actCode .D) ∧
        EvalGraph 5 (progCode OBot) (progCode (CupodBot k)) (progCode OBot) (actCode .D)) := by
  obtain ⟨k₀, hO⟩ := floor_CupodBot_vs_OBot_right
  refine ⟨k₀, fun k hk ↦ ?_⟩
  simp only [hingeB phiCu]
  constructor
  · intro hn
    refine ⟨?_, hO k hk⟩
    rw [progCode_CupodBot] at hn ⊢
    exact EvalGraph.mono_le (by omega) (search_else phiCu hn (const_play 0 _ _ _))
  · intro hf
    refine ⟨?_, hO k hk⟩
    rw [progCode_CupodBot] at hf ⊢
    exact EvalGraph.mono_le (by omega) (search_then phiCu hf (const_play 0 _ _ _))

end single

/-! ### 3. The prudence cells: Prudent's outer guard as the hinge, its prudence guard recovered by soundness or
kept as a second hinge -/

section prudence

/-- **Prudent × Dupoc** (engine `outcome_PrudentBot_vs_DupocBot = (D, D)`, pad 3; the staggered companion is
`(C, C)`). Hinge: Prudent's OUTER guard "Dupoc plays C against me". Not found ⇒ Prudent D, Dupoc's guard false
⇒ `(D, D)`. Found ⇒ by soundness Dupoc cooperates, so Dupoc's guard was found, so by soundness Prudent cooperates,
so the prudence guard was found too (`found_of_search_play` twice): `(C, C)` — the mutual Löb world. -/
theorem dich_PrudentBot_vs_DupocBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (DupocBot k)) k) →
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (DupocBot k)) (progCode (PrudentBot k)) (actCode .D) ∧
        EvalGraph 3 (progCode (DupocBot k)) (progCode (PrudentBot k)) (progCode (DupocBot k)) (actCode .D)) ∧
      (LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (DupocBot k)) k) →
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (DupocBot k)) (progCode (PrudentBot k)) (actCode .C) ∧
        EvalGraph 3 (progCode (DupocBot k)) (progCode (PrudentBot k)) (progCode (DupocBot k)) (actCode .C)) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiPo]
  constructor
  · intro hn
    have hP : EvalGraph 2 (progCode (PrudentBot k)) (progCode (DupocBot k)) (progCode (PrudentBot k)) 1 := by
      rw [progCode_PrudentBot_search] at hn ⊢
      exact search_else phiPo hn (const_play 0 _ _ _)
    exact ⟨EvalGraph.mono_le (by omega) hP,
      EvalGraph.mono_le (by omega) (dupoc_D_of_probe k (properPlayer_PrudentBot k) hP)⟩
  · intro hf
    obtain ⟨N, hDC⟩ := play_of_found_opp_self (properPlayer_PrudentBot k) (properPlayer_DupocBot k) .C hf
    have hDf : LenBox TAct k (guardCode (templateCode phiDu) (progCode (DupocBot k)) (progCode (PrudentBot k))) := by
      rw [progCode_DupocBot_search] at hDC ⊢
      exact (found_of_search_play phiDu hDC (by decide)).1
    obtain ⟨N', hPC⟩ := play_of_found_opp_self (properPlayer_DupocBot k) (properPlayer_PrudentBot k) .C hDf
    have hPi : LenBox TAct k (guardCode (templateCode phiPi) (progCode (PrudentBot k)) (progCode (DupocBot k))) := by
      rw [progCode_PrudentBot_search] at hPC ⊢
      obtain ⟨_, N'', hin⟩ := found_of_search_play phiPo hPC (by decide)
      exact (found_of_search_play phiPi hin (by decide)).1
    have hP : EvalGraph 3 (progCode (PrudentBot k)) (progCode (DupocBot k)) (progCode (PrudentBot k)) 0 := by
      rw [progCode_PrudentBot_search] at hf hPi ⊢
      exact search_then phiPo hf (search_then phiPi hPi (const_play 0 _ _ _))
    have hD : EvalGraph 2 (progCode (DupocBot k)) (progCode (PrudentBot k)) (progCode (DupocBot k)) 0 := by
      rw [progCode_DupocBot_search] at hDf ⊢
      exact search_then phiDu hDf (const_play 0 _ _ _)
    exact ⟨hP, EvalGraph.mono_le (by omega) hD⟩

/-- **Prudent × Prudent** (engine `outcome_PrudentBot_vs_PrudentBot = (D, D)`, pad 3). Hinge: the outer guard
"Prudent plays C against me" in self-play (ONE sentence for both sides). Not found ⇒ `(D, D)`; found ⇒ by
soundness Prudent cooperates with itself, so its prudence guard was found: `(C, C)`. -/
theorem dich_PrudentBot_vs_PrudentBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (PrudentBot k)) (progCode (PrudentBot k)) (actCode .D) ∧
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (PrudentBot k)) (progCode (PrudentBot k)) (actCode .D)) ∧
      (LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (PrudentBot k)) (progCode (PrudentBot k)) (actCode .C) ∧
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (PrudentBot k)) (progCode (PrudentBot k)) (actCode .C)) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiPo]
  constructor
  · intro hn
    have hP : EvalGraph 3 (progCode (PrudentBot k)) (progCode (PrudentBot k)) (progCode (PrudentBot k)) 1 := by
      rw [progCode_PrudentBot_search] at hn ⊢
      exact search_else phiPo hn (const_play 1 _ _ _)
    exact ⟨hP, hP⟩
  · intro hf
    obtain ⟨N, hPC⟩ := play_of_found_opp_self (properPlayer_PrudentBot k) (properPlayer_PrudentBot k) .C hf
    have hPi : LenBox TAct k (guardCode (templateCode phiPi) (progCode (PrudentBot k)) (progCode (PrudentBot k))) := by
      rw [progCode_PrudentBot_search] at hPC ⊢
      obtain ⟨_, N'', hin⟩ := found_of_search_play phiPo hPC (by decide)
      exact (found_of_search_play phiPi hin (by decide)).1
    have hP : EvalGraph 3 (progCode (PrudentBot k)) (progCode (PrudentBot k)) (progCode (PrudentBot k)) 0 := by
      rw [progCode_PrudentBot_search] at hf hPi ⊢
      exact search_then phiPo hf (search_then phiPi hPi (const_play 0 _ _ _))
    exact ⟨hP, hP⟩

/-- Prudent's play from the verdicts on its two guards (fuel 3): C iff both are found. -/
theorem prudent_of_verdicts (k : ℕ) (x : ℕ) :
    (LenBox TAct k (guardCode (templateCode phiPo) (progCode (PrudentBot k)) x) →
      LenBox TAct k (guardCode (templateCode phiPi) (progCode (PrudentBot k)) x) →
      EvalGraph 3 (progCode (PrudentBot k)) x (progCode (PrudentBot k)) 0) ∧
    (¬ LenBox TAct k (guardCode (templateCode phiPo) (progCode (PrudentBot k)) x) →
      EvalGraph 3 (progCode (PrudentBot k)) x (progCode (PrudentBot k)) 1) ∧
    (¬ LenBox TAct k (guardCode (templateCode phiPi) (progCode (PrudentBot k)) x) →
      EvalGraph 3 (progCode (PrudentBot k)) x (progCode (PrudentBot k)) 1) := by
  rw [progCode_PrudentBot_search]
  refine ⟨fun ho hi ↦ search_then phiPo ho (search_then phiPi hi (const_play 0 _ _ _)),
    fun ho ↦ search_else phiPo ho (const_play 1 _ _ _),
    fun hi ↦ search_either phiPo (search_else phiPi hi (const_play 0 _ _ _)) (const_play 1 _ _ _)⟩

/-- **Just × Prudent** (engine `outcome_JustBot_vs_PrudentBot = (D, D)`, pad 3). Three hinges, NESTED: `J` = Just's
guard "Prudent plays C against `.bot (DupocBot k)`" (outer split), then Prudent's outer guard `A` "Just plays C
against me" and prudence guard `B` "Just plays D against `.bot DefectBot`" (TRUE, `floor_JustBot_vs_PrudentBot_true`;
the verdict pass's floor). `¬J ⇒ (D, D)` (Just defects, so `A` is false); `J ⇒` Just C, Prudent C iff `A ∧ B`. -/
theorem dich_JustBot_vs_PrudentBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (JustBot k)) (progCode (PrudentBot k)) (progCode (JustBot k)) (actCode .D) ∧
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (JustBot k)) (progCode (PrudentBot k)) (actCode .D)) ∧
      (LenBox TAct k (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (JustBot k)) (progCode (PrudentBot k)) (progCode (JustBot k)) (actCode .C) ∧
        ((¬ LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (JustBot k)) k) ∨
          ¬ LenBox TAct k (guardCodeB (templateCode phiPi) (progCode (PrudentBot k)) (progCode (JustBot k)) k)) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (JustBot k)) (progCode (PrudentBot k)) (actCode .D)) ∧
        (LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (JustBot k)) k) →
          LenBox TAct k (guardCodeB (templateCode phiPi) (progCode (PrudentBot k)) (progCode (JustBot k)) k) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (JustBot k)) (progCode (PrudentBot k)) (actCode .C))) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB (phiJ k), hingeB phiPo, hingeB phiPi]
  obtain ⟨hPC, hPo, hPi⟩ := prudent_of_verdicts k (progCode (JustBot k))
  constructor
  · intro hn
    have hJ : EvalGraph 2 (progCode (JustBot k)) (progCode (PrudentBot k)) (progCode (JustBot k)) 1 := by
      rw [progCode_JustBot] at hn ⊢
      exact search_else_at (phiJ k) hn (const_play 0 _ _ _)
    exact ⟨EvalGraph.mono_le (by omega) hJ,
      EvalGraph.mono_le (by omega) (prudent_D_of_probe k (properPlayer_JustBot k) hJ)⟩
  · intro hf
    refine ⟨?_, fun h ↦ h.elim hPo hPi, hPC⟩
    rw [progCode_JustBot] at hf ⊢
    exact EvalGraph.mono_le (by omega) (search_then_at (phiJ k) hf (const_play 0 _ _ _))

/-- **CIMCIC × Prudent** (engine `llm_outcome_CIMCIC_vs_PrudentBot = (D, D)`, pad 3). Hinges: Prudent's outer guard
`A` "CIMCIC plays C against me" (outer split) and its prudence guard `B` "CIMCIC plays D against `.bot DefectBot`"
(TRUE, the floor). `¬A ⇒ (D, D)` (Prudent defects, so CIMCIC's guard is self-refuting, never found); `A ⇒` CIMCIC
cooperates (soundness of `A`, pinned by determinism), Prudent C iff `B`. -/
theorem dich_CIMCIC_vs_PrudentBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (CIMCIC k)) k) →
        EvalGraph 3 (progCode (CIMCIC k)) (progCode (PrudentBot k)) (progCode (CIMCIC k)) (actCode .D) ∧
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (CIMCIC k)) (progCode (PrudentBot k)) (actCode .D)) ∧
      (LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (CIMCIC k)) k) →
        EvalGraph 3 (progCode (CIMCIC k)) (progCode (PrudentBot k)) (progCode (CIMCIC k)) (actCode .C) ∧
        (¬ LenBox TAct k (guardCodeB (templateCode phiPi) (progCode (PrudentBot k)) (progCode (CIMCIC k)) k) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (CIMCIC k)) (progCode (PrudentBot k)) (actCode .D)) ∧
        (LenBox TAct k (guardCodeB (templateCode phiPi) (progCode (PrudentBot k)) (progCode (CIMCIC k)) k) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (CIMCIC k)) (progCode (PrudentBot k)) (actCode .C))) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiPo, hingeB phiPi]
  obtain ⟨hPC, hPo, hPi⟩ := prudent_of_verdicts k (progCode (CIMCIC k))
  constructor
  · intro hn
    have hP := hPo hn
    have hC := cimcic_selfref_not_found k (properPlayer_PrudentBot k) hP
    refine ⟨?_, hP⟩
    rw [progCode_CIMCIC_search] at hC ⊢
    exact EvalGraph.mono_le (by omega) (search_else phiC hC (const_play 0 _ _ _))
  · intro hf
    obtain ⟨N, hCC⟩ := play_of_found_opp_self (properPlayer_PrudentBot k) (properPlayer_CIMCIC k) .C hf
    refine ⟨?_, hPi, hPC hf⟩
    rw [progCode_CIMCIC_search] at hCC ⊢
    exact EvalGraph.mono_le (by omega)
      (search_then phiC (found_of_search_play phiC hCC (by decide)).1 (const_play 0 _ _ _))

/-- **Guardian × Prudent** (engine `llm_outcome_GuardianBot_vs_PrudentBot = (C, D)`, pad 3). Three hinges, NESTED:
`G` = Guardian's guard "Prudent plays D against `.bot CooperateBot`" (TRUE, `floor_GuardianBot_vs_PrudentBot_true`;
outer split), then Prudent's outer guard `A` "Guardian plays C against me" and prudence guard `B` "Guardian plays D
against `.bot DefectBot`" (rated (P) by the verdict pass). `G ⇒ (D, D)` (Guardian defects, so `A` is false);
`¬G ⇒` Guardian C, Prudent C iff `A ∧ B`. -/
theorem dich_GuardianBot_vs_PrudentBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenBox TAct k (guardCodeB (templateCode phiG) (progCode (GuardianBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (GuardianBot k)) (progCode (PrudentBot k)) (progCode (GuardianBot k)) (actCode .D) ∧
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (GuardianBot k)) (progCode (PrudentBot k)) (actCode .D)) ∧
      (¬ LenBox TAct k (guardCodeB (templateCode phiG) (progCode (GuardianBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (GuardianBot k)) (progCode (PrudentBot k)) (progCode (GuardianBot k)) (actCode .C) ∧
        ((¬ LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (GuardianBot k)) k) ∨
          ¬ LenBox TAct k (guardCodeB (templateCode phiPi) (progCode (PrudentBot k)) (progCode (GuardianBot k)) k)) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (GuardianBot k)) (progCode (PrudentBot k)) (actCode .D)) ∧
        (LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (GuardianBot k)) k) →
          LenBox TAct k (guardCodeB (templateCode phiPi) (progCode (PrudentBot k)) (progCode (GuardianBot k)) k) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (GuardianBot k)) (progCode (PrudentBot k)) (actCode .C))) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiG, hingeB phiPo, hingeB phiPi]
  obtain ⟨hPC, hPo, hPi⟩ := prudent_of_verdicts k (progCode (GuardianBot k))
  constructor
  · intro hG
    have hGD := guardian_D_of_found k hG
    exact ⟨EvalGraph.mono_le (by omega) hGD,
      EvalGraph.mono_le (by omega) (prudent_D_of_probe k (properPlayer_GuardianBot k) hGD)⟩
  · intro hn
    refine ⟨?_, fun h ↦ h.elim hPo hPi, hPC⟩
    rw [progCode_GuardianBot] at hn ⊢
    exact EvalGraph.mono_le (by omega) (search_else phiG hn (const_play 0 _ _ _))

/-- `TAct ⊢` "EBot defects against `.bot DefectBot`" (a closed search-free atom, both readings). -/
theorem tact_EBot_D_vs_botDB : TAct ⊢ sentenceAt EBot (.bot DefectBot) (.plays EBot (.bot DefectBot) .D) :=
  tact_proves_plays_closed sfp_EBot sfp_botDB .D (N := 6)
    (by rw [progCode_botDB]
        exact ebot_D_of_probes_D (bot_const_play 0 _ _ 1) (bot_const_play 0 _ _ 1) (bot_const_play 0 _ _ 1))
    (N' := 6)
    (evalGraph_transpose_of_eval (by decide) (sfp_transpose sfp_EBot (by decide) (by decide))
      (sfp_transpose sfp_botDB (by decide) (by decide)))

/-- **Prudent's prudence guard against a CLOSED opponent `X` is found for all large `k`** as soon as `TAct` proves
the closed atom "`X` defects against `.bot DefectBot`" (the guard names no `.self`; `guardian_found`'s twin). -/
theorem prudence_found_closed {X : PD.Prog} (hX : ProperPlayer X)
    (hT : TAct ⊢ sentenceAt X (.bot DefectBot) (.plays X (.bot DefectBot) .D)) :
    ∃ L : ℕ, ∀ k : ℕ, L ≤ k → LenBox TAct k (guardCode (templateCode phiPi) (progCode (PrudentBot k)) (progCode X)) := by
  obtain ⟨N, hN⟩ := lenBoxNat_of_provable hT
  refine ⟨N, fun k hk ↦ ?_⟩
  have e : phiPi.subst (PrudentBot k) X = .plays X (.bot DefectBot) .D := by
    simp [phiPi, PD.Formula.subst, PD.Prog.subst]
  rw [← quote_sentenceAt (PrudentBot k) X phiPi rfl, ← sentenceAt_subst X (.bot DefectBot) (properPlayer_PrudentBot k) hX phiPi rfl,
    e, lenBox_nat]
  exact lenBoxNat_codeBound_mono hk hN

/-- Prudent's prudence guard against EBot is FOUND for all large `k`. -/
theorem prudence_found_vs_EBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenBox TAct k (guardCode (templateCode phiPi) (progCode (PrudentBot k)) (progCode EBot)) := by
  obtain ⟨L, hL⟩ := prudence_found_closed sfp_EBot.1 tact_EBot_D_vs_botDB
  exact ⟨L, fun k hk ↦ hL k (Nat.le_of_lt hk)⟩

/-- **Prudent × EBot** (engine `outcome_PrudentBot_vs_EBot = (D, C)`, pad 7; the LOEB-FP cell). Hinge: Prudent's
outer guard "EBot plays C against me" (TRUE through EBot's first rung, Prudent's else-play against
`.bot DefectBot`); the prudence guard is FOUND (`prudence_found_vs_EBot`). Not found ⇒ Prudent D (EBot's C in that
world is Prudent's Löb cooperation with `.bot MirrorBot`, not built, so only Prudent's side is stated); found ⇒
`(C, C)` — EBot's C by soundness, pinned at the pad by totality + determinism. -/
theorem dich_PrudentBot_vs_EBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode EBot) k) →
        EvalGraph 7 (progCode (PrudentBot k)) (progCode EBot) (progCode (PrudentBot k)) (actCode .D)) ∧
      (LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode EBot) k) →
        EvalGraph 7 (progCode (PrudentBot k)) (progCode EBot) (progCode (PrudentBot k)) (actCode .C) ∧
        EvalGraph 7 (progCode EBot) (progCode (PrudentBot k)) (progCode EBot) (actCode .C)) := by
  obtain ⟨k₀, hB⟩ := prudence_found_vs_EBot
  refine ⟨k₀, fun k hk ↦ ?_⟩
  simp only [hingeB phiPo]
  obtain ⟨hPC, hPo, _⟩ := prudent_of_verdicts k (progCode EBot)
  constructor
  · intro hn
    exact EvalGraph.mono_le (by omega) (hPo hn)
  · intro hf
    refine ⟨EvalGraph.mono_le (by omega) (hPC hf (hB k hk)), ?_⟩
    obtain ⟨N, hEC⟩ := play_of_found_opp_self (properPlayer_PrudentBot k) sfp_EBot.1 .C hf
    obtain ⟨r, hr⟩ := prudent_total k (pBot Mirror)
    obtain ⟨r', hE⟩ := ebot_total (EvalGraph.mono_le (by omega) (snd_PrudentBot_vs_botDB k)) (snd_PrudentBot_vs_botCB k) hr
    have := EvalGraph.unique' hE hEC
    subst this
    exact hE

end prudence

/-! ### 4. The bistable-modulo-reflection cells: two searchers, each guard true only through the other's else-play -/

section bistable

/-- **Wary × Dupoc** (engine `llm_outcome_WaryBot_vs_DupocBot = (C, D)`, pad 2). Two hinges, NESTED: `W` = Wary's
`.neg` guard "¬(Dupoc plays C against me)" (outer split), `A` = Dupoc's guard "Wary plays C against me". `W ⇒ (D, D)`
(Wary defects, so `A` is false by soundness); `¬W ⇒` Wary C, then `¬A ⇒ Dupoc D` (the engine's world) and
`A ⇒ Dupoc C`. The three consistent scenarios of the verdict pass: `(D, D)`, `(C, D)`, `(C, C)`. -/
theorem dich_WaryBot_vs_DupocBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenBox TAct k (guardCodeB (templateCode phiW) (progCode (WaryBot k)) (progCode (DupocBot k)) k) →
        EvalGraph 2 (progCode (WaryBot k)) (progCode (DupocBot k)) (progCode (WaryBot k)) (actCode .D) ∧
        EvalGraph 2 (progCode (DupocBot k)) (progCode (WaryBot k)) (progCode (DupocBot k)) (actCode .D)) ∧
      (¬ LenBox TAct k (guardCodeB (templateCode phiW) (progCode (WaryBot k)) (progCode (DupocBot k)) k) →
        EvalGraph 2 (progCode (WaryBot k)) (progCode (DupocBot k)) (progCode (WaryBot k)) (actCode .C) ∧
        (¬ LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (WaryBot k)) k) →
          EvalGraph 2 (progCode (DupocBot k)) (progCode (WaryBot k)) (progCode (DupocBot k)) (actCode .D)) ∧
        (LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (WaryBot k)) k) →
          EvalGraph 2 (progCode (DupocBot k)) (progCode (WaryBot k)) (progCode (DupocBot k)) (actCode .C))) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiW, hingeB phiDu]
  constructor
  · intro hW
    have hWD : EvalGraph 2 (progCode (WaryBot k)) (progCode (DupocBot k)) (progCode (WaryBot k)) 1 := by
      rw [progCode_WaryBot] at hW ⊢
      exact search_then phiW hW (const_play 0 _ _ _)
    exact ⟨hWD, dupoc_D_of_probe k (properPlayer_WaryBot k) hWD⟩
  · intro hn
    refine ⟨?_, fun hA ↦ ?_, fun hA ↦ ?_⟩
    · rw [progCode_WaryBot] at hn ⊢
      exact search_else phiW hn (const_play 0 _ _ _)
    · rw [progCode_DupocBot_search] at hA ⊢
      exact search_else phiDu hA (const_play 0 _ _ _)
    · rw [progCode_DupocBot_search] at hA ⊢
      exact search_then phiDu hA (const_play 0 _ _ _)

/-- **Wary × Just** (engine `llm_outcome_WaryBot_vs_JustBot = (C, D)`, pad 2). Two hinges, NESTED: `J` = Just's
guard "Wary plays C against `.bot (DupocBot k)`" (outer split), `W` = Wary's `.neg` guard "¬(Just plays C against
me)". `J ⇒ (C, C)` (Just cooperates, so `W` is false by soundness); `¬J ⇒` Just D, then `W ⇒ Wary D` and `¬W ⇒ Wary C`
(the engine's world). -/
theorem dich_WaryBot_vs_JustBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenBox TAct k (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode (WaryBot k)) k) →
        EvalGraph 2 (progCode (WaryBot k)) (progCode (JustBot k)) (progCode (WaryBot k)) (actCode .C) ∧
        EvalGraph 2 (progCode (JustBot k)) (progCode (WaryBot k)) (progCode (JustBot k)) (actCode .C)) ∧
      (¬ LenBox TAct k (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode (WaryBot k)) k) →
        EvalGraph 2 (progCode (JustBot k)) (progCode (WaryBot k)) (progCode (JustBot k)) (actCode .D) ∧
        (LenBox TAct k (guardCodeB (templateCode phiW) (progCode (WaryBot k)) (progCode (JustBot k)) k) →
          EvalGraph 2 (progCode (WaryBot k)) (progCode (JustBot k)) (progCode (WaryBot k)) (actCode .D)) ∧
        (¬ LenBox TAct k (guardCodeB (templateCode phiW) (progCode (WaryBot k)) (progCode (JustBot k)) k) →
          EvalGraph 2 (progCode (WaryBot k)) (progCode (JustBot k)) (progCode (WaryBot k)) (actCode .C))) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB (phiJ k), hingeB phiW]
  constructor
  · intro hJ
    have hJC : EvalGraph 2 (progCode (JustBot k)) (progCode (WaryBot k)) (progCode (JustBot k)) 0 := by
      rw [progCode_JustBot] at hJ ⊢
      exact search_then_at (phiJ k) hJ (const_play 0 _ _ _)
    exact ⟨wary_C_of_probe k (properPlayer_JustBot k) hJC, hJC⟩
  · intro hn
    refine ⟨?_, fun hW ↦ ?_, fun hW ↦ ?_⟩
    · rw [progCode_JustBot] at hn ⊢
      exact search_else_at (phiJ k) hn (const_play 0 _ _ _)
    · rw [progCode_WaryBot] at hW ⊢
      exact search_then phiW hW (const_play 0 _ _ _)
    · rw [progCode_WaryBot] at hW ⊢
      exact search_else phiW hW (const_play 0 _ _ _)

/-- **Wary × Prudent** (engine `llm_outcome_WaryBot_vs_PrudentBot = (C, D)`, pad 3). Three hinges, NESTED: Prudent's
outer guard `A` "Wary plays C against me" and prudence guard `B` "Wary plays D against `.bot DefectBot`" (rated (P))
decide Prudent (outer split on `A ∧ B`); `W` = Wary's `.neg` guard "¬(Prudent plays C against me)". `A ∧ B ⇒ (C, C)`
(Prudent cooperates, so `W` is false); otherwise Prudent D, then `W ⇒ Wary D` and `¬W ⇒ Wary C` (the engine's
world). -/
theorem dich_WaryBot_vs_PrudentBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (WaryBot k)) k) →
        LenBox TAct k (guardCodeB (templateCode phiPi) (progCode (PrudentBot k)) (progCode (WaryBot k)) k) →
        EvalGraph 3 (progCode (WaryBot k)) (progCode (PrudentBot k)) (progCode (WaryBot k)) (actCode .C) ∧
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (WaryBot k)) (progCode (PrudentBot k)) (actCode .C)) ∧
      ((¬ LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (WaryBot k)) k) ∨
        ¬ LenBox TAct k (guardCodeB (templateCode phiPi) (progCode (PrudentBot k)) (progCode (WaryBot k)) k)) →
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (WaryBot k)) (progCode (PrudentBot k)) (actCode .D) ∧
        (LenBox TAct k (guardCodeB (templateCode phiW) (progCode (WaryBot k)) (progCode (PrudentBot k)) k) →
          EvalGraph 3 (progCode (WaryBot k)) (progCode (PrudentBot k)) (progCode (WaryBot k)) (actCode .D)) ∧
        (¬ LenBox TAct k (guardCodeB (templateCode phiW) (progCode (WaryBot k)) (progCode (PrudentBot k)) k) →
          EvalGraph 3 (progCode (WaryBot k)) (progCode (PrudentBot k)) (progCode (WaryBot k)) (actCode .C))) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiPo, hingeB phiPi, hingeB phiW]
  obtain ⟨hPC, hPo, hPi⟩ := prudent_of_verdicts k (progCode (WaryBot k))
  constructor
  · intro hA hB
    have hP := hPC hA hB
    exact ⟨EvalGraph.mono_le (by omega) (wary_C_of_probe k (properPlayer_PrudentBot k) hP), hP⟩
  · intro h
    refine ⟨h.elim hPo hPi, fun hW ↦ ?_, fun hW ↦ ?_⟩
    · rw [progCode_WaryBot] at hW ⊢
      exact EvalGraph.mono_le (by omega) (search_then phiW hW (const_play 0 _ _ _))
    · rw [progCode_WaryBot] at hW ⊢
      exact EvalGraph.mono_le (by omega) (search_else phiW hW (const_play 0 _ _ _))

/-- The Cupod × Prudent core (both orders share it). Three hinges, NESTED: `Cu` = Cupod's guard "Prudent plays D
against me" (outer split); Prudent's outer guard `A` "Cupod plays C against me" and prudence guard `B` "Cupod plays D
against `.bot DefectBot`" (rated (P)). `Cu ⇒ (D, D)` (Cupod defects, so `A` is false); `¬Cu ⇒` Cupod C, Prudent C iff
`A ∧ B` — the engine's `(C, D)` is `¬Cu` with `A ∧ B` failing. -/
theorem dich_CupodBot_vs_PrudentBot_core (k : ℕ) :
    (LenBox TAct k (guardCode (templateCode phiCu) (progCode (CupodBot k)) (progCode (PrudentBot k))) →
      EvalGraph 3 (progCode (CupodBot k)) (progCode (PrudentBot k)) (progCode (CupodBot k)) (actCode .D) ∧
      EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodBot k)) (progCode (PrudentBot k)) (actCode .D)) ∧
    (¬ LenBox TAct k (guardCode (templateCode phiCu) (progCode (CupodBot k)) (progCode (PrudentBot k))) →
      EvalGraph 3 (progCode (CupodBot k)) (progCode (PrudentBot k)) (progCode (CupodBot k)) (actCode .C) ∧
      ((¬ LenBox TAct k (guardCode (templateCode phiPo) (progCode (PrudentBot k)) (progCode (CupodBot k))) ∨
        ¬ LenBox TAct k (guardCode (templateCode phiPi) (progCode (PrudentBot k)) (progCode (CupodBot k)))) →
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodBot k)) (progCode (PrudentBot k)) (actCode .D)) ∧
      (LenBox TAct k (guardCode (templateCode phiPo) (progCode (PrudentBot k)) (progCode (CupodBot k))) →
        LenBox TAct k (guardCode (templateCode phiPi) (progCode (PrudentBot k)) (progCode (CupodBot k))) →
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodBot k)) (progCode (PrudentBot k)) (actCode .C))) := by
  obtain ⟨hPC, hPo, hPi⟩ := prudent_of_verdicts k (progCode (CupodBot k))
  constructor
  · intro hCu
    have hCD : EvalGraph 2 (progCode (CupodBot k)) (progCode (PrudentBot k)) (progCode (CupodBot k)) 1 := by
      rw [progCode_CupodBot] at hCu ⊢
      exact search_then phiCu hCu (const_play 0 _ _ _)
    exact ⟨EvalGraph.mono_le (by omega) hCD,
      EvalGraph.mono_le (by omega) (prudent_D_of_probe k (properPlayer_CupodBot k) hCD)⟩
  · intro hn
    refine ⟨?_, fun h ↦ h.elim hPo hPi, hPC⟩
    rw [progCode_CupodBot] at hn ⊢
    exact EvalGraph.mono_le (by omega) (search_else phiCu hn (const_play 0 _ _ _))

/-- **Cupod × Prudent** (engine `outcome_CupodBot_vs_PrudentBot = (C, D)`, pad 3): `dich_CupodBot_vs_PrudentBot_core`
with the hinges written as the evaluator consults them. -/
theorem dich_CupodBot_vs_PrudentBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (CupodBot k)) (progCode (PrudentBot k)) (progCode (CupodBot k)) (actCode .D) ∧
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodBot k)) (progCode (PrudentBot k)) (actCode .D)) ∧
      (¬ LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (CupodBot k)) (progCode (PrudentBot k)) (progCode (CupodBot k)) (actCode .C) ∧
        ((¬ LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (CupodBot k)) k) ∨
          ¬ LenBox TAct k (guardCodeB (templateCode phiPi) (progCode (PrudentBot k)) (progCode (CupodBot k)) k)) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodBot k)) (progCode (PrudentBot k)) (actCode .D)) ∧
        (LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (CupodBot k)) k) →
          LenBox TAct k (guardCodeB (templateCode phiPi) (progCode (PrudentBot k)) (progCode (CupodBot k)) k) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodBot k)) (progCode (PrudentBot k)) (actCode .C))) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiCu, hingeB phiPo, hingeB phiPi]
  exact dich_CupodBot_vs_PrudentBot_core k

/-- **Prudent × Cupod** (engine `outcome_PrudentBot_vs_CupodBot = (D, C)`, pad 3): the same pair, Prudent's side
first. -/
theorem dich_PrudentBot_vs_CupodBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodBot k)) (progCode (PrudentBot k)) (actCode .D) ∧
        EvalGraph 3 (progCode (CupodBot k)) (progCode (PrudentBot k)) (progCode (CupodBot k)) (actCode .D)) ∧
      (¬ LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (CupodBot k)) (progCode (PrudentBot k)) (progCode (CupodBot k)) (actCode .C) ∧
        ((¬ LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (CupodBot k)) k) ∨
          ¬ LenBox TAct k (guardCodeB (templateCode phiPi) (progCode (PrudentBot k)) (progCode (CupodBot k)) k)) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodBot k)) (progCode (PrudentBot k)) (actCode .D)) ∧
        (LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (CupodBot k)) k) →
          LenBox TAct k (guardCodeB (templateCode phiPi) (progCode (PrudentBot k)) (progCode (CupodBot k)) k) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodBot k)) (progCode (PrudentBot k)) (actCode .C))) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiCu, hingeB phiPo, hingeB phiPi]
  obtain ⟨h1, h2⟩ := dich_CupodBot_vs_PrudentBot_core k
  exact ⟨fun hCu ↦ ⟨(h1 hCu).2, (h1 hCu).1⟩, h2⟩

/-- **Just × Cupod** (engine `outcome_JustBot_vs_CupodBot = (D, C)`, pad 2). Two hinges, NESTED: `J` = Just's guard
"Cupod plays C against `.bot (DupocBot k)`" (outer split), `Cu` = Cupod's guard "Just plays D against me". `J ⇒ (C, C)`
(Just cooperates, so `Cu` is false); `¬J ⇒` Just D, then `Cu ⇒ Cupod D` and `¬Cu ⇒ Cupod C` (the engine's world). -/
theorem dich_JustBot_vs_CupodBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenBox TAct k (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode (CupodBot k)) k) →
        EvalGraph 2 (progCode (JustBot k)) (progCode (CupodBot k)) (progCode (JustBot k)) (actCode .C) ∧
        EvalGraph 2 (progCode (CupodBot k)) (progCode (JustBot k)) (progCode (CupodBot k)) (actCode .C)) ∧
      (¬ LenBox TAct k (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode (CupodBot k)) k) →
        EvalGraph 2 (progCode (JustBot k)) (progCode (CupodBot k)) (progCode (JustBot k)) (actCode .D) ∧
        (LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (JustBot k)) k) →
          EvalGraph 2 (progCode (CupodBot k)) (progCode (JustBot k)) (progCode (CupodBot k)) (actCode .D)) ∧
        (¬ LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (JustBot k)) k) →
          EvalGraph 2 (progCode (CupodBot k)) (progCode (JustBot k)) (progCode (CupodBot k)) (actCode .C))) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB (phiJ k), hingeB phiCu]
  constructor
  · intro hJ
    have hJC : EvalGraph 2 (progCode (JustBot k)) (progCode (CupodBot k)) (progCode (JustBot k)) 0 := by
      rw [progCode_JustBot] at hJ ⊢
      exact search_then_at (phiJ k) hJ (const_play 0 _ _ _)
    exact ⟨hJC, cupod_C_of_probe k (properPlayer_JustBot k) hJC⟩
  · intro hn
    refine ⟨?_, fun hCu ↦ ?_, fun hCu ↦ ?_⟩
    · rw [progCode_JustBot] at hn ⊢
      exact search_else_at (phiJ k) hn (const_play 0 _ _ _)
    · rw [progCode_CupodBot] at hCu ⊢
      exact search_then phiCu hCu (const_play 0 _ _ _)
    · rw [progCode_CupodBot] at hCu ⊢
      exact search_else phiCu hCu (const_play 0 _ _ _)

/-- **CIMCIC × Cupod** (engine `outcome_CIMCIC_vs_CupodBot = (D, C)`, pad 2). Two hinges, NESTED: `G` = CIMCIC's guard
"I cooperate with Cupod ⇒ Cupod cooperates with me" (outer split), `Cu` = Cupod's guard "CIMCIC plays D against me".
`G ⇒ (C, C)` (CIMCIC cooperates, so `Cu` is false); `¬G ⇒` CIMCIC D, then `Cu ⇒ Cupod D` and `¬Cu ⇒ Cupod C` (the
engine's world). -/
theorem dich_CIMCIC_vs_CupodBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (CupodBot k)) k) →
        EvalGraph 2 (progCode (CIMCIC k)) (progCode (CupodBot k)) (progCode (CIMCIC k)) (actCode .C) ∧
        EvalGraph 2 (progCode (CupodBot k)) (progCode (CIMCIC k)) (progCode (CupodBot k)) (actCode .C)) ∧
      (¬ LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (CupodBot k)) k) →
        EvalGraph 2 (progCode (CIMCIC k)) (progCode (CupodBot k)) (progCode (CIMCIC k)) (actCode .D) ∧
        (LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (CIMCIC k)) k) →
          EvalGraph 2 (progCode (CupodBot k)) (progCode (CIMCIC k)) (progCode (CupodBot k)) (actCode .D)) ∧
        (¬ LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (CIMCIC k)) k) →
          EvalGraph 2 (progCode (CupodBot k)) (progCode (CIMCIC k)) (progCode (CupodBot k)) (actCode .C))) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiC, hingeB phiCu]
  constructor
  · intro hG
    have hCC : EvalGraph 2 (progCode (CIMCIC k)) (progCode (CupodBot k)) (progCode (CIMCIC k)) 0 := by
      rw [progCode_CIMCIC_search] at hG ⊢
      exact search_then phiC hG (const_play 0 _ _ _)
    exact ⟨hCC, cupod_C_of_probe k (properPlayer_CIMCIC k) hCC⟩
  · intro hn
    refine ⟨?_, fun hCu ↦ ?_, fun hCu ↦ ?_⟩
    · rw [progCode_CIMCIC_search] at hn ⊢
      exact search_else phiC hn (const_play 0 _ _ _)
    · rw [progCode_CupodBot] at hCu ⊢
      exact search_then phiCu hCu (const_play 0 _ _ _)
    · rw [progCode_CupodBot] at hCu ⊢
      exact search_else phiCu hCu (const_play 0 _ _ _)

end bistable

/-! ### 5. The reduction theorem: the hinge of Dupoc × DBot is at least as hard as bounded consistency

The hinge `A_k` = `□_k` "DBot plays C against `DupocBot k`". DBot's C is the else-branch of its probe: DBot plays C
iff its opponent does NOT cooperate with `.bot DefectBot`, and Dupoc does not cooperate with `.bot DefectBot` iff its
guard `σ_k` = "`.bot DefectBot` plays C against `DupocBot k`" (FALSE in ℕ) is NOT provable within `k`. So, in every
model of `TAct` and in both standard readings, "DBot plays C against `DupocBot k`" ENTAILS "`σ_k` is not provable
within `k`" — in the standard reading for `σ_k`, in the swapped reading for its τ-twin. Completeness turns this
into a uniform `TAct`-theorem `∀ k, r(k) → (¬□_k σ_k ∨ ¬□_k τσ_k)`, whose instance at `binNumeral k` cut against `A_k`
yields the conclusion within `k + C₀ + C₁·size k`. The τ-symmetrized disjunction is what `TAct` proves: it cannot
tell its two readings apart, and internal τ-invariance of `□_k` is not available; at ℕ the two disjuncts are
equivalent (`lenBoxNat_swap_iff`), so the sentence is TRUE at `k` iff `¬□_k σ_k` (`negTwin_true_iff`).
The CONVERSE takes the conjunction: from "neither `σ_k` nor `τσ_k` is provable within `k`", Dupoc's else-branch and
DBot's probe give `r(k)` in both readings — the evaluator's determinism inside `TAct`. -/

section reduction

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! #### 5.1 DBot in every model, its probe step and its inverse -/

/-- DBot's code in every model: `ite (sim opp (bot DefectBot)) C (const D) (const C)`. -/
noncomputable def DBotV : V := pIte (pSim pOpp (pBot (pConst 1))) 0 (pConst 1) (pConst 0)

/-- The transposed DBot: `ite (sim opp (bot CooperateBot)) D (const C) (const D)`. -/
noncomputable def DBotTV : V := pIte (pSim pOpp (pBot (pConst 0))) 1 (pConst 0) (pConst 1)

lemma progCode_DBot_eq : progCode DBot = pIte (pSim pOpp (pBot (pConst 1))) 0 (pConst 1) (pConst 0) := by
  simp [DBot, DefectBot, actCode]

lemma cast_DBot : ((progCode DBot : ℕ) : V) = DBotV := by
  rw [progCode_DBot_eq, cast_pIte, cast_pSim, cast_pOpp, cast_pBot, cast_pConst, cast_pConst]
  simp [DBotV]

theorem transposeCode_DBotV : transposeCode (DBotV : V) = DBotTV := by
  unfold DBotV DBotTV transposeCode
  simp [revalueAction]

/-- DBot cooperates with `x` when `x` defects against `.bot DefectBot`, in every model (fuel `+2`). -/
theorem dbot_C_of_probe_D_V {x n : V} (h : EvalGraph n x (pBot (pConst 1)) x 1) :
    EvalGraph (n + 1 + 1) DBotV x DBotV 0 := by
  unfold DBotV
  rw [EvalGraph.ite_iff]
  refine ⟨1, ?_, Or.inr ⟨_root_.one_ne_zero, EvalGraph.const_iff.mpr rfl⟩⟩
  rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
  exact h

/-- The transposed DBot defects against `x` when `x` cooperates with `.bot CooperateBot`, in every model. -/
theorem dbotT_D_of_probe_C_V {x n : V} (h : EvalGraph n x (pBot (pConst 0)) x 0) :
    EvalGraph (n + 1 + 1) DBotTV x DBotTV 1 := by
  unfold DBotTV
  rw [EvalGraph.ite_iff]
  refine ⟨0, ?_, Or.inr ⟨_root_.zero_ne_one, EvalGraph.const_iff.mpr rfl⟩⟩
  rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
  exact h

/-- **The inverse**: DBot's cooperation with `x` means `x` did NOT cooperate with `.bot DefectBot` (in every
model, by the evaluator's determinism on the constant branches). -/
theorem probe_of_dbot_C_V {x n : V} (h : EvalGraph n DBotV x DBotV 0) :
    ∃ m r : V, EvalGraph m x (pBot (pConst 1)) x r ∧ r ≠ 0 := by
  obtain ⟨n', rfl, _⟩ := EvalGraph.case_iff.mp h
  unfold DBotV at h
  obtain ⟨r, hb, hpq⟩ := EvalGraph.ite_iff.mp h
  obtain ⟨n'', rfl, _⟩ := EvalGraph.case_iff.mp hb
  rw [EvalGraph.sim_iff, substCode_opp, substCode_bot] at hb
  refine ⟨n'', r, hb, ?_⟩
  rcases hpq with ⟨_, hc⟩ | ⟨hr, _⟩
  · exact absurd (EvalGraph.const_iff.mp hc) _root_.zero_ne_one
  · exact hr

/-- The transposed inverse: the transposed DBot's defection means `x` did NOT defect against `.bot CooperateBot`. -/
theorem probe_of_dbotT_D_V {x n : V} (h : EvalGraph n DBotTV x DBotTV 1) :
    ∃ m r : V, EvalGraph m x (pBot (pConst 0)) x r ∧ r ≠ 1 := by
  obtain ⟨n', rfl, _⟩ := EvalGraph.case_iff.mp h
  unfold DBotTV at h
  obtain ⟨r, hb, hpq⟩ := EvalGraph.ite_iff.mp h
  obtain ⟨n'', rfl, _⟩ := EvalGraph.case_iff.mp hb
  rw [EvalGraph.sim_iff, substCode_opp, substCode_bot] at hb
  refine ⟨n'', r, hb, ?_⟩
  rcases hpq with ⟨_, hc⟩ | ⟨hr, _⟩
  · exact absurd (EvalGraph.const_iff.mp hc) _root_.one_ne_zero
  · exact hr

/-! #### 5.2 The generic searcher's else-clause and its inverse, in every model -/

/-- A play of the generic searcher that differs from its then-constant means its guard was NOT found. -/
theorem not_found_of_SV_play {g : Semisentence LAct 6} {a : ℕ} {x y r n : V}
    (h : EvalGraph n (SV g a x) y (SV g a x) r) (hr : r ≠ (a : V)) :
    ¬ LenBox TAct x (guardCode (⌜g⌝ : V) (SV g a x) y) := by
  obtain ⟨n', rfl, _⟩ := EvalGraph.case_iff.mp h
  change EvalGraph (n' + 1) (SV g a x) y (pSearch x (⌜g⌝ : V) (pConst (a : V)) (pConst ((1 - a : ℕ) : V))) r at h
  rcases (EvalGraph.search_iff₆ (isSemiformula_quote₆ g)).mp h with ⟨_, hp⟩ | ⟨hn, _⟩
  · obtain ⟨m, rfl, _⟩ := EvalGraph.case_iff.mp hp
    exact absurd (EvalGraph.const_iff.mp hp) hr
  · exact hn

/-- Dupoc's else-clause in every model: guard not found ⇒ D (fuel 2). -/
theorem dupoc_else_V (x y : V) (h : ¬ LenBox TAct x (guardCode (⌜gDu⌝ : V) (SV gDu 0 x) y)) :
    EvalGraph 2 (SV gDu 0 x) y (SV gDu 0 x) 1 := by
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (SV gDu 0 x) y (pSearch x (⌜gDu⌝ : V) (pConst ((0 : ℕ) : V)) (pConst ((1 - 0 : ℕ) : V))) 1
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ gDu)]
  right
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) (SV gDu 0 x) y (pConst ((1 - 0 : ℕ) : V)) 1 := EvalGraph.const_iff.mpr (by simp)
  rwa [zero_add] at e

/-- Cupod's else-clause in every model: guard not found ⇒ C (fuel 2). -/
theorem cupod_else_V (x y : V) (h : ¬ LenBox TAct x (guardCode (⌜gCu⌝ : V) (SV gCu 1 x) y)) :
    EvalGraph 2 (SV gCu 1 x) y (SV gCu 1 x) 0 := by
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (SV gCu 1 x) y (pSearch x (⌜gCu⌝ : V) (pConst ((1 : ℕ) : V)) (pConst ((1 - 1 : ℕ) : V))) 0
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ gCu)]
  right
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) (SV gCu 1 x) y (pConst ((1 - 1 : ℕ) : V)) 0 := EvalGraph.const_iff.mpr (by simp)
  rwa [zero_add] at e

/-! #### 5.3 The formulas: the hinge `r`, the false guard `σ`, the budget box `boxK` -/

/-- Dupoc's guard against `.bot DefectBot` as a fixed formula: "`.bot DefectBot` plays C against `DupocBot k`"
— the FALSE guard `σ_k` through whose else-branch the hinge's witness runs. -/
noncomputable def qDuB1 : Semisentence LAct 1 :=
  qT gDu (TS gDu 0) (uS gDu 0) (wS gDu 0) (cl TB0) (cterm Act.D) (cterm Act.C)

theorem guardCode_DuB1 (k : V) :
    guardCode (⌜gDu⌝ : V) (SV gDu 0 k) (pBot (pConst 1)) = instB (⌜qDuB1⌝ : V) k :=
  guardCode_qT_eq_instB gDu k _ _ _ _ _ _ (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k)
    (hW_SV gDu 0 (Or.inl rfl) k) (hX_bot_one k) hU_D_bot_one hW_C_bot_one

/-- The τ-twin: Cupod's guard against `.bot CooperateBot` is the `binNumeral k`-instance of `τ qDuB1`. -/
theorem guardCode_DuB1_swap (k : V) :
    guardCode (⌜gCu⌝ : V) (SV gCu 1 k) (pBot (pConst 0)) = instB (⌜Semiformula.lMap swap qDuB1⌝ : V) k := by
  have h := guardCode_qT_swap_eq_instB gDu k (TS gDu 0) (uS gDu 0) (wS gDu 0) (cl TB0) (cterm Act.D) (cterm Act.C)
    (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k) (hW_SV gDu 0 (Or.inl rfl) k) (hX_bot_one k)
    hU_D_bot_one hW_C_bot_one
  rw [transposeCode_SV gDu 0 (Or.inl rfl), lMap_swap_gDu, transposeCode_pBot, transposeCode_pConst_one] at h
  exact h

/-- The hinge as a fixed formula: "DBot plays C against `DupocBot k`" (DBot by its generic closed description,
`describes_closed`). -/
noncomputable def rDB : Semisentence LAct 1 :=
  qT gDu (TS gDu 0) (uS gDu 0) (wS gDu 0) (cl (canonicalMeta (progCode DBot))) (revalueUMeta (progCode DBot)) (revalueWMeta (progCode DBot))

theorem guardCode_rDB (k : V) :
    guardCode (⌜gDu⌝ : V) (SV gDu 0 k) ((progCode DBot : ℕ) : V) = instB (⌜rDB⌝ : V) k :=
  guardCode_qT_eq_instB gDu k _ _ _ _ _ _ (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k)
    (hW_SV gDu 0 (Or.inl rfl) k)
    (by have := (describes_closed (progCode DBot)).hX V k; rwa [descVal_closed] at this)
    (by have := (describes_closed (progCode DBot)).hU V k; rwa [descVal_closed] at this)
    (by have := (describes_closed (progCode DBot)).hW V k; rwa [descVal_closed] at this)

/-- **The budget box**: `boxCoreK (n, k) := bewB k n k`, i.e. `LenBoxUnbounded TAct k (instB n k)` — the `k`-instance of
the code `n` is provable within the budget `k` ITSELF (`Box_g` has the polylog `gBudget k` here). -/
noncomputable def boxCoreK : Semisentence ℒₒᵣ 2 := “n k. !bewBDef k n k”

noncomputable def boxCoreKA : Semisentence LAct 2 := Semiformula.lMap emb boxCoreK

/-- `boxK χ (k) := □_k χ(k)`, the code `⌜χ⌝` as Foundation's Gödel numeral (a constant, never evaluated). -/
noncomputable def boxK (χ : Semisentence LAct 1) : Semisentence LAct 1 :=
  boxCoreKA ⇜ ![Semiterm.lMap emb (⌜χ⌝ : ArithmeticSemiterm Empty 1), #0]

lemma eval_boxCoreK (n k : V) :
    Semiformula.Eval (s := standardModel V) ![n, k] Empty.elim boxCoreK ↔ LenBoxUnbounded TAct k (instB n k) := by
  simp [boxCoreK, bewB]

/-- **The semantics of `boxK`** in every `LAct`-structure on `V` whose `ℒₒᵣ`-reduct is standard: reading-independent. -/
theorem eval_boxK_iff (χ : Semisentence LAct 1) (S : Structure LAct V)
    (hS : Structure.lMap emb S = standardModel V) (k : V) :
    Semiformula.Eval (s := S) ![k] Empty.elim (boxK χ) ↔ LenBoxUnbounded TAct k (instB (⌜χ⌝ : V) k) := by
  rw [boxK, Semiformula.eval_substs, val_vec_gödel S hS χ k]
  unfold boxCoreKA
  rw [Semiformula.eval_lMap, hS]
  exact eval_boxCoreK _ _

/-- "`σ_k` or its τ-twin is not provable within `k`" — the τ-symmetrized bounded-consistency instance. -/
noncomputable def negTwin : Semisentence LAct 1 := ∼ boxK qDuB1 ⋎ ∼ boxK (Semiformula.lMap swap qDuB1)

/-- "Neither `σ_k` nor its τ-twin is provable within `k`". -/
noncomputable def conjTwin : Semisentence LAct 1 := ∼ boxK qDuB1 ⋏ ∼ boxK (Semiformula.lMap swap qDuB1)

theorem eval_negTwin_iff (S : Structure LAct V) (hS : Structure.lMap emb S = standardModel V) (k : V) :
    Semiformula.Eval (s := S) ![k] Empty.elim negTwin ↔
      (¬ LenBoxUnbounded TAct k (instB (⌜qDuB1⌝ : V) k) ∨
        ¬ LenBoxUnbounded TAct k (instB (⌜Semiformula.lMap swap qDuB1⌝ : V) k)) := by
  unfold negTwin
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.or_eq,
    LogicalConnective.Prop.neg_eq]
  rw [eval_boxK_iff _ S hS, eval_boxK_iff _ S hS]

theorem eval_conjTwin_iff (S : Structure LAct V) (hS : Structure.lMap emb S = standardModel V) (k : V) :
    Semiformula.Eval (s := S) ![k] Empty.elim conjTwin ↔
      (¬ LenBoxUnbounded TAct k (instB (⌜qDuB1⌝ : V) k) ∧
        ¬ LenBoxUnbounded TAct k (instB (⌜Semiformula.lMap swap qDuB1⌝ : V) k)) := by
  unfold conjTwin
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.and_eq,
    LogicalConnective.Prop.neg_eq]
  rw [eval_boxK_iff _ S hS, eval_boxK_iff _ S hS]

/-! #### 5.4 The two uniform theorems -/

/-- **`TAct ⊢ ∀ k, r(k) → negTwin(k)`**: in every model and both readings, DBot's cooperation with `DupocBot k` means
Dupoc did not cooperate with `.bot DefectBot`, i.e. its guard `σ_k` (standard reading) or the τ-twin (swapped
reading) was not found within `k`. -/
theorem tact_rDB_imp_negTwin : TAct ⊢ ∀¹ (rDB 🡒 negTwin) := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro hr
    rw [rDB, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (desc_SV gDu 0 (Or.inl rfl) x) (descVal_closed (progCode DBot) x),
      actCode_C_cast, cast_DBot] at hr
    rw [eval_negTwin_iff _ (by rw [stdReadingV_eq_stdReading]; exact stdReading_lMap_emb)]
    left
    obtain ⟨n, hn⟩ := hr
    obtain ⟨m, r, hm, hr0⟩ := probe_of_dbot_C_V hn
    rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DuB1]
    exact not_found_of_SV_play hm (by simpa using hr0)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro hr
    rw [rDB, eval_qT_swap, lMap_swap_gDu, eval_qT_plays_opp_self .D _ _ _ _ _ _ x (descT_SV gDu 0 (Or.inl rfl) x)
      (descVal_closed_T (progCode DBot) x), actCode_D_cast, cast_DBot, transposeCode_DBotV, lMap_swap_gDu] at hr
    rw [eval_negTwin_iff _ swappedReading_lMap_emb]
    right
    obtain ⟨n, hn⟩ := hr
    obtain ⟨m, r, hm, hr1⟩ := probe_of_dbotT_D_V hn
    rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DuB1_swap]
    exact not_found_of_SV_play hm (by simpa using hr1)

/-- **`TAct ⊢ ∀ k, conjTwin(k) → r(k)`**: neither guard found ⇒ Dupoc's else-branch (D against `.bot DefectBot`,
C for Cupod against `.bot CooperateBot` in the swapped reading) ⇒ DBot's probe fails ⇒ DBot cooperates. -/
theorem tact_conjTwin_imp_rDB : TAct ⊢ ∀¹ (conjTwin 🡒 rDB) := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro h
    obtain ⟨h1, _⟩ := (eval_conjTwin_iff _ (by rw [stdReadingV_eq_stdReading]; exact stdReading_lMap_emb) x).mp h
    rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DuB1] at h1
    rw [rDB, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (desc_SV gDu 0 (Or.inl rfl) x) (descVal_closed (progCode DBot) x),
      actCode_C_cast, cast_DBot]
    exact ⟨_, dbot_C_of_probe_D_V (dupoc_else_V x _ h1)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro h
    obtain ⟨_, h2⟩ := (eval_conjTwin_iff _ swappedReading_lMap_emb x).mp h
    rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DuB1_swap] at h2
    rw [rDB, eval_qT_swap, lMap_swap_gDu, eval_qT_plays_opp_self .D _ _ _ _ _ _ x (descT_SV gDu 0 (Or.inl rfl) x)
      (descVal_closed_T (progCode DBot) x), actCode_D_cast, cast_DBot, transposeCode_DBotV, lMap_swap_gDu]
    exact ⟨_, dbotT_D_of_probe_C_V (cupod_else_V x _ h2)⟩

/-! #### 5.5 At ℕ: the hinge code is the instance of `r`; the reduction and its converse -/

/-- The hinge of Dupoc × DBot, as consulted by the evaluator, is the `binNumeral k`-instance of `rDB`. -/
theorem hinge_DupocBot_vs_DBot_eq (k : ℕ) :
    guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode DBot) k =
      (⌜(rDB ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  rw [hingeB phiDu, progCode_DupocBot_SV, templateCode_eq_quote_template phiDu rfl]
  have e := guardCode_rDB (V := ℕ) k
  rw [natCast_nat] at e
  have hq : instB (⌜rDB⌝ : ℕ) k = ⌜(rDB ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) rDB k
    rwa [natCast_nat] at this
  rw [← hq]
  exact e

/-- **THE REDUCTION.** If the hinge of Dupoc × DBot holds — "DBot plays C against `DupocBot k`" is `TAct`-provable
within `k` — then "`σ_k` or its τ-twin is NOT provable within `k`" (`σ_k` = Dupoc's guard against `.bot DefectBot`,
FALSE in ℕ; `negTwin_true_iff`) is `TAct`-provable within `k + C₀ + C₁·size k`: one instantiation of the uniform
theorem `tact_rDB_imp_negTwin` at `binNumeral k` and one modus ponens (`lenBoxNat_mp`), whose cut formulas carry the
binary numeral of `k`. The hinge is at least as hard as bounded consistency at `k`, up to this additive overhead. -/
theorem hinge_reduces_to_bounded_consistency_DupocBot_vs_DBot :
    ∃ C₀ C₁ : ℕ, ∀ k : ℕ,
      LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode DBot) k) →
      LenBox TAct (k + C₀ + C₁ * Nat.size k)
        (⌜(negTwin ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  obtain ⟨N₃, hN₃⟩ := lenBoxNat_of_provable tact_rDB_imp_negTwin
  refine ⟨N₃ + 13 * formulaLenMeta ((rDB 🡒 negTwin : Semisentence LAct 1) : Semiproposition LAct 1) + 8
      + 20 * formulaLenMeta (rDB : Semiproposition LAct 1) + 20 * formulaLenMeta (negTwin : Semiproposition LAct 1) + 9,
    30 * formulaLenMeta ((rDB 🡒 negTwin : Semisentence LAct 1) : Semiproposition LAct 1) + 6
      + 60 * formulaLenMeta (rDB : Semiproposition LAct 1) + 60 * formulaLenMeta (negTwin : Semiproposition LAct 1),
    fun k hA ↦ ?_⟩
  rw [hinge_DupocBot_vs_DBot_eq, lenBox_nat] at hA
  have h1 := lenBoxNat_inst_size (rDB 🡒 negTwin) k hN₃
  have hχt := formulaLenMeta_subst_binNumeralMeta_le (rDB 🡒 negTwin) k
  have hrt := formulaLenMeta_subst_binNumeralMeta_le rDB k
  have hnt := formulaLenMeta_subst_binNumeralMeta_le negTwin k
  set t : ClosedSemiterm LAct 0 := Semiterm.lMap emb (binNumeralMeta k) with ht
  set s := Nat.size k with hs
  set fχ := formulaLenMeta ((rDB 🡒 negTwin : Semisentence LAct 1) : Semiproposition LAct 1) with hfχ
  set fr := formulaLenMeta (rDB : Semiproposition LAct 1) with hfr
  set fn := formulaLenMeta (negTwin : Semiproposition LAct 1) with hfn
  have h1' : LenBoxNat (codeBound : ℕ → ℕ) (N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8) TAct
      (⌜((rDB 🡒 negTwin) ⇜ ![t] : Sentence LAct)⌝ : ℕ) :=
    lenBoxNat_codeBound_mono (by omega) h1
  rw [substs_imp] at h1'
  have h3 := lenBoxNat_mp h1' hA
  rw [lenBox_nat]
  refine lenBoxNat_codeBound_mono ?_ h3
  calc _ ≤ N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8 + k
        + 10 * (fr * (6 * s + 2) + fn * (6 * s + 2)) + 9 := by gcongr
    _ = k + (N₃ + 13 * fχ + 8 + 20 * fr + 20 * fn + 9) + (30 * fχ + 6 + 60 * fr + 60 * fn) * s := by ring

/-- **THE CONVERSE.** A `TAct`-proof within `m` of "neither `σ_k` nor its τ-twin is provable within `k`" yields the
hinge — "DBot plays C against `DupocBot k`" — within `m + C₀ + C₁·size k`, by the evaluator's determinism inside
`TAct` (`tact_conjTwin_imp_rDB`): the conjunction, not the disjunction, because each reading needs its own twin. -/
theorem bounded_consistency_reduces_to_hinge_DupocBot_vs_DBot :
    ∃ C₀ C₁ : ℕ, ∀ k m : ℕ,
      LenBox TAct m (⌜(conjTwin ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) →
      LenBox TAct (m + C₀ + C₁ * Nat.size k)
        (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode DBot) k) := by
  obtain ⟨N₃, hN₃⟩ := lenBoxNat_of_provable tact_conjTwin_imp_rDB
  refine ⟨N₃ + 13 * formulaLenMeta ((conjTwin 🡒 rDB : Semisentence LAct 1) : Semiproposition LAct 1) + 8
      + 20 * formulaLenMeta (conjTwin : Semiproposition LAct 1) + 20 * formulaLenMeta (rDB : Semiproposition LAct 1) + 9,
    30 * formulaLenMeta ((conjTwin 🡒 rDB : Semisentence LAct 1) : Semiproposition LAct 1) + 6
      + 60 * formulaLenMeta (conjTwin : Semiproposition LAct 1) + 60 * formulaLenMeta (rDB : Semiproposition LAct 1),
    fun k m hC ↦ ?_⟩
  rw [lenBox_nat] at hC
  have h1 := lenBoxNat_inst_size (conjTwin 🡒 rDB) k hN₃
  have hχt := formulaLenMeta_subst_binNumeralMeta_le (conjTwin 🡒 rDB) k
  have hct := formulaLenMeta_subst_binNumeralMeta_le conjTwin k
  have hrt := formulaLenMeta_subst_binNumeralMeta_le rDB k
  set t : ClosedSemiterm LAct 0 := Semiterm.lMap emb (binNumeralMeta k) with ht
  set s := Nat.size k with hs
  set fχ := formulaLenMeta ((conjTwin 🡒 rDB : Semisentence LAct 1) : Semiproposition LAct 1) with hfχ
  set fc := formulaLenMeta (conjTwin : Semiproposition LAct 1) with hfc
  set fr := formulaLenMeta (rDB : Semiproposition LAct 1) with hfr
  have h1' : LenBoxNat (codeBound : ℕ → ℕ) (N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8) TAct
      (⌜((conjTwin 🡒 rDB) ⇜ ![t] : Sentence LAct)⌝ : ℕ) :=
    lenBoxNat_codeBound_mono (by omega) h1
  rw [substs_imp] at h1'
  have h3 := lenBoxNat_mp h1' hC
  rw [hinge_DupocBot_vs_DBot_eq, lenBox_nat]
  refine lenBoxNat_codeBound_mono ?_ h3
  calc _ ≤ N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8 + m
        + 10 * (fc * (6 * s + 2) + fr * (6 * s + 2)) + 9 := by gcongr
    _ = m + (N₃ + 13 * fχ + 8 + 20 * fc + 20 * fr + 9) + (30 * fχ + 6 + 60 * fc + 60 * fr) * s := by ring

/-! #### 5.6 What the conclusion SAYS at ℕ -/

/-- The `binNumeral k`-instance of the τ-twin is the τ-image of the instance (the numeral is an `ℒₒᵣ`-term, fixed by τ). -/
lemma substs_lMap_swap_binNumeralMeta (φ : Semisentence LAct 1) (k : ℕ) :
    ((Semiformula.lMap swap φ) ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct) =
      Semiformula.lMap swap (φ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct) := by
  rw [Semiformula.lMap_subst]
  congr 1
  funext i
  fin_cases i
  simp [term_lMap_swap_emb]

/-- **At ℕ, `negTwin(k)` says exactly "Dupoc's guard against `.bot DefectBot` is not provable within `k`"**: the two
disjuncts are equivalent by the τ-symmetry of `TAct`'s proofs (`lenBoxNat_swap_iff`, exact in length). So
the reduction's conclusion is the bounded-consistency-type statement `¬□_k σ_k` — TRUE at every `k` (`σ_k` is false
and `TAct` is sound), and the question is only whether `TAct` PROVES it within `k + c`. -/
theorem negTwin_true_iff (k : ℕ) :
    ℕ↓[LAct] ⊧ (negTwin ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct) ↔
      ¬ LenBox TAct k (guardCode (templateCode phiDu) (progCode (DupocBot k)) (pBot (pConst 1))) := by
  rw [models_iff]
  unfold Semiformula.Realize
  rw [Semiformula.eval_substs]
  have hv : (Semiterm.val (s := stdReadingNat) ![] Empty.elim ∘ ![Semiterm.lMap emb (binNumeralMeta k)]) = ![(k : ℕ)] := by
    funext i
    fin_cases i
    show Semiterm.val (s := stdReadingNat) ![] Empty.elim (Semiterm.lMap emb (binNumeralMeta k)) = k
    rw [Semiterm.val_lMap, stdReadingNat_lMap_emb]
    have := val_binNumeralMeta_V (V := ℕ) k
    rwa [natCast_nat] at this
  rw [hv, eval_negTwin_iff stdReadingNat stdReadingNat_lMap_emb k, lenBoxUnbounded_iff_lenBox, lenBoxUnbounded_iff_lenBox,
    progCode_DupocBot_SV, templateCode_eq_quote_template phiDu rfl]
  have e1 := guardCode_DuB1 (V := ℕ) k
  have e2 := guardCode_DuB1_swap (V := ℕ) k
  have hq1 : instB (⌜qDuB1⌝ : ℕ) k = ⌜(qDuB1 ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) qDuB1 k
    rwa [natCast_nat] at this
  have hq2 : instB (⌜Semiformula.lMap swap qDuB1⌝ : ℕ) k =
      ⌜((Semiformula.lMap swap qDuB1) ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) (Semiformula.lMap swap qDuB1) k
    rwa [natCast_nat] at this
  have hsym : LenBox TAct k (instB (⌜Semiformula.lMap swap qDuB1⌝ : ℕ) k) ↔
      LenBox TAct k (instB (⌜qDuB1⌝ : ℕ) k) := by
    rw [hq1, hq2, lenBox_nat, lenBox_nat, substs_lMap_swap_binNumeralMeta]
    exact (lenBoxNat_swap_iff k _).symm
  rw [hsym, ← e1]
  constructor
  · rintro (h | h) <;> exact h
  · exact fun h ↦ Or.inl h

end reduction

end ArithS
