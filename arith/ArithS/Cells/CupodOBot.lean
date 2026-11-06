import ArithS.Cells.FloorDichotomy
import ArithS.Cells.Dimdid

/-!
# ArithS.Cells.CupodOBot — `CupodBot × OBot = (D, D)` in PA-`S'`: the hinge is FOUND

The verdict pass (`Cells/FloorVerdicts` §7) rated this pair a GENUINE floor: Cupod's guard "OBot plays D against
me" is TRUE, and OBot's evaluation runs through Cupod's ELSE-play against `.bot CooperateBot` (a search on a guard
false in ℕ). The EVALUATION does; a PROOF need not. OBot cooperates only with an opponent that cooperates with
BOTH `.bot CooperateBot` and `.bot DefectBot`:

  `OBot = ite (opp vs .bot CooperateBot = C) (ite (opp vs .bot DefectBot = C) C D) D`.

Cupod DEFECTS against `.bot DefectBot` through its THEN-branch, on a true atom found in every model above a
standard threshold (`cupod_botDB_V`). So OBot's defection is OVER-DETERMINED: whatever Cupod plays against
`.bot CooperateBot` — and a searcher always plays something, its Δ₁ box holds or fails — OBot ends on a `D`. `TAct`
splits on that play without deciding it; no bounded-consistency statement is needed. Hence

  `TAct ⊢ ∀ k ≥ k̂, "OBot plays D against CupodBot k"`   (`tact_rOB_above`, both readings),

its instance at `k` is found within `k` by the `k̂`-chain (`found_of_all_above`), Cupod plays its then-branch, and
the pair is `(D, D)` for all large `k` — the FOUND branch of `split_CupodBot_vs_OBot`, a FLIP of the engine's
`outcome_CupodBot_vs_OBot = (C, D)` (whose `+k` floor `no_provable_OBot_D_tail` stipulates the not-found side; `S`
has no rule that splits on a search it cannot read).

Contrast DBot and EBot (`Cells/FloorDichotomy` §5, `Cells/FloorReductions`): their cooperation with a searcher
REQUIRES the searcher's else-play, so their hinges are inter-reducible with bounded consistency.

1. **OBot in every model** is `Cells/Dimdid`'s (`OBotV`, `OBotTV`, `cast_OBot`, `transposeCode_OBotV`, and the two
   over-determination lemmas `obot_D_of_any_V`/`obotT_C_of_any_V`, written on 2026-10-13 for DIMDID × OBot — the
   same argument; it was not tried on Cupod then).
2. **The over-determined defection on the searchers**: `SV_play_succ_V` (one fuel step for a searcher, in any model
   — there is no general fuel monotonicity off ℕ), `obot_D_vs_cupod_V`, `obotT_C_vs_dupoc_V`.
3. **The hinge as a fixed formula** `rOB`, its instance equation, the uniform theorem `tact_rOB_above`.
4. **The cell**: `hinge_found_CupodBot_vs_OBot`, `khat_CupodBot_vs_OBot`.

Conventions: every threshold EXISTENTIAL; `simp` never sees a closed quote; no `sorry`, no `axiom`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

section obot

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 2. The over-determined defection -/

/-- **One fuel step for a searcher, in any model and any frame.** (Fuel monotonicity is a theorem at ℕ only; a
searcher's two branches are constants, so one step is immediate from the search clause.) -/
theorem SV_play_succ_V (g : Semisentence LAct 6) (a : ℕ) {x me opp r n : V}
    (h : EvalGraph n me opp (SV g a x) r) : EvalGraph (n + 1) me opp (SV g a x) r := by
  obtain ⟨n', rfl, _⟩ := EvalGraph.case_iff.mp h
  change EvalGraph (n' + 1) me opp (pSearch x (⌜g⌝ : V) (pConst (a : V)) (pConst ((1 - a : ℕ) : V))) r at h
  show EvalGraph (n' + 1 + 1) me opp (pSearch x (⌜g⌝ : V) (pConst (a : V)) (pConst ((1 - a : ℕ) : V))) r
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ g)] at h ⊢
  rcases h with ⟨hf, hp⟩ | ⟨hn, hp⟩
  · obtain ⟨m, rfl, _⟩ := EvalGraph.case_iff.mp hp
    exact Or.inl ⟨hf, EvalGraph.const_iff.mpr (EvalGraph.const_iff.mp hp)⟩
  · obtain ⟨m, rfl, _⟩ := EvalGraph.case_iff.mp hp
    exact Or.inr ⟨hn, EvalGraph.const_iff.mpr (EvalGraph.const_iff.mp hp)⟩

/-- **OBot defects against `CupodBot k` in every model, above a standard threshold**: Cupod's then-branch D against
`.bot DefectBot` (`cupod_botDB_V`), and a case split on its box against `.bot CooperateBot`. -/
theorem obot_D_vs_cupod_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      ∃ n : V, EvalGraph n OBotV (SV gCu 1 k) OBotV 1 := by
  obtain ⟨kHat, h⟩ := cupod_botDB_V
  refine ⟨kHat, fun V _ _ k hk ↦ ?_⟩
  by_cases hf : LenBox TAct k (guardCode (⌜gCu⌝ : V) (SV gCu 1 k) (pBot (pConst 0)))
  · exact ⟨_, obot_D_of_any_V (SV_play_succ_V gCu 1 (SV_search_V gCu 1 k _ hf)) (h V k hk)⟩
  · exact ⟨_, obot_D_of_any_V (SV_play_succ_V gCu 1 (cupod_else_V k _ hf)) (h V k hk)⟩

/-- The transposed OBot cooperates with `DupocBot k` in every model, above a standard threshold. -/
theorem obotT_C_vs_dupoc_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      ∃ n : V, EvalGraph n OBotTV (SV gDu 0 k) OBotTV 0 := by
  obtain ⟨kHat, h⟩ := dupoc_botCB_V
  refine ⟨kHat, fun V _ _ k hk ↦ ?_⟩
  by_cases hf : LenBox TAct k (guardCode (⌜gDu⌝ : V) (SV gDu 0 k) (pBot (pConst 1)))
  · exact ⟨_, obotT_C_of_any_V (SV_play_succ_V gDu 0 (SV_search_V gDu 0 k _ hf)) (h V k hk)⟩
  · exact ⟨_, obotT_C_of_any_V (SV_play_succ_V gDu 0 (dupoc_else_V k _ hf)) (h V k hk)⟩

/-! ### 3. The hinge as a fixed formula, and the uniform theorem -/

/-- The hinge as a fixed formula: "OBot plays D against `CupodBot k`" (OBot by its generic closed description,
`describes_closed`). -/
noncomputable def rOB : Semisentence LAct 1 :=
  qT gCu (TS gCu 1) (uS gCu 1) (wS gCu 1) (cl (canonicalMeta (progCode OBot))) (revalueUMeta (progCode OBot))
    (revalueWMeta (progCode OBot))

theorem guardCode_rOB (k : V) :
    guardCode (⌜gCu⌝ : V) (SV gCu 1 k) ((progCode OBot : ℕ) : V) = instB (⌜rOB⌝ : V) k :=
  guardCode_qT_eq_instB gCu k _ _ _ _ _ _ (hX_SV gCu 1 (Or.inr rfl) k) (hU_SV gCu 1 (Or.inr rfl) k)
    (hW_SV gCu 1 (Or.inr rfl) k)
    (by have := (describes_closed (progCode OBot)).hX V k; rwa [descVal_closed] at this)
    (by have := (describes_closed (progCode OBot)).hU V k; rwa [descVal_closed] at this)
    (by have := (describes_closed (progCode OBot)).hW V k; rwa [descVal_closed] at this)

end obot

/-- **`TAct ⊢ ∀ k ≥ k̂, "OBot plays D against CupodBot k"`**: in every model and both readings, by the
over-determined defection — no bounded-consistency statement enters. -/
theorem tact_rOB_above : ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 rOB) := by
  obtain ⟨k₁, h₁⟩ := obot_D_vs_cupod_V
  obtain ⟨k₂, h₂⟩ := obotT_C_vs_dupoc_V
  refine ⟨k₁ + k₂, tact_all_above_of_both _ _ (fun M _ _ x hx ↦ ?_) (fun M _ _ x hx ↦ ?_)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [rOB, eval_qT_plays_opp_self .D _ _ _ _ _ _ x (desc_SV gCu 1 (Or.inr rfl) x) (descVal_closed (progCode OBot) x),
      actCode_D_cast, cast_OBot]
    exact h₁ M x (le_trans (by push_cast; exact le_self_add) hx)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [rOB, eval_qT_swap, lMap_swap_gCu, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (descT_SV gCu 1 (Or.inr rfl) x)
      (descVal_closed_T (progCode OBot) x), actCode_C_cast, cast_OBot, transposeCode_OBotV, lMap_swap_gCu]
    exact h₂ M x (le_trans (by push_cast; exact le_add_self) hx)

/-! ### 4. The cell -/

/-- **The hinge of Cupod × OBot is FOUND for all large `k`**: Cupod's guard "OBot plays D against me" is provable
within `k` (the `k̂`-chain on `tact_rOB_above`). -/
theorem hinge_found_CupodBot_vs_OBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode OBot) k) := by
  obtain ⟨kHat, hq⟩ := tact_rOB_above
  obtain ⟨k₀, h⟩ := found_of_all_above kHat hq
    (fun k ↦ guardCode (templateCode phiCu) (progCode (CupodBot k)) (progCode OBot))
    (fun k ↦ by
      have e := guardCode_rOB (V := ℕ) k
      rw [natCast_nat] at e
      rw [progCode_CupodBot_SV, templateCode_eq_quote_template phiCu rfl]
      exact e)
  exact ⟨k₀, fun k hk ↦ by rw [hingeB phiCu]; exact h k hk⟩

/-- **`CupodBot × OBot = (D, D)`** for all large `k`, on the engine's own codes at the engine's pad 5 — a FLIP of
the engine's `outcome_CupodBot_vs_OBot = (C, D)`: the found branch of `split_CupodBot_vs_OBot`. -/
theorem khat_CupodBot_vs_OBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 5 (progCode (CupodBot k)) (progCode OBot) (progCode (CupodBot k)) (actCode .D) ∧
      EvalGraph 5 (progCode OBot) (progCode (CupodBot k)) (progCode OBot) (actCode .D) := by
  obtain ⟨k₁, hd⟩ := split_CupodBot_vs_OBot
  obtain ⟨k₂, hf⟩ := hinge_found_CupodBot_vs_OBot
  exact ⟨k₁ + k₂, fun k hk ↦ (hd k (by omega)).2 (hf k (by omega))⟩

end ArithS
