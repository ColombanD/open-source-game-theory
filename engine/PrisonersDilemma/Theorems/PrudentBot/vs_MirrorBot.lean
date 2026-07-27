import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.PrudentBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- MirrorBot --

/-- The prudence atom is a true Σ₁ fact: MirrorBot mirrors `.bot DefectBot`'s
    defection, so it plays `D` against it. -/
theorem MirrorBot_plays_D_vs_bot_DefectBot (fuel : Nat) :
    play (fuel + 3) MirrorBot (.bot DefectBot) = some .D := by
  show eval (fuel + 3) MirrorBot (.bot DefectBot) MirrorBot = some .D
  simp [eval, Prog.subst, MirrorBot, DefectBot]

/-- Hence the prudence atom `MirrorBot plays D vs DefectBot` is provable (for `k`
    large enough to fit the certificate). -/
theorem prudence_provable :
    Pf 27 (Formula.plays MirrorBot (.bot DefectBot) Action.D) := by
  have hPlay : play 3 MirrorBot (.bot DefectBot) = some .D := by
    simpa using MirrorBot_plays_D_vs_bot_DefectBot 0
  exact Pf.atom (atom_monotone (3 ^ 3) 27 _ (by norm_num)
    (atom_complete_searchfree MirrorBot (.bot DefectBot) Action.D 3 rfl rfl hPlay))

/-- **Löb premise for PrudentBot vs MirrorBot**, built with the new
    `searchThenSearch_t` rule. Two legs, chained by `implTrans`:
    * `searchThenSearch_t` reads PrudentBot's stacked `.search`/`.search` body and,
      *given the provable prudence atom*, yields `□_k φ → (PrudentBot plays C vs
      MirrorBot)` — the prudence box already discharged, leaving a single box;
    * `simStep` reads MirrorBot's `.sim .opp .self` swap: `(PrudentBot plays C vs
      MirrorBot) → (MirrorBot plays C vs PrudentBot)`.
    The result is the closed `□_k φ → φ` that `PBLT` consumes. -/
theorem prudent_mirror_loeb_premise (k : Nat) (hk : 27 ≤ k) :
    Pf (50 * Nat.log2 k + 500)
      (.impl (.box k (Formula.plays MirrorBot (PrudentBot k) Action.C))
             (Formula.plays MirrorBot (PrudentBot k) Action.C)) := by
  -- TRANSCRIPT-TIGHT: the whole premise costs O(log k) — searchThenSearch pays the
  -- prudence certificate (search-free, ≤ 27 chars, whence `27 ≤ k` so the inner
  -- search at budget `k` finds it) + its conclusion; the `.sim` leg is one leaf;
  -- `implTrans` pays both legs + the conclusion. No `K₀` eventuality.
  -- Leg 1: `□_k φ → (PrudentBot plays C vs Mirror)` via `searchThenSearch_t`.
  have leg1 : Pf (20 * Nat.log2 k + 200)
      (.impl (.box k (Formula.plays MirrorBot (PrudentBot k) Action.C))
             (Formula.plays (PrudentBot k) MirrorBot Action.C)) := by
    refine Pf.searchThenSearch_t k k 27
      (Formula.plays .opp .self Action.C)
      (Formula.plays .opp (.bot DefectBot) Action.D)
      Action.C Action.D (.const Action.D) (PrudentBot k) MirrorBot rfl
      prudence_provable (by omega) ?_
    simp only [numCost, Formula.subst, Prog.subst, Formula.size, Prog.size, PrudentBot, MirrorBot,
      DefectBot, c_guard]
    omega
  -- Leg 2: MirrorBot's `.sim` swap, as a bare `Pf.simStep` leaf.
  have leg2 : Pf (20 * Nat.log2 k + 200)
      (.impl (Formula.plays (PrudentBot k) MirrorBot Action.C)
             (Formula.plays MirrorBot (PrudentBot k) Action.C)) := by
    refine Pf.simStep MirrorBot .opp .self (PrudentBot k) Action.C rfl ?_
    simp only [Prog.subst, numCost, Formula.size, Prog.size, PrudentBot, MirrorBot, DefectBot]
    omega
  -- Chain leg1 (`□φ → A`) then leg2 (`A → φ`) into `□_k φ → φ` via `implTrans`.
  refine Pf.implTrans _ _ _ (20 * Nat.log2 k + 200) (20 * Nat.log2 k + 200) leg1 leg2 ?_
  simp only [numCost, Formula.size, Prog.size, PrudentBot, MirrorBot, DefectBot]
  omega

/-- Once `proofSearch k = true`, PrudentBot's stacked searches both fire (the inner
    prudence guard is the provable Σ₁ atom), so it cooperates with MirrorBot. -/
theorem PrudentBot_plays_C_against_MirrorBot (k fuel : Nat)
    (hCoop : proofSearch k (Formula.plays MirrorBot (PrudentBot k) Action.C) = true)
    (hPrud : proofSearch k (Formula.plays MirrorBot (.bot DefectBot) Action.D) = true) :
    play (fuel + 3) (PrudentBot k) MirrorBot = some .C := by
  show eval (fuel + 3) (PrudentBot k) MirrorBot (PrudentBot k) = some .C
  unfold PrudentBot at hCoop ⊢
  simp [eval, Prog.subst, Formula.subst, hCoop, hPrud]

/-- MirrorBot mirrors PrudentBot's cooperate via the `.sim .opp .self` swap. -/
theorem MirrorBot_plays_C_against_PrudentBot (k fuel : Nat)
    (hCoop : proofSearch k (Formula.plays MirrorBot (PrudentBot k) Action.C) = true)
    (hPrud : proofSearch k (Formula.plays MirrorBot (.bot DefectBot) Action.D) = true) :
    play (fuel + 4) MirrorBot (PrudentBot k) = some .C := by
  have hPrudent : play (fuel + 3) (PrudentBot k) MirrorBot = some .C :=
    PrudentBot_plays_C_against_MirrorBot k fuel hCoop hPrud
  simpa [play, eval, Prog.subst, MirrorBot] using hPrudent

/-- When PrudentBot's cooperation search fails, it lands in its root else-branch
    and defects against MirrorBot. -/
theorem PrudentBot_plays_D_against_MirrorBot (k fuel : Nat)
    (hf : proofSearch k (Formula.plays MirrorBot (PrudentBot k) Action.C) = false) :
    play (fuel + 2) (PrudentBot k) MirrorBot = some .D := by
  show eval (fuel + 2) (PrudentBot k) MirrorBot (PrudentBot k) = some .D
  unfold PrudentBot at hf ⊢
  simp [eval, Prog.subst, Formula.subst, hf]

/-- Inversion: a cooperation `play` on MirrorBot's leg forces PrudentBot's outer
    search to have fired at budget `k`. (If it were false, MirrorBot would mirror
    PrudentBot's defection and play `D`, contradicting the `C` witness.) -/
theorem proofSearch_k_of_play_MirrorBot_prudent
    (k n : Nat) (h : play n MirrorBot (PrudentBot k) = some .C) :
    proofSearch k (Formula.plays MirrorBot (PrudentBot k) Action.C) = true := by
  cases hps : proofSearch k (Formula.plays MirrorBot (PrudentBot k) Action.C) with
  | true  => rfl
  | false =>
    exfalso
    -- MirrorBot mirrors PrudentBot's defection: it plays D at high fuel.
    have hPrudD : ∀ f, play (f + 2) (PrudentBot k) MirrorBot = some .D :=
      fun f => PrudentBot_plays_D_against_MirrorBot k f hps
    have hMirD : play (n + 3) MirrorBot (PrudentBot k) = some .D := by
      have hP : play (n + 2) (PrudentBot k) MirrorBot = some .D := hPrudD n
      simpa [play, eval, Prog.subst, MirrorBot] using hP
    have hMonoC : play (n + 3) MirrorBot (PrudentBot k) = some .C := by
      unfold play at h ⊢
      exact eval_mono_le h (n + 3) (by omega)
    rw [hMonoC] at hMirD
    cases hMirD

/-- **PrudentBot vs MirrorBot → (C, C)** for all large enough `k`. Application of
    `PBLT` to the Löb premise: the cooperation atom `φ = MirrorBot plays C vs
    PrudentBot` is provable, so PrudentBot's outer search fires; the prudence atom
    is independently provable, so the inner search fires too — both bots cooperate.

    Contrast the *old* PrudentBot (prudence `.ite` over the search), whose Löb
    premise was unprovable: the fix was the `searchThenSearch_t` transparency rule,
    which lets S read PrudentBot's stacked-`.search` body. -/
theorem outcome_PrudentBot_vs_MirrorBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) MirrorBot = some (.C, .C) := by
  let φ : Nat → Formula := fun k => Formula.plays MirrorBot (PrudentBot k) Action.C
  have hLoeb : ∀ k, k > 27 →
      Pf (50 * Nat.log2 k + 500) (.impl (.box k (φ k)) (φ k)) := by
    intro k hk
    exact prudent_mirror_loeb_premise k (by omega)
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays MirrorBot (PrudentBot k) Action.C).size ≤ _
    simp only [numCost, Formula.size, Prog.size, PrudentBot, MirrorBot, DefectBot]
    omega
  have hpm : ∀ k, 50 * Nat.log2 k + 500 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 50 * Nat.log2 k + 500) 27 hφsz hpm hLoeb
  refine ⟨max k₂ 27, fun k hk => ?_⟩
  have hk2 : k > k₂ := lt_of_le_of_lt (le_max_left _ _) hk
  have hkP : (27 : Nat) ≤ k :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk)
  -- PBLT gives `Pf m (φ k)` at *some* budget `m`; its truth yields a play
  -- witness, which the inversion lemma lifts to `proofSearch k = true` at budget `k`.
  obtain ⟨m, hm⟩ := hk₂ k hk2
  obtain ⟨n, hMir⟩ := Pf_sound m (φ k) hm
  have hCoopPS : proofSearch k (Formula.plays MirrorBot (PrudentBot k) Action.C) = true :=
    proofSearch_k_of_play_MirrorBot_prudent k n hMir
  have hPrudPS : proofSearch k (Formula.plays MirrorBot (.bot DefectBot) Action.D) = true :=
    (proofSearch_spec _ _).2 (Pf_mono prudence_provable hkP)
  refine ⟨4, ?_⟩
  have hA : play 4 (PrudentBot k) MirrorBot = some .C := by
    simpa using PrudentBot_plays_C_against_MirrorBot k 1 hCoopPS hPrudPS
  have hB : play 4 MirrorBot (PrudentBot k) = some .C := by
    simpa using MirrorBot_plays_C_against_PrudentBot k 0 hCoopPS hPrudPS
  exact outcome_of_plays _ _ _ _ _ hA hB
end PD.Theorems
