import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.PrudentBot.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.JustBot.Helpers
import PrisonersDilemma.Base.Exclusion
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- PrudentBot --

/-- When `.bot (DupocBot k)`'s guard fails, it defects against PrudentBot. -/
theorem bot_dupoc_D_vs_prudent (k fuel : Nat)
    (hk : proofSearch k (.plays (PrudentBot k) (.bot (DupocBot k)) .C) = false) :
    play (fuel + 3) (.bot (DupocBot k)) (PrudentBot k) = some .D := by
  show eval (fuel + 3) (.bot (DupocBot k)) (PrudentBot k) (.bot (DupocBot k)) = some .D
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- Inversion: a cooperating play on `.bot (DupocBot k)`'s leg forces its guard
    (PrudentBot plays C vs `.bot DupocBot`) to have fired. -/
theorem ps_k_of_play_botdupoc (k n : Nat)
    (h : play n (.bot (DupocBot k)) (PrudentBot k) = some .C) :
    proofSearch k (.plays (PrudentBot k) (.bot (DupocBot k)) .C) = true := by
  cases hps : proofSearch k (.plays (PrudentBot k) (.bot (DupocBot k)) .C) with
  | true => rfl
  | false =>
    exfalso
    have hD : play (n + 3) (.bot (DupocBot k)) (PrudentBot k) = some .D :=
      bot_dupoc_D_vs_prudent k n hps
    have hC : play (n + 3) (.bot (DupocBot k)) (PrudentBot k) = some .C := by
      unfold play at h ⊢; exact eval_mono_le h (n + 3) (by omega)
    rw [hC] at hD; cases hD

/-! ### JustBot × PrudentBot — RETIRED at same-`k` (2026-07-02, the false-guard repair).

The former `prudent_botdupoc_legPD`/`legDP`/`prudent_botdupoc_coop`/
`outcome_JustBot_vs_PrudentBot` were axiom artifacts: PrudentBot's prudence fact
"`.bot (DupocBot k)` defects vs `.bot DefectBot`" is an ELSE-play of Dupoc's own search
(floor `k`), unaffordable inside PrudentBot's same-`k` inner search; and JustBot's own
defection vs `.bot DefectBot` (consumed as PrudentBot's prudence about JustBot) is
JustBot's OWN else-play — same floor. Staggered budgets (PrudentBot at `j ≥ k + O(log k)`,
via the two-budget mutual wrapper) are T3.2b; cf. the PrudentBot×DupocBot tombstone in
`Theorems/PrudentBot/vs_DupocBot.lean`. -/


/-! ### JustBot × PrudentBot — RECOVERED with STAGGERED budgets (T3.2b, 2026-07-03).

`JustBot k` vs `PrudentBot (2k+64)`: PrudentBot's inner search affords `.bot (DupocBot k)`'s
`search_f`-floored prudence certificate, and PrudentBot's outer guard affords JustBot's own
floored defection-vs-DefectBot certificate; the mutual Löb chain runs through
`mutual_pblt_engine_staggered` on the (botDupoc, PrudentBot) leg pair. -/

/-- `.bot (DupocBot k)`'s else-play vs `.bot DefectBot`, certified at the FLOOR. -/
theorem prudence_botdupoc (k : Nat) :
    Pf (k + Nat.log2 k + 17) (.plays (.bot (DupocBot k)) (.bot DefectBot) .D) := by
  have hneg : Pf (Nat.log2 k + 14)
      (.neg (.plays (.bot DefectBot) (.bot (DupocBot k)) .C)) := by
    refine Pf.atomNeg (.bot DefectBot) (.bot (DupocBot k)) .D .C 2
      ⟨PlaysProof.bot PlaysProof.const, by decide⟩ (by decide) ?_
    simp only [numCost, Formula.size, Prog.size, DefectBot, DupocBot]
    omega
  have hcert := atom_search_f_bot_top k (Nat.log2 k + 14) (.plays .opp .self .C) .C .D
    (.bot DefectBot) hneg
  exact Pf.atom (atom_monotone _ _ _ (by omega) hcert)

/-- JustBot's else-play vs `.bot DefectBot`, certified at the FLOOR (consumed as
    PrudentBot's prudence fact about JustBot). -/
theorem justbot_prudence (k : Nat) :
    Pf (k + Nat.log2 k + 16) (.plays (JustBot k) (.bot DefectBot) .D) := by
  have hneg : Pf (Nat.log2 k + 14)
      (.neg (.plays (.bot DefectBot) (.bot (DupocBot k)) .C)) := by
    refine Pf.atomNeg (.bot DefectBot) (.bot (DupocBot k)) .D .C 2
      ⟨PlaysProof.bot PlaysProof.const, by decide⟩ (by decide) ?_
    simp only [numCost, Formula.size, Prog.size, DefectBot, DupocBot]
    omega
  have hcert := atom_search_f_top k (Nat.log2 k + 14)
    (.plays .opp (.bot (DupocBot k)) .C) .C .D (.bot DefectBot) hneg
  exact Pf.atom (atom_monotone _ _ _ (by omega) hcert)

/-- Leg 1 (staggered): `□_{2k+64} φD' → φP'` — `PrudentBot (2k+64)` reads its stacked
    searches against `.bot (DupocBot k)`; the inner prudence is `prudence_botdupoc`. -/
theorem prudent_botdupoc_legPD (k : Nat) :
    Pf (30 * Nat.log2 k + 700)
      (.impl (.box (2*k+64) (.plays (.bot (DupocBot k)) (PrudentBot (2*k+64)) .C))
             (.plays (PrudentBot (2*k+64)) (.bot (DupocBot k)) .C)) := by
  have hlk := log2_le_self k
  have hlg := log2_stagger_le k
  refine Pf.searchThenSearch_t (2*k+64) (2*k+64) (k + Nat.log2 k + 17)
    (.plays .opp .self .C) (.plays .opp (.bot DefectBot) .D)
    .C .D (.const .D) (PrudentBot (2*k+64)) (.bot (DupocBot k)) rfl
    (by simpa [Formula.subst, Prog.subst] using prudence_botdupoc k) (by omega) ?_
  simp only [numCost, Formula.subst, Prog.subst, Formula.size, Prog.size, DupocBot, PrudentBot,
    DefectBot, c_guard]
  omega

/-- Leg 2 (staggered): `□_k φP' → φD'` — `.bot (DupocBot k)`'s `botSearchStep` leaf. -/
theorem prudent_botdupoc_legDP (k : Nat) :
    Pf (30 * Nat.log2 k + 700)
      (.impl (.box k (.plays (PrudentBot (2*k+64)) (.bot (DupocBot k)) .C))
             (.plays (.bot (DupocBot k)) (PrudentBot (2*k+64)) .C)) := by
  have hlg := log2_stagger_le k
  refine Pf.botSearchStep k (.plays .opp .self .C) .C .D (.bot (DupocBot k)) (PrudentBot (2*k+64)) rfl ?_
  simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot, PrudentBot, DefectBot]
  omega

/-- `.bot (DupocBot k)`'s staggered-opponent play lemmas (generic in the opponent). -/
theorem bot_dupoc_D_vs_any (k fuel : Nat) (q : Prog)
    (hk : proofSearch k (.plays q (.bot (DupocBot k)) .C) = false) :
    play (fuel + 3) (.bot (DupocBot k)) q = some .D := by
  show eval (fuel + 3) (.bot (DupocBot k)) q (.bot (DupocBot k)) = some .D
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

theorem ps_k_of_play_botdupoc_any (k n : Nat) (q : Prog)
    (h : play n (.bot (DupocBot k)) q = some .C) :
    proofSearch k (.plays q (.bot (DupocBot k)) .C) = true := by
  cases hps : proofSearch k (.plays q (.bot (DupocBot k)) .C) with
  | true => rfl
  | false =>
    exfalso
    have hD : play (n + 3) (.bot (DupocBot k)) q = some .D := bot_dupoc_D_vs_any k n q hps
    have hC : play (n + 3) (.bot (DupocBot k)) q = some .C := by
      unfold play at h ⊢; exact eval_mono_le h (n + 3) (by omega)
    rw [hC] at hD; cases hD

/-- **JustBot k vs PrudentBot (2k+64) → (C, C)** for all large enough `k` — cooperation
    at a budget STAGGER. Not the matrix cell (`outcome_JustBot_vs_PrudentBot = (D, D)`
    below is the shared-budget value); the `_staggered` companion. -/
theorem outcome_JustBot_vs_PrudentBot_staggered :
    OutcomeSpec .eventual 3
      JustBot (fun k => PrudentBot (2*k+64)) (some (.C, .C)) := by
  obtain ⟨KL, hKL⟩ := linear_log2_add_le 1 3
  have hsD : ∀ k, (Formula.plays (.bot (DupocBot k)) (PrudentBot (2*k+64)) .C).size
      ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    have hlg := log2_stagger_le k
    simp only [numCost, Formula.size, Prog.size, PrudentBot, DupocBot, DefectBot]
    omega
  have hsP : ∀ k, (Formula.plays (PrudentBot (2*k+64)) (.bot (DupocBot k)) .C).size
      ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    have hlg := log2_stagger_le k
    simp only [numCost, Formula.size, Prog.size, PrudentBot, DupocBot, DefectBot]
    omega
  have hpb : ∀ k, 30 * Nat.log2 k + 700 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := mutual_pblt_engine_staggered
    (fun k => Formula.plays (.bot (DupocBot k)) (PrudentBot (2*k+64)) .C)
    (fun k => Formula.plays (PrudentBot (2*k+64)) (.bot (DupocBot k)) .C)
    (fun k => 2*k+64)
    (fun k => 30 * Nat.log2 k + 700) (fun k => 30 * Nat.log2 k + 700) 0
    (fun k => by show k ≤ 2*k+64; omega) log2_stagger_le hsD hsP hpb hpb
    (fun k _ => prudent_botdupoc_legPD k)
    (fun k _ => prudent_botdupoc_legDP k)
  refine ⟨max k₂ KL, fun k hk fuel => outcome_at_of_ex ?_ ?_ fuel⟩
  -- The old existential-fuel argument, verbatim: some fuel determines the outcome…
  · have hk2 : k > k₂ := lt_of_le_of_lt (le_max_left _ _) hk
    have hKLk : Nat.log2 k + 3 ≤ k := by
      have := hKL k (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk))
      omega
    have hlk := log2_le_self k
    obtain ⟨m, hm⟩ := hk₂ k hk2
    obtain ⟨n, hplayD⟩ := Pf_sound m _ hm
    -- botDupoc's guard fired: JustBot's own guard about PrudentBot holds at k
    have hA_ps : proofSearch k
        (.plays (PrudentBot (2*k+64)) (.bot (DupocBot k)) .C) = true :=
      ps_k_of_play_botdupoc_any k n (PrudentBot (2*k+64)) hplayD
    -- JustBot cooperates (its guard is exactly hA_ps)
    have hA : play 4 (JustBot k) (PrudentBot (2*k+64)) = some .C := by
      refine JustBot_eval_step k 2 (PrudentBot (2*k+64)) .C ?_
      simpa using hA_ps
    -- PrudentBot's outer guard: JustBot's cooperative play, certified through its fired search
    have houter : proofSearch (2*k+64)
        (.plays (JustBot k) (PrudentBot (2*k+64)) .C) = true := by
      refine (proofSearch_spec _ _).2 (Pf.atom
        (⟨PlaysProof.search_t ((proofSearch_spec _ _).1 hA_ps) PlaysProof.const, ?_⟩ :
          AtomProvable (2*k+64) (.plays (JustBot k) (PrudentBot (2*k+64)) .C)))
      show c_leaf + c_guard k + c_node ≤ 2*k+64
      simp only [numCost, c_leaf, c_guard, c_node]
      omega
    -- PrudentBot's prudence about JustBot: the floored certificate fits its bigger budget
    have hprud : proofSearch (2*k+64) (.plays (JustBot k) (.bot DefectBot) .D) = true := by
      refine (proofSearch_spec _ _).2 (Pf_mono (justbot_prudence k) ?_)
      omega
    have hB : play 4 (PrudentBot (2*k+64)) (JustBot k) = some .C := by
      simpa using prudent_eval_both_true (2*k+64) 1 (JustBot k) houter hprud
    exact ⟨4, outcome_of_plays _ _ _ _ _ hA hB⟩
  -- …and the match is determined at fuel 3 whatever the oracle says, so
  -- determinism (`play_unique`) pins the value there and monotonicity does the rest.
  · refine outcome_total_of_plays (play_search_const_total _ _ _ _ _ 1) ?_
    unfold play PrudentBot
    simp only [eval]
    split <;> (try split) <;> exact ⟨_, rfl⟩
/-! ### The SAME-budget regime — the tau layer's value, proven in base (2026-08-25)

The strict `outcome_{L}_vs_{R}` theorem above is stated at a budget STAGGER: that is
what buys the cooperative cell, by paying a partner's `search_f` floor. At one shared
budget the floor is unpayable and the honest outcome is what the tau lift (`tauZoo k`,
one `k` for everyone) reads. These `_samek` theorems certify that value in base, so the
tau/base divergence on this pair is a matter of budget regime alone — both regimes are
theorems. (The `_samek` suffix keeps them out of the strict matrix scan.) -/

/-- The frozen `.bot (DupocBot k)`'s D on the defector is its else-play — floor-priced. -/
theorem proofSearch_false_botDupoc_D_vs_bot_DefectBot (k : Nat) :
    proofSearch k (.plays (.bot (DupocBot k)) (.bot DefectBot) .D) = false := by
  cases h : proofSearch k (.plays (.bot (DupocBot k)) (.bot DefectBot) .D) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => no_provable_botSearcherElse_tail k k (.plays .opp .self .C) .C .D (.const .D)
          (by decide) le_rfl (.bot DefectBot) k _ hp le_rfl (by simp [DupocBot]))
  | false => rfl

/-- PrudentBot defects on JustBot's frozen third party at the same budget. -/
theorem PrudentBot_plays_D_against_bot_DupocBot (k fuel : Nat) :
    play (fuel + 3) (PrudentBot k) (.bot (DupocBot k)) = some .D := by
  cases h1 : proofSearch k (.plays (.bot (DupocBot k)) (PrudentBot k) .C) with
  | false =>
      simpa [Nat.add_assoc] using
        PrudentBot_plays_D_of_search_false k (fuel + 1) (.bot (DupocBot k)) h1
  | true =>
      exact prudent_eval_inner_false k fuel (.bot (DupocBot k)) h1
        (proofSearch_false_botDupoc_D_vs_bot_DefectBot k)

theorem proofSearch_false_PrudentBot_C_vs_bot_DupocBot (k : Nat) :
    proofSearch k (.plays (PrudentBot k) (.bot (DupocBot k)) .C) = false := by
  cases h : proofSearch k (.plays (PrudentBot k) (.bot (DupocBot k)) .C) with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨n, hn⟩ := proofSearch_sound _ _ h
      have hD := PrudentBot_plays_D_against_bot_DupocBot k n
      have hC : play (n + 3) (PrudentBot k) (.bot (DupocBot k)) = some .C := by
        unfold play at hn ⊢; exact eval_mono_le hn (n + 3) (by omega)
      rw [hC] at hD; cases hD

theorem JustBot_plays_D_against_PrudentBot_samek (k fuel : Nat) :
    play (fuel + 2) (JustBot k) (PrudentBot k) = some .D :=
  JustBot_eval_step k fuel (PrudentBot k) .D
    (by rw [proofSearch_false_PrudentBot_C_vs_bot_DupocBot]; rfl)

theorem proofSearch_false_JustBot_C_vs_PrudentBot (k : Nat) :
    proofSearch k (.plays (JustBot k) (PrudentBot k) .C) = false := by
  cases h : proofSearch k (.plays (JustBot k) (PrudentBot k) .C) with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨n, hn⟩ := proofSearch_sound _ _ h
      have hD := JustBot_plays_D_against_PrudentBot_samek k n
      have hC : play (n + 2) (JustBot k) (PrudentBot k) = some .C := by
        unfold play at hn ⊢; exact eval_mono_le hn (n + 2) (by omega)
      rw [hC] at hD; cases hD

theorem PrudentBot_plays_D_against_JustBot_samek (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) (JustBot k) = some .D :=
  PrudentBot_plays_D_of_search_false k fuel (JustBot k)
    (proofSearch_false_JustBot_C_vs_PrudentBot k)

/-- **THE CELL — JustBot vs PrudentBot at ONE shared budget = (D, D)**. Cooperation needs
    `PrudentBot (2k+64)` — `outcome_JustBot_vs_PrudentBot_staggered`. (Until 2026-08-27 the
    staggered result filled the cell and this was `_samek`.) -/
@[outcome]
theorem outcome_JustBot_vs_PrudentBot :
    OutcomeSpec .universal 2 JustBot PrudentBot (some (.D, .D)) := fun k fuel =>
  outcome_of_plays _ _ _ _ _ (JustBot_plays_D_against_PrudentBot_samek k fuel)
    (PrudentBot_plays_D_against_JustBot_samek k fuel)

end PD.Theorems
