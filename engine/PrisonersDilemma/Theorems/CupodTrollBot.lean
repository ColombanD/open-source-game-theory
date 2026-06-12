import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot


import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems


--- Opp = CupodBot ---

/-- The structural-identity guard of CupodTrollBot **fires** when the opponent is
    literally `CupodBot k` and the budget `k` covers the guard formula's size.
    The witness is `eqRefl`, whose `Derivation.size` is exactly the conclusion's
    `Formula.size`. The guard's RHS is frozen by `subst`, so it stays the literal
    `CupodBot k` and `eqRefl` matches the bare opponent. -/
theorem proofSearch_true_for_CupodBot (k : Nat)
    (hk : (Formula.eq (CupodBot k) (CupodBot k)).size ≤ k) :
    proofSearch k (.eq (CupodBot k) (CupodBot k)) = true :=
  (proofSearch_spec _ _).2
    (Provable.struct ⟨Derivation.eqRefl (CupodBot k), hk⟩)

/-- CupodTrollBot defects against a literal `CupodBot k`: the guard fires, so the
    bot takes its `.const .D` branch. -/
theorem CupodTrollBot_defects_vs_CupodBot (k fuel : Nat)
    (hk : (Formula.eq (CupodBot k) (CupodBot k)).size ≤ k) :
    play (fuel + 2) (CupodTrollBot k) (CupodBot k) = some .D := by
  have hg := proofSearch_true_for_CupodBot k hk
  show eval (fuel + 2) (CupodTrollBot k) (CupodBot k) (CupodTrollBot k) = some .D
  unfold CupodTrollBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- CupodBot defects against CupodTrollBot. Its `.search` guard is
    `□(CupodTrollBot plays D vs me)`; since CupodTrollBot *does* defect (`hA`), the
    guard's atom is provable, so once the budget `k` covers it the guard fires and
    CupodBot takes its `.const .D` branch. The atom budget `atom_cost (fuel + 2)`
    must fit in `k` (`hbudget`). -/
theorem CupodBot_defects_vs_CupodTrollBot (k fuel : Nat)
    (hk : (Formula.eq (CupodBot k) (CupodBot k)).size ≤ k)
    (hbudget : atom_cost (fuel + 2) ≤ k) :
    play (fuel + 2) (CupodBot k) (CupodTrollBot k) = some .D := by
  -- CupodTrollBot defects against `CupodBot k` (direction A).
  have hA : play (fuel + 2) (CupodTrollBot k) (CupodBot k) = some .D :=
    CupodTrollBot_defects_vs_CupodBot k fuel hk
  -- Lift that play to a proof-search fact, then up to CupodBot's budget `k`.
  have hatom : proofSearch (atom_cost (fuel + 2))
      (.plays (CupodTrollBot k) (CupodBot k) .D) = true :=
    (proofSearch_spec _ _).2
      (Provable.atom (atom_complete (CupodTrollBot k) (CupodBot k) .D (fuel + 2) hA))
  have hg : proofSearch k (.plays (CupodTrollBot k) (CupodBot k) .D) = true :=
    proofSearch_monotone _ _ _ hbudget hatom
  -- CupodBot's `.search` guard `subst`s to exactly `hg`'s formula (`self` = `me`).
  show eval (fuel + 2) (CupodBot k) (CupodTrollBot k) (CupodBot k) = some .D
  unfold CupodBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

theorem outcome_CupodTrollBot_vs_CupodBot (k fuel : Nat)
    (hk : (Formula.eq (CupodBot k) (CupodBot k)).size ≤ k)
    (hbudget : atom_cost (fuel + 2) ≤ k) :
    outcome (fuel + 2) (CupodTrollBot k) (CupodBot k) = some (.D, .D) := by
  -- Direction A: CupodTrollBot recognises CupodBot and defects.
  have hA : play (fuel + 2) (CupodTrollBot k) (CupodBot k) = some .D :=
    CupodTrollBot_defects_vs_CupodBot k fuel hk
  -- Direction B: CupodBot's own guard is satisfied (CupodTrollBot defects), so it defects too.
  have hB : play (fuel + 2) (CupodBot k) (CupodTrollBot k) = some .D :=
    CupodBot_defects_vs_CupodTrollBot k fuel hk hbudget
  exact outcome_of_plays _ _ _ _ _ hA hB


--- Opponent ≠ CupodBot ---
--- Preliminary Lemmas ---

/-- CupodTrollBot's structural-identity guard fails whenever the opponent is not
    literally `CupodBot k`. By soundness, `proofSearch k (.eq opponent …)` can
    only be `true` if `.eq`'s interpretation `opponent = CupodBot k` holds; the
    hypothesis rules that out, so the guard is `false`. -/
theorem proofSearch_false_for_not_CupodBot (k : Nat) (opponent : Prog)
    (h : opponent ≠ CupodBot k) :
    proofSearch k (.eq opponent (CupodBot k)) = false := by
  cases hps : proofSearch k (.eq opponent (CupodBot k)) with
  | true  => exact absurd (proofSearch_sound _ _ hps) h
  | false => rfl

/-- If the opponent is not literally `CupodBot`, then CupodTrollBot cooperates.
    The `.search` guard tests structural identity against `CupodBot k`; since the
    opponent differs, the guard fails and the bot falls through to its `.const .C`
    branch. Needs `+ 2` fuel: one step for `.search`, one for the constant. -/
theorem CupodTrollBot_cooperates_if_opp_not_CupodBot (k fuel : Nat) (opponent : Prog)
    (h : opponent ≠ CupodBot k) :
    play (fuel + 2) (CupodTrollBot k) opponent = some .C := by
  have hg := proofSearch_false_for_not_CupodBot k opponent h
  show eval (fuel + 2) (CupodTrollBot k) opponent (CupodTrollBot k) = some .C
  unfold CupodTrollBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- CupodTrollBot cooperates against any `.bot z` probe: `.bot z` is never a
    `.search` node, so it differs from `CupodBot k` and the identity guard fails.
    This is the workhorse for the simulation-probing opponents below. -/
theorem CupodTrollBot_cooperates_against_bot (k fuel : Nat) (z : Prog) :
    play (fuel + 2) (CupodTrollBot k) (.bot z) = some .C :=
  CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (.bot z) (by simp [CupodBot])


--- CupodTrollBot ---

theorem outcome_CupodTrollBot_vs_CupodTrollBot (k fuel : Nat) :
    outcome (fuel + 3) (CupodTrollBot k) (CupodTrollBot k) = some (.C, .C) := by
  -- CupodTrollBot cooperates against itself
  have hA : play (fuel + 3) (CupodTrollBot k) (CupodTrollBot k) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (CupodTrollBot k)
      (by simp [CupodTrollBot, CupodBot])
  simp [outcome, hA]


--- CooperateBot ---

theorem outcome_CupodTrollBot_vs_CooperateBot (k fuel : Nat) :
    outcome (fuel + 2) (CupodTrollBot k) CooperateBot = some (.C, .C) := by
  -- CupodTrollBot cooperates against `CooperateBot` (direction A).
  have hA : play (fuel + 2) (CupodTrollBot k) CooperateBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (CooperateBot)
      (by simp [CooperateBot, CupodBot])
  -- `CooperateBot` cooperates against CupodTrollBot (direction B).
  have hB : play (fuel + 2) CooperateBot (CupodTrollBot k) = some .C := rfl
  exact outcome_of_plays _ _ _ _ _ hA hB


--- DefectBot ---

theorem outcome_CupodTrollBot_vs_DefectBot (k fuel : Nat) :
    outcome (fuel + 2) (CupodTrollBot k) DefectBot = some (.C, .D) := by
  -- CupodTrollBot cooperates against `DefectBot` (direction A).
  have hA : play (fuel + 2) (CupodTrollBot k) DefectBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (DefectBot)
      (by simp [DefectBot, CupodBot])
  -- `DefectBot` defects against CupodTrollBot (direction B).
  have hB : play (fuel + 2) DefectBot (CupodTrollBot k) = some .D := rfl
  exact outcome_of_plays _ _ _ _ _ hA hB


--- TitForTatBot ---

/-- TitForTat cooperates with CupodTrollBot: its `.sim .opp (.bot CooperateBot)`
    probe sees CupodTrollBot cooperate, so the `ite` selects the cooperate branch. -/
theorem TitForTatBot_plays_C_against_CupodTrollBot (k fuel : Nat) :
    play (fuel + 4) TitForTatBot (CupodTrollBot k) = some .C := by
  have hProbe : play (fuel + 2) (CupodTrollBot k) (.bot CooperateBot) = some .C :=
    CupodTrollBot_cooperates_against_bot k fuel CooperateBot
  have hGuard :
      eval (fuel + 3) TitForTatBot (CupodTrollBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (CupodTrollBot k) CooperateBot Action.C hProbe)
  have hPlay := play_ite_from_guard
    fuel 3 TitForTatBot (CupodTrollBot k) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem outcome_CupodTrollBot_vs_TitForTatBot (k fuel : Nat) :
    outcome (fuel + 4) (CupodTrollBot k) TitForTatBot = some (.C, .C) := by
  -- CupodTrollBot cooperates against `TitForTatBot` (direction A).
  have hA : play (fuel + 4) (CupodTrollBot k) TitForTatBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k (fuel + 2) (TitForTatBot)
      (by simp [TitForTatBot, CupodBot])
  -- `TitForTatBot` cooperates against CupodTrollBot (direction B).
  have hB : play (fuel + 4) TitForTatBot (CupodTrollBot k) = some .C :=
    TitForTatBot_plays_C_against_CupodTrollBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB


--- DBot ---

/-- DBot defects against CupodTrollBot: its `.sim .opp (.bot DefectBot)` probe sees
    CupodTrollBot cooperate, so the `ite` selects DBot's defect branch. -/
theorem DBot_plays_D_against_CupodTrollBot (k fuel : Nat) :
    play (fuel + 4) DBot (CupodTrollBot k) = some .D := by
  have hProbe : play (fuel + 2) (CupodTrollBot k) (.bot DefectBot) = some .C :=
    CupodTrollBot_cooperates_against_bot k fuel DefectBot
  have hGuard :
      eval (fuel + 3) DBot (CupodTrollBot k) (.sim .opp (.bot DefectBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) DBot (CupodTrollBot k) DefectBot Action.C hProbe)
  have hPlay := play_ite_from_guard
    fuel 3 DBot (CupodTrollBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C)
    Action.C Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem outcome_CupodTrollBot_vs_DBot (k fuel : Nat) :
    outcome (fuel + 4) (CupodTrollBot k) DBot = some (.C, .D) := by
  -- CupodTrollBot cooperates against `DBot` (direction A).
  have hA : play (fuel + 4) (CupodTrollBot k) DBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k (fuel + 2) DBot
      (by simp [DBot, CupodBot])
  -- `DBot` defects against CupodTrollBot (direction B).
  have hB : play (fuel + 4) DBot (CupodTrollBot k) = some .D :=
    DBot_plays_D_against_CupodTrollBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB


--- OBot ---

/-- OBot cooperates with CupodTrollBot: its first probe (`.bot CooperateBot`) sees
    CupodTrollBot cooperate, so it descends into the inner `ite`; that probe
    (`.bot DefectBot`) *also* sees CupodTrollBot cooperate, landing on the inner
    cooperate branch. So OBot cooperates — outcome is mutual cooperation, not `(.C, .D)`. -/
theorem OBot_plays_C_against_CupodTrollBot (k fuel : Nat) :
    play (fuel + 5) OBot (CupodTrollBot k) = some .C := by
  have hGuard1 :
      eval (fuel + 4) OBot (CupodTrollBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    have hProbe : play (fuel + 3) (CupodTrollBot k) (.bot CooperateBot) = some .C := by
      simpa [Nat.add_assoc] using CupodTrollBot_cooperates_against_bot k (fuel + 1) CooperateBot
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) OBot (CupodTrollBot k) CooperateBot Action.C hProbe)
  have hGuard2 :
      eval (fuel + 3) OBot (CupodTrollBot k) (.sim .opp (.bot DefectBot)) = some .C := by
    have hProbe : play (fuel + 2) (CupodTrollBot k) (.bot DefectBot) = some .C :=
      CupodTrollBot_cooperates_against_bot k fuel DefectBot
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) OBot (CupodTrollBot k) DefectBot Action.C hProbe)
  have hPlay := play_ite_from_guard
    fuel 4 OBot (CupodTrollBot k) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard1
  have hInner :
      eval (fuel + 4) OBot (CupodTrollBot k)
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D)) =
          some .C := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) OBot (CupodTrollBot k)
        (.sim .opp (.bot DefectBot)) (.const Action.C) (.const Action.D)
        Action.C Action.C hGuard2)
  simpa [hInner] using hPlay

theorem outcome_CupodTrollBot_vs_OBot (k fuel : Nat) :
    outcome (fuel + 5) (CupodTrollBot k) OBot = some (.C, .C) := by
  -- CupodTrollBot cooperates against `OBot` (direction A).
  have hA : play (fuel + 5) (CupodTrollBot k) OBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k (fuel + 3) OBot
      (by simp [OBot, CupodBot])
  -- `OBot` cooperates with CupodTrollBot (direction B).
  have hB : play (fuel + 5) OBot (CupodTrollBot k) = some .C :=
    OBot_plays_C_against_CupodTrollBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB


--- MirrorBot ---

/-- MirrorBot mirrors CupodTrollBot: `.sim .opp .self` reduces MirrorBot's play to
    `play _ (CupodTrollBot k) MirrorBot`, which cooperates (MirrorBot ≠ CupodBot k).
    So MirrorBot cooperates — the outcome is mutual cooperation, not `(.C, .D)`. -/
theorem MirrorBot_plays_C_against_CupodTrollBot (k fuel : Nat) :
    play (fuel + 3) MirrorBot (CupodTrollBot k) = some .C := by
  have hCTB : play (fuel + 2) (CupodTrollBot k) MirrorBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel MirrorBot (by simp [MirrorBot, CupodBot])
  simpa [play, eval, Prog.subst, MirrorBot] using hCTB

theorem outcome_CupodTrollBot_vs_MirrorBot (k fuel : Nat) :
    outcome (fuel + 3) (CupodTrollBot k) MirrorBot = some (.C, .C) := by
  -- CupodTrollBot cooperates against `MirrorBot` (direction A).
  have hA : play (fuel + 3) (CupodTrollBot k) MirrorBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k (fuel + 1) MirrorBot
      (by simp [MirrorBot, CupodBot])
  -- `MirrorBot` mirrors CupodTrollBot's cooperation (direction B).
  have hB : play (fuel + 3) MirrorBot (CupodTrollBot k) = some .C :=
    MirrorBot_plays_C_against_CupodTrollBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB


--- EBot ---

/-- EBot defects against CupodTrollBot: its first probe `.sim .opp (.bot DefectBot)`
    sees CupodTrollBot cooperate, so EBot's outer `ite` selects the defect branch
    (`.const .D`) immediately — the nested probes are never reached. -/
theorem EBot_plays_D_against_CupodTrollBot (k fuel : Nat) :
    play (fuel + 4) EBot (CupodTrollBot k) = some .D := by
  have hProbe : play (fuel + 2) (CupodTrollBot k) (.bot DefectBot) = some .C :=
    CupodTrollBot_cooperates_against_bot k fuel DefectBot
  have hGuard :
      eval (fuel + 3) EBot (CupodTrollBot k) (.sim .opp (.bot DefectBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) EBot (CupodTrollBot k) DefectBot Action.C hProbe)
  have hPlay := play_ite_from_guard
    fuel 3 EBot (CupodTrollBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D)
    (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
      (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
    Action.C Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem outcome_CupodTrollBot_vs_EBot (k fuel : Nat) :
    outcome (fuel + 4) (CupodTrollBot k) EBot = some (.C, .D) := by
  -- CupodTrollBot cooperates against `EBot` (direction A).
  have hA : play (fuel + 4) (CupodTrollBot k) EBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k (fuel + 2) EBot
      (by simp [EBot, CupodBot])
  -- `EBot` defects against CupodTrollBot (direction B).
  have hB : play (fuel + 4) EBot (CupodTrollBot k) = some .D :=
    EBot_plays_D_against_CupodTrollBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB


--- DupocBot ---

/-- DupocBot cooperates with CupodTrollBot. Its `.search` guard is
    `□(CupodTrollBot plays C vs me)`; since CupodTrollBot *does* cooperate, the
    guard's atom is provable, so once the budget `k` covers it (`hbudget`) the
    guard fires and DupocBot takes its `.const .C` branch. So the outcome is mutual
    cooperation, not `(.C, .D)`. -/
theorem DupocBot_plays_C_against_CupodTrollBot (k fuel : Nat)
    (hbudget : atom_cost (fuel + 2) ≤ k) :
    play (fuel + 2) (DupocBot k) (CupodTrollBot k) = some .C := by
  -- CupodTrollBot cooperates against `DupocBot k` (the guard's content).
  have hC : play (fuel + 2) (CupodTrollBot k) (DupocBot k) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (DupocBot k) (by simp [DupocBot, CupodBot])
  -- Lift that play to a proof-search fact, then up to DupocBot's budget `k`.
  have hatom : proofSearch (atom_cost (fuel + 2))
      (.plays (CupodTrollBot k) (DupocBot k) .C) = true :=
    (proofSearch_spec _ _).2
      (Provable.atom (atom_complete (CupodTrollBot k) (DupocBot k) .C (fuel + 2) hC))
  have hg : proofSearch k (.plays (CupodTrollBot k) (DupocBot k) .C) = true :=
    proofSearch_monotone _ _ _ hbudget hatom
  -- DupocBot's `.search` guard `subst`s to exactly `hg`'s formula (`self` = `me`).
  show eval (fuel + 2) (DupocBot k) (CupodTrollBot k) (DupocBot k) = some .C
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

theorem outcome_CupodTrollBot_vs_DupocBot (k fuel : Nat)
    (hbudget : atom_cost (fuel + 2) ≤ k) :
    outcome (fuel + 2) (CupodTrollBot k) (DupocBot k) = some (.C, .C) := by
  -- CupodTrollBot cooperates against `DupocBot` (direction A).
  have hA : play (fuel + 2) (CupodTrollBot k) (DupocBot k) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (DupocBot k)
      (by simp [DupocBot, CupodBot])
  -- `DupocBot` cooperates with CupodTrollBot once its guard fires (direction B).
  have hB : play (fuel + 2) (DupocBot k) (CupodTrollBot k) = some .C :=
    DupocBot_plays_C_against_CupodTrollBot k fuel hbudget
  exact outcome_of_plays _ _ _ _ _ hA hB


end PD.Theorems
