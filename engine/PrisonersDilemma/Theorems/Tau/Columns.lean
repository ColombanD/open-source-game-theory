import PrisonersDilemma.Theorems.Tau.TauDupoc.Helpers
import PrisonersDilemma.Theorems.Tau.TauEBot.Helpers

/-!
# Theorems/Tau/Columns — the three consulted columns (the bit API)

Cross-bot by type: a column asks one question of EVERY zoo member ("does T's
instance, seeing X, provably cooperate?"), so these aggregate the per-bot rows —
which is why this file imports the bot Helpers rather than the other way round.
The zoo's specs consult exactly three columns (δ_C, δ_D, δ_L) plus the behavioral
read of δ_C; each arm is a shape lemma from the shared Helpers, bridged by defeq
(the `Zoo.lean` peel equations pin the shapes). Adding a bot = one arm per column
here, plus its own Helpers if it brings new mathematics.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## The three consulted columns (the public bit API) -/

/-- δ_C column bits. Zero rows: Defect (refutable) and EBot (it EXPLOITS a
    cooperator). -/
def coopColBit : Tmpl → Bool
  | .defect => false
  | .ebot   => false
  | _       => true

theorem ps_probe_inst_coop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) :
    ∀ T, proofSearch k (probe (inst (zoo6 k) T .coop)) = coopColBit T
  | .coop   => ps_probe_constC hk
  | .defect => ps_probe_constD k
  | .tftSim => ps_simCopy_constC h6
  | .tftPf  => ps_searchProbe_constC hk hkk
  | .dupoc  => ps_searchProbe_constC hk hkk
  | .ebot   => ps_cascade_constC_false hk k

/-- δ_D column bits. Only the unconditional cooperator is exploitable. -/
def defectColBit : Tmpl → Bool
  | .coop => true
  | _     => false

theorem ps_probe_inst_defect {k : Nat} (hk : 2 ≤ k) :
    ∀ T, proofSearch k (probe (inst (zoo6 k) T .defect)) = defectColBit T
  | .coop   => ps_probe_constC hk
  | .defect => ps_probe_constD k
  | .tftSim => ps_simCopy_constD k
  | .tftPf  => ps_searchProbe_constD k k
  | .dupoc  => ps_searchProbe_constD k k
  | .ebot   => ps_cascade_constD_false k k

/-- δ_L column bits. Zero rows: Defect, and EBot — THE FLOOR. The diagonal is the
    Löb quine, supplied as a hypothesis (it holds past a THRESHOLD, not at a fixed
    budget bound — `ps_probe_inst_quine`). -/
def dupocColBit : Tmpl → Bool
  | .defect => false
  | .ebot   => false
  | _       => true

theorem ps_probe_inst_dupoc {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (zoo6 k) .dupoc .dupoc)) = true) :
    ∀ T, proofSearch k (probe (inst (zoo6 k) T .dupoc)) = dupocColBit T
  | .coop   => ps_probe_constC hk
  | .defect => ps_probe_constD k
  | .tftSim => (proofSearch_spec _ _).2 (pf_simCopy_searchProbeC hk hk7)
  | .tftPf  => (proofSearch_spec _ _).2 (pf_searchProbe_searchProbeC hk hkk hkk)
  | .dupoc  => hquine
  | .ebot   => ps_probe_inst_ebot_dupoc_false (le_refl k)

/-! ## The behavioral δ_C column — true plays, for `run`-mode consumers -/

/-- What T's instance seeing the cooperator TRULY plays (floor-blind). -/
def coopColPlay : Tmpl → Action
  | .defect => .D
  | .ebot   => .D
  | _       => .C

theorem inst_coop_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (zoo6 k) T .coop)) (.bot (inst (zoo6 k) T .coop))
              (inst (zoo6 k) T .coop) = some (coopColPlay T)
  | .coop   => ⟨1, rfl⟩
  | .defect => ⟨1, rfl⟩
  | .tftSim => entry_C_of_interp (Pf_sound _ _ (pf_simCopy_constC h6))
  | .tftPf  => entry_C_of_interp (Pf_sound _ _ (pf_searchProbe_constC hk hkk))
  | .dupoc  => entry_C_of_interp (Pf_sound _ _ (pf_searchProbe_constC hk hkk))
  | .ebot   => by
      have hb : proofSearch k (probe (.const .C)) = true := ps_probe_constC hk
      have hplay : eval 3
          (.bot (.search k (probe (.const .C)) (.const .D)
            (.search k (probe (.const .C)) (.const .C) (.const .D))))
          (.bot (.search k (probe (.const .C)) (.const .D)
            (.search k (probe (.const .C)) (.const .C) (.const .D))))
          (.search k (probe (.const .C)) (.const .D)
            (.search k (probe (.const .C)) (.const .C) (.const .D)))
          = some Action.D := by
        rw [eval, probe_subst, hb]; rfl
      exact ⟨3, hplay⟩

end PD.Tau
