import PrisonersDilemma.Tau.PeelLemmas
import PrisonersDilemma.Tau.Certs

/-!
# Tau/Phases — the α-regime play theorems

The headline, per non-constant tau player: past a budget threshold, the player's
play against EVERY opponent (tau players are `.opp`-free, hence extensionally
constant) is decided by where θ sits relative to its PROVABLE cooperation masses.

* TauDupoc, TauTFTPf, TauTFTSim cooperate exactly when `θ ≤ wC + wTs + wTp + wL`.
  TauDupoc's `wE` bit is 0 DESPITE `E(δ_L)` really cooperating — the cooperation is
  floor-priced (`ps_probe_eOfSearch_false`), the tau image of base
  `outcome_DupocBot_vs_EBot = (D, C)`.
* TauEBot's cooperation region is a WINDOW, `wC < θ ≤ wC + wTs + wTp + wL`: at
  `θ ≤ wC` its exploit stage fires on the Coop mass (defect), above the window the
  reciprocity mass falls short (defect). A non-monotone α-profile — the structural
  Def-3/Def-4 separation.

What separates the cooperators is the BUDGET at which their boundary becomes
available: TauTFTSim needs only shallow fuel + the trivial Coop bit, TauTFTPf and
TauEBot need shallow proof budgets, and TauDupoc needs the **Löb threshold** for its
`wL` bit (`ps_probe_quine`). The prover/behavioral split is a budget-phase gap, not
an α-gap.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## Mass computations -/

/-- TauDupoc's fired mass at an adequate budget: every bit but Defect AND EBot
    fires — `E(δ_L)` cooperates, but floor-priced, so its bit is honestly 0. -/
theorem dupocSig_mass (k wC wD wTs wTp wL wE : Nat) (me opponent : Prog)
    (hk2 : 2 ≤ k) (hk7 : c_guard k + 7 ≤ k) (hk3 : c_guard k + 3 ≤ k)
    (hL : proofSearch k (probe (TauDupocδ k)) = true) :
    (dupocSig k wC wD wTs wTp wL wE).massWhere
        (fun ψ => proofSearch k (ψ.subst me opponent))
      = wC + wTs + wTp + wL := by
  simp only [dupocSig, GuardList.massWhere, probe_subst,
    ps_probe_coop hk2, ps_probe_defect, ps_probe_simOfSearch hk2 hk7,
    ps_probe_searchOfSearch hk2 hk3, ps_probe_eOfSearch_false (Nat.le_refl k), hL]
  simp
  omega

/-- TauTFTPf's fired mass at an adequate (shallow) budget: same shape, no Löb. -/
theorem tftPfSig_mass (k wC wD wTs wTp wL wE : Nat) (me opponent : Prog)
    (hk2 : 2 ≤ k) (hk6 : 6 ≤ k) (hk3 : c_guard k + 3 ≤ k) :
    (tftPfSig k wC wD wTs wTp wL wE).massWhere
        (fun ψ => proofSearch k (ψ.subst me opponent))
      = wC + wTs + wTp + wL := by
  simp only [tftPfSig, GuardList.massWhere, probe_subst,
    ps_probe_coop hk2, ps_probe_defect, ps_probe_simOfCoop hk6,
    ps_probe_searchOfCoop hk2 hk3, ps_probe_eOfCoop_false hk2]
  simp
  omega

/-! ## TauDupoc -/

/-- **TauDupoc α-phase theorem** (Löb-gated). The boundary EXCLUDES `wE`: TauDupoc
    cannot certify TauEBot's (real) cooperation within its own budget. -/
theorem tauDupoc_phase :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE (opponent : Prog),
      (θ ≤ wC + wTs + wTp + wL →
        ∃ N, play N (TauDupoc k θ wC wD wTs wTp wL wE) opponent = some .C)
      ∧ (wC + wTs + wTp + wL < θ →
        ∃ N, play N (TauDupoc k θ wC wD wTs wTp wL wE) opponent = some .D) := by
  obtain ⟨kL, hkL⟩ := ps_probe_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  refine ⟨max kL kA, fun k hk θ wC wD wTs wTp wL wE opponent => ?_⟩
  have hL := hkL k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hkA' : 1 * Nat.log2 k + 8 ≤ k :=
    hkA k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  have hk2 : 2 ≤ k := by omega
  have hk7 : c_guard k + 7 ≤ k := by simp only [c_guard, numCost]; omega
  have hk3 : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hmass := dupocSig_mass k wC wD wTs wTp wL wE
    (.tsearch k (dupocSig k wC wD wTs wTp wL wE) θ (.const .C) (.const .D)) opponent
    hk2 hk7 hk3 hL
  constructor
  · intro hθ
    exact tau_play_C opponent (by rw [hmass]; exact hθ)
  · intro hθ
    exact tau_play_D opponent (by rw [hmass]; omega)

/-! ## TauTFTPf -/

/-- **TauTFTPf α-phase theorem** (shallow budgets only — no Löb). -/
theorem tauTFTPf_phase :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE (opponent : Prog),
      (θ ≤ wC + wTs + wTp + wL →
        ∃ N, play N (TauTFTPf k θ wC wD wTs wTp wL wE) opponent = some .C)
      ∧ (wC + wTs + wTp + wL < θ →
        ∃ N, play N (TauTFTPf k θ wC wD wTs wTp wL wE) opponent = some .D) := by
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  refine ⟨kA, fun k hk θ wC wD wTs wTp wL wE opponent => ?_⟩
  have hkA' : 1 * Nat.log2 k + 8 ≤ k := hkA k (Nat.le_of_lt hk)
  have hk2 : 2 ≤ k := by omega
  have hk6 : 6 ≤ k := by omega
  have hk3 : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hmass := tftPfSig_mass k wC wD wTs wTp wL wE
    (.tsearch k (tftPfSig k wC wD wTs wTp wL wE) θ (.const .C) (.const .D)) opponent
    hk2 hk6 hk3
  constructor
  · intro hθ
    exact tau_play_C opponent (by rw [hmass]; exact hθ)
  · intro hθ
    exact tau_play_D opponent (by rw [hmass]; omega)

/-! ## TauTFTSim -/

/-- The valuation of TauTFTSim's sim guards.

    Two guards defect: the Defect hypothesis, and — in the enlarged zoo — the
    EBot one, since `E(δ_C)` probes `.const D` and so plays D (base
    `EBot vs CooperateBot = (D, C)`: EBot exploits a cooperator). Both are
    `.sim`s of a `.bot`-frozen `.const D`, so one pattern covers them. -/
def tftSimVal (k : Nat) : Prog → Action := fun g =>
  if g = .sim (.bot tauDefectδ) (.bot tauDefectδ) then .D
  else if g = .sim (.bot (eOfCoopδ k)) (.bot (eOfCoopδ k)) then .D
  else .C

/-- The C-mass of TauTFTSim's guard list: everything but Defect and EBot. -/
theorem tftSimSig_mass (k wC wD wTs wTp wL wE : Nat) :
    simMass (tftSimVal k) (tftSimSig k wC wD wTs wTp wL wE) = wC + wTs + wTp + wL := by
  -- the five distinct guard programs and their valuations
  have hD : tftSimVal k (.sim (.bot tauDefectδ) (.bot tauDefectδ)) = Action.D := by
    simp [tftSimVal]
  have hE : tftSimVal k (.sim (.bot (eOfCoopδ k)) (.bot (eOfCoopδ k))) = Action.D := by
    simp [tftSimVal, eOfCoopδ, eδ, tauCoopδ, tauDefectδ]
  have hC : tftSimVal k (.sim (.bot tauCoopδ) (.bot tauCoopδ)) = Action.C := by
    simp [tftSimVal, tauCoopδ, tauDefectδ, eOfCoopδ, eδ]
  have hTs : tftSimVal k (.sim (.bot simOfCoopδ) (.bot simOfCoopδ)) = Action.C := by
    simp [tftSimVal, simOfCoopδ, tftSimδ, tauCoopδ, tauDefectδ, eOfCoopδ, eδ]
  have hTp : tftSimVal k (.sim (.bot (searchOfCoopδ k)) (.bot (searchOfCoopδ k)))
      = Action.C := by
    simp [tftSimVal, searchOfCoopδ, probeSearchδ, tauCoopδ, tauDefectδ, eOfCoopδ,
      eδ, probe]
  simp only [tftSimSig, simMass, hC, hD, hTs, hTp, hE]
  have h1 : (Action.C == Action.C) = true := rfl
  have h2 : (Action.D == Action.C) = false := rfl
  simp only [h1, h2, if_true, if_false, Bool.false_eq_true]
  omega

/-- Every guard of TauTFTSim evaluates to its valuation (at some fuel), for any
    players — the guards are closed sims of the δ_C column. Needs only the
    trivial Coop bit (`2 ≤ k`) for the searcher instances. -/
theorem tftSimSig_vals (k wC wD wTs wTp wL wE : Nat) (me opponent : Prog)
    (hk2 : 2 ≤ k) :
    ∀ wg ∈ tftSimSig k wC wD wTs wTp wL wE,
      ∃ N, eval N me opponent wg.2 = some (tftSimVal k wg.2) := by
  -- guard bits in the form the eval unfolding exposes (defeq to the certs)
  have hps : proofSearch k
      ((probe (Prog.const Action.C)).subst
        (.bot (.search k (probe (.const Action.C)) (.const Action.C) (.const Action.D)))
        (.bot (.search k (probe (.const Action.C)) (.const Action.C) (.const Action.D))))
      = true := ps_probe_coop hk2
  have hpsD : proofSearch k
      ((probe (Prog.const Action.D)).subst
        (.bot (.search k (probe (.const Action.D)) (.const Action.C) (.const Action.D)))
        (.bot (.search k (probe (.const Action.D)) (.const Action.C) (.const Action.D))))
      = false := ps_probe_defect k
  have hpsE : proofSearch k
      ((probe (Prog.const Action.C)).subst
        (.bot (.search k (probe (.const Action.C)) (.const Action.D)
          (.search k (probe (.const Action.C)) (.const Action.C) (.const Action.D))))
        (.bot (.search k (probe (.const Action.C)) (.const Action.D)
          (.search k (probe (.const Action.C)) (.const Action.C) (.const Action.D)))))
      = true := ps_probe_coop hk2
  have hD : tftSimVal k (.sim (.bot tauDefectδ) (.bot tauDefectδ)) = Action.D := by
    simp [tftSimVal]
  have hE : tftSimVal k (.sim (.bot (eOfCoopδ k)) (.bot (eOfCoopδ k))) = Action.D := by
    simp [tftSimVal, eOfCoopδ, eδ, tauCoopδ, tauDefectδ]
  have hC : tftSimVal k (.sim (.bot tauCoopδ) (.bot tauCoopδ)) = Action.C := by
    simp [tftSimVal, tauCoopδ, tauDefectδ, eOfCoopδ, eδ]
  have hTs : tftSimVal k (.sim (.bot simOfCoopδ) (.bot simOfCoopδ)) = Action.C := by
    simp [tftSimVal, simOfCoopδ, tftSimδ, tauCoopδ, tauDefectδ, eOfCoopδ, eδ]
  have hTp : tftSimVal k (.sim (.bot (searchOfCoopδ k)) (.bot (searchOfCoopδ k)))
      = Action.C := by
    simp [tftSimVal, searchOfCoopδ, probeSearchδ, tauCoopδ, tauDefectδ, eOfCoopδ,
      eδ, probe]
  intro wg hwg
  simp only [tftSimSig, List.mem_cons, List.not_mem_nil, or_false] at hwg
  rcases hwg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨3, by rw [hC]; simp [tauCoopδ, eval, Prog.subst]⟩
  · exact ⟨3, by rw [hD]; simp [tauDefectδ, eval, Prog.subst]⟩
  · refine ⟨7, ?_⟩
    rw [hTs]; simp [simOfCoopδ, tftSimδ, tauCoopδ, eval, Prog.subst]
    decide
  · refine ⟨4, ?_⟩
    rw [hTp]; simp [searchOfCoopδ, probeSearchδ, tauCoopδ, eval, Prog.subst, hps]
  · refine ⟨4, ?_⟩
    rw [hE]; simp [eOfCoopδ, eδ, tauCoopδ, eval, Prog.subst, hpsE]
  · refine ⟨4, ?_⟩
    rw [hTp]; simp [searchOfCoopδ, probeSearchδ, tauCoopδ, eval, Prog.subst, hps]

/-- **TauTFTSim α-phase theorem** (behavioral — sees true plays; only the trivial
    Coop bit is consulted, so the budget threshold is minimal). -/
theorem tauTFTSim_phase :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE (opponent : Prog),
      (θ ≤ wC + wTs + wTp + wL →
        ∃ N, play N (TauTFTSim k θ wC wD wTs wTp wL wE) opponent = some .C)
      ∧ (wC + wTs + wTp + wL < θ →
        ∃ N, play N (TauTFTSim k θ wC wD wTs wTp wL wE) opponent = some .D) := by
  refine ⟨2, fun k hk θ wC wD wTs wTp wL wE opponent => ?_⟩
  have hk2 : 2 ≤ k := by omega
  obtain ⟨N, hN⟩ := eval_iteTree_of_vals (TauTFTSim k θ wC wD wTs wTp wL wE) opponent
    (tftSimVal k) (tftSimSig k wC wD wTs wTp wL wE) θ
    (tftSimSig_vals k wC wD wTs wTp wL wE _ opponent hk2)
  rw [tftSimSig_mass] at hN
  constructor
  · intro hθ
    rw [if_pos hθ] at hN
    exact ⟨N, hN⟩
  · intro hθ
    rw [if_neg (by omega)] at hN
    exact ⟨N, hN⟩

/-! ## The constants -/

theorem tauCooperate_plays (opponent : Prog) :
    ∃ N, play N TauCooperate opponent = some .C := ⟨1, rfl⟩

theorem tauDefect_plays (opponent : Prog) :
    ∃ N, play N TauDefect opponent = some .D := ⟨1, rfl⟩

/-! ## TauEBot — the separating bot (cascade, 2026-08-12)

Base EBot's exploiter cascade lifted to the vote level: nested `tsearch`, exploit
stage (δ_D column) then reciprocity stage (δ_C column). Its cooperation region is
the WINDOW `wC < θ ≤ wC + wTs + wTp + wL` — defection at BOTH extremes. Def 3's
outcome-averaged lift can only produce one-sided thresholds, so this non-monotone
profile is the structural separation between the definitions. NO Löb budget is
needed anywhere (the 2026-08-11 reciprocity-vote TauEBot and its quine are gone —
they were Def 2's rejected geometry, and their instance family could only be
stipulated). -/

/-- TauEBot's exploit-stage fired mass: only the Coop hypothesis provably
    cooperates with a defector. -/
theorem exploitSig_mass (k wC wD wTs wTp wL wE : Nat) (me opponent : Prog)
    (hk2 : 2 ≤ k) :
    (exploitSig k wC wD wTs wTp wL wE).massWhere
        (fun ψ => proofSearch k (ψ.subst me opponent))
      = wC := by
  simp only [exploitSig, GuardList.massWhere, probe_subst,
    ps_probe_coop hk2, ps_probe_defect, ps_probe_simOfDefect,
    ps_probe_searchOfDefect, ps_probe_eOfDefect]
  simp

/-- **TauEBot α-phase theorem — THE WINDOW** (shallow budgets, no Löb): defect when
    the exploit stage fires (`θ ≤ wC`), cooperate inside the window
    (`wC < θ ≤ wC + wTs + wTp + wL`), defect above it. -/
theorem tauEBot_phase :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE (opponent : Prog),
      (θ ≤ wC →
        ∃ N, play N (TauEBot k θ wC wD wTs wTp wL wE) opponent = some .D)
      ∧ (wC < θ → θ ≤ wC + wTs + wTp + wL →
        ∃ N, play N (TauEBot k θ wC wD wTs wTp wL wE) opponent = some .C)
      ∧ (wC + wTs + wTp + wL < θ →
        ∃ N, play N (TauEBot k θ wC wD wTs wTp wL wE) opponent = some .D) := by
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  refine ⟨kA, fun k hk θ wC wD wTs wTp wL wE opponent => ?_⟩
  have hkA' : 1 * Nat.log2 k + 8 ≤ k := hkA k (Nat.le_of_lt hk)
  have hk2 : 2 ≤ k := by omega
  have hk6 : 6 ≤ k := by omega
  have hk3 : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hmassX := exploitSig_mass k wC wD wTs wTp wL wE
    (TauEBot k θ wC wD wTs wTp wL wE) opponent hk2
  have hmassC := tftPfSig_mass k wC wD wTs wTp wL wE
    (TauEBot k θ wC wD wTs wTp wL wE) opponent hk2 hk6 hk3
  refine ⟨fun hθ => ?_, fun hθ1 hθ2 => ?_, fun hθ => ?_⟩
  · -- the exploit stage fires: outer then-branch, defect
    exact eval_tsearch_of_bits _ opponent (.const .D) _ k .D _ θ
      ⟨1, by rw [if_pos (by rw [hmassX]; exact hθ)]; rfl⟩
  · -- the window: outer else, inner then — cooperate
    refine eval_tsearch_of_bits _ opponent (.const .D) _ k .C _ θ ?_
    rw [if_neg (by rw [hmassX]; omega)]
    exact eval_tsearch_of_bits _ opponent (.const .C) (.const .D) k .C _ θ
      ⟨1, by rw [if_pos (by rw [hmassC]; exact hθ2)]; rfl⟩
  · -- above the window: outer else, inner else — defect
    refine eval_tsearch_of_bits _ opponent (.const .D) _ k .D _ θ ?_
    rw [if_neg (by rw [hmassX]; omega)]
    exact eval_tsearch_of_bits _ opponent (.const .C) (.const .D) k .D _ θ
      ⟨1, by rw [if_neg (by rw [hmassC]; omega)]; rfl⟩

end PD.Tau
