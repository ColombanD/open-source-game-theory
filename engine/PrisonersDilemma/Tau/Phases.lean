import PrisonersDilemma.Tau.PeelLemmas
import PrisonersDilemma.Tau.Certs

/-!
# Tau/Phases — the α-regime play theorems

The milestone-1 headline, per non-constant tau player: past a budget threshold, the
player cooperates — against EVERY opponent (tau players are `.opp`-free, hence
extensionally constant) — **exactly when its scaled threshold θ is within the
cooperation mass `wC + wTs + wTp + wL`** (everything except the Defect hypothesis).

All three non-constant players share that α-boundary; what separates them is the
BUDGET at which it becomes available: TauTFTSim needs only shallow fuel + the trivial
Coop bit, TauTFTPf needs shallow proof budgets, and TauDupoc needs the **Löb
threshold** for its `wL` bit (`ps_probe_quine`). The prover/behavioral split is a
budget-phase gap, not an α-gap.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## Mass computations -/

/-- TauDupoc's fired mass at an adequate budget: every bit but Defect fires. -/
theorem dupocSig_mass (k wC wD wTs wTp wL : Nat) (me opponent : Prog)
    (hk2 : 2 ≤ k) (hk7 : c_guard k + 7 ≤ k) (hk3 : c_guard k + 3 ≤ k)
    (hL : proofSearch k (probe (TauDupocδ k)) = true) :
    (dupocSig k wC wD wTs wTp wL).massWhere
        (fun ψ => proofSearch k (ψ.subst me opponent))
      = wC + wTs + wTp + wL := by
  simp only [dupocSig, GuardList.massWhere, probe_subst,
    ps_probe_coop hk2, ps_probe_defect, ps_probe_simOfSearch hk2 hk7,
    ps_probe_searchOfSearch hk2 hk3, hL]
  simp
  omega

/-- TauTFTPf's fired mass at an adequate (shallow) budget: same shape, no Löb. -/
theorem tftPfSig_mass (k wC wD wTs wTp wL : Nat) (me opponent : Prog)
    (hk2 : 2 ≤ k) (hk6 : 6 ≤ k) (hk3 : c_guard k + 3 ≤ k) :
    (tftPfSig k wC wD wTs wTp wL).massWhere
        (fun ψ => proofSearch k (ψ.subst me opponent))
      = wC + wTs + wTp + wL := by
  simp only [tftPfSig, GuardList.massWhere, probe_subst,
    ps_probe_coop hk2, ps_probe_defect, ps_probe_simOfCoop hk6,
    ps_probe_searchOfCoop hk2 hk3]
  simp
  omega

/-! ## TauDupoc -/

/-- **TauDupoc α-phase theorem** (Löb-gated). -/
theorem tauDupoc_phase :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL (opponent : Prog),
      (θ ≤ wC + wTs + wTp + wL →
        ∃ N, play N (TauDupoc k θ wC wD wTs wTp wL) opponent = some .C)
      ∧ (wC + wTs + wTp + wL < θ →
        ∃ N, play N (TauDupoc k θ wC wD wTs wTp wL) opponent = some .D) := by
  obtain ⟨kL, hkL⟩ := ps_probe_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  refine ⟨max kL kA, fun k hk θ wC wD wTs wTp wL opponent => ?_⟩
  have hL := hkL k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hkA' : 1 * Nat.log2 k + 8 ≤ k :=
    hkA k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  have hk2 : 2 ≤ k := by omega
  have hk7 : c_guard k + 7 ≤ k := by simp only [c_guard, numCost]; omega
  have hk3 : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hmass := dupocSig_mass k wC wD wTs wTp wL
    (.tsearch k (dupocSig k wC wD wTs wTp wL) θ (.const .C) (.const .D)) opponent
    hk2 hk7 hk3 hL
  constructor
  · intro hθ
    exact tau_play_C opponent (by rw [hmass]; exact hθ)
  · intro hθ
    exact tau_play_D opponent (by rw [hmass]; omega)

/-! ## TauTFTPf -/

/-- **TauTFTPf α-phase theorem** (shallow budgets only — no Löb). -/
theorem tauTFTPf_phase :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL (opponent : Prog),
      (θ ≤ wC + wTs + wTp + wL →
        ∃ N, play N (TauTFTPf k θ wC wD wTs wTp wL) opponent = some .C)
      ∧ (wC + wTs + wTp + wL < θ →
        ∃ N, play N (TauTFTPf k θ wC wD wTs wTp wL) opponent = some .D) := by
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  refine ⟨kA, fun k hk θ wC wD wTs wTp wL opponent => ?_⟩
  have hkA' : 1 * Nat.log2 k + 8 ≤ k := hkA k (Nat.le_of_lt hk)
  have hk2 : 2 ≤ k := by omega
  have hk6 : 6 ≤ k := by omega
  have hk3 : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hmass := tftPfSig_mass k wC wD wTs wTp wL
    (.tsearch k (tftPfSig k wC wD wTs wTp wL) θ (.const .C) (.const .D)) opponent
    hk2 hk6 hk3
  constructor
  · intro hθ
    exact tau_play_C opponent (by rw [hmass]; exact hθ)
  · intro hθ
    exact tau_play_D opponent (by rw [hmass]; omega)

/-! ## TauTFTSim -/

/-- The valuation of TauTFTSim's sim guards: only the Defect probe defects. -/
def tftSimVal : Prog → Action := fun g =>
  if g = .sim (.bot tauDefectδ) (.bot tauDefectδ) then .D else .C

/-- The C-mass of TauTFTSim's guard list under that valuation. -/
theorem tftSimSig_mass (k wC wD wTs wTp wL : Nat) :
    simMass tftSimVal (tftSimSig k wC wD wTs wTp wL) = wC + wTs + wTp + wL := by
  have hct : (Action.C == Action.C) = true := rfl
  have hdf : ¬ ((Action.D == Action.C) = true) := by decide
  simp [tftSimSig, simMass, tftSimVal, tauCoopδ, tauDefectδ, simOfCoopδ, tftSimδ,
    searchOfCoopδ, probeSearchδ, hct, hdf]
  omega

/-- Every guard of TauTFTSim evaluates to its valuation (at some fuel), for any
    players — the guards are closed sims of the δ_C column. Needs only the trivial
    Coop bit (`2 ≤ k`) for the two searcher instances. -/
theorem tftSimSig_vals (k wC wD wTs wTp wL : Nat) (me opponent : Prog)
    (hk2 : 2 ≤ k) :
    ∀ wg ∈ tftSimSig k wC wD wTs wTp wL,
      ∃ N, eval N me opponent wg.2 = some (tftSimVal wg.2) := by
  -- the guard bit, stated in the form the eval unfolding exposes (defeq to
  -- `ps_probe_coop`)
  have hps : proofSearch k
      ((probe (Prog.const Action.C)).subst
        (.bot (.search k (probe (.const Action.C)) (.const Action.C) (.const Action.D)))
        (.bot (.search k (probe (.const Action.C)) (.const Action.C) (.const Action.D))))
      = true := ps_probe_coop hk2
  intro wg hwg
  simp only [tftSimSig, List.mem_cons, List.not_mem_nil, or_false] at hwg
  rcases hwg with rfl | rfl | rfl | rfl | rfl
  · -- Coop guard → C
    exact ⟨3, by simp [tftSimVal, tauCoopδ, tauDefectδ, eval, Prog.subst]⟩
  · -- Defect guard → D
    exact ⟨3, by simp [tftSimVal, tauDefectδ, eval, Prog.subst]⟩
  · -- Ts(δ_C) guard → C
    exact ⟨7, by
      simp [tftSimVal, simOfCoopδ, tftSimδ, tauCoopδ, tauDefectδ, eval, Prog.subst]
      decide⟩
  · -- Tp(δ_C) = L(δ_C) guard → C (the inner search fires on the Coop bit)
    exact ⟨4, by
      simp [tftSimVal, searchOfCoopδ, probeSearchδ, tauCoopδ, tauDefectδ, eval,
        Prog.subst, hps]⟩
  · -- L(δ_C) guard (same instance) → C
    exact ⟨4, by
      simp [tftSimVal, searchOfCoopδ, probeSearchδ, tauCoopδ, tauDefectδ, eval,
        Prog.subst, hps]⟩

/-- **TauTFTSim α-phase theorem** (behavioral — sees true plays; only the trivial
    Coop bit is consulted, so the budget threshold is minimal). -/
theorem tauTFTSim_phase :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL (opponent : Prog),
      (θ ≤ wC + wTs + wTp + wL →
        ∃ N, play N (TauTFTSim k θ wC wD wTs wTp wL) opponent = some .C)
      ∧ (wC + wTs + wTp + wL < θ →
        ∃ N, play N (TauTFTSim k θ wC wD wTs wTp wL) opponent = some .D) := by
  refine ⟨2, fun k hk θ wC wD wTs wTp wL opponent => ?_⟩
  have hk2 : 2 ≤ k := by omega
  obtain ⟨N, hN⟩ := eval_iteTree_of_vals (TauTFTSim k θ wC wD wTs wTp wL) opponent
    tftSimVal (tftSimSig k wC wD wTs wTp wL) θ
    (tftSimSig_vals k wC wD wTs wTp wL _ opponent hk2)
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

/-! ## TauEBot — the separating bot

Same reciprocity geometry as TauDupoc, reading the δ_E column — but a
DIFFERENT α-boundary, and that is exactly why it separates the definitions.
Only `C(δ_E)` and the quine fire: base `TitForTatBot vs EBot` and `DupocBot vs
EBot` are both `(D, C)`, so those hypotheses DEFECT against EBot and their
probe bits are 0. TauEBot's cooperation mass is therefore `wC + wE`, against
TauDupoc's `wC + wTs + wTp + wL`.

Under Def 3 the same bot would read the OTHER side of those asymmetric cells
("what do I do to them" — EBot cooperates with both), giving a different mass
and a different boundary. One asymmetric cell under a conditional bot is all it
takes. -/

/-- TauEBot's fired mass: only the Coop hypothesis and the quine fire. -/
theorem eSig_mass (k wC wD wTs wTp wE : Nat) (me opponent : Prog)
    (hk2 : 2 ≤ k)
    (hE : proofSearch k (probe (TauEBotδ k)) = true) :
    (eSig k wC wD wTs wTp wE).massWhere
        (fun ψ => proofSearch k (ψ.subst me opponent))
      = wC + wE := by
  simp only [eSig, GuardList.massWhere, probe_subst,
    ps_probe_coop hk2, ps_probe_defect, ps_probe_simOfE, ps_probe_searchOfE, hE]
  simp

/-- **TauEBot α-phase theorem** (Löb-gated, like TauDupoc — but at the `wC + wE`
    boundary). -/
theorem tauEBot_phase :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wE (opponent : Prog),
      (θ ≤ wC + wE →
        ∃ N, play N (TauEBot k θ wC wD wTs wTp wE) opponent = some .C)
      ∧ (wC + wE < θ →
        ∃ N, play N (TauEBot k θ wC wD wTs wTp wE) opponent = some .D) := by
  obtain ⟨kE, hkE⟩ := ps_probe_eQuine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  refine ⟨max kE kA, fun k hk θ wC wD wTs wTp wE opponent => ?_⟩
  have hE := hkE k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hkA' : 1 * Nat.log2 k + 8 ≤ k :=
    hkA k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  have hk2 : 2 ≤ k := by omega
  have hmass := eSig_mass k wC wD wTs wTp wE
    (.tsearch k (eSig k wC wD wTs wTp wE) θ (.const .C) (.const .D)) opponent
    hk2 hE
  constructor
  · intro hθ
    exact tau_play_C opponent (by rw [hmass]; exact hθ)
  · intro hθ
    exact tau_play_D opponent (by rw [hmass]; omega)

end PD.Tau
