import PrisonersDilemma.Tau.Theorems.TauMirror.Helpers
import PrisonersDilemma.Tau.Theorems.TauPrudent.Helpers
import PrisonersDilemma.Tau.Theorems.TauTFTSim.Phase
import PrisonersDilemma.Tau.Theorems.TauTFTPf.Phase
import PrisonersDilemma.Tau.Theorems.TauEBot.Phase
import PrisonersDilemma.Tau.Theorems.TauJust.Phase
import PrisonersDilemma.Tau.Theorems.TauOBot.Phase
import PrisonersDilemma.Tau.Theorems.TauGuardian.Phase
import PrisonersDilemma.Tau.Theorems.TauDBot.Phase
import PrisonersDilemma.Tau.Theorems.TauCupodTroll.Phase

/-!
# τ(Mirror)'s phase — `C` below its prefix mass, honestly `none` above it

τ(Mirror)'s row is the one row whose diagonal has NO play: `inst .mirror .mirror`
is `.sim .self .self`, base MirrorBot's self-play, proven divergent. `VoteBits`
needs a witness per entry, so the FULL 15-slot row is unstateable — that has
been recorded since the lift. But the vote COMMITS as soon as its residual hits
zero, without consulting later entries, and `.mirror` is the LAST slot of
`tauOrder`. So τ(Mirror) has a genuine two-regime phase:

* `θ ≤ mirrorMass w` — the C-mass of the 14 other slots reaches `θ` before the
  diagonal is consulted: plays `C`;
* otherwise the vote reaches the diagonal and DIVERGES: the play is `none` at
  every fuel — not `D`. This is the "a TauBot always terminates" caveat made a
  theorem: τ(Mirror) is the one tau player that does not, and only in the
  regime where it would have defected.

The 14 slots are what each other bot plays AGAINST the mirror (the forwarder
copies the signal): every classifier's `.mirror` slot from its own phase file,
and the four entangled self-probers' cells from `TauMirror/Helpers`.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- `tauOrder` without its last slot. -/
def tauOrderInit : List Tmpl :=
  [.coop, .defect, .tftSim, .tftPf, .dupoc, .ebot, .just, .obot, .guardian, .dbot,
   .cupodTroll, .cupod, .cimcic, .dimcid, .prudent]

theorem tauOrder_eq : tauOrder = tauOrderInit ++ [.mirror] := rfl

theorem vecOf_append {ι : Type} (Z : Zoo ι) [DecidableEq ι] (A : ι) (w : ι → Nat) :
    ∀ (l₁ l₂ : List ι), vecOf Z A w (l₁ ++ l₂) = (vecOf Z A w l₁).app (vecOf Z A w l₂)
  | [], _ => rfl
  | T :: rest, l₂ => by
      simp only [List.cons_append, vecOf, VoteList.app, vecOf_append Z A w rest l₂]

/-- What τ(Mirror) plays at each hypothesis: the hypothesis's own play against
    the mirror. The `.mirror` slot is never consulted below (the diagonal
    diverges); its value here is a placeholder outside the stated prefix. -/
def mirrorRow : Tmpl → Action
  | .coop       => .C
  | .defect     => .D
  | .tftSim     => .C
  | .tftPf      => .C
  | .dupoc      => .C
  | .ebot       => .C
  | .just       => .C
  | .obot       => .D
  | .guardian   => .C
  | .dbot       => .C
  | .cupodTroll => .C
  | .cupod      => .D
  | .cimcic     => .C
  | .dimcid     => .D
  | .prudent    => .C
  | .mirror     => .D

/-- The display form of the prefix mass. -/
def mirrorMass (w : Tmpl → Nat) : Nat :=
  w .coop + w .tftSim + w .tftPf + w .dupoc + w .ebot + w .just + w .guardian + w .dbot
    + w .cupodTroll + w .cimcic + w .prudent

/-- Every prefix slot's witness, past one threshold. -/
theorem mirrorRow_plays :
    ∃ k₂, ∀ k, k₂ < k → ∀ T ∈ tauOrderInit,
      ∃ N, eval N (.bot (inst (tauZoo k) .mirror T)) (.bot (inst (tauZoo k) .mirror T))
        (inst (tauZoo k) .mirror T) = some (mirrorRow T) := by
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 100 1000
  obtain ⟨kQ, hkQ⟩ := ps_probe_inst_quine
  obtain ⟨kM, hkM⟩ := ps_probe_inst_cimcic_dupoc
  obtain ⟨kX, hkX⟩ := ps_probe_mirror_dupoc
  obtain ⟨k1, h1⟩ := mirror_dupoc_plays_C
  obtain ⟨k2, h2⟩ := mirror_cupod_plays_D
  obtain ⟨k3, h3⟩ := mirror_cimcic_plays_C
  obtain ⟨k4, h4⟩ := mirror_dimcid_plays_D
  obtain ⟨k5, h5⟩ := mirror_prudent_plays_C
  obtain ⟨kP, hP⟩ := prudent_mirror_plays_C
  refine ⟨max (max (max kA kQ) (max (max kM kX) (max (max k1 k2) (max k3 k4)))) (max k5 kP),
    fun k hk T hT => ?_⟩
  have hL : 100 * Nat.log2 k + 1000 ≤ k := hkA k (by omega)
  have hlog := Nat.log2_le_self k
  have hk2 : 2 ≤ k := by omega
  have hk3 : 3 ≤ k := by omega
  have h6 : 6 ≤ k := by omega
  have h10 : 10 ≤ k := by omega
  have hkk : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hk7 : c_guard k + 7 ≤ k := by simp only [c_guard, numCost]; omega
  have hcg : c_guard k + 20 ≤ k := by simp only [c_guard, numCost]; omega
  have hquine := hkQ k (by omega)
  have hcim := hkM k (by omega)
  have hmir := hkX k (by omega)
  have hpm := hP k (by omega)
  simp only [tauOrderInit, List.mem_cons, List.mem_nil_iff, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mirror_coop_plays_C
  · exact mirror_defect_plays_D
  · exact mirror_copies (T := .tftSim) rfl (tftSimRow_plays hk2 hkk h6 h10 hL hcg .mirror)
  · exact mirror_copies (T := .tftPf) rfl (tftPfRow_plays hk2 hkk h6 h10 hL hcg .mirror)
  · exact h1 k (by omega)
  · exact mirror_copies (T := .ebot) rfl (eRow_plays hk2 hkk h6 h10 hL hcg hpm .mirror)
  · exact mirror_copies (T := .just) rfl (justRow_plays hk2 hkk hk7 hquine hcim hmir .mirror)
  · exact mirror_copies (T := .obot) rfl (obotRow_plays hk2 hkk h6 h10 hL hcg .mirror)
  · exact mirror_copies (T := .guardian) rfl
      (guardianRow_plays hk2 hkk h6 h10 hL hcg .mirror)
  · exact mirror_copies (T := .dbot) rfl (dbotRow_plays hk2 hL .mirror)
  · exact mirror_copies (T := .cupodTroll) rfl (cupodTrollRow_plays hk3 .mirror)
  · exact h2 k (by omega)
  · exact h3 k (by omega)
  · exact h4 k (by omega)
  · exact h5 k (by omega)

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list): the 15-slot PREFIX over `tauOrderInit`; the diagonal is not an
    entry (it diverges), which the scanner records as `N`. -/
theorem mirrorBits :
    ∃ k₂, ∀ k, k₂ < k → ∀ (w : Tmpl → Nat),
      VoteBits (vecOf (tauZoo k) .mirror w tauOrderInit)
        [(w .coop, .C), (w .defect, .D), (w .tftSim, .C), (w .tftPf, .C),
         (w .dupoc, .C), (w .ebot, .C), (w .just, .C), (w .obot, .D),
         (w .guardian, .C), (w .dbot, .C), (w .cupodTroll, .C), (w .cupod, .D), (w .cimcic, .C), (w .dimcid, .D), (w .prudent, .C)] := by
  obtain ⟨k₂, hrow⟩ := mirrorRow_plays
  exact ⟨k₂, fun k hk w => vecOf_bits (tauZoo k) .mirror w mirrorRow tauOrderInit (hrow k hk)⟩

/-- **τ(Mirror)'s phase.** Boundary `θ ≤ mirrorMass`; above it the play is `none`. -/
theorem tauMirror_phase :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (θ ≤ mirrorMass w → ∃ N, play N (TauBotZ k .mirror w θ) opponent = some .C)
      ∧ (¬ θ ≤ mirrorMass w → ∀ N, play N (TauBotZ k .mirror w θ) opponent = none) := by
  obtain ⟨k₂, hrow⟩ := mirrorRow_plays
  refine ⟨k₂, fun k hk θ w opponent => ?_⟩
  have hbits := vecOf_bits (tauZoo k) .mirror w mirrorRow tauOrderInit (hrow k hk)
  have h := tauPlayer_phase_prefix θ hbits (w' := w .mirror)
    (J := inst (tauZoo k) .mirror .mirror)
    (by rw [inst_mirror_quine]; exact mirror_quine_diverges) opponent
  have hvec : TauBotZ k .mirror w θ
      = tauPlayer ((vecOf (tauZoo k) .mirror w tauOrderInit).app
          (.cons (w .mirror) (inst (tauZoo k) .mirror .mirror) .nil)) θ := by
    rw [TauBotZ, tauOrder_eq, vecOf_append]; rfl
  rw [hvec]
  simp only [tauOrderInit, List.map, mirrorRow, massOf, massOf_ifC, massOf_ifD] at h
  exact ⟨fun hθ => h.1 (by unfold mirrorMass at hθ; omega),
         fun hθ => h.2 (by unfold mirrorMass at hθ; omega)⟩

end PD.Tau
