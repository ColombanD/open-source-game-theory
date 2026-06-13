import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.ProofSearch

open PD
open PD.Axioms
open PD.Bots
namespace PD.Theorems

/-- Local swap lemma: MirrorBot mirrors its opponent's action. -/
private theorem mirror_swap_provable' (q : Prog) (a : Action) :
    ∃ m, proofSearch m
      (.impl (.plays q MirrorBot a) (.plays MirrorBot q a)) = true := by
  have h := proof_system_verifies_sim MirrorBot .opp .self q a rfl
  simpa [Prog.subst, MirrorBot] using h

/-- DupocBot defects iff proofSearch fails; cooperates iff proofSearch succeeds. -/
private theorem DupocBot_plays_C_against_MirrorBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (DupocBot k) .C) = true) :
    play (fuel + 2) (DupocBot k) MirrorBot = some .C := by
  show eval (fuel + 2) (DupocBot k) MirrorBot (DupocBot k) = some .C
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

private theorem DupocBot_plays_D_against_MirrorBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (DupocBot k) .C) = false) :
    play (fuel + 2) (DupocBot k) MirrorBot = some .D := by
  show eval (fuel + 2) (DupocBot k) MirrorBot (DupocBot k) = some .D
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

private theorem MirrorBot_plays_C_against_DupocBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (DupocBot k) .C) = true) :
    play (fuel + 3) MirrorBot (DupocBot k) = some .C := by
  have hDupoc : play (fuel + 2) (DupocBot k) MirrorBot = some .C :=
    DupocBot_plays_C_against_MirrorBot k fuel hk
  simpa [play, eval, Prog.subst, MirrorBot] using hDupoc

private theorem MirrorBot_plays_D_against_DupocBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (DupocBot k) .C) = false) :
    play (fuel + 3) MirrorBot (DupocBot k) = some .D := by
  have hDupoc : play (fuel + 2) (DupocBot k) MirrorBot = some .D :=
    DupocBot_plays_D_against_MirrorBot k fuel hk
  simpa [play, eval, Prog.subst, MirrorBot] using hDupoc

/-- Inversion: if MirrorBot plays C against DupocBot k for some fuel, then
    DupocBot's proof-search guard must have fired. -/
private theorem proofSearch_k_of_play_MirrorBot_C
    (k n : Nat) (h : play n MirrorBot (DupocBot k) = some .C) :
    proofSearch k (.plays MirrorBot (DupocBot k) .C) = true := by
  cases hps : proofSearch k (.plays MirrorBot (DupocBot k) .C) with
  | true  => rfl
  | false =>
    exfalso
    rcases n with _ | _ | _ | n
    · simp [play, eval] at h
    · simp [play, eval, MirrorBot] at h
    · have hev : play 2 MirrorBot (DupocBot k) = none := by
        unfold DupocBot
        simp [play, eval, Prog.subst, MirrorBot, Formula.subst]
      rw [hev] at h
      cases h
    · have hev : play (n + 3) MirrorBot (DupocBot k) = some .D := by
        simpa using MirrorBot_plays_D_against_DupocBot k n hps
      rw [hev] at h
      cases h

/-- DupocBot vs MirrorBot cooperate, for k large enough, via PBLT.

Note: DupocBot's outcome with MirrorBot is fully determined by whether
`proofSearch k (.plays MirrorBot (DupocBot k) .C)` succeeds: if it does
both cooperate; if not, both defect. Either branch is internally consistent,
so the outcome is not determined for arbitrary `k`. PBLT (bounded Löb) forces
the cooperation fixed point for sufficiently large `k`, so the theorem is
naturally existential — analogous to `CupodBot_vs_MirrorBot` for the
defection direction. -/
theorem llm_outcome_DupocBot_vs_MirrorBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DupocBot k) MirrorBot = some (.C, .C) := by
  let φ : Nat → Formula := fun k => .plays MirrorBot (DupocBot k) .C
  have hMono : ∀ a b : Nat, a ≤ b → id a ≤ id b := fun _ _ h => h
  have hLog : ∃ c kHat, c > 0 ∧ ∀ k, k > kHat → id k > c * Nat.log2 k := by
    refine ⟨1, 0, Nat.zero_lt_one, ?_⟩
    intro k hk
    have hlog : Nat.log2 k < k := by
      rw [Nat.log2_lt (Nat.pos_iff_ne_zero.mp hk)]
      exact Nat.lt_two_pow_self
    simpa using hlog
  have hLoeb :
      ∀ k, k > 0 →
        ∃ m, proofSearch m (.impl (.box (id k) (φ k)) (φ k)) = true := by
    intro k _
    have hSearch : ∃ m, proofSearch m
        (.impl (.box k (φ k)) (.plays (DupocBot k) MirrorBot .C)) = true := by
      have h := proof_system_verifies_search_branch
        k (.plays .opp .self .C) .C .D (DupocBot k) MirrorBot rfl
      simpa [Formula.subst, Prog.subst, φ] using h
    have hMirror := mirror_swap_provable' (DupocBot k) .C
    have hChain := proofSearch_impl_trans _ _ _ hSearch hMirror
    simpa [φ] using hChain
  obtain ⟨k₂, hk₂⟩ := PBLT φ id 0 hMono hLog hLoeb
  refine ⟨k₂, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := proofSearch_sound m (φ k) hm
  obtain ⟨n, hMirror⟩ := hInterp
  have hPS : proofSearch k (.plays MirrorBot (DupocBot k) .C) = true :=
    proofSearch_k_of_play_MirrorBot_C k n hMirror
  refine ⟨3, ?_⟩
  have hA : play 3 (DupocBot k) MirrorBot = some .C := by
    simpa using DupocBot_plays_C_against_MirrorBot k 1 hPS
  have hB : play 3 MirrorBot (DupocBot k) = some .C := by
    simpa using MirrorBot_plays_C_against_DupocBot k 0 hPS
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
