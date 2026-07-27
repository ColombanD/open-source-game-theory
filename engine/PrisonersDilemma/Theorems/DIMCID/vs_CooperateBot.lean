import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- The substituted DIMCID guard against CooperateBot. -/
abbrev dimcid_guard (k : Nat) : Formula :=
  .impl (.plays (DIMCID k) CooperateBot Action.C) (.plays CooperateBot (DIMCID k) Action.D)

/-- The consequent atom `CooperateBot plays D vs DIMCID` is UNPROVABLE: CooperateBot plays C. -/
theorem dimcid_consequent_not_provable (k m : Nat) :
    ¬ Pf m (.plays CooperateBot (DIMCID k) Action.D) := by
  intro h
  obtain ⟨n, hn⟩ := Pf_sound m _ h
  have : play n CooperateBot (DIMCID k) = some Action.C ∨ play n CooperateBot (DIMCID k) = none := by
    cases n with
    | zero => right; rfl
    | succ n => left; exact play_CooperateBot n (DIMCID k)
  rcases this with hC | hNone
  · rw [hC] at hn; exact absurd hn (by decide)
  · rw [hNone] at hn; exact absurd hn (by decide)

/-- `ForbiddenD k φ`: φ is, or is an `.impl`-chain ending in, the false consequent. -/
def DimcidForbiddenD (k : Nat) : Formula → Prop
  | .plays p q a => p = CooperateBot ∧ q = DIMCID k ∧ a = Action.D
  | .impl _ ψ    => DimcidForbiddenD k ψ
  | _            => False

/-- **No `Pf` concludes `.impl _ (false-consequent)`** — ONE flat induction over the unified
    proof system.

    **Pf-only note (Phase 3)**: replaces the former PAIR — `dimcid_no_deriv_forbidden` (a
    `Derivation` induction) plus a 26-argument POSITIONAL `Pf.rec` whose `struct` arm
    reached through the glue into it. One proof system, one induction, NAMED arms via
    `Pf.induct`. The `atom` arm bottoms out on `dimcid_consequent_not_provable` (the consequent
    is a genuinely FALSE atom, refuted by soundness); the implication-forming rules recurse on
    the premise carrying the consequent chain; every other rule concludes a shape the motive
    maps to `False`. -/
theorem dimcid_no_provable_forbidden (k : Nat) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ → ¬ DimcidForbiddenD k φ := by
  intro m φ h
  induction h using Pf.induct with
  | atom k' φ' hatom =>
      intro hF
      cases hatom with
      | mk cert hle =>
          simp only [DimcidForbiddenD] at hF
          obtain ⟨hp, hq, ha⟩ := hF
          subst hp; subst hq; subst ha
          exact dimcid_consequent_not_provable k _ (Pf.atom (.mk cert hle))
  | searchBranch k' g ψ a b me opponent hme hle =>
      intro hF; subst hme; simp only [DimcidForbiddenD] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [CooperateBot] at hm
  | simStep k' me p q opponent a hme hle =>
      intro hF; subst hme; simp only [DimcidForbiddenD] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [CooperateBot] at hm
  | botSimStep k' me p q opponent a hme hle =>
      intro hF; subst hme; simp only [DimcidForbiddenD] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [CooperateBot] at hm
  | botSearchStep k' g ψ a b me opponent hme hle =>
      intro hF; subst hme; simp only [DimcidForbiddenD] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [CooperateBot] at hm
  | iteBranchSearch_t k' g z a' c0 c1 ψ q me opponent hme hle =>
      intro hF; subst hme; simp only [DimcidForbiddenD] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [CooperateBot] at hm
  | searchThenSearch_t k' k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle _ih =>
      intro hF; subst hme; simp only [DimcidForbiddenD] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [CooperateBot] at hm
  | mp k' m₁ m₂ φ' α h1 h2 hle ih1 _ih2 => intro hF; exact ih1 hF
  | implTrans k' φ' ψ χ a b h1 h2 hle _ih1 ih2 => intro hF; exact ih2 hF
  | weakenImpl k' φ' ψ m' hψ hle ih => intro hF; exact ih hF
  | impS2 φ' ψ χ m₁ m₂ K h1 h2 hle ih1 _ih2 => intro hF; exact ih1 hF
  | diagF pm fb g K tgt hgate hle ih => intro hF; exact ih hF
  | eqRefl k' p hle => intro hF; simp only [DimcidForbiddenD] at hF
  | eqNeg k' p q hne hle => intro hF; simp only [DimcidForbiddenD] at hF
  | atomNeg k' p q b aN m' hatom hne hle => intro hF; simp only [DimcidForbiddenD] at hF
  | atomBoxImpl k' kBox p q a hatom hle => intro hF; simp only [DimcidForbiddenD] at hF
  | boxIntro kIn K φ' hprem hle _ih => intro hF; simp only [DimcidForbiddenD] at hF
  | axK a b c m' K φ' α hprem hgate hle _ih => intro hF; simp only [DimcidForbiddenD] at hF
  | box4 a b K φ' hgate hsz => intro hF; simp only [DimcidForbiddenD] at hF
  | diagB pm fb g K tgt hgate hle _ih => intro hF; simp only [DimcidForbiddenD] at hF
  | axKf a b c K φ' α hgate hsz => intro hF; simp only [DimcidForbiddenD] at hF
  | boxMono a b K φ' hab hsz => intro hF; simp only [DimcidForbiddenD] at hF

theorem dimcid_guard_not_provable (k : Nat) : ¬ Pf k (dimcid_guard k) := by
  intro h
  refine dimcid_no_provable_forbidden k h ?_
  show DimcidForbiddenD k (dimcid_guard k)
  unfold dimcid_guard DimcidForbiddenD DimcidForbiddenD
  exact ⟨rfl, rfl, rfl⟩

theorem proofSearch_false_for_DIMCID_vs_CooperateBot (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) CooperateBot) = false := by
  show proofSearch k (dimcid_guard k) = false
  cases hps : proofSearch k (dimcid_guard k) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k (dimcid_guard k)).1 hps) (dimcid_guard_not_provable k)

/-- DIMCID cooperates against CooperateBot: its guard fails, so it takes the `.const .C` branch. -/
theorem DIMCID_plays_C_against_CooperateBot (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) CooperateBot = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) CooperateBot)
          then eval (fuel + 1) (DIMCID k) CooperateBot (.const Action.D)
          else eval (fuel + 1) (DIMCID k) CooperateBot (.const Action.C)) = some .C
  rw [proofSearch_false_for_DIMCID_vs_CooperateBot k]; simp [eval]

/-- **DIMCID vs CooperateBot: mutual cooperation (C, C)** — formerly deliberately-omitted, now
    PROVED with NO `atom_complete_false_guard` axiom. -/
theorem outcome_DIMCID_vs_CooperateBot :
    ∃ k, ∀ fuel, outcome (fuel + 2) (DIMCID k) CooperateBot = some (.C, .C) := by
  refine ⟨0, fun fuel => ?_⟩
  have hA : play (fuel + 2) (DIMCID 0) CooperateBot = some .C := DIMCID_plays_C_against_CooperateBot 0 fuel
  have hB : play (fuel + 2) CooperateBot (DIMCID 0) = some .C := by
    simpa using play_CooperateBot (fuel + 1) (DIMCID 0)
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
