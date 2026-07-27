import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.Helpers

import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Theorems.CooperateBot

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- The substituted CIMCIC guard against DefectBot. -/
abbrev cimcic_guard (k : Nat) : Formula :=
  .impl (.plays (CIMCIC k) DefectBot Action.C) (.plays DefectBot (CIMCIC k) Action.C)

/-- The consequent atom `DefectBot plays C vs CIMCIC` is genuinely UNPROVABLE: DefectBot plays D,
    so its `interp` is false, refuted by `Pf_sound`. -/
theorem cimcic_consequent_not_provable (k m : Nat) :
    ¬ Pf m (.plays DefectBot (CIMCIC k) Action.C) := by
  intro h
  obtain ⟨n, hn⟩ := Pf_sound m _ h
  have : play n DefectBot (CIMCIC k) = some Action.D ∨ play n DefectBot (CIMCIC k) = none := by
    cases n with
    | zero => right; rfl
    | succ n => left; simp [play, eval, DefectBot]
  rcases this with hD | hNone
  · rw [hD] at hn; exact absurd hn (by decide)
  · rw [hNone] at hn; exact absurd hn (by decide)

/-- `ForbiddenC k φ`: φ is, or is an `.impl`-chain ending in, the false consequent `DefectBot plays
    C vs CIMCIC`. The motive for the structural exclusion. -/
def CimcicForbiddenC (k : Nat) : Formula → Prop
  | .plays p q a => p = DefectBot ∧ q = CIMCIC k ∧ a = Action.C
  | .impl _ ψ    => CimcicForbiddenC k ψ
  | _            => False

/-- **No `Pf` concludes `.impl _ (false-consequent)`** — ONE flat induction over the unified
    proof system.

    **Pf-only note (Phase 3)**: this replaces the former PAIR of theorems — `cimcic_no_deriv_forbidden`
    (a `Derivation` induction) plus `cimcic_no_provable_forbidden` (a 26-argument POSITIONAL `Provable.rec`
    whose `struct` arm reached through the glue into the first). With one proof system there is
    one induction, with NAMED arms via `Pf.induct`. The `atom` arm bottoms out on
    `cimcic_consequent_not_provable` (the consequent is a genuinely FALSE atom, refuted by soundness);
    the implication-forming rules recurse on the premise carrying the consequent chain; every
    other rule concludes a shape the motive maps to `False`. -/
theorem cimcic_no_provable_forbidden (k : Nat) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ → ¬ CimcicForbiddenC k φ := by
  intro m φ h
  induction h using Pf.induct with
  -- the execution bridge: bottoms out on the FALSE consequent atom
  | atom k' φ' hatom =>
      intro hF
      cases hatom with
      | mk cert hle =>
          simp only [CimcicForbiddenC] at hF
          obtain ⟨hp, hq, ha⟩ := hF
          subst hp; subst hq; subst ha
          exact cimcic_consequent_not_provable k _ (Pf.atom (.mk cert hle))
  -- source transparency: the consequent's subject would have to be `DefectBot` (= `.const D`),
  -- but these rules read `.search`/`.sim`/`.ite` players — syntactic no-confusion.
  | searchBranch k' g ψ a b me opponent hme hle =>
      intro hF; subst hme; simp only [CimcicForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | simStep k' me p q opponent a hme hle =>
      intro hF; subst hme; simp only [CimcicForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | botSimStep k' me p q opponent a hme hle =>
      intro hF; subst hme; simp only [CimcicForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | botSearchStep k' g ψ a b me opponent hme hle =>
      intro hF; subst hme; simp only [CimcicForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | iteBranchSearch_t k' g z a' c0 c1 ψ q me opponent hme hle =>
      intro hF; subst hme; simp only [CimcicForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | searchThenSearch_t k' k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle _ih =>
      intro hF; subst hme; simp only [CimcicForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  -- implication-forming rules: the motive peels the `.impl`; recurse on the carrying premise
  | mp k' m₁ m₂ φ' α h1 h2 hle ih1 _ih2 => intro hF; exact ih1 hF
  | implTrans k' φ' ψ χ a b h1 h2 hle _ih1 ih2 => intro hF; exact ih2 hF
  | weakenImpl k' φ' ψ m' hψ hle ih => intro hF; exact ih hF
  | impS2 φ' ψ χ m₁ m₂ K h1 h2 hle ih1 _ih2 => intro hF; exact ih1 hF
  | diagF pm fb g K tgt hgate hle ih => intro hF; exact ih hF
  -- everything else concludes a `.eq`/`.neg`/`.box`/`.diag` shape: the motive is `False` there
  | eqRefl k' p hle => intro hF; simp only [CimcicForbiddenC] at hF
  | eqNeg k' p q hne hle => intro hF; simp only [CimcicForbiddenC] at hF
  | atomNeg k' p q b aN m' hatom hne hle => intro hF; simp only [CimcicForbiddenC] at hF
  | atomBoxImpl k' kBox p q a hatom hle => intro hF; simp only [CimcicForbiddenC] at hF
  | boxIntro kIn K φ' hprem hle _ih => intro hF; simp only [CimcicForbiddenC] at hF
  | axK a b c m' K φ' α hprem hgate hle _ih => intro hF; simp only [CimcicForbiddenC] at hF
  | box4 a b K φ' hgate hsz => intro hF; simp only [CimcicForbiddenC] at hF
  | diagB pm fb g K tgt hgate hle _ih => intro hF; simp only [CimcicForbiddenC] at hF
  | axKf a b c K φ' α hgate hsz => intro hF; simp only [CimcicForbiddenC] at hF
  | boxMono a b K φ' hab hsz => intro hF; simp only [CimcicForbiddenC] at hF

/-- CIMCIC's guard against DefectBot is **not provable** within any budget `k`. -/
theorem cimcic_guard_not_provable (k : Nat) : ¬ Pf k (cimcic_guard k) := by
  intro h
  refine cimcic_no_provable_forbidden k h ?_
  show CimcicForbiddenC k (cimcic_guard k)
  unfold cimcic_guard CimcicForbiddenC CimcicForbiddenC
  exact ⟨rfl, rfl, rfl⟩

/-- `proofSearch k guard = false` — from `cimcic_guard_not_provable`. -/
theorem proofSearch_false_for_CIMCIC_vs_DefectBot (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) DefectBot) = false := by
  show proofSearch k (cimcic_guard k) = false
  cases hps : proofSearch k (cimcic_guard k) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k (cimcic_guard k)).1 hps) (cimcic_guard_not_provable k)

/-- CIMCIC defects against DefectBot: its guard fails, so it takes the `.const .D` branch. -/
theorem CIMCIC_plays_D_against_DefectBot (k fuel : Nat) :
    play (fuel + 2) (CIMCIC k) DefectBot = some .D := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) DefectBot)
          then eval (fuel + 1) (CIMCIC k) DefectBot (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) DefectBot (.const Action.D)) = some .D
  rw [proofSearch_false_for_CIMCIC_vs_DefectBot k]; simp [eval]

/-- **CIMCIC vs DefectBot: mutual defection (D, D)** — formerly the deliberately-omitted theorem,
    now PROVED with NO `atom_complete_false_guard` axiom. -/
theorem outcome_CIMCIC_vs_DefectBot :
    ∃ k, ∀ fuel, outcome (fuel + 2) (CIMCIC k) DefectBot = some (.D, .D) := by
  refine ⟨0, fun fuel => ?_⟩
  have hA : play (fuel + 2) (CIMCIC 0) DefectBot = some .D := CIMCIC_plays_D_against_DefectBot 0 fuel
  have hB : play (fuel + 2) DefectBot (CIMCIC 0) = some .D := by
    simpa using play_DefectBot (fuel + 1) (CIMCIC 0)
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
