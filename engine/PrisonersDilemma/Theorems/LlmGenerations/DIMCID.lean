import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-!
# DIMCID outcomes

DIMCID ("Defect If My Cooperation Implies Defection") is

  `.search k (.impl (.plays .self .opp .C) (.plays .opp .self .D)) (.const .D) (.const .C)`

i.e. its guard is the implication "if I cooperate against the opponent, the
opponent defects against me"; if that is provable it **defects**, otherwise it
cooperates. Against opponent `X` the guard substitutes to

  `.impl (.plays (DIMCID k) X .C) (.plays X (DIMCID k) .D)`.

This is the mirror image of CIMCIC, and like CIMCIC it is made provable by the
`Pf.weakenImpl` rule (see `ProofSystem.lean` and the CIMCIC theorem file):
the implication is provable whenever its consequent is.

## The two outcomes

* **vs DefectBot — (D, D), proved below.** The consequent `.plays DefectBot
  (DIMCID k) .D` is provable (DefectBot defects against everything), so the guard
  is provable via `weakenImpl`, DIMCID's search fires, and it defects.

* **vs CooperateBot — (C, C), proved below.** The consequent `.plays CooperateBot
  (DIMCID k) .D` is *false* (CooperateBot never defects), so `weakenImpl` does not
  apply and the vacuously-true guard is *structurally unprovable*: a
  `ForbiddenD`-motive induction over `Pf` shows no constructor can conclude it,
  so `proofSearch = false` and DIMCID takes the `.const .C` else-branch. See the
  second half of the file (symmetric to CIMCIC vs DefectBot).
-/

-- DefectBot --

/-- The consequent of DIMCID's guard against DefectBot is provable: DefectBot
    defects against DIMCID. -/
theorem DIMCID_consequent_DefectBot (k : Nat) :
    Pf (atom_cost 1) (Formula.plays DefectBot (DIMCID k) Action.D) :=
  Pf.atom ⟨PlaysProof.const, by decide⟩

/-- DIMCID's guard against DefectBot is provable: `weakenImpl` turns the provable
    consequent into the implication, once `k` is large enough for the
    implication's `O(log k)` character size. -/
theorem proofSearch_true_for_DIMCID_vs_DefectBot :
    ∃ K, ∀ k, k ≥ K →
      proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
          (DIMCID k) DefectBot) = true := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 10 100
  refine ⟨K, fun k hk => ?_⟩
  refine (proofSearch_spec _ _).2 ?_
  show Pf k
    (Formula.impl (.plays (DIMCID k) DefectBot Action.C)
                  (.plays DefectBot (DIMCID k) Action.D))
  refine Pf.weakenImpl _ _ (atom_cost 1) (DIMCID_consequent_DefectBot k) ?_
  -- transcript: consequent certificate (`atom_cost 1 = 3`) + the implication's size, ≤ k.
  have hb := hK k hk
  have h1 : atom_cost 1 = 3 := by decide
  simp only [numCost, Formula.size, Prog.size, DIMCID, DefectBot]
  omega

/-- DIMCID defects against DefectBot: its guard fires (proved above), so it takes
    the `.const .D` branch. -/
theorem DIMCID_plays_D_against_DefectBot (k fuel : Nat)
    (hk : proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
          (DIMCID k) DefectBot) = true) :
    play (fuel + 2) (DIMCID k) DefectBot = some .D := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) DefectBot)
          then eval (fuel + 1) (DIMCID k) DefectBot (.const Action.D)
          else eval (fuel + 1) (DIMCID k) DefectBot (.const Action.C)) = some .D
  rw [hk]; simp [eval]

/-- DIMCID vs DefectBot: mutual defection. -/
theorem outcome_DIMCID_vs_DefectBot :
    ∃ k, ∀ fuel, outcome (fuel + 2) (DIMCID k) DefectBot = some (.D, .D) := by
  obtain ⟨K, hK⟩ := proofSearch_true_for_DIMCID_vs_DefectBot
  refine ⟨K + 1, fun fuel => ?_⟩
  have hk := hK (K + 1) (Nat.le_succ K)
  have hA : play (fuel + 2) (DIMCID (K + 1)) DefectBot = some .D :=
    DIMCID_plays_D_against_DefectBot (K + 1) fuel hk
  have hB : play (fuel + 2) DefectBot (DIMCID (K + 1)) = some .D := by
    simpa [Nat.add_comm] using play_DefectBot (fuel + 1) (DIMCID (K + 1))
  exact outcome_of_plays _ _ _ _ _ hA hB

/-!
## DIMCID vs CooperateBot — (C, C), PROVED with NO axiom

Symmetric to `outcome_CIMCIC_vs_DefectBot`. The guard `(.plays (DIMCID k) CooperateBot C) → (.plays
CooperateBot (DIMCID k) D)` is vacuously TRUE but **structurally UNPROVABLE**: its CONSEQUENT
`CooperateBot plays D` is a genuinely-FALSE atom (CooperateBot plays C), refuted by `Pf_sound`,
which blocks `weakenImpl`; a `ForbiddenD`-motive induction excludes the transparency-leaf/`implTrans`
paths. Hence `proofSearch = false`, DIMCID falls through to `.const .C`, giving (C, C). NO
`atom_complete_false_guard`. (Was deliberately omitted under the old belief that unprovability of a
true formula couldn't be certified — it can, structurally, via the false consequent.)
-/

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
