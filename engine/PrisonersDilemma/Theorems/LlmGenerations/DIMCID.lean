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
`Provable.weakenImpl` rule (see `Derivation.lean` and the CIMCIC theorem file):
the implication is provable whenever its consequent is.

## The two outcomes

* **vs DefectBot — (D, D), proved below.** The consequent `.plays DefectBot
  (DIMCID k) .D` is provable (DefectBot defects against everything), so the guard
  is provable via `weakenImpl`, DIMCID's search fires, and it defects.

* **vs CooperateBot — NOT provable, by design (incompleteness boundary).** The
  consequent `.plays CooperateBot (DIMCID k) .D` is *false* (CooperateBot never
  defects), so `weakenImpl` does not apply. The implication is semantically true
  vacuously, so making DIMCID *cooperate* (take the else-branch) would require
  certifying the guard *unprovable* — a Π₁ statement the sound rules cannot
  establish. Deliberately left unproved; see the bottom of the file (symmetric to
  CIMCIC vs DefectBot).
-/

-- DefectBot --

/-- The consequent of DIMCID's guard against DefectBot is provable: DefectBot
    defects against DIMCID. -/
theorem DIMCID_consequent_DefectBot (k : Nat) :
    Provable (atom_cost 1) (Formula.plays DefectBot (DIMCID k) Action.D) :=
  Provable.atom ⟨PlaysProof.const, by decide⟩

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
  show Provable k
    (Formula.impl (.plays (DIMCID k) DefectBot Action.C)
                  (.plays DefectBot (DIMCID k) Action.D))
  refine Provable.weakenImpl _ _ (atom_cost 1) (DIMCID_consequent_DefectBot k) ?_
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
`CooperateBot plays D` is a genuinely-FALSE atom (CooperateBot plays C), refuted by `Provable_sound`,
which blocks `weakenImpl`; a `ForbiddenD`-motive induction excludes the `Derivation`/`implTrans`
paths. Hence `proofSearch = false`, DIMCID falls through to `.const .C`, giving (C, C). NO
`atom_complete_false_guard`. (Was deliberately omitted under the old belief that unprovability of a
true formula couldn't be certified — it can, structurally, via the false consequent.)
-/

/-- The substituted DIMCID guard against CooperateBot. -/
abbrev dimcid_guard (k : Nat) : Formula :=
  .impl (.plays (DIMCID k) CooperateBot Action.C) (.plays CooperateBot (DIMCID k) Action.D)

/-- The consequent atom `CooperateBot plays D vs DIMCID` is UNPROVABLE: CooperateBot plays C. -/
theorem dimcid_consequent_not_provable (k m : Nat) :
    ¬ Provable m (.plays CooperateBot (DIMCID k) Action.D) := by
  intro h
  obtain ⟨n, hn⟩ := Provable_sound m _ h
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

theorem dimcid_no_deriv_forbidden (k : Nat) : ∀ {φ}, Derivation φ → ¬ DimcidForbiddenD k φ := by
  intro φ d
  induction d with
  | modusPonens _ _ _ _ ihimpl _ => intro hF; exact ihimpl hF
  | hypSyll _ _ _ _ _ _ ihbc => intro hF; exact ihbc hF
  | searchBranch _ _ _ _ _ _ hme => intro hF; subst hme; simp only [DimcidForbiddenD] at hF
                                    obtain ⟨hm, _, _⟩ := hF; simp [CooperateBot] at hm
  | simStep _ _ _ _ _ hme => intro hF; subst hme; simp only [DimcidForbiddenD] at hF
                             obtain ⟨hm, _, _⟩ := hF; simp [CooperateBot] at hm
  | botSimStep _ _ _ _ _ hme => intro hF; subst hme; simp only [DimcidForbiddenD] at hF
                                obtain ⟨hm, _, _⟩ := hF; simp [CooperateBot] at hm
  | botSearchStep _ _ _ _ _ _ hme => intro hF; subst hme; simp only [DimcidForbiddenD] at hF
                                     obtain ⟨hm, _, _⟩ := hF; simp [CooperateBot] at hm
  | iteBranchSearch_t _ _ _ _ _ _ _ _ _ hme => intro hF; subst hme; simp only [DimcidForbiddenD] at hF
                                               obtain ⟨hm, _, _⟩ := hF; simp [CooperateBot] at hm
  | eqRefl _ => intro hF; simp only [DimcidForbiddenD] at hF
  | eqNeg _ _ _ => intro hF; simp only [DimcidForbiddenD] at hF

theorem dimcid_no_provable_forbidden (k : Nat) :
    ∀ {m φ}, Provable m φ → ¬ DimcidForbiddenD k φ := by
  intro m φ h
  exact Provable.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ φ _ => ¬ DimcidForbiddenD k φ)
    trivial (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial)
    (fun {_k} {_φ} hd => by intro hF; obtain ⟨d, _⟩ := hd; exact dimcid_no_deriv_forbidden k d hF)
    (fun {_k} {_φ} hatom _ => by
        intro hF
        cases hatom with
        | mk cert hle =>
            simp only [DimcidForbiddenD] at hF; obtain ⟨hp, hq, ha⟩ := hF
            subst hp; subst hq; subst ha
            exact dimcid_consequent_not_provable k _ (Provable.atom (.mk cert hle)))
    (fun _ _ _ _ _ ih => by intro hF; exact ih hF)
    (fun {_k} _k₁ _k₂ _m _ψ₁ _ψ₂ _c0 _c1 _q _me _opp hme _hprud _hmk _hle _ih => by
        intro hF; subst hme; simp only [DimcidForbiddenD] at hF
        obtain ⟨hm, _, _⟩ := hF; simp [CooperateBot] at hm)
    (fun _φ _ψ _χ _a _b _hab _hbc _hle _ihab ihbc => by intro hF; exact ihbc hF)
    (fun {_k} _ _ _ _ _ _ _ => by intro hF; simp only [DimcidForbiddenD] at hF)
    (fun _kIn _K _φ _hprem _hle _ih => by intro hF; simp only [DimcidForbiddenD] at hF)  -- boxIntro
    (fun _k _m₁ _m₂ _φ' _α _himpl _hante _hle ihimpl _ihante => by intro hF; exact ihimpl hF)  -- app
    (fun _a _b _c _m _K _φ _α _hprem _hgate _hle _ih => by
        intro hF; simp only [DimcidForbiddenD] at hF)                             -- axK
    (fun _a _b _K _φ _hgate _hsz => by intro hF; simp only [DimcidForbiddenD] at hF)  -- box4
    -- diagF: conclusion peels to `DimcidForbiddenD tgt`; the LÖB-PREMISE GATE's IH peels to the same — contradiction.
    (fun _pm _fb _g _K _tgt _hgate _hle ih => by intro hF; exact ih hF)           -- diagF (gated)
    -- diagB: conclusion peels to `DimcidForbiddenD (.diag …)` = False (catch-all).
    (fun _pm _fb _g _K _tgt _hgate _hle _ih => by
        intro hF; simp only [DimcidForbiddenD] at hF)                             -- diagB
    -- axKf: conclusion peels to `.box` = False.
    (fun _a _b _c _K _φ _α _hgate _hsz => by intro hF; simp only [DimcidForbiddenD] at hF)  -- axKf
    -- impS2: conclusion `φ→χ` peels to `DimcidForbiddenD χ`; IH on premise-1 `φ→(ψ→χ)` peels to the same.
    (fun _φ _ψ _χ _m₁ _m₂ _K _h1 _h2 _hle ih1 _ih2 => by intro hF; exact ih1 hF)  -- impS2
    -- boxMono: conclusion `□_aφ→□_bφ` peels to `.box` = False.
    (fun _a _b _K _φ _hab _hsz => by intro hF; simp only [DimcidForbiddenD] at hF)  -- boxMono
    -- atomNeg: conclusion `.neg` = False (catch-all).
    (fun _p _q _b _aN _m _hatom _hne _hle _ih => by
        intro hF; simp only [DimcidForbiddenD] at hF)                               -- atomNeg
    h

theorem dimcid_guard_not_provable (k : Nat) : ¬ Provable k (dimcid_guard k) := by
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
