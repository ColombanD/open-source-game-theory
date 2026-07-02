import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.SizeLemmas

open PD
open PD.Axioms
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-!
# CIMCIC outcomes

CIMCIC ("Cooperate If My Cooperation Implies Cooperation") is

  `.search k (.impl (.plays .self .opp .C) (.plays .opp .self .C)) (.const .C) (.const .D)`

i.e. its guard is the **implication** "if I cooperate against the opponent, the
opponent cooperates against me". Against opponent `X` the guard substitutes to

  `.impl (.plays (CIMCIC k) X .C) (.plays X (CIMCIC k) .C)`.

## What made this provable: the `weakenImpl` rule

Proving an *implication* guard requires building a proof of `.impl A B` at the
`Provable` level. The original proof system had no way to introduce an implication
from a true consequent — `Derivation` only had `modusPonens`, `hypSyll`,
`searchBranch`, `simStep`, `eqRefl`, none of which produces `.impl A B` from a
proof of `B`. (This is precisely why the earlier automated attempt at CIMCIC
failed.)

We added the sound, faithful rule `Provable.weakenImpl` (in `Derivation.lean`):
from `Provable m ψ` conclude `Provable k (.impl φ ψ)` whenever the conclusion's
character size fits `k`. It is sound because `interp (.impl φ ψ) = φ.interp →
ψ.interp`, which follows from `ψ.interp` by `fun _ => ·`; it is faithful because a
PA-like `S` always proves `ψ ⊢ φ → ψ`.

## The two outcomes

* **vs CooperateBot — (C, C), proved below.** The consequent `.plays CooperateBot
  (CIMCIC k) .C` is provable (CooperateBot cooperates with everything), so the
  guard is provable via `weakenImpl`, CIMCIC's search fires, and it cooperates.

* **vs DefectBot — NOT provable, by design (incompleteness boundary).** Here the
  consequent `.plays DefectBot (CIMCIC k) .C` is *false* (DefectBot never plays C),
  so `weakenImpl` does not apply. The implication is nonetheless *semantically
  true* — its antecedent `.plays (CIMCIC k) DefectBot .C` is false (CIMCIC defects
  against DefectBot), so it holds vacuously. To make CIMCIC *defect* against
  DefectBot we would need `proofSearch k guard = false`, i.e. to certify that this
  true-but-vacuous implication is **unprovable** within budget `k`. That is a Π₁
  statement about the oracle's incompleteness, which the sound rules cannot
  establish (the `= false` direction is discharged by refuting `guard.interp`, but
  here `guard.interp` is *true*). So CIMCIC vs DefectBot sits on the genuine
  incompleteness boundary and is deliberately left unproved. See the note at the
  bottom of the file.
-/

-- CooperateBot --

/-- The consequent of CIMCIC's guard against CooperateBot is provable at any large
    enough budget: CooperateBot cooperates with CIMCIC. -/
theorem CIMCIC_consequent_CooperateBot (k : Nat) :
    Provable (atom_cost 1) (Formula.plays CooperateBot (CIMCIC k) Action.C) :=
  Provable.atom ⟨PlaysProof.const, by decide⟩

/-- CIMCIC's guard against CooperateBot is provable: the `weakenImpl` rule turns
    the provable consequent into the implication, once the budget `k` is large
    enough to hold the implication's character size (`O(log k)`, by
    `linear_log2_add_le`). -/
theorem proofSearch_true_for_CIMCIC_vs_CooperateBot :
    ∃ K, ∀ k, k ≥ K →
      proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) CooperateBot) = true := by
  -- The substituted guard is `.impl (.plays (CIMCIC k) CooperateBot .C)
  --                                  (.plays CooperateBot (CIMCIC k) .C)`.
  -- Its size is `5 * log2 k + C` for a constant `C` (CIMCIC k costs `log2 k + …`),
  -- so `linear_log2_add_le` gives a `K` past which it fits within budget `k`.
  -- We pick a generous linear bound and discharge the exact size goal with `omega`.
  obtain ⟨K, hK⟩ := linear_log2_add_le 10 100
  refine ⟨K, fun k hk => ?_⟩
  refine (proofSearch_spec _ _).2 ?_
  show Provable k
    (Formula.impl (.plays (CIMCIC k) CooperateBot Action.C)
                  (.plays CooperateBot (CIMCIC k) Action.C))
  refine Provable.weakenImpl _ _ (atom_cost 1) (CIMCIC_consequent_CooperateBot k) ?_
  -- transcript: consequent certificate (`atom_cost 1 = 3`) + the implication's size, ≤ k.
  have hb := hK k hk
  have h1 : atom_cost 1 = 3 := by decide
  simp only [Formula.size, Prog.size, CIMCIC, CooperateBot]
  omega

/-- CIMCIC cooperates against CooperateBot: its guard fires (proved above), so it
    takes the `.const .C` branch. -/
theorem CIMCIC_plays_C_against_CooperateBot (k fuel : Nat)
    (hk : proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) CooperateBot) = true) :
    play (fuel + 2) (CIMCIC k) CooperateBot = some .C := by
  -- One eval step: the guard `proofSearch` argument is definitionally the
  -- substituted implication that `hk` proves true, so the search takes the
  -- `.const .C` branch.
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) CooperateBot)
          then eval (fuel + 1) (CIMCIC k) CooperateBot (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) CooperateBot (.const Action.D)) = some .C
  rw [hk]; simp [eval]

/-- CIMCIC vs CooperateBot: mutual cooperation. -/
theorem CIMCIC_vs_CooperateBot :
    ∃ k, ∀ fuel, outcome (fuel + 2) (CIMCIC k) CooperateBot = some (.C, .C) := by
  obtain ⟨K, hK⟩ := proofSearch_true_for_CIMCIC_vs_CooperateBot
  refine ⟨K + 1, fun fuel => ?_⟩
  have hk := hK (K + 1) (Nat.le_succ K)
  have hA : play (fuel + 2) (CIMCIC (K + 1)) CooperateBot = some .C :=
    CIMCIC_plays_C_against_CooperateBot (K + 1) fuel hk
  have hB : play (fuel + 2) CooperateBot (CIMCIC (K + 1)) = some .C := by
    simpa [Nat.add_comm] using play_CooperateBot (fuel + 1) (CIMCIC (K + 1))
  exact outcome_of_plays _ _ _ _ _ hA hB

/-!
## CIMCIC vs DefectBot — (D, D), PROVED with NO axiom

The guard `(.plays (CIMCIC k) DefectBot C) → (.plays DefectBot (CIMCIC k) C)` is vacuously TRUE
(both antecedent and consequent false) but **structurally UNPROVABLE** within `S`. An earlier note
left this "deliberately omitted" believing unprovability of a *true* formula could not be certified.
It can — not by the `interp`-refutation route (the implication's interp IS true), but by a
**structural exclusion**: NO `Provable` constructor concludes this implication. The KEY is that the
implication's CONSEQUENT (`DefectBot plays C`) is a genuinely-FALSE atom — refuted by
`Provable_sound` — which blocks the only realistic path (`weakenImpl`, which needs the consequent
provable). Combined with a `ForbiddenC`-motive induction excluding the `Derivation` and `implTrans`
paths, this gives `¬ Provable k guard`, hence `proofSearch = false`, hence CIMCIC defects.

This does NOT use `atom_complete_false_guard`. The `.impl`-guard false case is genuinely
dischargeable BECAUSE its consequent is a false atom; contrast the play-atom false guards
(DupocBot/JustBot/…) whose guard is a play-atom with no such handle.
-/

/-- The substituted CIMCIC guard against DefectBot. -/
abbrev cimcic_guard (k : Nat) : Formula :=
  .impl (.plays (CIMCIC k) DefectBot Action.C) (.plays DefectBot (CIMCIC k) Action.C)

/-- The consequent atom `DefectBot plays C vs CIMCIC` is genuinely UNPROVABLE: DefectBot plays D,
    so its `interp` is false, refuted by `Provable_sound`. -/
theorem cimcic_consequent_not_provable (k m : Nat) :
    ¬ Provable m (.plays DefectBot (CIMCIC k) Action.C) := by
  intro h
  obtain ⟨n, hn⟩ := Provable_sound m _ h
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

/-- No `Derivation` concludes `.impl _ (false-consequent)`: leaf rules need the consequent-subject
    `DefectBot` (= `.const D`) to be `.sim`/`.ite`/`.search`; `modusPonens`/`hypSyll` recurse. -/
theorem cimcic_no_deriv_forbidden (k : Nat) : ∀ {φ}, Derivation φ → ¬ CimcicForbiddenC k φ := by
  intro φ d
  induction d with
  | modusPonens _ _ _ _ ihimpl _ => intro hF; exact ihimpl hF
  | hypSyll _ _ _ _ _ _ ihbc => intro hF; exact ihbc hF
  | searchBranch _ _ _ _ _ _ hme => intro hF; subst hme; simp only [CimcicForbiddenC] at hF
                                    obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | simStep _ _ _ _ _ hme => intro hF; subst hme; simp only [CimcicForbiddenC] at hF
                             obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | botSimStep _ _ _ _ _ hme => intro hF; subst hme; simp only [CimcicForbiddenC] at hF
                                obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | botSearchStep _ _ _ _ _ _ hme => intro hF; subst hme; simp only [CimcicForbiddenC] at hF
                                     obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | iteBranchSearch_t _ _ _ _ _ _ _ _ _ hme => intro hF; subst hme; simp only [CimcicForbiddenC] at hF
                                               obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | eqRefl _ => intro hF; simp only [CimcicForbiddenC] at hF
  | eqNeg _ _ _ => intro hF; simp only [CimcicForbiddenC] at hF

/-- No `Provable` concludes `.impl _ (false-consequent)` — covers `weakenImpl` + `implTrans` + the
    rest. By `Provable.rec`; the `atom` case bottoms out on `cimcic_consequent_not_provable`. -/
theorem cimcic_no_provable_forbidden (k : Nat) :
    ∀ {m φ}, Provable m φ → ¬ CimcicForbiddenC k φ := by
  intro m φ h
  exact Provable.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ φ _ => ¬ CimcicForbiddenC k φ)
    trivial (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial)
    (fun {_k} {_φ} hd => by intro hF; obtain ⟨d, _⟩ := hd; exact cimcic_no_deriv_forbidden k d hF)
    (fun {_k} {_φ} hatom _ => by
        intro hF
        cases hatom with
        | mk cert hle =>
            simp only [CimcicForbiddenC] at hF; obtain ⟨hp, hq, ha⟩ := hF
            subst hp; subst hq; subst ha
            exact cimcic_consequent_not_provable k _ (Provable.atom (.mk cert hle)))
    (fun _ _ _ _ _ ih => by intro hF; exact ih hF)                               -- weakenImpl
    (fun {_k} _k₁ _k₂ _m _ψ₁ _ψ₂ _c0 _c1 _q _me _opp hme _hprud _hmk _hle _ih => by      -- searchThenSearch_t
        intro hF; subst hme; simp only [CimcicForbiddenC] at hF
        obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm)
    (fun _φ _ψ _χ _a _b _hab _hbc _hle _ihab ihbc => by intro hF; exact ihbc hF)  -- implTrans
    (fun {_k} _ _ _ _ _ _ _ => by intro hF; simp only [CimcicForbiddenC] at hF)  -- atomBoxImpl
    (fun _kIn _K _φ _hprem _hle _ih => by intro hF; simp only [CimcicForbiddenC] at hF)  -- boxIntro
    -- app: conclusion `α`; `CimcicForbiddenC (φ'→α) = CimcicForbiddenC α`, so the IH on the
    -- IMPLICATION premise discharges the conclusion `α`.
    (fun _k _m₁ _m₂ _φ' _α _himpl _hante _hle ihimpl _ihante => by intro hF; exact ihimpl hF)  -- app
    -- axK: conclusion `□_bφ→□_cα`; `CimcicForbiddenC` peels `.impl` to `□α`, then `.box → False`.
    (fun _a _b _c _m _K _φ _α _hprem _hgate _hle _ih => by
        intro hF; simp only [CimcicForbiddenC] at hF)                             -- axK
    (fun _a _b _K _φ _hgate _hsz => by intro hF; simp only [CimcicForbiddenC] at hF)  -- box4
    -- diagF: conclusion peels to `CimcicForbiddenC tgt`; the LÖB-PREMISE GATE's IH peels to the same — contradiction.
    (fun _pm _fb _g _K _tgt _hgate _hle ih => by intro hF; exact ih hF)           -- diagF (gated)
    -- diagB: conclusion peels to `CimcicForbiddenC (.diag …)` = False (catch-all).
    (fun _pm _fb _g _K _tgt _hgate _hle _ih => by
        intro hF; simp only [CimcicForbiddenC] at hF)                             -- diagB
    -- axKf: conclusion peels to `.box` = False.
    (fun _a _b _c _K _φ _α _hgate _hsz => by intro hF; simp only [CimcicForbiddenC] at hF)  -- axKf
    -- impS2: conclusion `φ→χ` peels to `CimcicForbiddenC χ`; IH on premise-1 `φ→(ψ→χ)` peels to the same.
    (fun _φ _ψ _χ _m₁ _m₂ _K _h1 _h2 _hle ih1 _ih2 => by intro hF; exact ih1 hF)  -- impS2
    -- boxMono: conclusion `□_aφ→□_bφ` peels to `.box` = False.
    (fun _a _b _K _φ _hab _hsz => by intro hF; simp only [CimcicForbiddenC] at hF)  -- boxMono
    -- atomNeg: conclusion `.neg` = False (catch-all).
    (fun _p _q _b _aN _m _hatom _hne _hle _ih => by
        intro hF; simp only [CimcicForbiddenC] at hF)                               -- atomNeg
    h

/-- CIMCIC's guard against DefectBot is **not provable** within any budget `k`. -/
theorem cimcic_guard_not_provable (k : Nat) : ¬ Provable k (cimcic_guard k) := by
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
theorem CIMCIC_vs_DefectBot :
    ∃ k, ∀ fuel, outcome (fuel + 2) (CIMCIC k) DefectBot = some (.D, .D) := by
  refine ⟨0, fun fuel => ?_⟩
  have hA : play (fuel + 2) (CIMCIC 0) DefectBot = some .D := CIMCIC_plays_D_against_DefectBot 0 fuel
  have hB : play (fuel + 2) DefectBot (CIMCIC 0) = some .D := by
    simpa using play_DefectBot (fuel + 1) (CIMCIC 0)
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
