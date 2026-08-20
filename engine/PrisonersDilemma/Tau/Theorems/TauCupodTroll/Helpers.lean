import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Base.Exclusion

/-!
# Tau/Theorems/TauCupodTroll — the identity-checker's row

τ(CupodTrollBot) asks a question no other bot in the zoo asks: **structural
identity**. Its stage is `.eq .opp (.bot (inst T .dupoc))`, and in the entry frame
`.opp` substitutes to the entry itself, so the guard reads

    "is `inst T .cupodTroll` literally the term `inst T .dupoc`?"

which is decidably FALSE for every hypothesis — the two are different compiled
cascades. So every stage falls through to the trusting default and τ(CupodTroll)
plays C at every hypothesis, INCLUDING itself.

**Two honest observations, recorded rather than hidden.**

1. **The row is uniformly C, so the bot is behaviorally constant ON THIS ZOO.** That
   is not a defect of the lift: base CupodTrollBot defects only against CupodBot,
   and CupodBot is `.sys`-blocked, hence absent. The row will change shape exactly
   when CupodBot lands — the lift is faithful to a bot whose one target is missing.
2. **The identity guard is the only one in the zoo that is decidable in BOTH
   directions** (`Pf.eqRefl` / `Pf.eqNeg`), so its bits are never floor-priced.
   Nonetheless the FALL is via `search_f` and therefore pays the failed-search floor
   like any else-branch — which is why the C-play below is a play theorem, not a
   provability theorem, and why `probe (inst .cupodTroll T)` is 0 at every budget
   (`ps_probe_inst_cupodTroll_false`): true-but-unprovable cooperation, the same
   Gödelian shape as Guardian's whole row.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- The identity guard is REFUTABLE: the two compiled instances are distinct terms,
    so `.eq` fails and its negation is provable — the `search_f` route. -/
theorem cupodTroll_guard_false {k : Nat} (T : Tmpl) :
    proofSearch k
      ((Formula.eq .opp (.bot (inst (tauZoo k) T .dupoc))).subst
        (.bot (inst (tauZoo k) .cupodTroll T)) (.bot (inst (tauZoo k) .cupodTroll T)))
      = false := by
  cases h : proofSearch k
      ((Formula.eq .opp (.bot (inst (tauZoo k) T .dupoc))).subst
        (.bot (inst (tauZoo k) .cupodTroll T)) (.bot (inst (tauZoo k) .cupodTroll T))) with
  | false => rfl
  | true =>
      exfalso
      have hs := proofSearch_sound _ _ h
      simp only [Formula.subst, Prog.subst, Formula.interp, inst_cupodTroll_peel] at hs
      -- `hs` says a `.search` node EQUALS the very term sitting inside its own guard.
      -- Impossible by SIZE: a program is strictly larger than any of its subterms.
      have hsz := congrArg Prog.size (Prog.bot.inj hs)
      simp only [Prog.size, Formula.size, numCost] at hsz
      omega

/-- τ(CupodTroll) plays C at every hypothesis: the identity check fails and the
    cascade falls to its trusting default. -/
theorem cupodTroll_plays_C {k : Nat} (T : Tmpl) :
    ∃ N, eval N (.bot (inst (tauZoo k) .cupodTroll T))
      (.bot (inst (tauZoo k) .cupodTroll T)) (inst (tauZoo k) .cupodTroll T)
      = some Action.C := by
  refine ⟨2, ?_⟩
  -- Unfold ONE compile level in the BODY slot only. A bare `rw` would also rewrite
  -- the two FRAME slots (they are syntactically the same term), after which the
  -- guard lemma — stated with `inst …` frames — no longer matches. `conv` targets
  -- the third argument alone.
  conv_lhs => arg 4; rw [inst_cupodTroll_peel k T]
  rw [eval, cupodTroll_guard_false T, if_neg (by simp)]
  rfl

/-! ## The column bits — a floor row

`inst .cupodTroll T` reaches C through a FAILED `.eq` search, so every certificate
must cross `search_f` and pay the full failed budget. The identity guard being
decidable does not help: it is decidably FALSE, and the fall is what costs. So the
prover columns read 0 over a TRUE cooperation — Guardian's Gödelian shape again,
reached by a different route. -/

/-- The cooperation probe is FALSE-free but floor-priced: unprovable at every
    budget ≤ k. -/
theorem ps_probe_inst_cupodTroll_false {k K : Nat} (hK : K ≤ k) (T : Tmpl) :
    proofSearch K (probe (inst (tauZoo k) .cupodTroll T)) = false := by
  cases h : proofSearch K (probe (inst (tauZoo k) .cupodTroll T)) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_botSearcherElse_tail k k
        (.eq .opp (.bot (inst (tauZoo k) T .dupoc))) .D .C (.const .C)
        (by decide) (Nat.le_refl k)
        (.bot (inst (tauZoo k) .cupodTroll T))
        K _ ((proofSearch_spec _ _).1 h) hK
        (by simp only [probe, inst_cupodTroll_peel k T, TailTo_plays])

/-- Its DEFECTION probe is false too — it truly cooperates (eval determinism). -/
theorem ps_probeD_inst_cupodTroll_false {k : Nat} (m : Nat) (T : Tmpl) :
    proofSearch m (probeD (inst (tauZoo k) .cupodTroll T)) = false :=
  ps_probeD_false_of_plays_C m (cupodTroll_plays_C T)

end PD.Tau
