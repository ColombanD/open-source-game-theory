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
   like any else-branch — which is why the C-play below is a play theorem (`⊨`), not a
   provability theorem (`⊢_k`), and why `probe (inst .cupodTroll T)` is 0 at every budget
   (`ps_probe_inst_cupodTroll_false`): true-but-unprovable (`⊨`, `¬ ⊢_k`) cooperation, the same
   Gödelian shape as Guardian's whole row.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## The identity guard, RESTATED (2026-08-24)

The old emission asked `.eq .opp (.bot (inst T .dupoc))` — about `.opp`, a FREE
pronoun, against a counterfactual probe. It could never fire, so this row was
uniformly `C` and the bot never did what base CupodTrollBot does. The corrected
guard asks "is the signal I am treating the lift of CupodBot?", decided from the
INDEX and witnessed by a closed `.eq` between constants (carrying a compiled
instance would re-enter the mutual-quine wall — Cupod probes CupodTroll back).

So the row now SPLITS: it defects at `.cupod` and cooperates everywhere else. -/

/-- At the recognised hypothesis the guard is `.eq .C .C` — provable by
    `Pf.eqRefl`, so the punish branch runs. -/
theorem cupodTroll_guard_true {k : Nat} (hk : 3 ≤ k) :
    proofSearch k
      ((Formula.eq (.const Action.C) (.const Action.C)).subst
        (.bot (inst (tauZoo k) .cupodTroll .cupod))
        (.bot (inst (tauZoo k) .cupodTroll .cupod)))
      = true := by
  refine (proofSearch_spec _ _).2 ?_
  show Pf k (.eq (.const Action.C) (.const Action.C))
  exact Pf.eqRefl _ (by simp only [Formula.size, Prog.size]; omega)

/-- Everywhere else it is `.eq .C .D` — refuted by `Pf.eqNeg`, so the cascade
    falls through to the trusting default. -/
theorem cupodTroll_guard_false {k : Nat} (T : Tmpl) (hT : T ≠ .cupod) :
    proofSearch k
      ((Formula.eq (.const Action.C) (.const Action.D)).subst
        (.bot (inst (tauZoo k) .cupodTroll T)) (.bot (inst (tauZoo k) .cupodTroll T)))
      = false := by
  cases h : proofSearch k
      ((Formula.eq (.const Action.C) (.const Action.D)).subst
        (.bot (inst (tauZoo k) .cupodTroll T)) (.bot (inst (tauZoo k) .cupodTroll T))) with
  | false => rfl
  | true =>
      exfalso
      have hs := proofSearch_sound _ _ h
      simp only [Formula.subst, Prog.subst, Formula.interp] at hs
      exact absurd hs (by simp)

/-- **τ(CupodTroll) DEFECTS against Cupod** — the behaviour base CupodTrollBot was
    written for, and which the old emission could not produce. -/
theorem cupodTroll_plays_D_at_cupod {k : Nat} (hk : 3 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .cupodTroll .cupod))
      (.bot (inst (tauZoo k) .cupodTroll .cupod)) (inst (tauZoo k) .cupodTroll .cupod)
      = some Action.D := by
  refine ⟨2, ?_⟩
  conv_lhs => arg 4; rw [inst_cupodTroll_peel_cupod k]
  rw [eval, cupodTroll_guard_true hk]
  rfl

/-- …and cooperates at every other hypothesis. -/
theorem cupodTroll_plays_C {k : Nat} (T : Tmpl) (hT : T ≠ .cupod) :
    ∃ N, eval N (.bot (inst (tauZoo k) .cupodTroll T))
      (.bot (inst (tauZoo k) .cupodTroll T)) (inst (tauZoo k) .cupodTroll T)
      = some Action.C := by
  refine ⟨2, ?_⟩
  conv_lhs => arg 4; rw [inst_cupodTroll_peel k T hT]
  rw [eval, cupodTroll_guard_false T hT, if_neg (by simp)]
  rfl

/-! ## The column bits

The C-cells still reach cooperation through a FAILED `.eq` search, so they stay
floor-priced (Guardian's Gödelian shape, a different route). The `.cupod` cell is
new: a FIRED guard, so its defection has a cheap positive transcript. -/

/-- The cooperation probe is floor-priced at every hypothesis but `.cupod`. -/
theorem ps_probe_inst_cupodTroll_false {k K : Nat} (hK : K ≤ k) (T : Tmpl)
    (hT : T ≠ .cupod) :
    proofSearch K (probe (inst (tauZoo k) .cupodTroll T)) = false := by
  cases h : proofSearch K (probe (inst (tauZoo k) .cupodTroll T)) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_botSearcherElse_tail k k
        (.eq (.const Action.C) (.const Action.D)) .D .C (.const .C)
        (by decide) (Nat.le_refl k)
        (.bot (inst (tauZoo k) .cupodTroll T))
        K _ ((proofSearch_spec _ _).1 h) hK
        (by simp only [probe, inst_cupodTroll_peel k T hT, TailTo_plays])

/-- Its DEFECTION probe is false off the `.cupod` cell (it truly cooperates). -/
theorem ps_probeD_inst_cupodTroll_false {k : Nat} (m : Nat) (T : Tmpl)
    (hT : T ≠ .cupod) :
    proofSearch m (probeD (inst (tauZoo k) .cupodTroll T)) = false :=
  ps_probeD_false_of_plays_C m (cupodTroll_plays_C T hT)

/-- At `.cupod` the defection IS provable — the guard fired, so `search_t` gives a
    cheap positive transcript. -/
theorem ps_probeD_inst_cupodTroll_cupod {k : Nat} (hk : 3 ≤ k)
    (hkk : c_guard k + 3 ≤ k) :
    proofSearch k (probeD (inst (tauZoo k) .cupodTroll .cupod)) = true := by
  refine (proofSearch_spec _ _).2 ?_
  rw [probeD, inst_cupodTroll_peel_cupod k]
  refine Pf.atom ⟨PlaysProof.bot (PlaysProof.search_t ?_ PlaysProof.const), ?_⟩
  · show Pf k (.eq (.const Action.C) (.const Action.C))
    exact Pf.eqRefl _ (by simp only [Formula.size, Prog.size]; omega)
  · have := hcl; have := hcn; omega

end PD.Tau
