import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Base.Exclusion

/-!
# Tau/Theorems/TauDupocTroll — the Dupoc-hunting identity checker's row

The twin of `TauCupodTroll/Helpers.lean` with the recognised SOURCE moved from Cupod's to
Dupoc's. The stage is the source-decided `proveEq` guard (`Tau/Spec.lean`, 2026-10-19):
at a hypothesis whose spec is `tauDupocSpec` — `.dupoc` and the two natives — it is the
decidably true `.eq .C .C` (`Pf.eqRefl`), so the punish branch runs and the troll
DEFECTS; at every other hypothesis it is the decidably false `.eq .C .D` (`Pf.eqNeg`), so
the cascade falls through and the troll cooperates.

As for CupodTroll, the C-cells reach cooperation through a FAILED `.eq` search, so they
stay floor-priced in `S` (`ps_probe_inst_dupocTroll_false`): true-but-unprovable
cooperation. The difference that matters downstream: the recognised partners are
self-probers whose probe of the troll's instance is therefore FALSE rather than
floor-priced — Dupoc (and its native twins) defect on the troll by soundness, a theorem bit
where `dupoc × cupodTroll` is a floor bit.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- The recognised guard `.eq .C .C` is provable by `Pf.eqRefl` in every frame. -/
theorem dupocTroll_guard_true {k : Nat} (hk : 3 ≤ k) (T : Tmpl) :
    proofSearch k
      ((Formula.eq (.const Action.C) (.const Action.C)).subst
        (.bot (inst (tauZoo k) .dupocTroll T)) (.bot (inst (tauZoo k) .dupocTroll T)))
      = true := by
  refine (proofSearch_spec _ _).2 ?_
  show Pf k (.eq (.const Action.C) (.const Action.C))
  exact Pf.eqRefl _ (by simp only [Formula.size, Prog.size]; omega)

/-- The unrecognised guard `.eq .C .D` is refuted by `Pf.eqNeg` in every frame. -/
theorem dupocTroll_guard_false {k : Nat} (T : Tmpl) :
    proofSearch k
      ((Formula.eq (.const Action.C) (.const Action.D)).subst
        (.bot (inst (tauZoo k) .dupocTroll T)) (.bot (inst (tauZoo k) .dupocTroll T)))
      = false := by
  cases h : proofSearch k
      ((Formula.eq (.const Action.C) (.const Action.D)).subst
        (.bot (inst (tauZoo k) .dupocTroll T)) (.bot (inst (tauZoo k) .dupocTroll T))) with
  | false => rfl
  | true =>
      exfalso
      have hs := proofSearch_sound _ _ h
      simp only [Formula.subst, Prog.subst, Formula.interp] at hs
      exact absurd hs (by simp)

/-- **τ(DupocTroll) DEFECTS on every hypothesis with Dupoc's source** — base
    DupocTrollBot's whole point. -/
theorem dupocTroll_plays_D_at {k : Nat} (hk : 3 ≤ k) (T : Tmpl) (hT : tmplSpec T = tauDupocSpec) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dupocTroll T))
      (.bot (inst (tauZoo k) .dupocTroll T)) (inst (tauZoo k) .dupocTroll T)
      = some Action.D := by
  refine ⟨2, ?_⟩
  conv_lhs => arg 4; rw [inst_dupocTroll_peel_rec k T hT]
  rw [eval, dupocTroll_guard_true hk T]
  rfl

theorem dupocTroll_plays_D_at_dupoc {k : Nat} (hk : 3 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dupocTroll .dupoc))
      (.bot (inst (tauZoo k) .dupocTroll .dupoc)) (inst (tauZoo k) .dupocTroll .dupoc)
      = some Action.D :=
  dupocTroll_plays_D_at hk .dupoc rfl

/-- …and cooperates at every other hypothesis. -/
theorem dupocTroll_plays_C {k : Nat} (T : Tmpl) (hT : tmplSpec T ≠ tauDupocSpec) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dupocTroll T))
      (.bot (inst (tauZoo k) .dupocTroll T)) (inst (tauZoo k) .dupocTroll T)
      = some Action.C := by
  refine ⟨2, ?_⟩
  conv_lhs => arg 4; rw [inst_dupocTroll_peel k T hT]
  rw [eval, dupocTroll_guard_false T, if_neg (by simp)]
  rfl

/-! ## The column bits -/

/-- The cooperation probe is floor-priced at every unrecognised hypothesis. -/
theorem ps_probe_inst_dupocTroll_false {k K : Nat} (hK : K ≤ k) (T : Tmpl)
    (hT : tmplSpec T ≠ tauDupocSpec) :
    proofSearch K (probe (inst (tauZoo k) .dupocTroll T)) = false := by
  cases h : proofSearch K (probe (inst (tauZoo k) .dupocTroll T)) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_botSearcherElse_tail k k
        (.eq (.const Action.C) (.const Action.D)) .D .C (.const .C)
        (by decide) (Nat.le_refl k)
        (.bot (inst (tauZoo k) .dupocTroll T))
        K _ ((proofSearch_spec _ _).1 h) hK
        (by simp only [probe, inst_dupocTroll_peel k T hT, TailTo_plays])

/-- At a recognised hypothesis the cooperation probe is FALSE outright (the troll defects). -/
theorem ps_probe_inst_dupocTroll_rec_false {k : Nat} (hk : 3 ≤ k) (m : Nat) (T : Tmpl)
    (hT : tmplSpec T = tauDupocSpec) :
    proofSearch m (probe (inst (tauZoo k) .dupocTroll T)) = false :=
  ps_probe_false_of_plays_D m (dupocTroll_plays_D_at hk T hT)

theorem ps_probe_inst_dupocTroll_dupoc_false {k : Nat} (hk : 3 ≤ k) (m : Nat) :
    proofSearch m (probe (inst (tauZoo k) .dupocTroll .dupoc)) = false :=
  ps_probe_inst_dupocTroll_rec_false hk m .dupoc rfl

/-- Its DEFECTION probe is false at every unrecognised hypothesis (it truly cooperates). -/
theorem ps_probeD_inst_dupocTroll_false {k : Nat} (m : Nat) (T : Tmpl)
    (hT : tmplSpec T ≠ tauDupocSpec) :
    proofSearch m (probeD (inst (tauZoo k) .dupocTroll T)) = false :=
  ps_probeD_false_of_plays_C m (dupocTroll_plays_C T hT)

/-- At a recognised hypothesis the defection IS provable — the guard fired, so `search_t`
    gives a cheap positive transcript. -/
theorem ps_probeD_inst_dupocTroll_rec {k : Nat} (hk : 3 ≤ k)
    (hkk : 3 * c_guard k + 22 ≤ k) (T : Tmpl) (hT : tmplSpec T = tauDupocSpec) :
    proofSearch k (probeD (inst (tauZoo k) .dupocTroll T)) = true := by
  refine (proofSearch_spec _ _).2 ?_
  rw [probeD, inst_dupocTroll_peel_rec k T hT]
  refine Pf.atom ⟨PlaysProof.bot (PlaysProof.search_t ?_ PlaysProof.const), ?_⟩
  · show Pf k (.eq (.const Action.C) (.const Action.C))
    exact Pf.eqRefl _ (by simp only [Formula.size, Prog.size]; omega)
  · have := hcl; have := hcn
    simp only [c_guard, numCost, Formula.size, Prog.size] at hkk ⊢
    omega

end PD.Tau
