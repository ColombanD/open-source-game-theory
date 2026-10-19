import PrisonersDilemma.Tau.Theorems.TauDIMDID.Helpers

/-!
# Tau/Theorems/TauDIMDID/Tower — the then-`D` partners (guardian, the two trolls) by the tower census (2026-10-19)

DIMDID's guard at hypothesis T is `(I defect vs I_T) → (I_T defects vs me)`. Against Guardian and
the two name-reading trolls the partner's instance COOPERATES with DIMDID (Guardian's punish-search
on `inst .dimdid .coop` fails because that instance cooperates — `dimdid_coop_plays_C`; the trolls'
identity guards are decidably false at `.dimdid`), so the consequent is their THEN-play `D`, which
`S` could only conclude from their own guard — unprovable one level down. These are DIMCID's three
tower-census proofs (`TauDIMCID/Helpers.lean`) at the other polarity: the same chains of targets,
the same dead levels; only the antecedent of DIMDID's guard carries action `D` now, so where DIMCID's
side conditions closed on an action mismatch (`C` vs `D`) these close on a PROGRAM mismatch
(`inst .dimdid T` is a `.search` on an implication; the partner's instance is a different shape).
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## guardian — three levels

Guardian's chain has three targets: DIMDID's consequent `Td₁` ("guardian plays D against me"),
guardian's guard `Yd₂` ("`inst .dimdid .coop` self-defects"), and the consequent `Zd₃` of THAT
instance's guard ("the constant cooperator defects") — whose player nothing reads, so the chain
ends. -/

/-- Level 3: the constant cooperator's defection against `inst .dimdid .coop`. -/
private abbrev Zd₃ (k : Nat) : Formula :=
  .plays (.bot (.const .C)) (.bot (inst (tauZoo k) .dimdid .coop)) Action.D

private theorem leveld3 (k : Nat) :
    ∀ K n φ, Pf K φ → TowerAt (Zd₃ k) (DeadAll []) n φ → False := by
  refine tower_census (Zd₃ k) [] ⟨Or.inl ⟨_, _, _, rfl⟩, fun Z' h => by simp at h, trivial⟩
    DeadAll_nil_kill ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro K ⟨hpp, -⟩
    cases hpp with
    | bot hin => cases hin
  · intro g ψ b c opp h; simp at h
  · intro p q opp a h; simp at h
  · intro p q opp a h; simp at h
  · intro g ψ b c opp h; simp at h
  · intro defs i opp a h; simp at h
  · intro z a' g ψ c0 c1 q opp h; simp at h
  · intro k₁ ψ₁ k₂ ψ₂ c0 c1 q opp h; simp at h
  · intro g₁ ψ₁ e₁ L a opp h; simp at h
  · intro hd L a opp h; cases hd <;> simp [ctxPlug] at h
  · intro hd L a opp h; cases hd <;> simp [plug2] at h

/-- Level 2 (guardian): guardian's guard — `inst .dimdid .coop` self-defects. -/
private abbrev Yd₂ (k : Nat) : Formula :=
  .plays (.bot (inst (tauZoo k) .dimdid .coop)) (.bot (inst (tauZoo k) .dimdid .coop)) Action.D

private theorem leveld2 (k : Nat) :
    ∀ K n φ, Pf K φ → TowerAt (Yd₂ k) (DeadAll [Zd₃ k]) n φ → False := by
  refine tower_census (Yd₂ k) [Zd₃ k]
    ⟨Or.inl ⟨_, _, _, rfl⟩, ?_, Or.inl ⟨_, _, _, rfl⟩, fun Z' h => by simp at h, trivial⟩
    (DeadAll_cons_kill (leveld3 k) DeadAll_nil_kill) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Z' h; simp only [List.mem_singleton] at h; subst h
    intro h; simp [inst_dimdid_peel_coop] at h
  · -- no certificate: the instance cooperates
    intro K h
    obtain ⟨m, hm⟩ := Pf_sound K _ (Pf.atom h)
    obtain ⟨N, hN⟩ := dimdid_coop_plays_C (k := k)
    have hN' : eval (N + 1) (.bot (inst (tauZoo k) .dimdid .coop))
        (.bot (inst (tauZoo k) .dimdid .coop)) (.bot (inst (tauZoo k) .dimdid .coop))
        = some Action.C := by rw [eval]; exact hN
    rw [play] at hm
    exact absurd (eval_det hm hN') (by decide)
  · intro g ψ b c opp h; simp [inst_dimdid_peel_coop] at h
  · intro p q opp a h; simp [inst_dimdid_peel_coop] at h
  · intro p q opp a h; simp [inst_dimdid_peel_coop] at h
  · -- THE reading rule: its box is the guard of `inst .dimdid .coop`, a level-3 formula
    intro g ψ b c opp h
    simp only [Yd₂] at h
    rw [inst_dimdid_peel_coop] at h
    simp only [Formula.plays.injEq, Prog.bot.injEq, Prog.search.injEq, Prog.const.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, -⟩ := h
    refine Or.inl ⟨1, le_rfl, (TowerAt_succ_box _ _ _ _ _).2 ?_⟩
    simp only [Formula.subst, Prog.subst, inst_coop_peel k .dimdid]
    refine (TowerAt_impl _ _ _ _ _).2 ⟨(TowerAt_zero_plays _ _ _ _ _).2 rfl, ?_, fun h => h⟩
    intro m hm hT
    have hm0 : m = 0 := by omega
    subst hm0
    have := (TowerAt_zero_plays _ _ _ _ _).1 hT
    simp [inst_dimdid_peel_coop] at this
  · intro defs i opp a h; simp [inst_dimdid_peel_coop] at h
  · intro z a' g ψ c0 c1 q opp h; simp [inst_dimdid_peel_coop] at h
  · intro k₁ ψ₁ k₂ ψ₂ c0 c1 q opp h; simp [inst_dimdid_peel_coop] at h
  · intro g₁ ψ₁ e₁ L a opp h; simp [inst_dimdid_peel_coop] at h
  · intro hd L a opp h; cases hd <;> simp [ctxPlug, inst_dimdid_peel_coop] at h
  · intro hd L a opp h; cases hd <;> simp [plug2, inst_dimdid_peel_coop] at h

/-- Level 1 (guardian): DIMDID's consequent — guardian defects against it. -/
private abbrev Td₁ (k : Nat) : Formula :=
  .plays (.bot (inst (tauZoo k) .guardian .dimdid)) (.bot (inst (tauZoo k) .dimdid .guardian))
    Action.D

/-- Guardian COOPERATES with DIMDID in DIMDID's own frame: its punish-search on
    `inst .dimdid .coop` fails. -/
private theorem guardian_plays_C_vs_dimdid (k : Nat) :
    ∃ N, eval N (.bot (inst (tauZoo k) .guardian .dimdid)) (.bot (inst (tauZoo k) .dimdid .guardian))
      (.bot (inst (tauZoo k) .guardian .dimdid)) = some Action.C := by
  have hY : proofSearch k
      ((Formula.plays (.bot (inst (tauZoo k) .dimdid .coop)) (.bot (inst (tauZoo k) .dimdid .coop))
        Action.D).subst (.bot (inst (tauZoo k) .guardian .dimdid))
        (.bot (inst (tauZoo k) .dimdid .guardian))) = false := by
    simp only [Formula.subst, Prog.subst]
    exact ps_probeD_false_of_plays_C k dimdid_coop_plays_C
  obtain ⟨N, hN⟩ := searchGuardD_plays_C (k := k)
    (.bot (inst (tauZoo k) .guardian .dimdid)) (.bot (inst (tauZoo k) .dimdid .guardian)) hY
  refine ⟨N + 1, ?_⟩
  rw [eval, inst_guardian_peel k .dimdid]
  exact hN

private theorem leveld1 (k : Nat) :
    ∀ K n φ, Pf K φ → TowerAt (Td₁ k) (DeadAll [Yd₂ k, Zd₃ k]) n φ → False := by
  refine tower_census (Td₁ k) [Yd₂ k, Zd₃ k]
    ⟨Or.inl ⟨_, _, _, rfl⟩, ?_,
     Or.inl ⟨_, _, _, rfl⟩, ?_, Or.inl ⟨_, _, _, rfl⟩, fun Z' h => by simp at h, trivial⟩
    (DeadAll_cons_kill (leveld2 k) (DeadAll_cons_kill (leveld3 k) DeadAll_nil_kill))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Z' h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · intro h; simp [inst_guardian_peel, inst_dimdid_peel_coop] at h
    · intro h; simp [inst_guardian_peel] at h
  · intro Z' h; simp only [List.mem_singleton] at h; subst h
    intro h; simp [inst_dimdid_peel_coop] at h
  · -- no certificate: guardian cooperates
    intro K h
    obtain ⟨m, hm⟩ := Pf_sound K _ (Pf.atom h)
    obtain ⟨N, hN⟩ := guardian_plays_C_vs_dimdid k
    rw [play] at hm
    exact absurd (eval_det hm hN) (by decide)
  · intro g ψ b c opp h; simp [inst_guardian_peel] at h
  · intro p q opp a h; simp [inst_guardian_peel] at h
  · intro p q opp a h; simp [inst_guardian_peel] at h
  · -- THE reading rule: guardian's box is its guard, a level-2 formula
    intro g ψ b c opp h
    simp only [Td₁] at h
    rw [inst_guardian_peel k .dimdid] at h
    simp only [Formula.plays.injEq, Prog.bot.injEq, Prog.search.injEq, Prog.const.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, -⟩ := h
    refine Or.inl ⟨1, le_rfl, (TowerAt_succ_box _ _ _ _ _).2 ?_⟩
    simp only [Formula.subst, Prog.subst]
    exact (TowerAt_zero_plays _ _ _ _ _).2 rfl
  · intro defs i opp a h; simp [inst_guardian_peel] at h
  · intro z a' g ψ c0 c1 q opp h; simp [inst_guardian_peel] at h
  · intro k₁ ψ₁ k₂ ψ₂ c0 c1 q opp h; simp [inst_guardian_peel] at h
  · intro g₁ ψ₁ e₁ L a opp h; simp [inst_guardian_peel] at h
  · intro hd L a opp h; cases hd <;> simp [ctxPlug, inst_guardian_peel] at h
  · intro hd L a opp h; cases hd <;> simp [plug2, inst_guardian_peel] at h

/-- **τ(DIMDID) at Guardian COOPERATES**: its guard is unprovable at every budget. -/
theorem dimdid_guardian_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .guardian))
      (.bot (inst (tauZoo k) .dimdid .guardian)) (inst (tauZoo k) .dimdid .guardian)
      = some Action.C := by
  have hg : proofSearch k
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .guardian .dimdid)) Action.D)
                     (.plays (.bot (inst (tauZoo k) .guardian .dimdid)) .self Action.D)).subst
        (.bot (inst (tauZoo k) .dimdid .guardian)) (.bot (inst (tauZoo k) .dimdid .guardian)))
      = false := by
    rw [ddG_subst]
    cases h : proofSearch k (ddG (.bot (inst (tauZoo k) .dimdid .guardian))
        (inst (tauZoo k) .guardian .dimdid)) with
    | false => rfl
    | true =>
        exfalso
        refine leveld1 k k 0 _ ((proofSearch_spec _ _).1 h)
          ((TowerAt_impl _ _ _ _ _).2 ⟨(TowerAt_zero_plays _ _ _ _ _).2 rfl, ?_, ?_⟩)
        · intro m hm hT
          have hm0 : m = 0 := by omega
          subst hm0
          have := (TowerAt_zero_plays _ _ _ _ _).1 hT
          simp [inst_dimdid_peel_guardian, inst_guardian_peel] at this
        · rintro (⟨m, -, hT⟩ | ⟨m, -, hT⟩ | h)
          · cases m with
            | zero =>
                have := (TowerAt_zero_plays _ _ _ _ _).1 hT
                simp [inst_dimdid_peel_guardian, inst_dimdid_peel_coop, inst_guardian_peel,
                  inst_coop_peel] at this
            | succ _ => exact TowerAt_succ_plays _ _ _ _ _ _ hT
          · cases m with
            | zero =>
                have := (TowerAt_zero_plays _ _ _ _ _).1 hT
                simp [inst_dimdid_peel_guardian] at this
            | succ _ => exact TowerAt_succ_plays _ _ _ _ _ _ hT
          · exact h
  generalize hMe : (Prog.bot (inst (tauZoo k) .dimdid .guardian)) = Me at hg ⊢
  rw [inst_dimdid_peel_guardian k]
  exact searchGuardD_plays_C _ _ hg

/-! ## cupodTroll — two levels, the second an identity atom -/

private abbrev Zt₂ : Formula := .eq (.const Action.C) (.const Action.D)

private theorem levelt2 :
    ∀ K n φ, Pf K φ → TowerAt Zt₂ (DeadAll []) n φ → False := by
  refine tower_census Zt₂ [] ⟨Or.inr ⟨_, _, by simp, rfl⟩, fun Z' h => by simp at h, trivial⟩
    DeadAll_nil_kill ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro K h; cases h
  all_goals (intros; simp_all)

private abbrev Tdc₁ (k : Nat) : Formula :=
  .plays (.bot (inst (tauZoo k) .cupodTroll .dimdid)) (.bot (inst (tauZoo k) .dimdid .cupodTroll))
    Action.D

private theorem cupodTroll_plays_C_vs_dimdid (k : Nat) :
    ∃ N, eval N (.bot (inst (tauZoo k) .cupodTroll .dimdid))
      (.bot (inst (tauZoo k) .dimdid .cupodTroll)) (.bot (inst (tauZoo k) .cupodTroll .dimdid))
      = some Action.C := by
  have hY : proofSearch k
      ((Formula.eq (.const Action.C) (.const Action.D)).subst
        (.bot (inst (tauZoo k) .cupodTroll .dimdid)) (.bot (inst (tauZoo k) .dimdid .cupodTroll)))
      = false := by
    simp only [Formula.subst, Prog.subst]
    cases hps : proofSearch k (Formula.eq (.const Action.C) (.const Action.D)) with
    | false => rfl
    | true =>
        have := Pf_sound _ _ ((proofSearch_spec _ _).1 hps)
        simp [Formula.interp] at this
  obtain ⟨N, hN⟩ := searchGuardD_plays_C (k := k)
    (.bot (inst (tauZoo k) .cupodTroll .dimdid)) (.bot (inst (tauZoo k) .dimdid .cupodTroll)) hY
  refine ⟨N + 1, ?_⟩
  rw [eval, inst_cupodTroll_peel k .dimdid (by decide)]
  exact hN

private theorem leveldc1 (k : Nat) :
    ∀ K n φ, Pf K φ → TowerAt (Tdc₁ k) (DeadAll [Zt₂]) n φ → False := by
  refine tower_census (Tdc₁ k) [Zt₂]
    ⟨Or.inl ⟨_, _, _, rfl⟩, fun Z' h => by simp only [List.mem_singleton] at h; subst h; simp,
     Or.inr ⟨_, _, by simp, rfl⟩, fun Z' h => by simp at h, trivial⟩
    (DeadAll_cons_kill levelt2 DeadAll_nil_kill) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro K h
    obtain ⟨m, hm⟩ := Pf_sound K _ (Pf.atom h)
    obtain ⟨N, hN⟩ := cupodTroll_plays_C_vs_dimdid k
    rw [play] at hm
    exact absurd (eval_det hm hN) (by decide)
  · intro g ψ b c opp h; simp [inst_cupodTroll_peel k .dimdid (by decide)] at h
  · intro p q opp a h; simp [inst_cupodTroll_peel k .dimdid (by decide)] at h
  · intro p q opp a h; simp [inst_cupodTroll_peel k .dimdid (by decide)] at h
  · intro g ψ b c opp h
    simp only [Tdc₁] at h
    rw [inst_cupodTroll_peel k .dimdid (by decide)] at h
    simp only [Formula.plays.injEq, Prog.bot.injEq, Prog.search.injEq, Prog.const.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, -⟩ := h
    refine Or.inl ⟨1, le_rfl, (TowerAt_succ_box _ _ _ _ _).2 ?_⟩
    simp only [Formula.subst, Prog.subst]
    exact (TowerAt_zero_eq _ _ _ _).2 rfl
  · intro defs i opp a h; simp [inst_cupodTroll_peel k .dimdid (by decide)] at h
  · intro z a' g ψ c0 c1 q opp h; simp [inst_cupodTroll_peel k .dimdid (by decide)] at h
  · intro k₁ ψ₁ k₂ ψ₂ c0 c1 q opp h; simp [inst_cupodTroll_peel k .dimdid (by decide)] at h
  · intro g₁ ψ₁ e₁ L a opp h; simp [inst_cupodTroll_peel k .dimdid (by decide)] at h
  · intro hd L a opp h; cases hd <;> simp [ctxPlug, inst_cupodTroll_peel k .dimdid (by decide)] at h
  · intro hd L a opp h; cases hd <;> simp [plug2, inst_cupodTroll_peel k .dimdid (by decide)] at h

/-- **τ(DIMDID) at CupodTroll COOPERATES**: its guard is unprovable at every budget. -/
theorem dimdid_cupodTroll_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .cupodTroll))
      (.bot (inst (tauZoo k) .dimdid .cupodTroll)) (inst (tauZoo k) .dimdid .cupodTroll)
      = some Action.C := by
  have hg : proofSearch k
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .cupodTroll .dimdid)) Action.D)
                     (.plays (.bot (inst (tauZoo k) .cupodTroll .dimdid)) .self Action.D)).subst
        (.bot (inst (tauZoo k) .dimdid .cupodTroll)) (.bot (inst (tauZoo k) .dimdid .cupodTroll)))
      = false := by
    rw [ddG_subst]
    cases h : proofSearch k (ddG (.bot (inst (tauZoo k) .dimdid .cupodTroll))
        (inst (tauZoo k) .cupodTroll .dimdid)) with
    | false => rfl
    | true =>
        exfalso
        refine leveldc1 k k 0 _ ((proofSearch_spec _ _).1 h)
          ((TowerAt_impl _ _ _ _ _).2 ⟨(TowerAt_zero_plays _ _ _ _ _).2 rfl, ?_, ?_⟩)
        · intro m hm hT
          have hm0 : m = 0 := by omega
          subst hm0
          have := (TowerAt_zero_plays _ _ _ _ _).1 hT
          simp [inst_dimdid_peel_cupodTroll, inst_cupodTroll_peel k .dimdid (by decide)] at this
        · rintro (⟨m, -, hT⟩ | h)
          · cases m with
            | zero => have := (TowerAt_zero_plays _ _ _ _ _).1 hT; simp at this
            | succ _ => exact TowerAt_succ_plays _ _ _ _ _ _ hT
          · exact h
  generalize hMe : (Prog.bot (inst (tauZoo k) .dimdid .cupodTroll)) = Me at hg ⊢
  rw [inst_dimdid_peel_cupodTroll k]
  exact searchGuardD_plays_C _ _ hg

/-! ## dupocTroll — the same two levels, the recognised slot being `.dupoc` -/

private abbrev Tdd₁ (k : Nat) : Formula :=
  .plays (.bot (inst (tauZoo k) .dupocTroll .dimdid)) (.bot (inst (tauZoo k) .dimdid .dupocTroll))
    Action.D

private theorem dupocTroll_plays_C_vs_dimdid (k : Nat) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dupocTroll .dimdid))
      (.bot (inst (tauZoo k) .dimdid .dupocTroll)) (.bot (inst (tauZoo k) .dupocTroll .dimdid))
      = some Action.C := by
  have hY : proofSearch k
      ((Formula.eq (.const Action.C) (.const Action.D)).subst
        (.bot (inst (tauZoo k) .dupocTroll .dimdid)) (.bot (inst (tauZoo k) .dimdid .dupocTroll)))
      = false := by
    simp only [Formula.subst, Prog.subst]
    cases hps : proofSearch k (Formula.eq (.const Action.C) (.const Action.D)) with
    | false => rfl
    | true =>
        have := Pf_sound _ _ ((proofSearch_spec _ _).1 hps)
        simp [Formula.interp] at this
  obtain ⟨N, hN⟩ := searchGuardD_plays_C (k := k)
    (.bot (inst (tauZoo k) .dupocTroll .dimdid)) (.bot (inst (tauZoo k) .dimdid .dupocTroll)) hY
  refine ⟨N + 1, ?_⟩
  rw [eval, inst_dupocTroll_peel k .dimdid (by decide)]
  exact hN

private theorem leveldd1 (k : Nat) :
    ∀ K n φ, Pf K φ → TowerAt (Tdd₁ k) (DeadAll [Zt₂]) n φ → False := by
  refine tower_census (Tdd₁ k) [Zt₂]
    ⟨Or.inl ⟨_, _, _, rfl⟩, fun Z' h => by simp only [List.mem_singleton] at h; subst h; simp,
     Or.inr ⟨_, _, by simp, rfl⟩, fun Z' h => by simp at h, trivial⟩
    (DeadAll_cons_kill levelt2 DeadAll_nil_kill) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro K h
    obtain ⟨m, hm⟩ := Pf_sound K _ (Pf.atom h)
    obtain ⟨N, hN⟩ := dupocTroll_plays_C_vs_dimdid k
    rw [play] at hm
    exact absurd (eval_det hm hN) (by decide)
  · intro g ψ b c opp h; simp [inst_dupocTroll_peel k .dimdid (by decide)] at h
  · intro p q opp a h; simp [inst_dupocTroll_peel k .dimdid (by decide)] at h
  · intro p q opp a h; simp [inst_dupocTroll_peel k .dimdid (by decide)] at h
  · intro g ψ b c opp h
    simp only [Tdd₁] at h
    rw [inst_dupocTroll_peel k .dimdid (by decide)] at h
    simp only [Formula.plays.injEq, Prog.bot.injEq, Prog.search.injEq, Prog.const.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, -⟩ := h
    refine Or.inl ⟨1, le_rfl, (TowerAt_succ_box _ _ _ _ _).2 ?_⟩
    simp only [Formula.subst, Prog.subst]
    exact (TowerAt_zero_eq _ _ _ _).2 rfl
  · intro defs i opp a h; simp [inst_dupocTroll_peel k .dimdid (by decide)] at h
  · intro z a' g ψ c0 c1 q opp h; simp [inst_dupocTroll_peel k .dimdid (by decide)] at h
  · intro k₁ ψ₁ k₂ ψ₂ c0 c1 q opp h; simp [inst_dupocTroll_peel k .dimdid (by decide)] at h
  · intro g₁ ψ₁ e₁ L a opp h; simp [inst_dupocTroll_peel k .dimdid (by decide)] at h
  · intro hd L a opp h; cases hd <;> simp [ctxPlug, inst_dupocTroll_peel k .dimdid (by decide)] at h
  · intro hd L a opp h; cases hd <;> simp [plug2, inst_dupocTroll_peel k .dimdid (by decide)] at h

/-- **τ(DIMDID) at DupocTroll COOPERATES**: its guard is unprovable at every budget. -/
theorem dimdid_dupocTroll_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .dupocTroll))
      (.bot (inst (tauZoo k) .dimdid .dupocTroll)) (inst (tauZoo k) .dimdid .dupocTroll)
      = some Action.C := by
  have hg : proofSearch k
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .dupocTroll .dimdid)) Action.D)
                     (.plays (.bot (inst (tauZoo k) .dupocTroll .dimdid)) .self Action.D)).subst
        (.bot (inst (tauZoo k) .dimdid .dupocTroll)) (.bot (inst (tauZoo k) .dimdid .dupocTroll)))
      = false := by
    rw [ddG_subst]
    cases h : proofSearch k (ddG (.bot (inst (tauZoo k) .dimdid .dupocTroll))
        (inst (tauZoo k) .dupocTroll .dimdid)) with
    | false => rfl
    | true =>
        exfalso
        refine leveldd1 k k 0 _ ((proofSearch_spec _ _).1 h)
          ((TowerAt_impl _ _ _ _ _).2 ⟨(TowerAt_zero_plays _ _ _ _ _).2 rfl, ?_, ?_⟩)
        · intro m hm hT
          have hm0 : m = 0 := by omega
          subst hm0
          have := (TowerAt_zero_plays _ _ _ _ _).1 hT
          simp [inst_dimdid_peel_dupocTroll, inst_dupocTroll_peel k .dimdid (by decide)] at this
        · rintro (⟨m, -, hT⟩ | h)
          · cases m with
            | zero => have := (TowerAt_zero_plays _ _ _ _ _).1 hT; simp at this
            | succ _ => exact TowerAt_succ_plays _ _ _ _ _ _ hT
          · exact h
  generalize hMe : (Prog.bot (inst (tauZoo k) .dimdid .dupocTroll)) = Me at hg ⊢
  rw [inst_dimdid_peel_dupocTroll k]
  exact searchGuardD_plays_C _ _ hg

end PD.Tau
