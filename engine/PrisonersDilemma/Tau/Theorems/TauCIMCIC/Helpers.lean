import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Tau.Theorems.TauCupod.Helpers
import PrisonersDilemma.Tau.Theorems.TauEBot.Helpers

/-!
# Tau/Theorems/TauCIMCIC/Helpers — the first `.impl`-guard row

τ(CIMCIC)'s guard at hypothesis T is `me coops with I_T → I_T coops with me`
(`cimG`), searched at budget k. The row's mathematics splits by what the
CONSEQUENT — "the partner's instance cooperates with me" — costs to certify:

* **provable** (coop, tftSim, tftPf, just, the diagonal): `weakenImpl` turns the
  consequent certificate into the implication. The diagonal needs no certificate at
  all — after subst the guard is literally `φ → φ` (`implRefl`): the conditional
  cooperator trivially satisfies its own condition.
* **floor-priced or false** (defect, ebot, obot, guardian, dbot, cupodTroll): the
  spine-tail census walks through the `.impl` to the consequent atom, and the
  existing per-shape censuses kill it — the same floors, seen through an
  implication.
* **entangled** (dupoc, cupod): `.sys` systems — see the dedicated sections; dupoc
  closes COOPERATIVELY by MUTUAL bounded Löb (the actions align, unlike
  cupod×dupoc), cupod closes by the floor.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## The guard shape -/

/-- The substituted CIMCIC guard: frame `me`, hypothesis instance `I`. -/
abbrev cimG (me I : Prog) : Formula :=
  .impl (.plays me (.bot I) Action.C) (.plays (.bot I) me Action.C)

/-- The stored guard substitutes to `cimG` — `.self` is the only pronoun in it. -/
theorem cimG_subst (I me o : Prog) :
    (Formula.impl (.plays .self (.bot I) Action.C)
                  (.plays (.bot I) .self Action.C)).subst me o
      = cimG me I := rfl

/-- `weakenImpl`, packaged: a provable consequent fires the CIMCIC guard. -/
theorem pf_cimG_of_consequent {K m : Nat} {me I : Prog}
    (h : Pf m (.plays (.bot I) me Action.C))
    (hK : m + (cimG me I).size ≤ K) :
    Pf K (cimG me I) :=
  Pf.weakenImpl _ _ m h hK

/-! ## Generic play lemmas for an arbitrary-guard prove stage -/

/-- A prove-stage with an arbitrary guard cooperates when the substituted guard is
    provable… -/
theorem searchGuard_plays_C {k : Nat} {g : Formula} (me opp : Prog)
    (h : proofSearch k (g.subst me opp) = true) :
    ∃ N, eval N me opp (.search k g (.const .C) (.const .D)) = some Action.C := by
  refine ⟨2, ?_⟩
  rw [eval, h]
  rfl

/-- …and defects when it is not. -/
theorem searchGuard_plays_D {k : Nat} {g : Formula} (me opp : Prog)
    (h : proofSearch k (g.subst me opp) = false) :
    ∃ N, eval N me opp (.search k g (.const .C) (.const .D)) = some Action.D := by
  refine ⟨2, ?_⟩
  rw [eval, h, if_neg (by simp)]
  rfl

/-! ## The TRUE bits — `weakenImpl` cells

Cost hypothesis convention: one generous linear bound `100·log₂ k + 1000 ≤ k`
(`hL`), discharged in the phase theorem by `linear_log2_add_le`. -/

/-- The coop-cell guard fires: the constant cooperator's consequent is a 2-character
    certificate, and the implication's size is `O(log k)`. -/
theorem pf_cimG_coop {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    Pf k (cimG (.bot (inst (tauZoo k) .cimcic .coop)) (.const .C)) := by
  refine pf_cimG_of_consequent (m := 3)
    (Pf.atom ⟨PlaysProof.bot PlaysProof.const, by decide⟩) ?_
  rw [inst_cimcic_peel_coop k, inst_coop_peel k .cimcic]
  have hlog := Nat.log2_le_self k
  simp only [cimG, Formula.size, Prog.size, numCost]
  omega

/-- The searched formula of the coop cell, in `eval`'s own form. -/
theorem ps_cimGuard_coop {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    proofSearch k
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .coop .cimcic)) Action.C)
                     (.plays (.bot (inst (tauZoo k) .coop .cimcic)) .self Action.C)).subst
        (.bot (inst (tauZoo k) .cimcic .coop)) (.bot (inst (tauZoo k) .cimcic .coop)))
      = true := by
  rw [cimG_subst]
  exact (proofSearch_spec _ _).2 (by rw [inst_coop_peel k .cimcic]; exact pf_cimG_coop hL)

/-- τ(CIMCIC) COOPERATES with the cooperator. -/
theorem cimcic_coop_plays_C {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .coop))
      (.bot (inst (tauZoo k) .cimcic .coop)) (inst (tauZoo k) .cimcic .coop)
      = some Action.C := by
  rw [inst_cimcic_peel_coop k]
  exact searchGuard_plays_C _ _ (ps_cimGuard_coop hL)

/-- The δ_C bit: τ(CIMCIC)'s self-play cooperation at the coop hypothesis is
    PROVABLE — `bot ∘ search_t` citing the fired guard. -/
theorem pf_probe_cimcic_coop {k K : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k)
    (hK : c_guard k + 10 ≤ K) :
    Pf K (probe (inst (tauZoo k) .cimcic .coop)) := by
  rw [show inst (tauZoo k) .cimcic .coop
      = .search k (.impl (.plays .self (.bot (inst (tauZoo k) .coop .cimcic)) Action.C)
                         (.plays (.bot (inst (tauZoo k) .coop .cimcic)) .self Action.C))
          (.const .C) (.const .D) from inst_cimcic_peel_coop k]
  refine Pf.atom ⟨PlaysProof.bot (PlaysProof.search_t ?_ PlaysProof.const), ?_⟩
  · rw [cimG_subst, inst_coop_peel k .cimcic]
    exact pf_cimG_coop hL
  · have := hcl; have := hcn; omega

theorem ps_probe_cimcic_coop {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k)
    (hkk : c_guard k + 10 ≤ k) :
    proofSearch k (probe (inst (tauZoo k) .cimcic .coop)) = true :=
  (proofSearch_spec _ _).2 (pf_probe_cimcic_coop hL hkk)

/-- The tftSim-cell guard fires: the consequent — the mirror copies the coop cell's
    C — is certified by an `ite_t ∘ sim` transcript over the SAME fired guard. -/
theorem pf_cimG_tftSim {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k)
    (hkk : c_guard k + 20 ≤ k) :
    Pf k (cimG (.bot (inst (tauZoo k) .cimcic .tftSim))
               (inst (tauZoo k) .tftSim .cimcic)) := by
  refine pf_cimG_of_consequent (m := c_guard k + 20)
    ?_ ?_
  · rw [show inst (tauZoo k) .tftSim .cimcic
        = .ite (.sim (.bot (inst (tauZoo k) .cimcic .coop))
                     (.bot (inst (tauZoo k) .cimcic .coop)))
            Action.C (.const .C) (.const .D) from inst_tftSim_peel k .cimcic,
       show inst (tauZoo k) .cimcic .coop
        = .search k (.impl (.plays .self (.bot (inst (tauZoo k) .coop .cimcic)) Action.C)
                           (.plays (.bot (inst (tauZoo k) .coop .cimcic)) .self Action.C))
            (.const .C) (.const .D) from inst_cimcic_peel_coop k,
       show inst (tauZoo k) .coop .cimcic = .const .C from inst_coop_peel k .cimcic]
    refine Pf.atom ⟨PlaysProof.bot (PlaysProof.ite_t (PlaysProof.sim
      (PlaysProof.bot (PlaysProof.search_t ?_ PlaysProof.const))) rfl
      PlaysProof.const), ?_⟩
    · rw [cimG_subst]
      exact pf_cimG_coop hL
    · have := hcl; have := hcn; omega
  · rw [inst_cimcic_peel_tftSim k, inst_tftSim_peel k .cimcic,
        inst_cimcic_peel_coop k, inst_coop_peel k .cimcic]
    have hlog := Nat.log2_le_self k
    simp only [cimG, Formula.size, Prog.size, numCost, c_guard]
    omega

/-- The tftPf-cell guard fires: the prover TFT probes the δ_C cell, whose bit is
    true (`pf_probe_cimcic_coop`). -/
theorem pf_cimG_tftPf {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k)
    (hkk : c_guard k + 20 ≤ k) :
    Pf k (cimG (.bot (inst (tauZoo k) .cimcic .tftPf))
               (inst (tauZoo k) .tftPf .cimcic)) := by
  refine pf_cimG_of_consequent (m := c_guard k + 20) ?_ ?_
  · rw [show inst (tauZoo k) .tftPf .cimcic
        = .search k (probe (inst (tauZoo k) .cimcic .coop)) (.const .C) (.const .D)
          from inst_tftPf_peel k .cimcic]
    refine Pf.atom ⟨PlaysProof.bot (PlaysProof.search_t ?_ PlaysProof.const), ?_⟩
    · rw [probe_subst]
      exact pf_probe_cimcic_coop hL (by omega)
    · have := hcl; have := hcn; omega
  · rw [inst_cimcic_peel_tftPf k, inst_tftPf_peel k .cimcic,
        inst_cimcic_peel_coop k, inst_coop_peel k .cimcic]
    have hlog := Nat.log2_le_self k
    simp only [cimG, Formula.size, Prog.size, Formula.size, probe, numCost, c_guard]
    omega

/-- The just-cell guard fires CONDITIONALLY on the Löb bit of the entangled
    `inst .cimcic .dupoc` diagonal — τ(Just) probes exactly that cell. -/
theorem pf_cimG_just {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k)
    (hcq : proofSearch k (probe (inst (tauZoo k) .cimcic .dupoc)) = true) :
    Pf k (cimG (.bot (inst (tauZoo k) .cimcic .just))
               (inst (tauZoo k) .just .cimcic)) := by
  refine pf_cimG_of_consequent (m := c_guard k + 20) ?_ ?_
  · rw [show inst (tauZoo k) .just .cimcic
        = .search k (probe (inst (tauZoo k) .cimcic .dupoc)) (.const .C) (.const .D)
          from inst_just_peel k .cimcic]
    refine Pf.atom ⟨PlaysProof.bot (PlaysProof.search_t ?_ PlaysProof.const), ?_⟩
    · rw [probe_subst]
      exact (proofSearch_spec _ _).1 hcq
    · have := hcl; have := hcn; omega
  · rw [inst_cimcic_peel_just k, inst_just_peel k .cimcic, inst_cimcic_sys_dupoc k]
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [cimG, Formula.size, Prog.size, ProgList.psize, probe, numCost, c_guard]
    omega

/-- THE DIAGONAL: after subst the guard is literally `φ → φ`. No Löb, no
    certificate — `implRefl` and a size bound. -/
theorem pf_cimG_quine {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    Pf k ((Formula.impl (.plays .self .self Action.C) (.plays .self .self Action.C)).subst
      (.bot (inst (tauZoo k) .cimcic .cimcic)) (.bot (inst (tauZoo k) .cimcic .cimcic))) := by
  refine Pf.implRefl _ ?_
  rw [inst_cimcic_quine k]
  have hlog := Nat.log2_le_self k
  simp only [Formula.subst, Prog.subst, Formula.size, Prog.size, numCost]
  omega

/-- τ(CIMCIC) COOPERATES WITH ITSELF — trivially, not Löbianly. -/
theorem cimcic_quine_plays_C {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .cimcic))
      (.bot (inst (tauZoo k) .cimcic .cimcic)) (inst (tauZoo k) .cimcic .cimcic)
      = some Action.C := by
  rw [inst_cimcic_quine k]
  exact searchGuard_plays_C _ _ ((proofSearch_spec _ _).2 (pf_cimG_quine hL))

/-! ## The FALSE bits — floors and impossibilities seen through the `.impl`

`TailTo` walks through the implication to its consequent, so each cell reduces to
the census for the consequent's SUBJECT shape: the frozen constant (defect), the
run cascade (ebot, dbot — `no_provable_botRunCascade_C`), the searcher's else-play
(guardian, cupodTroll — `no_provable_botSearcherElse_tail`), and OBot's two-watch
tester (the one new census, budget-free). -/

/-- No proof, at ANY budget, tails at "the frozen constant `a` plays `b ≠ a`":
    `.bot (.const a)` is bridge-unreadable and the atom itself is impossible. -/
theorem no_provable_botConst_tail {a b : Action} (hne : a ≠ b) (O : Prog) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ → ¬ TailTo (.plays (.bot (.const a)) O b) φ := by
  intro m φ h
  refine no_provable_tailTo_unreadable (.bot (.const a)) O b ?_ ?_ ?_ ?_ ?_ h
  · rintro n ⟨hpp, -⟩
    cases hpp with
    | bot hin => cases hin; exact hne rfl
  · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
      ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, h⟩) <;> simp at h
  · intro L
    cases L with
    | nil => simp [searchPlug]
    | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug]
  · intro hd L; cases hd <;> simp [ctxPlug]
  · intro hd L; cases hd <;> simp [plug2]

/-- τ(CIMCIC)'s defect-cell guard is FALSE at every budget: the consequent claims
    the constant defector cooperates. -/
theorem ps_cimGuard_defect_false {k K : Nat} :
    proofSearch K
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .defect .cimcic)) Action.C)
                     (.plays (.bot (inst (tauZoo k) .defect .cimcic)) .self Action.C)).subst
        (.bot (inst (tauZoo k) .cimcic .defect)) (.bot (inst (tauZoo k) .cimcic .defect)))
      = false := by
  rw [cimG_subst]
  cases h : proofSearch K (cimG (.bot (inst (tauZoo k) .cimcic .defect))
      (inst (tauZoo k) .defect .cimcic)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      rw [show inst (tauZoo k) .defect .cimcic = .const .D
          from inst_defect_peel k .cimcic] at hp
      refine no_provable_botConst_tail (by decide) _ hp ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      exact absurd hA (by rw [inst_cimcic_peel_defect k]; simp)

/-- τ(CIMCIC) DEFECTS against the defector. -/
theorem cimcic_defect_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .defect))
      (.bot (inst (tauZoo k) .cimcic .defect)) (inst (tauZoo k) .cimcic .defect)
      = some Action.D := by
  rw [inst_cimcic_peel_defect k]
  exact searchGuard_plays_D _ _ (ps_cimGuard_defect_false (k := k))

/-- τ(CIMCIC)'s ebot-cell guard is FALSE at every budget ≤ k: the consequent — the
    exploiter's run cascade cooperates — embeds the defect-cell's `search_f` floor
    (`no_provable_botRunCascade_C`, the τ(EBot) mechanism through an `.impl`). -/
theorem ps_cimGuard_ebot_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .ebot .cimcic)) Action.C)
                     (.plays (.bot (inst (tauZoo k) .ebot .cimcic)) .self Action.C)).subst
        (.bot (inst (tauZoo k) .cimcic .ebot)) (.bot (inst (tauZoo k) .cimcic .ebot)))
      = false := by
  rw [cimG_subst]
  cases h : proofSearch K (cimG (.bot (inst (tauZoo k) .cimcic .ebot))
      (inst (tauZoo k) .ebot .cimcic)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      rw [show inst (tauZoo k) .ebot .cimcic
          = .ite (.sim (.bot (inst (tauZoo k) .cimcic .defect))
                       (.bot (inst (tauZoo k) .cimcic .defect)))
              .C (.const .D)
              (.ite (.sim (.bot (inst (tauZoo k) .cimcic .coop))
                          (.bot (inst (tauZoo k) .cimcic .coop)))
                .C (.const .C) (.const .D)) from inst_ebot_peel k .cimcic,
          show inst (tauZoo k) .cimcic .defect
          = .search k (.impl (.plays .self (.bot (inst (tauZoo k) .defect .cimcic)) Action.C)
                             (.plays (.bot (inst (tauZoo k) .defect .cimcic)) .self Action.C))
              (.const .C) (.const .D) from inst_cimcic_peel_defect k] at hp
      refine no_provable_botRunCascade_C k k (Nat.le_refl k) _ (.const .D) _ _
        K _ hp hK ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      exact absurd hA (by rw [inst_cimcic_peel_ebot k]; simp)

/-- τ(CIMCIC) DEFECTS against the exploiter — it cannot certify EBot's trust. -/
theorem cimcic_ebot_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .ebot))
      (.bot (inst (tauZoo k) .cimcic .ebot)) (inst (tauZoo k) .cimcic .ebot)
      = some Action.D := by
  rw [inst_cimcic_peel_ebot k]
  exact searchGuard_plays_D _ _ (ps_cimGuard_ebot_false (le_refl k))

/-- τ(CIMCIC)'s dbot-cell guard is FALSE at every budget ≤ k: the consequent — the
    punisher's trusting C — is a fall-through past the same embedded floor (the
    dbot cell IS a one-watch run cascade with `cont = .const .C`). -/
theorem ps_cimGuard_dbot_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .dbot .cimcic)) Action.C)
                     (.plays (.bot (inst (tauZoo k) .dbot .cimcic)) .self Action.C)).subst
        (.bot (inst (tauZoo k) .cimcic .dbot)) (.bot (inst (tauZoo k) .cimcic .dbot)))
      = false := by
  rw [cimG_subst]
  cases h : proofSearch K (cimG (.bot (inst (tauZoo k) .cimcic .dbot))
      (inst (tauZoo k) .dbot .cimcic)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      rw [show inst (tauZoo k) .dbot .cimcic
          = .ite (.sim (.bot (inst (tauZoo k) .cimcic .defect))
                       (.bot (inst (tauZoo k) .cimcic .defect)))
              .C (.const .D) (.const .C) from inst_dbot_peel k .cimcic,
          show inst (tauZoo k) .cimcic .defect
          = .search k (.impl (.plays .self (.bot (inst (tauZoo k) .defect .cimcic)) Action.C)
                             (.plays (.bot (inst (tauZoo k) .defect .cimcic)) .self Action.C))
              (.const .C) (.const .D) from inst_cimcic_peel_defect k] at hp
      refine no_provable_botRunCascade_C k k (Nat.le_refl k) _ (.const .D) _ _
        K _ hp hK ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      exact absurd hA (by rw [inst_cimcic_peel_dbot k]; simp)

/-- τ(CIMCIC) DEFECTS against the punisher — the trusting C is uncitable. -/
theorem cimcic_dbot_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .dbot))
      (.bot (inst (tauZoo k) .cimcic .dbot)) (inst (tauZoo k) .cimcic .dbot)
      = some Action.D := by
  rw [inst_cimcic_peel_dbot k]
  exact searchGuard_plays_D _ _ (ps_cimGuard_dbot_false (le_refl k))

/-- τ(CIMCIC)'s guardian-cell guard is FALSE at every budget ≤ k: the consequent —
    Guardian's trusting C — is the else-play of its punish-searcher
    (`no_provable_botSearcherElse_tail`). -/
theorem ps_cimGuard_guardian_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .guardian .cimcic)) Action.C)
                     (.plays (.bot (inst (tauZoo k) .guardian .cimcic)) .self Action.C)).subst
        (.bot (inst (tauZoo k) .cimcic .guardian)) (.bot (inst (tauZoo k) .cimcic .guardian)))
      = false := by
  rw [cimG_subst]
  cases h : proofSearch K (cimG (.bot (inst (tauZoo k) .cimcic .guardian))
      (inst (tauZoo k) .guardian .cimcic)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      rw [show inst (tauZoo k) .guardian .cimcic
          = .search k (.plays (.bot (inst (tauZoo k) .cimcic .coop))
                              (.bot (inst (tauZoo k) .cimcic .coop)) Action.D)
              (.const .D) (.const .C) from inst_guardian_peel k .cimcic] at hp
      refine no_provable_botSearcherElse_tail k k _ .D .C _ (by decide) (Nat.le_refl k) _
        K _ hp hK ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      exact absurd hA (by rw [inst_cimcic_peel_guardian k]; simp)

/-- τ(CIMCIC) DEFECTS against Guardian — trust by default is invisible to it. -/
theorem cimcic_guardian_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .guardian))
      (.bot (inst (tauZoo k) .cimcic .guardian)) (inst (tauZoo k) .cimcic .guardian)
      = some Action.D := by
  rw [inst_cimcic_peel_guardian k]
  exact searchGuard_plays_D _ _ (ps_cimGuard_guardian_false (le_refl k))

/-- τ(CIMCIC)'s cupodTroll-cell guard is FALSE at every budget ≤ k: the troll's C
    is the else-play of its failed `.eq` search — the same floor. -/
theorem ps_cimGuard_cupodTroll_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .cupodTroll .cimcic)) Action.C)
                     (.plays (.bot (inst (tauZoo k) .cupodTroll .cimcic)) .self Action.C)).subst
        (.bot (inst (tauZoo k) .cimcic .cupodTroll))
        (.bot (inst (tauZoo k) .cimcic .cupodTroll)))
      = false := by
  rw [cimG_subst]
  cases h : proofSearch K (cimG (.bot (inst (tauZoo k) .cimcic .cupodTroll))
      (inst (tauZoo k) .cupodTroll .cimcic)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      rw [show inst (tauZoo k) .cupodTroll .cimcic
          = .search k (.eq .opp (.bot (inst (tauZoo k) .cimcic .dupoc)))
              (.const .D) (.const .C) from inst_cupodTroll_peel k .cimcic] at hp
      refine no_provable_botSearcherElse_tail k k _ .D .C _ (by decide) (Nat.le_refl k) _
        K _ hp hK ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      exact absurd hA (by rw [inst_cimcic_peel_cupodTroll k]; simp)

/-- τ(CIMCIC) DEFECTS against the troll — a floor-priced cooperator earns no trust
    from a prover. -/
theorem cimcic_cupodTroll_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .cupodTroll))
      (.bot (inst (tauZoo k) .cimcic .cupodTroll)) (inst (tauZoo k) .cimcic .cupodTroll)
      = some Action.D := by
  rw [inst_cimcic_peel_cupodTroll k]
  exact searchGuard_plays_D _ _ (ps_cimGuard_cupodTroll_false (le_refl k))

/-! ## OBot's cell — the one NEW census, and it is budget-free

τ(OBot) at CIMCIC truly DEFECTS (watch 2 catches CIMCIC defecting against the
defector), so the consequent "OBot cooperates with me" is FALSE — but the guard is
an implication, so soundness alone cannot refute it (a defecting CIMCIC makes the
antecedent false and the implication TRUE). The census is syntactic, and every
route dies STRUCTURALLY — no floor needed:

* either watch FIRING concludes the fire-constant `.D` — action mismatch with `.C`;
* watch 2 FALLING to the trailing `.const .C` requires its guard premise "the
  watched defect-cell plays ≠ D", whose only non-contradictory route (`search_t`,
  concluding the then-`C`) must PROVE the defect-cell guard — killed by
  `no_provable_botConst_tail` through the `.impl`;
* the player `.bot (.ite …)` is bridge-unreadable, so the atom layer is all there is.

Generic in watch 1 and in the frame; watch 2 is pinned to the defect-cell shape. -/

/-- The two-watch DEFECTION tester over an arbitrary first watch and the CIMCIC
    defect-cell second watch cannot be certified to COOPERATE, at any budget. -/
theorem no_provable_twoTestD_cimcic_C (kb : Nat) (W1 : Prog) (O : Prog) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ →
      ¬ TailTo (.plays (.bot (.ite (.sim (.bot W1) (.bot W1)) Action.D (.const .D)
        (.ite (.sim (.bot (.search kb
            (.impl (.plays .self (.bot (.const .D)) Action.C)
                   (.plays (.bot (.const .D)) .self Action.C))
            (.const .C) (.const .D)))
          (.bot (.search kb
            (.impl (.plays .self (.bot (.const .D)) Action.C)
                   (.plays (.bot (.const .D)) .self Action.C))
            (.const .C) (.const .D))))
          Action.D (.const .D) (.const .C)))) O .C) φ := by
  intro m φ h
  refine no_provable_tailTo_unreadable _ O .C ?_ ?_ ?_ ?_ ?_ h
  · rintro n ⟨hpp, -⟩
    cases hpp with
    | bot hin =>
      cases hin with
      | ite_t hg hbeq hbr => cases hbr
      | ite_f hg hbeq hbr =>
        cases hbr with
        | ite_t hg2 hbeq2 hbr2 => cases hbr2
        | ite_f hg2 hbeq2 hbr2 =>
          cases hg2 with
          | sim hin2 =>
            cases hin2 with
            | bot hin3 =>
              cases hin3 with
              | search_t hProv hbr3 =>
                  refine no_provable_botConst_tail (by decide) _ hProv ⟨rfl, ?_⟩
                  intro hA
                  simp only [Formula.subst, Prog.subst, TailTo] at hA
                  simp at hA
              | search_f hneg hbr3 =>
                  cases hbr3
                  exact absurd hbeq2 (by decide)
  · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
      ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, h⟩) <;> simp at h
  · intro L
    cases L with
    | nil => simp [searchPlug]
    | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug]
  · intro hd L; cases hd <;> simp [ctxPlug]
  · intro hd L; cases hd <;> simp [plug2]

/-- τ(CIMCIC)'s obot-cell guard is FALSE at every budget. -/
theorem ps_cimGuard_obot_false {k K : Nat} :
    proofSearch K
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .obot .cimcic)) Action.C)
                     (.plays (.bot (inst (tauZoo k) .obot .cimcic)) .self Action.C)).subst
        (.bot (inst (tauZoo k) .cimcic .obot)) (.bot (inst (tauZoo k) .cimcic .obot)))
      = false := by
  rw [cimG_subst]
  cases h : proofSearch K (cimG (.bot (inst (tauZoo k) .cimcic .obot))
      (inst (tauZoo k) .obot .cimcic)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      rw [show inst (tauZoo k) .obot .cimcic
          = .ite (.sim (.bot (inst (tauZoo k) .cimcic .coop))
                       (.bot (inst (tauZoo k) .cimcic .coop)))
              Action.D (.const .D)
              (.ite (.sim (.bot (inst (tauZoo k) .cimcic .defect))
                          (.bot (inst (tauZoo k) .cimcic .defect)))
                Action.D (.const .D) (.const .C)) from inst_obot_peel k .cimcic,
          show inst (tauZoo k) .cimcic .defect
          = .search k (.impl (.plays .self (.bot (inst (tauZoo k) .defect .cimcic)) Action.C)
                             (.plays (.bot (inst (tauZoo k) .defect .cimcic)) .self Action.C))
              (.const .C) (.const .D) from inst_cimcic_peel_defect k,
          show inst (tauZoo k) .defect .cimcic = .const .D
            from inst_defect_peel k .cimcic] at hp
      refine no_provable_twoTestD_cimcic_C k _ _ hp ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      exact absurd hA (by rw [inst_cimcic_peel_obot k]; simp)

/-- τ(CIMCIC) DEFECTS against OBot. -/
theorem cimcic_obot_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .obot))
      (.bot (inst (tauZoo k) .cimcic .obot)) (inst (tauZoo k) .cimcic .obot)
      = some Action.D := by
  rw [inst_cimcic_peel_obot k]
  exact searchGuard_plays_D _ _ (ps_cimGuard_obot_false (k := k))

/-! ## The entangled systems

Four orientations, two pairs. Naming: `mdSys`/`dmSys` = CIMCIC×Dupoc in each
order, `mcSys`/`cmSys` = CIMCIC×Cupod. -/

/-- `inst .cimcic .dupoc`: CIMCIC at the head, Dupoc probing it. -/
def mdSys (k : Nat) : ProgList :=
  .cons (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                          (.plays (.bot (.selfIdx 1)) .self Action.C))
    (.const .C) (.const .D))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
    (.const .C) (.const .D)) .nil)

theorem inst_cimcic_dupoc_eq (k : Nat) :
    inst (tauZoo k) .cimcic .dupoc = .sys (mdSys k) 0 := rfl

theorem mdSys_get0 (k : Nat) :
    (mdSys k).get? 0
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                               (.plays (.bot (.selfIdx 1)) .self Action.C))
          (.const .C) (.const .D)) := rfl

theorem mdSys_get1 (k : Nat) :
    (mdSys k).get? 1
      = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
          (.const .C) (.const .D)) := rfl

/-- `inst .dupoc .cimcic`: Dupoc at the head. -/
def dmSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
    (.const .C) (.const .D))
  (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                           (.plays (.bot (.selfIdx 0)) .self Action.C))
    (.const .C) (.const .D)) .nil)

theorem inst_dupoc_cimcic_eq (k : Nat) :
    inst (tauZoo k) .dupoc .cimcic = .sys (dmSys k) 0 := rfl

theorem dmSys_get0 (k : Nat) :
    (dmSys k).get? 0
      = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
          (.const .C) (.const .D)) := rfl

theorem dmSys_get1 (k : Nat) :
    (dmSys k).get? 1
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                               (.plays (.bot (.selfIdx 0)) .self Action.C))
          (.const .C) (.const .D)) := rfl

/-- `inst .cimcic .cupod`: CIMCIC at the head, Cupod punishing it. -/
def mcSys (k : Nat) : ProgList :=
  .cons (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                          (.plays (.bot (.selfIdx 1)) .self Action.C))
    (.const .C) (.const .D))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.D)
    (.const .D) (.const .C)) .nil)

theorem inst_cimcic_cupod_eq (k : Nat) :
    inst (tauZoo k) .cimcic .cupod = .sys (mcSys k) 0 := rfl

theorem mcSys_get0 (k : Nat) :
    (mcSys k).get? 0
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                               (.plays (.bot (.selfIdx 1)) .self Action.C))
          (.const .C) (.const .D)) := rfl

theorem mcSys_get1 (k : Nat) :
    (mcSys k).get? 1
      = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.D)
          (.const .D) (.const .C)) := rfl

/-- `inst .cupod .cimcic`: Cupod at the head. -/
def cmSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.D)
    (.const .D) (.const .C))
  (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                           (.plays (.bot (.selfIdx 0)) .self Action.C))
    (.const .C) (.const .D)) .nil)

theorem inst_cupod_cimcic_eq (k : Nat) :
    inst (tauZoo k) .cupod .cimcic = .sys (cmSys k) 0 := rfl

theorem cmSys_get0 (k : Nat) :
    (cmSys k).get? 0
      = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.D)
          (.const .D) (.const .C)) := rfl

theorem cmSys_get1 (k : Nat) :
    (cmSys k).get? 1
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                               (.plays (.bot (.selfIdx 0)) .self Action.C))
          (.const .C) (.const .D)) := rfl

/-- The closed-substituted form of the entangled CIMCIC guard. -/
theorem sysClose_subst_cimSelfIdx (defs : ProgList) (j : Nat) (me o : Prog) :
    ((Formula.impl (.plays .self (.bot (.selfIdx j)) Action.C)
                   (.plays (.bot (.selfIdx j)) .self Action.C)).sysClose defs).subst me o
      = .impl (.plays me (.bot (.sys defs j)) Action.C)
              (.plays (.bot (.sys defs j)) me Action.C) := by
  simp [Formula.sysClose, Prog.sysClose, Formula.subst, Prog.subst]

/-! ## CIMCIC × Cupod — CLOSED BY THE FLOOR (both orientations)

Same mechanism as Cupod×Dupoc: the actions do not align (CIMCIC's consequent aims
C at the punisher whose then-action is D; Cupod's probe aims D at the conditional
cooperator whose then-action is C), so both guards are floor-false and both
components play their defaults — CIMCIC defects, Cupod trusts. `(D, C)`: the
suspicious cooperator extends trust the conditional cooperator cannot verify. -/

/-- τ(CIMCIC)'s guard in the Cupod system is FALSE at every budget ≤ k. -/
theorem ps_cimGuard_cupod_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K
      (.impl (.plays (.bot (.sys (mcSys k) 0)) (.bot (.sys (mcSys k) 1)) Action.C)
             (.plays (.bot (.sys (mcSys k) 1)) (.bot (.sys (mcSys k) 0)) Action.C))
      = false := by
  cases h : proofSearch K
      (.impl (.plays (.bot (.sys (mcSys k) 0)) (.bot (.sys (mcSys k) 1)) Action.C)
             (.plays (.bot (.sys (mcSys k) 1)) (.bot (.sys (mcSys k) 0)) Action.C)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      refine no_provable_botSysSearcherElse_tail k (mcSys k) 1 k _ .D .C _ (by decide)
        (Nat.le_refl k) (mcSys_get1 k) _ K _ hp hK ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      exact absurd hA (by simp)

/-- τ(CIMCIC) at Cupod DEFECTS. -/
theorem cimcic_cupod_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .cupod))
      (.bot (inst (tauZoo k) .cimcic .cupod)) (inst (tauZoo k) .cimcic .cupod)
      = some Action.D := by
  rw [inst_cimcic_cupod_eq k]
  refine sysSearcher_plays_else _ _ (mcSys_get0 k) ?_
  rw [sysClose_subst_cimSelfIdx]
  exact ps_cimGuard_cupod_false (Nat.le_refl k)

/-- δ_Cu's `.cimcic` bit: `probeD (inst .cimcic .cupod)` is FALSE — the head
    component's then-action is C. -/
theorem ps_probeD_inst_cimcic_cupod_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probeD (inst (tauZoo k) .cimcic .cupod)) = false := by
  rw [show probeD (inst (tauZoo k) .cimcic .cupod)
        = .plays (.bot (.sys (mcSys k) 0)) (.bot (.sys (mcSys k) 0)) Action.D
      from by rw [probeD, inst_cimcic_cupod_eq]]
  exact ps_botSys_mismatch_false hK (mcSys k) 0 k _ .C .D _ (by decide)
    (Nat.le_refl k) (mcSys_get0 k) _

/-- τ(Cupod)'s guard in the CIMCIC system is FALSE: it aims D at the conditional
    cooperator whose then-action is C. -/
theorem ps_cupodGuard_cimcic_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K
      (.plays (.bot (.sys (cmSys k) 1)) (.bot (.sys (cmSys k) 1)) Action.D) = false :=
  ps_botSys_mismatch_false hK (cmSys k) 1 k _ .C .D _ (by decide)
    (Nat.le_refl k) (cmSys_get1 k) _

/-- τ(Cupod) at CIMCIC TRUSTS. -/
theorem cupod_cimcic_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .cupod .cimcic))
      (.bot (inst (tauZoo k) .cupod .cimcic)) (inst (tauZoo k) .cupod .cimcic)
      = some Action.C := by
  rw [inst_cupod_cimcic_eq k]
  refine sysSearcher_plays_else _ _ (cmSys_get0 k) ?_
  rw [sysClose_subst_botSelfIdx]
  exact ps_cupodGuard_cimcic_false (Nat.le_refl k)

/-! ## CIMCIC × Dupoc — CLOSED COOPERATIVELY BY MUTUAL BOUNDED LÖB

The FIRST entangled cell where the actions ALIGN: CIMCIC's member concludes C from
□(its guard), Dupoc's member concludes C from □(CIMCIC's cooperation) — the base
`llm_outcome_CIMCIC_vs_DupocBot` fixpoint (`mutual_pblt_engine_id`), transferred to
the binder through `Pf.botSysSearchStep`. With

    Af := probe of the CIMCIC component,   Bf := its substituted guard,

the two premises are `□Bf → Af` (CIMCIC's own reading) and `□Af → Bf`
(Dupoc's reading, weakened into the implication by `implK ∘ implTrans`). -/

/-- CIMCIC's side: □(its guard) → it cooperates (generic in the system). -/
theorem sys_cross_impl_cim (defs : ProgList) (i j : Nat) (k K : Nat)
    (hget : defs.get? i = some (.search k
      (.impl (.plays .self (.bot (.selfIdx j)) Action.C)
             (.plays (.bot (.selfIdx j)) .self Action.C)) (.const .C) (.const .D)))
    (hK : (Formula.impl
        (.box k (.impl (.plays (.bot (.sys defs i)) (.bot (.sys defs j)) Action.C)
                       (.plays (.bot (.sys defs j)) (.bot (.sys defs i)) Action.C)))
        (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.C)).size ≤ K) :
    Pf K (.impl
      (.box k (.impl (.plays (.bot (.sys defs i)) (.bot (.sys defs j)) Action.C)
                     (.plays (.bot (.sys defs j)) (.bot (.sys defs i)) Action.C)))
      (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.C)) := by
  have h := Pf.botSysSearchStep defs i k
    (.impl (.plays .self (.bot (.selfIdx j)) Action.C)
           (.plays (.bot (.selfIdx j)) .self Action.C)) .C .D
    (.bot (.sys defs i)) (.bot (.sys defs i)) rfl hget
    (by simpa [sysClose_subst_cimSelfIdx] using hK)
  rw [sysClose_subst_cimSelfIdx] at h
  exact h

/-- Dupoc's side, at an arbitrary opponent frame: □(i cooperates) → j plays C
    against `opp`. -/
theorem sys_cross_C_at (defs : ProgList) (j i : Nat) (k K : Nat) (opp : Prog)
    (hget : defs.get? j = some (.search k
      (.plays (.bot (.selfIdx i)) (.bot (.selfIdx i)) Action.C) (.const .C) (.const .D)))
    (hK : (Formula.impl
        (.box k (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.C))
        (.plays (.bot (.sys defs j)) opp Action.C)).size ≤ K) :
    Pf K (.impl (.box k (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.C))
                (.plays (.bot (.sys defs j)) opp Action.C)) := by
  have h := Pf.botSysSearchStep defs j k
    (.plays (.bot (.selfIdx i)) (.bot (.selfIdx i)) Action.C) .C .D
    (.bot (.sys defs j)) opp rfl hget
    (by simpa [sysClose_subst_botSelfIdx] using hK)
  rw [sysClose_subst_botSelfIdx] at h
  exact h

/-- **The mutual engine, CIMCIC-at-the-head orientation**: past a threshold, the
    CIMCIC component's self-cooperation is provable. -/
theorem cimcic_dupoc_mutual :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ m, Pf m (.plays (.bot (.sys (mdSys k) 0)) (.bot (.sys (mdSys k) 0)) Action.C) := by
  refine mutual_pblt_engine_id
    (fun k => .plays (.bot (.sys (mdSys k) 0)) (.bot (.sys (mdSys k) 0)) Action.C)
    (fun k => .impl (.plays (.bot (.sys (mdSys k) 0)) (.bot (.sys (mdSys k) 1)) Action.C)
                    (.plays (.bot (.sys (mdSys k) 1)) (.bot (.sys (mdSys k) 0)) Action.C))
    (fun k => 100 * Nat.log2 k + 1000) (fun k => 100 * Nat.log2 k + 1000) 0
    ?_ ?_ (fun k => le_rfl) (fun k => le_rfl) ?_ ?_
  · intro k
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [Formula.size, Prog.size, ProgList.psize, mdSys, numCost]
    omega
  · intro k
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [Formula.size, Prog.size, ProgList.psize, mdSys, numCost]
    omega
  · -- □Af → Bf : Dupoc's reading, weakened into the implication
    intro k _
    have h1 := sys_cross_C_at (mdSys k) 1 0 k
      ((Formula.impl (.box k (.plays (.bot (.sys (mdSys k) 0)) (.bot (.sys (mdSys k) 0)) Action.C))
        (.plays (.bot (.sys (mdSys k) 1)) (.bot (.sys (mdSys k) 0)) Action.C)).size)
      (.bot (.sys (mdSys k) 0)) (mdSys_get1 k) le_rfl
    have h2 := Pf.implK
      (.plays (.bot (.sys (mdSys k) 1)) (.bot (.sys (mdSys k) 0)) Action.C)
      (.plays (.bot (.sys (mdSys k) 0)) (.bot (.sys (mdSys k) 1)) Action.C)
      (k := (Formula.impl (.plays (.bot (.sys (mdSys k) 1)) (.bot (.sys (mdSys k) 0)) Action.C)
        (.impl (.plays (.bot (.sys (mdSys k) 0)) (.bot (.sys (mdSys k) 1)) Action.C)
               (.plays (.bot (.sys (mdSys k) 1)) (.bot (.sys (mdSys k) 0)) Action.C))).size)
      le_rfl
    have h3 := Pf.implTrans _ _ _ _ _ h1 h2 (Nat.le_refl _)
    refine Pf_mono h3 ?_
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1' : Nat.log2 1 = 0 := by decide
    simp only [Formula.size, Prog.size, ProgList.psize, mdSys, numCost]
    omega
  · -- □Bf → Af : CIMCIC's own reading
    intro k _
    refine Pf_mono (sys_cross_impl_cim (mdSys k) 0 1 k _ (mdSys_get0 k) le_rfl) ?_
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [Formula.size, Prog.size, ProgList.psize, mdSys, numCost]
    omega

/-- Eval inversion: a system component that plays its THEN action must have FIRED. -/
theorem sysSearcher_fired_of_plays {defs : ProgList} {i kb : Nat} {g : Formula}
    {aT aE : Action} (hne : aT ≠ aE) (me opp : Prog)
    (hget : defs.get? i = some (.search kb g (.const aT) (.const aE)))
    (h : ∃ N, eval N me opp (.sys defs i) = some aT) :
    proofSearch kb ((g.sysClose defs).subst me opp) = true := by
  cases hps : proofSearch kb ((g.sysClose defs).subst me opp) with
  | true => rfl
  | false =>
      exfalso
      obtain ⟨N, hN⟩ := h
      obtain ⟨M, hM⟩ := sysSearcher_plays_else me opp hget hps
      have h1 := eval_mono_le hN (max N M) (Nat.le_max_left _ _)
      have h2 := eval_mono_le hM (max N M) (Nat.le_max_right _ _)
      rw [h1] at h2
      exact hne (Option.some.inj h2)

/-- The cheap budget-`k` certificate for the CIMCIC component's cooperation, from
    its fired guard (`search_t` cites via `c_guard`, not the premise transcript). -/
theorem pf_Af_of_Bf_md {k : Nat} (hkk : c_guard k + 5 ≤ k)
    (hBf : Pf k (.impl (.plays (.bot (.sys (mdSys k) 0)) (.bot (.sys (mdSys k) 1)) Action.C)
                       (.plays (.bot (.sys (mdSys k) 1)) (.bot (.sys (mdSys k) 0)) Action.C))) :
    Pf k (.plays (.bot (.sys (mdSys k) 0)) (.bot (.sys (mdSys k) 0)) Action.C) := by
  have hpre : Pf k (((Formula.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
      (.plays (.bot (.selfIdx 1)) .self Action.C)).sysClose (mdSys k)).subst
      (.bot (.sys (mdSys k) 0)) (.bot (.sys (mdSys k) 0))) := by
    rw [sysClose_subst_cimSelfIdx]; exact hBf
  have h1 := PlaysProof.search_t (q := .const .D) hpre
    (PlaysProof.const (me := .bot (.sys (mdSys k) 0)) (opponent := .bot (.sys (mdSys k) 0))
      (a := Action.C))
  exact Pf.atom ⟨PlaysProof.bot (PlaysProof.sysStep (mdSys_get0 k) h1),
    by have := hcl; have := hcn; omega⟩

/-- **τ(CIMCIC) at Dupoc COOPERATES** (Löb-gated). -/
theorem cimcic_dupoc_plays_C :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .dupoc))
        (.bot (inst (tauZoo k) .cimcic .dupoc)) (inst (tauZoo k) .cimcic .dupoc)
        = some Action.C := by
  obtain ⟨kL, hLb⟩ := cimcic_dupoc_mutual
  refine ⟨kL, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hLb k hk
  have hint : (probe (.sys (mdSys k) 0)).interp := Pf_sound m _ hm
  rw [inst_cimcic_dupoc_eq k]
  exact entry_C_of_interp hint

/-- **THE LÖB BIT of the entangled pair**: past a threshold, the probe of
    `inst .cimcic .dupoc` fires at the probing budget itself. Consumed by the δ_L
    column's `.cimcic` slot and by τ(Just)'s row. -/
theorem ps_probe_inst_cimcic_dupoc :
    ∃ k₂, ∀ k, k₂ < k →
      proofSearch k (probe (inst (tauZoo k) .cimcic .dupoc)) = true := by
  obtain ⟨kL, hLp⟩ := cimcic_dupoc_plays_C
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 12
  refine ⟨max kL kA, fun k hk => ?_⟩
  have hplay := hLp k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hkA' : 1 * Nat.log2 k + 12 ≤ k :=
    hkA k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  have hkk : c_guard k + 5 ≤ k := by simp only [c_guard, numCost]; omega
  rw [inst_cimcic_dupoc_eq k] at hplay
  have hfired := sysSearcher_fired_of_plays (by decide) _ _ (mdSys_get0 k) hplay
  rw [sysClose_subst_cimSelfIdx] at hfired
  exact (proofSearch_spec _ _).2 (pf_Af_of_Bf_md hkk ((proofSearch_spec _ _).1 hfired))

/-- **The mutual engine, Dupoc-at-the-head orientation.** -/
theorem dupoc_cimcic_mutual :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ m, Pf m (.plays (.bot (.sys (dmSys k) 1)) (.bot (.sys (dmSys k) 1)) Action.C) := by
  refine mutual_pblt_engine_id
    (fun k => .plays (.bot (.sys (dmSys k) 1)) (.bot (.sys (dmSys k) 1)) Action.C)
    (fun k => .impl (.plays (.bot (.sys (dmSys k) 1)) (.bot (.sys (dmSys k) 0)) Action.C)
                    (.plays (.bot (.sys (dmSys k) 0)) (.bot (.sys (dmSys k) 1)) Action.C))
    (fun k => 100 * Nat.log2 k + 1000) (fun k => 100 * Nat.log2 k + 1000) 0
    ?_ ?_ (fun k => le_rfl) (fun k => le_rfl) ?_ ?_
  · intro k
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [Formula.size, Prog.size, ProgList.psize, dmSys, numCost]
    omega
  · intro k
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [Formula.size, Prog.size, ProgList.psize, dmSys, numCost]
    omega
  · -- □Af → Bf : the head Dupoc's reading, weakened
    intro k _
    have h1 := sys_cross_C_at (dmSys k) 0 1 k
      ((Formula.impl (.box k (.plays (.bot (.sys (dmSys k) 1)) (.bot (.sys (dmSys k) 1)) Action.C))
        (.plays (.bot (.sys (dmSys k) 0)) (.bot (.sys (dmSys k) 1)) Action.C)).size)
      (.bot (.sys (dmSys k) 1)) (dmSys_get0 k) le_rfl
    have h2 := Pf.implK
      (.plays (.bot (.sys (dmSys k) 0)) (.bot (.sys (dmSys k) 1)) Action.C)
      (.plays (.bot (.sys (dmSys k) 1)) (.bot (.sys (dmSys k) 0)) Action.C)
      (k := (Formula.impl (.plays (.bot (.sys (dmSys k) 0)) (.bot (.sys (dmSys k) 1)) Action.C)
        (.impl (.plays (.bot (.sys (dmSys k) 1)) (.bot (.sys (dmSys k) 0)) Action.C)
               (.plays (.bot (.sys (dmSys k) 0)) (.bot (.sys (dmSys k) 1)) Action.C))).size)
      le_rfl
    have h3 := Pf.implTrans _ _ _ _ _ h1 h2 (Nat.le_refl _)
    refine Pf_mono h3 ?_
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1' : Nat.log2 1 = 0 := by decide
    simp only [Formula.size, Prog.size, ProgList.psize, dmSys, numCost]
    omega
  · -- □Bf → Af : the CIMCIC component's reading
    intro k _
    refine Pf_mono (sys_cross_impl_cim (dmSys k) 1 0 k _ (dmSys_get1 k) le_rfl) ?_
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [Formula.size, Prog.size, ProgList.psize, dmSys, numCost]
    omega

/-- The cheap budget-`k` certificate, `dm` orientation. -/
theorem pf_Af_of_Bf_dm {k : Nat} (hkk : c_guard k + 5 ≤ k)
    (hBf : Pf k (.impl (.plays (.bot (.sys (dmSys k) 1)) (.bot (.sys (dmSys k) 0)) Action.C)
                       (.plays (.bot (.sys (dmSys k) 0)) (.bot (.sys (dmSys k) 1)) Action.C))) :
    Pf k (.plays (.bot (.sys (dmSys k) 1)) (.bot (.sys (dmSys k) 1)) Action.C) := by
  have hpre : Pf k (((Formula.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
      (.plays (.bot (.selfIdx 0)) .self Action.C)).sysClose (dmSys k)).subst
      (.bot (.sys (dmSys k) 1)) (.bot (.sys (dmSys k) 1))) := by
    rw [sysClose_subst_cimSelfIdx]; exact hBf
  have h1 := PlaysProof.search_t (q := .const .D) hpre
    (PlaysProof.const (me := .bot (.sys (dmSys k) 1)) (opponent := .bot (.sys (dmSys k) 1))
      (a := Action.C))
  exact Pf.atom ⟨PlaysProof.bot (PlaysProof.sysStep (dmSys_get1 k) h1),
    by have := hcl; have := hcn; omega⟩

/-- **τ(Dupoc) at CIMCIC COOPERATES** (Löb-gated): its trust-probe of the CIMCIC
    component FIRES — the mirror of the base `(C, C)`. -/
theorem dupoc_cimcic_plays_C :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .cimcic))
        (.bot (inst (tauZoo k) .dupoc .cimcic)) (inst (tauZoo k) .dupoc .cimcic)
        = some Action.C := by
  obtain ⟨kL, hLb⟩ := dupoc_cimcic_mutual
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 12
  refine ⟨max kL kA, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hLb k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hkA' : 1 * Nat.log2 k + 12 ≤ k :=
    hkA k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  have hkk : c_guard k + 5 ≤ k := by simp only [c_guard, numCost]; omega
  -- the CIMCIC component really cooperates in self-play…
  have hint : (probe (.sys (dmSys k) 1)).interp := Pf_sound m _ hm
  have hplay := entry_C_of_interp hint
  -- …so its guard FIRED, giving `Pf k Bf`, hence the cheap `Pf k Af` certificate…
  have hfired := sysSearcher_fired_of_plays (by decide) _ _ (dmSys_get1 k) hplay
  rw [sysClose_subst_cimSelfIdx] at hfired
  have hAf := pf_Af_of_Bf_dm hkk ((proofSearch_spec _ _).1 hfired)
  -- …which fires the head Dupoc's trust-probe.
  rw [inst_dupoc_cimcic_eq k]
  refine sysSearcher_plays_then _ _ (dmSys_get0 k) ?_
  rw [sysClose_subst_botSelfIdx]
  exact (proofSearch_spec _ _).2 hAf

/-! ## Row-facing plays for the remaining TRUE cells -/

/-- τ(CIMCIC) COOPERATES with the behavioral TFT. -/
theorem cimcic_tftSim_plays_C {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k)
    (hkk : c_guard k + 20 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .tftSim))
      (.bot (inst (tauZoo k) .cimcic .tftSim)) (inst (tauZoo k) .cimcic .tftSim)
      = some Action.C := by
  rw [inst_cimcic_peel_tftSim k]
  refine searchGuard_plays_C _ _ ?_
  rw [cimG_subst]
  exact (proofSearch_spec _ _).2 (pf_cimG_tftSim hL hkk)

/-- τ(CIMCIC) COOPERATES with the prover TFT. -/
theorem cimcic_tftPf_plays_C {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k)
    (hkk : c_guard k + 20 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .tftPf))
      (.bot (inst (tauZoo k) .cimcic .tftPf)) (inst (tauZoo k) .cimcic .tftPf)
      = some Action.C := by
  rw [inst_cimcic_peel_tftPf k]
  refine searchGuard_plays_C _ _ ?_
  rw [cimG_subst]
  exact (proofSearch_spec _ _).2 (pf_cimG_tftPf hL hkk)

/-- τ(CIMCIC) COOPERATES with τ(Just) — conditionally on the entangled Löb bit,
    which τ(Just) probes. -/
theorem cimcic_just_plays_C {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k)
    (hcq : proofSearch k (probe (inst (tauZoo k) .cimcic .dupoc)) = true) :
    ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .just))
      (.bot (inst (tauZoo k) .cimcic .just)) (inst (tauZoo k) .cimcic .just)
      = some Action.C := by
  rw [inst_cimcic_peel_just k]
  refine searchGuard_plays_C _ _ ?_
  rw [cimG_subst]
  exact (proofSearch_spec _ _).2 (pf_cimG_just hL hcq)
