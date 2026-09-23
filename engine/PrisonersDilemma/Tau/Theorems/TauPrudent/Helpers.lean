import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Base.Loeb
import PrisonersDilemma.Tau.Theorems.TauMirror.Helpers
import PrisonersDilemma.Tau.Theorems.TauDIMCID.Helpers
import PrisonersDilemma.Tau.Theorems.TauCupod.Helpers
import PrisonersDilemma.Tau.Theorems.TauCupodTroll.Helpers

/-!
# Tau/Theorems/TauPrudent — Critch's canonical bot at one budget (2026-08-25)

τ(Prudent) is `search (probe P) (search (probeD (inst T defect)) C D) D`: cooperate
iff "the hypothesis PROVABLY cooperates with me" AND "it PROVABLY defects on the
defector". At a single shared budget the row is `D` everywhere except against the
forwarder, and the reason is uniform:

* the INNER check `probeD (inst T defect)` is floor-unprovable for exactly the
  partners whose defection on the defector is an ELSE-play (coop, tftPf, dupoc,
  just, dbot, cupodTroll, cimcic, prudent itself) — base needs `PrudentBot (2k+64)`
  to pay that floor; here the search simply fails and Prudent defects;
* where the inner check passes cheaply (defect, tftSim, obot, ebot, guardian,
  cupod, dimcid, mirror), the OUTER probe fails: by soundness (defect, tftSim,
  obot play D on it), by a watch-cost floor (ebot's C embeds Prudent's own
  floor-priced D on the defector), or by an else-play floor (guardian, cupod,
  dimcid trust it without a certificate) — except the mirror, which forwards
  Prudent's own cooperation and closes the Löb cycle through the binder.

The mirror pair needs the one new reading rule of this port,
`Pf.botSysSearchThenSearch` — the `.sys` twin of `searchThenSearch_t` — for
Prudent's leg; the forwarder's leg is `botSysSimStep` as before.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## The nested shape — plays and transcripts -/

/-- A two-stage prudent searcher DEFECTS whenever its INNER check fails,
    whatever the outer says. -/
theorem nested_plays_D_of_inner {k : Nat} {g₁ g₂ : Formula} (me opp : Prog)
    (h₂ : proofSearch k (g₂.subst me opp) = false) :
    ∃ N, eval N me opp (.search k g₁ (.search k g₂ (.const .C) (.const .D)) (.const .D))
      = some Action.D := by
  refine ⟨3, ?_⟩
  rw [eval]
  cases h₁ : proofSearch k (g₁.subst me opp)
  · simp only [Bool.false_eq_true, if_false]; rfl
  · simp only [if_true]; rw [eval, h₂]; simp only [Bool.false_eq_true, if_false]; rfl

/-- …and DEFECTS whenever the OUTER probe fails. -/
theorem nested_plays_D_of_outer {k : Nat} {g₁ g₂ : Formula} (me opp : Prog)
    (h₁ : proofSearch k (g₁.subst me opp) = false) :
    ∃ N, eval N me opp (.search k g₁ (.search k g₂ (.const .C) (.const .D)) (.const .D))
      = some Action.D := by
  refine ⟨2, ?_⟩
  rw [eval, h₁]; simp only [Bool.false_eq_true, if_false]; rfl

/-- …and COOPERATES when both fire. -/
theorem nested_plays_C_of_both {k : Nat} {g₁ g₂ : Formula} (me opp : Prog)
    (h₁ : proofSearch k (g₁.subst me opp) = true)
    (h₂ : proofSearch k (g₂.subst me opp) = true) :
    ∃ N, eval N me opp (.search k g₁ (.search k g₂ (.const .C) (.const .D)) (.const .D))
      = some Action.C := by
  refine ⟨3, ?_⟩
  rw [eval, h₁]; simp only [if_true]; rw [eval, h₂]; simp only [if_true]; rfl

-- `nested_D_transcript_ge` / `nested_C_transcript_inner` moved to `Base/Exclusion.lean`
-- (2026-08-25) with the `no_provable_sysNested_*_tail` censuses they serve.
/-- The else-play of a `.bot`-wrapped constant-branch searcher is uncitable at ≤ k,
    in ANY frame — the singleton floor kernel, packaged as a bit. -/
theorem ps_botSearcherElse_false {k K : Nat} (hK : K ≤ k) (g : Formula) (aT aE : Action)
    (hne : aT ≠ aE) (O : Prog) :
    proofSearch K (.plays (.bot (.search k g (.const aT) (.const aE))) O aE) = false := by
  cases h : proofSearch K (.plays (.bot (.search k g (.const aT) (.const aE))) O aE) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_botSearcherElse_tail k k g aT aE (.const aE) hne (Nat.le_refl k) O
        K _ ((proofSearch_spec _ _).1 h) hK rfl

/-! ## The inner column: `probeD (inst T .defect)` — who provably defects on the defector

TRUE (cheap D transcripts) for defect, tftSim, ebot, obot, guardian, cupod, dimcid,
mirror; FALSE for coop (it cooperates), and for tftPf, dupoc, just, cimcic, prudent
(their D is a floor-priced ELSE-play), dbot and cupodTroll (they cooperate). -/

theorem ps_probeD_inst_coop_defect_false {k : Nat} :
    proofSearch k (probeD (inst (tauZoo k) .coop .defect)) = false :=
  ps_probeD_false_of_plays_C k ⟨1, rfl⟩

theorem ps_probeD_inst_tftPf_defect_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probeD (inst (tauZoo k) .tftPf .defect)) = false := by
  rw [inst_tftPf_peel k .defect]; exact ps_probeD_searchProbe_false hK _

theorem ps_probeD_inst_dupoc_defect_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probeD (inst (tauZoo k) .dupoc .defect)) = false := by
  rw [show inst (tauZoo k) .dupoc .defect
      = .search k (probe (inst (tauZoo k) .defect .dupoc)) (.const .C) (.const .D) from rfl]
  exact ps_probeD_searchProbe_false hK _

theorem ps_probeD_inst_just_defect_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probeD (inst (tauZoo k) .just .defect)) = false := by
  rw [show inst (tauZoo k) .just .defect
      = .search k (probe (inst (tauZoo k) .defect .dupoc)) (.const .C) (.const .D) from rfl]
  exact ps_probeD_searchProbe_false hK _

theorem ps_probeD_inst_dbot_defect_false {k : Nat} (hk : 2 ≤ k)
    (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    proofSearch k (probeD (inst (tauZoo k) .dbot .defect)) = false :=
  ps_probeD_false_of_plays_C k (by
    rw [inst_dbot_peel k .defect]
    exact simWatchC_falls _ _ ⟨1, rfl⟩ ⟨1, rfl⟩)

theorem ps_probeD_inst_cupodTroll_defect_false {k : Nat} (hk : 3 ≤ k) :
    proofSearch k (probeD (inst (tauZoo k) .cupodTroll .defect)) = false :=
  ps_probeD_false_of_plays_C k (cupodTroll_plays_C _ (by decide))

/-- CIMCIC's defection on the defector is an else-play behind an IMPL guard:
    no refutation, no certificate — floor. -/
theorem ps_probeD_inst_cimcic_defect_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probeD (inst (tauZoo k) .cimcic .defect)) = false := by
  rw [inst_cimcic_peel_defect k, probeD]
  exact ps_botSearcherElse_false hK _ .C .D (by decide) _

/-- The forwarder's D on the defector is cheap: `bot ∘ sim ∘ bot ∘ const`. -/
theorem pf_probeD_mirror_defect {k K : Nat} (hK : 5 ≤ K) :
    Pf K (probeD (inst (tauZoo k) .mirror .defect)) := by
  rw [probeD, show inst (tauZoo k) .mirror .defect
      = .sim (.bot (inst (tauZoo k) .defect .mirror)) (.bot (inst (tauZoo k) .defect .mirror))
      from rfl]
  exact Pf.atom ⟨PlaysProof.bot (playsProof_simFwd (I := inst (tauZoo k) .defect .mirror)
    (PlaysProof.const (a := Action.D))), by have := hcl; have := hcn; omega⟩

/-! ## τ(Prudent)'s OFF-CYCLE row — ten cells, all `D` -/

theorem prudent_coop_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .coop)) (.bot (inst (tauZoo k) .prudent .coop))
      (inst (tauZoo k) .prudent .coop) = some Action.D := by
  rw [inst_prudent_peel_coop k]
  exact nested_plays_D_of_inner _ _ (by rw [probeD_subst]; exact ps_probeD_inst_coop_defect_false)

theorem prudent_defect_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .defect)) (.bot (inst (tauZoo k) .prudent .defect))
      (inst (tauZoo k) .prudent .defect) = some Action.D := by
  rw [inst_prudent_peel_defect k]
  exact nested_plays_D_of_outer _ _ (by rw [probe_subst]; exact ps_probe_constD k)

/-- τ(TFTSim) sees τ(Prudent) defect on the cooperator, and copies it. -/
theorem tftSim_prudent_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .tftSim .prudent)) (.bot (inst (tauZoo k) .tftSim .prudent))
      (inst (tauZoo k) .tftSim .prudent) = some Action.D := by
  rw [inst_tftSim_peel k .prudent]
  exact simWatchC_falls _ _ prudent_coop_plays_D ⟨1, rfl⟩

theorem prudent_tftSim_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .tftSim)) (.bot (inst (tauZoo k) .prudent .tftSim))
      (inst (tauZoo k) .prudent .tftSim) = some Action.D := by
  rw [inst_prudent_peel_tftSim k]
  exact nested_plays_D_of_outer _ _
    (by rw [probe_subst]; exact ps_probe_false_of_plays_D k tftSim_prudent_plays_D)

theorem prudent_tftPf_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .tftPf)) (.bot (inst (tauZoo k) .prudent .tftPf))
      (inst (tauZoo k) .prudent .tftPf) = some Action.D := by
  rw [inst_prudent_peel_tftPf k]
  exact nested_plays_D_of_inner _ _
    (by rw [probeD_subst]; exact ps_probeD_inst_tftPf_defect_false (le_refl k))

theorem prudent_just_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .just)) (.bot (inst (tauZoo k) .prudent .just))
      (inst (tauZoo k) .prudent .just) = some Action.D := by
  rw [inst_prudent_peel_just k]
  exact nested_plays_D_of_inner _ _
    (by rw [probeD_subst]; exact ps_probeD_inst_just_defect_false (le_refl k))

/-- τ(OBot)'s first watch tests DEFECTION on the cooperator — and fires on Prudent. -/
theorem obot_prudent_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .obot .prudent)) (.bot (inst (tauZoo k) .obot .prudent))
      (inst (tauZoo k) .obot .prudent) = some Action.D := by
  rw [inst_obot_peel k .prudent]
  exact simTestD_fires _ _ prudent_coop_plays_D

theorem prudent_obot_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .obot)) (.bot (inst (tauZoo k) .prudent .obot))
      (inst (tauZoo k) .prudent .obot) = some Action.D := by
  rw [inst_prudent_peel_obot k]
  exact nested_plays_D_of_outer _ _
    (by rw [probe_subst]; exact ps_probe_false_of_plays_D k obot_prudent_plays_D)

theorem prudent_dbot_plays_D {k : Nat} (hk : 2 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .dbot)) (.bot (inst (tauZoo k) .prudent .dbot))
      (inst (tauZoo k) .prudent .dbot) = some Action.D := by
  rw [inst_prudent_peel_dbot k]
  exact nested_plays_D_of_inner _ _
    (by rw [probeD_subst]; exact ps_probeD_inst_dbot_defect_false hk hL)

theorem prudent_cupodTroll_plays_D {k : Nat} (hk : 3 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .cupodTroll))
      (.bot (inst (tauZoo k) .prudent .cupodTroll)) (inst (tauZoo k) .prudent .cupodTroll)
      = some Action.D := by
  rw [inst_prudent_peel_cupodTroll k]
  exact nested_plays_D_of_inner _ _
    (by rw [probeD_subst]; exact ps_probeD_inst_cupodTroll_defect_false hk)

/-! ### guardian and ebot — outer probes of floor-priced cooperation -/

/-- Guardian's cooperation with Prudent is an else-play: its punish-search on
    `inst .prudent .coop` fails. -/
theorem guardian_prudent_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .guardian .prudent))
      (.bot (inst (tauZoo k) .guardian .prudent)) (inst (tauZoo k) .guardian .prudent)
      = some Action.C := by
  rw [inst_guardian_peel k .prudent]
  refine searchProbeD_plays_C _ _ ?_
  -- Prudent's D on the cooperator is the INNER else-play: its certificate pays the floor
  cases h : proofSearch k (probeD (inst (tauZoo k) .prudent .coop)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      rw [probeD, inst_prudent_peel_coop k] at hp
      refine no_provable_tailTo_floor k _ _ .D ?_ ?_ ?_ ?_ ?_ ?_ ?_ k _ hp le_rfl rfl
      · rintro K hK ⟨hpp, hn⟩
        cases hpp with
        | bot hin =>
          have := nested_D_transcript_ge hin
          have := hcn; omega
      · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
          ⟨_, _, _, _, _, _, _, h⟩) <;> simp at h
      · intro defs i h; simp at h
      · intro k₁ ψ₁ k₂ ψ₂ c1 q h; simp at h
      · intro L; cases L with
        | nil => simp [searchPlug]
        | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug]
      · intro hd L; cases hd <;> simp [ctxPlug]
      · intro hd L h; cases hd <;> simp [plug2] at h

/-- The guard column's `.prudent` bit: Prudent's defection on the cooperator is
    uncitable at budget `k`. -/
theorem ps_probeD_inst_prudent_coop_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probeD (inst (tauZoo k) .prudent .coop)) = false := by
  cases h : proofSearch K (probeD (inst (tauZoo k) .prudent .coop)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      rw [probeD, inst_prudent_peel_coop k] at hp
      refine no_provable_tailTo_floor k _ _ .D ?_ ?_ ?_ ?_ ?_ ?_ ?_ K _ hp hK rfl
      · rintro K' hK' ⟨hpp, hn⟩
        cases hpp with
        | bot hin =>
          have := nested_D_transcript_ge hin
          have := hcn; omega
      · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
          ⟨_, _, _, _, _, _, _, h⟩) <;> simp at h
      · intro defs i h; simp at h
      · intro k₁ ψ₁ k₂ ψ₂ c1 q h; simp at h
      · intro L; cases L with
        | nil => simp [searchPlug]
        | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug]
      · intro hd L; cases hd <;> simp [ctxPlug]
      · intro hd L h; cases hd <;> simp [plug2] at h

theorem prudent_guardian_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .guardian))
      (.bot (inst (tauZoo k) .prudent .guardian)) (inst (tauZoo k) .prudent .guardian)
      = some Action.D := by
  rw [inst_prudent_peel_guardian k]
  refine nested_plays_D_of_outer _ _ ?_
  rw [probe_subst, probe, inst_guardian_peel k .prudent]
  exact ps_botSearcherElse_false (le_refl k) _ .D .C (by decide) _

/-- A watch on `inst .prudent .defect` costs more than `k`: its D is an outer
    else-play (floor), and a C transcript is unsound. -/
theorem prudent_defect_watch_over_budget {k : Nat} {me opp : Prog} {r : Action} {m : Nat}
    (h : PlaysProof me opp
      (.sim (.bot (inst (tauZoo k) .prudent .defect)) (.bot (inst (tauZoo k) .prudent .defect))) r m)
    (hm : m ≤ k) : False := by
  cases h with
  | sim hin =>
    simp only [Prog.subst] at hin
    cases hin with
    | bot hin3 =>
      rename_i m₃
      cases r with
      | D =>
          rw [inst_prudent_peel_defect k] at hin3
          have := nested_D_transcript_ge hin3
          have := hcn; omega
      | C =>
          have hcert : AtomProvable (m₃ + c_node)
              (.plays (.bot (inst (tauZoo k) .prudent .defect))
                (.bot (inst (tauZoo k) .prudent .defect)) Action.C) :=
            ⟨PlaysProof.bot hin3, le_refl _⟩
          obtain ⟨n, hn⟩ := Pf_sound _ _ (Pf.atom hcert)
          obtain ⟨N, hN⟩ := prudent_defect_plays_D (k := k)
          have hN' : eval (N + 1) (.bot (inst (tauZoo k) .prudent .defect))
              (.bot (inst (tauZoo k) .prudent .defect)) (.bot (inst (tauZoo k) .prudent .defect))
              = some Action.D := by rw [eval]; exact hN
          rw [play] at hn
          exact absurd (eval_det hn hN') (by decide)

/-- τ(EBot) COOPERATES with Prudent (its third watch sees Prudent cooperate with the
    mirror), but that cooperation embeds Prudent's floor-priced D on the defector,
    so it is uncitable at budget `k`: Prudent's outer probe fails. -/
theorem ps_probe_inst_ebot_prudent_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probe (inst (tauZoo k) .ebot .prudent)) = false := by
  cases h : proofSearch K (probe (inst (tauZoo k) .ebot .prudent)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      rw [probe, inst_ebot_peel k .prudent] at hp
      refine no_provable_tailTo_floor k _ _ .C ?_ ?_ ?_ ?_ ?_ ?_ ?_ K _ hp hK rfl
      · rintro K' hK' ⟨hpp, hn⟩
        cases hpp with
        | bot hin =>
          cases hin with
          | ite_t hg _ _ => exact prudent_defect_watch_over_budget hg (by omega)
          | ite_f hg _ _ => exact prudent_defect_watch_over_budget hg (by omega)
      · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
          ⟨_, _, _, _, _, _, _, h⟩) <;> simp at h
      · intro defs i h; simp at h
      · intro k₁ ψ₁ k₂ ψ₂ c1 q h; simp at h
      · intro L; cases L with
        | nil => simp [searchPlug]
        | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug]
      · intro hd L; cases hd <;> simp [ctxPlug]
      · intro hd L h; cases hd <;> simp [plug2] at h

theorem prudent_ebot_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .ebot)) (.bot (inst (tauZoo k) .prudent .ebot))
      (inst (tauZoo k) .prudent .ebot) = some Action.D := by
  rw [inst_prudent_peel_ebot k]
  exact nested_plays_D_of_outer _ _
    (by rw [probe_subst]; exact ps_probe_inst_ebot_prudent_false (le_refl k))

/-! ## The DIAGONAL — the inner check on its own δ_D cell fails -/

/-- Prudent's own D on the defector is an outer else-play — floor-priced. -/
theorem ps_probeD_inst_prudent_defect_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probeD (inst (tauZoo k) .prudent .defect)) = false := by
  cases h : proofSearch K (probeD (inst (tauZoo k) .prudent .defect)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      rw [probeD, inst_prudent_peel_defect k] at hp
      refine no_provable_tailTo_floor k _ _ .D ?_ ?_ ?_ ?_ ?_ ?_ ?_ K _ hp hK rfl
      · rintro K' hK' ⟨hpp, hn⟩
        cases hpp with
        | bot hin =>
          have := nested_D_transcript_ge hin
          have := hcn; omega
      · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
          ⟨_, _, _, _, _, _, _, h⟩) <;> simp at h
      · intro defs i h; simp at h
      · intro k₁ ψ₁ k₂ ψ₂ c1 q h; simp at h
      · intro L; cases L with
        | nil => simp [searchPlug]
        | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug]
      · intro hd L; cases hd <;> simp [ctxPlug]
      · intro hd L h; cases hd <;> simp [plug2] at h

/-- **τ(Prudent) DEFECTS AGAINST ITSELF** — single-tier prudence is self-defeating
    (base `outcome_PrudentBot_vs_PrudentBot = (D, D)`). -/
theorem prudent_quine_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .prudent))
      (.bot (inst (tauZoo k) .prudent .prudent)) (inst (tauZoo k) .prudent .prudent)
      = some Action.D := by
  rw [inst_prudent_quine k]
  exact nested_plays_D_of_inner _ _
    (by rw [probeD_subst]; exact ps_probeD_inst_prudent_defect_false (le_refl k))

/-! ## The ENTANGLED systems

Prudent self-probes, so it entangles with dupoc, cupod, cimcic, dimcid and mirror.
Its member is the nested shape with the partner as `.selfIdx 1` in the OUTER
guard and the partner's δ_D instance (a third party) in the inner. -/

/-- A nested system member defects when its inner check fails… -/
theorem sysNested_plays_D_of_inner {defs : ProgList} {i k : Nat} {g₁ g₂ : Formula}
    (me opp : Prog)
    (hget : defs.get? i = some (.search k g₁ (.search k g₂ (.const .C) (.const .D)) (.const .D)))
    (h₂ : proofSearch k ((g₂.sysClose defs).subst me opp) = false) :
    ∃ N, eval N me opp (.sys defs i) = some Action.D := by
  obtain ⟨N, hN⟩ := nested_plays_D_of_inner (k := k) (g₁ := g₁.sysClose defs)
    (g₂ := g₂.sysClose defs) me opp h₂
  refine ⟨N + 1, ?_⟩
  rw [eval_sys_some N hget]
  simp only [Prog.sysClose]
  exact hN

/-- …and when its outer probe fails. -/
theorem sysNested_plays_D_of_outer {defs : ProgList} {i k : Nat} {g₁ g₂ : Formula}
    (me opp : Prog)
    (hget : defs.get? i = some (.search k g₁ (.search k g₂ (.const .C) (.const .D)) (.const .D)))
    (h₁ : proofSearch k ((g₁.sysClose defs).subst me opp) = false) :
    ∃ N, eval N me opp (.sys defs i) = some Action.D := by
  obtain ⟨N, hN⟩ := nested_plays_D_of_outer (k := k) (g₁ := g₁.sysClose defs)
    (g₂ := g₂.sysClose defs) me opp h₁
  refine ⟨N + 1, ?_⟩
  rw [eval_sys_some N hget]
  simp only [Prog.sysClose]
  exact hN

-- `no_provable_sysNested_D_tail` moved to `Base/Exclusion.lean` (2026-08-25): a shape-general census
-- with no tau content — one census library for base and tau.

-- `no_provable_sysNested_C_tail` moved to `Base/Exclusion.lean` (2026-08-25): a shape-general census
-- with no tau content — one census library for base and tau.

/-! ### prudent × dupoc — the inner check on Dupoc's else-play D fails: `(D, D)` -/

def pdSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
          (.search k (probeD (inst (tauZoo k) .dupoc .defect)) (.const .C) (.const .D))
          (.const .D))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
    (.const .C) (.const .D)) .nil)

theorem inst_prudent_dupoc_eq (k : Nat) : inst (tauZoo k) .prudent .dupoc = .sys (pdSys k) 0 := rfl
theorem pdSys_get0 (k : Nat) : (pdSys k).get? 0
    = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
        (.search k (probeD (inst (tauZoo k) .dupoc .defect)) (.const .C) (.const .D))
        (.const .D)) := rfl
theorem pdSys_get1 (k : Nat) : (pdSys k).get? 1
    = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
        (.const .C) (.const .D)) := rfl

def dpSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
    (.const .C) (.const .D))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
          (.search k (probeD (inst (tauZoo k) .dupoc .defect)) (.const .C) (.const .D))
          (.const .D)) .nil)

theorem inst_dupoc_prudent_eq (k : Nat) : inst (tauZoo k) .dupoc .prudent = .sys (dpSys k) 0 := rfl
theorem dpSys_get0 (k : Nat) : (dpSys k).get? 0
    = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
        (.const .C) (.const .D)) := rfl
theorem dpSys_get1 (k : Nat) : (dpSys k).get? 1
    = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
        (.search k (probeD (inst (tauZoo k) .dupoc .defect)) (.const .C) (.const .D))
        (.const .D)) := rfl

/-- The inner guard, closed and substituted, is the plain δ_D probe bit (no pronoun in it). -/
theorem sysClose_subst_probeD (defs : ProgList) (I me o : Prog) (hI : I.sysClose defs = I) :
    ((probeD I).sysClose defs).subst me o = probeD I := by
  simp [probeD, Formula.sysClose, Prog.sysClose, Formula.subst, Prog.subst, hI]

theorem prudent_dupoc_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .dupoc)) (.bot (inst (tauZoo k) .prudent .dupoc))
      (inst (tauZoo k) .prudent .dupoc) = some Action.D := by
  rw [inst_prudent_dupoc_eq k]
  exact sysNested_plays_D_of_inner _ _ (pdSys_get0 k)
    (by rw [sysClose_subst_probeD _ _ _ _ rfl]; exact ps_probeD_inst_dupoc_defect_false (le_refl k))

/-- The δ_L column's `.prudent` bit: Prudent's member does not cooperate. -/
theorem ps_probe_inst_prudent_dupoc_false {k K : Nat} :
    proofSearch K (probe (inst (tauZoo k) .prudent .dupoc)) = false :=
  ps_probe_false_of_plays_D K prudent_dupoc_plays_D

theorem dupoc_prudent_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .prudent)) (.bot (inst (tauZoo k) .dupoc .prudent))
      (inst (tauZoo k) .dupoc .prudent) = some Action.D := by
  rw [inst_dupoc_prudent_eq k]
  refine sysSearcher_plays_else _ _ (dpSys_get0 k) ?_
  rw [sysClose_subst_botSelfIdx]
  refine ps_probe_false_of_plays_D k ?_
  exact sysNested_plays_D_of_inner _ _ (dpSys_get1 k)
    (by rw [sysClose_subst_probeD _ _ _ _ rfl]; exact ps_probeD_inst_dupoc_defect_false (le_refl k))

/-! ### prudent × cupod — `(D, C)`: the value base only STIPULATES -/

def pcSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
          (.search k (probeD (inst (tauZoo k) .cupod .defect)) (.const .C) (.const .D))
          (.const .D))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.D)
    (.const .D) (.const .C)) .nil)

theorem inst_prudent_cupod_eq (k : Nat) : inst (tauZoo k) .prudent .cupod = .sys (pcSys k) 0 := rfl
theorem pcSys_get0 (k : Nat) : (pcSys k).get? 0
    = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
        (.search k (probeD (inst (tauZoo k) .cupod .defect)) (.const .C) (.const .D))
        (.const .D)) := rfl
theorem pcSys_get1 (k : Nat) : (pcSys k).get? 1
    = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.D)
        (.const .D) (.const .C)) := rfl

def cpSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.D)
    (.const .D) (.const .C))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
          (.search k (probeD (inst (tauZoo k) .cupod .defect)) (.const .C) (.const .D))
          (.const .D)) .nil)

theorem inst_cupod_prudent_eq (k : Nat) : inst (tauZoo k) .cupod .prudent = .sys (cpSys k) 0 := rfl
theorem cpSys_get0 (k : Nat) : (cpSys k).get? 0
    = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.D)
        (.const .D) (.const .C)) := rfl
theorem cpSys_get1 (k : Nat) : (cpSys k).get? 1
    = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
        (.search k (probeD (inst (tauZoo k) .cupod .defect)) (.const .C) (.const .D))
        (.const .D)) := rfl

/-- Prudent's OUTER probe of the Cupod member fails: Cupod's trust is an else-play. -/
theorem prudent_cupod_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .cupod)) (.bot (inst (tauZoo k) .prudent .cupod))
      (inst (tauZoo k) .prudent .cupod) = some Action.D := by
  rw [inst_prudent_cupod_eq k]
  refine sysNested_plays_D_of_outer _ _ (pcSys_get0 k) ?_
  rw [sysClose_subst_botSelfIdx]
  exact ps_botSys_mismatch_false (le_refl k) (pcSys k) 1 k _ .D .C _ (by decide)
    (Nat.le_refl k) (pcSys_get1 k) _

/-- δ_Cu's `.prudent` bit: Prudent's D on Cupod is an else-play, floor-priced. -/
theorem ps_probeD_inst_prudent_cupod_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probeD (inst (tauZoo k) .prudent .cupod)) = false := by
  cases h : proofSearch K (probeD (inst (tauZoo k) .prudent .cupod)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      rw [probeD, inst_prudent_cupod_eq k] at hp
      exact no_provable_sysNested_D_tail k (pcSys k) 0 _ _ (pcSys_get0 k) _ K _ hp hK rfl

/-- Cupod at the head TRUSTS Prudent: it cannot convict it. -/
theorem cupod_prudent_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .cupod .prudent)) (.bot (inst (tauZoo k) .cupod .prudent))
      (inst (tauZoo k) .cupod .prudent) = some Action.C := by
  rw [inst_cupod_prudent_eq k]
  refine sysSearcher_plays_else _ _ (cpSys_get0 k) ?_
  rw [sysClose_subst_botSelfIdx]
  cases h : proofSearch k (.plays (.bot (.sys (cpSys k) 1)) (.bot (.sys (cpSys k) 1)) Action.D) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_sysNested_D_tail k (cpSys k) 1 _ _ (cpSys_get1 k) _ k _
        ((proofSearch_spec _ _).1 h) le_rfl rfl

/-! ### prudent × cimcic — `(D, D)`: the inner check fails, and CIMCIC cannot
certify a cooperation Prudent never offers -/

def pmSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
          (.search k (probeD (inst (tauZoo k) .cimcic .defect)) (.const .C) (.const .D))
          (.const .D))
  (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                           (.plays (.bot (.selfIdx 0)) .self Action.C))
    (.const .C) (.const .D)) .nil)

theorem inst_prudent_cimcic_eq (k : Nat) : inst (tauZoo k) .prudent .cimcic = .sys (pmSys k) 0 := rfl
theorem pmSys_get0 (k : Nat) : (pmSys k).get? 0
    = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
        (.search k (probeD (inst (tauZoo k) .cimcic .defect)) (.const .C) (.const .D))
        (.const .D)) := rfl

def mpSys (k : Nat) : ProgList :=
  .cons (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                          (.plays (.bot (.selfIdx 1)) .self Action.C))
    (.const .C) (.const .D))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
          (.search k (probeD (inst (tauZoo k) .cimcic .defect)) (.const .C) (.const .D))
          (.const .D)) .nil)

theorem inst_cimcic_prudent_eq (k : Nat) : inst (tauZoo k) .cimcic .prudent = .sys (mpSys k) 0 := rfl
theorem mpSys_get0 (k : Nat) : (mpSys k).get? 0
    = some (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                             (.plays (.bot (.selfIdx 1)) .self Action.C))
        (.const .C) (.const .D)) := rfl
theorem mpSys_get1 (k : Nat) : (mpSys k).get? 1
    = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
        (.search k (probeD (inst (tauZoo k) .cimcic .defect)) (.const .C) (.const .D))
        (.const .D)) := rfl

theorem prudent_cimcic_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .cimcic)) (.bot (inst (tauZoo k) .prudent .cimcic))
      (inst (tauZoo k) .prudent .cimcic) = some Action.D := by
  rw [inst_prudent_cimcic_eq k]
  exact sysNested_plays_D_of_inner _ _ (pmSys_get0 k)
    (by rw [sysClose_subst_probeD _ _ _ _ rfl]; exact ps_probeD_inst_cimcic_defect_false (le_refl k))

/-- CIMCIC's guard against the Prudent member is unprovable: its consequent — the
    Prudent member cooperates with it — has no certificate, because the nested
    bridge's held premise (Prudent's inner check on CIMCIC) is floor-false. -/
theorem cimcic_prudent_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .prudent)) (.bot (inst (tauZoo k) .cimcic .prudent))
      (inst (tauZoo k) .cimcic .prudent) = some Action.D := by
  rw [inst_cimcic_prudent_eq k]
  refine sysSearcher_plays_else _ _ (mpSys_get0 k) ?_
  rw [sysClose_subst_cimSelfIdx]
  cases h : proofSearch k (.impl (.plays (.bot (.sys (mpSys k) 0)) (.bot (.sys (mpSys k) 1)) Action.C)
      (.plays (.bot (.sys (mpSys k) 1)) (.bot (.sys (mpSys k) 0)) Action.C)) with
  | false => rfl
  | true =>
      exfalso
      refine no_provable_sysNested_C_tail k (mpSys k) 1 _ _ (mpSys_get1 k) _ ?_ k _
        ((proofSearch_spec _ _).1 h) le_rfl ⟨rfl, by simp⟩
      intro m hm me oppo hpf
      rw [sysClose_subst_probeD _ _ _ _ rfl] at hpf
      exact absurd ((proofSearch_spec _ _).2 hpf)
        (by rw [ps_probeD_inst_cimcic_defect_false hm]; decide)

/-! ### prudent × dimcid — `(D, C)`: the outer probe of DIMCID's trust fails, and
DIMCID's guard needs a defection Prudent never certifies -/

def pdiSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
          (.search k (probeD (inst (tauZoo k) .dimcid .defect)) (.const .C) (.const .D))
          (.const .D))
  (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                           (.plays (.bot (.selfIdx 0)) .self Action.D))
    (.const .D) (.const .C)) .nil)

theorem inst_prudent_dimcid_eq (k : Nat) : inst (tauZoo k) .prudent .dimcid = .sys (pdiSys k) 0 := rfl
theorem pdiSys_get0 (k : Nat) : (pdiSys k).get? 0
    = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
        (.search k (probeD (inst (tauZoo k) .dimcid .defect)) (.const .C) (.const .D))
        (.const .D)) := rfl
theorem pdiSys_get1 (k : Nat) : (pdiSys k).get? 1
    = some (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                             (.plays (.bot (.selfIdx 0)) .self Action.D))
        (.const .D) (.const .C)) := rfl

def dipSys (k : Nat) : ProgList :=
  .cons (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                          (.plays (.bot (.selfIdx 1)) .self Action.D))
    (.const .D) (.const .C))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
          (.search k (probeD (inst (tauZoo k) .dimcid .defect)) (.const .C) (.const .D))
          (.const .D)) .nil)

theorem inst_dimcid_prudent_eq (k : Nat) : inst (tauZoo k) .dimcid .prudent = .sys (dipSys k) 0 := rfl
theorem dipSys_get0 (k : Nat) : (dipSys k).get? 0
    = some (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                             (.plays (.bot (.selfIdx 1)) .self Action.D))
        (.const .D) (.const .C)) := rfl
theorem dipSys_get1 (k : Nat) : (dipSys k).get? 1
    = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
        (.search k (probeD (inst (tauZoo k) .dimcid .defect)) (.const .C) (.const .D))
        (.const .D)) := rfl

theorem prudent_dimcid_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .dimcid)) (.bot (inst (tauZoo k) .prudent .dimcid))
      (inst (tauZoo k) .prudent .dimcid) = some Action.D := by
  rw [inst_prudent_dimcid_eq k]
  refine sysNested_plays_D_of_outer _ _ (pdiSys_get0 k) ?_
  rw [sysClose_subst_botSelfIdx]
  exact ps_botSys_mismatch_false (le_refl k) (pdiSys k) 1 k _ .D .C _ (by decide)
    (Nat.le_refl k) (pdiSys_get1 k) _

theorem dimcid_prudent_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .prudent)) (.bot (inst (tauZoo k) .dimcid .prudent))
      (inst (tauZoo k) .dimcid .prudent) = some Action.C := by
  rw [inst_dimcid_prudent_eq k]
  refine sysSearcher_plays_else _ _ (dipSys_get0 k) ?_
  rw [sysClose_subst_cimSelfIdxD]
  cases h : proofSearch k (.impl (.plays (.bot (.sys (dipSys k) 0)) (.bot (.sys (dipSys k) 1)) Action.C)
      (.plays (.bot (.sys (dipSys k) 1)) (.bot (.sys (dipSys k) 0)) Action.D)) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_sysNested_D_tail k (dipSys k) 1 _ _ (dipSys_get1 k) _ k _
        ((proofSearch_spec _ _).1 h) le_rfl ⟨rfl, by simp⟩

/-! ### prudent × mirror — `(C, C)` by bounded Löb through the binder

Prudent's inner check on the mirror passes cheaply (the forwarder copies the
defector). Its outer probe is the mirror member's self-cooperation, and the
mirror member forwards Prudent's; so with `φ` := "the mirror member self-cooperates":
`□φ → Prudent's member cooperates` (the NEW nested reading rule, inner premise
held) and `Prudent's member cooperates → φ` (the forwarder). Single engine. -/

def pmirSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
          (.search k (probeD (inst (tauZoo k) .mirror .defect)) (.const .C) (.const .D))
          (.const .D))
  (.cons (.sim (.bot (.selfIdx 0)) (.bot (.selfIdx 0))) .nil)

theorem inst_prudent_mirror_eq (k : Nat) : inst (tauZoo k) .prudent .mirror = .sys (pmirSys k) 0 := rfl
theorem pmirSys_get0 (k : Nat) : (pmirSys k).get? 0
    = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
        (.search k (probeD (inst (tauZoo k) .mirror .defect)) (.const .C) (.const .D))
        (.const .D)) := rfl
theorem pmirSys_get1 (k : Nat) : (pmirSys k).get? 1
    = some (.sim (.bot (.selfIdx 0)) (.bot (.selfIdx 0))) := rfl

def mirpSys (k : Nat) : ProgList :=
  .cons (.sim (.bot (.selfIdx 1)) (.bot (.selfIdx 1)))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
          (.search k (probeD (inst (tauZoo k) .mirror .defect)) (.const .C) (.const .D))
          (.const .D)) .nil)

theorem inst_mirror_prudent_eq (k : Nat) : inst (tauZoo k) .mirror .prudent = .sys (mirpSys k) 0 := rfl
theorem mirpSys_get0 (k : Nat) : (mirpSys k).get? 0
    = some (.sim (.bot (.selfIdx 1)) (.bot (.selfIdx 1))) := rfl
theorem mirpSys_get1 (k : Nat) : (mirpSys k).get? 1
    = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
        (.search k (probeD (inst (tauZoo k) .mirror .defect)) (.const .C) (.const .D))
        (.const .D)) := rfl

/-- Prudent's leg, generic: □(the forwarder member self-cooperates) → Prudent's
    member cooperates, with the inner check on the mirror's δ_D cell held. -/
theorem sys_prudent_leg (defs : ProgList) (p f k K : Nat) (opp : Prog)
    (hget : defs.get? p = some (.search k (.plays (.bot (.selfIdx f)) (.bot (.selfIdx f)) Action.C)
        (.search k (probeD (inst (tauZoo k) .mirror .defect)) (.const .C) (.const .D))
        (.const .D)))
    (h5 : 5 ≤ k)
    (hK : c_guard k + (Formula.impl (.box k (.plays (.bot (.sys defs f)) (.bot (.sys defs f)) Action.C))
        (.plays (.bot (.sys defs p)) opp Action.C)).size ≤ K) :
    Pf K (.impl (.box k (.plays (.bot (.sys defs f)) (.bot (.sys defs f)) Action.C))
                (.plays (.bot (.sys defs p)) opp Action.C)) := by
  have h := Pf.botSysSearchThenSearch defs p k k k
    (.plays (.bot (.selfIdx f)) (.bot (.selfIdx f)) Action.C)
    (probeD (inst (tauZoo k) .mirror .defect)) .C .D (.const .D)
    (.bot (.sys defs p)) opp rfl hget
    (by rw [sysClose_subst_probeD _ _ _ _ rfl]; exact pf_probeD_mirror_defect h5) le_rfl
    (by simpa [sysClose_subst_botSelfIdx] using hK)
  rw [sysClose_subst_botSelfIdx] at h
  exact h

/-- The forwarder's δ_D cell, concretely: it copies the defector. -/
theorem inst_mirror_defect_eq (k : Nat) :
    inst (tauZoo k) .mirror .defect = .sim (.bot (.const .D)) (.bot (.const .D)) := rfl

private theorem log_facts'' (k : Nat) :
    Nat.log2 k ≤ k ∧ Nat.log2 0 = 0 ∧ Nat.log2 1 = 0 :=
  ⟨Nat.log2_le_self k, by decide, by decide⟩

private def pmA (k : Nat) : Formula :=   -- the forwarder member (index 1) self-cooperates
  .plays (.bot (.sys (pmirSys k) 1)) (.bot (.sys (pmirSys k) 1)) Action.C
private def pmB (k : Nat) : Formula :=   -- Prudent's member (index 0) self-cooperates
  .plays (.bot (.sys (pmirSys k) 0)) (.bot (.sys (pmirSys k) 0)) Action.C

theorem pmir_loeb_premise (k : Nat) (h5 : 5 ≤ k) :
    Pf ((c_guard k + (Formula.impl (.box k (pmA k)) (pmB k)).size)
        + (Formula.impl (pmB k) (pmA k)).size
        + (Formula.impl (.box k (pmA k)) (pmA k)).size)
      (.impl (.box k (pmA k)) (pmA k)) :=
  Pf.implTrans _ _ _ _ _
    (sys_prudent_leg (pmirSys k) 0 1 k _ (.bot (.sys (pmirSys k) 0)) (pmirSys_get0 k) h5 le_rfl)
    (sys_mirror_fwd (pmirSys k) 1 0 .C _ (.bot (.sys (pmirSys k) 1)) (pmirSys_get1 k) le_rfl)
    le_rfl

theorem pmir_loeb : ∃ k₂, ∀ k, k₂ < k → ∃ m, 2 * m ≤ k ∧ Pf m (pmA k) := by
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  refine pblt_engine_id_bounded pmA
    (fun k => (c_guard k + (Formula.impl (.box k (pmA k)) (pmB k)).size)
        + (Formula.impl (pmB k) (pmA k)).size
        + (Formula.impl (.box k (pmA k)) (pmA k)).size) kA ?_ ?_ ?_
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts'' k
    simp only [pmA, Formula.size, Prog.size, ProgList.psize, pmirSys, probeD, inst_mirror_defect_eq, numCost]; omega
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts'' k
    simp only [pmA, pmB, c_guard, Formula.size, Prog.size, ProgList.psize, pmirSys, probeD, inst_mirror_defect_eq,
      numCost]; omega
  · intro k hk
    exact pmir_loeb_premise k (by have := hkA k (Nat.le_of_lt hk); omega)

/-- …and COOPERATES when both fire. -/
theorem sysNested_plays_C_of_both {defs : ProgList} {i k : Nat} {g₁ g₂ : Formula}
    (me opp : Prog)
    (hget : defs.get? i = some (.search k g₁ (.search k g₂ (.const .C) (.const .D)) (.const .D)))
    (h₁ : proofSearch k ((g₁.sysClose defs).subst me opp) = true)
    (h₂ : proofSearch k ((g₂.sysClose defs).subst me opp) = true) :
    ∃ N, eval N me opp (.sys defs i) = some Action.C := by
  obtain ⟨N, hN⟩ := nested_plays_C_of_both (k := k) (g₁ := g₁.sysClose defs)
    (g₂ := g₂.sysClose defs) me opp h₁ h₂
  refine ⟨N + 1, ?_⟩
  rw [eval_sys_some N hget]
  simp only [Prog.sysClose]
  exact hN

/-- **τ(Prudent) at Mirror COOPERATES** — the one cooperative cell of its row. -/
theorem prudent_mirror_plays_C :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .prudent .mirror)) (.bot (inst (tauZoo k) .prudent .mirror))
        (inst (tauZoo k) .prudent .mirror) = some Action.C := by
  obtain ⟨kL, hLb⟩ := pmir_loeb
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  refine ⟨max kL kA, fun k hk => ?_⟩
  obtain ⟨m, hmk, hm⟩ := hLb k (by omega)
  have h8 : 1 * Nat.log2 k + 8 ≤ k := hkA k (by omega)
  rw [inst_prudent_mirror_eq k]
  refine sysNested_plays_C_of_both _ _ (pmirSys_get0 k) ?_ ?_
  · rw [sysClose_subst_botSelfIdx]; exact (proofSearch_spec _ _).2 (Pf_mono hm (by omega))
  · rw [sysClose_subst_probeD _ _ _ _ rfl]; exact (proofSearch_spec _ _).2 (pf_probeD_mirror_defect (by omega))

/-- **τ(Mirror) at Prudent COOPERATES**: the forwarder copies the Löb-certified
    self-cooperation of Prudent's member (the other `.sys` orientation, its own run). -/
private def mpA (k : Nat) : Formula :=   -- the forwarder member (index 0) self-cooperates
  .plays (.bot (.sys (mirpSys k) 0)) (.bot (.sys (mirpSys k) 0)) Action.C
private def mpB (k : Nat) : Formula :=
  .plays (.bot (.sys (mirpSys k) 1)) (.bot (.sys (mirpSys k) 1)) Action.C

theorem mirp_loeb_premise (k : Nat) (h5 : 5 ≤ k) :
    Pf ((c_guard k + (Formula.impl (.box k (mpA k)) (mpB k)).size)
        + (Formula.impl (mpB k) (mpA k)).size
        + (Formula.impl (.box k (mpA k)) (mpA k)).size)
      (.impl (.box k (mpA k)) (mpA k)) :=
  Pf.implTrans _ _ _ _ _
    (sys_prudent_leg (mirpSys k) 1 0 k _ (.bot (.sys (mirpSys k) 1)) (mirpSys_get1 k) h5 le_rfl)
    (sys_mirror_fwd (mirpSys k) 0 1 .C _ (.bot (.sys (mirpSys k) 0)) (mirpSys_get0 k) le_rfl)
    le_rfl

theorem mirp_loeb : ∃ k₂, ∀ k, k₂ < k → ∃ m, 2 * m ≤ k ∧ Pf m (mpA k) := by
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  refine pblt_engine_id_bounded mpA
    (fun k => (c_guard k + (Formula.impl (.box k (mpA k)) (mpB k)).size)
        + (Formula.impl (mpB k) (mpA k)).size
        + (Formula.impl (.box k (mpA k)) (mpA k)).size) kA ?_ ?_ ?_
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts'' k
    simp only [mpA, Formula.size, Prog.size, ProgList.psize, mirpSys, probeD, inst_mirror_defect_eq, numCost]; omega
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts'' k
    simp only [mpA, mpB, c_guard, Formula.size, Prog.size, ProgList.psize, mirpSys, probeD, inst_mirror_defect_eq,
      numCost]; omega
  · intro k hk
    exact mirp_loeb_premise k (by have := hkA k (Nat.le_of_lt hk); omega)

theorem mirror_prudent_plays_C :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .mirror .prudent)) (.bot (inst (tauZoo k) .mirror .prudent))
        (inst (tauZoo k) .mirror .prudent) = some Action.C := by
  obtain ⟨kL, hLb⟩ := mirp_loeb
  refine ⟨kL, fun k hk => ?_⟩
  obtain ⟨m, -, hm⟩ := hLb k hk
  rw [inst_mirror_prudent_eq k]
  exact entry_of_interp (Pf_sound m _ hm)

end PD.Tau
