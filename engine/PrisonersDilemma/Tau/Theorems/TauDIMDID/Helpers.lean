import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Base.Loeb
import PrisonersDilemma.Base.TowerCensus
import PrisonersDilemma.Base.EvalTranspose
import PrisonersDilemma.Tau.Theorems.TauCIMCIC.Helpers
import PrisonersDilemma.Tau.Theorems.TauDIMCID.Helpers
import PrisonersDilemma.Tau.Theorems.TauPrudent.Helpers
import PrisonersDilemma.Tau.Theorems.TauMirror.Helpers

/-!
# Tau/Theorems/TauDIMDID/Helpers — τ(DIMDID)'s row: CIMCIC's, transposed (2026-10-19)

τ(DIMDID)'s guard at hypothesis T is `I defect vs I_T → I_T defects vs me` (`ddG`), searched at budget
`k`, firing `D` with default `C` — τ̂(τ(CIMCIC)) template by template (`tauDIMDIDSpec` is CIMCIC's spec
with the test and the branches swapped). The row splits in three:

* **the τ̂-closed part of the roster** (`coop ↔ defect`, `dupoc ↔ cupod`, `cimcic ↔ dimdid`, the τ-fixed
  `mirror`, and the natives through the Dupoc bridges): `inst (tauZoo k) .dimdid T = (inst (tauZoo k)
  .cimcic τT).transpose` by `rfl`, so every play is CIMCIC's play at `τT` with the action swapped
  (`plays_transpose`, `Base/EvalTranspose.lean`) and every proof-search bit is CIMCIC's bit by
  `Pf.transpose_iff` (`proofSearch_transpose`). Nothing new is proved for these cells;
* **the run-stage and prover partners** (tftSim, ebot, dbot, obot, tftPf, just): DIMCID's censuses at
  the other polarity — `TailTo` walks through the implication to its consequent, which is the partner's
  cooperation (no certificate: soundness) or a floor-priced defection, so the guard is unprovable and
  DIMDID falls through to `C`;
* **the entangled partners that are not τ̂-images** (prudent, dimcid — cimcic is one orientation of a
  τ̂-pair with itself): the floor on the nested system (prudent), the floor on the `cimcic × dimdid`
  system (one orientation direct, the other by τ̂), and the aligned-on-D mutual Löb with DIMCID.

Two cells (`guardian`, the two trolls) need the tower census, as DIMCID's did.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## The guard shape -/

/-- The substituted DIMDID guard: frame `me`, hypothesis instance `I`. -/
abbrev ddG (me I : Prog) : Formula :=
  .impl (.plays me (.bot I) Action.D) (.plays (.bot I) me Action.D)

theorem ddG_subst (I me o : Prog) :
    (Formula.impl (.plays .self (.bot I) Action.D)
                  (.plays (.bot I) .self Action.D)).subst me o
      = ddG me I := rfl

/-- The DIMDID member's guard, closed and substituted (the twin of `sysClose_subst_cimSelfIdxD`). -/
theorem sysClose_subst_ddSelfIdx (defs : ProgList) (j : Nat) (me o : Prog) :
    ((Formula.impl (.plays .self (.bot (.selfIdx j)) Action.D)
                   (.plays (.bot (.selfIdx j)) .self Action.D)).sysClose defs).subst me o
      = .impl (.plays me (.bot (.sys defs j)) Action.D)
              (.plays (.bot (.sys defs j)) me Action.D) := by
  simp [Formula.sysClose, Prog.sysClose, Formula.subst, Prog.subst]

/-! ## τ(DIMDID) = τ̂(τ(CIMCIC)) on the τ̂-closed part of the roster -/

theorem inst_dimdid_coop_tr (k : Nat) :
    inst (tauZoo k) .dimdid .coop = (inst (tauZoo k) .cimcic .defect).transpose := rfl
theorem inst_dimdid_defect_tr (k : Nat) :
    inst (tauZoo k) .dimdid .defect = (inst (tauZoo k) .cimcic .coop).transpose := rfl
theorem inst_dimdid_dupoc_tr (k : Nat) :
    inst (tauZoo k) .dimdid .dupoc = (inst (tauZoo k) .cimcic .cupod).transpose := rfl
theorem inst_dimdid_cupod_tr (k : Nat) :
    inst (tauZoo k) .dimdid .cupod = (inst (tauZoo k) .cimcic .dupoc).transpose := rfl
theorem inst_dimdid_cimcic_tr (k : Nat) :
    inst (tauZoo k) .dimdid .cimcic = (inst (tauZoo k) .cimcic .dimdid).transpose := rfl
theorem inst_dimdid_dimdid_tr (k : Nat) :
    inst (tauZoo k) .dimdid .dimdid = (inst (tauZoo k) .cimcic .cimcic).transpose := rfl
theorem inst_dimdid_mirror_tr (k : Nat) :
    inst (tauZoo k) .dimdid .mirror = (inst (tauZoo k) .cimcic .mirror).transpose := rfl
theorem inst_dupoc_dimdid_tr (k : Nat) :
    inst (tauZoo k) .dupoc .dimdid = (inst (tauZoo k) .cupod .cimcic).transpose := rfl
theorem inst_cupod_dimdid_tr (k : Nat) :
    inst (tauZoo k) .cupod .dimdid = (inst (tauZoo k) .dupoc .cimcic).transpose := rfl
theorem inst_cimcic_dimdid_tr (k : Nat) :
    inst (tauZoo k) .cimcic .dimdid = (inst (tauZoo k) .dimdid .cimcic).transpose := rfl
theorem inst_mirror_dimdid_tr (k : Nat) :
    inst (tauZoo k) .mirror .dimdid = (inst (tauZoo k) .mirror .cimcic).transpose := rfl

/-! ### The transported plays -/

/-- τ(DIMDID) at the cooperator COOPERATES — τ̂ of CIMCIC's defection on the defector. -/
theorem dimdid_coop_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .coop))
      (.bot (inst (tauZoo k) .dimdid .coop)) (inst (tauZoo k) .dimdid .coop)
      = some Action.C := by
  rw [inst_dimdid_coop_tr]; exact plays_transpose cimcic_defect_plays_D

/-- τ(DIMDID) at the defector DEFECTS — τ̂ of CIMCIC's cooperation with the cooperator. -/
theorem dimdid_defect_plays_D {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .defect))
      (.bot (inst (tauZoo k) .dimdid .defect)) (inst (tauZoo k) .dimdid .defect)
      = some Action.D := by
  rw [inst_dimdid_defect_tr]; exact plays_transpose (cimcic_coop_plays_C hL)

/-- τ(DIMDID) at Dupoc COOPERATES — τ̂ of `cimcic_cupod_plays_D` (the floor-closed system). -/
theorem dimdid_dupoc_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .dupoc))
      (.bot (inst (tauZoo k) .dimdid .dupoc)) (inst (tauZoo k) .dimdid .dupoc)
      = some Action.C := by
  rw [inst_dimdid_dupoc_tr]; exact plays_transpose cimcic_cupod_plays_D

/-- τ(DIMDID) at Cupod DEFECTS (Löb-gated) — τ̂ of the `cimcic × dupoc` mutual Löb. -/
theorem dimdid_cupod_plays_D :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .cupod))
        (.bot (inst (tauZoo k) .dimdid .cupod)) (inst (tauZoo k) .dimdid .cupod)
        = some Action.D := by
  obtain ⟨k₂, h⟩ := cimcic_dupoc_plays_C
  exact ⟨k₂, fun k hk => by rw [inst_dimdid_cupod_tr]; exact plays_transpose (h k hk)⟩

/-- τ(DIMDID)'s DIAGONAL DEFECTS — τ̂ of CIMCIC's `implRefl` self-cooperation. -/
theorem dimdid_dimdid_plays_D {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .dimdid))
      (.bot (inst (tauZoo k) .dimdid .dimdid)) (inst (tauZoo k) .dimdid .dimdid)
      = some Action.D := by
  rw [inst_dimdid_dimdid_tr]; exact plays_transpose (cimcic_quine_plays_C hL)

/-- τ(DIMDID) at Mirror DEFECTS (Löb-gated) — τ̂ of `cimcic_mirror_plays_C`. -/
theorem dimdid_mirror_plays_D :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .mirror))
        (.bot (inst (tauZoo k) .dimdid .mirror)) (inst (tauZoo k) .dimdid .mirror)
        = some Action.D := by
  obtain ⟨k₂, h⟩ := cimcic_mirror_plays_C
  exact ⟨k₂, fun k hk => by rw [inst_dimdid_mirror_tr]; exact plays_transpose (h k hk)⟩

/-- τ(Dupoc) at DIMDID DEFECTS — τ̂ of `cupod_cimcic_plays_C` (Cupod cannot convict CIMCIC). -/
theorem dupoc_dimdid_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .dimdid))
      (.bot (inst (tauZoo k) .dupoc .dimdid)) (inst (tauZoo k) .dupoc .dimdid)
      = some Action.D := by
  rw [inst_dupoc_dimdid_tr]; exact plays_transpose cupod_cimcic_plays_C

/-- τ(Cupod) at DIMDID DEFECTS (Löb-gated) — τ̂ of `dupoc_cimcic_plays_C`. -/
theorem cupod_dimdid_plays_D :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .cupod .dimdid))
        (.bot (inst (tauZoo k) .cupod .dimdid)) (inst (tauZoo k) .cupod .dimdid)
        = some Action.D := by
  obtain ⟨k₂, h⟩ := dupoc_cimcic_plays_C
  exact ⟨k₂, fun k hk => by rw [inst_cupod_dimdid_tr]; exact plays_transpose (h k hk)⟩

/-- τ(Mirror) at DIMDID DEFECTS (Löb-gated) — τ̂ of `mirror_cimcic_plays_C`. -/
theorem mirror_dimdid_plays_D :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .mirror .dimdid))
        (.bot (inst (tauZoo k) .mirror .dimdid)) (inst (tauZoo k) .mirror .dimdid)
        = some Action.D := by
  obtain ⟨k₂, h⟩ := mirror_cimcic_plays_C
  exact ⟨k₂, fun k hk => by rw [inst_mirror_dimdid_tr]; exact plays_transpose (h k hk)⟩

/-! ### The transported proof-search bits (the column theorems' arms) -/

/-- DIMDID's cooperation with the cooperator is floor-priced — τ̂ of CIMCIC's floor-priced
    defection on the defector. -/
theorem ps_probe_inst_dimdid_coop_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probe (inst (tauZoo k) .dimdid .coop)) = false := by
  rw [show probe (inst (tauZoo k) .dimdid .coop)
        = (probeD (inst (tauZoo k) .cimcic .defect)).transpose from rfl, proofSearch_transpose]
  exact ps_probeD_inst_cimcic_defect_false hK

/-- Its cooperation probe at the defector is FALSE (it defects there). -/
theorem ps_probe_inst_dimdid_defect_false {k K : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    proofSearch K (probe (inst (tauZoo k) .dimdid .defect)) = false := by
  rw [show probe (inst (tauZoo k) .dimdid .defect)
        = (probeD (inst (tauZoo k) .cimcic .coop)).transpose from rfl, proofSearch_transpose]
  exact ps_probeD_false_of_plays_C K (cimcic_coop_plays_C hL)

/-- Its cooperation with Dupoc is floor-priced — τ̂ of `ps_probeD_inst_cimcic_cupod_false`. -/
theorem ps_probe_inst_dimdid_dupoc_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probe (inst (tauZoo k) .dimdid .dupoc)) = false := by
  rw [show probe (inst (tauZoo k) .dimdid .dupoc)
        = (probeD (inst (tauZoo k) .cimcic .cupod)).transpose from rfl, proofSearch_transpose]
  exact ps_probeD_inst_cimcic_cupod_false hK

/-- Its defection probe at the cooperator is FALSE (it cooperates there). -/
theorem ps_probeD_inst_dimdid_coop_false {k K : Nat} :
    proofSearch K (probeD (inst (tauZoo k) .dimdid .coop)) = false := by
  rw [show probeD (inst (tauZoo k) .dimdid .coop)
        = (probe (inst (tauZoo k) .cimcic .defect)).transpose from rfl, proofSearch_transpose]
  exact ps_probe_false_of_plays_D K cimcic_defect_plays_D

/-- **The `hdd` gate**: its defection on Cupod is PROVABLE at large `k` — τ̂ of the Löb-certified
    `ps_probe_inst_cimcic_dupoc`. -/
theorem ps_probeD_inst_dimdid_cupod :
    ∃ k₂, ∀ k, k₂ < k →
      proofSearch k (probeD (inst (tauZoo k) .dimdid .cupod)) = true := by
  obtain ⟨k₂, h⟩ := ps_probe_inst_cimcic_dupoc
  refine ⟨k₂, fun k hk => ?_⟩
  rw [show probeD (inst (tauZoo k) .dimdid .cupod)
        = (probe (inst (tauZoo k) .cimcic .dupoc)).transpose from rfl, proofSearch_transpose]
  exact h k hk

/-- DIMDID's coop-cell guard is refuted at every budget — τ̂ of `ps_cimGuard_defect_false`. -/
theorem ps_ddGuard_coop_false {k K : Nat} :
    proofSearch K
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .coop .dimdid)) Action.D)
                     (.plays (.bot (inst (tauZoo k) .coop .dimdid)) .self Action.D)).subst
        (.bot (inst (tauZoo k) .dimdid .coop)) (.bot (inst (tauZoo k) .dimdid .coop)))
      = false := by
  have h := ps_cimGuard_defect_false (k := k) (K := K)
  rw [← proofSearch_transpose] at h
  exact h

/-! ## The run-stage partners: DIMCID's censuses at the other polarity -/

/-- Generic play lemma for the fire-D / default-C stage (DIMCID's, reused). -/
theorem dimdid_plays_C_of_iteC {k : Nat} (T : Tmpl) (b : Prog) (aT : Action) (p q : Prog)
    (hpeelT : inst (tauZoo k) T .dimdid = .ite b aT p q)
    (hpeelD : inst (tauZoo k) .dimdid T
      = .search k (.impl (.plays .self (.bot (inst (tauZoo k) T .dimdid)) Action.D)
                         (.plays (.bot (inst (tauZoo k) T .dimdid)) .self Action.D))
          (.const .D) (.const .C))
    (hplaysC : ∀ me opp, ∃ N, eval N me opp (inst (tauZoo k) T .dimdid) = some Action.C) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid T))
      (.bot (inst (tauZoo k) .dimdid T)) (inst (tauZoo k) .dimdid T)
      = some Action.C := by
  have hg : proofSearch k
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) T .dimdid)) Action.D)
                     (.plays (.bot (inst (tauZoo k) T .dimdid)) .self Action.D)).subst
        (.bot (inst (tauZoo k) .dimdid T)) (.bot (inst (tauZoo k) .dimdid T))) = false := by
    rw [ddG_subst]
    cases h : proofSearch k (ddG (.bot (inst (tauZoo k) .dimdid T))
        (inst (tauZoo k) T .dimdid)) with
    | false => rfl
    | true =>
        exfalso
        have hp := (proofSearch_spec _ _).1 h
        refine no_provable_tailTo_unreadable (.bot (inst (tauZoo k) T .dimdid))
          (.bot (inst (tauZoo k) .dimdid T)) .D ?_ ?_ ?_ ?_ ?_ hp ⟨rfl, by simp [hpeelT, hpeelD]⟩
        · intro n hA
          obtain ⟨m, hm⟩ := Pf_sound n _ (Pf.atom hA)
          obtain ⟨N, hN⟩ := hplaysC (.bot (inst (tauZoo k) T .dimdid))
            (.bot (inst (tauZoo k) .dimdid T))
          have hN' : eval (N + 1) (.bot (inst (tauZoo k) T .dimdid))
              (.bot (inst (tauZoo k) .dimdid T)) (.bot (inst (tauZoo k) T .dimdid))
              = some Action.C := by rw [eval]; exact hN
          rw [play] at hm
          exact absurd (eval_det hm hN') (by decide)
        · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
            ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, h⟩) <;>
            simp [hpeelT] at h
        · intro L
          cases L with
          | nil => simp [searchPlug]
          | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug]
        · intro hd L; cases hd <;> simp [ctxPlug]
        · intro hd L; cases hd <;> simp [plug2]
  generalize hMe : (Prog.bot (inst (tauZoo k) .dimdid T)) = Me at hg ⊢
  rw [hpeelD]
  exact searchGuardD_plays_C _ _ hg

theorem dimdid_tftSim_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .tftSim))
      (.bot (inst (tauZoo k) .dimdid .tftSim)) (inst (tauZoo k) .dimdid .tftSim)
      = some Action.C :=
  dimdid_plays_C_of_iteC .tftSim _ _ _ _ (inst_tftSim_peel k .dimdid)
    (inst_dimdid_peel_tftSim k)
    (fun me opp => by rw [inst_tftSim_peel k .dimdid]; exact simCopy_plays _ _ dimdid_coop_plays_C)

theorem dimdid_ebot_plays_C {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .ebot))
      (.bot (inst (tauZoo k) .dimdid .ebot)) (inst (tauZoo k) .dimdid .ebot)
      = some Action.C :=
  dimdid_plays_C_of_iteC .ebot _ _ _ _ (inst_ebot_peel k .dimdid)
    (inst_dimdid_peel_ebot k)
    (fun me opp => by
      rw [inst_ebot_peel k .dimdid]
      exact simWatchC_falls _ _ (dimdid_defect_plays_D hL)
        (simWatchC_fires _ _ dimdid_coop_plays_C))

theorem dimdid_dbot_plays_C {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .dbot))
      (.bot (inst (tauZoo k) .dimdid .dbot)) (inst (tauZoo k) .dimdid .dbot)
      = some Action.C :=
  dimdid_plays_C_of_iteC .dbot _ _ _ _ (inst_dbot_peel k .dimdid)
    (inst_dimdid_peel_dbot k)
    (fun me opp => by
      rw [inst_dbot_peel k .dimdid]
      exact simWatchC_falls _ _ (dimdid_defect_plays_D hL) ⟨1, rfl⟩)

/-! ### obot — the defector whose defection is too expensive to cite -/

theorem dimdid_coop_watch_over_budget {k : Nat} {me opp : Prog} {r : Action} {m : Nat}
    (h : PlaysProof me opp
      (.sim (.bot (inst (tauZoo k) .dimdid .coop)) (.bot (inst (tauZoo k) .dimdid .coop))) r m)
    (hm : m ≤ k) : False := by
  cases h with
  | sim hin =>
    simp only [Prog.subst] at hin
    cases hin with
    | bot hin3 =>
      rename_i m₃
      have hfalse := ps_ddGuard_coop_false (k := k) (K := k)
      rw [inst_dimdid_peel_coop k] at hin3 hfalse
      cases hin3 with
      | search_t hg _ =>
          have h1 := (proofSearch_spec _ _).2 hg
          exact absurd (h1.symm.trans hfalse) (by decide)
      | search_f _ _ =>
          have := hcn; omega

theorem dimdid_obot_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .obot))
      (.bot (inst (tauZoo k) .dimdid .obot)) (inst (tauZoo k) .dimdid .obot)
      = some Action.C := by
  have hg : proofSearch k
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .obot .dimdid)) Action.D)
                     (.plays (.bot (inst (tauZoo k) .obot .dimdid)) .self Action.D)).subst
        (.bot (inst (tauZoo k) .dimdid .obot)) (.bot (inst (tauZoo k) .dimdid .obot))) = false := by
    rw [ddG_subst]
    cases h : proofSearch k (ddG (.bot (inst (tauZoo k) .dimdid .obot))
        (inst (tauZoo k) .obot .dimdid)) with
    | false => rfl
    | true =>
        exfalso
        have hp := (proofSearch_spec _ _).1 h
        rw [inst_obot_peel k .dimdid] at hp
        refine no_provable_tailTo_floor k _ (.bot (inst (tauZoo k) .dimdid .obot)) .D
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ k _ hp le_rfl ⟨rfl, by simp [inst_dimdid_peel_obot]⟩
        · rintro K hK ⟨hpp, hn⟩
          cases hpp with
          | bot hin =>
            cases hin with
            | ite_t hg' _ _ => exact dimdid_coop_watch_over_budget hg' (by omega)
            | ite_f hg' _ _ => exact dimdid_coop_watch_over_budget hg' (by omega)
        · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
            ⟨_, _, _, _, _, _, _, h⟩) <;> simp at h
        · intro defs i h; simp at h
        · intro k₁ ψ₁ k₂ ψ₂ c1 q h; simp at h
        · intro L
          cases L with
          | nil => simp [searchPlug]
          | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug]
        · intro hd L; cases hd <;> simp [ctxPlug]
        · intro hd L h; cases hd <;> simp [plug2] at h
  generalize hMe : (Prog.bot (inst (tauZoo k) .dimdid .obot)) = Me at hg ⊢
  rw [inst_dimdid_peel_obot k]
  exact searchGuardD_plays_C _ _ hg

/-! ## The prover partners — floor-priced defections (then-`C` searchers) -/

theorem ps_ddGuard_searcherC_false {k K : Nat} (hK : K ≤ k) (T : Tmpl)
    (g : Formula) (pE : Prog)
    (hpeelT : inst (tauZoo k) T .dimdid = .search k g (.const .C) pE)
    (hpeelD : inst (tauZoo k) .dimdid T
      = .search k (.impl (.plays .self (.bot (inst (tauZoo k) T .dimdid)) Action.D)
                         (.plays (.bot (inst (tauZoo k) T .dimdid)) .self Action.D))
          (.const .D) (.const .C)) :
    proofSearch K
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) T .dimdid)) Action.D)
                     (.plays (.bot (inst (tauZoo k) T .dimdid)) .self Action.D)).subst
        (.bot (inst (tauZoo k) .dimdid T)) (.bot (inst (tauZoo k) .dimdid T)))
      = false := by
  rw [ddG_subst]
  cases h : proofSearch K (ddG (.bot (inst (tauZoo k) .dimdid T))
      (inst (tauZoo k) T .dimdid)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      rw [hpeelT] at hp
      refine no_provable_botSearcherElse_tail k k g .C .D pE (by decide)
        (Nat.le_refl k) _ K _ hp hK ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      exact absurd hA (by rw [hpeelD, hpeelT]; simp)

theorem dimdid_plays_C_of_searcherC {k : Nat} (T : Tmpl) (g : Formula) (pE : Prog)
    (hpeelT : inst (tauZoo k) T .dimdid = .search k g (.const .C) pE)
    (hpeelD : inst (tauZoo k) .dimdid T
      = .search k (.impl (.plays .self (.bot (inst (tauZoo k) T .dimdid)) Action.D)
                         (.plays (.bot (inst (tauZoo k) T .dimdid)) .self Action.D))
          (.const .D) (.const .C)) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid T))
      (.bot (inst (tauZoo k) .dimdid T)) (inst (tauZoo k) .dimdid T)
      = some Action.C := by
  have hg := ps_ddGuard_searcherC_false (Nat.le_refl k) T g pE hpeelT hpeelD
  generalize hMe : (Prog.bot (inst (tauZoo k) .dimdid T)) = Me at hg ⊢
  rw [hpeelD]
  exact searchGuardD_plays_C _ _ hg

theorem dimdid_tftPf_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .tftPf))
      (.bot (inst (tauZoo k) .dimdid .tftPf)) (inst (tauZoo k) .dimdid .tftPf)
      = some Action.C :=
  dimdid_plays_C_of_searcherC .tftPf _ _ (inst_tftPf_peel k .dimdid) (inst_dimdid_peel_tftPf k)

theorem dimdid_just_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .just))
      (.bot (inst (tauZoo k) .dimdid .just)) (inst (tauZoo k) .dimdid .just)
      = some Action.C :=
  dimdid_plays_C_of_searcherC .just _ _ (inst_just_peel k .dimdid) (inst_dimdid_peel_just k)

/-! ## dimdid × cimcic — anti-aligned, closed by the floor (one orientation direct, the other by τ̂) -/

/-- `inst .dimdid .cimcic`: DIMDID at the head. -/
def ddCiSys (k : Nat) : ProgList :=
  .cons (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.D)
                          (.plays (.bot (.selfIdx 1)) .self Action.D))
    (.const .D) (.const .C))
  (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                           (.plays (.bot (.selfIdx 0)) .self Action.C))
    (.const .C) (.const .D)) .nil)

theorem inst_dimdid_cimcic_eq (k : Nat) : inst (tauZoo k) .dimdid .cimcic = .sys (ddCiSys k) 0 := rfl
theorem ddCiSys_get0 (k : Nat) :
    (ddCiSys k).get? 0
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.D)
                               (.plays (.bot (.selfIdx 1)) .self Action.D))
          (.const .D) (.const .C)) := rfl
theorem ddCiSys_get1 (k : Nat) :
    (ddCiSys k).get? 1
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                               (.plays (.bot (.selfIdx 0)) .self Action.C))
          (.const .C) (.const .D)) := rfl

/-- **τ(DIMDID) at CIMCIC COOPERATES**: its guard's consequent is the CIMCIC member's floor-priced
    else-play `D`, so the search fails and the else-constant `C` runs. -/
theorem dimdid_cimcic_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .cimcic))
      (.bot (inst (tauZoo k) .dimdid .cimcic)) (inst (tauZoo k) .dimdid .cimcic)
      = some Action.C := by
  rw [inst_dimdid_cimcic_eq]
  refine sysSearcher_plays_else _ _ (ddCiSys_get0 k) ?_
  rw [sysClose_subst_ddSelfIdx]
  cases h : proofSearch k
      (.impl (.plays (.bot (.sys (ddCiSys k) 0)) (.bot (.sys (ddCiSys k) 1)) Action.D)
             (.plays (.bot (.sys (ddCiSys k) 1)) (.bot (.sys (ddCiSys k) 0)) Action.D)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      refine no_provable_botSysSearcherElse_tail k (ddCiSys k) 1 k _ .C .D _ (by decide)
        (Nat.le_refl k) (ddCiSys_get1 k) _ k _ hp (Nat.le_refl k) ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      exact absurd hA (by simp)

/-- **τ(CIMCIC) at DIMDID DEFECTS** — τ̂ of the orientation above. -/
theorem cimcic_dimdid_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .dimdid))
      (.bot (inst (tauZoo k) .cimcic .dimdid)) (inst (tauZoo k) .cimcic .dimdid)
      = some Action.D := by
  rw [inst_cimcic_dimdid_tr]; exact plays_transpose dimdid_cimcic_plays_C

/-! ## prudent × dimdid — `(D, C)`: Prudent's outer probe of DIMDID's trust fails, and DIMDID's guard
needs a defection Prudent never certifies (DIMCID's cells, at the other polarity) -/

def pddSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
          (.search k (probeD (inst (tauZoo k) .dimdid .defect)) (.const .C) (.const .D))
          (.const .D))
  (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.D)
                           (.plays (.bot (.selfIdx 0)) .self Action.D))
    (.const .D) (.const .C)) .nil)

theorem inst_prudent_dimdid_eq (k : Nat) : inst (tauZoo k) .prudent .dimdid = .sys (pddSys k) 0 := rfl
theorem pddSys_get0 (k : Nat) : (pddSys k).get? 0
    = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
        (.search k (probeD (inst (tauZoo k) .dimdid .defect)) (.const .C) (.const .D))
        (.const .D)) := rfl
theorem pddSys_get1 (k : Nat) : (pddSys k).get? 1
    = some (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.D)
                             (.plays (.bot (.selfIdx 0)) .self Action.D))
        (.const .D) (.const .C)) := rfl

def ddpSys (k : Nat) : ProgList :=
  .cons (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.D)
                          (.plays (.bot (.selfIdx 1)) .self Action.D))
    (.const .D) (.const .C))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
          (.search k (probeD (inst (tauZoo k) .dimdid .defect)) (.const .C) (.const .D))
          (.const .D)) .nil)

theorem inst_dimdid_prudent_eq (k : Nat) : inst (tauZoo k) .dimdid .prudent = .sys (ddpSys k) 0 := rfl
theorem ddpSys_get0 (k : Nat) : (ddpSys k).get? 0
    = some (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.D)
                             (.plays (.bot (.selfIdx 1)) .self Action.D))
        (.const .D) (.const .C)) := rfl
theorem ddpSys_get1 (k : Nat) : (ddpSys k).get? 1
    = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
        (.search k (probeD (inst (tauZoo k) .dimdid .defect)) (.const .C) (.const .D))
        (.const .D)) := rfl

theorem prudent_dimdid_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .prudent .dimdid)) (.bot (inst (tauZoo k) .prudent .dimdid))
      (inst (tauZoo k) .prudent .dimdid) = some Action.D := by
  rw [inst_prudent_dimdid_eq k]
  refine sysNested_plays_D_of_outer _ _ (pddSys_get0 k) ?_
  rw [sysClose_subst_botSelfIdx]
  exact ps_botSys_mismatch_false (le_refl k) (pddSys k) 1 k _ .D .C _ (by decide)
    (Nat.le_refl k) (pddSys_get1 k) _

theorem dimdid_prudent_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .prudent)) (.bot (inst (tauZoo k) .dimdid .prudent))
      (inst (tauZoo k) .dimdid .prudent) = some Action.C := by
  rw [inst_dimdid_prudent_eq k]
  refine sysSearcher_plays_else _ _ (ddpSys_get0 k) ?_
  rw [sysClose_subst_ddSelfIdx]
  cases h : proofSearch k (.impl (.plays (.bot (.sys (ddpSys k) 0)) (.bot (.sys (ddpSys k) 1)) Action.D)
      (.plays (.bot (.sys (ddpSys k) 1)) (.bot (.sys (ddpSys k) 0)) Action.D)) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_sysNested_D_tail k (ddpSys k) 1 _ _ (ddpSys_get1 k) _ k _
        ((proofSearch_spec _ _).1 h) le_rfl ⟨rfl, by simp⟩

end PD.Tau
