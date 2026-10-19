import ArithS.Tau.Entangled.Dimcid

/-!
# ArithS.Tau.Entangled.DimdidSys — τ(DIMDID)'s entangled systems (2026-10-19)

τ(DIMDID)'s member at the pronoun `j` is `ddm j k`: "if I defect against member `j`, it defects against me", then
`D`, else `C` — the C/D transposition of CIMCIC's member `cim`. Its systems with the self-probers
(`inst_dimdid_*`, `inst_*_dimdid`, by `rfl` from `Tau/Zoo.inst_dimdid_sys_*`) and what they play:

* **`dimdid × cupod` and `cupod × dimdid`: D, D** — a MUTUAL family ALIGNED ON DEFECTION (`loebSound_CDd`, the
  transposition of `DupocCimcic.loebSound_DCi`): a box of both guards makes the Cupod member punish in every frame
  (its probe is closed, `q_congr_opp_plays`) and the DIMDID member defect against itself, so the probe "the DIMDID
  member defects against itself" is true and the implication's consequent "the Cupod member defects against me"
  holds. Both members find their guards (`found_CDd`).
* **`dimdid × dimcid` and `dimcid × dimdid`: D, D** — the family `loebSound_DdDi`: the DIMDID member's guard needs
  the DIMCID member's defection (its consequent), the DIMCID member's guard is self-fulfilling (a box makes it defect,
  refuting its own antecedent, as in `Dimcid.loebSound_Di`). The DIMCID head alone is `Sys2.found_Di`.
* **the floors** `dimdid × {dupoc, cimcic, prudent, maxconfidence, minconfidence}` (C when the DIMDID member's guard
  is not found: `bit_C_of_ddm_else`) and `{dupoc, cimcic, prudent, maxconfidence, minconfidence} × dimdid` (the
  partner's else-play) are stated in `Tau/Rows/*.lean` with `FloorBitA.of_not_hinge`; base dichotomies
  `dich_DIMDID_vs_DupocBot / CIMCIC / PrudentBot` (`Cells/Dimdid.lean`).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open PD PD.Tau

/-! ### 1. The member and the systems -/

/-- DIMDID's raw member guard at the pronoun `j`. -/
abbrev entDdG (j : ℕ) : Formula := .impl (.plays .self (.bot (.selfIdx j)) .D) (.plays (.bot (.selfIdx j)) .self .D)

/-- DIMDID's member at the pronoun `j`: the guard, then `D`, else `C`. -/
def ddm (j k : ℕ) : Prog := .search k (entDdG j) (.const .D) (.const .C)

lemma ddm_eq (j k : ℕ) : ddm j k = .search k (entDdG j) (.const .D) (.const Action.D.swap) := rfl

theorem memberP_ddm (j k : ℕ) (hj : j ≤ 1) : memberP (ddm j k) = true := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl <;> rfl

theorem ddm_sysClose (j k : ℕ) (defs : ProgList) :
    (ddm j k).sysClose defs =
      .search k (.impl (.plays .self (.bot (.sys defs j)) .D) (.plays (.bot (.sys defs j)) .self .D)) (.const .D) (.const .C) := rfl

/-- The systems, DIMDID at the head… -/
theorem inst_dimdid_dupoc (k : ℕ) : inst (tauZoo k) .dimdid .dupoc = .sys (sys2 (ddm 1 k) (dm 0 k)) 0 := rfl
theorem inst_dimdid_cupod (k : ℕ) : inst (tauZoo k) .dimdid .cupod = .sys (sys2 (ddm 1 k) (cm 0 k)) 0 := rfl
theorem inst_dimdid_cimcic (k : ℕ) : inst (tauZoo k) .dimdid .cimcic = .sys (sys2 (ddm 1 k) (cim 0 k)) 0 := rfl
theorem inst_dimdid_dimcid (k : ℕ) : inst (tauZoo k) .dimdid .dimcid = .sys (sys2 (ddm 1 k) (dim 0 k)) 0 := rfl
theorem inst_dimdid_prudent (k : ℕ) : inst (tauZoo k) .dimdid .prudent = .sys (sys2 (ddm 1 k) (pm 0 k .dimdid)) 0 := rfl
theorem inst_dimdid_maxconfidence (k : ℕ) : inst (tauZoo k) .dimdid .maxconfidence = .sys (sys2 (ddm 1 k) (dm 0 k)) 0 := rfl
theorem inst_dimdid_minconfidence (k : ℕ) : inst (tauZoo k) .dimdid .minconfidence = .sys (sys2 (ddm 1 k) (dm 0 k)) 0 := rfl
theorem inst_dimdid_mirror (k : ℕ) : inst (tauZoo k) .dimdid .mirror = .sys (sys2 (ddm 1 k) (mm 0)) 0 := rfl

/-- …and seen from the partners' sides. -/
theorem inst_dupoc_dimdid (k : ℕ) : inst (tauZoo k) .dupoc .dimdid = .sys (sys2 (dm 1 k) (ddm 0 k)) 0 := rfl
theorem inst_cupod_dimdid (k : ℕ) : inst (tauZoo k) .cupod .dimdid = .sys (sys2 (cm 1 k) (ddm 0 k)) 0 := rfl
theorem inst_cimcic_dimdid (k : ℕ) : inst (tauZoo k) .cimcic .dimdid = .sys (sys2 (cim 1 k) (ddm 0 k)) 0 := rfl
theorem inst_dimcid_dimdid (k : ℕ) : inst (tauZoo k) .dimcid .dimdid = .sys (sys2 (dim 1 k) (ddm 0 k)) 0 := rfl
theorem inst_prudent_dimdid (k : ℕ) : inst (tauZoo k) .prudent .dimdid = .sys (sys2 (pm 1 k .dimdid) (ddm 0 k)) 0 := rfl
theorem inst_maxconfidence_dimdid (k : ℕ) : inst (tauZoo k) .maxconfidence .dimdid = .sys (sys2 (dm 1 k) (ddm 0 k)) 0 := rfl
theorem inst_minconfidence_dimdid (k : ℕ) : inst (tauZoo k) .minconfidence .dimdid = .sys (sys2 (dm 1 k) (ddm 0 k)) 0 := rfl

/-- The else-play of a DIMDID-shaped member `0` (then `D`, else `C`), when its guard is not found. -/
theorem bit_C_of_ddm_else {k : ℕ} {A T : Tmpl} {m₁ : Prog} (h : inst (tauZoo k) A T = .sys (sys2 (ddm 1 k) m₁) 0)
    (hn : ¬ LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot (.sys (sys2 (ddm 1 k) m₁) 1)) .D)
      (.plays (.bot (.sys (sys2 (ddm 1 k) m₁) 1)) .self .D)))
      (progCode (sysFrame (ddm 1 k) m₁)) (progCode (sysFrame (ddm 1 k) m₁)))) :
    bitPlays k A T .C :=
  bitPlays_of_member h (memberP_ddm 1 k (by decide))
    (by rw [ddm_sysClose]; exact member_else _ hn (const_play 0 _ _ _))

/-- The then-play of a DIMDID-shaped member `0`. -/
theorem bit_D_of_ddm_then {k : ℕ} {A T : Tmpl} {m₁ : Prog} (h : inst (tauZoo k) A T = .sys (sys2 (ddm 1 k) m₁) 0)
    (hf : LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot (.sys (sys2 (ddm 1 k) m₁) 1)) .D)
      (.plays (.bot (.sys (sys2 (ddm 1 k) m₁) 1)) .self .D)))
      (progCode (sysFrame (ddm 1 k) m₁)) (progCode (sysFrame (ddm 1 k) m₁)))) :
    bitPlays k A T .D :=
  bitPlays_of_member h (memberP_ddm 1 k (by decide))
    (by rw [ddm_sysClose]; exact member_then _ hf (const_play 0 _ _ _))

/-! ### 2. The mutual families -/

namespace Sys2

/-- **The mutual Löb premise of a Cupod/DIMDID system, aligned on defection**: member `c` is Cupod probing `d`,
member `d` is DIMDID probing `c`. Boxes of both make the Cupod member punish in the frame `(c, d)` (its probe is
closed) and the DIMDID member defect against itself — the probe is true and the implication's consequent holds;
the transposed system is Dupoc/CIMCIC's (`DupocCimcic.loebSound_DCi`), cooperating. -/
theorem loebSound_CDd (S : Sys2) (c d : ℕ) (hc : c ≤ 1) (hd : d ≤ 1)
    (hgc : (S.mem c).g = template13 (entCmG d)) (hac : (S.mem c).a = 1)
    (hgd : (S.mem d).g = template13 (entDdG c)) (had : (S.mem d).a = 1) :
    LoebSound (pQ (S.q c c c ⋏ S.q d d d)) (14 + S.K) 16 := by
  refine loebSound_pQ₂_above _ _ S.K fun V _ _ k hk b₁ b₂ b₃ b₄ ↦ ?_
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  rw [← stdReadingV_eq_stdReading]
  have hcongr : S.q c c c = S.q c c d :=
    q_congr_opp_plays S (pa := .bot (.selfIdx d)) (pb := .bot (.selfIdx d)) (by simp) (by simp) hgc c c d
  -- Cupod punishes in the frame `(c, d)`, DIMDID defects against itself
  have hCd : EvalGraph 4 (pBot (S.code c k)) (pBot (S.code d k)) (pBot (S.code c k)) (actCode .D : V) := by
    have := plays_of_box hk c hc c d (by rw [← hcongr]; exact b₁)
    rwa [hac, Nat.cast_one, ← actCode_D_cast] at this
  have hDd : EvalGraph 4 (pBot (S.code d k)) (pBot (S.code d k)) (pBot (S.code d k)) (actCode .D : V) := by
    have := plays_of_box hk d hd d d b₂
    rwa [had, Nat.cast_one, ← actCode_D_cast] at this
  have hCdT : EvalGraph 4 (pBot (S.tr.code c k)) (pBot (S.tr.code d k)) (pBot (S.tr.code c k)) (actCode Action.D.swap : V) := by
    have := tr_plays_of_box hk c hc c d (by rw [show Semiformula.lMap swap (S.q c c d) = Semiformula.lMap swap (S.q c c c) by rw [hcongr]]; exact b₃)
    rw [tr_mem S c hc, SM.tr_a, hac] at this
    simp only [Nat.sub_self, Nat.cast_zero] at this
    rw [show Action.D.swap = .C from rfl, actCode_C_cast]
    exact this
  have hDdT : EvalGraph 4 (pBot (S.tr.code d k)) (pBot (S.tr.code d k)) (pBot (S.tr.code d k)) (actCode Action.D.swap : V) := by
    have := tr_plays_of_box hk d hd d d b₄
    rw [tr_mem S d hd, SM.tr_a, had] at this
    simp only [Nat.sub_self, Nat.cast_zero] at this
    rw [show Action.D.swap = .C from rfl, actCode_C_cast]
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (eval_q_partner hk (j := c) (j' := d) hd hgc c c).mpr ⟨4, hDd⟩
  · exact (eval_q_impl hk (j := d) (j' := c) hc hgd d d).mpr fun _ ↦ ⟨4, hCd⟩
  · exact (eval_q_partner_swap hk (j := c) (j' := d) hd hgc c c).mpr ⟨4, hDdT⟩
  · exact (eval_q_impl_swap hk (j := d) (j' := c) hc hgd d d).mpr fun _ ↦ ⟨4, hCdT⟩

/-- **Both members find their guards for all large `k`.** -/
theorem found_CDd (S : Sys2) (c d : ℕ) (hc : c ≤ 1) (hd : d ≤ 1)
    (hgc : (S.mem c).g = template13 (entCmG d)) (hac : (S.mem c).a = 1)
    (hgd : (S.mem d).g = template13 (entDdG c)) (had : (S.mem d).a = 1) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → S.K ≤ k ∧
      LenBox TAct k (instB (⌜S.q c c c⌝ : ℕ) k) ∧ LenBox TAct k (instB (⌜S.q d d d⌝ : ℕ) k) := by
  obtain ⟨k₀, h⟩ := family_found (pQ (S.q c c c ⋏ S.q d d d)) boundedInnerNec_sixteen
    (loebSound_CDd S c d hc hd hgc hac hgd had)
  refine ⟨k₀ + S.K, fun k hk ↦ ?_⟩
  obtain ⟨a, ha', hbox⟩ := h k (by omega)
  obtain ⟨b₁, b₂, -, -⟩ := boxes_pQ₂_nat _ _ S.K k a ha' hbox
  exact ⟨by omega, b₁, b₂⟩

/-- **The Löb premise of a DIMDID/DIMCID system**: member `d` is DIMDID probing `i`, member `i` is DIMCID probing
`d`; the family is DIMDID's guard in its self-play frame and DIMCID's guard in the frame `(i, d)`. A box of the
second makes the DIMCID member defect against the DIMDID member — the consequent of DIMDID's guard and the refutation
of DIMCID's own antecedent. -/
theorem loebSound_DdDi (S : Sys2) (d i : ℕ) (hd : d ≤ 1) (hi : i ≤ 1)
    (hgd : (S.mem d).g = template13 (entDdG i)) (_had : (S.mem d).a = 1)
    (hgi : (S.mem i).g = template13 (entDimG d)) (hai : (S.mem i).a = 1) :
    LoebSound (pQ (S.q d d d ⋏ S.q i i d)) (14 + S.K) 16 := by
  refine loebSound_pQ₂_above _ _ S.K fun V _ _ k hk b₁ b₂ b₃ b₄ ↦ ?_
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  rw [← stdReadingV_eq_stdReading]
  -- DIMCID defects against DIMDID in the frame `(i, d)`
  have hDi : EvalGraph 4 (pBot (S.code i k)) (pBot (S.code d k)) (pBot (S.code i k)) (actCode .D : V) := by
    have := plays_of_box hk i hi i d b₂
    rwa [hai, Nat.cast_one, ← actCode_D_cast] at this
  have hDiT : EvalGraph 4 (pBot (S.tr.code i k)) (pBot (S.tr.code d k)) (pBot (S.tr.code i k)) (actCode Action.D.swap : V) := by
    have := tr_plays_of_box hk i hi i d b₄
    rw [tr_mem S i hi, SM.tr_a, hai] at this
    simp only [Nat.sub_self, Nat.cast_zero] at this
    rw [show Action.D.swap = .C from rfl, actCode_C_cast]
    exact this
  have hA : ¬ ∃ n, EvalGraph n (pBot (S.code i k)) (pBot (S.code d k)) (pBot (S.code i k)) (actCode .C : V) := by
    rintro ⟨n, hn⟩
    have := EvalGraph.unique_V' n 4 _ _ _ _ _ hn hDi
    rw [actCode_C_cast, actCode_D_cast] at this
    exact _root_.zero_ne_one this
  have hAT : ¬ ∃ n, EvalGraph n (pBot (S.tr.code i k)) (pBot (S.tr.code d k)) (pBot (S.tr.code i k)) (actCode Action.C.swap : V) := by
    rintro ⟨n, hn⟩
    have := EvalGraph.unique_V' n 4 _ _ _ _ _ hn hDiT
    rw [show Action.C.swap = .D from rfl, show Action.D.swap = .C from rfl, actCode_D_cast, actCode_C_cast] at this
    exact _root_.one_ne_zero this
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (eval_q_impl hk (j := d) (j' := i) hi hgd d d).mpr fun _ ↦ ⟨4, hDi⟩
  · exact (eval_q_impl hk (j := i) (j' := d) hd hgi i d).mpr fun h ↦ absurd h hA
  · exact (eval_q_impl_swap hk (j := d) (j' := i) hi hgd d d).mpr fun _ ↦ ⟨4, hDiT⟩
  · exact (eval_q_impl_swap hk (j := i) (j' := d) hd hgi i d).mpr fun h ↦ absurd h hAT

theorem found_DdDi (S : Sys2) (d i : ℕ) (hd : d ≤ 1) (hi : i ≤ 1)
    (hgd : (S.mem d).g = template13 (entDdG i)) (had : (S.mem d).a = 1)
    (hgi : (S.mem i).g = template13 (entDimG d)) (hai : (S.mem i).a = 1) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → S.K ≤ k ∧
      LenBox TAct k (instB (⌜S.q d d d⌝ : ℕ) k) ∧ LenBox TAct k (instB (⌜S.q i i d⌝ : ℕ) k) := by
  obtain ⟨k₀, h⟩ := family_found (pQ (S.q d d d ⋏ S.q i i d)) boundedInnerNec_sixteen
    (loebSound_DdDi S d i hd hi hgd had hgi hai)
  refine ⟨k₀ + S.K, fun k hk ↦ ?_⟩
  obtain ⟨a, ha', hbox⟩ := h k (by omega)
  obtain ⟨b₁, b₂, -, -⟩ := boxes_pQ₂_nat _ _ S.K k a ha' hbox
  exact ⟨by omega, b₁, b₂⟩

end Sys2

/-! ### 3. `dimdid × cupod`, `cupod × dimdid` -/

noncomputable def SDdC : Sys2 := ⟨SM.ofSearch (entDdG 1) .D, SM.ofSearch (entCmG 0) .D⟩

theorem found_DdC_engine : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot (.sys (sys2 (ddm 1 k) (cm 0 k)) 1)) .D)
      (.plays (.bot (.sys (sys2 (ddm 1 k) (cm 0 k)) 1)) .self .D)))
      (progCode (sysFrame (ddm 1 k) (cm 0 k))) (progCode (sysFrame (ddm 1 k) (cm 0 k)))) := by
  obtain ⟨k₀, h⟩ := Sys2.found_CDd SDdC 1 0 (by decide) (by decide) rfl rfl rfl rfl
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, -, b₂⟩ := h k hk
  have := Sys2.box_guard_nat hK 0 0 0 rfl b₂
  rw [show SDdC = Sys2.mk (SM.ofSearch (entDdG 1) .D) (SM.ofSearch (entCmG 0) .D) from rfl] at this
  rw [Sys2.guardCodeB_sysClose_nat (entDdG 1) (entCmG 0) .D .D k (entDdG 1) rfl rfl, Sys2.code_nat (entDdG 1) (entCmG 0) .D .D] at this
  exact this

/-- `dimdid × cupod`: D. -/
theorem ent_dimdid_cupod : bitEventually .dimdid .cupod .D := by
  obtain ⟨k₀, h⟩ := found_DdC_engine
  exact ⟨k₀, fun k hk ↦ bit_D_of_ddm_then (inst_dimdid_cupod k) (h k hk)⟩

noncomputable def SCDd : Sys2 := ⟨SM.ofSearch (entCmG 1) .D, SM.ofSearch (entDdG 0) .D⟩

theorem found_CDd_engine : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    LenBox TAct k (guardCode (templateCode (.plays (.bot (.sys (sys2 (cm 1 k) (ddm 0 k)) 1)) (.bot (.sys (sys2 (cm 1 k) (ddm 0 k)) 1)) .D))
      (progCode (sysFrame (cm 1 k) (ddm 0 k))) (progCode (sysFrame (cm 1 k) (ddm 0 k)))) := by
  obtain ⟨k₀, h⟩ := Sys2.found_CDd SCDd 0 1 (by decide) (by decide) rfl rfl rfl rfl
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, b₁, -⟩ := h k hk
  have := Sys2.box_guard_nat hK 0 0 0 rfl b₁
  rw [show SCDd = Sys2.mk (SM.ofSearch (entCmG 1) .D) (SM.ofSearch (entDdG 0) .D) from rfl] at this
  rw [Sys2.guardCodeB_sysClose_nat (entCmG 1) (entDdG 0) .D .D k (entCmG 1) rfl rfl, Sys2.code_nat (entCmG 1) (entDdG 0) .D .D] at this
  exact this

/-- `cupod × dimdid`: D. -/
theorem ent_cupod_dimdid : bitEventually .cupod .dimdid .D := by
  obtain ⟨k₀, h⟩ := found_CDd_engine
  exact ⟨k₀, fun k hk ↦ bit_D_of_cm_then (inst_cupod_dimdid k) (h k hk)⟩

/-! ### 4. `dimdid × dimcid`, `dimcid × dimdid` -/

noncomputable def SDdDi : Sys2 := ⟨SM.ofSearch (entDdG 1) .D, SM.ofSearch (entDimG 0) .D⟩

theorem found_DdDi_engine : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot (.sys (sys2 (ddm 1 k) (dim 0 k)) 1)) .D)
      (.plays (.bot (.sys (sys2 (ddm 1 k) (dim 0 k)) 1)) .self .D)))
      (progCode (sysFrame (ddm 1 k) (dim 0 k))) (progCode (sysFrame (ddm 1 k) (dim 0 k)))) := by
  obtain ⟨k₀, h⟩ := Sys2.found_DdDi SDdDi 0 1 (by decide) (by decide) rfl rfl rfl rfl
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, b₁, -⟩ := h k hk
  have := Sys2.box_guard_nat hK 0 0 0 rfl b₁
  rw [show SDdDi = Sys2.mk (SM.ofSearch (entDdG 1) .D) (SM.ofSearch (entDimG 0) .D) from rfl] at this
  rw [Sys2.guardCodeB_sysClose_nat (entDdG 1) (entDimG 0) .D .D k (entDdG 1) rfl rfl, Sys2.code_nat (entDdG 1) (entDimG 0) .D .D] at this
  exact this

/-- `dimdid × dimcid`: D. -/
theorem ent_dimdid_dimcid : bitEventually .dimdid .dimcid .D := by
  obtain ⟨k₀, h⟩ := found_DdDi_engine
  exact ⟨k₀, fun k hk ↦ bit_D_of_ddm_then (inst_dimdid_dimcid k) (h k hk)⟩

noncomputable def SDiDd : Sys2 := ⟨SM.ofSearch (entDimG 1) .D, SM.ofSearch (entDdG 0) .D⟩

theorem found_DiDd_engine : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot (.sys (sys2 (dim 1 k) (ddm 0 k)) 1)) .C)
      (.plays (.bot (.sys (sys2 (dim 1 k) (ddm 0 k)) 1)) .self .D)))
      (progCode (sysFrame (dim 1 k) (ddm 0 k))) (progCode (sysFrame (dim 1 k) (ddm 0 k)))) := by
  obtain ⟨k₀, h⟩ := Sys2.found_Di SDiDd 0 1 (by decide) (by decide) rfl rfl
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, b₁, -⟩ := h k hk
  have := Sys2.box_guard_nat hK 0 0 0 rfl b₁
  rw [show SDiDd = Sys2.mk (SM.ofSearch (entDimG 1) .D) (SM.ofSearch (entDdG 0) .D) from rfl] at this
  rw [Sys2.guardCodeB_sysClose_nat (entDimG 1) (entDdG 0) .D .D k (entDimG 1) rfl rfl, Sys2.code_nat (entDimG 1) (entDdG 0) .D .D] at this
  exact this

/-- `dimcid × dimdid`: D (the DIMCID member's self-fulfilling family). -/
theorem ent_dimcid_dimdid : bitEventually .dimcid .dimdid .D := by
  obtain ⟨k₀, h⟩ := found_DiDd_engine
  exact ⟨k₀, fun k hk ↦ bit_D_of_dim_then (inst_dimcid_dimdid k) (h k hk)⟩

/-! ### 5. The floor bits on the systems -/

/-- `dimdid × dupoc` ‡ (base `dich_DIMDID_vs_DupocBot`): C when the DIMDID member's guard is not found. -/
theorem entFloor_dimdid_dupoc : FloorBitA .dimdid .dupoc
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (ddm 1 k) (dm 0 k)) 1)) .D)
      (.plays (.bot (.sys (sys2 (ddm 1 k) (dm 0 k)) 1)) .self .D)))
      (pBot (instCode k .dimdid .dupoc)) (pBot (instCode k .dimdid .dupoc)) k)) .C :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_C_of_ddm_else (inst_dimdid_dupoc k) (not_found_of_not_hinge (inst_dimdid_dupoc k) _ hn)⟩

theorem entFloor_dimdid_maxconfidence : FloorBitA .dimdid .maxconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (ddm 1 k) (dm 0 k)) 1)) .D)
      (.plays (.bot (.sys (sys2 (ddm 1 k) (dm 0 k)) 1)) .self .D)))
      (pBot (instCode k .dimdid .maxconfidence)) (pBot (instCode k .dimdid .maxconfidence)) k)) .C :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_C_of_ddm_else (inst_dimdid_maxconfidence k) (not_found_of_not_hinge (inst_dimdid_maxconfidence k) _ hn)⟩

theorem entFloor_dimdid_minconfidence : FloorBitA .dimdid .minconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (ddm 1 k) (dm 0 k)) 1)) .D)
      (.plays (.bot (.sys (sys2 (ddm 1 k) (dm 0 k)) 1)) .self .D)))
      (pBot (instCode k .dimdid .minconfidence)) (pBot (instCode k .dimdid .minconfidence)) k)) .C :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_C_of_ddm_else (inst_dimdid_minconfidence k) (not_found_of_not_hinge (inst_dimdid_minconfidence k) _ hn)⟩

/-- `dimdid × cimcic` ‡ (base `dich_DIMDID_vs_CIMCIC`, the self-dual pair). -/
theorem entFloor_dimdid_cimcic : FloorBitA .dimdid .cimcic
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (ddm 1 k) (cim 0 k)) 1)) .D)
      (.plays (.bot (.sys (sys2 (ddm 1 k) (cim 0 k)) 1)) .self .D)))
      (pBot (instCode k .dimdid .cimcic)) (pBot (instCode k .dimdid .cimcic)) k)) .C :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_C_of_ddm_else (inst_dimdid_cimcic k) (not_found_of_not_hinge (inst_dimdid_cimcic k) _ hn)⟩

/-- `dimdid × prudent` ‡ (base `dich_DIMDID_vs_PrudentBot`). -/
theorem entFloor_dimdid_prudent : FloorBitA .dimdid .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (ddm 1 k) (pm 0 k .dimdid)) 1)) .D)
      (.plays (.bot (.sys (sys2 (ddm 1 k) (pm 0 k .dimdid)) 1)) .self .D)))
      (pBot (instCode k .dimdid .prudent)) (pBot (instCode k .dimdid .prudent)) k)) .C :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_C_of_ddm_else (inst_dimdid_prudent k) (not_found_of_not_hinge (inst_dimdid_prudent k) _ hn)⟩

/-- `dupoc × dimdid` ‡: D when the Dupoc member's probe of the DIMDID member is not found (DIMDID's cooperation is an
else-play). -/
theorem entFloor_dupoc_dimdid : FloorBitA .dupoc .dimdid
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (ddm 0 k)) 1))
      (.bot (.sys (sys2 (dm 1 k) (ddm 0 k)) 1)) .C))
      (pBot (instCode k .dupoc .dimdid)) (pBot (instCode k .dupoc .dimdid)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_dm_else (inst_dupoc_dimdid k) (not_found_of_not_hinge (inst_dupoc_dimdid k) _ hn)⟩

theorem entFloor_maxconfidence_dimdid : FloorBitA .maxconfidence .dimdid
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (ddm 0 k)) 1))
      (.bot (.sys (sys2 (dm 1 k) (ddm 0 k)) 1)) .C))
      (pBot (instCode k .maxconfidence .dimdid)) (pBot (instCode k .maxconfidence .dimdid)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_dm_else (inst_maxconfidence_dimdid k) (not_found_of_not_hinge (inst_maxconfidence_dimdid k) _ hn)⟩

theorem entFloor_minconfidence_dimdid : FloorBitA .minconfidence .dimdid
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (ddm 0 k)) 1))
      (.bot (.sys (sys2 (dm 1 k) (ddm 0 k)) 1)) .C))
      (pBot (instCode k .minconfidence .dimdid)) (pBot (instCode k .minconfidence .dimdid)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_dm_else (inst_minconfidence_dimdid k) (not_found_of_not_hinge (inst_minconfidence_dimdid k) _ hn)⟩

/-- `cimcic × dimdid` ‡: D when the CIMCIC member's guard about the DIMDID member is not found. -/
theorem entFloor_cimcic_dimdid : FloorBitA .cimcic .dimdid
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (cim 1 k) (ddm 0 k)) 1)) .C)
      (.plays (.bot (.sys (sys2 (cim 1 k) (ddm 0 k)) 1)) .self .C)))
      (pBot (instCode k .cimcic .dimdid)) (pBot (instCode k .cimcic .dimdid)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_cim_else (inst_cimcic_dimdid k) (not_found_of_not_hinge (inst_cimcic_dimdid k) _ hn)⟩

/-- `prudent × dimdid` ‡: D when the Prudent member's outer probe of the DIMDID member is not found. -/
theorem entFloor_prudent_dimdid : FloorBitA .prudent .dimdid
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (pm 1 k .dimdid) (ddm 0 k)) 1))
      (.bot (.sys (sys2 (pm 1 k .dimdid) (ddm 0 k)) 1)) .C))
      (pBot (instCode k .prudent .dimdid)) (pBot (instCode k .prudent .dimdid)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_pm_else (inst_prudent_dimdid k) (not_found_of_not_hinge (inst_prudent_dimdid k) _ hn)⟩

end ArithS.Tau
