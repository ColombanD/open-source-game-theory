import ArithS.Necessitation.Verify3
import ArithS.Necessitation.Bounds

/-!
# ArithS.Necessitation.Verify4 — the recursion invariant at `m = 4`: `verifyGraph''_ok4` / `verifyGraph''_ok_pow4`

`Verify3.lean` §5 glues the node invariant of `VerifyGraph''` at DEGREE 6 (`shiftsV L ≤ (Cs + Cv)·p6 (dlen ρ)`, E-room
`(Ck + 5·Cv)·p6 (dlen ρ + 1)`): the `all`/`exs` arms consumed `Prologue`'s QUINTIC prologue shift bounds, and the
one-child recursion `X + Cs·y^m ≤ Cs·(y + m')^m` needs the node's own contribution `X ≤ Cs·d^{m-1}`. `Bounds.lean`
replaced those by CUBIC bounds (`shiftsV_proAll_le_cubic ≤ 402·p3 (D+1)`, `shiftsV_proExs_le_cubic ≤ 256·p3 (D+1)`)
and supplied the recursion arithmetic at `m = 4` name-for-name (`p4`, `rec1₄`/`rec2₄`, `allNode_p4`, `axmLeaf_p4`,
`allE_p4`/`exsE_p4`, `allEQ_p3`/`alliE_p3`/`exsEQ_p3`/`exsiE_p3`, `capE4`/`capE4'`, `child_bound4`, `lin_le_p3`,
`one_le_Cs_p4`, `proSA_add_le_p3`). This file is the re-glue:

* `verifyGraph''_ok4` — `Verify3.verifyGraph''_ok` with `p6 ↦ p4` THROUGHOUT (statement and motive): under the E-room
  `(Ck + 5·Cv)·p4 (dlen ρ + 1) ≤ E`, every list of `VerifyGraph''` at a node laid out at `0` is applicable at cap `9`,
  cut-admitting, has `shiftsV L ≤ (Cs + Cv)·p4 (dlen ρ)`, and leaves the node's goal fact. Constants `Cs = 25731`,
  `Ck = 5·25731 = 128655` (`Csv = 25731 + Cv ≥ 25731` is `proSA_add_le_p3`'s floor, and covers `allE_p4`'s `853`
  and `exsE_p4`'s `2236`; `Ckv = 5·Csv`). Arm by arm:
  - `axL`/`verumIntro`: linear E-caps through `capE4'`, the leaf shift `1 ≤ Csv·p4 d` (`one_le_Cs_p4`);
  - `andIntro`/`orIntro`/`wkRule`/`shiftRule`/`cutRule`: the linear per-node terms sit under `Csv·p3 d` (`lin_le_p3`)
    and `rec1₄`/`rec2₄` absorb them, the E-caps through `capE4` with `child_bound4` and `le_p4_self` — the nine arms
    of `Verify2.lean` §8.9 with the `p5/p6` lemmas renamed;
  - `allIntro`/`exsIntro`: `hSA := shiftsV_proAll_le_cubic`/`_proExs_le_cubic` at `D = 2d`, landed in
    `402·p3 (2(d+1))` (`256 ≤ 402` for `exs`), the E-caps `allE_p4`/`exsE_p4` and the quadratic caps `allEQ_p3` …
    `exsiE_p3` lifted by `p3_le_p4`, the node inequality `allNode_p4`;
  - `axm`: `shiftsV pro ≤ Cv·p3 (|p|+1) ≤ Cv·p4 d` (`|p| + 1 ≤ d`), the leaf `axmLeaf_p4`.
* `verifyGraph''_ok_pow4` — the `VerifyKit''`-shaped form at exponent 4 (`pow4_eq_p4`): the cap `Ck·(Cv+1)·(dlen ρ+1)^4
  ≤ E`, the list `shiftsV L ≤ Ck·(Cv+1)·(dlen ρ+1)^4`; so `Top.deg 4 = 16` is the degree this recursion supports.

NOT LOWER: every arm closes at `m = 4`; `m = 3` would need PER-NODE accounting (`Bounds.lean` §4.2, `rec1_local`) — the
`_ok`s take ONE `D` that also bounds the child sequent and `|substs1 t p|`, only globally bounded by `dlen ρ`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

/-! ## 1. The glue at `m = 4` -/

section glue4

set_option maxHeartbeats 20000000 in
/-- **The node invariant for `VerifyGraph''` at DEGREE 4** (`Verify3.verifyGraph''_ok` with `p6 ↦ p4`): at a node laid out
at offset `0`, every verification list is applicable at cap `9`, cut-admitting, has at most `(Cs + Cv)·(dlen ρ)^4`
eigenvariables, and leaves the node's goal fact at `&(k + 1 + shiftsV L)`. The E-room is `(Ck + 5·Cv)·(dlen ρ + 1)^4 ≤ E`.
The `all`/`exs` arms run on `Bounds`' cubic prologue shifts (`402·p3 (2(d+1))` at `D = 2d`) and `allNode_p4`; the `axm`
leaf on `axmLeaf_p4`; the other nine arms are `Verify2.lean` §8.9 with `rec1₄`/`rec2₄`. Constants `Csv = 25731 + Cv`,
`Ckv = 5·Csv`. -/
theorem verifyGraph''_ok4 : ∃ Cs Ck : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {tbl N N' B' Ww Wl Wc W₁ W₂ W T A Cv E ρ : V},
    TableOK tbl N → ProTable tbl → NumTableOK T N' B' → Ww = walkPieces → Wl = layoutPieces → Wc = certPieces →
    W₁ = frag1Pieces → W₂ = frag2Pieces → W = proPieces → AxmTableOK' tbl E Ww A Cv → Derivation TAct ρ →
    (((Ck : ℕ) : V) + 5 * Cv) * p4 (dlen TAct ρ + 1) ≤ E →
    ∀ L Γ : V, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A ρ L → IsFormulaSet LAct Γ → NodeLay Ww Wc T Γ (fstIdx ρ) →
      ListOK tbl E ((9 : ℕ) : V) Γ L ∧ NoDrop' L ∧ shiftsV L ≤ (((Cs : ℕ) : V) + Cv) * p4 (dlen TAct ρ) ∧
      neg LAct (goalFact (^&(len (memberList (fstIdx ρ)) + 1 + shiftsV L)) (bnum (dlen TAct ρ))) ∈ finalCtx Γ L := by
  refine ⟨25731, 128655, fun V _ _ tbl N N' B' Ww Wl Wc W₁ W₂ W T A Cv E ρ htbl hP htblN hWw hWl hWc hW₁ hW₂ hWp hA hd ↦ ?_⟩
  obtain ⟨Csv, hCsv⟩ : ∃ x : V, x = ((25731 : ℕ) : V) + Cv := ⟨_, rfl⟩
  obtain ⟨Ckv, hCkv⟩ : ∃ x : V, x = ((128655 : ℕ) : V) + 5 * Cv := ⟨_, rfl⟩
  rw [← hCsv, ← hCkv]
  have hCs1 : (1 : V) ≤ Csv := by
    rw [hCsv]; exact le_trans (b := ((25731 : ℕ) : V)) (by exact_mod_cast (by norm_num : 1 ≤ 25731)) le_self_add
  have hCs' : (25731 : V) ≤ Csv := by
    rw [hCsv]; exact le_trans (b := ((25731 : ℕ) : V)) (by exact_mod_cast (by norm_num : 25731 ≤ 25731)) le_self_add
  have hCs853 : (853 : V) ≤ Csv := le_trans (by exact_mod_cast (by norm_num : (853 : ℕ) ≤ 25731)) hCs'
  have hCs2236 : (2236 : V) ≤ Csv := le_trans (by exact_mod_cast (by norm_num : (2236 : ℕ) ≤ 25731)) hCs'
  have hCk : ∀ a : ℕ, a ≤ 128655 → ((a : ℕ) : V) ≤ Ckv := fun a ha ↦ by
    rw [hCkv]; exact le_trans (b := ((128655 : ℕ) : V)) (by exact_mod_cast ha) le_self_add
  have hCsCk : 5 * Csv ≤ Ckv := by rw [hCsv, hCkv]; exact le_of_eq (by push_cast; ring)
  have hCv1 : Cv + 1 ≤ Csv := by
    rw [hCsv]
    calc Cv + 1 ≤ Cv + ((25731 : ℕ) : V) := add_le_add le_rfl (by exact_mod_cast (by norm_num : 1 ≤ 25731))
      _ = ((25731 : ℕ) : V) + Cv := add_comm _ _
  have hCv9 : Cv + 9 ≤ Ckv := by
    rw [hCkv]
    calc Cv + 9 ≤ 5 * Cv + ((128655 : ℕ) : V) :=
          add_le_add (le_mul_of_one_le_left zero_le (by norm_num : (1 : V) ≤ 5)) (by exact_mod_cast (by norm_num : 9 ≤ 128655))
      _ = ((128655 : ℕ) : V) + 5 * Cv := add_comm _ _
  subst hWw
  apply Derivation.induction1 𝚷 (T := TAct)
    (P := fun ρ ↦ Ckv * p4 (dlen TAct ρ + 1) ≤ E → ∀ L Γ : V, VerifyGraph'' walkPieces Wl Wc W₁ W₂ W T A ρ L →
      IsFormulaSet LAct Γ → NodeLay walkPieces Wc T Γ (fstIdx ρ) →
      ListOK tbl E ((9 : ℕ) : V) Γ L ∧ NoDrop' L ∧ shiftsV L ≤ Csv * p4 (dlen TAct ρ) ∧
      neg LAct (goalFact (^&(len (memberList (fstIdx ρ)) + 1 + shiftsV L)) (bnum (dlen TAct ρ))) ∈ finalCtx Γ L)
    (by simp only [VerifyGraph'', p4]; definability) hd
  · -- axL
    intro s hs p hp hnp hE L Γ hL hΓ hLay
    rw [VerifyGraph''.axL_iff] at hL; subst hL
    rw [fstIdx_axL] at hLay ⊢
    have hD : Derivation TAct (axL s p) := Derivation.axL hs hp hnp
    have hd1 : 1 ≤ dlen TAct (axL s p) := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (axL s p) := by have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_axL] at this
    have hkD : len (memberList s) ≤ dlen TAct (axL s p) := le_trans (len_memberList_le_setLen hs) hsD
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (axL s p) := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hkD
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hn : 18 * ‖setLen LAct s + 1‖ + 7 ≤ 43 * (d + 1) := by
      have h1 : ‖setLen LAct s + 1‖ ≤ d + 1 := le_trans (length_le _) (add_le_add hsD (le_refl 1))
      calc 18 * ‖setLen LAct s + 1‖ + 7 ≤ 18 * (d + 1) + 7 := add_le_add (mul_le_mul_of_nonneg_left h1 zero_le) (le_refl 7)
        _ ≤ 43 * (d + 1) := le_of_add_eq' (c := 25 * d + 18) (by ring)
    obtain ⟨ok, nd, sh, goal⟩ := vAxL_ok (D := d) htbl hP htblN hWc hW₁ hs hp hnp hsD
      (capE4' hE he1 (hCk 39 (by norm_num)) (by
        calc 13 * d + 18 * ‖d‖ + 8 ≤ (13 + 18 + 8) * (d + 1) := lin_cap 13 18 8 d
          _ = ((39 : ℕ) : V) * (d + 1) := by push_cast; ring))
      (capE4' hE he1 (hCk 11 (by norm_num)) (by push_cast; exact le_of_add_eq' (c := 3 * d + 8) (by ring)))
      (capE4' hE he1 (hCk 3 (by norm_num)) (by
        push_cast; exact le_trans (add_le_add hkD (le_refl 3)) (le_of_add_eq' (c := 2 * d) (by ring))))
      (capE4' hE he1 (hCk 43 (by norm_num)) (by push_cast; exact hn))
      hΓ hLay.layout
    refine ⟨ok, nd, ?_, by rw [sh]; exact goal⟩
    rw [sh, ← hdd]
    exact one_le_Cs_p4 hCs1 hd1
  · -- verumIntro
    intro s hs hv hE L Γ hL hΓ hLay
    rw [VerifyGraph''.verumIntro_iff] at hL; subst hL
    rw [fstIdx_verumIntro] at hLay ⊢
    have hD : Derivation TAct (verumIntro s) := Derivation.verumIntro hs hv
    have hd1 : 1 ≤ dlen TAct (verumIntro s) := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (verumIntro s) := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_verumIntro] at this
    have hkD : len (memberList s) ≤ dlen TAct (verumIntro s) := le_trans (len_memberList_le_setLen hs) hsD
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (verumIntro s) := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hkD
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hn : 18 * ‖setLen LAct s + 1‖ + 7 ≤ 43 * (d + 1) := by
      have h1 : ‖setLen LAct s + 1‖ ≤ d + 1 := le_trans (length_le _) (add_le_add hsD (le_refl 1))
      calc 18 * ‖setLen LAct s + 1‖ + 7 ≤ 18 * (d + 1) + 7 := add_le_add (mul_le_mul_of_nonneg_left h1 zero_le) (le_refl 7)
        _ ≤ 43 * (d + 1) := le_of_add_eq' (c := 25 * d + 18) (by ring)
    obtain ⟨ok, nd, sh, goal⟩ := vVerum_ok (D := d) htbl hP htblN hWc hW₁ hs hv hsD
      (capE4' hE he1 (hCk 9 (by norm_num)) (by push_cast; exact le_of_add_eq' (c := 3 * d + 6) (by ring)))
      (capE4' hE he1 (hCk 3 (by norm_num)) (by
        push_cast; exact le_trans (add_le_add hkD (le_refl 3)) (le_of_add_eq' (c := 2 * d) (by ring))))
      (capE4' hE he1 (hCk 43 (by norm_num)) (by push_cast; exact hn))
      hΓ hLay.layout
    refine ⟨ok, nd, ?_, by rw [sh]; exact goal⟩
    rw [sh, ← hdd]
    exact one_le_Cs_p4 hCs1 hd1
  · -- andIntro
    intro s hs p q dp dq hpq hdp hdq ih₁ ih₂ hE L Γ hL hΓ hLay
    rw [VerifyGraph''.andIntro_iff] at hL
    obtain ⟨L₁, -, hL₁, L₂, -, hL₂, rfl⟩ := hL
    rw [fstIdx_andIntro] at hLay ⊢
    have hD : Derivation TAct (andIntro s p q dp dq) := Derivation.andIntro hpq hdp hdq
    have hd1 : 1 ≤ dlen TAct (andIntro s p q dp dq) := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (andIntro s p q dp dq) := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_andIntro] at this
    have hc₁D := setLen_child_le_dlen_andIntro_left hD
    have hc₂D := setLen_child_le_dlen_andIntro_right hD
    have hy₁ := dlen_dp_succ_le_andIntro hD
    have hy₂ := dlen_dq_succ_le_andIntro hD
    have hdl := dlen_andIntro hD
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (andIntro s p q dp dq) := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hc₁D hc₂D hy₁ hy₂ hdl
    obtain ⟨y₁, hy₁d⟩ : ∃ x, x = dlen TAct dp := ⟨_, rfl⟩
    obtain ⟨y₂, hy₂d⟩ : ∃ x, x = dlen TAct dq := ⟨_, rfl⟩
    rw [← hy₁d] at hy₁ hdl; rw [← hy₂d] at hy₂ hdl
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hm₁D : y₁ ≤ d := le_trans le_self_add hy₁
    have hm₂D : y₂ ≤ d := le_trans le_self_add hy₂
    have hch₁ : ChildOK tbl Wc T E L₁ dp (Csv * p4 y₁) := fun Γ' hΓ' hLay' ↦ by
      rw [hy₁d]
      exact ih₁ (le_trans (child_bound4 (by rw [← hy₁d]; exact le_trans hy₁ le_self_add)) hE) L₁ Γ' hL₁ hΓ' hLay'
    have hch₂ : ChildOK tbl Wc T E L₂ dq (Csv * p4 y₂) := fun Γ' hΓ' hLay' ↦ by
      rw [hy₂d]
      exact ih₂ (le_trans (child_bound4 (by rw [← hy₂d]; exact le_trans hy₂ le_self_add)) hE) L₂ Γ' hL₂ hΓ' hLay'
    have hlin : 60 * d + 18 * ‖d‖ + 60 ≤ 138 * p4 (d + 1) := by
      calc 60 * d + 18 * ‖d‖ + 60 ≤ (60 + 18 + 60) * (d + 1) := lin_cap 60 18 60 d
        _ = 138 * (d + 1) := by ring
        _ ≤ 138 * p4 (d + 1) := mul_le_mul_of_nonneg_left (le_p4_self he1) zero_le
    have h138 : (138 : V) ≤ 2 * Csv := by rw [hCsv]; exact le_trans (b := 2 * ((25731 : ℕ) : V)) (by exact_mod_cast (by norm_num : 138 ≤ 2 * 25731)) (mul_le_mul_of_nonneg_left le_self_add zero_le)
    obtain ⟨ok, nd, sh, goal⟩ := vAnd_ok (D := d) htbl hP htblN hWl hWc hWp hW₁ hs hpq hdp hdq hsD hc₁D hc₂D
      (by rw [← hy₁d]; exact hm₁D) (by rw [← hy₂d]; exact hm₂D)
      (capE4 hE hCsCk (by
        calc 60 * d + 18 * ‖d‖ + Csv * p4 y₁ + 2 * (Csv * p4 y₂) + 60
            = (60 * d + 18 * ‖d‖ + 60) + Csv * p4 y₁ + 2 * (Csv * p4 y₂) := by ring
          _ ≤ 138 * p4 (d + 1) + Csv * p4 (d + 1) + 2 * (Csv * p4 (d + 1)) :=
              add_le_add (add_le_add hlin (child_bound4 (le_trans hm₁D le_self_add)))
                (mul_le_mul_of_nonneg_left (child_bound4 (le_trans hm₂D le_self_add)) zero_le)
          _ = (138 + 3 * Csv) * p4 (d + 1) := by ring
          _ ≤ (2 * Csv + 3 * Csv) * p4 (d + 1) := mul_le_mul_of_nonneg_right (add_le_add h138 (le_refl _)) zero_le
          _ = 5 * Csv * p4 (d + 1) := by ring))
      hΓ hLay hch₁ hch₂
    refine ⟨ok, nd, ?_, goal⟩
    rw [← hdd]
    refine le_trans sh ?_
    have hdeq : d = y₁ + y₂ + (setLen LAct s + 1) := by rw [hdl]; ring
    have hX : 12 * d + 9 ≤ Csv * p3 d := lin_le_p3 hd1 (by
      rw [hCsv]; exact le_trans (b := ((25731 : ℕ) : V)) (by exact_mod_cast (by norm_num : 12 + 9 ≤ 25731)) le_self_add)
    calc 12 * d + Csv * p4 y₁ + Csv * p4 y₂ + 9 = (12 * d + 9) + Csv * p4 y₁ + Csv * p4 y₂ := by ring
      _ ≤ Csv * p4 d := rec2₄ le_add_self hdeq hX
  · -- orIntro
    intro s hs p q d' hpq hd' ih hE L Γ hL hΓ hLay
    rw [VerifyGraph''.orIntro_iff] at hL
    obtain ⟨L', -, hL', rfl⟩ := hL
    rw [fstIdx_orIntro] at hLay ⊢
    have hD : Derivation TAct (orIntro s p q d') := Derivation.orIntro hpq hd'
    have hd1 : 1 ≤ dlen TAct (orIntro s p q d') := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (orIntro s p q d') := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_orIntro] at this
    have hcD := setLen_child_le_dlen_orIntro hD
    have hy := dlen_d_succ_le_orIntro hD
    have hdl := dlen_orIntro hD
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (orIntro s p q d') := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hcD hy hdl
    obtain ⟨y, hyd⟩ : ∃ x, x = dlen TAct d' := ⟨_, rfl⟩
    rw [← hyd] at hy hdl
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hmD : y ≤ d := le_trans le_self_add hy
    have hch : ChildOK tbl Wc T E L' d' (Csv * p4 y) := fun Γ' hΓ' hLay' ↦ by
      rw [hyd]
      exact ih (le_trans (child_bound4 (by rw [← hyd]; exact le_trans hy le_self_add)) hE) L' Γ' hL' hΓ' hLay'
    have hlin : 40 * d + 18 * ‖d‖ + 40 ≤ 98 * p4 (d + 1) := by
      calc 40 * d + 18 * ‖d‖ + 40 ≤ (40 + 18 + 40) * (d + 1) := lin_cap 40 18 40 d
        _ = 98 * (d + 1) := by ring
        _ ≤ 98 * p4 (d + 1) := mul_le_mul_of_nonneg_left (le_p4_self he1) zero_le
    have h98 : (98 : V) ≤ 4 * Csv := by rw [hCsv]; exact le_trans (b := 4 * ((25731 : ℕ) : V)) (by exact_mod_cast (by norm_num : 98 ≤ 4 * 25731)) (mul_le_mul_of_nonneg_left le_self_add zero_le)
    obtain ⟨ok, nd, sh, goal⟩ := vOr_ok (D := d) htbl hP htblN hWl hWc hWp hW₁ hs hpq hd' hsD hcD (by rw [← hyd]; exact hmD)
      (capE4 hE hCsCk (by
        calc 40 * d + 18 * ‖d‖ + Csv * p4 y + 40 = (40 * d + 18 * ‖d‖ + 40) + Csv * p4 y := by ring
          _ ≤ 98 * p4 (d + 1) + Csv * p4 (d + 1) := add_le_add hlin (child_bound4 (le_trans hmD le_self_add))
          _ = (98 + Csv) * p4 (d + 1) := by ring
          _ ≤ (4 * Csv + Csv) * p4 (d + 1) := mul_le_mul_of_nonneg_right (add_le_add h98 (le_refl _)) zero_le
          _ = 5 * Csv * p4 (d + 1) := by ring))
      hΓ hLay hch
    refine ⟨ok, nd, ?_, goal⟩
    rw [← hdd]
    refine le_trans sh ?_
    have hdeq : d = y + (setLen LAct s + 1) := by rw [hdl]; ring
    have hX : 12 * d + 7 ≤ Csv * p3 d := lin_le_p3 hd1 (by
      rw [hCsv]; exact le_trans (b := ((25731 : ℕ) : V)) (by exact_mod_cast (by norm_num : 12 + 7 ≤ 25731)) le_self_add)
    calc 12 * d + Csv * p4 y + 7 = (12 * d + 7) + Csv * p4 y := by ring
      _ ≤ Csv * p4 d := rec1₄ le_add_self hdeq hX
  · -- allIntro
    intro s hs p d' hr hd' ih hE L Γ hL hΓ hLay
    rw [VerifyGraph''.allIntro_iff] at hL
    obtain ⟨L', -, hL', rfl⟩ := hL
    rw [fstIdx_allIntro] at hLay ⊢
    have hD : Derivation TAct (allIntro s p d') := Derivation.allIntro hr hd'
    have hd1 : 1 ≤ dlen TAct (allIntro s p d') := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (allIntro s p d') := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_allIntro] at this
    have hcD := setLen_child_le_dlen_allIntro hD
    have hy := dlen_d_succ_le_allIntro hD
    have hdl := dlen_allIntro hD
    have hp1 : IsSemiformula LAct 1 p := by have := IsSemiformula.all.mp (hs _ hr); simpa using this
    have hspD : formulaLen LAct (shift LAct p) ≤ 2 * dlen TAct (allIntro s p d') := by
      refine le_trans (formulaLen_shift_le hp1) (mul_le_mul_of_nonneg_left ?_ zero_le)
      have := formulaLen_all_le_dlen_allIntro hD
      rw [formulaLen_all hp1.isUFormula] at this
      exact le_trans le_self_add this
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (allIntro s p d') := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hcD hy hdl hspD
    obtain ⟨y, hyd⟩ : ∃ x, x = dlen TAct d' := ⟨_, rfl⟩
    rw [← hyd] at hy hdl
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hmD : y ≤ d := le_trans le_self_add hy
    have hch : ChildOK tbl Wc T E L' d' (Csv * p4 y) := fun Γ' hΓ' hLay' ↦ by
      rw [hyd]
      exact ih (le_trans (child_bound4 (by rw [← hyd]; exact le_trans hy le_self_add)) hE) L' Γ' hL' hΓ' hLay'
    obtain ⟨D, hDe⟩ : ∃ x : V, x = 2 * d := ⟨_, rfl⟩
    have hDd : d ≤ D := by rw [hDe]; exact le_of_add_eq' (c := d) (by ring)
    have hD3 : D + 1 ≤ 2 * (d + 1) := le_of_add_eq' (c := 1) (by rw [hDe]; ring)
    have hSA : shiftsV (proAll walkPieces Wl Wc W T s p 0) ≤ 402 * p3 (2 * (d + 1)) := by
      refine le_trans (shiftsV_proAll_le_cubic htbl hP hWl hWc walkPieces W T 0 hs hp1 hr (le_trans hsD hDd)
        (le_trans hcD hDd) (by rw [hDe]; exact hspD)) ?_
      exact mul_le_mul_of_nonneg_left (p3_mono hD3) zero_le
    have hEQ : 2 * ((1 + D) * (1 + D + 1)) * (D + 1) + 4 * D + 11 ≤ 27 * p4 (d + 1) :=
      le_trans (allEQ_p3 hDe) (mul_le_mul_of_nonneg_left (p3_le_p4 he1) zero_le)
    have hiE : 0 + 2 * ((1 + D) * (1 + D + 1)) * D + 40 * D + 20 ≤ 96 * p4 (d + 1) :=
      le_trans (alliE_p3 hDe) (mul_le_mul_of_nonneg_left (p3_le_p4 he1) zero_le)
    obtain ⟨ok, nd, sh, goal⟩ := vAll_ok (D := D) htbl hP htblN hWl hWc hWp hW₂ hs hr hd' (le_trans hsD hDd)
      (le_trans hcD hDd) (by rw [hDe]; exact hspD) (by rw [← hyd]; exact le_trans hmD hDd) hSA
      (capE4 hE hCsCk (allE_p4 hd1 hDe hmD hCs853))
      (capE4 hE (by have := hCk 27 (by norm_num); push_cast at this; exact this) hEQ)
      (capE4 hE (by have := hCk 96 (by norm_num); push_cast at this; exact this) hiE)
      hΓ hLay hch
    refine ⟨ok, nd, ?_, goal⟩
    rw [← hdd]
    refine le_trans sh ?_
    have hdeq : d = y + (setLen LAct s + 1) := by rw [hdl]; ring
    exact allNode_p4 hd1 le_add_self hdeq hCs'
  · -- exsIntro
    intro s hs p t d' hr ht hd' ih hE L Γ hL hΓ hLay
    rw [VerifyGraph''.exsIntro_iff] at hL
    obtain ⟨L', -, hL', rfl⟩ := hL
    rw [fstIdx_exsIntro] at hLay ⊢
    have hD : Derivation TAct (exsIntro s p t d') := Derivation.exsIntro hr ht hd'
    have hd1 : 1 ≤ dlen TAct (exsIntro s p t d') := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (exsIntro s p t d') := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_exsIntro] at this
    have hcD := setLen_child_le_dlen_exsIntro hD
    have htD := termLen_le_dlen_exsIntro hD
    have hy := dlen_d_succ_le_exsIntro hD
    have hdl := dlen_exsIntro hD
    have hp1 : IsSemiformula LAct 1 p := by have := IsSemiformula.exs.mp (hs _ hr); simpa using this
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (exsIntro s p t d') := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hcD htD hy hdl
    obtain ⟨y, hyd⟩ : ∃ x, x = dlen TAct d' := ⟨_, rfl⟩
    rw [← hyd] at hy hdl
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hmD : y ≤ d := le_trans le_self_add hy
    have hch : ChildOK tbl Wc T E L' d' (Csv * p4 y) := fun Γ' hΓ' hLay' ↦ by
      rw [hyd]
      exact ih (le_trans (child_bound4 (by rw [← hyd]; exact le_trans hy le_self_add)) hE) L' Γ' hL' hΓ' hLay'
    obtain ⟨D, hDe⟩ : ∃ x : V, x = 2 * d := ⟨_, rfl⟩
    have hDd : d ≤ D := by rw [hDe]; exact le_of_add_eq' (c := d) (by ring)
    have hD3 : D + 1 ≤ 2 * (d + 1) := le_of_add_eq' (c := 1) (by rw [hDe]; ring)
    have hSA : shiftsV (proExs walkPieces Wl Wc W T s p t 0) ≤ 402 * p3 (2 * (d + 1)) := by
      refine le_trans (shiftsV_proExs_le_cubic htbl hP hWl hWc walkPieces W T 0 hs hp1 hr ht (le_trans hsD hDd)
        (le_trans hcD hDd) (le_trans htD hDd)) ?_
      have h256 : (256 : V) ≤ 402 := by exact_mod_cast (by norm_num : (256 : ℕ) ≤ 402)
      exact mul_le_mul h256 (p3_mono hD3) zero_le zero_le
    have hEQ : 2 * ((1 + D) * (1 + D + D)) * (D + 1) + 4 * D + 11 ≤ 43 * p4 (d + 1) :=
      le_trans (exsEQ_p3 hDe) (mul_le_mul_of_nonneg_left (p3_le_p4 he1) zero_le)
    have hiE : 0 + 2 * ((1 + D) * (1 + D + D)) * D + 40 * D + 20 ≤ 112 * p4 (d + 1) :=
      le_trans (exsiE_p3 hDe) (mul_le_mul_of_nonneg_left (p3_le_p4 he1) zero_le)
    obtain ⟨ok, nd, sh, goal⟩ := vExs_ok (D := D) htbl hP htblN hWl hWc hWp hW₂ hs hr ht hd' (le_trans hsD hDd)
      (le_trans hcD hDd) (le_trans htD hDd) (by rw [← hyd]; exact le_trans hmD hDd) hSA
      (capE4 hE hCsCk (exsE_p4 hd1 hDe hmD hCs2236))
      (capE4 hE (by have := hCk 43 (by norm_num); push_cast at this; exact this) hEQ)
      (capE4 hE (by have := hCk 112 (by norm_num); push_cast at this; exact this) hiE)
      hΓ hLay hch
    refine ⟨ok, nd, ?_, goal⟩
    rw [← hdd]
    refine le_trans sh ?_
    have hdeq : d = y + (setLen LAct s + termLen LAct t + 1) := by rw [hdl]; ring
    exact allNode_p4 hd1 le_add_self hdeq hCs'
  · -- wkRule
    intro s hs d' hsub hd' ih hE L Γ hL hΓ hLay
    rw [VerifyGraph''.wkRule_iff] at hL
    obtain ⟨L', -, hL', rfl⟩ := hL
    rw [fstIdx_wkRule] at hLay ⊢
    have hD : Derivation TAct (wkRule s d') := Derivation.wkRule hs hsub ⟨rfl, hd'⟩
    have hd1 : 1 ≤ dlen TAct (wkRule s d') := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (wkRule s d') := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_wkRule] at this
    have hcD := setLen_child_le_dlen_wkRule hD
    have hy := dlen_d_succ_le_wkRule hD
    have hdl := dlen_wkRule hD
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (wkRule s d') := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hcD hy hdl
    obtain ⟨y, hyd⟩ : ∃ x, x = dlen TAct d' := ⟨_, rfl⟩
    rw [← hyd] at hy hdl
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hmD : y ≤ d := le_trans le_self_add hy
    have hch : ChildOK tbl Wc T E L' d' (Csv * p4 y) := fun Γ' hΓ' hLay' ↦ by
      rw [hyd]
      exact ih (le_trans (child_bound4 (by rw [← hyd]; exact le_trans hy le_self_add)) hE) L' Γ' hL' hΓ' hLay'
    have hlin : 40 * d + 18 * ‖d‖ + 40 ≤ 98 * p4 (d + 1) := by
      calc 40 * d + 18 * ‖d‖ + 40 ≤ (40 + 18 + 40) * (d + 1) := lin_cap 40 18 40 d
        _ = 98 * (d + 1) := by ring
        _ ≤ 98 * p4 (d + 1) := mul_le_mul_of_nonneg_left (le_p4_self he1) zero_le
    have h98 : (98 : V) ≤ 4 * Csv := by rw [hCsv]; exact le_trans (b := 4 * ((25731 : ℕ) : V)) (by exact_mod_cast (by norm_num : 98 ≤ 4 * 25731)) (mul_le_mul_of_nonneg_left le_self_add zero_le)
    obtain ⟨ok, nd, sh, goal⟩ := vWk_ok (D := d) htbl hP htblN hWl hWc hWp hW₁ hs hd' hsub hsD hcD (by rw [← hyd]; exact hmD)
      (capE4 hE hCsCk (by
        calc 40 * d + 18 * ‖d‖ + Csv * p4 y + 40 = (40 * d + 18 * ‖d‖ + 40) + Csv * p4 y := by ring
          _ ≤ 98 * p4 (d + 1) + Csv * p4 (d + 1) := add_le_add hlin (child_bound4 (le_trans hmD le_self_add))
          _ = (98 + Csv) * p4 (d + 1) := by ring
          _ ≤ (4 * Csv + Csv) * p4 (d + 1) := mul_le_mul_of_nonneg_right (add_le_add h98 (le_refl _)) zero_le
          _ = 5 * Csv * p4 (d + 1) := by ring))
      hΓ hLay hch
    refine ⟨ok, nd, ?_, goal⟩
    rw [← hdd]
    refine le_trans sh ?_
    have hdeq : d = y + (setLen LAct s + 1) := by rw [hdl]; ring
    have hX : 7 * d + 8 ≤ Csv * p3 d := lin_le_p3 hd1 (by
      rw [hCsv]; exact le_trans (b := ((25731 : ℕ) : V)) (by exact_mod_cast (by norm_num : 7 + 8 ≤ 25731)) le_self_add)
    calc 7 * d + Csv * p4 y + 8 = (7 * d + 8) + Csv * p4 y := by ring
      _ ≤ Csv * p4 d := rec1₄ le_add_self hdeq hX
  · -- shiftRule
    intro s hs d' hsc hd' ih hE L Γ hL hΓ hLay
    rw [VerifyGraph''.shiftRule_iff] at hL
    obtain ⟨L', -, hL', rfl⟩ := hL
    rw [fstIdx_shiftRule] at hLay ⊢
    have hD : Derivation TAct (shiftRule s d') := by
      have := Derivation.shiftRule (T := TAct) ⟨rfl, hd'⟩; rwa [← hsc] at this
    have hd1 : 1 ≤ dlen TAct (shiftRule s d') := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (shiftRule s d') := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_shiftRule] at this
    have hcD := setLen_child_le_dlen_shiftRule hD
    have hy := dlen_d_succ_le_shiftRule hD
    have hdl := dlen_shiftRule hD
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (shiftRule s d') := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hcD hy hdl
    obtain ⟨y, hyd⟩ : ∃ x, x = dlen TAct d' := ⟨_, rfl⟩
    rw [← hyd] at hy hdl
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hmD : y ≤ d := le_trans le_self_add hy
    have hch : ChildOK tbl Wc T E L' d' (Csv * p4 y) := fun Γ' hΓ' hLay' ↦ by
      rw [hyd]
      exact ih (le_trans (child_bound4 (by rw [← hyd]; exact le_trans hy le_self_add)) hE) L' Γ' hL' hΓ' hLay'
    have hlin : 40 * d + 18 * ‖d‖ + 40 ≤ 98 * p4 (d + 1) := by
      calc 40 * d + 18 * ‖d‖ + 40 ≤ (40 + 18 + 40) * (d + 1) := lin_cap 40 18 40 d
        _ = 98 * (d + 1) := by ring
        _ ≤ 98 * p4 (d + 1) := mul_le_mul_of_nonneg_left (le_p4_self he1) zero_le
    have h98 : (98 : V) ≤ 4 * Csv := by rw [hCsv]; exact le_trans (b := 4 * ((25731 : ℕ) : V)) (by exact_mod_cast (by norm_num : 98 ≤ 4 * 25731)) (mul_le_mul_of_nonneg_left le_self_add zero_le)
    obtain ⟨ok, nd, sh, goal⟩ := vShift_ok (D := d) htbl hP htblN hWl hWc hWp hW₂ hs hd' hsc hsD hcD (by rw [← hyd]; exact hmD)
      (capE4 hE hCsCk (by
        calc 40 * d + 18 * ‖d‖ + Csv * p4 y + 40 = (40 * d + 18 * ‖d‖ + 40) + Csv * p4 y := by ring
          _ ≤ 98 * p4 (d + 1) + Csv * p4 (d + 1) := add_le_add hlin (child_bound4 (le_trans hmD le_self_add))
          _ = (98 + Csv) * p4 (d + 1) := by ring
          _ ≤ (4 * Csv + Csv) * p4 (d + 1) := mul_le_mul_of_nonneg_right (add_le_add h98 (le_refl _)) zero_le
          _ = 5 * Csv * p4 (d + 1) := by ring))
      hΓ hLay hch
    refine ⟨ok, nd, ?_, goal⟩
    rw [← hdd]
    refine le_trans sh ?_
    have hdeq : d = y + (setLen LAct s + 1) := by rw [hdl]; ring
    have hX : 7 * d + 8 ≤ Csv * p3 d := lin_le_p3 hd1 (by
      rw [hCsv]; exact le_trans (b := ((25731 : ℕ) : V)) (by exact_mod_cast (by norm_num : 7 + 8 ≤ 25731)) le_self_add)
    calc 7 * d + Csv * p4 y + 8 = (7 * d + 8) + Csv * p4 y := by ring
      _ ≤ Csv * p4 d := rec1₄ le_add_self hdeq hX
  · -- cutRule
    intro s hs p d₁ d₂ hd₁ hd₂ ih₁ ih₂ hE L Γ hL hΓ hLay
    rw [VerifyGraph''.cutRule_iff] at hL
    obtain ⟨L₁, -, hL₁, L₂, -, hL₂, rfl⟩ := hL
    rw [fstIdx_cutRule] at hLay ⊢
    have hD : Derivation TAct (cutRule s p d₁ d₂) := Derivation.cutRule hd₁ hd₂
    have hd1 : 1 ≤ dlen TAct (cutRule s p d₁ d₂) := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (cutRule s p d₁ d₂) := by
      have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_cutRule] at this
    have hc₁D := setLen_child_le_dlen_cutRule_left hD
    have hc₂D := setLen_child_le_dlen_cutRule_right hD
    have hy₁ := dlen_d₁_succ_le_cutRule hD
    have hy₂ := dlen_d₂_succ_le_cutRule hD
    have hdl := dlen_cutRule hD
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (cutRule s p d₁ d₂) := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hc₁D hc₂D hy₁ hy₂ hdl
    obtain ⟨y₁, hy₁d⟩ : ∃ x, x = dlen TAct d₁ := ⟨_, rfl⟩
    obtain ⟨y₂, hy₂d⟩ : ∃ x, x = dlen TAct d₂ := ⟨_, rfl⟩
    rw [← hy₁d] at hy₁ hdl; rw [← hy₂d] at hy₂ hdl
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hm₁D : y₁ ≤ d := le_trans le_self_add hy₁
    have hm₂D : y₂ ≤ d := le_trans le_self_add hy₂
    have hch₁ : ChildOK tbl Wc T E L₁ d₁ (Csv * p4 y₁) := fun Γ' hΓ' hLay' ↦ by
      rw [hy₁d]
      exact ih₁ (le_trans (child_bound4 (by rw [← hy₁d]; exact le_trans hy₁ le_self_add)) hE) L₁ Γ' hL₁ hΓ' hLay'
    have hch₂ : ChildOK tbl Wc T E L₂ d₂ (Csv * p4 y₂) := fun Γ' hΓ' hLay' ↦ by
      rw [hy₂d]
      exact ih₂ (le_trans (child_bound4 (by rw [← hy₂d]; exact le_trans hy₂ le_self_add)) hE) L₂ Γ' hL₂ hΓ' hLay'
    have hlin : 60 * d + 18 * ‖d‖ + 60 ≤ 138 * p4 (d + 1) := by
      calc 60 * d + 18 * ‖d‖ + 60 ≤ (60 + 18 + 60) * (d + 1) := lin_cap 60 18 60 d
        _ = 138 * (d + 1) := by ring
        _ ≤ 138 * p4 (d + 1) := mul_le_mul_of_nonneg_left (le_p4_self he1) zero_le
    have h138 : (138 : V) ≤ 2 * Csv := by rw [hCsv]; exact le_trans (b := 2 * ((25731 : ℕ) : V)) (by exact_mod_cast (by norm_num : 138 ≤ 2 * 25731)) (mul_le_mul_of_nonneg_left le_self_add zero_le)
    obtain ⟨ok, nd, sh, goal⟩ := vCut_ok (D := d) htbl hP htblN hWl hWc hWp hW₁ hs hd₁ hd₂ hsD hc₁D hc₂D
      (by rw [← hy₁d]; exact hm₁D) (by rw [← hy₂d]; exact hm₂D)
      (capE4 hE hCsCk (by
        calc 60 * d + 18 * ‖d‖ + Csv * p4 y₁ + 2 * (Csv * p4 y₂) + 60
            = (60 * d + 18 * ‖d‖ + 60) + Csv * p4 y₁ + 2 * (Csv * p4 y₂) := by ring
          _ ≤ 138 * p4 (d + 1) + Csv * p4 (d + 1) + 2 * (Csv * p4 (d + 1)) :=
              add_le_add (add_le_add hlin (child_bound4 (le_trans hm₁D le_self_add)))
                (mul_le_mul_of_nonneg_left (child_bound4 (le_trans hm₂D le_self_add)) zero_le)
          _ = (138 + 3 * Csv) * p4 (d + 1) := by ring
          _ ≤ (2 * Csv + 3 * Csv) * p4 (d + 1) := mul_le_mul_of_nonneg_right (add_le_add h138 (le_refl _)) zero_le
          _ = 5 * Csv * p4 (d + 1) := by ring))
      hΓ hLay hch₁ hch₂
    refine ⟨ok, nd, ?_, goal⟩
    rw [← hdd]
    refine le_trans sh ?_
    have hdeq : d = y₁ + y₂ + (setLen LAct s + 1) := by rw [hdl]; ring
    have hX : 20 * d + 9 ≤ Csv * p3 d := lin_le_p3 hd1 (by
      rw [hCsv]; exact le_trans (b := ((25731 : ℕ) : V)) (by exact_mod_cast (by norm_num : 20 + 9 ≤ 25731)) le_self_add)
    calc 20 * d + Csv * p4 y₁ + Csv * p4 y₂ + 9 = (20 * d + 9) + Csv * p4 y₁ + Csv * p4 y₂ := by ring
      _ ≤ Csv * p4 d := rec2₄ le_add_self hdeq hX
  · -- axm
    intro s hs p hps hpT hE L Γ hL hΓ hLay
    rw [VerifyGraph''.axm_iff] at hL
    obtain ⟨pro, -, hmem, rfl⟩ := hL
    rw [fstIdx_axm] at hLay ⊢
    obtain ⟨p', -, ip', -, pro', -, heq, hok, hnd, hsh, -, -, hfact⟩ := hA _ hmem
    obtain ⟨e₁, heq₂⟩ := pair_ext_iff.mp heq
    obtain ⟨e₂, e₃⟩ := pair_ext_iff.mp heq₂
    subst e₁; subst e₂; subst e₃
    have hD : Derivation TAct (axm s p) := Derivation.axm hs hps hpT
    have hd1 : 1 ≤ dlen TAct (axm s p) := one_le_dlen hD
    have hsD : setLen LAct s ≤ dlen TAct (axm s p) := by have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_axm] at this
    have hkD : len (memberList s) ≤ dlen TAct (axm s p) := le_trans (len_memberList_le_setLen hs) hsD
    have hpd : formulaLen LAct p + 1 ≤ dlen TAct (axm s p) := by
      rw [dlen_axm hD]; exact add_le_add (formulaLen_le_setLen_of_mem (L := LAct) hps) le_rfl
    obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (axm s p) := ⟨_, rfl⟩
    rw [← hdd] at hE hd1 hsD hkD hpd
    have he1 : (1 : V) ≤ d + 1 := le_add_self
    have hsh' : shiftsV pro ≤ Cv * p3 (formulaLen LAct p + 1) := by unfold entryB at hsh; exact hsh
    -- the entry's shift under the budget
    have hσ : shiftsV pro ≤ Cv * p4 d :=
      le_trans hsh' (mul_le_mul_of_nonneg_left (le_trans (p3_mono hpd) (p3_le_p4 hd1)) zero_le)
    have hσE : shiftsV pro ≤ Cv * p4 (d + 1) := le_trans hσ (child_bound4 le_self_add)
    have capσ : ∀ {X c : V}, c ≤ 9 → X ≤ shiftsV pro + c * (d + 1) → X ≤ E := fun {X c} hc hX ↦ by
      refine le_trans hX (le_trans ?_ hE)
      calc shiftsV pro + c * (d + 1) ≤ Cv * p4 (d + 1) + 9 * p4 (d + 1) :=
            add_le_add hσE (mul_le_mul hc (le_p4_self he1) zero_le zero_le)
        _ = (Cv + 9) * p4 (d + 1) := by ring
        _ ≤ Ckv * p4 (d + 1) := mul_le_mul_of_nonneg_right hCv9 zero_le
    have hn : 18 * ‖setLen LAct s + 1‖ + 7 ≤ 43 * (d + 1) := by
      have h1 : ‖setLen LAct s + 1‖ ≤ d + 1 := le_trans (length_le _) (add_le_add hsD (le_refl 1))
      calc 18 * ‖setLen LAct s + 1‖ + 7 ≤ 18 * (d + 1) + 7 := add_le_add (mul_le_mul_of_nonneg_left h1 zero_le) (le_refl 7)
        _ ≤ 43 * (d + 1) := le_of_add_eq' (c := 25 * d + 18) (by ring)
    have hiE' : shiftsV pro + 6 * d + 3 ≤ E := capσ (c := 9) le_rfl (by
      rw [add_assoc]; exact add_le_add le_rfl (le_of_add_eq' (c := 3 * d + 6) (by ring)))
    have hkE' : shiftsV pro + len (memberList s) + 3 ≤ E := capσ (c := 9) le_rfl (by
      rw [add_assoc]; exact add_le_add le_rfl (le_trans (add_le_add hkD le_rfl) (le_of_add_eq' (c := 8 * d + 6) (by ring))))
    have hlE' : shiftsV pro + 4 ≤ E := capσ (c := 9) le_rfl (add_le_add le_rfl (le_of_add_eq' (c := 9 * d + 5) (by ring)))
    obtain ⟨ok, nd, sh, goal⟩ := vAxm_ok' (D := d) htbl hP htblN hWc hW₂ hs hps hpT hsD hiE' hkE' hlE'
      (capE4' hE he1 (hCk 43 (by norm_num)) (by push_cast; exact hn)) hΓ hLay.layout ⟨hok, hnd, hfact⟩
    refine ⟨ok, nd, ?_, ?_⟩
    · rw [sh, ← hdd]
      calc shiftsV pro + 1 ≤ Cv * p3 (formulaLen LAct p + 1) + 1 := add_le_add hsh' le_rfl
        _ ≤ Csv * p4 d := axmLeaf_p4 hpd hd1 hCv1
    · rw [sh, ← add_assoc]; exact goal

end glue4

/-! ## 2. The kit-facing form: `(dlen ρ + 1)^4`, the constant `Ck·(Cv + 1)` -/

section kitForm4

/-- `verifyGraph''_ok4` restated with the `VerifyKit''`-style multiplier `(dlen ρ + 1)^4` and ONE constant `Ck·(Cv + 1)`
(`Cv` the table's constant; `verifyGraph''_exists_unconditional` supplies a standard one) — `Verify3.verifyGraph''_ok_pow`
at exponent 4, so the kit's `m` is `4` and `Top.deg 4 = 16`. -/
theorem verifyGraph''_ok_pow4 : ∃ Ck : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {tbl N N' B' Ww Wl Wc W₁ W₂ W T A Cv E ρ : V},
    TableOK tbl N → ProTable tbl → NumTableOK T N' B' → Ww = walkPieces → Wl = layoutPieces → Wc = certPieces →
    W₁ = frag1Pieces → W₂ = frag2Pieces → W = proPieces → AxmTableOK' tbl E Ww A Cv → Derivation TAct ρ →
    (Ck : V) * (Cv + 1) * (dlen TAct ρ + 1) ^ 4 ≤ E →
    ∀ L Γ : V, VerifyGraph'' Ww Wl Wc W₁ W₂ W T A ρ L → IsFormulaSet LAct Γ → NodeLay Ww Wc T Γ (fstIdx ρ) →
      ListOK tbl E ((9 : ℕ) : V) Γ L ∧ NoDrop' L ∧ shiftsV L ≤ (Ck : V) * (Cv + 1) * (dlen TAct ρ + 1) ^ 4 ∧
      neg LAct (goalFact (^&(len (memberList (fstIdx ρ)) + 1 + shiftsV L)) (bnum (dlen TAct ρ))) ∈ finalCtx Γ L := by
  obtain ⟨Cs, Ck, h⟩ := verifyGraph''_ok4
  refine ⟨Cs + Ck + 5, fun V _ _ tbl N N' B' Ww Wl Wc W₁ W₂ W T A Cv E ρ htbl hP htblN hWw hWl hWc hW₁ hW₂ hWp hA hd hE
    L Γ hL hΓ hLay ↦ ?_⟩
  have hp : (dlen TAct ρ + 1) ^ 4 = p4 (dlen TAct ρ + 1) := pow4_eq_p4 _
  rw [hp] at hE ⊢
  have hE' : (((Ck : ℕ) : V) + 5 * Cv) * p4 (dlen TAct ρ + 1) ≤ E := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ zero_le) hE
    push_cast
    exact le_of_add_eq' (c := ((Cs : V) + Ck) * Cv + Cs + 5) (by ring)
  obtain ⟨ok, nd, sh, goal⟩ := h V htbl hP htblN hWw hWl hWc hW₁ hW₂ hWp hA hd hE' L Γ hL hΓ hLay
  refine ⟨ok, nd, ?_, goal⟩
  refine le_trans sh (mul_le_mul ?_ (p4_mono le_self_add) zero_le zero_le)
  push_cast
  exact le_of_add_eq' (c := ((Cs : V) + Ck + 4) * Cv + Ck + 5) (by ring)

end kitForm4

end ArithS
