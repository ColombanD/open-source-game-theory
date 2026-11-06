import ArithS.Tau.Entangled.Generic
import ArithS.Tau.Entangled.EBotPrudent
import ArithS.Tau.Watch2
import ArithS.Tau.ClosedWatch

/-!
# ArithS.Tau.Entangled.DimcidPrudent — the `dimcid × prudent` systems: two bits D (Phase 3e)

`inst dimcid prudent = .sys [dim 1, pm 0 dimcid] 0` and `inst prudent dimcid = .sys [pm 1 dimcid, dim 0] 0`. The
Prudent member is NESTED: its outer guard probes the DIMCID member, its inner (prudence) guard freezes DIMCID's
instance at the defector — a `.search k`, so before route (c) was made generic the member's stored template carried
`binNumeral k` and the system was the `k̂`-instance of no fixed term (`DupocPrudent.lean`'s §7 obstacle). Since
Phase 2c the inner template is stored with the budget abstracted, and it is a CONSTANT (`templateAt_probeD_dimcid_
defect`: the description of the bot-wrapped searcher `SV`, `Tau/Stored.closedDescAt_botSV`, at EVERY budget). The
Prudent member is therefore a nested member `NM` (`EBotPrudent.lean`) on two fixed templates, and the system is a
`Sys2m` (`Generic.lean`) of a nested and a simple member:

* §1 the τ-order of the two mixed lists: `[simple, nested]` is decided by its second member (`member1_dominates`),
  `[nested, simple]` by its FIRST — the nested member's gain over its transposition (`nested_gain`, the gain
  calculus of `Tau/Watch2.lean`) exceeds the whole tail (`nested_dominates`);
* §2 `Sys2m.ofSN`/`Sys2m.ofNS` and their soundness;
* §3 Prudent's member at DIMCID (`PMd`) and its code at ℕ;
* §4 **`dimcid × prudent` is D** — the `S'` flip: the DIMCID member finds its self-fulfilling guard in the bit's
  frame (`Sys2m.found_Di`); **`prudent × dimcid` is D**: the DIMCID member defects against itself, so the Prudent
  member's outer probe "it cooperates with itself" is false, never found (soundness), and the else-branch plays D.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD PD.Tau

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The τ-order of the mixed lists -/

/-- The base step through a search wrapper: the inner part raised by one raises `ppair k ·` by the slack plus `k`. -/
theorem Gain.base {c x y y' : V} (h : y + 1 ≤ y') (hc : c ≤ x) : Gain c (ppair x y) (ppair x y') x := by
  refine ⟨?_, hc⟩
  have h3 := ppair_add_le_of_succ_le x h
  calc ppair x y + c + x ≤ ppair x y + x + x := add_le_add (add_le_add le_rfl hc) le_rfl
    _ ≤ ppair x y + x + x + (2 * y + 2) := le_self_add
    _ = ppair x y + (2 * (x + y) + 2) := by ring
    _ ≤ ppair x y' := h3

lemma one_le_mul' {a b : V} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := le_trans ha (le_mul_right_of_one_le a hb)

/-- A gain that covers a tail decides a sum. -/
lemma add_lt_of_gain {a a' c g r r' : V} (hg : Gain c a a' g) (hc : 1 ≤ c) (hr : r ≤ g) : a + r < a' + r' := by
  calc a + r ≤ a + g := add_le_add le_rfl hr
    _ < a + g + 1 := lt_add_one _
    _ ≤ a + g + c := add_le_add le_rfl hc
    _ = a + c + g := by ring
    _ ≤ a' := hg.1
    _ ≤ a' + r' := le_self_add

/-- **The gain of a nested searcher over a rival with a larger inner part**: the slack `c` (above the constant
parts) plus a gain that is at least the member's `ppair k ·` layer. -/
theorem nested_gain {k G G' I I' c₀ c₀' c : V} (hI : I + 1 ≤ I') (hck : c ≤ k) (h1 : 1 ≤ c) (hG : G ≤ c) (hc₀ : c₀ ≤ c) :
    ∃ g, Gain c (ppair 6 (ppair k (ppair G (ppair (ppair 6 (ppair k I) + 1) c₀))) + 1)
        (ppair 6 (ppair k (ppair G' (ppair (ppair 6 (ppair k I') + 1) c₀'))) + 1) g ∧
      ppair k (ppair G (ppair (ppair 6 (ppair k I) + 1) c₀)) ≤ g := by
  have hk1 : (1 : V) ≤ k := le_trans h1 hck
  have g1 : Gain c (ppair k I) (ppair k I') k := Gain.base hI hck
  have hX : (1 : V) ≤ ppair k I := le_trans hk1 (le_ppair_left _ _)
  have g2 := (Gain.ppair_right (c := c) (x := 6) (x' := 6) le_self_add hX g1).succ
  have hS : (1 : V) ≤ ppair 6 (ppair k I) + 1 := le_add_self
  have g3 := Gain.ppair_left (y := c₀) (y' := c₀') (le_trans hc₀ le_add_self) hS g2
  have hA : (1 : V) ≤ ppair (ppair 6 (ppair k I) + 1) c₀ := le_trans hS (le_ppair_left _ _)
  have g4 := Gain.ppair_right (x := G) (x' := G') (le_trans hG le_add_self) hA g3
  have hB : (1 : V) ≤ ppair G (ppair (ppair 6 (ppair k I) + 1) c₀) := le_trans hA (le_ppair_right _ _)
  have g5 := Gain.ppair_right (c := c) (x := k) (x' := k) le_self_add hB g4
  have hC : (1 : V) ≤ ppair k (ppair G (ppair (ppair 6 (ppair k I) + 1) c₀)) := le_trans hB (le_ppair_right _ _)
  refine ⟨_, (Gain.ppair_right (c := c) (x := 6) (x' := 6) le_self_add hC g5).succ, ?_⟩
  exact le_mul_right_of_one_le _ (one_le_mul' hB (one_le_mul' hA (one_le_mul' hS (one_le_mul' hX hk1))))

/-- **A nested first member decides the list**: its gain exceeds the tail `pCons x pNil` of a member `x` below
the square of its inner searcher. -/
theorem nested_dominates {k G G' I I' c₀ c₀' c x : V} (x' : V) (hI : I + 1 ≤ I') (hck : c ≤ k) (h1 : 1 ≤ c)
    (hG : G ≤ c) (hc₀ : c₀ ≤ c) (h10 : 10 < k)
    (hx : x ≤ (ppair 6 (ppair k I) + 1) * (ppair 6 (ppair k I) + 1)) :
    pCons (ppair 6 (ppair k (ppair G (ppair (ppair 6 (ppair k I) + 1) c₀))) + 1) (pCons x pNil) <
      pCons (ppair 6 (ppair k (ppair G' (ppair (ppair 6 (ppair k I') + 1) c₀'))) + 1) (pCons x' pNil) := by
  obtain ⟨g, hg, hCg⟩ := nested_gain (G' := G') (c₀' := c₀') hI hck h1 hG hc₀
  have hxA : x ≤ ppair (ppair 6 (ppair k I) + 1) c₀ := by
    refine le_trans hx ?_
    unfold ppair
    exact le_trans (mul_le_mul le_self_add le_self_add (by simp) (by simp)) le_self_add
  have hxxB : ppair x 0 ≤ ppair G (ppair (ppair 6 (ppair k I) + 1) c₀) := by
    rw [ppair_zero_right]
    refine le_trans (mul_le_mul hxA hxA (by simp) (by simp)) ?_
    conv_rhs => unfold ppair
    exact le_trans (mul_le_mul le_add_self le_add_self (by simp) (by simp)) le_self_add
  have hR : pCons x pNil ≤ g := by
    refine le_trans ?_ hCg
    unfold pCons
    exact le_trans (add_le_add (ppair_le_ppair_right 10 hxxB) le_rfl) (lt_iff_succ_le.mp (ppair_lt_ppair_left h10 _))
  rw [pCons_lt_pCons_iff]
  apply ppair_lt_of_add_lt
  exact add_lt_of_gain hg h1 hR

/-- A simple member is below the square of any other simple member at the same budget (`3 ≤ k`, inner part below
`k`): `72 k⁴ ≤ k⁸`. -/
lemma simple_le_sq (k I₀ I₁ : V) (hI : I₀ ≤ k) (hk : 3 ≤ k) :
    ppair 6 (ppair k I₀) + 1 ≤ (ppair 6 (ppair k I₁) + 1) * (ppair 6 (ppair k I₁) + 1) := by
  have h9 : (9 : V) ≤ k * k := le_trans (by norm_num) (mul_le_mul hk hk (by simp) (by simp))
  have h72 : (72 : V) ≤ k * k * (k * k) := by
    calc (72 : V) ≤ 9 * 9 := by norm_num
      _ ≤ k * k * (k * k) := mul_le_mul h9 h9 (by simp) (by simp)
  have h1 := simple_ge_k4 k I₁
  calc ppair 6 (ppair k I₀) + 1 ≤ 72 * (k * k * (k * k)) := simple_le_bound k I₀ hI hk
    _ ≤ (k * k * (k * k)) * (k * k * (k * k)) := mul_le_mul h72 le_rfl (by simp) (by simp)
    _ ≤ (ppair 6 (ppair k I₁) + 1) * (ppair 6 (ppair k I₁) + 1) := mul_le_mul h1 h1 (by simp) (by simp)

/-! ### 2. The mixed systems -/

/-- A nested member as a member tower. -/
noncomputable def MT.ofNM (m : NM) : MT := ⟨m.T1, m.tr.T1⟩

lemma MT.ofNM_code (m : NM) (k : V) : (MT.ofNM m).code k = m.code k := NM.val_T1_V m k
lemma MT.ofNM_tr_code (m : NM) (k : V) : (MT.ofNM m).tr.code k = m.tr.code k := NM.val_T1_V m.tr k

theorem MT.ofNM_ok (m : NM) : (MT.ofNM m).Ok where
  sub := fun V _ _ k ↦ by rw [MT.ofNM_code]; exact NM.termSubst_T1 m k
  subT := fun V _ _ k ↦ by rw [MT.ofNM_tr_code]; exact NM.termSubst_T1 m.tr k
  trc := fun V _ _ k ↦ by rw [MT.ofNM_code, MT.ofNM_tr_code, NM.transposeCode_code]

/-- The threshold of a mixed system: the nested member's template codes, its constants, the simple member's
inner parts (never evaluated). -/
noncomputable def Kmix (m : NM) (s : SM) : ℕ := m.K + 14 + s.inner + s.tr.inner

lemma Kmix_def (m : NM) (s : SM) : Kmix m s = m.K + 14 + s.inner + s.tr.inner := rfl

attribute [irreducible] Kmix

lemma Kmix_facts {m : NM} {s : SM} {k : V} (hk : ((Kmix m s : ℕ) : V) ≤ k) :
    ((m.K : ℕ) : V) + 14 ≤ k ∧ ((s.inner : ℕ) : V) ≤ k ∧ ((s.tr.inner : ℕ) : V) ≤ k := by
  rw [Kmix_def] at hk; push_cast at hk
  exact ⟨le_trans (le_trans le_self_add le_self_add) hk, le_trans (le_trans le_add_self le_self_add) hk,
    le_trans le_add_self hk⟩

/-- The system `[simple, nested]`. -/
noncomputable def Sys2m.ofSN (s : SM) (m : NM) : Sys2m := ⟨MT.ofSM s, MT.ofNM m, Kmix m s, m.orig⟩
/-- The system `[nested, simple]`. -/
noncomputable def Sys2m.ofNS (m : NM) (s : SM) : Sys2m := ⟨MT.ofNM m, MT.ofSM s, Kmix m s, m.orig⟩

/-- **`[simple, nested]` is sound**: the second (nested) member decides the τ-order. -/
theorem Sys2m.ofSN_ok (s : SM) (m : NM) : (Sys2m.ofSN s m).Ok where
  ok₀ := MT.ofSM_ok s
  ok₁ := MT.ofNM_ok m
  hlt := fun h V _ _ k hk ↦ by
    obtain ⟨hK, hI, -⟩ := Kmix_facts hk
    have hmK : ((m.K : ℕ) : V) ≤ k := le_trans le_self_add hK
    have h3 : (3 : V) ≤ k := le_trans (by norm_num) (le_trans le_add_self hK)
    show pCons ((MT.ofSM s).code k) (pCons ((MT.ofNM m).code k) pNil) <
      pCons ((MT.ofSM s).tr.code k) (pCons ((MT.ofNM m).tr.code k) pNil)
    rw [MT.ofSM_code, MT.ofNM_code, MT.ofSM_tr_code, MT.ofNM_tr_code]
    refine (pSys_lt_pSys_iff (j := (0 : V))).mp (sys2_lt_of_member1 (lt_iff_succ_le.mp (NM.code_lt_tr hmK h)) ?_)
    rw [SM.code_eq_inner, NM.code_eq_inner]
    exact member1_dominates k _ _ hI h3
  hgt := fun h V _ _ k hk ↦ by
    obtain ⟨hK, -, hI⟩ := Kmix_facts hk
    have hmK : ((m.K : ℕ) : V) ≤ k := le_trans le_self_add hK
    have h3 : (3 : V) ≤ k := le_trans (by norm_num) (le_trans le_add_self hK)
    show pCons ((MT.ofSM s).tr.code k) (pCons ((MT.ofNM m).tr.code k) pNil) <
      pCons ((MT.ofSM s).code k) (pCons ((MT.ofNM m).code k) pNil)
    rw [MT.ofSM_code, MT.ofNM_code, MT.ofSM_tr_code, MT.ofNM_tr_code]
    refine (pSys_lt_pSys_iff (j := (0 : V))).mp (sys2_lt_of_member1 (lt_iff_succ_le.mp (NM.tr_lt_code hmK h)) ?_)
    rw [SM.code_eq_inner, NM.code_eq_inner]
    exact member1_dominates k _ _ hI h3

/-- **`[nested, simple]` is sound**: the FIRST (nested) member decides the τ-order. -/
theorem Sys2m.ofNS_ok (m : NM) (s : SM) : (Sys2m.ofNS m s).Ok where
  ok₀ := MT.ofNM_ok m
  ok₁ := MT.ofSM_ok s
  hlt := fun h V _ _ k hk ↦ by
    obtain ⟨hK, hI, -⟩ := Kmix_facts hk
    have h14 : (14 : V) ≤ k := le_trans le_add_self hK
    have h3 : (3 : V) ≤ k := le_trans (by norm_num) h14
    show pCons ((MT.ofNM m).code k) (pCons ((MT.ofSM s).code k) pNil) <
      pCons ((MT.ofNM m).tr.code k) (pCons ((MT.ofSM s).tr.code k) pNil)
    rw [MT.ofSM_code, MT.ofNM_code, MT.ofSM_tr_code, MT.ofNM_tr_code, NM.code_eq_inner, NM.code_eq_inner, NM.tr_inn]
    refine nested_dominates (c := ((m.K : ℕ) : V) + 14) _ (lt_iff_succ_le.mp (Nat.cast_lt.mpr h)) hK
      (le_trans (by norm_num) le_add_self) (le_trans (NM.quote_g_le_of_K le_rfl) le_self_add)
      (le_trans (le_trans le_self_add (NM.pConst_sub_succ_le m)) le_add_self) (lt_of_lt_of_le (by norm_num) h14) ?_
    rw [SM.code_eq_inner]
    exact simple_le_sq k _ _ hI h3
  hgt := fun h V _ _ k hk ↦ by
    obtain ⟨hK, -, hI⟩ := Kmix_facts hk
    have h14 : (14 : V) ≤ k := le_trans le_add_self hK
    have h3 : (3 : V) ≤ k := le_trans (by norm_num) h14
    have h' : m.inn.tr.inner < m.inn.inner := lt_of_le_of_ne (not_lt.mp h) (Ne.symm (SM.inner_ne_tr _))
    show pCons ((MT.ofNM m).tr.code k) (pCons ((MT.ofSM s).tr.code k) pNil) <
      pCons ((MT.ofNM m).code k) (pCons ((MT.ofSM s).code k) pNil)
    rw [MT.ofSM_code, MT.ofNM_code, MT.ofSM_tr_code, MT.ofNM_tr_code, NM.code_eq_inner, NM.code_eq_inner, NM.tr_inn]
    refine nested_dominates (c := ((m.K : ℕ) : V) + 14) _ (lt_iff_succ_le.mp (Nat.cast_lt.mpr h')) hK
      (le_trans (by norm_num) le_add_self) (le_trans (NM.quote_gT_le_of_K le_rfl) le_self_add)
      (le_trans (le_trans le_self_add (NM.pConst_sub_succ_le m.tr)) le_add_self) (lt_of_lt_of_le (by norm_num) h14) ?_
    rw [SM.code_eq_inner]
    exact simple_le_sq k _ _ hI h3

/-! ### 3. Prudent's member at DIMCID -/

/-- DIMCID's instance at the defector, as a six-variable template (`Tau/ClosedWatch.sDiDef`). -/
noncomputable abbrev gDiDef : Semisentence LAct 6 := template (implC .D .C .D)

/-- **The stored prudence template of Prudent's member at DIMCID** — "DIMCID's instance at the defector defects
against itself", the frozen searcher described with its budget abstracted: a constant. -/
noncomputable def gPrD : Semisentence LAct 13 := plAt (DfixSV gDiDef 1) (DfixSV gDiDef 1) 1

theorem templateAt_probeD_dimcid_defect (k : ℕ) :
    templateAt (probeD (inst (tauZoo k) .dimcid .defect)) (some k) = gPrD := by
  have hns : noSelfIdxP (.bot (inst (tauZoo k) .dimcid .defect)) = true := rfl
  show templateAt (.plays (.bot (inst (tauZoo k) .dimcid .defect)) (.bot (inst (tauZoo k) .dimcid .defect)) .D) (some k) = _
  rw [templateAt_plays_eq, progGraphAt_closed _ (by simp) (by simp) (pronounP_eq_false_of_noSelfIdxP hns),
    progCode_bot_inst, ← sDiDef_code, show sDiDef = SM.ofSearch (implC .D .C .D) .D from rfl,
    SM.code_ofSearch_eq_SV (V := ℕ) _ rfl, closedDescAt_botSV _ _ (actCode_zero_or_one .D)]
  rfl

/-- Prudent's member at DIMCID (pronoun `j`), as a nested member on two constant templates. -/
noncomputable def PMd (j : ℕ) : NM := ⟨template13 (entDmG j), gPrD, 0, Or.inl rfl⟩

/-- At ℕ, the nested member is the engine's code of Prudent's member, at every budget. -/
theorem PMd_code_nat (j k : ℕ) (hj : j ≤ 1) : (PMd j).code k = progCode (pm j k .dimcid) := by
  have e : progCode (pm j k .dimcid) =
      pSearch k (templateCode (entDmG j)) (pSearch k (⌜gPrD⌝ : ℕ) (pConst 0) (pConst 1)) (pConst 1) := by
    rw [show pm j k .dimcid = .search k (entDmG j)
        (.search k (probeD (inst (tauZoo k) .dimcid .defect)) (.const .C) (.const .D)) (.const .D) from rfl,
      progCode_search_noSnap k (entDmG j) _ _
        (by rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl <;> rfl), progCode_search]
    unfold templateCodeAt
    rw [templateAt_probeD_dimcid_defect]
    simp [actCode]
  rw [e]
  unfold NM.code SM.code
  simp only [PMd, NM.inn, natCast_nat]
  rfl

/-- DIMCID's member (pronoun `j`), as a simple member. -/
noncomputable def sDim (j : ℕ) : SM := SM.ofSearch (entDimG j) .D

/-! ### 4. The two systems and their bits -/

/-- `.sys [dim 1, pm 0 dimcid]`. -/
noncomputable def SDiP : Sys2m := Sys2m.ofSN (sDim 1) (PMd 0)
/-- `.sys [pm 1 dimcid, dim 0]`. -/
noncomputable def SPDi : Sys2m := Sys2m.ofNS (PMd 1) (sDim 0)

theorem SDiP_ok : SDiP.Ok := Sys2m.ofSN_ok _ _
theorem SPDi_ok : SPDi.Ok := Sys2m.ofNS_ok _ _

lemma SDiP_D_nat (k : ℕ) : SDiP.D k = progListCode (sys2 (dim 1 k) (pm 0 k .dimcid)) := by
  show pCons ((MT.ofSM (sDim 1)).code k) (pCons ((MT.ofNM (PMd 0)).code k) pNil) = _
  rw [MT.ofSM_code, MT.ofNM_code, PMd_code_nat 0 k (by decide), show sDim 1 = SM.ofSearch (entDimG 1) .D from rfl,
    SM.code_nat (entDimG 1) .D k]
  rfl

lemma SDiP_code_nat (j k : ℕ) : SDiP.code j k = progCode (.sys (sys2 (dim 1 k) (pm 0 k .dimcid)) j) := by
  unfold Sys2m.code; rw [SDiP_D_nat, progCode_sys, natCast_nat]

lemma SPDi_D_nat (k : ℕ) : SPDi.D k = progListCode (sys2 (pm 1 k .dimcid) (dim 0 k)) := by
  show pCons ((MT.ofNM (PMd 1)).code k) (pCons ((MT.ofSM (sDim 0)).code k) pNil) = _
  rw [MT.ofSM_code, MT.ofNM_code, PMd_code_nat 1 k (by decide), show sDim 0 = SM.ofSearch (entDimG 0) .D from rfl,
    SM.code_nat (entDimG 0) .D k]
  rfl

lemma SPDi_code_nat (j k : ℕ) : SPDi.code j k = progCode (.sys (sys2 (pm 1 k .dimcid) (dim 0 k)) j) := by
  unfold Sys2m.code; rw [SPDi_D_nat, progCode_sys, natCast_nat]

/-- The DIMCID member finds its guard in the bit's frame, on the engine's codes. -/
theorem found_DiP_engine : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot (.sys (sys2 (dim 1 k) (pm 0 k .dimcid)) 1)) .C)
      (.plays (.bot (.sys (sys2 (dim 1 k) (pm 0 k .dimcid)) 1)) .self .D)))
      (progCode (sysFrame (dim 1 k) (pm 0 k .dimcid))) (progCode (sysFrame (dim 1 k) (pm 0 k .dimcid)))) := by
  obtain ⟨k₀, h⟩ := Sys2m.found_Di SDiP_ok (sDim 1) 0 1 (by decide) (by decide)
    (fun V _ _ k ↦ MT.ofSM_code (sDim 1) k) rfl rfl
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, b₁, -⟩ := h k hk
  have := Sys2m.box_guard_nat SDiP_ok hK (sDim 1).g 0 0 b₁
  rw [SDiP_D_nat, SDiP_code_nat, show (⌜(sDim 1).g⌝ : ℕ) = templateCode (entDimG 1) from rfl,
    templateCode_sysClose _ _ rfl, guardCodeB_of_template (isSemiformula_templateCode _ rfl)] at this
  exact this

/-- **`dimcid × prudent`: D** — the `S'` FLIP of the engine's C: the DIMCID member's guard is self-fulfilling in
the system with Prudent's (nested) member. -/
theorem ent_dimcid_prudent : bitEventually .dimcid .prudent .D := by
  obtain ⟨k₀, h⟩ := found_DiP_engine
  exact ⟨k₀, fun k hk ↦ bit_D_of_dim_then (inst_dimcid_prudent k) (h k hk)⟩

/-- **The Prudent member's outer probe is never found**: the DIMCID member defects against itself (its guard is
found in its self-play frame), so "it cooperates with itself" is false in ℕ. -/
theorem prudent_probe_dimcid_not_found : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    ¬ LenBox TAct k (guardCode (templateCode (.plays (.bot (.sys (sys2 (pm 1 k .dimcid) (dim 0 k)) 1))
      (.bot (.sys (sys2 (pm 1 k .dimcid) (dim 0 k)) 1)) .C))
      (progCode (sysFrame (pm 1 k .dimcid) (dim 0 k))) (progCode (sysFrame (pm 1 k .dimcid) (dim 0 k)))) := by
  obtain ⟨k₀, h⟩ := Sys2m.found_Di SPDi_ok (sDim 0) 1 0 (by decide) (by decide)
    (fun V _ _ k ↦ MT.ofSM_code (sDim 0) k) rfl rfl
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, b₁, -⟩ := h k hk
  have hD := Sys2m.plays_of_box_nat SPDi_ok hK (sDim 0) 1 (by decide) (MT.ofSM_code (sDim 0) k) 1 1 b₁
  rw [SPDi_code_nat] at hD
  refine closed_not_found rfl ?_ k
  rw [models_partner_probe]
  exact not_exists_evalGraph_of_ne (a := .C) (b := .D) (by decide) hD

/-- **`prudent × dimcid`: D** — the Prudent member's outer probe of the DIMCID member is false, hence not found. -/
theorem ent_prudent_dimcid : bitEventually .prudent .dimcid .D := by
  obtain ⟨k₀, h⟩ := prudent_probe_dimcid_not_found
  exact ⟨k₀, fun k hk ↦ bit_D_of_pm_else (inst_prudent_dimcid k) (h k hk)⟩

end ArithS.Tau
