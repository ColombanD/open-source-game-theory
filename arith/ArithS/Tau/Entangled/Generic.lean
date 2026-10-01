import ArithS.Tau.Entangled.Dimcid

/-!
# ArithS.Tau.Entangled.Generic — two-member systems given by member TOWERS (Phase 3e)

`Sys2` (two simple members, `Tower.lean`/`Loeb.lean`), `Sys2c` (a simple member and a closed τ-fixed one,
`Mirror.lean`) and `Sys2n` (a nested member and a closed τ-fixed one, `EBotPrudent.lean`) repeat one development
for three member shapes. The systems of Phase 3e mix a NESTED member (Prudent's, whose inner guard is a constant
template since route (c) was made generic) with a SIMPLE one (DIMCID's), in both orders — a fourth and a fifth
shape. This module states the development ONCE, for members given by what it actually uses:

* `MT` — a member tower: the one-variable ℒₒᵣ-terms of a member and of its transposition; `MT.Ok` — the budget
  substitution into their codes gives the structural terms of their values, and τ maps the one's value to the
  other's (`MT.ofSM`: a simple member);
* `Sys2m` — two member towers, a threshold `K` and the decision `lt`; `Sys2m.Ok` — the members are `Ok` and the
  τ-order of the member LIST is uniform above the threshold (`hlt`/`hgt`: the one arithmetic fact a shape owes);
* the canonical codes, the re-valuation terms, the towers `TM`/`TX`, the description values, the thirteen-slot
  instance equation for ANY template (`guard_eq_instB_of`, and its transposed twin), the truth equations of the
  `.impl` guard in both readings (`eval_q_impl`, `eval_q_impl_swap`);
* the search clause of a SIMPLE member sitting in slot `j` (`simple_member_then_V`, `plays_of_box`,
  `tr_plays_of_box`), and **DIMCID's self-fulfilling family on such a system** (`loebSound_Di`, `found_Di`) —
  `Dimcid.lean`'s, whatever the partner's shape.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD PD.Tau

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. Member towers -/

/-- A member tower: the one-variable terms of a member and of its transposition. -/
structure MT where
  T : Semiterm ℒₒᵣ Empty 1
  Tt : Semiterm ℒₒᵣ Empty 1

namespace MT

/-- The member's code at the budget `k`, in every model: the value of its term. -/
noncomputable def code (m : MT) (k : V) : V := m.T.val (s := standardModel V) ![k] Empty.elim

/-- The transposed member. -/
def tr (m : MT) : MT := ⟨m.Tt, m.T⟩

/-- A member tower is sound: its terms instantiate to the structural terms of their values, and τ exchanges
the two values. -/
structure Ok (m : MT) : Prop where
  sub : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb m.T : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (m.code k)
  subT : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb m.Tt : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (m.tr.code k)
  trc : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), transposeCode (m.code k) = m.tr.code k

theorem Ok.tr {m : MT} (h : m.Ok) : m.tr.Ok where
  sub := h.subT
  subT := h.sub
  trc := fun V _ _ k ↦ by
    show transposeCode (m.tr.code k) = m.code k
    rw [← h.trc V k, transposeCode_transposeCode]

/-- A simple member as a member tower. -/
noncomputable def ofSM (s : SM) : MT := ⟨s.T1, s.tr.T1⟩

lemma ofSM_code (s : SM) (k : V) : (ofSM s).code k = s.code k := SM.val_T1_V s k
lemma ofSM_tr_code (s : SM) (k : V) : (ofSM s).tr.code k = s.tr.code k := SM.val_T1_V s.tr k

theorem ofSM_ok (s : SM) : (ofSM s).Ok where
  sub := fun V _ _ k ↦ by rw [ofSM_code]; exact SM.termSubst_T1 s k
  subT := fun V _ _ k ↦ by rw [ofSM_tr_code]; exact SM.termSubst_T1 s.tr k
  trc := fun V _ _ k ↦ by rw [ofSM_code, ofSM_tr_code, SM.transposeCode_code]

end MT

/-! ### 2. Systems of two member towers -/

/-- A two-member system given by its member towers, the threshold of its τ-order and the decision. -/
structure Sys2m where
  m₀ : MT
  m₁ : MT
  K : ℕ
  lt : Prop

namespace Sys2m

noncomputable def D (S : Sys2m) (k : V) : V := pCons (S.m₀.code k) (pCons (S.m₁.code k) pNil)
noncomputable def code (S : Sys2m) (j : ℕ) (k : V) : V := pSys (S.D k) (j : V)
def tr (S : Sys2m) : Sys2m := ⟨S.m₀.tr, S.m₁.tr, S.K, ¬ S.lt⟩

/-- The system is sound: its members are, and the τ-order of the member list is uniform above the threshold. -/
structure Ok (S : Sys2m) : Prop where
  ok₀ : S.m₀.Ok
  ok₁ : S.m₁.Ok
  hlt : S.lt → ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (S.K : V) ≤ k → S.D k < S.tr.D k
  hgt : ¬ S.lt → ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (S.K : V) ≤ k → S.tr.D k < S.D k

theorem Ok.tr {S : Sys2m} (hS : S.Ok) : S.tr.Ok where
  ok₀ := hS.ok₀.tr
  ok₁ := hS.ok₁.tr
  hlt := fun h V _ _ k hk ↦ hS.hgt h V k hk
  hgt := fun h V _ _ k hk ↦ hS.hlt (not_not.mp h) V k hk

theorem transposeCode_D {S : Sys2m} (hS : S.Ok) (k : V) : transposeCode (S.D k) = S.tr.D k := by
  unfold D transposeCode
  rw [revalue_cons, revalue_cons, revalue_nil]
  show pCons (transposeCode _) (pCons (transposeCode _) pNil) = _
  rw [hS.ok₀.trc V k, hS.ok₁.trc V k]; rfl

theorem transposeCode_code {S : Sys2m} (hS : S.Ok) (j : ℕ) (k : V) : transposeCode (S.code j k) = S.tr.code j k := by
  unfold code transposeCode
  rw [revalue_sys]
  show pSys (transposeCode _) _ = _
  rw [transposeCode_D hS]

theorem code_lt_tr {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (h : S.lt) (j : ℕ) :
    S.code j k < S.tr.code j k := by
  unfold code; rw [pSys_lt_pSys_iff]; exact hS.hlt h V k hk

theorem tr_lt_code {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (h : ¬ S.lt) (j : ℕ) :
    S.tr.code j k < S.code j k := by
  unfold code; rw [pSys_lt_pSys_iff]; exact hS.hgt h V k hk

open scoped Classical in
noncomputable def can (S : Sys2m) : Sys2m := if S.lt then S else S.tr
open scoped Classical in
noncomputable def uT (S : Sys2m) : ClosedSemiterm LAct 0 := if S.lt then cterm Act.C else cterm Act.D
open scoped Classical in
noncomputable def wT (S : Sys2m) : ClosedSemiterm LAct 0 := if S.lt then cterm Act.D else cterm Act.C

theorem can_ok {S : Sys2m} (hS : S.Ok) : S.can.Ok := by
  unfold can; split_ifs
  · exact hS
  · exact hS.tr

theorem canonical_code {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    canonical (S.code j k) = S.can.code j k := by
  unfold can
  by_cases h : S.lt
  · rw [if_pos h, canonical_of_lt (by rw [transposeCode_code hS]; exact code_lt_tr hS hk h j)]
  · rw [if_neg h, canonical_of_gt (by rw [transposeCode_code hS]; exact tr_lt_code hS hk h j), transposeCode_code hS]

theorem revalueU_code {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    revalueU (S.code j k) = (⌜S.uT⌝ : V) := by
  unfold revalueU uT
  rw [transposeCode_code hS]
  by_cases h : S.lt
  · rw [if_pos (code_lt_tr hS hk h j), if_pos h, quote_cterm_C]
  · rw [if_neg (lt_asymm (tr_lt_code hS hk h j)), if_pos (tr_lt_code hS hk h j), if_neg h, quote_cterm_D]

theorem revalueW_code {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    revalueW (S.code j k) = (⌜S.wT⌝ : V) := by
  unfold revalueW wT
  rw [transposeCode_code hS]
  by_cases h : S.lt
  · rw [if_pos (code_lt_tr hS hk h j), if_pos h, quote_cterm_D]
  · rw [if_neg (lt_asymm (tr_lt_code hS hk h j)), if_pos (tr_lt_code hS hk h j), if_neg h, quote_cterm_C]

theorem revalue_val_uT_wT {S : Sys2m} (hS : S.Ok) (k : V) (j : ℕ) :
    revalue (S.uT.val (s := stdReadingV V) ![] Empty.elim) (S.wT.val (s := stdReadingV V) ![] Empty.elim)
      (S.can.code j k) = S.code j k := by
  unfold uT wT can
  by_cases h : S.lt
  · rw [if_pos h, if_pos h, if_pos h, val_cterm_C_V, val_cterm_D_V, revalue_zero_one]
  · rw [if_neg h, if_neg h, if_neg h, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (S.tr.code j k) = _
    rw [← transposeCode_code hS j k, transposeCode_transposeCode]

theorem revalue_val_uT_wT_swap {S : Sys2m} (hS : S.Ok) (k : V) (j : ℕ) :
    revalue ((Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim) (S.can.code j k) = S.tr.code j k := by
  unfold uT wT can
  by_cases h : S.lt
  · rw [if_pos h, if_pos h, if_pos h, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (S.code j k) = _
    rw [transposeCode_code hS]
  · rw [if_neg h, if_neg h, if_neg h, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
      revalue_zero_one]

/-! #### The towers -/

noncomputable def T1 (S : Sys2m) (j : ℕ) : Semiterm ℒₒᵣ Empty 1 := sysT1 (consT1 S.m₀.T (consT1 S.m₁.T nilT1)) j

lemma val_T1_V (S : Sys2m) (j : ℕ) (k : V) : (S.T1 j).val (s := standardModel V) ![k] Empty.elim = S.code j k := by
  rw [T1, val_sysT1_V, val_consT1_V, val_consT1_V, val_nilT1_V]; rfl

lemma termSubst_T1 {S : Sys2m} (hS : S.Ok) (j : ℕ) (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb (S.T1 j) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (S.code j k) := by
  rw [T1]
  exact termSubst_sysT1 _ (termSubst_consT1 _ (hS.ok₀.sub V k) (termSubst_consT1 _ (hS.ok₁.sub V k) (termSubst_nilT1 _))) j

noncomputable def TM (S : Sys2m) (j : ℕ) : Semiterm LAct Empty 1 := Semiterm.lMap emb (S.can.T1 j)
noncomputable def TX (S : Sys2m) (j : ℕ) : Semiterm LAct Empty 1 := Semiterm.lMap emb (botT1 (S.can.T1 j))
lemma lMap_swap_TM (S : Sys2m) (j : ℕ) : Semiterm.lMap swap (S.TM j) = S.TM j := term_lMap_swap_emb _
lemma lMap_swap_TX (S : Sys2m) (j : ℕ) : Semiterm.lMap swap (S.TX j) = S.TX j := term_lMap_swap_emb _

theorem val_TM_V {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    (S.TM j).val (s := stdReadingV V) ![k] Empty.elim = canonical (S.code j k) := by
  unfold TM; rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_T1_V, canonical_code hS hk]
theorem val_TX_V {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    (S.TX j).val (s := stdReadingV V) ![k] Empty.elim = canonical (pBot (S.code j k)) := by
  unfold TX; rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_botT1_V, val_T1_V, canonical_pBot, canonical_code hS hk]
theorem hX_TM {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb (S.TM j) : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (S.code j k)) := by
  unfold TM; rw [term_emb_lMap_emb_n, quote_term_lMap_emb, termSubst_T1 (can_ok hS), canonical_code hS hk]
theorem hX_TX {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb (S.TX j) : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (pBot (S.code j k))) := by
  unfold TX
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, termSubst_botT1 _ (termSubst_T1 (can_ok hS) _ _), canonical_pBot,
    canonical_code hS hk]

theorem descVal_TM {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    descVal (S.TM j) S.uT S.wT k = S.code j k := by
  rw [descVal_def, val_TM_V hS hk, canonical_code hS hk, revalue_val_uT_wT hS]
theorem descVal_TM_T {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    descVal (Semiterm.lMap swap (S.TM j)) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT) k = S.tr.code j k := by
  rw [descVal_def, lMap_swap_TM, val_TM_V hS hk, canonical_code hS hk, revalue_val_uT_wT_swap hS]
theorem descVal_TX {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    descVal (S.TX j) S.uT S.wT k = pBot (S.code j k) := by
  rw [descVal_def, val_TX_V hS hk, canonical_pBot, revalue_bot, canonical_code hS hk, revalue_val_uT_wT hS]
theorem descVal_TX_T {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    descVal (Semiterm.lMap swap (S.TX j)) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT) k = pBot (S.tr.code j k) := by
  rw [descVal_def, lMap_swap_TX, val_TX_V hS hk, canonical_pBot, revalue_bot, canonical_code hS hk,
    revalue_val_uT_wT_swap hS]

/-! #### The instance equation, for any thirteen-variable template -/

lemma code_zero (S : Sys2m) (k : V) : S.code 0 k = pSys (S.D k) 0 := by unfold code; rw [Nat.cast_zero]
lemma code_one (S : Sys2m) (k : V) : S.code 1 k = pSys (S.D k) 1 := by unfold code; rw [Nat.cast_one]

/-- A thirteen-variable template consulted in the frame of the bot-wrapped members `(i, i')`. -/
noncomputable def q (S : Sys2m) (g : Semisentence LAct 13) (i i' : ℕ) : Semisentence LAct 1 :=
  qT13 g (S.TX i) S.uT S.wT (S.TX i') S.uT S.wT (S.TM 0) S.uT S.wT (S.TM 1) S.uT S.wT

theorem guard_eq_instB_of {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (g : Semisentence LAct 13) (i i' : ℕ) :
    guardCodeB (sysCloseTemplate (S.D k) ((⌜g⌝ : ℕ) : V)) (pBot (S.code i k)) (pBot (S.code i' k)) k =
      instB (⌜S.q g i i'⌝ : V) k := by
  rw [coe_quote_sentence₁₃]
  unfold q
  refine guardCodeB_sysClose_eq_instB _ k (S.D k) _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hX_TX hS hk i
  · rw [revalueU_pBot, revalueU_code hS hk]
  · rw [revalueW_pBot, revalueW_code hS hk]
  · exact hX_TX hS hk i'
  · rw [revalueU_pBot, revalueU_code hS hk]
  · rw [revalueW_pBot, revalueW_code hS hk]
  · rw [← code_zero]; exact hX_TM hS hk 0
  · rw [← code_zero, revalueU_code hS hk]
  · rw [← code_zero, revalueW_code hS hk]
  · rw [← code_one]; exact hX_TM hS hk 1
  · rw [← code_one, revalueU_code hS hk]
  · rw [← code_one, revalueW_code hS hk]

theorem canonical_tr_code {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    canonical (S.tr.code j k) = S.can.code j k := by
  rw [← transposeCode_code hS, canonical_transposeCode, canonical_code hS hk]

theorem revalueU_tr_code {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    revalueU (S.tr.code j k) = (⌜Semiterm.lMap swap S.uT⌝ : V) := by
  have e : transposeCode (S.tr.code j k) = S.code j k := by rw [← transposeCode_code hS, transposeCode_transposeCode]
  unfold revalueU uT
  rw [e]
  by_cases h : S.lt
  · rw [if_neg (lt_asymm (code_lt_tr hS hk h j)), if_pos (code_lt_tr hS hk h j), if_pos h, lMap_swap_cterm_C, quote_cterm_D]
  · rw [if_pos (tr_lt_code hS hk h j), if_neg h, lMap_swap_cterm_D, quote_cterm_C]

theorem revalueW_tr_code {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    revalueW (S.tr.code j k) = (⌜Semiterm.lMap swap S.wT⌝ : V) := by
  have e : transposeCode (S.tr.code j k) = S.code j k := by rw [← transposeCode_code hS, transposeCode_transposeCode]
  unfold revalueW wT
  rw [e]
  by_cases h : S.lt
  · rw [if_neg (lt_asymm (code_lt_tr hS hk h j)), if_pos (code_lt_tr hS hk h j), if_pos h, lMap_swap_cterm_D, quote_cterm_C]
  · rw [if_pos (tr_lt_code hS hk h j), if_neg h, lMap_swap_cterm_C, quote_cterm_D]

lemma lMap_swap_q (S : Sys2m) (g : Semisentence LAct 13) (i i' : ℕ) :
    Semiformula.lMap swap (S.q g i i') =
      qT13 (Semiformula.lMap swap g) (S.TX i) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT)
        (S.TX i') (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT)
        (S.TM 0) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT)
        (S.TM 1) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT) := by
  unfold q
  rw [lMap_swap_qT13, lMap_swap_TX, lMap_swap_TX, lMap_swap_TM, lMap_swap_TM]

/-- The transposed instance equation. -/
theorem tr_guard_eq_instB_of {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (g : Semisentence LAct 13) (i i' : ℕ) :
    guardCodeB (sysCloseTemplate (S.tr.D k) ((⌜Semiformula.lMap swap g⌝ : ℕ) : V)) (pBot (S.tr.code i k)) (pBot (S.tr.code i' k)) k =
      instB (⌜Semiformula.lMap swap (S.q g i i')⌝ : V) k := by
  rw [coe_quote_sentence₁₃, lMap_swap_q]
  refine guardCodeB_sysClose_eq_instB _ k (S.tr.D k) _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hX_TX hS hk, canonical_pBot, canonical_pBot, canonical_tr_code hS hk, canonical_code hS hk]
  · rw [revalueU_pBot, revalueU_tr_code hS hk]
  · rw [revalueW_pBot, revalueW_tr_code hS hk]
  · rw [hX_TX hS hk, canonical_pBot, canonical_pBot, canonical_tr_code hS hk, canonical_code hS hk]
  · rw [revalueU_pBot, revalueU_tr_code hS hk]
  · rw [revalueW_pBot, revalueW_tr_code hS hk]
  · rw [hX_TM hS hk, ← code_zero, canonical_tr_code hS hk, canonical_code hS hk]
  · rw [← code_zero]; exact (revalueU_tr_code hS hk 0).symm
  · rw [← code_zero]; exact (revalueW_tr_code hS hk 0).symm
  · rw [hX_TM hS hk, ← code_one, canonical_tr_code hS hk, canonical_code hS hk]
  · rw [← code_one]; exact (revalueU_tr_code hS hk 1).symm
  · rw [← code_one]; exact (revalueW_tr_code hS hk 1).symm

/-! #### The truth equations -/

noncomputable def vals (S : Sys2m) (i i' : ℕ) (k : V) : Fin 13 → V :=
  ![(S.TX i).val (s := stdReadingV V) ![k] Empty.elim, S.uT.val (s := stdReadingV V) ![] Empty.elim,
    S.wT.val (s := stdReadingV V) ![] Empty.elim, (S.TX i').val (s := stdReadingV V) ![k] Empty.elim,
    S.uT.val (s := stdReadingV V) ![] Empty.elim, S.wT.val (s := stdReadingV V) ![] Empty.elim, k,
    (S.TM 0).val (s := stdReadingV V) ![k] Empty.elim, S.uT.val (s := stdReadingV V) ![] Empty.elim,
    S.wT.val (s := stdReadingV V) ![] Empty.elim, (S.TM 1).val (s := stdReadingV V) ![k] Empty.elim,
    S.uT.val (s := stdReadingV V) ![] Empty.elim, S.wT.val (s := stdReadingV V) ![] Empty.elim]

noncomputable def valsT (S : Sys2m) (i i' : ℕ) (k : V) : Fin 13 → V :=
  ![(S.TX i).val (s := stdReadingV V) ![k] Empty.elim, (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim,
    (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim, (S.TX i').val (s := stdReadingV V) ![k] Empty.elim,
    (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim, (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim, k,
    (S.TM 0).val (s := stdReadingV V) ![k] Empty.elim, (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim,
    (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim, (S.TM 1).val (s := stdReadingV V) ![k] Empty.elim,
    (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim, (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma eval_q_iff_vals (S : Sys2m) (g : Semisentence LAct 13) (i i' : ℕ) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (S.q g i i') ↔
      Semiformula.Eval (s := stdReadingV V) (S.vals i i' k) Empty.elim g := by
  unfold q vals; exact eval_qT13_iff _ _ _ _ _ _ _ _ _ _ _ _ _ k

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma eval_swap_q_iff_valsT (S : Sys2m) (g : Semisentence LAct 13) (i i' : ℕ) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap (S.q g i i')) ↔
      Semiformula.Eval (s := stdReadingV V) (S.valsT i i' k) Empty.elim (Semiformula.lMap swap g) := by
  rw [lMap_swap_q]; unfold valsT; exact eval_qT13_iff _ _ _ _ _ _ _ _ _ _ _ _ _ k

lemma vals_me {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (i i' : ℕ) :
    revalue (S.vals i i' k 1) (S.vals i i' k 2) (S.vals i i' k 0) = pBot (S.code i k) := by
  have := descVal_TX hS hk (k := k) i
  rw [descVal_def] at this
  exact this

lemma vals_mem {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (i i' j : ℕ) (hj : j ≤ 1) :
    memVal (S.vals i i' k) j = S.code j k := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · rw [memVal_zero]
    have := descVal_TM hS hk (k := k) 0
    rw [descVal_def] at this
    exact this
  · rw [memVal_one]
    have := descVal_TM hS hk (k := k) 1
    rw [descVal_def] at this
    exact this

lemma valsT_me {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (i i' : ℕ) :
    revalue (S.valsT i i' k 1) (S.valsT i i' k 2) (S.valsT i i' k 0) = pBot (S.tr.code i k) := by
  have := descVal_TX_T hS hk (k := k) i
  rw [descVal_def, lMap_swap_TX] at this
  exact this

lemma valsT_mem {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (i i' j : ℕ) (hj : j ≤ 1) :
    memVal (S.valsT i i' k) j = S.tr.code j k := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · rw [memVal_zero]
    have := descVal_TM_T hS hk (k := k) 0
    rw [descVal_def, lMap_swap_TM] at this
    exact this
  · rw [memVal_one]
    have := descVal_TM_T hS hk (k := k) 1
    rw [descVal_def, lMap_swap_TM] at this
    exact this

/-- **The implication guard** at the pronoun `j'`, in the standard reading, in the frame `(i, i')`. -/
theorem eval_q_impl {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) {j' : ℕ} (hj' : j' ≤ 1) {a a' : PD.Action}
    (i i' : ℕ) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim
        (S.q (template13 (.impl (.plays .self (.bot (.selfIdx j')) a) (.plays (.bot (.selfIdx j')) .self a'))) i i') ↔
      ((∃ n, EvalGraph n (pBot (S.code i k)) (pBot (S.code j' k)) (pBot (S.code i k)) (actCode a : V)) →
        (∃ n, EvalGraph n (pBot (S.code j' k)) (pBot (S.code i k)) (pBot (S.code j' k)) (actCode a' : V))) := by
  rw [eval_q_iff_vals, template13_impl]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
  rw [eval_template13_self_partner j' hj', eval_template13_partner_self j' hj', vals_mem hS hk i i' j' hj',
    vals_me hS hk]

/-- …and in the SWAPPED reading: the same sentence about the transposed system. -/
theorem eval_q_impl_swap {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) {j' : ℕ} (hj' : j' ≤ 1) {a a' : PD.Action}
    (i i' : ℕ) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap
        (S.q (template13 (.impl (.plays .self (.bot (.selfIdx j')) a) (.plays (.bot (.selfIdx j')) .self a'))) i i')) ↔
      ((∃ n, EvalGraph n (pBot (S.tr.code i k)) (pBot (S.tr.code j' k)) (pBot (S.tr.code i k)) (actCode a.swap : V)) →
        (∃ n, EvalGraph n (pBot (S.tr.code j' k)) (pBot (S.tr.code i k)) (pBot (S.tr.code j' k)) (actCode a'.swap : V))) := by
  rw [eval_swap_q_iff_valsT, lMap_swap_template13_impl, lMap_swap_template13_self_partner j' hj',
    lMap_swap_template13_partner_self j' hj']
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
  rw [eval_template13_self_partner j' hj', eval_template13_partner_self j' hj', valsT_mem hS hk i i' j' hj',
    valsT_me hS hk]

/-! #### A simple member in slot `j` -/

/-- Member `j` of the system (`j ∈ {0, 1}`). -/
def mem (S : Sys2m) (j : ℕ) : MT := if j = 0 then S.m₀ else S.m₁

lemma mem_ok {S : Sys2m} (hS : S.Ok) (j : ℕ) : (S.mem j).Ok := by
  unfold mem; split_ifs
  · exact hS.ok₀
  · exact hS.ok₁

lemma tr_mem (S : Sys2m) (j : ℕ) : S.tr.mem j = (S.mem j).tr := by
  unfold mem; split_ifs <;> rfl

lemma listGet_D (S : Sys2m) (j : ℕ) (hj : j ≤ 1) (k : V) : listGet (S.D k) (j : V) = (S.mem j).code k + 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · unfold D; rw [Nat.cast_zero, listGet_cons_zero]; rfl
  · unfold D
    rw [Nat.cast_one]
    conv_lhs => rw [show (1 : V) = 0 + 1 by simp]
    rw [listGet_cons_succ, listGet_cons_zero]; rfl

end Sys2m

/-- **The then-clause of a simple member sitting in a member list**, in every model: a box of the consulted code
makes the bot-wrapped system member play the then-action (fuel `4`). -/
theorem simple_member_then_V (s : SM) (d j k me opp : V) (hget : listGet d j = s.code k + 1)
    (h : LenBox TAct k (guardCodeB (sysCloseTemplate d ((⌜s.g⌝ : ℕ) : V)) me opp k)) :
    EvalGraph 4 me opp (pBot (pSys d j)) (s.a : V) := by
  rw [show (4 : V) = 3 + 1 from three_add_one_eq_four.symm, EvalGraph.bot_iff,
    show (3 : V) = 2 + 1 from two_add_one_eq_three.symm, EvalGraph.sys_iff]
  refine ⟨_, hget, ?_⟩
  unfold SM.code
  rw [sysCloseCode_search, sysCloseCode_const, sysCloseCode_const, show (2 : V) = 1 + 1 from one_add_one_eq_two.symm,
    EvalGraph.search_iff]
  exact Or.inl ⟨h, by rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]⟩

namespace Sys2m

/-- A box of the simple member's guard in the frame `(i, i')` makes it play its then-action there. -/
theorem plays_of_box {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (s : SM) (j : ℕ) (hj : j ≤ 1)
    (hm : (S.mem j).code k = s.code k) (i i' : ℕ) (h : LenBox TAct k (instB (⌜S.q s.g i i'⌝ : V) k)) :
    EvalGraph 4 (pBot (S.code i k)) (pBot (S.code i' k)) (pBot (S.code j k)) (s.a : V) := by
  rw [← guard_eq_instB_of hS hk] at h
  exact simple_member_then_V s (S.D k) j k _ _ (by rw [listGet_D S j hj, hm]) h

/-- …and a box of the swapped guard makes the TRANSPOSED member play its then-action in the transposed frame. -/
theorem tr_plays_of_box {S : Sys2m} (hS : S.Ok) {k : V} (hk : (S.K : V) ≤ k) (s : SM) (j : ℕ) (hj : j ≤ 1)
    (hm : (S.mem j).code k = s.code k) (i i' : ℕ)
    (h : LenBox TAct k (instB (⌜Semiformula.lMap swap (S.q s.g i i')⌝ : V) k)) :
    EvalGraph 4 (pBot (S.tr.code i k)) (pBot (S.tr.code i' k)) (pBot (S.tr.code j k)) (s.tr.a : V) := by
  rw [← tr_guard_eq_instB_of hS hk] at h
  have hmT : (S.tr.mem j).code k = s.tr.code k := by
    rw [tr_mem S j, ← (mem_ok hS j).trc V k, hm, SM.transposeCode_code]
  exact simple_member_then_V s.tr (S.tr.D k) j k _ _ (by rw [listGet_D S.tr j hj, hmT]) h

/-! ### 3. DIMCID's self-fulfilling family, whatever the partner -/

/-- **DIMCID's Löb premise on the member slot `i` of a generic system**: boxes of its guard in the frames `(i, i)`
and `(i, j')` make it defect in both, falsifying the antecedent of both guards, in both readings. -/
theorem loebSound_Di {S : Sys2m} (hS : S.Ok) (s : SM) (i j' : ℕ) (hi : i ≤ 1) (hj' : j' ≤ 1)
    (hm : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (S.mem i).code k = s.code k)
    (hg : s.g = template13 (entDimG j')) (ha : s.a = 1) :
    LoebSound (pQ (S.q s.g i i ⋏ S.q s.g i j')) (14 + S.K) 16 := by
  refine loebSound_pQ₂_above _ _ S.K fun V _ _ k hk b₁ b₂ b₃ b₄ ↦ ?_
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  rw [← stdReadingV_eq_stdReading]
  have hD := plays_of_box hS hk s i hi (hm V k) i j' b₂
  have hDT := tr_plays_of_box hS hk s i hi (hm V k) i j' b₄
  rw [ha, Nat.cast_one] at hD
  rw [SM.tr_a, ha] at hDT
  simp only [Nat.sub_self, Nat.cast_zero] at hDT
  have hA : ¬ ∃ n, EvalGraph n (pBot (S.code i k)) (pBot (S.code j' k)) (pBot (S.code i k)) (actCode .C : V) := by
    rintro ⟨n, hn⟩
    have := EvalGraph.unique_V' n 4 _ _ _ _ _ hn hD
    rw [actCode_C_cast] at this
    exact _root_.zero_ne_one this
  have hAT : ¬ ∃ n, EvalGraph n (pBot (S.tr.code i k)) (pBot (S.tr.code j' k)) (pBot (S.tr.code i k)) (actCode Action.C.swap : V) := by
    rintro ⟨n, hn⟩
    have := EvalGraph.unique_V' n 4 _ _ _ _ _ hn hDT
    rw [show Action.C.swap = .D from rfl, actCode_D_cast] at this
    exact _root_.one_ne_zero this
  rw [hg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (eval_q_impl hS hk hj' i i).mpr fun h ↦ absurd h hA
  · exact (eval_q_impl hS hk hj' i j').mpr fun h ↦ absurd h hA
  · exact (eval_q_impl_swap hS hk hj' i i).mpr fun h ↦ absurd h hAT
  · exact (eval_q_impl_swap hS hk hj' i j').mpr fun h ↦ absurd h hAT

/-- **DIMCID finds its guard in both frames for all large `k`.** -/
theorem found_Di {S : Sys2m} (hS : S.Ok) (s : SM) (i j' : ℕ) (hi : i ≤ 1) (hj' : j' ≤ 1)
    (hm : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (S.mem i).code k = s.code k)
    (hg : s.g = template13 (entDimG j')) (ha : s.a = 1) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → S.K ≤ k ∧
      LenBox TAct k (instB (⌜S.q s.g i i⌝ : ℕ) k) ∧ LenBox TAct k (instB (⌜S.q s.g i j'⌝ : ℕ) k) := by
  obtain ⟨k₀, h⟩ := family_found (pQ (S.q s.g i i ⋏ S.q s.g i j')) boundedInnerNec_sixteen
    (loebSound_Di hS s i j' hi hj' hm hg ha)
  refine ⟨k₀ + S.K, fun k hk ↦ ?_⟩
  obtain ⟨a, ha', hbox⟩ := h k (by omega)
  obtain ⟨b₁, b₂, -, -⟩ := boxes_pQ₂_nat _ _ S.K k a ha' hbox
  exact ⟨by omega, b₁, b₂⟩

/-- A box of `S.q g i i'` at ℕ, read on the consulted code. -/
theorem box_guard_nat {S : Sys2m} (hS : S.Ok) {k : ℕ} (hk : S.K ≤ k) (g : Semisentence LAct 13) (i i' : ℕ)
    (h : LenBox TAct k (instB (⌜S.q g i i'⌝ : ℕ) k)) :
    LenBox TAct k (guardCodeB (sysCloseTemplate (S.D k) (⌜g⌝ : ℕ)) (pBot (S.code i k)) (pBot (S.code i' k)) k) := by
  have e := guard_eq_instB_of (V := ℕ) hS (k := k) (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk))) g i i'
  rw [natCast_nat] at e
  rw [e]; exact h

/-- The play of the simple member at ℕ from a box of its instance. -/
theorem plays_of_box_nat {S : Sys2m} (hS : S.Ok) {k : ℕ} (hk : S.K ≤ k) (s : SM) (j : ℕ) (hj : j ≤ 1)
    (hm : (S.mem j).code k = s.code k) (i i' : ℕ) (h : LenBox TAct k (instB (⌜S.q s.g i i'⌝ : ℕ) k)) :
    EvalGraph 4 (pBot (S.code i k)) (pBot (S.code i' k)) (pBot (S.code j k)) s.a := by
  have := plays_of_box (V := ℕ) hS (k := k) (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk))) s j hj hm i i' h
  rwa [natCast_nat] at this

end Sys2m

end ArithS.Tau
