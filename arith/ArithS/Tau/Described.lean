import ArithS.Tau.Columns
import ArithS.Cells.PositiveCells

/-!
# ArithS.Tau.Described — the instance bits that need the instance's OWN description (Phase 3)

Two of the `coop`/`defect` column bits are POS cells whose guard mentions the SEARCHER ITSELF (`.self`): CIMCIC's
instance at the cooperator (`implC .C .C .C`: "if I cooperate with the frozen cooperator, it cooperates with me")
and DIMCID's instance at the defector (`implC .D .C .D`: "if I cooperate with the frozen defector, it defects
against me"). Both consequents are closed truths about a constant, so the guard is TRUE in every model — but its
sentence names the instance's own code, which carries `k`, so `found_of_tact` gives no budget-uniform bound.
The uniform route is the base `pos_CIMCIC_vs_botCB`'s: the consulted guard is the `binNumeral k`-instance of a
FIXED one-variable formula (`guardCode_qT_eq_instB` with the bot tower `describes_botSV`, which describes
`pBot (SV g a k)` — exactly the instance's frame player), that formula is a `TAct`-theorem by completeness
(`tact_all_of_both`: the consequent holds in both readings), and the instance fits the budget for all large
`k` (`found_of_all`).

* `eval_template_plays_self_closed_V` / `eval_template_plays_closed_self_V` — the two atom shapes of `implC` in
  every model (the twins of `eval_template_plays_opp_closed_V`);
* `qInst g a` — the template `g` filled with the bot tower of `SV g a k` on BOTH sides (the bit's frame is
  `(pBot I, pBot I)`), and `guardCode_botSV_self_eq_instB` — the instance equation at ℕ;
* `tact_qInst_implC` — `TAct ⊢ ∀¹ qInst (template (implC d a' d)) n`;
* `found_implC_self` — found at every large `k`, in the instance's frame;
* the bits `col_cimcic_coop` (C) and `col_dimcid_defect` (D).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD PD.Tau

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The atoms of `implC` in every model -/

/-- **The `.plays .self q a` atom of `template` for a CLOSED `q`, in every model**: "me plays `a` against the
(cast) code of `q`". -/
lemma eval_template_plays_self_closed_V (q : PD.Prog) (hq1 : q ≠ .self) (hq2 : q ≠ .opp) (a : PD.Action)
    (b : Fin 6 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (template (.plays .self q a)) ↔
      ∃ n, EvalGraph n (revalue (b 1) (b 2) (b 0)) ((progCode q : ℕ) : V) (revalue (b 1) (b 2) (b 0)) (actCode a : V) := by
  rw [template_plays]
  unfold progGraph
  rw [progAux_self, progAux_of_ne hq1 hq2]
  unfold descF
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, eval_closedDesc_V,
    stdReadingV_rel_eq, Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, ⟨d, rfl, rfl⟩, rfl, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, ⟨_, rfl, rfl⟩, rfl, h⟩

/-- **The `.plays p .self a` atom of `template` for a CLOSED `p`, in every model**: "the (cast) code of `p` plays
`a` against me". -/
lemma eval_template_plays_closed_self_V (p : PD.Prog) (hp1 : p ≠ .self) (hp2 : p ≠ .opp) (a : PD.Action)
    (b : Fin 6 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (template (.plays p .self a)) ↔
      ∃ n, EvalGraph n ((progCode p : ℕ) : V) (revalue (b 1) (b 2) (b 0)) ((progCode p : ℕ) : V) (actCode a : V) := by
  rw [template_plays]
  unfold progGraph
  rw [progAux_of_ne hp1 hp2, progAux_self]
  unfold descF
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, eval_closedDesc_V,
    stdReadingV_rel_eq, Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, rfl, ⟨d, rfl, rfl⟩, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, rfl, ⟨_, rfl, rfl⟩, h⟩

/-- The cast code of a frozen constant. -/
lemma cast_progCode_botConst (a : PD.Action) : ((progCode (.bot (.const a)) : ℕ) : V) = pBot (pConst (actCode a : V)) := by
  rw [progCode_botConst, cast_pBot, cast_pConst]

/-- **The truth of `template (implC d a' d)` at ANY frame, in every model**: the consequent "the frozen `d` plays
`d` against me" holds (`bot_const_play_V`), whatever the antecedent. -/
theorem eval_template_implC_V (d a' : PD.Action) (b : Fin 6 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (template (implC d a' d)) := by
  show Semiformula.Eval (s := stdReadingV V) b Empty.elim (template (.impl (.plays .self (.bot (.const d)) a') (.plays (.bot (.const d)) .self d)))
  rw [template_impl]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
  intro _
  rw [eval_template_plays_closed_self_V _ (by simp) (by simp), cast_progCode_botConst]
  exact bot_const_play_V _ _ _

/-! ### 2. The fixed formula of an instance's guard in its own frame -/

/-- The template `g` filled with the bot tower of `SV g a k` on BOTH sides: the fixed formula of the guard the
instance `pBot (SV g a k)` consults in the bit's frame `(pBot I, pBot I)`. -/
noncomputable def qInst (g : Semisentence LAct 6) (a : ℕ) : Semisentence LAct 1 :=
  qT g (TBS g a) (uS g a) (wS g a) (TBS g a) (uS g a) (wS g a)

/-- **The instance equation at ℕ**: the guard code of `pBot (SV g a k)` against itself on `g` is the
`binNumeral k`-instance of `⌜qInst g a⌝` (`guardCode_qT_eq_instB` + `describes_botSV`). -/
theorem guardCode_botSV_self_eq_instB (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : ℕ) :
    guardCode (⌜g⌝ : ℕ) (pBot (SV g a k)) (pBot (SV g a k)) = instB (⌜qInst g a⌝ : ℕ) k := by
  have hX := (describes_botSV g a ha).hX ℕ k
  have hU := (describes_botSV g a ha).hU ℕ k
  have hW := (describes_botSV g a ha).hW ℕ k
  rw [descVal_botSV g a ha] at hX hU hW
  exact guardCode_qT_eq_instB g k _ _ _ _ _ _ hX hU hW hX hU hW

/-- The swapped reading of `qInst (template φ) a` is the standard reading of `qInst (template φ.transpose) a`
up to the swapped triples; only the TEMPLATE matters for `implC`'s truth. -/
theorem tact_qInst_implC (d a' : PD.Action) (n : ℕ) :
    TAct ⊢ ∀¹ qInst (template (implC d a' d)) n := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    unfold qInst
    rw [eval_qT_iff]
    exact eval_template_implC_V d a' _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    unfold qInst
    rw [eval_qT_swap, lMap_swap_template _ (by cases d <;> cases a' <;> rfl), eval_qT_iff]
    have ht : (implC d a' d).transpose = implC d.swap a'.swap d.swap := by cases d <;> cases a' <;> rfl
    rw [ht]
    exact eval_template_implC_V d.swap a'.swap _

/-- **Found in the instance's frame for all large `k`**: the guard `implC d a' d` of the instance
`pSearch k (templateCode (implC d a' d)) (pConst n) (pConst (1 - n))`, consulted against itself. -/
theorem found_implC_self (d a' : PD.Action) (n : ℕ) (hn : n = 0 ∨ n = 1) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode (implC d a' d))
        (pBot (pSearch k (templateCode (implC d a' d)) (pConst n) (pConst (1 - n))))
        (pBot (pSearch k (templateCode (implC d a' d)) (pConst n) (pConst (1 - n))))) := by
  have hns : noSelfIdxF (implC d a' d) = true := by cases d <;> cases a' <;> rfl
  refine found_of_all (tact_qInst_implC d a' n) _ fun k ↦ ?_
  rw [templateCode_eq_quote_template _ hns, ← SV_nat]
  exact guardCode_botSV_self_eq_instB _ n hn k

/-! ### 3. The two bits -/

/-- τ(CIMCIC) at the cooperator: its guard "if I cooperate with the frozen cooperator, it cooperates with me"
has a true consequent, is a `TAct`-theorem in `k`, and is found for all large `k` — POS, C. -/
theorem col_cimcic_coop : bitEventually .cimcic .coop .C := by
  obtain ⟨k₀, h⟩ := found_implC_self .C .C 0 (Or.inl rfl)
  refine ⟨k₀, fun k hk ↦ bitPlays_of_eq (instCode_cimcic_coop k) ?_⟩
  exact ⟨_, search_then (implC .C .C .C) (h k hk) (const_play 0 _ _ _)⟩

/-- τ(DIMCID) at the defector: its guard "if I cooperate with the frozen defector, it defects against me" has
a true consequent — POS, D. -/
theorem col_dimcid_defect : bitEventually .dimcid .defect .D := by
  obtain ⟨k₀, h⟩ := found_implC_self .D .C 1 (Or.inr rfl)
  refine ⟨k₀, fun k hk ↦ bitPlays_of_eq (instCode_dimcid_defect k) ?_⟩
  exact ⟨_, search_then (implC .D .C .D) (h k hk) (const_play 0 _ _ _)⟩

/-! ### 4. The FLIP: τ(DIMCID) at the cooperator defects (`dimcid_vs_closed` on the instance)

DIMCID's instance at the cooperator searches for `implC .C .C .D`: "if I cooperate with the frozen cooperator, it
defects against me". The consequent is false, so the guard says "I do not cooperate with the cooperator" — a proof
of it within the budget makes the instance DEFECT, which makes it TRUE: the Löb premise holds (`loebSound_pQ_of` on
the two-guard family `pQ qDiI`), and bounded Löb finds it for all large `k` (`family_found`). The engine proves
`(C, C)` for `DIMCID × CooperateBot` and so reads this bit `C`; in `S'` it is `D`.

The fixed formula `qDiI` is the guard in the PROBE frame `(pBot (SV g 1 k), pBot (pConst 0))` — the frame in
which the antecedent's own search consults it — with the bot tower of the instance in the me-slots and the
`.bot CooperateBot` triple in the opp-slots. The bit's frame `(pBot I, pBot I)` consults the SAME code at ℕ:
the template mentions no `.opp` (`guardOf_implConst_frame`). -/

/-- The template of DIMCID's instance at the cooperator. -/
noncomputable def gDiI : Semisentence LAct 6 := template (implC .C .C .D)

lemma gDiI_swap : Semiformula.lMap swap gDiI = template (implC .D .D .C) := lMap_swap_template _ rfl

/-- The fixed formula: `gDiI` filled with the instance's bot tower (me) and `.bot CooperateBot`'s triple (opp). -/
noncomputable def qDiI : Semisentence LAct 1 :=
  qT gDiI (TBS gDiI 1) (uS gDiI 1) (wS gDiI 1) (cl TB0) (cterm Act.C) (cterm Act.D)

/-- **The instance equation in every model** (probe frame). -/
theorem guardCode_DiI (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V) :
    guardCode (⌜gDiI⌝ : V) (pBot (SV gDiI 1 k)) (pBot (pConst 0)) = instB (⌜qDiI⌝ : V) k := by
  have hX := (describes_botSV gDiI 1 (Or.inr rfl)).hX V k
  have hU := (describes_botSV gDiI 1 (Or.inr rfl)).hU V k
  have hW := (describes_botSV gDiI 1 (Or.inr rfl)).hW V k
  rw [descVal_botSV gDiI 1 (Or.inr rfl)] at hX hU hW
  have hX' := describes_botCB.hX V k
  have hU' := describes_botCB.hU V k
  have hW' := describes_botCB.hW V k
  rw [descVal_botCB] at hX' hU' hW'
  exact guardCode_qT_eq_instB gDiI k _ _ _ _ _ _ hX hU hW hX' hU' hW'

/-- **The transposed instance equation**: the transposed instance against `.bot DefectBot`. -/
theorem guardCode_DiIT (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V) :
    guardCode (⌜Semiformula.lMap swap gDiI⌝ : V) (pBot (SV (Semiformula.lMap swap gDiI) (1 - 1) k)) (pBot (pConst 1)) =
      instB (⌜Semiformula.lMap swap qDiI⌝ : V) k := by
  have hX := (describes_botSV gDiI 1 (Or.inr rfl)).hX V k
  have hU := (describes_botSV gDiI 1 (Or.inr rfl)).hU V k
  have hW := (describes_botSV gDiI 1 (Or.inr rfl)).hW V k
  rw [descVal_botSV gDiI 1 (Or.inr rfl)] at hX hU hW
  have hX' := describes_botCB.hX V k
  have hU' := describes_botCB.hU V k
  have hW' := describes_botCB.hW V k
  rw [descVal_botCB] at hX' hU' hW'
  have := guardCode_qT_swap_eq_instB gDiI k _ _ _ _ _ _ hX hU hW hX' hU' hW'
  rwa [transposeCode_pBot, transposeCode_pBot, transposeCode_SV gDiI 1 (Or.inr rfl), transposeCode_pConst_zero] at this

/-- **The Löb premise**: a box of either guard makes the corresponding instance DEFECT against the frozen
constant, which falsifies the antecedent of that guard — so the guard is true. Both readings. -/
theorem loebSound_pDiI : LoebSound (pQ qDiI) 7 8 := by
  refine loebSound_pQ_of qDiI fun V _ _ k h1 h2 ↦ ?_
  rw [← guardCode_DiI V k] at h1
  rw [← guardCode_DiIT V k] at h2
  have e1 := botSV_then_V gDiI 1 k _ _ h1
  have e2 := botSV_then_V (Semiformula.lMap swap gDiI) (1 - 1) k _ _ h2
  rw [Nat.cast_one] at e1
  rw [show ((1 - 1 : ℕ) : V) = 0 by simp] at e2
  rw [← stdReadingV_eq_stdReading]
  constructor
  · unfold qDiI
    rw [eval_qT_iff]
    show Semiformula.Eval (s := stdReadingV V) _ Empty.elim (template (.impl (.plays .self (.bot (.const .C)) .C) (.plays (.bot (.const .C)) .self .D)))
    rw [template_impl]
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro hA
    exfalso
    rw [eval_template_plays_self_closed_V _ (by simp) (by simp), cast_progCode_botConst] at hA
    simp only [Matrix.cons_val] at hA
    rw [desc_botSV gDiI 1 (Or.inr rfl) k, actCode_C_cast] at hA
    obtain ⟨n, hn⟩ := hA
    exact _root_.zero_ne_one (EvalGraph.unique_V' n 3 _ _ _ _ _ hn e1)
  · unfold qDiI
    rw [lMap_swap_qT, gDiI_swap, eval_qT_iff]
    show Semiformula.Eval (s := stdReadingV V) _ Empty.elim (template (.impl (.plays .self (.bot (.const .D)) .D) (.plays (.bot (.const .D)) .self .C)))
    rw [template_impl]
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro hA
    exfalso
    rw [eval_template_plays_self_closed_V _ (by simp) (by simp), cast_progCode_botConst] at hA
    simp only [Matrix.cons_val] at hA
    rw [descT_botSV gDiI 1 (Or.inr rfl) k, gDiI_swap, actCode_D_cast] at hA
    rw [gDiI_swap] at e2
    obtain ⟨n, hn⟩ := hA
    exact _root_.one_ne_zero (EvalGraph.unique_V' n 3 _ _ _ _ _ hn e2)

/-- **The guard of DIMCID's instance at the cooperator is FOUND for all large `k`, in the bit's own frame.** -/
theorem dimcid_coop_found :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode (implC .C .C .D)) (pBot (instCode k .dimcid .coop)) (pBot (instCode k .dimcid .coop))) := by
  obtain ⟨k₀, hf⟩ := family_found (pQ qDiI) boundedInnerNec_sixteen loebSound_pDiI
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := hf k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pQ (V := ℕ) qDiI k) ha)
  have h1 := (pQ_both_V (V := ℕ) qDiI k a ha' hpc).1
  rw [← guardCode_DiI ℕ k] at h1
  -- the probe frame's guard is the bit frame's guard (no `.opp` in the template)
  have hfr := guardOf_implConst_frame (me := .bot (inst (tauZoo k) .dimcid .coop)) (opp := .bot (inst (tauZoo k) .dimcid .coop))
    (opp' := .bot (.const .C)) (properPlayer_bot _) (properPlayer_bot _) (properPlayer_bot _)
    (by show noSelfIdxP (.bot (.search k (implC .C .C .D) (.const .D) (.const .C))) = true; rfl)
    (by show noSelfIdxP (.bot (.search k (implC .C .C .D) (.const .D) (.const .C))) = true; rfl) rfl .C .C .D
  unfold guardOf at hfr
  rw [progCode_bot_inst, progCode_botConst, instCode_dimcid_coop, templateCode_eq_quote_template _ rfl] at hfr
  simp only [actCode_C] at hfr
  rw [instCode_dimcid_coop, templateCode_eq_quote_template _ rfl, hfr]
  have hSV : SV gDiI 1 k = pSearch k (⌜template (implC .C .C .D)⌝ : ℕ) (pConst 1) (pConst 0) := by
    rw [SV_nat]; rfl
  rw [hSV] at h1
  exact h1

/-- **τ(DIMCID) at the cooperator: D — the `S'` FLIP of the engine's C.** -/
theorem col_dimcid_coop : bitEventually .dimcid .coop .D := by
  obtain ⟨k₀, h⟩ := dimcid_coop_found
  refine ⟨k₀, fun k hk ↦ bitPlays_of_eq (instCode_dimcid_coop k) ?_⟩
  have := h k hk
  rw [instCode_dimcid_coop] at this
  exact ⟨_, search_then (implC .C .C .D) this (const_play 0 _ _ _)⟩

end ArithS.Tau
