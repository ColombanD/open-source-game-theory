import ArithS.Cells.SearchFree
import ArithS.Det
import ArithS.InstanceV
import ArithS.NumeralFacts
import ArithS.Diag
import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.CupodTrollBot

/-!
# ArithS.Cells.SoundnessCells — the SND and POS classes of the census in PA-`S'` (draft)
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open PD.Bots

/-! ### 1. The general SND lemma -/

/-- **SND**: a guard whose realization is FALSE in `ℕ` is never found, at ANY budget (`TAct` is
sound in `ℕ`, `models_trAt_of_lenProvableV`). -/
theorem snd_else_of_false {φ : PD.Formula} {me opp : PD.Prog} {k : ℕ}
    (h : ¬ ℕ↓[LAct] ⊧ trAt me opp φ) : ¬ LenProvableV TAct k (guardOf φ me opp) :=
  fun hl ↦ h (models_trAt_of_lenProvableV hl)

/-- The realization of a fragment guard in a proper frame is the realization of its CLOSED
instantiation in any frame (`tmpl_subst` + the closed description terms are fixed by every
rewriter). -/
theorem trAt_subst (me' opp' : PD.Prog) {me opp : PD.Prog} (hme : Proper me) (hopp : Proper opp)
    (φ : PD.Formula) (hφ : fragF φ = true) :
    trAt me' opp' (φ.subst me opp) = trAt me opp φ := by
  unfold trAt
  rw [tmpl_subst hme hopp φ hφ]
  have hv : (fun i ↦ Rew.subst (descTerms (pcode me') (pcode opp')) (descTerms6 me opp i)) =
      descTerms (pcode me) (pcode opp) := by
    funext i
    unfold descTerms6
    rw [rew_cl, cl_zero]
  unfold Rewriting.subst
  rw [← TransitiveRewriting.comp_app, comp_subst_eq, hv]

/-- The realization of a negated guard is the negation of the realization. -/
theorem trAt_neg (me opp : PD.Prog) (φ : PD.Formula) :
    trAt me opp (.neg φ) = ∼ trAt me opp φ := by
  unfold trAt
  rw [tmpl_neg]
  unfold Rewriting.subst
  rw [LogicalConnective.HomClass.map_neg]

theorem trAt_impl (me opp : PD.Prog) (φ ψ : PD.Formula) :
    trAt me opp (.impl φ ψ) = trAt me opp φ 🡒 trAt me opp ψ := by
  unfold trAt
  rw [tmpl_impl]
  unfold Rewriting.subst
  rw [LogicalConnective.HomClass.map_imply]

theorem models_trAt_neg (me opp : PD.Prog) (φ : PD.Formula) :
    ℕ↓[LAct] ⊧ trAt me opp (.neg φ) ↔ ¬ ℕ↓[LAct] ⊧ trAt me opp φ := by
  rw [trAt_neg, Semantics.Not.models_not]

theorem models_trAt_impl (me opp : PD.Prog) (φ ψ : PD.Formula) :
    ℕ↓[LAct] ⊧ trAt me opp (.impl φ ψ) ↔ (ℕ↓[LAct] ⊧ trAt me opp φ → ℕ↓[LAct] ⊧ trAt me opp ψ) := by
  rw [trAt_impl, Semantics.Imp.models_imply]

/-- **The truth equation of the `.eq` atom**: for a proper probe `P`, "`P` is `Q`" holds in `ℕ` iff
the codes coincide. -/
theorem models_trAt_eq (me' opp' P Q : PD.Prog) (hP : Proper P) :
    ℕ↓[LAct] ⊧ trAt me' opp' (.eq P Q) ↔ pcode P = pcode Q := by
  rw [models_iff]
  unfold trAt Semiformula.Realize
  rw [tmpl_eq]
  unfold progGraph
  rw [progAux_of_ne hP.1 hP.2]
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, eval_closedDesc, Semiformula.eval_rel, stdAct_rel_eq, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_one, Semiterm.val_bvar]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, _, rfl, rfl, h⟩

/-! ### 2. The guard shapes: "not found" from the arithmetized sub-play -/

section shapes

lemma proper_bot (p : PD.Prog) : Proper (.bot p) := ⟨by simp, by simp⟩

/-- **`.plays .opp .self a` is not found** when `opp` plays `b ≠ a` against `me`. -/
theorem not_found_opp_self {me opp : PD.Prog} (hme : Proper me) (hopp : Proper opp) (a : PD.Action)
    {b : PD.Action} (hab : b ≠ a) {N : ℕ} (h : EvalGraph N (pcode opp) (pcode me) (pcode opp) (actCode b))
    (k : ℕ) : ¬ LenProvableV TAct k (guardCode (tcode (.plays .opp .self a)) (pcode me) (pcode opp)) := by
  apply snd_else_of_false (φ := .plays .opp .self a)
  rw [← trAt_subst me opp hme hopp _ rfl]
  show ¬ ℕ↓[LAct] ⊧ trAt me opp (.plays opp me a)
  rw [models_trAt_plays me opp opp me a hopp hme]
  rintro ⟨N', h'⟩
  exact hab (actCode_inj (EvalGraph.unique' h h'))

/-- **`.plays .opp (.bot P) a` is not found** when `opp` plays `b ≠ a` against the frozen `.bot P`. -/
theorem not_found_opp_bot {me opp : PD.Prog} (hme : Proper me) (hopp : Proper opp) {P : PD.Prog}
    (hfP : fragP P = true) (a : PD.Action) {b : PD.Action} (hab : b ≠ a) {N : ℕ}
    (h : EvalGraph N (pcode opp) (pBot (pcode P)) (pcode opp) (actCode b))
    (k : ℕ) : ¬ LenProvableV TAct k (guardCode (tcode (.plays .opp (.bot P) a)) (pcode me) (pcode opp)) := by
  apply snd_else_of_false (φ := .plays .opp (.bot P) a)
  rw [← trAt_subst me opp hme hopp _ (by simp [fragF, fragP, atomicP, closedP, hfP])]
  show ¬ ℕ↓[LAct] ⊧ trAt me opp (.plays opp (.bot P) a)
  rw [models_trAt_plays me opp opp (.bot P) a hopp (proper_bot P), pcode_bot]
  rintro ⟨N', h'⟩
  exact hab (actCode_inj (EvalGraph.unique' h h'))

/-- **`.neg (.plays .opp .self a)` is not found** when `opp` DOES play `a` against `me`. -/
theorem not_found_neg_opp_self {me opp : PD.Prog} (hme : Proper me) (hopp : Proper opp) (a : PD.Action)
    {N : ℕ} (h : EvalGraph N (pcode opp) (pcode me) (pcode opp) (actCode a))
    (k : ℕ) : ¬ LenProvableV TAct k (guardCode (tcode (.neg (.plays .opp .self a))) (pcode me) (pcode opp)) := by
  apply snd_else_of_false (φ := .neg (.plays .opp .self a))
  rw [← trAt_subst me opp hme hopp _ rfl]
  show ¬ ℕ↓[LAct] ⊧ trAt me opp (.neg (.plays opp me a))
  rw [models_trAt_neg, models_trAt_plays me opp opp me a hopp hme, not_not]
  exact ⟨N, h⟩

/-- **`.eq .opp Q` is not found** when the opponent's code is not `Q`'s. -/
theorem not_found_eq_opp {me opp : PD.Prog} (hme : Proper me) (hopp : Proper opp) {Q : PD.Prog}
    (hfQ : fragP Q = true) (hne : pcode opp ≠ pcode Q) (k : ℕ) :
    ¬ LenProvableV TAct k (guardCode (tcode (.eq .opp Q)) (pcode me) (pcode opp)) := by
  apply snd_else_of_false (φ := .eq .opp Q)
  rw [← trAt_subst me opp hme hopp _ (by simp [fragF, fragP, atomicP, hfQ])]
  show ¬ ℕ↓[LAct] ⊧ trAt me opp (.eq opp Q)
  rw [models_trAt_eq me opp opp Q hopp]
  exact hne

end shapes

/-! ### 3. The "found" lemmas: closed atoms, fixed sentences -/

section found

/-- A `TAct`-theorem is found at every budget above its proof length. -/
theorem found_of_tact {φ : PD.Formula} {me opp : PD.Prog} (h : TAct ⊢ trAt me opp φ) :
    ∃ L : ℕ, ∀ k : ℕ, L ≤ k → LenProvableV TAct k (guardCode (tcode φ) (pcode me) (pcode opp)) := by
  obtain ⟨N, hN⟩ := lenProvable_of_provable h
  refine ⟨N, fun k hk ↦ ?_⟩
  rw [← guardOf, guardOf_eq_quote_trAt, lenProvableV_nat]
  exact lenProvable_fbound_mono hk hN

/-- τ on the realized sentence (fragment frame and formula). -/
theorem lMap_swap_trAt {me opp : PD.Prog} (hme : fragP me = true) (hopp : fragP opp = true)
    (φ : PD.Formula) (hφ : fragF φ = true) :
    Semiformula.lMap swap (trAt me opp φ) = trAt me.transpose opp.transpose φ.transpose := by
  unfold trAt
  rw [Semiformula.lMap_subst, lMap_swap_tmpl φ hφ]
  congr 1
  funext i
  fin_cases i <;> simp [descTerms, lMap_swap_dnumT, lMap_swap_dUT, lMap_swap_dWT, swapcode_pcode me hme,
    swapcode_pcode opp hopp]

/-- **`TAct` proves a true closed atom** about search-free proper players: the standard reading by
Σ₁-completeness of PA at ℕ (`pa_proves_trAt_of_evalGraph`), the swapped reading by the same on the
TRANSPOSED play; completeness (`tact_complete'`) closes. -/
theorem tact_proves_plays_closed {X Y : PD.Prog} (hX : SearchFreePlayer X) (hY : SearchFreePlayer Y)
    (hXc : closedP X = true) (hYc : closedP Y = true) (a : PD.Action) {N : ℕ} (h : EvalGraph N (pcode X) (pcode Y) (pcode X) (actCode a)) {N' : ℕ}
    (hτ : EvalGraph N' (pcode X.transpose) (pcode Y.transpose) (pcode X.transpose) (actCode a.swap))
    (hXτ : Proper X.transpose) (hYτ : Proper Y.transpose) :
    TAct ⊢ trAt X Y (.plays X Y a) := by
  refine tact_complete' _ fun M _ _ ↦ ?_
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  constructor
  · have hpa := pa_proves_trAt_of_evalGraph X Y h hX.1 hY.1
    have hM : M↓[ℒₒᵣ] ⊧ Semiformula.lMap inst (trAt X Y (.plays X Y a)) := models_of_provable inferInstance hpa
    rw [models_inst_V, stdActV_eq_stdActS] at hM
    exact hM
  · have hpa := pa_proves_trAt_of_evalGraph X.transpose Y.transpose hτ hXτ hYτ
    have hM : M↓[ℒₒᵣ] ⊧ Semiformula.lMap inst (trAt X.transpose Y.transpose (.plays X.transpose Y.transpose a.swap)) :=
      models_of_provable inferInstance hpa
    rw [models_inst_V, stdActV_eq_stdActS] at hM
    refine (Semiformula.eval_lMap (s₂ := stdActS M) (Φ := swap)).mp ?_
    rw [lMap_swap_trAt (fragP_of_modestP X hX.2.1) (fragP_of_modestP Y hY.2.1) _
      (by simp [fragF, atomicP, hXc, hYc, fragP_of_modestP X hX.2.1, fragP_of_modestP Y hY.2.1])]
    exact hM

end found

/-! ### 4. The zoo codes -/

section codes

/-- Guardian's guard. -/
def phiG : PD.Formula := .plays .opp (.bot CooperateBot) .D
/-- Cupod's guard. -/
def phiCu : PD.Formula := .plays .opp .self .D
/-- Dupoc's guard. -/
def phiDu : PD.Formula := .plays .opp .self .C
/-- CupodTroll's guard. -/
def phiT (k : ℕ) : PD.Formula := .eq .opp (CupodBot k)
/-- Wary's guard. -/
def phiW : PD.Formula := .neg (.plays .opp .self .C)
/-- Just's guard. -/
def phiJ (k : ℕ) : PD.Formula := .plays .opp (.bot (DupocBot k)) .C
/-- Prudent's outer guard. -/
def phiP1 : PD.Formula := .plays .opp .self .C
/-- Prudent's inner (prudence) guard. -/
def phiP2 : PD.Formula := .plays .opp (.bot DefectBot) .D

lemma pcode_GuardianBot (k : ℕ) :
    pcode (GuardianBot k) = pSearch k (tcode phiG) (pConst 1) (pConst 0) := by
  simp [GuardianBot, phiG, actCode]
lemma pcode_CupodBot (k : ℕ) :
    pcode (CupodBot k) = pSearch k (tcode phiCu) (pConst 1) (pConst 0) := by
  simp [CupodBot, phiCu, actCode]
lemma pcode_DupocBot' (k : ℕ) :
    pcode (DupocBot k) = pSearch k (tcode phiDu) (pConst 0) (pConst 1) := by
  simp [DupocBot, phiDu, actCode]
lemma pcode_CupodTrollBot (k : ℕ) :
    pcode (CupodTrollBot k) = pSearch k (tcode (phiT k)) (pConst 1) (pConst 0) := by
  simp [CupodTrollBot, phiT, actCode]
lemma pcode_WaryBot (k : ℕ) :
    pcode (WaryBot k) = pSearch k (tcode phiW) (pConst 1) (pConst 0) := by
  simp [WaryBot, phiW, actCode]
lemma pcode_JustBot (k : ℕ) :
    pcode (JustBot k) = pSearch k (tcode (phiJ k)) (pConst 0) (pConst 1) := by
  simp [JustBot, phiJ, actCode]
lemma pcode_PrudentBot' (k : ℕ) :
    pcode (PrudentBot k) =
      pSearch k (tcode phiP1) (pSearch k (tcode phiP2) (pConst 0) (pConst 1)) (pConst 1) := by
  simp [PrudentBot, phiP1, phiP2, actCode]

lemma pcode_botCB : pcode (PD.Prog.bot CooperateBot) = pBot (pConst 0) := by simp [CooperateBot, actCode]
lemma pcode_botDB : pcode (PD.Prog.bot DefectBot) = pBot (pConst 1) := by simp [DefectBot, actCode]
lemma pcode_CB : pcode CooperateBot = pConst 0 := by simp [CooperateBot, actCode]
lemma pcode_DB : pcode DefectBot = pConst 1 := by simp [DefectBot, actCode]

lemma proper_GuardianBot (k : ℕ) : Proper (GuardianBot k) := ⟨by simp [GuardianBot], by simp [GuardianBot]⟩
lemma proper_CupodBot (k : ℕ) : Proper (CupodBot k) := ⟨by simp [CupodBot], by simp [CupodBot]⟩
lemma proper_CupodTrollBot (k : ℕ) : Proper (CupodTrollBot k) :=
  ⟨by simp [CupodTrollBot], by simp [CupodTrollBot]⟩
lemma proper_WaryBot (k : ℕ) : Proper (WaryBot k) := ⟨by simp [WaryBot], by simp [WaryBot]⟩
lemma proper_JustBot (k : ℕ) : Proper (JustBot k) := ⟨by simp [JustBot], by simp [JustBot]⟩
lemma proper_PrudentBot (k : ℕ) : Proper (PrudentBot k) := ⟨by simp [PrudentBot], by simp [PrudentBot]⟩
lemma proper_botCB : Proper (PD.Prog.bot CooperateBot) := proper_bot _
lemma proper_botDB : Proper (PD.Prog.bot DefectBot) := proper_bot _

end codes

/-! ### 5. The search clause on engine codes, and the search-free probers -/

section steps

/-- The else branch of a search node on an engine template. -/
theorem search_else {k n a x y : ℕ} (φ : PD.Formula) {p q : ℕ}
    (hn : ¬ LenProvableV TAct k (guardCode (tcode φ) x y)) (h : EvalGraph n x y q a) :
    EvalGraph (n + 1) x y (pSearch k (tcode φ) p q) a :=
  (EvalGraph.search_iff₆ (isSemiformula_tcode φ)).mpr (Or.inr ⟨hn, h⟩)

/-- The then branch of a search node on an engine template. -/
theorem search_then {k n a x y : ℕ} (φ : PD.Formula) {p q : ℕ}
    (hy : LenProvableV TAct k (guardCode (tcode φ) x y)) (h : EvalGraph n x y p a) :
    EvalGraph (n + 1) x y (pSearch k (tcode φ) p q) a :=
  (EvalGraph.search_iff₆ (isSemiformula_tcode φ)).mpr (Or.inl ⟨hy, h⟩)

/-- A search node whose two branches AGREE plays that value whatever the verdict. -/
theorem search_either {k n a x y : ℕ} (φ : PD.Formula) {p q : ℕ}
    (hp : EvalGraph n x y p a) (hq : EvalGraph n x y q a) :
    EvalGraph (n + 1) x y (pSearch k (tcode φ) p q) a := by
  by_cases hg : LenProvableV TAct k (guardCode (tcode φ) x y)
  · exact search_then φ hg hp
  · exact search_else φ hg hq

lemma bot_const_play (n me opp a : ℕ) : EvalGraph (n + 1 + 1) me opp (pBot (pConst a)) a :=
  EvalGraph.bot_iff.mpr (EvalGraph.const_iff.mpr rfl)

lemma const_play (n me opp a : ℕ) : EvalGraph (n + 1) me opp (pConst a) a := EvalGraph.const_iff.mpr rfl

/-- `MirrorBot` copies the opponent's play against it. -/
theorem mirror_copies {x a n : ℕ} (h : EvalGraph n x (pcode MirrorBot) x a) :
    EvalGraph (n + 1) (pcode MirrorBot) x (pcode MirrorBot) a := by
  rw [pcode_MirrorBot, Mirror, EvalGraph.sim_iff, psubst_opp, psubst_self]
  exact h

/-- `DBot` defects against `x` when `x` cooperates with `.bot DefectBot`. -/
theorem dbot_D_of_probe_C {x n : ℕ} (h : EvalGraph n x (pBot (pConst 1)) x 0) :
    EvalGraph (n + 1 + 1) (pcode DBot) x (pcode DBot) 1 := by
  simp only [DBot, DefectBot, pcode_ite, pcode_sim, pcode_opp, pcode_bot, pcode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨0, ?_, Or.inl ⟨rfl, const_play _ _ _ _⟩⟩
  rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
  exact h

/-- `DBot` cooperates with `x` when `x` defects against `.bot DefectBot`. -/
theorem dbot_C_of_probe_D {x n : ℕ} (h : EvalGraph n x (pBot (pConst 1)) x 1) :
    EvalGraph (n + 1 + 1) (pcode DBot) x (pcode DBot) 0 := by
  simp only [DBot, DefectBot, pcode_ite, pcode_sim, pcode_opp, pcode_bot, pcode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨1, ?_, Or.inr ⟨by decide, const_play _ _ _ _⟩⟩
  rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
  exact h

/-- `TitForTatBot` cooperates with `x` when `x` cooperates with `.bot CooperateBot`. -/
theorem tft_C_of_probe_C {x n : ℕ} (h : EvalGraph n x (pBot (pConst 0)) x 0) :
    EvalGraph (n + 1 + 1) (pcode TitForTatBot) x (pcode TitForTatBot) 0 := by
  simp only [TitForTatBot, CooperateBot, pcode_ite, pcode_sim, pcode_opp, pcode_bot, pcode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨0, ?_, Or.inl ⟨rfl, const_play _ _ _ _⟩⟩
  rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
  exact h

/-- `TitForTatBot` defects against `x` when `x` defects against `.bot CooperateBot`. -/
theorem tft_D_of_probe_D {x n : ℕ} (h : EvalGraph n x (pBot (pConst 0)) x 1) :
    EvalGraph (n + 1 + 1) (pcode TitForTatBot) x (pcode TitForTatBot) 1 := by
  simp only [TitForTatBot, CooperateBot, pcode_ite, pcode_sim, pcode_opp, pcode_bot, pcode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨1, ?_, Or.inr ⟨by decide, const_play _ _ _ _⟩⟩
  rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
  exact h

/-- `OBot` defects against `x` when `x` does not cooperate with `.bot CooperateBot`. -/
theorem obot_D_of_probe1_D {x n r : ℕ} (h : EvalGraph n x (pBot (pConst 0)) x r) (hr : r ≠ 0) :
    EvalGraph (n + 1 + 1) (pcode OBot) x (pcode OBot) 1 := by
  simp only [OBot, CooperateBot, DefectBot, pcode_ite, pcode_sim, pcode_opp, pcode_bot, pcode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨r, ?_, Or.inr ⟨hr, const_play _ _ _ _⟩⟩
  rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
  exact h


/-- `OBot` cooperates with `x` when `x` cooperates with both `.bot CooperateBot` and `.bot DefectBot`. -/
theorem obot_C_of_probes {x n : ℕ} (h1 : EvalGraph n x (pBot (pConst 0)) x 0)
    (h2 : EvalGraph n x (pBot (pConst 1)) x 0) :
    EvalGraph (n + 1 + 1 + 1) (pcode OBot) x (pcode OBot) 0 := by
  simp only [OBot, CooperateBot, DefectBot, pcode_ite, pcode_sim, pcode_opp, pcode_bot, pcode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨0, ?_, Or.inl ⟨rfl, ?_⟩⟩
  · rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
    exact EvalGraph.mono _ _ _ _ _ h1
  · rw [EvalGraph.ite_iff]
    refine ⟨0, ?_, Or.inl ⟨rfl, const_play _ _ _ _⟩⟩
    rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
    exact h2

/-- `OBot` defects against `x` when `x` cooperates with `.bot CooperateBot` but defects against
`.bot DefectBot`. -/
theorem obot_D_of_probes {x n : ℕ} (h1 : EvalGraph n x (pBot (pConst 0)) x 0)
    (h2 : EvalGraph n x (pBot (pConst 1)) x 1) :
    EvalGraph (n + 1 + 1 + 1) (pcode OBot) x (pcode OBot) 1 := by
  simp only [OBot, CooperateBot, DefectBot, pcode_ite, pcode_sim, pcode_opp, pcode_bot, pcode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨0, ?_, Or.inl ⟨rfl, ?_⟩⟩
  · rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
    exact EvalGraph.mono _ _ _ _ _ h1
  · rw [EvalGraph.ite_iff]
    refine ⟨1, ?_, Or.inr ⟨by decide, const_play _ _ _ _⟩⟩
    rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
    exact h2

/-- `OBot` defects against `x` whenever `x` defects against `.bot DefectBot`, whatever `x` does
against `.bot CooperateBot` (as long as it plays). -/
theorem obot_D_of_any {x n r : ℕ} (h1 : EvalGraph n x (pBot (pConst 0)) x r)
    (h2 : EvalGraph n x (pBot (pConst 1)) x 1) :
    EvalGraph (n + 1 + 1 + 1) (pcode OBot) x (pcode OBot) 1 := by
  by_cases hr : r = 0
  · subst hr; exact obot_D_of_probes h1 h2
  · exact EvalGraph.mono _ _ _ _ _ (obot_D_of_probe1_D h1 hr)

/-- `EBot` defects against `x` when `x` cooperates with `.bot DefectBot`. -/
theorem ebot_D_of_probe1_C {x n : ℕ} (h : EvalGraph n x (pBot (pConst 1)) x 0) :
    EvalGraph (n + 1 + 1) (pcode EBot) x (pcode EBot) 1 := by
  simp only [EBot, CooperateBot, DefectBot, MirrorBot, pcode_ite, pcode_sim, pcode_opp, pcode_self, pcode_bot,
    pcode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨0, ?_, Or.inl ⟨rfl, const_play _ _ _ _⟩⟩
  rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
  exact h

/-- `EBot` cooperates with `x` when `x` defects against `.bot DefectBot` and cooperates with
`.bot CooperateBot`. -/
theorem ebot_C_of_probes {x n : ℕ} (h1 : EvalGraph n x (pBot (pConst 1)) x 1)
    (h2 : EvalGraph n x (pBot (pConst 0)) x 0) :
    EvalGraph (n + 1 + 1 + 1) (pcode EBot) x (pcode EBot) 0 := by
  simp only [EBot, CooperateBot, DefectBot, MirrorBot, pcode_ite, pcode_sim, pcode_opp, pcode_self, pcode_bot,
    pcode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨1, ?_, Or.inr ⟨by decide, ?_⟩⟩
  · rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
    exact EvalGraph.mono _ _ _ _ _ h1
  · rw [EvalGraph.ite_iff]
    refine ⟨0, ?_, Or.inl ⟨rfl, const_play _ _ _ _⟩⟩
    rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
    exact h2

end steps

/-! ### 6. Code disjointness (for the `.eq` guard of CupodTrollBot) -/

section disjoint

lemma pConst_ne_pSearch (a k g p q : ℕ) : pConst a ≠ pSearch k g p q := by
  simp [pConst, pSearch]
lemma pBot_ne_pSearch (x k g p q : ℕ) : pBot x ≠ pSearch k g p q := by
  simp [pBot, pSearch]
lemma pSim_ne_pSearch (x y k g p q : ℕ) : pSim x y ≠ pSearch k g p q := by
  simp [pSim, pSearch]
lemma pIte_ne_pSearch (b a x y k g p q : ℕ) : pIte b a x y ≠ pSearch k g p q := by
  simp [pIte, pSearch]

/-- Two templates with different formulas have different codes (quote injectivity at ℕ). -/
lemma tcode_ne_of_ne {φ ψ : PD.Formula} (h : tmpl φ ≠ tmpl ψ) : tcode φ ≠ tcode ψ := by
  unfold tcode
  intro e
  exact h ((Sentence.quote_inj_iff (V := ℕ)).mp e)

/-- **Semantic disjointness of templates**: two guards whose realizations differ in truth at ONE
frame have different template codes (equal codes give equal realized sentences, `quote_trAt` +
quote injectivity). -/
lemma tcode_ne_of_models {φ ψ : PD.Formula} (me opp : PD.Prog) (h1 : ℕ↓[LAct] ⊧ trAt me opp φ)
    (h2 : ¬ ℕ↓[LAct] ⊧ trAt me opp ψ) : tcode φ ≠ tcode ψ := by
  intro e
  apply h2
  have hq : (⌜trAt me opp φ⌝ : ℕ) = ⌜trAt me opp ψ⌝ := by rw [quote_trAt, quote_trAt, e]
  rw [← (Sentence.quote_inj_iff (V := ℕ)).mp hq]
  exact h1

end disjoint

/-! ### 7. The searchers' plays from a verdict on their guard -/

section searchers

/-- Guardian cooperates with an opponent that cooperates with `.bot CooperateBot`. -/
theorem guardian_C_of_probe (k : ℕ) {opp : PD.Prog} (hopp : Proper opp) {N : ℕ}
    (h : EvalGraph N (pcode opp) (pBot (pConst 0)) (pcode opp) 0) :
    EvalGraph 2 (pcode (GuardianBot k)) (pcode opp) (pcode (GuardianBot k)) 0 := by
  have hn := not_found_opp_bot (proper_GuardianBot k) hopp (P := CooperateBot) rfl .D (b := .C) (by decide)
    (by rw [pcode_CB]; exact h) k
  rw [pcode_GuardianBot] at hn ⊢
  exact search_else phiG hn (const_play _ _ _ _)

/-- Guardian defects against an opponent when it FINDS its guard. -/
theorem guardian_D_of_found (k : ℕ) {opp : PD.Prog}
    (hy : LenProvableV TAct k (guardCode (tcode phiG) (pcode (GuardianBot k)) (pcode opp))) :
    EvalGraph 2 (pcode (GuardianBot k)) (pcode opp) (pcode (GuardianBot k)) 1 := by
  rw [pcode_GuardianBot] at hy ⊢
  exact search_then phiG hy (const_play _ _ _ _)

/-- Guardian cooperates with `.bot CooperateBot`. -/
theorem guardian_vs_botCB (k : ℕ) :
    EvalGraph 2 (pcode (GuardianBot k)) (pBot (pConst 0)) (pcode (GuardianBot k)) 0 := by
  have := guardian_C_of_probe k (opp := .bot CooperateBot) proper_botCB (N := 2)
    (by rw [pcode_botCB]; exact bot_const_play 0 _ _ _)
  rwa [pcode_botCB] at this

/-- Cupod cooperates with an opponent that cooperates with it. -/
theorem cupod_C_of_probe (k : ℕ) {opp : PD.Prog} (hopp : Proper opp) {N : ℕ}
    (h : EvalGraph N (pcode opp) (pcode (CupodBot k)) (pcode opp) 0) :
    EvalGraph 2 (pcode (CupodBot k)) (pcode opp) (pcode (CupodBot k)) 0 := by
  have hn := not_found_opp_self (proper_CupodBot k) hopp .D (b := .C) (by decide) h k
  rw [pcode_CupodBot] at hn ⊢
  exact search_else phiCu hn (const_play _ _ _ _)

/-- Cupod cooperates with `CooperateBot`. -/
theorem snd_CupodBot_vs_CooperateBot_aux (k : ℕ) :
    EvalGraph 2 (pcode (CupodBot k)) (pcode CooperateBot) (pcode (CupodBot k)) 0 :=
  cupod_C_of_probe k sfp_CooperateBot.1 (by rw [pcode_CB]; exact const_play 0 _ _ 0)

/-- Cupod cooperates with `.bot CooperateBot`. -/
theorem cupod_vs_botCB (k : ℕ) :
    EvalGraph 2 (pcode (CupodBot k)) (pBot (pConst 0)) (pcode (CupodBot k)) 0 := by
  have := cupod_C_of_probe k (opp := .bot CooperateBot) proper_botCB (N := 2)
    (by rw [pcode_botCB]; exact bot_const_play 0 _ _ _)
  rwa [pcode_botCB] at this

/-- Dupoc defects against an opponent that defects against it. -/
theorem dupoc_D_of_probe (k : ℕ) {opp : PD.Prog} (hopp : Proper opp) {N : ℕ}
    (h : EvalGraph N (pcode opp) (pcode (DupocBot k)) (pcode opp) 1) :
    EvalGraph 2 (pcode (DupocBot k)) (pcode opp) (pcode (DupocBot k)) 1 := by
  have hn := not_found_opp_self (proper_DupocBot k) hopp .C (b := .D) (by decide) h k
  rw [pcode_DupocBot'] at hn ⊢
  exact search_else phiDu hn (const_play _ _ _ _)

/-- Dupoc's BODY, in any proper frame whose opponent defects against the frame's `me`, defects
(for the frozen snapshot `.bot (DupocBot k)` of JustBot's guard). -/
theorem dupoc_body_D_of_probe (k : ℕ) {me opp : PD.Prog} (hme : Proper me) (hopp : Proper opp) {N : ℕ}
    (h : EvalGraph N (pcode opp) (pcode me) (pcode opp) 1) :
    EvalGraph 2 (pcode me) (pcode opp) (pcode (DupocBot k)) 1 := by
  have hn := not_found_opp_self hme hopp .C (b := .D) (by decide) h k
  rw [pcode_DupocBot']
  exact search_else phiDu hn (const_play _ _ _ _)

/-- Dupoc's body always plays in a proper frame (fuel 2), whatever the verdict. -/
theorem dupoc_body_total (k : ℕ) (me opp : PD.Prog) :
    ∃ r, EvalGraph 2 (pcode me) (pcode opp) (pcode (DupocBot k)) r := by
  rw [pcode_DupocBot']
  by_cases hg : LenProvableV TAct k (guardCode (tcode phiDu) (pcode me) (pcode opp))
  · exact ⟨0, search_then phiDu hg (const_play _ _ _ _)⟩
  · exact ⟨1, search_else phiDu hg (const_play _ _ _ _)⟩

/-- Dupoc defects against `.bot DefectBot`. -/
theorem dupoc_vs_botDB (k : ℕ) :
    EvalGraph 2 (pcode (DupocBot k)) (pBot (pConst 1)) (pcode (DupocBot k)) 1 := by
  have := dupoc_D_of_probe k (opp := .bot DefectBot) proper_botDB (N := 2)
    (by rw [pcode_botDB]; exact bot_const_play 0 _ _ _)
  rwa [pcode_botDB] at this

/-- CupodTroll cooperates with any opponent whose code is not `CupodBot k`'s. -/
theorem ctb_C_of_ne (k : ℕ) {opp : PD.Prog} (hopp : Proper opp)
    (hne : pcode opp ≠ pcode (CupodBot k)) :
    EvalGraph 2 (pcode (CupodTrollBot k)) (pcode opp) (pcode (CupodTrollBot k)) 0 := by
  have hn := not_found_eq_opp (proper_CupodTrollBot k) hopp (Q := CupodBot k) rfl hne k
  rw [pcode_CupodTrollBot] at hn ⊢
  exact search_else (phiT k) hn (const_play _ _ _ _)

/-- CupodTroll cooperates with `.bot CooperateBot`. -/
theorem ctb_vs_botCB (k : ℕ) :
    EvalGraph 2 (pcode (CupodTrollBot k)) (pBot (pConst 0)) (pcode (CupodTrollBot k)) 0 := by
  have := ctb_C_of_ne k (opp := .bot CooperateBot) proper_botCB
    (by rw [pcode_botCB, pcode_CupodBot]; exact pBot_ne_pSearch _ _ _ _ _)
  rwa [pcode_botCB] at this

/-- CupodTroll cooperates with `.bot DefectBot`. -/
theorem ctb_vs_botDB (k : ℕ) :
    EvalGraph 2 (pcode (CupodTrollBot k)) (pBot (pConst 1)) (pcode (CupodTrollBot k)) 0 := by
  have := ctb_C_of_ne k (opp := .bot DefectBot) proper_botDB
    (by rw [pcode_botDB, pcode_CupodBot]; exact pBot_ne_pSearch _ _ _ _ _)
  rwa [pcode_botDB] at this

/-- Wary cooperates with an opponent that cooperates with it (the `.neg` guard is false). -/
theorem wary_C_of_probe (k : ℕ) {opp : PD.Prog} (hopp : Proper opp) {N : ℕ}
    (h : EvalGraph N (pcode opp) (pcode (WaryBot k)) (pcode opp) 0) :
    EvalGraph 2 (pcode (WaryBot k)) (pcode opp) (pcode (WaryBot k)) 0 := by
  have hn := not_found_neg_opp_self (proper_WaryBot k) hopp .C h k
  rw [pcode_WaryBot] at hn ⊢
  exact search_else phiW hn (const_play _ _ _ _)

/-- Wary cooperates with `.bot CooperateBot`. -/
theorem wary_vs_botCB (k : ℕ) :
    EvalGraph 2 (pcode (WaryBot k)) (pBot (pConst 0)) (pcode (WaryBot k)) 0 := by
  have := wary_C_of_probe k (opp := .bot CooperateBot) proper_botCB (N := 2)
    (by rw [pcode_botCB]; exact bot_const_play 0 _ _ _)
  rwa [pcode_botCB] at this

/-- Just defects against an opponent that defects against `.bot (DupocBot k)`. -/
theorem just_D_of_probe (k : ℕ) {opp : PD.Prog} (hopp : Proper opp) {N : ℕ}
    (h : EvalGraph N (pcode opp) (pBot (pcode (DupocBot k))) (pcode opp) 1) :
    EvalGraph 2 (pcode (JustBot k)) (pcode opp) (pcode (JustBot k)) 1 := by
  have hn := not_found_opp_bot (proper_JustBot k) hopp (P := DupocBot k) rfl .C (b := .D) (by decide) h k
  rw [pcode_JustBot] at hn ⊢
  exact search_else (phiJ k) hn (const_play _ _ _ _)

/-- Prudent defects against an opponent that defects against it (the outer guard fails). -/
theorem prudent_D_of_probe (k : ℕ) {opp : PD.Prog} (hopp : Proper opp) {N : ℕ}
    (h : EvalGraph N (pcode opp) (pcode (PrudentBot k)) (pcode opp) 1) :
    EvalGraph 2 (pcode (PrudentBot k)) (pcode opp) (pcode (PrudentBot k)) 1 := by
  have hn := not_found_opp_self (proper_PrudentBot k) hopp .C (b := .D) (by decide) h k
  rw [pcode_PrudentBot'] at hn ⊢
  exact search_else phiP1 hn (const_play _ _ _ _)

/-- Prudent defects against an opponent that cooperates with `.bot DefectBot` (the prudence guard
fails; the outer verdict is irrelevant). -/
theorem prudent_D_of_inner (k : ℕ) {opp : PD.Prog} (hopp : Proper opp) {N : ℕ}
    (h : EvalGraph N (pcode opp) (pBot (pConst 1)) (pcode opp) 0) :
    EvalGraph 3 (pcode (PrudentBot k)) (pcode opp) (pcode (PrudentBot k)) 1 := by
  have hn := not_found_opp_bot (proper_PrudentBot k) hopp (P := DefectBot) rfl .D (b := .C) (by decide)
    (by rw [pcode_DB]; exact h) k
  rw [pcode_PrudentBot'] at hn ⊢
  exact search_either phiP1 (search_else phiP2 hn (const_play _ _ _ _)) (const_play _ _ _ _)

/-- Prudent defects against `.bot DefectBot` and against `.bot CooperateBot`. -/
theorem prudent_vs_botDB (k : ℕ) :
    EvalGraph 2 (pcode (PrudentBot k)) (pBot (pConst 1)) (pcode (PrudentBot k)) 1 := by
  have := prudent_D_of_probe k (opp := .bot DefectBot) proper_botDB (N := 2)
    (by rw [pcode_botDB]; exact bot_const_play 0 _ _ _)
  rwa [pcode_botDB] at this

theorem prudent_vs_botCB (k : ℕ) :
    EvalGraph 3 (pcode (PrudentBot k)) (pBot (pConst 0)) (pcode (PrudentBot k)) 1 := by
  have := prudent_D_of_inner k (opp := .bot CooperateBot) proper_botCB (N := 2)
    (by rw [pcode_botCB]; exact bot_const_play 0 _ _ _)
  rwa [pcode_botCB] at this

end searchers

/-! ### 8. Template disjointness for the `.eq` guard against the zoo -/

section templates

/-- Guardian's and Cupod's templates differ: at the frame `(TitForTatBot, DBot)`, "DBot plays D
against `.bot CooperateBot`" is true while "DBot plays D against TitForTatBot" is false. -/
lemma tcode_phiG_ne_phiCu : tcode phiG ≠ tcode phiCu := by
  refine tcode_ne_of_models TitForTatBot DBot ?_ ?_
  · rw [← trAt_subst TitForTatBot DBot sfp_TitForTatBot.1 sfp_DBot.1 _ rfl]
    show ℕ↓[LAct] ⊧ trAt TitForTatBot DBot (.plays DBot (.bot CooperateBot) .D)
    rw [models_trAt_plays _ _ _ _ _ sfp_DBot.1 proper_botCB, pcode_botCB]
    exact ⟨4, dbot_D_of_probe_C (bot_const_play 0 _ _ 0)⟩
  · rw [← trAt_subst TitForTatBot DBot sfp_TitForTatBot.1 sfp_DBot.1 _ rfl]
    show ¬ ℕ↓[LAct] ⊧ trAt TitForTatBot DBot (.plays DBot TitForTatBot .D)
    rw [models_trAt_plays _ _ _ _ _ sfp_DBot.1 sfp_TitForTatBot.1]
    rintro ⟨N, hN⟩
    have hC : EvalGraph 6 (pcode DBot) (pcode TitForTatBot) (pcode DBot) 0 :=
      dbot_C_of_probe_D (tft_D_of_probe_D (bot_const_play 0 _ _ 1))
    exact absurd (EvalGraph.unique' hN hC) (by decide)

/-- CupodTroll's and Cupod's templates differ: at the frame `(CooperateBot, CupodBot k)`,
"the opponent IS `CupodBot k`" is true while "the opponent defects against CooperateBot" is false. -/
lemma tcode_phiT_ne_phiCu (k : ℕ) : tcode (phiT k) ≠ tcode phiCu := by
  refine tcode_ne_of_models CooperateBot (CupodBot k) ?_ ?_
  · rw [← trAt_subst CooperateBot (CupodBot k) sfp_CooperateBot.1 (proper_CupodBot k) _ rfl]
    show ℕ↓[LAct] ⊧ trAt CooperateBot (CupodBot k) (.eq (CupodBot k) (CupodBot k))
    rw [models_trAt_eq _ _ _ _ (proper_CupodBot k)]
  · rw [← trAt_subst CooperateBot (CupodBot k) sfp_CooperateBot.1 (proper_CupodBot k) _ rfl]
    show ¬ ℕ↓[LAct] ⊧ trAt CooperateBot (CupodBot k) (.plays (CupodBot k) CooperateBot .D)
    rw [models_trAt_plays _ _ _ _ _ (proper_CupodBot k) sfp_CooperateBot.1]
    rintro ⟨N, hN⟩
    exact absurd (EvalGraph.unique' hN (snd_CupodBot_vs_CooperateBot_aux k)) (by decide)

/-- Wary's and Cupod's templates differ: at the frame `(MirrorBot, MirrorBot)` (a non-terminating
match), "the opponent does NOT cooperate" is true while "the opponent defects" is false. -/
lemma tcode_phiW_ne_phiCu : tcode phiW ≠ tcode phiCu := by
  refine tcode_ne_of_models MirrorBot MirrorBot ?_ ?_
  · rw [← trAt_subst MirrorBot MirrorBot sfp_MirrorBot.1 sfp_MirrorBot.1 _ rfl]
    show ℕ↓[LAct] ⊧ trAt MirrorBot MirrorBot (.neg (.plays MirrorBot MirrorBot .C))
    rw [models_trAt_neg, models_trAt_plays _ _ _ _ _ sfp_MirrorBot.1 sfp_MirrorBot.1, pcode_MirrorBot]
    rintro ⟨N, hN⟩
    exact mirror_vs_mirror N _ hN
  · rw [← trAt_subst MirrorBot MirrorBot sfp_MirrorBot.1 sfp_MirrorBot.1 _ rfl]
    show ¬ ℕ↓[LAct] ⊧ trAt MirrorBot MirrorBot (.plays MirrorBot MirrorBot .D)
    rw [models_trAt_plays _ _ _ _ _ sfp_MirrorBot.1 sfp_MirrorBot.1, pcode_MirrorBot]
    rintro ⟨N, hN⟩
    exact mirror_vs_mirror N _ hN

lemma pcode_GuardianBot_ne_CupodBot (k : ℕ) : pcode (GuardianBot k) ≠ pcode (CupodBot k) := by
  rw [pcode_GuardianBot, pcode_CupodBot]
  intro e
  exact tcode_phiG_ne_phiCu (pSearch_inj e).2.1

lemma pcode_CupodTrollBot_ne_CupodBot (k : ℕ) : pcode (CupodTrollBot k) ≠ pcode (CupodBot k) := by
  rw [pcode_CupodTrollBot, pcode_CupodBot]
  intro e
  exact tcode_phiT_ne_phiCu k (pSearch_inj e).2.1

lemma pcode_WaryBot_ne_CupodBot (k : ℕ) : pcode (WaryBot k) ≠ pcode (CupodBot k) := by
  rw [pcode_WaryBot, pcode_CupodBot]
  intro e
  exact tcode_phiW_ne_phiCu (pSearch_inj e).2.1

lemma pcode_PrudentBot_ne_CupodBot (k : ℕ) : pcode (PrudentBot k) ≠ pcode (CupodBot k) := by
  rw [pcode_PrudentBot', pcode_CupodBot]
  intro e
  exact pConst_ne_pSearch _ _ _ _ _ (pSearch_inj e).2.2.1.symm

lemma pcode_CB_ne_CupodBot (k : ℕ) : pcode CooperateBot ≠ pcode (CupodBot k) := by
  rw [pcode_CB, pcode_CupodBot]; exact pConst_ne_pSearch _ _ _ _ _
lemma pcode_DB_ne_CupodBot (k : ℕ) : pcode DefectBot ≠ pcode (CupodBot k) := by
  rw [pcode_DB, pcode_CupodBot]; exact pConst_ne_pSearch _ _ _ _ _
lemma pcode_Mirror_ne_CupodBot (k : ℕ) : pcode MirrorBot ≠ pcode (CupodBot k) := by
  rw [pcode_MirrorBot, Mirror, pcode_CupodBot]; exact pSim_ne_pSearch _ _ _ _ _ _
lemma pcode_DBot_ne_CupodBot (k : ℕ) : pcode DBot ≠ pcode (CupodBot k) := by
  simp only [DBot, DefectBot, pcode_ite, pcode_sim, pcode_opp, pcode_bot, pcode_const, pcode_CupodBot]
  exact pIte_ne_pSearch _ _ _ _ _ _ _ _
lemma pcode_EBot_ne_CupodBot (k : ℕ) : pcode EBot ≠ pcode (CupodBot k) := by
  simp only [EBot, DefectBot, CooperateBot, MirrorBot, pcode_ite, pcode_sim, pcode_opp, pcode_self, pcode_bot,
    pcode_const, pcode_CupodBot]
  exact pIte_ne_pSearch _ _ _ _ _ _ _ _
lemma pcode_OBot_ne_CupodBot (k : ℕ) : pcode OBot ≠ pcode (CupodBot k) := by
  simp only [OBot, DefectBot, CooperateBot, pcode_ite, pcode_sim, pcode_opp, pcode_bot, pcode_const, pcode_CupodBot]
  exact pIte_ne_pSearch _ _ _ _ _ _ _ _
lemma pcode_TFT_ne_CupodBot (k : ℕ) : pcode TitForTatBot ≠ pcode (CupodBot k) := by
  simp only [TitForTatBot, CooperateBot, pcode_ite, pcode_sim, pcode_opp, pcode_bot, pcode_const, pcode_CupodBot]
  exact pIte_ne_pSearch _ _ _ _ _ _ _ _

end templates

/-! ### 9. The SND cells: the guard is false, the else branch by soundness -/

section sndCells

/-! #### GuardianBot (6 of 8; `× EBot` and `× OBot` need a positive sub-fact, §11) -/

/-- `GuardianBot × CupodBot = (C, C)` (engine `llm_outcome_GuardianBot_vs_CupodBot`, pad 2), every `k`. -/
theorem snd_GuardianBot_vs_CupodBot (k : ℕ) :
    EvalGraph 2 (pcode (GuardianBot k)) (pcode (CupodBot k)) (pcode (GuardianBot k)) (actCode .C) ∧
    EvalGraph 2 (pcode (CupodBot k)) (pcode (GuardianBot k)) (pcode (CupodBot k)) (actCode .C) := by
  have hG := guardian_C_of_probe k (proper_CupodBot k) (cupod_vs_botCB k)
  exact ⟨hG, cupod_C_of_probe k (proper_GuardianBot k) hG⟩

/-- `GuardianBot × CupodTrollBot = (C, C)` (engine `llm_outcome_GuardianBot_vs_CupodTrollBot`, pad 2). -/
theorem snd_GuardianBot_vs_CupodTrollBot (k : ℕ) :
    EvalGraph 2 (pcode (GuardianBot k)) (pcode (CupodTrollBot k)) (pcode (GuardianBot k)) (actCode .C) ∧
    EvalGraph 2 (pcode (CupodTrollBot k)) (pcode (GuardianBot k)) (pcode (CupodTrollBot k)) (actCode .C) :=
  ⟨guardian_C_of_probe k (proper_CupodTrollBot k) (ctb_vs_botCB k),
   ctb_C_of_ne k (proper_GuardianBot k) (pcode_GuardianBot_ne_CupodBot k)⟩

/-- `GuardianBot × GuardianBot = (C, C)` (engine `llm_outcome_GuardianBot_vs_GuardianBot`, pad 2). -/
theorem snd_GuardianBot_vs_GuardianBot (k : ℕ) :
    EvalGraph 2 (pcode (GuardianBot k)) (pcode (GuardianBot k)) (pcode (GuardianBot k)) (actCode .C) ∧
    EvalGraph 2 (pcode (GuardianBot k)) (pcode (GuardianBot k)) (pcode (GuardianBot k)) (actCode .C) :=
  ⟨guardian_C_of_probe k (proper_GuardianBot k) (guardian_vs_botCB k),
   guardian_C_of_probe k (proper_GuardianBot k) (guardian_vs_botCB k)⟩

/-- `GuardianBot × TitForTatBot = (C, C)` (engine `llm_outcome_GuardianBot_vs_TitForTatBot`, pad 4). -/
theorem snd_GuardianBot_vs_TitForTatBot (k : ℕ) :
    EvalGraph 4 (pcode (GuardianBot k)) (pcode TitForTatBot) (pcode (GuardianBot k)) (actCode .C) ∧
    EvalGraph 4 (pcode TitForTatBot) (pcode (GuardianBot k)) (pcode TitForTatBot) (actCode .C) :=
  ⟨EvalGraph.mono_le (by omega) (guardian_C_of_probe k sfp_TitForTatBot.1
      (tft_C_of_probe_C (bot_const_play 0 _ _ 0))),
   tft_C_of_probe_C (guardian_vs_botCB k)⟩

/-- `GuardianBot × CooperateBot = (C, C)` (engine `outcome_GuardianBot_vs_CooperateBot`, pad 2). -/
theorem snd_GuardianBot_vs_CooperateBot (k : ℕ) :
    EvalGraph 2 (pcode (GuardianBot k)) (pcode CooperateBot) (pcode (GuardianBot k)) (actCode .C) ∧
    EvalGraph 2 (pcode CooperateBot) (pcode (GuardianBot k)) (pcode CooperateBot) (actCode .C) :=
  ⟨guardian_C_of_probe k sfp_CooperateBot.1 (by rw [pcode_CB]; exact const_play 0 _ _ 0),
   by rw [pcode_CB]; exact const_play 1 _ _ _⟩

/-- `GuardianBot × MirrorBot = (C, C)` (engine `outcome_GuardianBot_vs_MirrorBot`, pad 3). -/
theorem snd_GuardianBot_vs_MirrorBot (k : ℕ) :
    EvalGraph 3 (pcode (GuardianBot k)) (pcode MirrorBot) (pcode (GuardianBot k)) (actCode .C) ∧
    EvalGraph 3 (pcode MirrorBot) (pcode (GuardianBot k)) (pcode MirrorBot) (actCode .C) := by
  have hG := guardian_C_of_probe k sfp_MirrorBot.1 (mirror_copies (bot_const_play 0 _ _ 0))
  exact ⟨EvalGraph.mono_le (by omega) hG, mirror_copies hG⟩

/-! #### CupodTrollBot (8 of 8) -/

/-- `CupodTrollBot × CooperateBot = (C, C)` (engine `outcome_CupodTrollBot_vs_CooperateBot`, pad 2). -/
theorem snd_CupodTrollBot_vs_CooperateBot (k : ℕ) :
    EvalGraph 2 (pcode (CupodTrollBot k)) (pcode CooperateBot) (pcode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 2 (pcode CooperateBot) (pcode (CupodTrollBot k)) (pcode CooperateBot) (actCode .C) :=
  ⟨ctb_C_of_ne k sfp_CooperateBot.1 (pcode_CB_ne_CupodBot k), by rw [pcode_CB]; exact const_play 1 _ _ _⟩

/-- `CupodTrollBot × CupodTrollBot = (C, C)` (engine `outcome_CupodTrollBot_vs_CupodTrollBot`, pad 3). -/
theorem snd_CupodTrollBot_vs_CupodTrollBot (k : ℕ) :
    EvalGraph 3 (pcode (CupodTrollBot k)) (pcode (CupodTrollBot k)) (pcode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 3 (pcode (CupodTrollBot k)) (pcode (CupodTrollBot k)) (pcode (CupodTrollBot k)) (actCode .C) :=
  ⟨EvalGraph.mono_le (by omega) (ctb_C_of_ne k (proper_CupodTrollBot k) (pcode_CupodTrollBot_ne_CupodBot k)),
   EvalGraph.mono_le (by omega) (ctb_C_of_ne k (proper_CupodTrollBot k) (pcode_CupodTrollBot_ne_CupodBot k))⟩

/-- `CupodTrollBot × DBot = (C, D)` (engine `outcome_CupodTrollBot_vs_DBot`, pad 4). -/
theorem snd_CupodTrollBot_vs_DBot (k : ℕ) :
    EvalGraph 4 (pcode (CupodTrollBot k)) (pcode DBot) (pcode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 4 (pcode DBot) (pcode (CupodTrollBot k)) (pcode DBot) (actCode .D) :=
  ⟨EvalGraph.mono_le (by omega) (ctb_C_of_ne k sfp_DBot.1 (pcode_DBot_ne_CupodBot k)),
   dbot_D_of_probe_C (ctb_vs_botDB k)⟩

/-- `CupodTrollBot × DefectBot = (C, D)` (engine `outcome_CupodTrollBot_vs_DefectBot`, pad 2). -/
theorem snd_CupodTrollBot_vs_DefectBot (k : ℕ) :
    EvalGraph 2 (pcode (CupodTrollBot k)) (pcode DefectBot) (pcode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 2 (pcode DefectBot) (pcode (CupodTrollBot k)) (pcode DefectBot) (actCode .D) :=
  ⟨ctb_C_of_ne k sfp_DefectBot.1 (pcode_DB_ne_CupodBot k), by rw [pcode_DB]; exact const_play 1 _ _ _⟩

/-- `CupodTrollBot × EBot = (C, D)` (engine `outcome_CupodTrollBot_vs_EBot`, pad 4). -/
theorem snd_CupodTrollBot_vs_EBot (k : ℕ) :
    EvalGraph 4 (pcode (CupodTrollBot k)) (pcode EBot) (pcode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 4 (pcode EBot) (pcode (CupodTrollBot k)) (pcode EBot) (actCode .D) :=
  ⟨EvalGraph.mono_le (by omega) (ctb_C_of_ne k sfp_EBot.1 (pcode_EBot_ne_CupodBot k)),
   ebot_D_of_probe1_C (ctb_vs_botDB k)⟩

/-- `CupodTrollBot × MirrorBot = (C, C)` (engine `outcome_CupodTrollBot_vs_MirrorBot`, pad 3). -/
theorem snd_CupodTrollBot_vs_MirrorBot (k : ℕ) :
    EvalGraph 3 (pcode (CupodTrollBot k)) (pcode MirrorBot) (pcode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 3 (pcode MirrorBot) (pcode (CupodTrollBot k)) (pcode MirrorBot) (actCode .C) := by
  have hT := ctb_C_of_ne k sfp_MirrorBot.1 (pcode_Mirror_ne_CupodBot k)
  exact ⟨EvalGraph.mono_le (by omega) hT, mirror_copies hT⟩

/-- `CupodTrollBot × OBot = (C, C)` (engine `outcome_CupodTrollBot_vs_OBot`, pad 5). -/
theorem snd_CupodTrollBot_vs_OBot (k : ℕ) :
    EvalGraph 5 (pcode (CupodTrollBot k)) (pcode OBot) (pcode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 5 (pcode OBot) (pcode (CupodTrollBot k)) (pcode OBot) (actCode .C) :=
  ⟨EvalGraph.mono_le (by omega) (ctb_C_of_ne k sfp_OBot.1 (pcode_OBot_ne_CupodBot k)),
   obot_C_of_probes (ctb_vs_botCB k) (ctb_vs_botDB k)⟩

/-- `CupodTrollBot × TitForTatBot = (C, C)` (engine `outcome_CupodTrollBot_vs_TitForTatBot`, pad 4). -/
theorem snd_CupodTrollBot_vs_TitForTatBot (k : ℕ) :
    EvalGraph 4 (pcode (CupodTrollBot k)) (pcode TitForTatBot) (pcode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 4 (pcode TitForTatBot) (pcode (CupodTrollBot k)) (pcode TitForTatBot) (actCode .C) :=
  ⟨EvalGraph.mono_le (by omega) (ctb_C_of_ne k sfp_TitForTatBot.1 (pcode_TFT_ne_CupodBot k)),
   tft_C_of_probe_C (ctb_vs_botCB k)⟩

/-! #### PrudentBot (6 of 6) -/

/-- `PrudentBot × CooperateBot = (D, C)` (engine `outcome_PrudentBot_vs_CooperateBot`, pad 3): the
prudence guard is false; the outer verdict is irrelevant. -/
theorem snd_PrudentBot_vs_CooperateBot (k : ℕ) :
    EvalGraph 3 (pcode (PrudentBot k)) (pcode CooperateBot) (pcode (PrudentBot k)) (actCode .D) ∧
    EvalGraph 3 (pcode CooperateBot) (pcode (PrudentBot k)) (pcode CooperateBot) (actCode .C) :=
  ⟨prudent_D_of_inner k sfp_CooperateBot.1 (by rw [pcode_CB]; exact const_play 0 _ _ 0),
   by rw [pcode_CB]; exact const_play 2 _ _ _⟩

/-- `PrudentBot × CupodTrollBot = (D, C)` (engine `outcome_PrudentBot_vs_CupodTrollBot`, pad 3). -/
theorem snd_PrudentBot_vs_CupodTrollBot (k : ℕ) :
    EvalGraph 3 (pcode (PrudentBot k)) (pcode (CupodTrollBot k)) (pcode (PrudentBot k)) (actCode .D) ∧
    EvalGraph 3 (pcode (CupodTrollBot k)) (pcode (PrudentBot k)) (pcode (CupodTrollBot k)) (actCode .C) :=
  ⟨prudent_D_of_inner k (proper_CupodTrollBot k) (ctb_vs_botDB k),
   EvalGraph.mono_le (by omega) (ctb_C_of_ne k (proper_PrudentBot k) (pcode_PrudentBot_ne_CupodBot k))⟩

/-- `PrudentBot × DBot = (D, C)` (engine `outcome_PrudentBot_vs_DBot`, pad 7). -/
theorem snd_PrudentBot_vs_DBot (k : ℕ) :
    EvalGraph 7 (pcode (PrudentBot k)) (pcode DBot) (pcode (PrudentBot k)) (actCode .D) ∧
    EvalGraph 7 (pcode DBot) (pcode (PrudentBot k)) (pcode DBot) (actCode .C) :=
  ⟨EvalGraph.mono_le (by omega) (prudent_D_of_inner k sfp_DBot.1 (dbot_C_of_probe_D (bot_const_play 0 _ _ 1))),
   EvalGraph.mono_le (by omega) (dbot_C_of_probe_D (prudent_vs_botDB k))⟩

/-- `PrudentBot × DefectBot = (D, D)` (engine `outcome_PrudentBot_vs_DefectBot`, pad 2). -/
theorem snd_PrudentBot_vs_DefectBot (k : ℕ) :
    EvalGraph 2 (pcode (PrudentBot k)) (pcode DefectBot) (pcode (PrudentBot k)) (actCode .D) ∧
    EvalGraph 2 (pcode DefectBot) (pcode (PrudentBot k)) (pcode DefectBot) (actCode .D) :=
  ⟨prudent_D_of_probe k sfp_DefectBot.1 (by rw [pcode_DB]; exact const_play 0 _ _ 1),
   by rw [pcode_DB]; exact const_play 1 _ _ _⟩

/-- `PrudentBot × OBot = (D, D)` (engine `outcome_PrudentBot_vs_OBot`, pad 6). -/
theorem snd_PrudentBot_vs_OBot (k : ℕ) :
    EvalGraph 6 (pcode (PrudentBot k)) (pcode OBot) (pcode (PrudentBot k)) (actCode .D) ∧
    EvalGraph 6 (pcode OBot) (pcode (PrudentBot k)) (pcode OBot) (actCode .D) := by
  have hO := obot_D_of_probe1_D (prudent_vs_botCB k) (by decide)
  exact ⟨EvalGraph.mono_le (by omega) (prudent_D_of_probe k sfp_OBot.1 hO), EvalGraph.mono_le (by omega) hO⟩

/-- `PrudentBot × TitForTatBot = (D, D)` (engine `outcome_PrudentBot_vs_TitForTatBot`, pad 6). -/
theorem snd_PrudentBot_vs_TitForTatBot (k : ℕ) :
    EvalGraph 6 (pcode (PrudentBot k)) (pcode TitForTatBot) (pcode (PrudentBot k)) (actCode .D) ∧
    EvalGraph 6 (pcode TitForTatBot) (pcode (PrudentBot k)) (pcode TitForTatBot) (actCode .D) := by
  have hT := tft_D_of_probe_D (prudent_vs_botCB k)
  exact ⟨EvalGraph.mono_le (by omega) (prudent_D_of_probe k sfp_TitForTatBot.1 hT),
    EvalGraph.mono_le (by omega) hT⟩

/-! #### WaryBot (4 of 6; `× DBot` and `× EBot` need the positive `.neg` guard, out of scope) -/

/-- `WaryBot × CooperateBot = (C, C)` (engine `outcome_WaryBot_vs_CooperateBot`, pad 2). -/
theorem snd_WaryBot_vs_CooperateBot (k : ℕ) :
    EvalGraph 2 (pcode (WaryBot k)) (pcode CooperateBot) (pcode (WaryBot k)) (actCode .C) ∧
    EvalGraph 2 (pcode CooperateBot) (pcode (WaryBot k)) (pcode CooperateBot) (actCode .C) :=
  ⟨wary_C_of_probe k sfp_CooperateBot.1 (by rw [pcode_CB]; exact const_play 0 _ _ 0),
   by rw [pcode_CB]; exact const_play 1 _ _ _⟩

/-- `WaryBot × CupodTrollBot = (C, C)` (engine `outcome_WaryBot_vs_CupodTrollBot`, pad 2). -/
theorem snd_WaryBot_vs_CupodTrollBot (k : ℕ) :
    EvalGraph 2 (pcode (WaryBot k)) (pcode (CupodTrollBot k)) (pcode (WaryBot k)) (actCode .C) ∧
    EvalGraph 2 (pcode (CupodTrollBot k)) (pcode (WaryBot k)) (pcode (CupodTrollBot k)) (actCode .C) := by
  have hT := ctb_C_of_ne k (proper_WaryBot k) (pcode_WaryBot_ne_CupodBot k)
  exact ⟨wary_C_of_probe k (proper_CupodTrollBot k) hT, hT⟩

/-- `WaryBot × GuardianBot = (C, C)` (engine `llm_outcome_WaryBot_vs_GuardianBot`, pad 2). -/
theorem snd_WaryBot_vs_GuardianBot (k : ℕ) :
    EvalGraph 2 (pcode (WaryBot k)) (pcode (GuardianBot k)) (pcode (WaryBot k)) (actCode .C) ∧
    EvalGraph 2 (pcode (GuardianBot k)) (pcode (WaryBot k)) (pcode (GuardianBot k)) (actCode .C) := by
  have hG := guardian_C_of_probe k (proper_WaryBot k) (wary_vs_botCB k)
  exact ⟨wary_C_of_probe k (proper_GuardianBot k) hG, hG⟩

/-- `WaryBot × TitForTatBot = (C, C)` (engine `outcome_WaryBot_vs_TitForTatBot`, pad 4). -/
theorem snd_WaryBot_vs_TitForTatBot (k : ℕ) :
    EvalGraph 4 (pcode (WaryBot k)) (pcode TitForTatBot) (pcode (WaryBot k)) (actCode .C) ∧
    EvalGraph 4 (pcode TitForTatBot) (pcode (WaryBot k)) (pcode TitForTatBot) (actCode .C) := by
  have hT := tft_C_of_probe_C (wary_vs_botCB k)
  exact ⟨EvalGraph.mono_le (by omega) (wary_C_of_probe k sfp_TitForTatBot.1 hT), hT⟩

/-! #### CupodBot (2 of 4; `× DBot` and `× EBot` need Cupod's positive guard against `.bot DefectBot`) -/

/-- `CupodBot × CooperateBot = (C, C)` (engine `outcome_CupodBot_vs_CooperateBot`, pad 2). -/
theorem snd_CupodBot_vs_CooperateBot (k : ℕ) :
    EvalGraph 2 (pcode (CupodBot k)) (pcode CooperateBot) (pcode (CupodBot k)) (actCode .C) ∧
    EvalGraph 2 (pcode CooperateBot) (pcode (CupodBot k)) (pcode CooperateBot) (actCode .C) :=
  ⟨cupod_C_of_probe k sfp_CooperateBot.1 (by rw [pcode_CB]; exact const_play 0 _ _ 0),
   by rw [pcode_CB]; exact const_play 1 _ _ _⟩

/-- `CupodBot × TitForTatBot = (C, C)` (engine `outcome_CupodBot_vs_TitForTatBot`, pad 4). -/
theorem snd_CupodBot_vs_TitForTatBot (k : ℕ) :
    EvalGraph 4 (pcode (CupodBot k)) (pcode TitForTatBot) (pcode (CupodBot k)) (actCode .C) ∧
    EvalGraph 4 (pcode TitForTatBot) (pcode (CupodBot k)) (pcode TitForTatBot) (actCode .C) := by
  have hT := tft_C_of_probe_C (cupod_vs_botCB k)
  exact ⟨EvalGraph.mono_le (by omega) (cupod_C_of_probe k sfp_TitForTatBot.1 hT), hT⟩

/-! #### DupocBot (2 of 2) -/

/-- `DupocBot × DefectBot = (D, D)` (engine `outcome_DupocBot_vs_DefectBot`, pad 2). -/
theorem snd_DupocBot_vs_DefectBot (k : ℕ) :
    EvalGraph 2 (pcode (DupocBot k)) (pcode DefectBot) (pcode (DupocBot k)) (actCode .D) ∧
    EvalGraph 2 (pcode DefectBot) (pcode (DupocBot k)) (pcode DefectBot) (actCode .D) :=
  ⟨dupoc_D_of_probe k sfp_DefectBot.1 (by rw [pcode_DB]; exact const_play 0 _ _ 1),
   by rw [pcode_DB]; exact const_play 1 _ _ _⟩

/-- `DupocBot × OBot = (D, D)` (engine `outcome_DupocBot_vs_OBot`, pad 5): OBot's first probe (Dupoc
against `.bot CooperateBot`) is left undecided — Dupoc defects against `.bot DefectBot` either way. -/
theorem snd_DupocBot_vs_OBot (k : ℕ) :
    EvalGraph 5 (pcode (DupocBot k)) (pcode OBot) (pcode (DupocBot k)) (actCode .D) ∧
    EvalGraph 5 (pcode OBot) (pcode (DupocBot k)) (pcode OBot) (actCode .D) := by
  obtain ⟨r, hr⟩ := dupoc_body_total k (DupocBot k) (.bot CooperateBot)
  rw [pcode_botCB] at hr
  have hO := obot_D_of_any hr (dupoc_vs_botDB k)
  exact ⟨EvalGraph.mono_le (by omega) (dupoc_D_of_probe k sfp_OBot.1 hO), hO⟩

/-! #### JustBot (2 of 2), on the engine's own code `pcode (JustBot k)` -/

/-- `JustBot × DefectBot = (D, D)` (engine `outcome_JustBot_vs_DefectBot`, pad 2). -/
theorem snd_JustBot_vs_DefectBot (k : ℕ) :
    EvalGraph 2 (pcode (JustBot k)) (pcode DefectBot) (pcode (JustBot k)) (actCode .D) ∧
    EvalGraph 2 (pcode DefectBot) (pcode (JustBot k)) (pcode DefectBot) (actCode .D) :=
  ⟨just_D_of_probe k sfp_DefectBot.1 (by rw [pcode_DB]; exact const_play 0 _ _ 1),
   by rw [pcode_DB]; exact const_play 1 _ _ _⟩

/-- The frozen snapshot `.bot (DupocBot k)` defects against `.bot DefectBot` (fuel 3). -/
theorem botDupoc_vs_botDB (k : ℕ) :
    EvalGraph 3 (pBot (pcode (DupocBot k))) (pBot (pConst 1)) (pBot (pcode (DupocBot k))) 1 := by
  show EvalGraph (2 + 1) _ _ _ _
  rw [EvalGraph.bot_iff]
  have := dupoc_body_D_of_probe k (me := .bot (DupocBot k)) (opp := .bot DefectBot) (proper_bot _) proper_botDB
    (N := 2) (by rw [pcode_botDB, pcode_bot]; exact bot_const_play 0 _ _ _)
  rwa [pcode_botDB, pcode_bot] at this

/-- The frozen snapshot `.bot (DupocBot k)` plays against `.bot CooperateBot` (fuel 3). -/
theorem botDupoc_vs_botCB_total (k : ℕ) :
    ∃ r, EvalGraph 3 (pBot (pcode (DupocBot k))) (pBot (pConst 0)) (pBot (pcode (DupocBot k))) r := by
  obtain ⟨r, hr⟩ := dupoc_body_total k (.bot (DupocBot k)) (.bot CooperateBot)
  rw [pcode_botCB, pcode_bot] at hr
  exact ⟨r, (EvalGraph.bot_iff (n := 2)).mpr hr⟩

/-- `JustBot × OBot = (D, D)` (engine `outcome_JustBot_vs_OBot`, pad 6): OBot defects against the
frozen `.bot (DupocBot k)` (which defects against `.bot DefectBot`), so Just's guard is false. -/
theorem snd_JustBot_vs_OBot (k : ℕ) :
    EvalGraph 6 (pcode (JustBot k)) (pcode OBot) (pcode (JustBot k)) (actCode .D) ∧
    EvalGraph 6 (pcode OBot) (pcode (JustBot k)) (pcode OBot) (actCode .D) := by
  obtain ⟨r, hr⟩ := botDupoc_vs_botCB_total k
  have hOb : EvalGraph 6 (pcode OBot) (pBot (pcode (DupocBot k))) (pcode OBot) 1 :=
    obot_D_of_any hr (botDupoc_vs_botDB k)
  have hJ := just_D_of_probe k sfp_OBot.1 hOb
  refine ⟨EvalGraph.mono_le (by omega) hJ, ?_⟩
  -- OBot against Just: Just cooperates with neither probe … it defects against `.bot DefectBot`,
  -- and against `.bot CooperateBot` it plays something.
  have h2 : EvalGraph 2 (pcode (JustBot k)) (pBot (pConst 1)) (pcode (JustBot k)) 1 := by
    have := just_D_of_probe k (opp := .bot DefectBot) proper_botDB (N := 2)
      (by rw [pcode_botDB]; exact bot_const_play 0 _ _ _)
    rwa [pcode_botDB] at this
  have h1 : ∃ r, EvalGraph 2 (pcode (JustBot k)) (pBot (pConst 0)) (pcode (JustBot k)) r := by
    rw [pcode_JustBot]
    by_cases hg : LenProvableV TAct k (guardCode (tcode (phiJ k)) (pSearch k (tcode (phiJ k)) (pConst 0) (pConst 1))
      (pBot (pConst 0)))
    · exact ⟨0, search_then (phiJ k) hg (const_play _ _ _ _)⟩
    · exact ⟨1, search_else (phiJ k) hg (const_play _ _ _ _)⟩
  obtain ⟨r', hr'⟩ := h1
  exact EvalGraph.mono_le (by omega) (obot_D_of_any hr' h2)

end sndCells

end ArithS
