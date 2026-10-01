import ArithS.Cells.SearchFree
import ArithS.Eval.Det
import ArithS.Agents.InstanceV
import ArithS.Loeb.NumeralFacts
import ArithS.Loeb.Diag
import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.CupodTrollBot

/-!
# ArithS.Cells.SoundnessCells — the SND class of the census in PA-`S'`, and Guardian's positive cells

`Research/Notes/ROUTE_B_SCOPE.md` §3 Phase 4, class **SND** of `ROUTE_B_CENSUS.md`: the 36 cells
whose searcher takes its ELSE branch because its guard is semantically FALSE — the red cell's argument
(`RedCell.lean`), cell by cell, with no oracle, no Löb, no floor and no budget threshold (every `k`, or all large
`k` where a positive sub-fact is needed).

1. **The general SND lemma** `snd_else_of_false : ¬ (ℕ ⊨ sentenceAt me opp φ) → ¬ LenBox TAct k (guardOf φ me opp)`
   (`TAct` is sound in ℕ, `models_sentenceAt_of_lenBox`), and the realization of a fragment guard in a proper
   frame as the realization of its CLOSED instantiation in any frame, `sentenceAt_subst` (`template_subst` + the closed
   description terms are fixed by every rewriter). Truth equations for the guard shapes that were missing:
   `models_sentenceAt_neg`, `models_sentenceAt_impl`, `models_sentenceAt_eq` (the `.eq` atom is code equality).
2. **The "not found" lemmas per guard shape** (`not_found_opp_self`, `_opp_bot`, `_neg_opp_self`, `_eq_opp`):
   the arithmetized sub-play of the OTHER program, by determinism (`EvalGraph.unique'`), refutes the guard.
3. **The closed-atom positive kit**: `tact_proves_plays_closed` (a true closed atom about search-free players is
   a `TAct`-theorem: Σ₁-completeness of PA at ℕ in both readings — `lMap_swap_sentenceAt_plays` needs no atomicity,
   the transposed play comes from the engine's `decide` through the search-free lockstep transfer — and
   `TAct_complete_of_readings`), `found_of_tact` (found above the proof length).
4. **The engine's codes** (`progCode_GuardianBot`, …, `progCode_PrudentBot_search`), the search clause on engine templates
   (`search_else`/`search_then`/`search_either` — a node whose two branches agree needs NO verdict: Prudent's
   outer guard, Dupoc's and Just's probe against `.bot CooperateBot` inside OBot), and the search-free probers'
   plays from their probe results (`dbot_*`, `tft_*`, `obot_*`, `ebot_*`, `mirror_copies`).
5. **Template disjointness** for CupodTroll's `.eq` guard is SEMANTIC (`templateCode_ne_of_models`: two guards whose
   realizations differ in truth at ONE frame have different codes) — Guardian vs Cupod at `(TitForTatBot, DBot)`,
   CupodTroll vs Cupod at `(CooperateBot, CupodBot k)`, Wary vs Cupod at the NON-TERMINATING frame
   `(MirrorBot, MirrorBot)` (a terminating frame never separates `¬(plays C)` from `plays D`).
6. **The cells** `snd_<L>_vs_<R>`, at the engine's pads, stated on the engine's own codes `progCode (L k)`:
   Guardian 8 (`× EBot`/`× OBot` need Guardian's guard FOUND against `.bot DefectBot`: its guard names no `.self`,
   so against a closed opponent its realization is a FIXED closed atom, `guardian_found`), CupodTroll 8,
   Prudent 6, Wary 4, Cupod 2, Dupoc 2, Just 2 (on `progCode (JustBot k)`, the frozen snapshot evaluated as Dupoc's
   body in its own frame). Plus the two Guardian POS cells `pos_GuardianBot_vs_DefectBot`/`_DBot`.
   Wary's `× DBot`/`× EBot` and Cupod's `× DBot`/`× EBot` need the searcher's OWN description (a `.self` guard
   found against `.bot DefectBot`): `Cells/PositiveCells.lean`.

Conventions: every threshold EXISTENTIAL; `simp` never sees a closed quote; the `≤` at ℕ is `Nat.le`;
statements pin the fuel to the engine's pad (`EvalGraph.mono_le` lifts).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open PD.Bots

/-! ### 1. The general SND lemma -/

/-- **SND**: a guard whose realization is FALSE in `ℕ` is never found, at ANY budget (`TAct` is
sound in `ℕ`, `models_sentenceAt_of_lenBox`). -/
theorem snd_else_of_false {φ : PD.Formula} {me opp : PD.Prog} {k : ℕ}
    (h : ¬ ℕ↓[LAct] ⊧ sentenceAt me opp φ) (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    ¬ LenBox TAct k (guardOf φ me opp) :=
  fun hl ↦ h (models_sentenceAt_of_lenBox hl hφ)

/-- The realization of a fragment guard in a proper frame is the realization of its CLOSED
instantiation in any frame (`template_subst` + the closed description terms are fixed by every
rewriter). -/
theorem sentenceAt_subst (me' opp' : PD.Prog) {me opp : PD.Prog} (hme : ProperPlayer me) (hopp : ProperPlayer opp)
    (φ : PD.Formula) (hφ : fragF φ = true) :
    sentenceAt me' opp' (φ.subst me opp) = sentenceAt me opp φ := by
  unfold sentenceAt
  rw [template_subst hme hopp φ hφ]
  have hv : (fun i ↦ Rew.subst (descriptionTerms (progCode me') (progCode opp')) (descTerms6 me opp i)) =
      descriptionTerms (progCode me) (progCode opp) := by
    funext i
    unfold descTerms6
    rw [rew_cl, cl_zero]
  unfold Rewriting.subst
  rw [← TransitiveRewriting.comp_app, comp_subst_eq, hv]

/-- The realization of a negated guard is the negation of the realization. -/
theorem sentenceAt_neg (me opp : PD.Prog) (φ : PD.Formula) :
    sentenceAt me opp (.neg φ) = ∼ sentenceAt me opp φ := by
  unfold sentenceAt
  rw [template_neg]
  unfold Rewriting.subst
  rw [LogicalConnective.HomClass.map_neg]

theorem sentenceAt_impl (me opp : PD.Prog) (φ ψ : PD.Formula) :
    sentenceAt me opp (.impl φ ψ) = sentenceAt me opp φ 🡒 sentenceAt me opp ψ := by
  unfold sentenceAt
  rw [template_impl]
  unfold Rewriting.subst
  rw [LogicalConnective.HomClass.map_imply]

theorem models_sentenceAt_neg (me opp : PD.Prog) (φ : PD.Formula) :
    ℕ↓[LAct] ⊧ sentenceAt me opp (.neg φ) ↔ ¬ ℕ↓[LAct] ⊧ sentenceAt me opp φ := by
  rw [sentenceAt_neg, Semantics.Not.models_not]

theorem models_sentenceAt_impl (me opp : PD.Prog) (φ ψ : PD.Formula) :
    ℕ↓[LAct] ⊧ sentenceAt me opp (.impl φ ψ) ↔ (ℕ↓[LAct] ⊧ sentenceAt me opp φ → ℕ↓[LAct] ⊧ sentenceAt me opp ψ) := by
  rw [sentenceAt_impl, Semantics.Imp.models_imply]

/-- **The truth equation of the `.eq` atom**: for a proper probe `P`, "`P` is `Q`" holds in `ℕ` iff
the codes coincide. -/
theorem models_sentenceAt_eq (me' opp' P Q : PD.Prog) (hP : ProperPlayer P) :
    ℕ↓[LAct] ⊧ sentenceAt me' opp' (.eq P Q) ↔ progCode P = progCode Q := by
  rw [models_iff]
  unfold sentenceAt Semiformula.Realize
  rw [template_eq]
  unfold progGraph
  rw [progAux_of_ne hP.1 hP.2]
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, eval_closedDesc, Semiformula.eval_rel, stdReadingNat_rel_eq, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_one, Semiterm.val_bvar]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, _, rfl, rfl, h⟩

/-! ### 2. The guard shapes: "not found" from the arithmetized sub-play -/

section shapes

lemma properPlayer_bot (p : PD.Prog) : ProperPlayer (.bot p) := ⟨by simp, by simp⟩

/-- **`.plays .opp .self a` is not found** when `opp` plays `b ≠ a` against `me`. -/
theorem not_found_opp_self {me opp : PD.Prog} (hme : ProperPlayer me) (hopp : ProperPlayer opp) (a : PD.Action)
    {b : PD.Action} (hab : b ≠ a) {N : ℕ} (h : EvalGraph N (progCode opp) (progCode me) (progCode opp) (actCode b))
    (k : ℕ) : ¬ LenBox TAct k (guardCode (templateCode (.plays .opp .self a)) (progCode me) (progCode opp)) := by
  apply snd_else_of_false (φ := .plays .opp .self a)
  rw [← sentenceAt_subst me opp hme hopp _ rfl]
  show ¬ ℕ↓[LAct] ⊧ sentenceAt me opp (.plays opp me a)
  rw [models_sentenceAt_plays me opp opp me a hopp hme]
  rintro ⟨N', h'⟩
  exact hab (actCode_inj (EvalGraph.unique' h h'))

/-- **`.plays .opp (.bot P) a` is not found** when `opp` plays `b ≠ a` against the frozen `.bot P`. -/
theorem not_found_opp_bot {me opp : PD.Prog} (hme : ProperPlayer me) (hopp : ProperPlayer opp) {P : PD.Prog}
    (hfP : fragP P = true) (a : PD.Action) {b : PD.Action} (hab : b ≠ a) {N : ℕ}
    (h : EvalGraph N (progCode opp) (pBot (progCode P)) (progCode opp) (actCode b))
    (k : ℕ) : ¬ LenBox TAct k (guardCode (templateCode (.plays .opp (.bot P) a)) (progCode me) (progCode opp)) := by
  apply snd_else_of_false (φ := .plays .opp (.bot P) a)
  rw [← sentenceAt_subst me opp hme hopp _ (by simp [fragF, fragP, atomicP, closedP, hfP])]
  show ¬ ℕ↓[LAct] ⊧ sentenceAt me opp (.plays opp (.bot P) a)
  rw [models_sentenceAt_plays me opp opp (.bot P) a hopp (properPlayer_bot P), progCode_bot]
  rintro ⟨N', h'⟩
  exact hab (actCode_inj (EvalGraph.unique' h h'))

/-- **`.neg (.plays .opp .self a)` is not found** when `opp` DOES play `a` against `me`. -/
theorem not_found_neg_opp_self {me opp : PD.Prog} (hme : ProperPlayer me) (hopp : ProperPlayer opp) (a : PD.Action)
    {N : ℕ} (h : EvalGraph N (progCode opp) (progCode me) (progCode opp) (actCode a))
    (k : ℕ) : ¬ LenBox TAct k (guardCode (templateCode (.neg (.plays .opp .self a))) (progCode me) (progCode opp)) := by
  apply snd_else_of_false (φ := .neg (.plays .opp .self a))
  rw [← sentenceAt_subst me opp hme hopp _ rfl]
  show ¬ ℕ↓[LAct] ⊧ sentenceAt me opp (.neg (.plays opp me a))
  rw [models_sentenceAt_neg, models_sentenceAt_plays me opp opp me a hopp hme, not_not]
  exact ⟨N, h⟩

/-- **`.eq .opp Q` is not found** when the opponent's code is not `Q`'s. -/
theorem not_found_eq_opp {me opp : PD.Prog} (hme : ProperPlayer me) (hopp : ProperPlayer opp) {Q : PD.Prog}
    (hfQ : fragP Q = true) (hne : progCode opp ≠ progCode Q) (k : ℕ) :
    ¬ LenBox TAct k (guardCode (templateCode (.eq .opp Q)) (progCode me) (progCode opp)) := by
  apply snd_else_of_false (φ := .eq .opp Q)
  rw [← sentenceAt_subst me opp hme hopp _ (by simp [fragF, fragP, atomicP, hfQ])]
  show ¬ ℕ↓[LAct] ⊧ sentenceAt me opp (.eq opp Q)
  rw [models_sentenceAt_eq me opp opp Q hopp]
  exact hne

end shapes

/-! ### 3. The "found" lemmas: closed atoms, fixed sentences -/

section found

/-- A `TAct`-theorem is found at every budget above its proof length. -/
theorem found_of_tact {φ : PD.Formula} {me opp : PD.Prog} (h : TAct ⊢ sentenceAt me opp φ)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    ∃ L : ℕ, ∀ k : ℕ, L ≤ k → LenBox TAct k (guardCode (templateCode φ) (progCode me) (progCode opp)) := by
  obtain ⟨N, hN⟩ := lenBoxNat_of_provable h
  refine ⟨N, fun k hk ↦ ?_⟩
  rw [← guardOf, guardOf_eq_quote_sentenceAt φ me opp hφ, lenBox_nat]
  exact lenBoxNat_codeBound_mono hk hN

/-- τ on the template of a play atom over FRAGMENT programs (atomicity is not needed: the `.plays`
arm of `Code.lMap_swap_template`, verbatim). -/
theorem lMap_swap_template_plays {p q : PD.Prog} (hp : fragP p = true) (hq : fragP q = true) (a : PD.Action) :
    Semiformula.lMap swap (template (.plays p q a)) = template (.plays p.transpose q.transpose a.swap) := by
  rw [template_plays, template_plays]
  unfold progGraph
  simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
    lMap_swap_evalG, lMap_swap_progAux (transposeCode_progCode p hp), lMap_swap_progAux (transposeCode_progCode q hq)]
  congr 4
  · congr 1; funext i; fin_cases i <;> rfl
  · congr 1
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1
      funext i
      fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · show Semiterm.lMap swap (cl (actT (actCode a))) = cl (actT (actCode a.swap))
        rw [lMap_swap_cl, lMap_swap_actT, actCode_swap]

/-- τ on the realized play atom (fragment frame and programs). -/
theorem lMap_swap_sentenceAt_plays {me opp p q : PD.Prog} (hme : fragP me = true) (hopp : fragP opp = true)
    (hp : fragP p = true) (hq : fragP q = true) (a : PD.Action) :
    Semiformula.lMap swap (sentenceAt me opp (.plays p q a)) =
      sentenceAt me.transpose opp.transpose (.plays p.transpose q.transpose a.swap) := by
  unfold sentenceAt
  rw [Semiformula.lMap_subst, lMap_swap_template_plays hp hq]
  congr 1
  funext i
  fin_cases i <;> simp [descriptionTerms, lMap_swap_canonicalMeta, lMap_swap_revalueUMeta, lMap_swap_revalueWMeta, transposeCode_progCode me hme,
    transposeCode_progCode opp hopp]

/-- The transposition of a search-free player is a search-free player. -/
theorem sfp_transpose {X : PD.Prog} (hX : SearchFreePlayer X) (hm : modestP X.transpose = true)
    (hs : X.transpose.hasSearch = false) : SearchFreePlayer X.transpose :=
  ⟨⟨transpose_ne_self hX.1.1, transpose_ne_opp hX.1.2⟩, hm, hs⟩

/-- **`TAct` proves a true closed atom** about search-free proper players: the standard reading by
Σ₁-completeness of PA at ℕ (`pa_proves_sentenceAt_of_evalGraph`), the swapped reading by the same on the
TRANSPOSED play; completeness (`TAct_complete_of_readings`) closes. -/
theorem tact_proves_plays_closed {X Y : PD.Prog} (hX : SearchFreePlayer X) (hY : SearchFreePlayer Y)
    (a : PD.Action) {N : ℕ} (h : EvalGraph N (progCode X) (progCode Y) (progCode X) (actCode a)) {N' : ℕ}
    (hτ : EvalGraph N' (progCode X.transpose) (progCode Y.transpose) (progCode X.transpose) (actCode a.swap)) :
    TAct ⊢ sentenceAt X Y (.plays X Y a) := by
  have hXτ : ProperPlayer X.transpose := ⟨transpose_ne_self hX.1.1, transpose_ne_opp hX.1.2⟩
  have hYτ : ProperPlayer Y.transpose := ⟨transpose_ne_self hY.1.1, transpose_ne_opp hY.1.2⟩
  refine TAct_complete_of_readings _ fun M _ _ ↦ ?_
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  constructor
  · have hpa := pa_proves_sentenceAt_of_evalGraph X Y h hX.1 hY.1
    have hM : M↓[ℒₒᵣ] ⊧ Semiformula.lMap inst (sentenceAt X Y (.plays X Y a)) := models_of_provable inferInstance hpa
    rw [models_inst_V, stdReadingV_eq_stdReading] at hM
    exact hM
  · have hpa := pa_proves_sentenceAt_of_evalGraph X.transpose Y.transpose hτ hXτ hYτ
    have hM : M↓[ℒₒᵣ] ⊧ Semiformula.lMap inst (sentenceAt X.transpose Y.transpose (.plays X.transpose Y.transpose a.swap)) :=
      models_of_provable inferInstance hpa
    rw [models_inst_V, stdReadingV_eq_stdReading] at hM
    refine (Semiformula.eval_lMap (s₂ := stdReading M) (Φ := swap)).mp ?_
    rw [lMap_swap_sentenceAt_plays (fragP_of_modestP X hX.2.1) (fragP_of_modestP Y hY.2.1)
      (fragP_of_modestP X hX.2.1) (fragP_of_modestP Y hY.2.1)]
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
def phiPo : PD.Formula := .plays .opp .self .C
/-- Prudent's inner (prudence) guard. -/
def phiPi : PD.Formula := .plays .opp (.bot DefectBot) .D

lemma progCode_GuardianBot (k : ℕ) :
    progCode (GuardianBot k) = pSearch k (templateCode phiG) (pConst 1) (pConst 0) := by
  rw [GuardianBot, progCode_search_noSnap _ _ _ _ rfl]; simp [phiG, actCode]
lemma progCode_CupodBot (k : ℕ) :
    progCode (CupodBot k) = pSearch k (templateCode phiCu) (pConst 1) (pConst 0) := by
  rw [CupodBot, progCode_search_noSnap _ _ _ _ rfl]; simp [phiCu, actCode]
lemma progCode_DupocBot_search (k : ℕ) :
    progCode (DupocBot k) = pSearch k (templateCode phiDu) (pConst 0) (pConst 1) := by
  rw [DupocBot, progCode_search_noSnap _ _ _ _ rfl]; simp [phiDu, actCode]
/-- CupodTroll's stored template is ABSTRACTED (its guard freezes the budget-carrying `CupodBot k`): the code
stores `templateCodeAt (phiT k) k`, a constant (route (c) made generic, 2026-10-01). -/
lemma progCode_CupodTrollBot (k : ℕ) :
    progCode (CupodTrollBot k) = pSearch k (templateCodeAt (phiT k) k) (pConst 1) (pConst 0) := by
  simp [CupodTrollBot, phiT, actCode]
lemma progCode_WaryBot (k : ℕ) :
    progCode (WaryBot k) = pSearch k (templateCode phiW) (pConst 1) (pConst 0) := by
  rw [WaryBot, progCode_search_noSnap _ _ _ _ rfl]; simp [phiW, actCode]
/-- Just's stored template is ABSTRACTED (its guard freezes the budget-carrying `DupocBot k`): the code stores
`templateCodeAt (phiJ k) k`, a constant (route (c) made generic, 2026-10-01); the sentence consulted is still
`guardCode (templateCode (phiJ k)) me opp` (`guardCodeB_templateCodeAt`, `search_then_at`). -/
lemma progCode_JustBot (k : ℕ) :
    progCode (JustBot k) = pSearch k (templateCodeAt (phiJ k) k) (pConst 0) (pConst 1) := by
  simp [JustBot, phiJ, actCode]
lemma progCode_PrudentBot_search (k : ℕ) :
    progCode (PrudentBot k) =
      pSearch k (templateCode phiPo) (pSearch k (templateCode phiPi) (pConst 0) (pConst 1)) (pConst 1) := by
  rw [PrudentBot, progCode_search_noSnap _ _ _ _ rfl, progCode_search_noSnap _ _ _ _ rfl]; simp [phiPo, phiPi, actCode]

lemma progCode_botCB : progCode (PD.Prog.bot CooperateBot) = pBot (pConst 0) := by simp [CooperateBot, actCode]
lemma progCode_botDB : progCode (PD.Prog.bot DefectBot) = pBot (pConst 1) := by simp [DefectBot, actCode]
lemma progCode_CB : progCode CooperateBot = pConst 0 := by simp [CooperateBot, actCode]
lemma progCode_DB : progCode DefectBot = pConst 1 := by simp [DefectBot, actCode]

lemma properPlayer_GuardianBot (k : ℕ) : ProperPlayer (GuardianBot k) := ⟨by simp [GuardianBot], by simp [GuardianBot]⟩
lemma properPlayer_CupodBot (k : ℕ) : ProperPlayer (CupodBot k) := ⟨by simp [CupodBot], by simp [CupodBot]⟩
lemma properPlayer_CupodTrollBot (k : ℕ) : ProperPlayer (CupodTrollBot k) :=
  ⟨by simp [CupodTrollBot], by simp [CupodTrollBot]⟩
lemma properPlayer_WaryBot (k : ℕ) : ProperPlayer (WaryBot k) := ⟨by simp [WaryBot], by simp [WaryBot]⟩
lemma properPlayer_JustBot (k : ℕ) : ProperPlayer (JustBot k) := ⟨by simp [JustBot], by simp [JustBot]⟩
lemma properPlayer_PrudentBot (k : ℕ) : ProperPlayer (PrudentBot k) := ⟨by simp [PrudentBot], by simp [PrudentBot]⟩
lemma properPlayer_botCB : ProperPlayer (PD.Prog.bot CooperateBot) := properPlayer_bot _
lemma properPlayer_botDB : ProperPlayer (PD.Prog.bot DefectBot) := properPlayer_bot _

end codes

/-! ### 5. The search clause on engine codes, and the search-free probers -/

section steps

/-- The else branch of a search node on an engine template. -/
theorem search_else {k n a x y : ℕ} (φ : PD.Formula) {p q : ℕ}
    (hn : ¬ LenBox TAct k (guardCode (templateCode φ) x y)) (h : EvalGraph n x y q a)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    EvalGraph (n + 1) x y (pSearch k (templateCode φ) p q) a :=
  (EvalGraph.search_iff₆ (isSemiformula_templateCode φ)).mpr (Or.inr ⟨hn, h⟩)

/-- The then branch of a search node on an engine template. -/
theorem search_then {k n a x y : ℕ} (φ : PD.Formula) {p q : ℕ}
    (hy : LenBox TAct k (guardCode (templateCode φ) x y)) (h : EvalGraph n x y p a)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    EvalGraph (n + 1) x y (pSearch k (templateCode φ) p q) a :=
  (EvalGraph.search_iff₆ (isSemiformula_templateCode φ)).mpr (Or.inl ⟨hy, h⟩)

/-- The search clauses on a STORED (budget-abstracted) template `templateCodeAt φ k`: the consulted sentence is
the unabstracted guard (`guardCodeB_templateCodeAt`), so the hypotheses are those of `search_then`/`search_else`. -/
theorem search_else_at {k n a x y : ℕ} (φ : PD.Formula) {p q : ℕ}
    (hn : ¬ LenBox TAct k (guardCode (templateCode φ) x y)) (h : EvalGraph n x y q a)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    EvalGraph (n + 1) x y (pSearch k (templateCodeAt φ k) p q) a :=
  (EvalGraph.search_iff_at φ hφ).mpr (Or.inr ⟨hn, h⟩)

theorem search_then_at {k n a x y : ℕ} (φ : PD.Formula) {p q : ℕ}
    (hy : LenBox TAct k (guardCode (templateCode φ) x y)) (h : EvalGraph n x y p a)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    EvalGraph (n + 1) x y (pSearch k (templateCodeAt φ k) p q) a :=
  (EvalGraph.search_iff_at φ hφ).mpr (Or.inl ⟨hy, h⟩)

/-- A search node whose two branches AGREE plays that value whatever the verdict. -/
theorem search_either {k n a x y : ℕ} (φ : PD.Formula) {p q : ℕ}
    (hp : EvalGraph n x y p a) (hq : EvalGraph n x y q a) (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    EvalGraph (n + 1) x y (pSearch k (templateCode φ) p q) a := by
  by_cases hg : LenBox TAct k (guardCode (templateCode φ) x y)
  · exact search_then φ hg hp
  · exact search_else φ hg hq

theorem search_either_at {k n a x y : ℕ} (φ : PD.Formula) {p q : ℕ}
    (hp : EvalGraph n x y p a) (hq : EvalGraph n x y q a) (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    EvalGraph (n + 1) x y (pSearch k (templateCodeAt φ k) p q) a := by
  by_cases hg : LenBox TAct k (guardCode (templateCode φ) x y)
  · exact search_then_at φ hg hp
  · exact search_else_at φ hg hq

lemma bot_const_play (n me opp a : ℕ) : EvalGraph (n + 1 + 1) me opp (pBot (pConst a)) a :=
  EvalGraph.bot_iff.mpr (EvalGraph.const_iff.mpr rfl)

lemma const_play (n me opp a : ℕ) : EvalGraph (n + 1) me opp (pConst a) a := EvalGraph.const_iff.mpr rfl

/-- `MirrorBot` copies the opponent's play against it. -/
theorem mirror_copies {x a n : ℕ} (h : EvalGraph n x (progCode MirrorBot) x a) :
    EvalGraph (n + 1) (progCode MirrorBot) x (progCode MirrorBot) a := by
  rw [progCode_MirrorBot, Mirror, EvalGraph.sim_iff, substCode_opp, substCode_self]
  exact h

/-- `DBot` defects against `x` when `x` cooperates with `.bot DefectBot`. -/
theorem dbot_D_of_probe_C {x n : ℕ} (h : EvalGraph n x (pBot (pConst 1)) x 0) :
    EvalGraph (n + 1 + 1) (progCode DBot) x (progCode DBot) 1 := by
  simp only [DBot, DefectBot, progCode_ite, progCode_sim, progCode_opp, progCode_bot, progCode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨0, ?_, Or.inl ⟨rfl, const_play _ _ _ _⟩⟩
  rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
  exact h

/-- `DBot` cooperates with `x` when `x` defects against `.bot DefectBot`. -/
theorem dbot_C_of_probe_D {x n : ℕ} (h : EvalGraph n x (pBot (pConst 1)) x 1) :
    EvalGraph (n + 1 + 1) (progCode DBot) x (progCode DBot) 0 := by
  simp only [DBot, DefectBot, progCode_ite, progCode_sim, progCode_opp, progCode_bot, progCode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨1, ?_, Or.inr ⟨by decide, const_play _ _ _ _⟩⟩
  rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
  exact h

/-- `TitForTatBot` cooperates with `x` when `x` cooperates with `.bot CooperateBot`. -/
theorem tft_C_of_probe_C {x n : ℕ} (h : EvalGraph n x (pBot (pConst 0)) x 0) :
    EvalGraph (n + 1 + 1) (progCode TitForTatBot) x (progCode TitForTatBot) 0 := by
  simp only [TitForTatBot, CooperateBot, progCode_ite, progCode_sim, progCode_opp, progCode_bot, progCode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨0, ?_, Or.inl ⟨rfl, const_play _ _ _ _⟩⟩
  rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
  exact h

/-- `TitForTatBot` defects against `x` when `x` defects against `.bot CooperateBot`. -/
theorem tft_D_of_probe_D {x n : ℕ} (h : EvalGraph n x (pBot (pConst 0)) x 1) :
    EvalGraph (n + 1 + 1) (progCode TitForTatBot) x (progCode TitForTatBot) 1 := by
  simp only [TitForTatBot, CooperateBot, progCode_ite, progCode_sim, progCode_opp, progCode_bot, progCode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨1, ?_, Or.inr ⟨by decide, const_play _ _ _ _⟩⟩
  rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
  exact h

/-- `OBot` defects against `x` when `x` does not cooperate with `.bot CooperateBot`. -/
theorem obot_D_of_probe1_D {x n r : ℕ} (h : EvalGraph n x (pBot (pConst 0)) x r) (hr : r ≠ 0) :
    EvalGraph (n + 1 + 1) (progCode OBot) x (progCode OBot) 1 := by
  simp only [OBot, CooperateBot, DefectBot, progCode_ite, progCode_sim, progCode_opp, progCode_bot, progCode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨r, ?_, Or.inr ⟨hr, const_play _ _ _ _⟩⟩
  rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
  exact h


/-- `OBot` cooperates with `x` when `x` cooperates with both `.bot CooperateBot` and `.bot DefectBot`. -/
theorem obot_C_of_probes {x n : ℕ} (h1 : EvalGraph n x (pBot (pConst 0)) x 0)
    (h2 : EvalGraph n x (pBot (pConst 1)) x 0) :
    EvalGraph (n + 1 + 1 + 1) (progCode OBot) x (progCode OBot) 0 := by
  simp only [OBot, CooperateBot, DefectBot, progCode_ite, progCode_sim, progCode_opp, progCode_bot, progCode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨0, ?_, Or.inl ⟨rfl, ?_⟩⟩
  · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
    exact EvalGraph.mono _ _ _ _ _ h1
  · rw [EvalGraph.ite_iff]
    refine ⟨0, ?_, Or.inl ⟨rfl, const_play _ _ _ _⟩⟩
    rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
    exact h2

/-- `OBot` defects against `x` when `x` cooperates with `.bot CooperateBot` but defects against
`.bot DefectBot`. -/
theorem obot_D_of_probes {x n : ℕ} (h1 : EvalGraph n x (pBot (pConst 0)) x 0)
    (h2 : EvalGraph n x (pBot (pConst 1)) x 1) :
    EvalGraph (n + 1 + 1 + 1) (progCode OBot) x (progCode OBot) 1 := by
  simp only [OBot, CooperateBot, DefectBot, progCode_ite, progCode_sim, progCode_opp, progCode_bot, progCode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨0, ?_, Or.inl ⟨rfl, ?_⟩⟩
  · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
    exact EvalGraph.mono _ _ _ _ _ h1
  · rw [EvalGraph.ite_iff]
    refine ⟨1, ?_, Or.inr ⟨by decide, const_play _ _ _ _⟩⟩
    rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
    exact h2

/-- `OBot` defects against `x` whenever `x` defects against `.bot DefectBot`, whatever `x` does
against `.bot CooperateBot` (as long as it plays). -/
theorem obot_D_of_any {x n r : ℕ} (h1 : EvalGraph n x (pBot (pConst 0)) x r)
    (h2 : EvalGraph n x (pBot (pConst 1)) x 1) :
    EvalGraph (n + 1 + 1 + 1) (progCode OBot) x (progCode OBot) 1 := by
  by_cases hr : r = 0
  · subst hr; exact obot_D_of_probes h1 h2
  · exact EvalGraph.mono _ _ _ _ _ (obot_D_of_probe1_D h1 hr)

/-- `EBot` defects against `x` when `x` cooperates with `.bot DefectBot`. -/
theorem ebot_D_of_probe1_C {x n : ℕ} (h : EvalGraph n x (pBot (pConst 1)) x 0) :
    EvalGraph (n + 1 + 1) (progCode EBot) x (progCode EBot) 1 := by
  simp only [EBot, CooperateBot, DefectBot, MirrorBot, progCode_ite, progCode_sim, progCode_opp, progCode_self, progCode_bot,
    progCode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨0, ?_, Or.inl ⟨rfl, const_play _ _ _ _⟩⟩
  rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
  exact h

/-- `EBot` cooperates with `x` when `x` defects against `.bot DefectBot` and cooperates with
`.bot CooperateBot`. -/
theorem ebot_C_of_probes {x n : ℕ} (h1 : EvalGraph n x (pBot (pConst 1)) x 1)
    (h2 : EvalGraph n x (pBot (pConst 0)) x 0) :
    EvalGraph (n + 1 + 1 + 1) (progCode EBot) x (progCode EBot) 0 := by
  simp only [EBot, CooperateBot, DefectBot, MirrorBot, progCode_ite, progCode_sim, progCode_opp, progCode_self, progCode_bot,
    progCode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨1, ?_, Or.inr ⟨by decide, ?_⟩⟩
  · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
    exact EvalGraph.mono _ _ _ _ _ h1
  · rw [EvalGraph.ite_iff]
    refine ⟨0, ?_, Or.inl ⟨rfl, const_play _ _ _ _⟩⟩
    rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
    exact h2

/-- `EBot` defects against `x` when `x` defects against all three frozen probes `.bot DefectBot`,
`.bot CooperateBot`, `.bot MirrorBot` (the end of its ladder). -/
theorem ebot_D_of_probes_D {x n : ℕ} (h1 : EvalGraph n x (pBot (pConst 1)) x 1)
    (h2 : EvalGraph n x (pBot (pConst 0)) x 1) (h3 : EvalGraph n x (pBot Mirror) x 1) :
    EvalGraph (n + 1 + 1 + 1 + 1) (progCode EBot) x (progCode EBot) 1 := by
  simp only [EBot, CooperateBot, DefectBot, MirrorBot, progCode_ite, progCode_sim, progCode_opp, progCode_self, progCode_bot,
    progCode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨1, ?_, Or.inr ⟨by decide, ?_⟩⟩
  · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
    exact EvalGraph.mono_le (by omega) h1
  · rw [EvalGraph.ite_iff]
    refine ⟨1, ?_, Or.inr ⟨by decide, ?_⟩⟩
    · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
      exact EvalGraph.mono_le (by omega) h2
    · rw [EvalGraph.ite_iff]
      refine ⟨1, ?_, Or.inr ⟨by decide, const_play _ _ _ _⟩⟩
      rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
      exact h3

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
lemma templateCode_ne_of_ne {φ ψ : PD.Formula} (h : template φ ≠ template ψ)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) (hψ : noSelfIdxF ψ = true := by noSelfIdx_tac) :
    templateCode φ ≠ templateCode ψ := by
  rw [templateCode_eq_quote_template φ hφ, templateCode_eq_quote_template ψ hψ]
  intro e
  exact h ((Sentence.quote_inj_iff (V := ℕ)).mp e)

/-- **Semantic disjointness of templates**: two guards whose realizations differ in truth at ONE
frame have different template codes (equal codes give equal realized sentences, `quote_sentenceAt` +
quote injectivity). -/
lemma templateCode_ne_of_models {φ ψ : PD.Formula} (me opp : PD.Prog) (h1 : ℕ↓[LAct] ⊧ sentenceAt me opp φ)
    (h2 : ¬ ℕ↓[LAct] ⊧ sentenceAt me opp ψ)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) (hψ : noSelfIdxF ψ = true := by noSelfIdx_tac) :
    templateCode φ ≠ templateCode ψ := by
  intro e
  apply h2
  have hq : (⌜sentenceAt me opp φ⌝ : ℕ) = ⌜sentenceAt me opp ψ⌝ := by
    rw [quote_sentenceAt me opp φ hφ, quote_sentenceAt me opp ψ hψ, e]
  rw [← (Sentence.quote_inj_iff (V := ℕ)).mp hq]
  exact h1

/-- The same separation with the first template STORED (budget-abstracted, `templateCodeAt φ k`): equal stored
codes would give equal consulted sentences (`guardCodeB_templateCodeAt`), hence equal truth values. -/
lemma templateCodeAt_ne_templateCode_of_models {φ ψ : PD.Formula} (k : ℕ) (me opp : PD.Prog)
    (h1 : ℕ↓[LAct] ⊧ sentenceAt me opp φ) (h2 : ¬ ℕ↓[LAct] ⊧ sentenceAt me opp ψ)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) (hψ : noSelfIdxF ψ = true := by noSelfIdx_tac) :
    templateCodeAt φ k ≠ templateCode ψ := by
  intro e
  apply h2
  have hg : guardCode (templateCode φ) (progCode me) (progCode opp) = guardCode (templateCode ψ) (progCode me) (progCode opp) := by
    rw [← guardCodeB_templateCodeAt φ (progCode me) (progCode opp) k hφ, e,
      guardCodeB_of_template (isSemiformula_templateCode ψ hψ)]
  have hq : (⌜sentenceAt me opp φ⌝ : ℕ) = ⌜sentenceAt me opp ψ⌝ := by
    rw [quote_sentenceAt me opp φ hφ, quote_sentenceAt me opp ψ hψ, hg]
  rw [← (Sentence.quote_inj_iff (V := ℕ)).mp hq]
  exact h1

end disjoint

/-! ### 7. The searchers' plays from a verdict on their guard -/

section searchers

/-- Guardian cooperates with an opponent that cooperates with `.bot CooperateBot`. -/
theorem guardian_C_of_probe (k : ℕ) {opp : PD.Prog} (hopp : ProperPlayer opp) {N : ℕ}
    (h : EvalGraph N (progCode opp) (pBot (pConst 0)) (progCode opp) 0) :
    EvalGraph 2 (progCode (GuardianBot k)) (progCode opp) (progCode (GuardianBot k)) 0 := by
  have hn := not_found_opp_bot (properPlayer_GuardianBot k) hopp (P := CooperateBot) rfl .D (b := .C) (by decide)
    (by rw [progCode_CB]; exact h) k
  rw [progCode_GuardianBot] at hn ⊢
  exact search_else phiG hn (const_play _ _ _ _)

/-- Guardian defects against an opponent when it FINDS its guard. -/
theorem guardian_D_of_found (k : ℕ) {opp : PD.Prog}
    (hy : LenBox TAct k (guardCode (templateCode phiG) (progCode (GuardianBot k)) (progCode opp))) :
    EvalGraph 2 (progCode (GuardianBot k)) (progCode opp) (progCode (GuardianBot k)) 1 := by
  rw [progCode_GuardianBot] at hy ⊢
  exact search_then phiG hy (const_play _ _ _ _)

/-- Guardian cooperates with `.bot CooperateBot`. -/
theorem snd_GuardianBot_vs_botCB (k : ℕ) :
    EvalGraph 2 (progCode (GuardianBot k)) (pBot (pConst 0)) (progCode (GuardianBot k)) 0 := by
  have := guardian_C_of_probe k (opp := .bot CooperateBot) properPlayer_botCB (N := 2)
    (by rw [progCode_botCB]; exact bot_const_play 0 _ _ _)
  rwa [progCode_botCB] at this

/-- Cupod cooperates with an opponent that cooperates with it. -/
theorem cupod_C_of_probe (k : ℕ) {opp : PD.Prog} (hopp : ProperPlayer opp) {N : ℕ}
    (h : EvalGraph N (progCode opp) (progCode (CupodBot k)) (progCode opp) 0) :
    EvalGraph 2 (progCode (CupodBot k)) (progCode opp) (progCode (CupodBot k)) 0 := by
  have hn := not_found_opp_self (properPlayer_CupodBot k) hopp .D (b := .C) (by decide) h k
  rw [progCode_CupodBot] at hn ⊢
  exact search_else phiCu hn (const_play _ _ _ _)

/-- Cupod cooperates with `CooperateBot`. -/
theorem snd_CupodBot_vs_CooperateBot_aux (k : ℕ) :
    EvalGraph 2 (progCode (CupodBot k)) (progCode CooperateBot) (progCode (CupodBot k)) 0 :=
  cupod_C_of_probe k sfp_CooperateBot.1 (by rw [progCode_CB]; exact const_play 0 _ _ 0)

/-- Cupod cooperates with `.bot CooperateBot`. -/
theorem snd_CupodBot_vs_botCB (k : ℕ) :
    EvalGraph 2 (progCode (CupodBot k)) (pBot (pConst 0)) (progCode (CupodBot k)) 0 := by
  have := cupod_C_of_probe k (opp := .bot CooperateBot) properPlayer_botCB (N := 2)
    (by rw [progCode_botCB]; exact bot_const_play 0 _ _ _)
  rwa [progCode_botCB] at this

/-- Dupoc defects against an opponent that defects against it. -/
theorem dupoc_D_of_probe (k : ℕ) {opp : PD.Prog} (hopp : ProperPlayer opp) {N : ℕ}
    (h : EvalGraph N (progCode opp) (progCode (DupocBot k)) (progCode opp) 1) :
    EvalGraph 2 (progCode (DupocBot k)) (progCode opp) (progCode (DupocBot k)) 1 := by
  have hn := not_found_opp_self (properPlayer_DupocBot k) hopp .C (b := .D) (by decide) h k
  rw [progCode_DupocBot_search] at hn ⊢
  exact search_else phiDu hn (const_play _ _ _ _)

/-- Dupoc's BODY, in any proper frame whose opponent defects against the frame's `me`, defects
(for the frozen snapshot `.bot (DupocBot k)` of JustBot's guard). -/
theorem dupoc_body_D_of_probe (k : ℕ) {me opp : PD.Prog} (hme : ProperPlayer me) (hopp : ProperPlayer opp) {N : ℕ}
    (h : EvalGraph N (progCode opp) (progCode me) (progCode opp) 1) :
    EvalGraph 2 (progCode me) (progCode opp) (progCode (DupocBot k)) 1 := by
  have hn := not_found_opp_self hme hopp .C (b := .D) (by decide) h k
  rw [progCode_DupocBot_search]
  exact search_else phiDu hn (const_play _ _ _ _)

/-- Dupoc's body always plays in a proper frame (fuel 2), whatever the verdict. -/
theorem dupoc_body_total (k : ℕ) (me opp : PD.Prog) :
    ∃ r, EvalGraph 2 (progCode me) (progCode opp) (progCode (DupocBot k)) r := by
  rw [progCode_DupocBot_search]
  by_cases hg : LenBox TAct k (guardCode (templateCode phiDu) (progCode me) (progCode opp))
  · exact ⟨0, search_then phiDu hg (const_play _ _ _ _)⟩
  · exact ⟨1, search_else phiDu hg (const_play _ _ _ _)⟩

/-- Dupoc defects against `.bot DefectBot`. -/
theorem snd_DupocBot_vs_botDB (k : ℕ) :
    EvalGraph 2 (progCode (DupocBot k)) (pBot (pConst 1)) (progCode (DupocBot k)) 1 := by
  have := dupoc_D_of_probe k (opp := .bot DefectBot) properPlayer_botDB (N := 2)
    (by rw [progCode_botDB]; exact bot_const_play 0 _ _ _)
  rwa [progCode_botDB] at this

/-- CupodTroll cooperates with any opponent whose code is not `CupodBot k`'s. -/
theorem ctb_C_of_ne (k : ℕ) {opp : PD.Prog} (hopp : ProperPlayer opp)
    (hne : progCode opp ≠ progCode (CupodBot k)) :
    EvalGraph 2 (progCode (CupodTrollBot k)) (progCode opp) (progCode (CupodTrollBot k)) 0 := by
  have hn := not_found_eq_opp (properPlayer_CupodTrollBot k) hopp (Q := CupodBot k) rfl hne k
  rw [progCode_CupodTrollBot] at hn ⊢
  exact search_else_at (phiT k) hn (const_play _ _ _ _)

/-- CupodTroll cooperates with `.bot CooperateBot`. -/
theorem snd_CupodTrollBot_vs_botCB (k : ℕ) :
    EvalGraph 2 (progCode (CupodTrollBot k)) (pBot (pConst 0)) (progCode (CupodTrollBot k)) 0 := by
  have := ctb_C_of_ne k (opp := .bot CooperateBot) properPlayer_botCB
    (by rw [progCode_botCB, progCode_CupodBot]; exact pBot_ne_pSearch _ _ _ _ _)
  rwa [progCode_botCB] at this

/-- CupodTroll cooperates with `.bot DefectBot`. -/
theorem snd_CupodTrollBot_vs_botDB (k : ℕ) :
    EvalGraph 2 (progCode (CupodTrollBot k)) (pBot (pConst 1)) (progCode (CupodTrollBot k)) 0 := by
  have := ctb_C_of_ne k (opp := .bot DefectBot) properPlayer_botDB
    (by rw [progCode_botDB, progCode_CupodBot]; exact pBot_ne_pSearch _ _ _ _ _)
  rwa [progCode_botDB] at this

/-- Wary cooperates with an opponent that cooperates with it (the `.neg` guard is false). -/
theorem wary_C_of_probe (k : ℕ) {opp : PD.Prog} (hopp : ProperPlayer opp) {N : ℕ}
    (h : EvalGraph N (progCode opp) (progCode (WaryBot k)) (progCode opp) 0) :
    EvalGraph 2 (progCode (WaryBot k)) (progCode opp) (progCode (WaryBot k)) 0 := by
  have hn := not_found_neg_opp_self (properPlayer_WaryBot k) hopp .C h k
  rw [progCode_WaryBot] at hn ⊢
  exact search_else phiW hn (const_play _ _ _ _)

/-- Wary cooperates with `.bot CooperateBot`. -/
theorem snd_WaryBot_vs_botCB (k : ℕ) :
    EvalGraph 2 (progCode (WaryBot k)) (pBot (pConst 0)) (progCode (WaryBot k)) 0 := by
  have := wary_C_of_probe k (opp := .bot CooperateBot) properPlayer_botCB (N := 2)
    (by rw [progCode_botCB]; exact bot_const_play 0 _ _ _)
  rwa [progCode_botCB] at this

/-- Just defects against an opponent that defects against `.bot (DupocBot k)`. -/
theorem just_D_of_probe (k : ℕ) {opp : PD.Prog} (hopp : ProperPlayer opp) {N : ℕ}
    (h : EvalGraph N (progCode opp) (pBot (progCode (DupocBot k))) (progCode opp) 1) :
    EvalGraph 2 (progCode (JustBot k)) (progCode opp) (progCode (JustBot k)) 1 := by
  have hn := not_found_opp_bot (properPlayer_JustBot k) hopp (P := DupocBot k) rfl .C (b := .D) (by decide) h k
  rw [progCode_JustBot] at hn ⊢
  exact search_else_at (phiJ k) hn (const_play _ _ _ _)

/-- Prudent defects against an opponent that defects against it (the outer guard fails). -/
theorem prudent_D_of_probe (k : ℕ) {opp : PD.Prog} (hopp : ProperPlayer opp) {N : ℕ}
    (h : EvalGraph N (progCode opp) (progCode (PrudentBot k)) (progCode opp) 1) :
    EvalGraph 2 (progCode (PrudentBot k)) (progCode opp) (progCode (PrudentBot k)) 1 := by
  have hn := not_found_opp_self (properPlayer_PrudentBot k) hopp .C (b := .D) (by decide) h k
  rw [progCode_PrudentBot_search] at hn ⊢
  exact search_else phiPo hn (const_play _ _ _ _)

/-- Prudent defects against an opponent that cooperates with `.bot DefectBot` (the prudence guard
fails; the outer verdict is irrelevant). -/
theorem prudent_D_of_inner (k : ℕ) {opp : PD.Prog} (hopp : ProperPlayer opp) {N : ℕ}
    (h : EvalGraph N (progCode opp) (pBot (pConst 1)) (progCode opp) 0) :
    EvalGraph 3 (progCode (PrudentBot k)) (progCode opp) (progCode (PrudentBot k)) 1 := by
  have hn := not_found_opp_bot (properPlayer_PrudentBot k) hopp (P := DefectBot) rfl .D (b := .C) (by decide)
    (by rw [progCode_DB]; exact h) k
  rw [progCode_PrudentBot_search] at hn ⊢
  exact search_either phiPo (search_else phiPi hn (const_play _ _ _ _)) (const_play _ _ _ _)

/-- Prudent defects against `.bot DefectBot` and against `.bot CooperateBot`. -/
theorem snd_PrudentBot_vs_botDB (k : ℕ) :
    EvalGraph 2 (progCode (PrudentBot k)) (pBot (pConst 1)) (progCode (PrudentBot k)) 1 := by
  have := prudent_D_of_probe k (opp := .bot DefectBot) properPlayer_botDB (N := 2)
    (by rw [progCode_botDB]; exact bot_const_play 0 _ _ _)
  rwa [progCode_botDB] at this

theorem snd_PrudentBot_vs_botCB (k : ℕ) :
    EvalGraph 3 (progCode (PrudentBot k)) (pBot (pConst 0)) (progCode (PrudentBot k)) 1 := by
  have := prudent_D_of_inner k (opp := .bot CooperateBot) properPlayer_botCB (N := 2)
    (by rw [progCode_botCB]; exact bot_const_play 0 _ _ _)
  rwa [progCode_botCB] at this

end searchers

/-! ### 8. Template disjointness for the `.eq` guard against the zoo -/

section templates

/-- Guardian's and Cupod's templates differ: at the frame `(TitForTatBot, DBot)`, "DBot plays D
against `.bot CooperateBot`" is true while "DBot plays D against TitForTatBot" is false. -/
lemma templateCode_phiG_ne_phiCu : templateCode phiG ≠ templateCode phiCu := by
  refine templateCode_ne_of_models TitForTatBot DBot ?_ ?_
  · rw [← sentenceAt_subst TitForTatBot DBot sfp_TitForTatBot.1 sfp_DBot.1 _ rfl]
    show ℕ↓[LAct] ⊧ sentenceAt TitForTatBot DBot (.plays DBot (.bot CooperateBot) .D)
    rw [models_sentenceAt_plays _ _ _ _ _ sfp_DBot.1 properPlayer_botCB, progCode_botCB]
    exact ⟨4, dbot_D_of_probe_C (bot_const_play 0 _ _ 0)⟩
  · rw [← sentenceAt_subst TitForTatBot DBot sfp_TitForTatBot.1 sfp_DBot.1 _ rfl]
    show ¬ ℕ↓[LAct] ⊧ sentenceAt TitForTatBot DBot (.plays DBot TitForTatBot .D)
    rw [models_sentenceAt_plays _ _ _ _ _ sfp_DBot.1 sfp_TitForTatBot.1]
    rintro ⟨N, hN⟩
    have hC : EvalGraph 6 (progCode DBot) (progCode TitForTatBot) (progCode DBot) 0 :=
      dbot_C_of_probe_D (tft_D_of_probe_D (bot_const_play 0 _ _ 1))
    exact absurd (EvalGraph.unique' hN hC) (by decide)

/-- CupodTroll's and Cupod's templates differ: at the frame `(CooperateBot, CupodBot k)`,
"the opponent IS `CupodBot k`" is true while "the opponent defects against CooperateBot" is false. -/
lemma models_phiT_at_CB_Cupod (k : ℕ) : ℕ↓[LAct] ⊧ sentenceAt CooperateBot (CupodBot k) (phiT k) := by
  rw [← sentenceAt_subst CooperateBot (CupodBot k) sfp_CooperateBot.1 (properPlayer_CupodBot k) _ rfl]
  show ℕ↓[LAct] ⊧ sentenceAt CooperateBot (CupodBot k) (.eq (CupodBot k) (CupodBot k))
  rw [models_sentenceAt_eq _ _ _ _ (properPlayer_CupodBot k)]

lemma not_models_phiCu_at_CB_Cupod (k : ℕ) : ¬ ℕ↓[LAct] ⊧ sentenceAt CooperateBot (CupodBot k) phiCu := by
  rw [← sentenceAt_subst CooperateBot (CupodBot k) sfp_CooperateBot.1 (properPlayer_CupodBot k) _ rfl]
  show ¬ ℕ↓[LAct] ⊧ sentenceAt CooperateBot (CupodBot k) (.plays (CupodBot k) CooperateBot .D)
  rw [models_sentenceAt_plays _ _ _ _ _ (properPlayer_CupodBot k) sfp_CooperateBot.1]
  rintro ⟨N, hN⟩
  exact absurd (EvalGraph.unique' hN (snd_CupodBot_vs_CooperateBot_aux k)) (by decide)

lemma templateCode_phiT_ne_phiCu (k : ℕ) : templateCode (phiT k) ≠ templateCode phiCu :=
  templateCode_ne_of_models CooperateBot (CupodBot k) (models_phiT_at_CB_Cupod k) (not_models_phiCu_at_CB_Cupod k)

/-- CupodTroll's STORED template (abstracted) differs from Cupod's. -/
lemma templateCodeAt_phiT_ne_phiCu (k : ℕ) : templateCodeAt (phiT k) k ≠ templateCode phiCu :=
  templateCodeAt_ne_templateCode_of_models k CooperateBot (CupodBot k) (models_phiT_at_CB_Cupod k)
    (not_models_phiCu_at_CB_Cupod k)

/-- Wary's and Cupod's templates differ: at the frame `(MirrorBot, MirrorBot)` (a non-terminating
match), "the opponent does NOT cooperate" is true while "the opponent defects" is false. -/
lemma templateCode_phiW_ne_phiCu : templateCode phiW ≠ templateCode phiCu := by
  refine templateCode_ne_of_models MirrorBot MirrorBot ?_ ?_
  · rw [← sentenceAt_subst MirrorBot MirrorBot sfp_MirrorBot.1 sfp_MirrorBot.1 _ rfl]
    show ℕ↓[LAct] ⊧ sentenceAt MirrorBot MirrorBot (.neg (.plays MirrorBot MirrorBot .C))
    rw [models_sentenceAt_neg, models_sentenceAt_plays _ _ _ _ _ sfp_MirrorBot.1 sfp_MirrorBot.1, progCode_MirrorBot]
    rintro ⟨N, hN⟩
    exact mirror_vs_mirror N _ hN
  · rw [← sentenceAt_subst MirrorBot MirrorBot sfp_MirrorBot.1 sfp_MirrorBot.1 _ rfl]
    show ¬ ℕ↓[LAct] ⊧ sentenceAt MirrorBot MirrorBot (.plays MirrorBot MirrorBot .D)
    rw [models_sentenceAt_plays _ _ _ _ _ sfp_MirrorBot.1 sfp_MirrorBot.1, progCode_MirrorBot]
    rintro ⟨N, hN⟩
    exact mirror_vs_mirror N _ hN

lemma progCode_GuardianBot_ne_CupodBot (k : ℕ) : progCode (GuardianBot k) ≠ progCode (CupodBot k) := by
  rw [progCode_GuardianBot, progCode_CupodBot]
  intro e
  exact templateCode_phiG_ne_phiCu (pSearch_inj e).2.1

lemma progCode_CupodTrollBot_ne_CupodBot (k : ℕ) : progCode (CupodTrollBot k) ≠ progCode (CupodBot k) := by
  rw [progCode_CupodTrollBot, progCode_CupodBot]
  intro e
  exact templateCodeAt_phiT_ne_phiCu k (pSearch_inj e).2.1

lemma progCode_WaryBot_ne_CupodBot (k : ℕ) : progCode (WaryBot k) ≠ progCode (CupodBot k) := by
  rw [progCode_WaryBot, progCode_CupodBot]
  intro e
  exact templateCode_phiW_ne_phiCu (pSearch_inj e).2.1

lemma progCode_PrudentBot_ne_CupodBot (k : ℕ) : progCode (PrudentBot k) ≠ progCode (CupodBot k) := by
  rw [progCode_PrudentBot_search, progCode_CupodBot]
  intro e
  exact pConst_ne_pSearch _ _ _ _ _ (pSearch_inj e).2.2.1.symm

lemma progCode_CB_ne_CupodBot (k : ℕ) : progCode CooperateBot ≠ progCode (CupodBot k) := by
  rw [progCode_CB, progCode_CupodBot]; exact pConst_ne_pSearch _ _ _ _ _
lemma progCode_DB_ne_CupodBot (k : ℕ) : progCode DefectBot ≠ progCode (CupodBot k) := by
  rw [progCode_DB, progCode_CupodBot]; exact pConst_ne_pSearch _ _ _ _ _
lemma progCode_Mirror_ne_CupodBot (k : ℕ) : progCode MirrorBot ≠ progCode (CupodBot k) := by
  rw [progCode_MirrorBot, Mirror, progCode_CupodBot]; exact pSim_ne_pSearch _ _ _ _ _ _
lemma progCode_DBot_ne_CupodBot (k : ℕ) : progCode DBot ≠ progCode (CupodBot k) := by
  simp only [DBot, DefectBot, progCode_ite, progCode_sim, progCode_opp, progCode_bot, progCode_const, progCode_CupodBot]
  exact pIte_ne_pSearch _ _ _ _ _ _ _ _
lemma progCode_EBot_ne_CupodBot (k : ℕ) : progCode EBot ≠ progCode (CupodBot k) := by
  simp only [EBot, DefectBot, CooperateBot, MirrorBot, progCode_ite, progCode_sim, progCode_opp, progCode_self, progCode_bot,
    progCode_const, progCode_CupodBot]
  exact pIte_ne_pSearch _ _ _ _ _ _ _ _
lemma progCode_OBot_ne_CupodBot (k : ℕ) : progCode OBot ≠ progCode (CupodBot k) := by
  simp only [OBot, DefectBot, CooperateBot, progCode_ite, progCode_sim, progCode_opp, progCode_bot, progCode_const, progCode_CupodBot]
  exact pIte_ne_pSearch _ _ _ _ _ _ _ _
lemma progCode_TFT_ne_CupodBot (k : ℕ) : progCode TitForTatBot ≠ progCode (CupodBot k) := by
  simp only [TitForTatBot, CooperateBot, progCode_ite, progCode_sim, progCode_opp, progCode_bot, progCode_const, progCode_CupodBot]
  exact pIte_ne_pSearch _ _ _ _ _ _ _ _

end templates

/-! ### 9. The SND cells: the guard is false, the else branch by soundness -/

section sndCells

/-! #### GuardianBot (6 of 8; `× EBot` and `× OBot` need a positive sub-fact, §11) -/

/-- `GuardianBot × CupodBot = (C, C)` (engine `llm_outcome_GuardianBot_vs_CupodBot`, pad 2), every `k`. -/
theorem snd_GuardianBot_vs_CupodBot (k : ℕ) :
    EvalGraph 2 (progCode (GuardianBot k)) (progCode (CupodBot k)) (progCode (GuardianBot k)) (actCode .C) ∧
    EvalGraph 2 (progCode (CupodBot k)) (progCode (GuardianBot k)) (progCode (CupodBot k)) (actCode .C) := by
  have hG := guardian_C_of_probe k (properPlayer_CupodBot k) (snd_CupodBot_vs_botCB k)
  exact ⟨hG, cupod_C_of_probe k (properPlayer_GuardianBot k) hG⟩

/-- `GuardianBot × CupodTrollBot = (C, C)` (engine `llm_outcome_GuardianBot_vs_CupodTrollBot`, pad 2). -/
theorem snd_GuardianBot_vs_CupodTrollBot (k : ℕ) :
    EvalGraph 2 (progCode (GuardianBot k)) (progCode (CupodTrollBot k)) (progCode (GuardianBot k)) (actCode .C) ∧
    EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (GuardianBot k)) (progCode (CupodTrollBot k)) (actCode .C) :=
  ⟨guardian_C_of_probe k (properPlayer_CupodTrollBot k) (snd_CupodTrollBot_vs_botCB k),
   ctb_C_of_ne k (properPlayer_GuardianBot k) (progCode_GuardianBot_ne_CupodBot k)⟩

/-- `GuardianBot × GuardianBot = (C, C)` (engine `llm_outcome_GuardianBot_vs_GuardianBot`, pad 2). -/
theorem snd_GuardianBot_vs_GuardianBot (k : ℕ) :
    EvalGraph 2 (progCode (GuardianBot k)) (progCode (GuardianBot k)) (progCode (GuardianBot k)) (actCode .C) ∧
    EvalGraph 2 (progCode (GuardianBot k)) (progCode (GuardianBot k)) (progCode (GuardianBot k)) (actCode .C) :=
  ⟨guardian_C_of_probe k (properPlayer_GuardianBot k) (snd_GuardianBot_vs_botCB k),
   guardian_C_of_probe k (properPlayer_GuardianBot k) (snd_GuardianBot_vs_botCB k)⟩

/-- `GuardianBot × TitForTatBot = (C, C)` (engine `llm_outcome_GuardianBot_vs_TitForTatBot`, pad 4). -/
theorem snd_GuardianBot_vs_TitForTatBot (k : ℕ) :
    EvalGraph 4 (progCode (GuardianBot k)) (progCode TitForTatBot) (progCode (GuardianBot k)) (actCode .C) ∧
    EvalGraph 4 (progCode TitForTatBot) (progCode (GuardianBot k)) (progCode TitForTatBot) (actCode .C) :=
  ⟨EvalGraph.mono_le (by omega) (guardian_C_of_probe k sfp_TitForTatBot.1
      (tft_C_of_probe_C (bot_const_play 0 _ _ 0))),
   tft_C_of_probe_C (snd_GuardianBot_vs_botCB k)⟩

/-- `GuardianBot × CooperateBot = (C, C)` (engine `outcome_GuardianBot_vs_CooperateBot`, pad 2). -/
theorem snd_GuardianBot_vs_CooperateBot (k : ℕ) :
    EvalGraph 2 (progCode (GuardianBot k)) (progCode CooperateBot) (progCode (GuardianBot k)) (actCode .C) ∧
    EvalGraph 2 (progCode CooperateBot) (progCode (GuardianBot k)) (progCode CooperateBot) (actCode .C) :=
  ⟨guardian_C_of_probe k sfp_CooperateBot.1 (by rw [progCode_CB]; exact const_play 0 _ _ 0),
   by rw [progCode_CB]; exact const_play 1 _ _ _⟩

/-- `GuardianBot × MirrorBot = (C, C)` (engine `outcome_GuardianBot_vs_MirrorBot`, pad 3). -/
theorem snd_GuardianBot_vs_MirrorBot (k : ℕ) :
    EvalGraph 3 (progCode (GuardianBot k)) (progCode MirrorBot) (progCode (GuardianBot k)) (actCode .C) ∧
    EvalGraph 3 (progCode MirrorBot) (progCode (GuardianBot k)) (progCode MirrorBot) (actCode .C) := by
  have hG := guardian_C_of_probe k sfp_MirrorBot.1 (mirror_copies (bot_const_play 0 _ _ 0))
  exact ⟨EvalGraph.mono_le (by omega) hG, mirror_copies hG⟩

/-! #### CupodTrollBot (8 of 8) -/

/-- `CupodTrollBot × CooperateBot = (C, C)` (engine `outcome_CupodTrollBot_vs_CooperateBot`, pad 2). -/
theorem snd_CupodTrollBot_vs_CooperateBot (k : ℕ) :
    EvalGraph 2 (progCode (CupodTrollBot k)) (progCode CooperateBot) (progCode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 2 (progCode CooperateBot) (progCode (CupodTrollBot k)) (progCode CooperateBot) (actCode .C) :=
  ⟨ctb_C_of_ne k sfp_CooperateBot.1 (progCode_CB_ne_CupodBot k), by rw [progCode_CB]; exact const_play 1 _ _ _⟩

/-- `CupodTrollBot × CupodTrollBot = (C, C)` (engine `outcome_CupodTrollBot_vs_CupodTrollBot`, pad 3). -/
theorem snd_CupodTrollBot_vs_CupodTrollBot (k : ℕ) :
    EvalGraph 3 (progCode (CupodTrollBot k)) (progCode (CupodTrollBot k)) (progCode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 3 (progCode (CupodTrollBot k)) (progCode (CupodTrollBot k)) (progCode (CupodTrollBot k)) (actCode .C) :=
  ⟨EvalGraph.mono_le (by omega) (ctb_C_of_ne k (properPlayer_CupodTrollBot k) (progCode_CupodTrollBot_ne_CupodBot k)),
   EvalGraph.mono_le (by omega) (ctb_C_of_ne k (properPlayer_CupodTrollBot k) (progCode_CupodTrollBot_ne_CupodBot k))⟩

/-- `CupodTrollBot × DBot = (C, D)` (engine `outcome_CupodTrollBot_vs_DBot`, pad 4). -/
theorem snd_CupodTrollBot_vs_DBot (k : ℕ) :
    EvalGraph 4 (progCode (CupodTrollBot k)) (progCode DBot) (progCode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 4 (progCode DBot) (progCode (CupodTrollBot k)) (progCode DBot) (actCode .D) :=
  ⟨EvalGraph.mono_le (by omega) (ctb_C_of_ne k sfp_DBot.1 (progCode_DBot_ne_CupodBot k)),
   dbot_D_of_probe_C (snd_CupodTrollBot_vs_botDB k)⟩

/-- `CupodTrollBot × DefectBot = (C, D)` (engine `outcome_CupodTrollBot_vs_DefectBot`, pad 2). -/
theorem snd_CupodTrollBot_vs_DefectBot (k : ℕ) :
    EvalGraph 2 (progCode (CupodTrollBot k)) (progCode DefectBot) (progCode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 2 (progCode DefectBot) (progCode (CupodTrollBot k)) (progCode DefectBot) (actCode .D) :=
  ⟨ctb_C_of_ne k sfp_DefectBot.1 (progCode_DB_ne_CupodBot k), by rw [progCode_DB]; exact const_play 1 _ _ _⟩

/-- `CupodTrollBot × EBot = (C, D)` (engine `outcome_CupodTrollBot_vs_EBot`, pad 4). -/
theorem snd_CupodTrollBot_vs_EBot (k : ℕ) :
    EvalGraph 4 (progCode (CupodTrollBot k)) (progCode EBot) (progCode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 4 (progCode EBot) (progCode (CupodTrollBot k)) (progCode EBot) (actCode .D) :=
  ⟨EvalGraph.mono_le (by omega) (ctb_C_of_ne k sfp_EBot.1 (progCode_EBot_ne_CupodBot k)),
   ebot_D_of_probe1_C (snd_CupodTrollBot_vs_botDB k)⟩

/-- `CupodTrollBot × MirrorBot = (C, C)` (engine `outcome_CupodTrollBot_vs_MirrorBot`, pad 3). -/
theorem snd_CupodTrollBot_vs_MirrorBot (k : ℕ) :
    EvalGraph 3 (progCode (CupodTrollBot k)) (progCode MirrorBot) (progCode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 3 (progCode MirrorBot) (progCode (CupodTrollBot k)) (progCode MirrorBot) (actCode .C) := by
  have hT := ctb_C_of_ne k sfp_MirrorBot.1 (progCode_Mirror_ne_CupodBot k)
  exact ⟨EvalGraph.mono_le (by omega) hT, mirror_copies hT⟩

/-- `CupodTrollBot × OBot = (C, C)` (engine `outcome_CupodTrollBot_vs_OBot`, pad 5). -/
theorem snd_CupodTrollBot_vs_OBot (k : ℕ) :
    EvalGraph 5 (progCode (CupodTrollBot k)) (progCode OBot) (progCode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 5 (progCode OBot) (progCode (CupodTrollBot k)) (progCode OBot) (actCode .C) :=
  ⟨EvalGraph.mono_le (by omega) (ctb_C_of_ne k sfp_OBot.1 (progCode_OBot_ne_CupodBot k)),
   obot_C_of_probes (snd_CupodTrollBot_vs_botCB k) (snd_CupodTrollBot_vs_botDB k)⟩

/-- `CupodTrollBot × TitForTatBot = (C, C)` (engine `outcome_CupodTrollBot_vs_TitForTatBot`, pad 4). -/
theorem snd_CupodTrollBot_vs_TitForTatBot (k : ℕ) :
    EvalGraph 4 (progCode (CupodTrollBot k)) (progCode TitForTatBot) (progCode (CupodTrollBot k)) (actCode .C) ∧
    EvalGraph 4 (progCode TitForTatBot) (progCode (CupodTrollBot k)) (progCode TitForTatBot) (actCode .C) :=
  ⟨EvalGraph.mono_le (by omega) (ctb_C_of_ne k sfp_TitForTatBot.1 (progCode_TFT_ne_CupodBot k)),
   tft_C_of_probe_C (snd_CupodTrollBot_vs_botCB k)⟩

/-! #### PrudentBot (6 of 6) -/

/-- `PrudentBot × CooperateBot = (D, C)` (engine `outcome_PrudentBot_vs_CooperateBot`, pad 3): the
prudence guard is false; the outer verdict is irrelevant. -/
theorem snd_PrudentBot_vs_CooperateBot (k : ℕ) :
    EvalGraph 3 (progCode (PrudentBot k)) (progCode CooperateBot) (progCode (PrudentBot k)) (actCode .D) ∧
    EvalGraph 3 (progCode CooperateBot) (progCode (PrudentBot k)) (progCode CooperateBot) (actCode .C) :=
  ⟨prudent_D_of_inner k sfp_CooperateBot.1 (by rw [progCode_CB]; exact const_play 0 _ _ 0),
   by rw [progCode_CB]; exact const_play 2 _ _ _⟩

/-- `PrudentBot × CupodTrollBot = (D, C)` (engine `outcome_PrudentBot_vs_CupodTrollBot`, pad 3). -/
theorem snd_PrudentBot_vs_CupodTrollBot (k : ℕ) :
    EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodTrollBot k)) (progCode (PrudentBot k)) (actCode .D) ∧
    EvalGraph 3 (progCode (CupodTrollBot k)) (progCode (PrudentBot k)) (progCode (CupodTrollBot k)) (actCode .C) :=
  ⟨prudent_D_of_inner k (properPlayer_CupodTrollBot k) (snd_CupodTrollBot_vs_botDB k),
   EvalGraph.mono_le (by omega) (ctb_C_of_ne k (properPlayer_PrudentBot k) (progCode_PrudentBot_ne_CupodBot k))⟩

/-- `PrudentBot × DBot = (D, C)` (engine `outcome_PrudentBot_vs_DBot`, pad 7). -/
theorem snd_PrudentBot_vs_DBot (k : ℕ) :
    EvalGraph 7 (progCode (PrudentBot k)) (progCode DBot) (progCode (PrudentBot k)) (actCode .D) ∧
    EvalGraph 7 (progCode DBot) (progCode (PrudentBot k)) (progCode DBot) (actCode .C) :=
  ⟨EvalGraph.mono_le (by omega) (prudent_D_of_inner k sfp_DBot.1 (dbot_C_of_probe_D (bot_const_play 0 _ _ 1))),
   EvalGraph.mono_le (by omega) (dbot_C_of_probe_D (snd_PrudentBot_vs_botDB k))⟩

/-- `PrudentBot × DefectBot = (D, D)` (engine `outcome_PrudentBot_vs_DefectBot`, pad 2). -/
theorem snd_PrudentBot_vs_DefectBot (k : ℕ) :
    EvalGraph 2 (progCode (PrudentBot k)) (progCode DefectBot) (progCode (PrudentBot k)) (actCode .D) ∧
    EvalGraph 2 (progCode DefectBot) (progCode (PrudentBot k)) (progCode DefectBot) (actCode .D) :=
  ⟨prudent_D_of_probe k sfp_DefectBot.1 (by rw [progCode_DB]; exact const_play 0 _ _ 1),
   by rw [progCode_DB]; exact const_play 1 _ _ _⟩

/-- `PrudentBot × OBot = (D, D)` (engine `outcome_PrudentBot_vs_OBot`, pad 6). -/
theorem snd_PrudentBot_vs_OBot (k : ℕ) :
    EvalGraph 6 (progCode (PrudentBot k)) (progCode OBot) (progCode (PrudentBot k)) (actCode .D) ∧
    EvalGraph 6 (progCode OBot) (progCode (PrudentBot k)) (progCode OBot) (actCode .D) := by
  have hO := obot_D_of_probe1_D (snd_PrudentBot_vs_botCB k) (by decide)
  exact ⟨EvalGraph.mono_le (by omega) (prudent_D_of_probe k sfp_OBot.1 hO), EvalGraph.mono_le (by omega) hO⟩

/-- `PrudentBot × TitForTatBot = (D, D)` (engine `outcome_PrudentBot_vs_TitForTatBot`, pad 6). -/
theorem snd_PrudentBot_vs_TitForTatBot (k : ℕ) :
    EvalGraph 6 (progCode (PrudentBot k)) (progCode TitForTatBot) (progCode (PrudentBot k)) (actCode .D) ∧
    EvalGraph 6 (progCode TitForTatBot) (progCode (PrudentBot k)) (progCode TitForTatBot) (actCode .D) := by
  have hT := tft_D_of_probe_D (snd_PrudentBot_vs_botCB k)
  exact ⟨EvalGraph.mono_le (by omega) (prudent_D_of_probe k sfp_TitForTatBot.1 hT),
    EvalGraph.mono_le (by omega) hT⟩

/-! #### WaryBot (4 of 6; `× DBot` and `× EBot` need the positive `.neg` guard, out of scope) -/

/-- `WaryBot × CooperateBot = (C, C)` (engine `outcome_WaryBot_vs_CooperateBot`, pad 2). -/
theorem snd_WaryBot_vs_CooperateBot (k : ℕ) :
    EvalGraph 2 (progCode (WaryBot k)) (progCode CooperateBot) (progCode (WaryBot k)) (actCode .C) ∧
    EvalGraph 2 (progCode CooperateBot) (progCode (WaryBot k)) (progCode CooperateBot) (actCode .C) :=
  ⟨wary_C_of_probe k sfp_CooperateBot.1 (by rw [progCode_CB]; exact const_play 0 _ _ 0),
   by rw [progCode_CB]; exact const_play 1 _ _ _⟩

/-- `WaryBot × CupodTrollBot = (C, C)` (engine `outcome_WaryBot_vs_CupodTrollBot`, pad 2). -/
theorem snd_WaryBot_vs_CupodTrollBot (k : ℕ) :
    EvalGraph 2 (progCode (WaryBot k)) (progCode (CupodTrollBot k)) (progCode (WaryBot k)) (actCode .C) ∧
    EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (WaryBot k)) (progCode (CupodTrollBot k)) (actCode .C) := by
  have hT := ctb_C_of_ne k (properPlayer_WaryBot k) (progCode_WaryBot_ne_CupodBot k)
  exact ⟨wary_C_of_probe k (properPlayer_CupodTrollBot k) hT, hT⟩

/-- `WaryBot × GuardianBot = (C, C)` (engine `llm_outcome_WaryBot_vs_GuardianBot`, pad 2). -/
theorem snd_WaryBot_vs_GuardianBot (k : ℕ) :
    EvalGraph 2 (progCode (WaryBot k)) (progCode (GuardianBot k)) (progCode (WaryBot k)) (actCode .C) ∧
    EvalGraph 2 (progCode (GuardianBot k)) (progCode (WaryBot k)) (progCode (GuardianBot k)) (actCode .C) := by
  have hG := guardian_C_of_probe k (properPlayer_WaryBot k) (snd_WaryBot_vs_botCB k)
  exact ⟨wary_C_of_probe k (properPlayer_GuardianBot k) hG, hG⟩

/-- `WaryBot × TitForTatBot = (C, C)` (engine `outcome_WaryBot_vs_TitForTatBot`, pad 4). -/
theorem snd_WaryBot_vs_TitForTatBot (k : ℕ) :
    EvalGraph 4 (progCode (WaryBot k)) (progCode TitForTatBot) (progCode (WaryBot k)) (actCode .C) ∧
    EvalGraph 4 (progCode TitForTatBot) (progCode (WaryBot k)) (progCode TitForTatBot) (actCode .C) := by
  have hT := tft_C_of_probe_C (snd_WaryBot_vs_botCB k)
  exact ⟨EvalGraph.mono_le (by omega) (wary_C_of_probe k sfp_TitForTatBot.1 hT), hT⟩

/-! #### CupodBot (2 of 4; `× DBot` and `× EBot` need Cupod's positive guard against `.bot DefectBot`) -/

/-- `CupodBot × CooperateBot = (C, C)` (engine `outcome_CupodBot_vs_CooperateBot`, pad 2). -/
theorem snd_CupodBot_vs_CooperateBot (k : ℕ) :
    EvalGraph 2 (progCode (CupodBot k)) (progCode CooperateBot) (progCode (CupodBot k)) (actCode .C) ∧
    EvalGraph 2 (progCode CooperateBot) (progCode (CupodBot k)) (progCode CooperateBot) (actCode .C) :=
  ⟨cupod_C_of_probe k sfp_CooperateBot.1 (by rw [progCode_CB]; exact const_play 0 _ _ 0),
   by rw [progCode_CB]; exact const_play 1 _ _ _⟩

/-- `CupodBot × TitForTatBot = (C, C)` (engine `outcome_CupodBot_vs_TitForTatBot`, pad 4). -/
theorem snd_CupodBot_vs_TitForTatBot (k : ℕ) :
    EvalGraph 4 (progCode (CupodBot k)) (progCode TitForTatBot) (progCode (CupodBot k)) (actCode .C) ∧
    EvalGraph 4 (progCode TitForTatBot) (progCode (CupodBot k)) (progCode TitForTatBot) (actCode .C) := by
  have hT := tft_C_of_probe_C (snd_CupodBot_vs_botCB k)
  exact ⟨EvalGraph.mono_le (by omega) (cupod_C_of_probe k sfp_TitForTatBot.1 hT), hT⟩

/-! #### DupocBot (2 of 2) -/

/-- `DupocBot × DefectBot = (D, D)` (engine `outcome_DupocBot_vs_DefectBot`, pad 2). -/
theorem snd_DupocBot_vs_DefectBot (k : ℕ) :
    EvalGraph 2 (progCode (DupocBot k)) (progCode DefectBot) (progCode (DupocBot k)) (actCode .D) ∧
    EvalGraph 2 (progCode DefectBot) (progCode (DupocBot k)) (progCode DefectBot) (actCode .D) :=
  ⟨dupoc_D_of_probe k sfp_DefectBot.1 (by rw [progCode_DB]; exact const_play 0 _ _ 1),
   by rw [progCode_DB]; exact const_play 1 _ _ _⟩

/-- `DupocBot × OBot = (D, D)` (engine `outcome_DupocBot_vs_OBot`, pad 5): OBot's first probe (Dupoc
against `.bot CooperateBot`) is left undecided — Dupoc defects against `.bot DefectBot` either way. -/
theorem snd_DupocBot_vs_OBot (k : ℕ) :
    EvalGraph 5 (progCode (DupocBot k)) (progCode OBot) (progCode (DupocBot k)) (actCode .D) ∧
    EvalGraph 5 (progCode OBot) (progCode (DupocBot k)) (progCode OBot) (actCode .D) := by
  obtain ⟨r, hr⟩ := dupoc_body_total k (DupocBot k) (.bot CooperateBot)
  rw [progCode_botCB] at hr
  have hO := obot_D_of_any hr (snd_DupocBot_vs_botDB k)
  exact ⟨EvalGraph.mono_le (by omega) (dupoc_D_of_probe k sfp_OBot.1 hO), hO⟩

/-! #### JustBot (2 of 2), on the engine's own code `progCode (JustBot k)` -/

/-- `JustBot × DefectBot = (D, D)` (engine `outcome_JustBot_vs_DefectBot`, pad 2). -/
theorem snd_JustBot_vs_DefectBot (k : ℕ) :
    EvalGraph 2 (progCode (JustBot k)) (progCode DefectBot) (progCode (JustBot k)) (actCode .D) ∧
    EvalGraph 2 (progCode DefectBot) (progCode (JustBot k)) (progCode DefectBot) (actCode .D) :=
  ⟨just_D_of_probe k sfp_DefectBot.1 (by rw [progCode_DB]; exact const_play 0 _ _ 1),
   by rw [progCode_DB]; exact const_play 1 _ _ _⟩

/-- The frozen snapshot `.bot (DupocBot k)` defects against `.bot DefectBot` (fuel 3). -/
theorem snd_botDupocBot_vs_botDB (k : ℕ) :
    EvalGraph 3 (pBot (progCode (DupocBot k))) (pBot (pConst 1)) (pBot (progCode (DupocBot k))) 1 := by
  show EvalGraph (2 + 1) _ _ _ _
  rw [EvalGraph.bot_iff]
  have := dupoc_body_D_of_probe k (me := .bot (DupocBot k)) (opp := .bot DefectBot) (properPlayer_bot _) properPlayer_botDB
    (N := 2) (by rw [progCode_botDB, progCode_bot]; exact bot_const_play 0 _ _ _)
  rwa [progCode_botDB, progCode_bot] at this

/-- The frozen snapshot `.bot (DupocBot k)` plays against `.bot CooperateBot` (fuel 3). -/
theorem botDupoc_vs_botCB_total (k : ℕ) :
    ∃ r, EvalGraph 3 (pBot (progCode (DupocBot k))) (pBot (pConst 0)) (pBot (progCode (DupocBot k))) r := by
  obtain ⟨r, hr⟩ := dupoc_body_total k (.bot (DupocBot k)) (.bot CooperateBot)
  rw [progCode_botCB, progCode_bot] at hr
  exact ⟨r, (EvalGraph.bot_iff (n := 2)).mpr hr⟩

/-- `JustBot × OBot = (D, D)` (engine `outcome_JustBot_vs_OBot`, pad 6): OBot defects against the
frozen `.bot (DupocBot k)` (which defects against `.bot DefectBot`), so Just's guard is false. -/
theorem snd_JustBot_vs_OBot (k : ℕ) :
    EvalGraph 6 (progCode (JustBot k)) (progCode OBot) (progCode (JustBot k)) (actCode .D) ∧
    EvalGraph 6 (progCode OBot) (progCode (JustBot k)) (progCode OBot) (actCode .D) := by
  obtain ⟨r, hr⟩ := botDupoc_vs_botCB_total k
  have hOb : EvalGraph 6 (progCode OBot) (pBot (progCode (DupocBot k))) (progCode OBot) 1 :=
    obot_D_of_any hr (snd_botDupocBot_vs_botDB k)
  have hJ := just_D_of_probe k sfp_OBot.1 hOb
  refine ⟨EvalGraph.mono_le (by omega) hJ, ?_⟩
  -- OBot against Just: Just cooperates with neither probe … it defects against `.bot DefectBot`,
  -- and against `.bot CooperateBot` it plays something.
  have h2 : EvalGraph 2 (progCode (JustBot k)) (pBot (pConst 1)) (progCode (JustBot k)) 1 := by
    have := just_D_of_probe k (opp := .bot DefectBot) properPlayer_botDB (N := 2)
      (by rw [progCode_botDB]; exact bot_const_play 0 _ _ _)
    rwa [progCode_botDB] at this
  have h1 : ∃ r, EvalGraph 2 (progCode (JustBot k)) (pBot (pConst 0)) (progCode (JustBot k)) r := by
    rw [progCode_JustBot]
    by_cases hg : LenBox TAct k (guardCode (templateCode (phiJ k)) (pSearch k (templateCodeAt (phiJ k) k) (pConst 0) (pConst 1))
      (pBot (pConst 0)))
    · exact ⟨0, search_then_at (phiJ k) hg (const_play _ _ _ _)⟩
    · exact ⟨1, search_else_at (phiJ k) hg (const_play _ _ _ _)⟩
  obtain ⟨r', hr'⟩ := h1
  exact EvalGraph.mono_le (by omega) (obot_D_of_any hr' h2)

end sndCells

/-! ### 10. Guardian's guard against a closed opponent is a FIXED sentence: the positive cells -/

section guardianPos

lemma sfp_botCB : SearchFreePlayer (.bot CooperateBot) := ⟨properPlayer_botCB, rfl, rfl⟩
lemma sfp_botDB : SearchFreePlayer (.bot DefectBot) := ⟨properPlayer_botDB, rfl, rfl⟩

/-- **Guardian finds its guard against a closed opponent `X` for all large `k`** as soon as `TAct`
proves the closed atom "`X` defects against `.bot CooperateBot`": the guard mentions no `.self`, so
its realization is that FIXED sentence (`sentenceAt_subst`), found above its proof length. -/
theorem guardian_found {X : PD.Prog} (hX : ProperPlayer X)
    (hT : TAct ⊢ sentenceAt X (.bot CooperateBot) (.plays X (.bot CooperateBot) .D)) :
    ∃ L : ℕ, ∀ k : ℕ, L ≤ k → LenBox TAct k (guardCode (templateCode phiG) (progCode (GuardianBot k)) (progCode X)) := by
  obtain ⟨N, hN⟩ := lenBoxNat_of_provable hT
  refine ⟨N, fun k hk ↦ ?_⟩
  have e : phiG.subst (GuardianBot k) X = .plays X (.bot CooperateBot) .D := by
    simp [phiG, PD.Formula.subst, PD.Prog.subst]
  rw [← quote_sentenceAt (GuardianBot k) X phiG rfl, ← sentenceAt_subst X (.bot CooperateBot) (properPlayer_GuardianBot k) hX phiG rfl,
    e, lenBox_nat]
  exact lenBoxNat_codeBound_mono hk hN

/-- The transposed play of a closed search-free match, from the engine's evaluation by `decide`. -/
theorem evalGraph_transpose_of_eval {X Y : PD.Prog} {a : PD.Action} {n : ℕ}
    (h : PD.eval n X.transpose Y.transpose X.transpose = some a) (hX : SearchFreePlayer X.transpose)
    (hY : SearchFreePlayer Y.transpose) :
    EvalGraph n (progCode X.transpose) (progCode Y.transpose) (progCode X.transpose) (actCode a) :=
  evalGraph_of_eval_searchFree h hX hY hX.2.1 hX.2.2

/-- `TAct ⊢` "`DefectBot` defects against `.bot CooperateBot`". -/
theorem tact_DB_D_vs_botCB : TAct ⊢ sentenceAt DefectBot (.bot CooperateBot) (.plays DefectBot (.bot CooperateBot) .D) :=
  tact_proves_plays_closed sfp_DefectBot sfp_botCB .D (N := 1)
    (by rw [progCode_DB]; exact const_play 0 _ _ _) (N' := 1)
    (by show EvalGraph 1 (progCode CooperateBot) (progCode (.bot DefectBot)) (progCode CooperateBot) (actCode .C)
        rw [progCode_CB]; exact const_play 0 _ _ _)

/-- `TAct ⊢` "`.bot DefectBot` defects against `.bot CooperateBot`". -/
theorem tact_botDB_D_vs_botCB :
    TAct ⊢ sentenceAt (.bot DefectBot) (.bot CooperateBot) (.plays (.bot DefectBot) (.bot CooperateBot) .D) :=
  tact_proves_plays_closed sfp_botDB sfp_botCB .D (N := 2)
    (by rw [progCode_botDB]; exact bot_const_play 0 _ _ _) (N' := 2)
    (by show EvalGraph 2 (progCode (.bot CooperateBot)) (progCode (.bot DefectBot)) (progCode (.bot CooperateBot)) (actCode .C)
        rw [progCode_botCB]; exact bot_const_play 0 _ _ _)

/-- `TAct ⊢` "`DBot` defects against `.bot CooperateBot`". -/
theorem tact_DBot_D_vs_botCB : TAct ⊢ sentenceAt DBot (.bot CooperateBot) (.plays DBot (.bot CooperateBot) .D) :=
  tact_proves_plays_closed sfp_DBot sfp_botCB .D (N := 4)
    (by rw [progCode_botCB]; exact dbot_D_of_probe_C (bot_const_play 0 _ _ 0)) (N' := 4)
    (evalGraph_transpose_of_eval (by decide) (sfp_transpose sfp_DBot (by decide) (by decide))
      (sfp_transpose sfp_botCB (by decide) (by decide)))

/-- `TAct ⊢` "`EBot` defects against `.bot CooperateBot`". -/
theorem tact_EBot_D_vs_botCB : TAct ⊢ sentenceAt EBot (.bot CooperateBot) (.plays EBot (.bot CooperateBot) .D) :=
  tact_proves_plays_closed sfp_EBot sfp_botCB .D (N := 4)
    (by rw [progCode_botCB]; exact ebot_D_of_probe1_C (bot_const_play 0 _ _ 0)) (N' := 4)
    (evalGraph_transpose_of_eval (by decide) (sfp_transpose sfp_EBot (by decide) (by decide))
      (sfp_transpose sfp_botCB (by decide) (by decide)))

/-- Guardian defects against `.bot DefectBot` for all large `k`. -/
theorem pos_GuardianBot_vs_botDB :
    ∃ L : ℕ, ∀ k : ℕ, L ≤ k → EvalGraph 2 (progCode (GuardianBot k)) (pBot (pConst 1)) (progCode (GuardianBot k)) 1 := by
  obtain ⟨L, hL⟩ := guardian_found (X := .bot DefectBot) properPlayer_botDB tact_botDB_D_vs_botCB
  refine ⟨L, fun k hk ↦ ?_⟩
  have := guardian_D_of_found k (hL k hk)
  rwa [progCode_botDB] at this

/-- `GuardianBot × DefectBot = (D, D)` (engine `outcome_GuardianBot_vs_DefectBot`, pad 2), for all large `k`:
the guard "DefectBot defects against `.bot CooperateBot`" is a fixed true closed atom. -/
theorem pos_GuardianBot_vs_DefectBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (GuardianBot k)) (progCode DefectBot) (progCode (GuardianBot k)) (actCode .D) ∧
      EvalGraph 2 (progCode DefectBot) (progCode (GuardianBot k)) (progCode DefectBot) (actCode .D) := by
  obtain ⟨L, hL⟩ := guardian_found (X := DefectBot) sfp_DefectBot.1 tact_DB_D_vs_botCB
  exact ⟨L, fun k hk ↦ ⟨guardian_D_of_found k (hL k (Nat.le_of_lt hk)), by rw [progCode_DB]; exact const_play 1 _ _ _⟩⟩

/-- `GuardianBot × DBot = (D, C)` (engine `llm_outcome_GuardianBot_vs_DBot`, pad 4), for all large `k`. -/
theorem pos_GuardianBot_vs_DBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 4 (progCode (GuardianBot k)) (progCode DBot) (progCode (GuardianBot k)) (actCode .D) ∧
      EvalGraph 4 (progCode DBot) (progCode (GuardianBot k)) (progCode DBot) (actCode .C) := by
  obtain ⟨L₁, hL₁⟩ := guardian_found (X := DBot) sfp_DBot.1 tact_DBot_D_vs_botCB
  obtain ⟨L₂, hL₂⟩ := pos_GuardianBot_vs_botDB
  refine ⟨L₁ + L₂, fun k hk ↦ ⟨EvalGraph.mono_le (by omega) (guardian_D_of_found k (hL₁ k (by omega))), ?_⟩⟩
  exact dbot_C_of_probe_D (hL₂ k (by omega))

/-- `GuardianBot × EBot = (D, C)` (engine `llm_outcome_GuardianBot_vs_EBot`, pad 6), for all large `k`: Guardian
finds "EBot defects against `.bot CooperateBot`"; EBot sees Guardian defect against `.bot DefectBot` (found) and
cooperate with `.bot CooperateBot` (guard false). -/
theorem pos_GuardianBot_vs_EBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 6 (progCode (GuardianBot k)) (progCode EBot) (progCode (GuardianBot k)) (actCode .D) ∧
      EvalGraph 6 (progCode EBot) (progCode (GuardianBot k)) (progCode EBot) (actCode .C) := by
  obtain ⟨L₁, hL₁⟩ := guardian_found (X := EBot) sfp_EBot.1 tact_EBot_D_vs_botCB
  obtain ⟨L₂, hL₂⟩ := pos_GuardianBot_vs_botDB
  refine ⟨L₁ + L₂, fun k hk ↦ ⟨EvalGraph.mono_le (by omega) (guardian_D_of_found k (hL₁ k (by omega))), ?_⟩⟩
  exact EvalGraph.mono_le (by omega) (ebot_C_of_probes (hL₂ k (by omega)) (snd_GuardianBot_vs_botCB k))

/-- `GuardianBot × OBot = (C, D)` (engine `llm_outcome_GuardianBot_vs_OBot`, pad 7), for all large `k`: OBot
cooperates with `.bot CooperateBot`, so Guardian's guard is false; OBot sees Guardian cooperate with
`.bot CooperateBot` but defect against `.bot DefectBot` (found), and defects. -/
theorem pos_GuardianBot_vs_OBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 7 (progCode (GuardianBot k)) (progCode OBot) (progCode (GuardianBot k)) (actCode .C) ∧
      EvalGraph 7 (progCode OBot) (progCode (GuardianBot k)) (progCode OBot) (actCode .D) := by
  obtain ⟨L₂, hL₂⟩ := pos_GuardianBot_vs_botDB
  refine ⟨L₂, fun k hk ↦ ⟨?_, ?_⟩⟩
  · have hO : EvalGraph 5 (progCode OBot) (pBot (pConst 0)) (progCode OBot) 0 :=
      obot_C_of_probes (bot_const_play 0 _ _ 0) (bot_const_play 0 _ _ 0)
    exact EvalGraph.mono_le (by omega) (guardian_C_of_probe k sfp_OBot.1 hO)
  · exact EvalGraph.mono_le (by omega) (obot_D_of_probes (snd_GuardianBot_vs_botCB k) (hL₂ k (Nat.le_of_lt hk)))

end guardianPos

end ArithS
