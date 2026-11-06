import ArithS.Tau.Described
import ArithS.Tau.Rows.TftSim
import ArithS.Tau.Rows.OBot
import ArithS.Tau.Rows.EBot
import ArithS.Tau.Rows.DBot
import ArithS.Tau.Rows.CupodTroll
import ArithS.Cells.FloorDichotomy

/-!
# ArithS.Tau.Quine — the self-probers' DIAGONALS and the shared kit of their rows (Phase 3b)

The seven self-probing templates (`dupoc cupod cimcic dimcid prudent maxconfidence minconfidence`) compile, on
the diagonal `T = A`, to the QUINE: `instGo` emits the `.self` pronoun where the hypothesis would have to contain
itself (`Tau/Zoo.lean`, `inst_dupoc_quine`), so the instance is `.search k (.plays .self .self C) …` and the bit's
frame `(.bot I, .bot I)` consults the fixed point "`.bot I` plays C against `.bot I`". Its stored template is
BUDGET-FREE, so the instance is the bot-wrapped engine searcher `pBot (SV g a k)` and its own description is the
tower `TBS g a` (`Cells/Common/Bots.lean`): the Löb families of `Tau/Described.lean` apply verbatim, with the
instance's triple on BOTH sides (`qInst`).

* §1 the two atoms of a self-self template in every model (`eval_template_plays_self_self_V`, and the
  `.opp .opp` twin the closed probes use);
* §2 the instance equation of `pBot (SV g a k)` against itself in EVERY model, both readings
  (`guardCode_botSV_self_eq_instB_V`, `guardCode_botSV_self_swap_eq_instB_V` — `Tau/Described.lean`'s ℕ
  statement, lifted);
* §3 **the three diagonal mechanisms**: the Löb quine `.plays .self .self t` (`loebSound_quine`,
  `quine_found` — Dupoc at `t = C`, Cupod at `t = D`, the natives by `inst_maxconfidence_quine`), DIMCID's
  Löb fixpoint on defection `.impl (self plays self C) (self plays self D)` (`loebSound_dimQ`,
  `dimcid_quine_found` — the then-branch D refutes the antecedent), and CIMCIC's tautology
  `.impl (self plays self C) (self plays self C)` (`cimcic_quine_found`, Löb-free, the `S'` twin of
  `Pf.implRefl` on the instance);
* §4 the row kit: a hypothesis's bit lifted to its bot-wrapped play (`botPlays_of_bit`), a probe refuted by the
  opposite play (`probe_not_found_of_bit`), the Dupoc-shaped searcher's SND slot and FLOOR-SIDE slot
  (`dupocLike_D_of_probe_false`, `dupocLike_floor_D`), Cupod's and Prudent's twins.

The non-diagonal slots whose guard names the instance ITSELF (`.self`) AND a hypothesis instance that carries
`k` (CIMCIC/DIMCID at `tftSim ebot obot dbot cupodTroll`) are NOT here: their stored template carries the
hypothesis's `.search k` leaf, so the instance's own code is not a `binNumeral k`-tower (`ROUTE_B_SCOPE.md` §7),
and the row files record them (see `Rows/CIMCIC.lean`, `Rows/DIMCID.lean`).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD PD.Tau

/-! ### 1. The self-self and opp-opp atoms in every model -/

section atoms

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The `.plays .self .self a` atom of `template` in every model**: "me plays `a` against me". -/
lemma eval_template_plays_self_self_V (a : PD.Action) (b : Fin 6 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (template (.plays .self .self a)) ↔
      ∃ n, EvalGraph n (revalue (b 1) (b 2) (b 0)) (revalue (b 1) (b 2) (b 0))
        (revalue (b 1) (b 2) (b 0)) (actCode a : V) := by
  rw [template_plays]
  unfold progGraph
  rw [progAux_self]
  unfold descF
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, stdReadingV_rel_eq,
    Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, ⟨d, rfl, rfl⟩, ⟨d', rfl, rfl⟩, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, h⟩

/-- **The `.plays .opp .opp a` atom of `template` in every model**: "opp plays `a` against opp" (the shape a
closed probe `.plays (.bot X) (.bot X) a` takes once the probed program is moved into the opp-slots). -/
lemma eval_template_plays_opp_opp_V (a : PD.Action) (b : Fin 6 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (template (.plays .opp .opp a)) ↔
      ∃ n, EvalGraph n (revalue (b 4) (b 5) (b 3)) (revalue (b 4) (b 5) (b 3))
        (revalue (b 4) (b 5) (b 3)) (actCode a : V) := by
  rw [template_plays]
  unfold progGraph
  rw [progAux_opp]
  unfold descF
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, stdReadingV_rel_eq,
    Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, ⟨d, rfl, rfl⟩, ⟨d', rfl, rfl⟩, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, h⟩

end atoms

/-! ### 2. The instance equation of the bot-wrapped searcher against itself, in every model -/

section instanceEq

/-- **The instance equation in every model**: the guard code of `pBot (SV g a k)` against itself on `g` is the
`binNumeral k`-instance of `⌜qInst g a⌝` (`Tau/Described.guardCode_botSV_self_eq_instB` at ℕ, lifted). -/
theorem guardCode_botSV_self_eq_instB_V (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    guardCode (⌜g⌝ : V) (pBot (SV g a k)) (pBot (SV g a k)) = instB (⌜qInst g a⌝ : V) k := by
  have hX := (describes_botSV g a ha).hX V k
  have hU := (describes_botSV g a ha).hU V k
  have hW := (describes_botSV g a ha).hW V k
  rw [descVal_botSV g a ha] at hX hU hW
  exact guardCode_qT_eq_instB g k _ _ _ _ _ _ hX hU hW hX hU hW

/-- **The transposed instance equation**: the transposed searcher against itself, on the transposed template. -/
theorem guardCode_botSV_self_swap_eq_instB_V (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    guardCode (⌜Semiformula.lMap swap g⌝ : V) (pBot (SV (Semiformula.lMap swap g) (1 - a) k))
        (pBot (SV (Semiformula.lMap swap g) (1 - a) k)) =
      instB (⌜Semiformula.lMap swap (qInst g a)⌝ : V) k := by
  have hX := (describes_botSV g a ha).hX V k
  have hU := (describes_botSV g a ha).hU V k
  have hW := (describes_botSV g a ha).hW V k
  rw [descVal_botSV g a ha] at hX hU hW
  have := guardCode_qT_swap_eq_instB g k _ _ _ _ _ _ hX hU hW hX hU hW
  unfold qInst
  rwa [transposeCode_pBot, transposeCode_SV g a ha] at this

end instanceEq

/-! ### 3. The three diagonal mechanisms -/

section diagonal

/-- The quine template `.plays .self .self t`. -/
abbrev quineF (t : PD.Action) : PD.Formula := .plays .self .self t

lemma quineF_transpose (t : PD.Action) : (quineF t).transpose = quineF t.swap := by cases t <;> rfl
lemma fragF_quineF (t : PD.Action) : fragF (quineF t) = true := by cases t <;> rfl
lemma noSelfIdxF_quineF (t : PD.Action) : noSelfIdxF (quineF t) = true := by cases t <;> rfl
lemma actCode_zero_or_one (t : PD.Action) : actCode t = 0 ∨ actCode t = 1 := by cases t <;> simp [actCode]

lemma one_sub_actCode_cast {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (t : PD.Action) :
    ((1 - actCode t : ℕ) : V) = ((actCode t.swap : ℕ) : V) := by
  cases t <;> simp [actCode, PD.Action.swap]

/-- **The Löb premise of the quine**: a box of "`.bot I` plays `t` against `.bot I`" (either reading) makes the
bot-wrapped searcher take its then-branch `t`, which is exactly what the sentence says. -/
theorem loebSound_quine (t : PD.Action) :
    LoebSound (pQ (qInst (template (quineF t)) (actCode t))) 7 8 := by
  have ha := actCode_zero_or_one t
  refine loebSound_pQ_of _ fun V _ _ k h1 h2 ↦ ?_
  rw [← guardCode_botSV_self_eq_instB_V V _ _ ha k] at h1
  rw [← guardCode_botSV_self_swap_eq_instB_V V _ _ ha k] at h2
  have e1 := botSV_then_V (template (quineF t)) (actCode t) k _ _ h1
  have e2 := botSV_then_V (Semiformula.lMap swap (template (quineF t))) (1 - actCode t) k _ _ h2
  rw [← stdReadingV_eq_stdReading]
  constructor
  · unfold qInst
    rw [eval_qT_iff, eval_template_plays_self_self_V]
    simp only [Matrix.cons_val]
    rw [desc_botSV _ _ ha k]
    exact ⟨3, e1⟩
  · unfold qInst
    have ht : Semiformula.lMap swap (template (quineF t)) = template (quineF t.swap) := by
      rw [lMap_swap_template _ (fragF_quineF t), quineF_transpose]
    rw [lMap_swap_qT, ht, eval_qT_iff, eval_template_plays_self_self_V]
    simp only [Matrix.cons_val]
    rw [descT_botSV _ _ ha k, ← one_sub_actCode_cast t]
    exact ⟨3, e2⟩

/-- **The quine is FOUND for all large `k`, in the bit's own frame**: the guard `.plays .self .self t` of the
bot-wrapped instance `pBot (pSearch k ⌜…⌝ (pConst t) (pConst (1 - t)))`, consulted against itself. -/
theorem quine_found (t : PD.Action) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode (quineF t))
        (pBot (pSearch k (templateCode (quineF t)) (pConst (actCode t)) (pConst (1 - actCode t))))
        (pBot (pSearch k (templateCode (quineF t)) (pConst (actCode t)) (pConst (1 - actCode t))))) := by
  have ha := actCode_zero_or_one t
  obtain ⟨k₀, hf⟩ := family_found (pQ (qInst (template (quineF t)) (actCode t))) boundedInnerNec_sixteen
    (loebSound_quine t)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha', hpc⟩ := hf k hk
  have ha'' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pQ (V := ℕ) _ k) ha')
  have h1 := (pQ_both_V (V := ℕ) _ k a ha'' hpc).1
  rw [← guardCode_botSV_self_eq_instB_V ℕ _ _ ha k, SV_nat] at h1
  rw [templateCode_eq_quote_template _ (noSelfIdxF_quineF t)]
  exact h1

/-- DIMCID's diagonal template: "if I cooperate with myself, I defect against myself" — the SAME player at
opposite actions, a genuine Löb fixpoint on defection (`Tau/Zoo.inst_dimcid_quine`). -/
abbrev dimQ : PD.Formula := .impl (.plays .self .self .C) (.plays .self .self .D)

/-- CIMCIC's diagonal template: `φ → φ`. -/
abbrev cimQ : PD.Formula := .impl (.plays .self .self .C) (.plays .self .self .C)

/-- **DIMCID's Löb premise on the diagonal**: a box of the guard makes the instance DEFECT against itself,
refuting the antecedent "I cooperate with myself" — so the implication is true. Both readings. -/
theorem loebSound_dimQ : LoebSound (pQ (qInst (template dimQ) 1)) 7 8 := by
  refine loebSound_pQ_of _ fun V _ _ k h1 h2 ↦ ?_
  rw [← guardCode_botSV_self_eq_instB_V V _ _ (Or.inr rfl) k] at h1
  rw [← guardCode_botSV_self_swap_eq_instB_V V _ _ (Or.inr rfl) k] at h2
  have e1 := botSV_then_V (template dimQ) 1 k _ _ h1
  have e2 := botSV_then_V (Semiformula.lMap swap (template dimQ)) (1 - 1) k _ _ h2
  rw [Nat.cast_one] at e1
  rw [show ((1 - 1 : ℕ) : V) = 0 by simp] at e2
  rw [← stdReadingV_eq_stdReading]
  constructor
  · unfold qInst
    rw [eval_qT_iff]
    show Semiformula.Eval (s := stdReadingV V) _ Empty.elim
      (template (.plays .self .self .C) 🡒 template (.plays .self .self .D))
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro hA
    exfalso
    rw [eval_template_plays_self_self_V] at hA
    simp only [Matrix.cons_val] at hA
    rw [desc_botSV _ 1 (Or.inr rfl) k, actCode_C_cast] at hA
    obtain ⟨n, hn⟩ := hA
    exact _root_.zero_ne_one (EvalGraph.unique_V' n 3 _ _ _ _ _ hn e1)
  · unfold qInst
    have ht : Semiformula.lMap swap (template dimQ) =
        template (.impl (.plays .self .self .D) (.plays .self .self .C)) := lMap_swap_template _ rfl
    rw [lMap_swap_qT, ht, eval_qT_iff]
    show Semiformula.Eval (s := stdReadingV V) _ Empty.elim
      (template (.plays .self .self .D) 🡒 template (.plays .self .self .C))
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro hA
    exfalso
    rw [eval_template_plays_self_self_V] at hA
    simp only [Matrix.cons_val] at hA
    rw [descT_botSV _ 1 (Or.inr rfl) k, actCode_D_cast] at hA
    obtain ⟨n, hn⟩ := hA
    exact _root_.one_ne_zero (EvalGraph.unique_V' n 3 _ _ _ _ _ hn e2)

/-- **DIMCID's diagonal guard is FOUND for all large `k`**, in the bit's own frame (then-branch `D`). -/
theorem dimcid_quine_found :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode dimQ)
        (pBot (pSearch k (templateCode dimQ) (pConst 1) (pConst (1 - 1))))
        (pBot (pSearch k (templateCode dimQ) (pConst 1) (pConst (1 - 1))))) := by
  obtain ⟨k₀, hf⟩ := family_found (pQ (qInst (template dimQ) 1)) boundedInnerNec_sixteen loebSound_dimQ
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha', hpc⟩ := hf k hk
  have ha'' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pQ (V := ℕ) _ k) ha')
  have h1 := (pQ_both_V (V := ℕ) _ k a ha'' hpc).1
  rw [← guardCode_botSV_self_eq_instB_V ℕ _ _ (Or.inr rfl) k, SV_nat] at h1
  rw [templateCode_eq_quote_template _ rfl]
  exact h1

/-- **CIMCIC's diagonal guard is a `TAct`-theorem in `k`**: `φ → φ` in both readings. -/
theorem tact_qInst_cimQ (n : ℕ) : TAct ⊢ ∀¹ qInst (template cimQ) n := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    unfold qInst
    rw [eval_qT_iff]
    show Semiformula.Eval (s := stdReadingV M) _ Empty.elim
      (template (.plays .self .self .C) 🡒 template (.plays .self .self .C))
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    exact id
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    unfold qInst
    have ht : Semiformula.lMap swap (template cimQ) =
        template (.impl (.plays .self .self .D) (.plays .self .self .D)) := lMap_swap_template _ rfl
    rw [eval_qT_swap, ht, eval_qT_iff]
    show Semiformula.Eval (s := stdReadingV M) _ Empty.elim
      (template (.plays .self .self .D) 🡒 template (.plays .self .self .D))
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    exact id

/-- **CIMCIC's diagonal guard is FOUND for all large `k`, Löb-free** (the instance of the tautology costs
`K₀ + K₁·size k`, `found_of_all`). -/
theorem cimcic_quine_found :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode cimQ)
        (pBot (pSearch k (templateCode cimQ) (pConst 0) (pConst (1 - 0))))
        (pBot (pSearch k (templateCode cimQ) (pConst 0) (pConst (1 - 0))))) := by
  refine found_of_all (tact_qInst_cimQ 0) _ fun k ↦ ?_
  rw [templateCode_eq_quote_template _ rfl, ← SV_nat]
  exact guardCode_botSV_self_eq_instB_V ℕ _ 0 (Or.inl rfl) k

end diagonal

/-! ### 4. The row kit of the self-probers -/

section kit

/-- A hypothesis's bit, lifted to the play of its bot-wrapped instance (`EvalGraph.bot_iff` keeps the frame). -/
theorem botPlays_of_bit {k : ℕ} {A T : Tmpl} {a : PD.Action} (h : bitPlays k A T a) :
    ∃ N, EvalGraph N (pBot (instCode k A T)) (pBot (instCode k A T)) (pBot (instCode k A T)) (actCode a) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, EvalGraph.bot_iff.mpr hn⟩

/-- **A probe refuted by the opposite play**: the probe "`T`'s instance at `A` plays `a` against itself" is never
found, in any frame, when that instance plays `b ≠ a` (soundness, `closed_not_found`). -/
theorem probe_not_found_of_bit {k : ℕ} {T A : Tmpl} {a b : PD.Action} (hab : b ≠ a) (h : bitPlays k T A b)
    (hns : noSelfIdxF (.plays (.bot (inst (tauZoo k) T A)) (.bot (inst (tauZoo k) T A)) a) = true)
    (me opp : PD.Prog) (K : ℕ) :
    ¬ LenBox TAct K (guardCode (templateCode (.plays (.bot (inst (tauZoo k) T A)) (.bot (inst (tauZoo k) T A)) a))
      (progCode me) (progCode opp)) := by
  obtain ⟨N, hN⟩ := botPlays_of_bit h
  refine closed_not_found hns (not_models_plays (properPlayer_bot _) (properPlayer_bot _) hab (N := N) ?_) K
  rw [progCode_bot_inst]
  exact hN

/-- **The Dupoc-shaped searcher's SND slot** (`A ∈ {dupoc, maxconfidence, minconfidence}`): the probe of `T`'s
instance at `A` is false because that instance defects — else-branch D. -/
theorem dupocLike_D_of_probe_false {k : ℕ} {A T : Tmpl}
    (hc : instCode k A T = pSearch k (templateCode (probe (inst (tauZoo k) T A))) (pConst 0) (pConst 1))
    (hns : noSelfIdxF (probe (inst (tauZoo k) T A)) = true) (h : bitPlays k T A .D) : bitPlays k A T .D :=
  bit_search_not_found k hc (fun me opp ↦ probe_not_found_of_bit (by decide) h hns me opp k)
    (fun _ _ ↦ const_play 0 _ _ _) hns

/-- **The Dupoc-shaped searcher's FLOOR-SIDE slot**: when its own probe is NOT found, the else-branch D. -/
theorem dupocLike_floor_D {k : ℕ} {A T : Tmpl}
    (hc : instCode k A T = pSearch k (templateCode (probe (inst (tauZoo k) T A))) (pConst 0) (pConst 1))
    (hns : noSelfIdxF (probe (inst (tauZoo k) T A)) = true)
    (hn : ¬ LenBox TAct k (guardCodeB (templateCode (probe (inst (tauZoo k) T A)))
      (pBot (instCode k A T)) (pBot (instCode k A T)) k)) : bitPlays k A T .D := by
  rw [hingeB _ _ _ _ hns, hc] at hn
  exact bitPlays_of_eq hc ⟨_, search_else _ hn (const_play 0 _ _ _) hns⟩

/-- **Cupod's SND slot**: the defection probe of `T`'s instance at Cupod is false because that instance
cooperates — else-branch C. -/
theorem cupod_C_of_probeD_false {k : ℕ} {T : Tmpl}
    (hc : instCode k .cupod T = pSearch k (templateCode (probeD (inst (tauZoo k) T .cupod))) (pConst 1) (pConst 0))
    (hns : noSelfIdxF (probeD (inst (tauZoo k) T .cupod)) = true) (h : bitPlays k T .cupod .C) :
    bitPlays k .cupod T .C :=
  bit_search_not_found k hc (fun me opp ↦ probe_not_found_of_bit (by decide) h hns me opp k)
    (fun _ _ ↦ const_play 0 _ _ _) hns

/-- **Cupod's FLOOR-SIDE slot**: its own defection probe not found — else-branch C. -/
theorem cupod_floor_C {k : ℕ} {T : Tmpl}
    (hc : instCode k .cupod T = pSearch k (templateCode (probeD (inst (tauZoo k) T .cupod))) (pConst 1) (pConst 0))
    (hns : noSelfIdxF (probeD (inst (tauZoo k) T .cupod)) = true)
    (hn : ¬ LenBox TAct k (guardCodeB (templateCode (probeD (inst (tauZoo k) T .cupod)))
      (pBot (instCode k .cupod T)) (pBot (instCode k .cupod T)) k)) : bitPlays k .cupod T .C := by
  rw [hingeB _ _ _ _ hns, hc] at hn
  exact bitPlays_of_eq hc ⟨_, search_else _ hn (const_play 0 _ _ _) hns⟩

/-! The same kit on STORED (budget-abstracted) templates `templateCodeAt … k` — the instances whose probed hypothesis
instance carries the budget (route (c) made generic, 2026-10-01). -/

theorem dupocLike_D_of_probe_false_at {k : ℕ} {A T : Tmpl}
    (hc : instCode k A T = pSearch k (templateCodeAt (probe (inst (tauZoo k) T A)) k) (pConst 0) (pConst 1))
    (hns : noSelfIdxF (probe (inst (tauZoo k) T A)) = true) (h : bitPlays k T A .D) : bitPlays k A T .D :=
  bit_search_not_found_at k hc (fun me opp ↦ probe_not_found_of_bit (by decide) h hns me opp k)
    (fun _ _ ↦ const_play 0 _ _ _) hns

theorem dupocLike_floor_D_at {k : ℕ} {A T : Tmpl}
    (hc : instCode k A T = pSearch k (templateCodeAt (probe (inst (tauZoo k) T A)) k) (pConst 0) (pConst 1))
    (hns : noSelfIdxF (probe (inst (tauZoo k) T A)) = true)
    (hn : ¬ LenBox TAct k (guardCodeB (templateCode (probe (inst (tauZoo k) T A)))
      (pBot (instCode k A T)) (pBot (instCode k A T)) k)) : bitPlays k A T .D := by
  rw [hingeB _ _ _ _ hns, hc] at hn
  exact bitPlays_of_eq hc ⟨_, search_else_at _ hn (const_play 0 _ _ _) hns⟩

theorem cupod_C_of_probeD_false_at {k : ℕ} {T : Tmpl}
    (hc : instCode k .cupod T = pSearch k (templateCodeAt (probeD (inst (tauZoo k) T .cupod)) k) (pConst 1) (pConst 0))
    (hns : noSelfIdxF (probeD (inst (tauZoo k) T .cupod)) = true) (h : bitPlays k T .cupod .C) :
    bitPlays k .cupod T .C :=
  bit_search_not_found_at k hc (fun me opp ↦ probe_not_found_of_bit (by decide) h hns me opp k)
    (fun _ _ ↦ const_play 0 _ _ _) hns

theorem cupod_floor_C_at {k : ℕ} {T : Tmpl}
    (hc : instCode k .cupod T = pSearch k (templateCodeAt (probeD (inst (tauZoo k) T .cupod)) k) (pConst 1) (pConst 0))
    (hns : noSelfIdxF (probeD (inst (tauZoo k) T .cupod)) = true)
    (hn : ¬ LenBox TAct k (guardCodeB (templateCode (probeD (inst (tauZoo k) T .cupod)))
      (pBot (instCode k .cupod T)) (pBot (instCode k .cupod T)) k)) : bitPlays k .cupod T .C := by
  rw [hingeB _ _ _ _ hns, hc] at hn
  exact bitPlays_of_eq hc ⟨_, search_else_at _ hn (const_play 0 _ _ _) hns⟩

theorem prudent_D_of_outer_false_at {k : ℕ} {T : Tmpl} {inner : ℕ}
    (hc : instCode k .prudent T = pSearch k (templateCodeAt (probe (inst (tauZoo k) T .prudent)) k) inner (pConst 1))
    (hns : noSelfIdxF (probe (inst (tauZoo k) T .prudent)) = true) (h : bitPlays k T .prudent .D) :
    bitPlays k .prudent T .D :=
  bit_search_not_found_at k hc (fun me opp ↦ probe_not_found_of_bit (by decide) h hns me opp k)
    (fun _ _ ↦ const_play 0 _ _ _) hns

/-- Prudent's inner-false slot with the OUTER template stored abstracted and the inner one unabstracted. -/
theorem prudent_D_of_inner_false_at {k : ℕ} {T : Tmpl} {g : PD.Formula}
    (hc : instCode k .prudent T = pSearch k (templateCodeAt g k)
      (pSearch k (templateCode (probeD (inst (tauZoo k) T .defect))) (pConst 0) (pConst 1)) (pConst 1))
    (hg : noSelfIdxF g = true) (hns : noSelfIdxF (probeD (inst (tauZoo k) T .defect)) = true)
    (h : bitPlays k T .defect .C) : bitPlays k .prudent T .D := by
  apply bitPlays_of_eq hc
  have hn := probe_not_found_of_bit (by decide) h hns (.bot (inst (tauZoo k) .prudent T))
    (.bot (inst (tauZoo k) .prudent T)) k
  rw [progCode_bot_inst, hc] at hn
  exact ⟨_, search_either_at g (search_else _ hn (const_play 0 _ _ _) hns) (const_play 1 _ _ _) hg⟩

/-- Prudent's inner-false slot with BOTH templates stored abstracted. -/
theorem prudent_D_of_inner_false_at₂ {k : ℕ} {T : Tmpl} {g : PD.Formula}
    (hc : instCode k .prudent T = pSearch k (templateCodeAt g k)
      (pSearch k (templateCodeAt (probeD (inst (tauZoo k) T .defect)) k) (pConst 0) (pConst 1)) (pConst 1))
    (hg : noSelfIdxF g = true) (hns : noSelfIdxF (probeD (inst (tauZoo k) T .defect)) = true)
    (h : bitPlays k T .defect .C) : bitPlays k .prudent T .D := by
  apply bitPlays_of_eq hc
  have hn := probe_not_found_of_bit (by decide) h hns (.bot (inst (tauZoo k) .prudent T))
    (.bot (inst (tauZoo k) .prudent T)) k
  rw [progCode_bot_inst, hc] at hn
  exact ⟨_, search_either_at g (search_else_at _ hn (const_play 0 _ _ _) hns) (const_play 1 _ _ _) hg⟩

theorem prudent_floor_D_at {k : ℕ} {T : Tmpl} {g : PD.Formula} {inner : ℕ}
    (hc : instCode k .prudent T = pSearch k (templateCodeAt g k) inner (pConst 1)) (hg : noSelfIdxF g = true)
    (hn : ¬ LenBox TAct k (guardCodeB (templateCode g) (pBot (instCode k .prudent T)) (pBot (instCode k .prudent T)) k)) :
    bitPlays k .prudent T .D := by
  rw [hingeB _ _ _ _ hg, hc] at hn
  exact bitPlays_of_eq hc ⟨_, search_else_at _ hn (const_play 0 _ _ _) hg⟩

/-- **Prudent's slots where the OUTER probe is false**: `T`'s instance at Prudent defects — D. -/
theorem prudent_D_of_outer_false {k : ℕ} {T : Tmpl} {inner : ℕ}
    (hc : instCode k .prudent T = pSearch k (templateCode (probe (inst (tauZoo k) T .prudent))) inner (pConst 1))
    (hns : noSelfIdxF (probe (inst (tauZoo k) T .prudent)) = true) (h : bitPlays k T .prudent .D) :
    bitPlays k .prudent T .D :=
  bit_search_not_found k hc (fun me opp ↦ probe_not_found_of_bit (by decide) h hns me opp k)
    (fun _ _ ↦ const_play 0 _ _ _) hns

/-- **Prudent's slots where the INNER (prudence) probe is false**: `T`'s instance at the defector does not defect
against itself, so the then-branch of the outer search plays D too — D whatever the outer verdict. -/
theorem prudent_D_of_inner_false {k : ℕ} {T : Tmpl} {g : PD.Formula}
    (hc : instCode k .prudent T = pSearch k (templateCode g)
      (pSearch k (templateCode (probeD (inst (tauZoo k) T .defect))) (pConst 0) (pConst 1)) (pConst 1))
    (hg : noSelfIdxF g = true) (hns : noSelfIdxF (probeD (inst (tauZoo k) T .defect)) = true)
    (h : bitPlays k T .defect .C) : bitPlays k .prudent T .D := by
  apply bitPlays_of_eq hc
  have hn := probe_not_found_of_bit (by decide) h hns (.bot (inst (tauZoo k) .prudent T))
    (.bot (inst (tauZoo k) .prudent T)) k
  rw [progCode_bot_inst, hc] at hn
  exact ⟨_, search_either g (search_else _ hn (const_play 0 _ _ _) hns) (const_play 1 _ _ _) hg⟩

/-- **Prudent's FLOOR-SIDE slot**: its own OUTER probe not found — else-branch D. -/
theorem prudent_floor_D {k : ℕ} {T : Tmpl} {g : PD.Formula} {inner : ℕ}
    (hc : instCode k .prudent T = pSearch k (templateCode g) inner (pConst 1)) (hg : noSelfIdxF g = true)
    (hn : ¬ LenBox TAct k (guardCodeB (templateCode g) (pBot (instCode k .prudent T)) (pBot (instCode k .prudent T)) k)) :
    bitPlays k .prudent T .D := by
  rw [hingeB _ _ _ _ hg, hc] at hn
  exact bitPlays_of_eq hc ⟨_, search_else _ hn (const_play 0 _ _ _) hg⟩

end kit

end ArithS.Tau
