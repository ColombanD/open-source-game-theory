import ArithS.Cells.JustEngine
import ArithS.Cells.PrudentLoose
import ArithS.Cells.Transposition
import ArithS.Cells.KhatCells
import PrisonersDilemma.Bots.DIMDID

/-!
# ArithS.Cells.Dimdid — the PA-`S'` row of `DIMDID` ("defect iff my defection provably implies yours")

`DIMDID k := .search k (.impl (.plays .self .opp .D) (.plays .opp .self .D)) (.const D) (.const C)`
(`engine/.../Bots/DIMDID.lean`, 2026-10-13). **DIMDID is the C/D transposition of CIMCIC**:
`(CIMCIC k).transpose = DIMDID k` by `rfl` (`DIMDID_eq_transpose`), so on codes it is the generic engine
searcher `SV (gI .D) 1 k` — the "transposed world"'s CIMCIC of `Cells/JustEngine.lean` — and the general
transposition theorem (`Cells/Transposition.lean`, `outcomeSpecA_transpose`) hands over every CIMCIC cell whose
partner's transposition is in the zoo: `DIMDID × DefectBot = τ(CIMCIC × CooperateBot)`, `DIMDID × CupodBot =
τ(CIMCIC × DupocBot)`, `DIMDID × DIMDID = τ(CIMCIC × CIMCIC)` (those three cells are stated directly in
`Outcome/Matrix/DIMDID.lean` from the CIMCIC cells). It has NO engine cell — every result here is `S'`-only
(`docs/notes/ROUTE_B_CENSUS.md`, "S'-only cells"). Thirteen cells, DIMDID on the left: the ten `body` bots,
CIMCIC, PrudentBot and itself.

The one new argument — **the self-defeating guard** (`dimdid_selfref_not_found`, the dual of
`cimcic_selfref_not_found`): a proof of "I defect against `opp` ⇒ `opp` defects against me" makes DIMDID defect,
so by soundness `opp` defects — against the fact when `opp` cooperates. So against every opponent that cooperates
with it, DIMDID's guard is TRUE (vacuously) but never found, and DIMDID cooperates: `(C, C)` with CooperateBot,
TitForTatBot, CupodTrollBot (every `k`) and with DBot, EBot (large `k`: their probe is DIMDID's FOUND defection
against `.bot DefectBot`, `pos_DIMDID_vs_botDB`, a `TAct`-theorem instance). These are the SND/POS classes with
the soundness step pointing the other way.

1. **The code** (`phiDd`, `progCode_DIMDID_search`, `progCode_DIMDID_SV`), the self-defeating lemma and the
   plays it forces (`dimdid_C_of_probe`, `dimdid_D_of_found`, `dimdid_C_of_not_found`).
2. **The found probe**: DIMDID defects against `.bot DefectBot` in every model above a threshold
   (`dimdid_botDB_V`, from `tact_qDdB1`), and its τ-twin `cimcic_botCB_V` (CIMCIC cooperates with
   `.bot CooperateBot`) — the pair the prudence `k̂`-chain of `Cells/PrudentLoose.lean` consumes.
3. **The SND/POS cells**: `snd_DIMDID_vs_CooperateBot`, `snd_DIMDID_vs_TitForTatBot`, `snd_DIMDID_vs_CupodTrollBot`
   (the `.eq` guard false, `progCode_DIMDID_ne_CupodBot` by the semantic separation `templateCode_phiDd_ne_phiCu`),
   `pos_DIMDID_vs_DBot`, `pos_DIMDID_vs_EBot`.
4. **The Löb cells**, as conjunction families over described players (`DP`, `qF` of `Cells/JustEngine.lean`;
   `found_pL` is the world-free `found_world`): `loeb_DIMDID_vs_OBot` `(D, D)` — DIMDID's guard against OBot and
   against `.bot DefectBot` (OBot defects against anyone who defects against `.bot DefectBot`, whatever its first
   probe: `obot_D_of_any_V`, the transposed OBot `obotT_C_of_any_V`); `loeb_DIMDID_vs_DIMCID` `(D, D)` — DIMDID's
   guard against DIMCID and DIMCID's against DIMDID, each the other's consequent.
5. **The floors**: three GENUINE two-hinge dichotomies, DIMDID's own guard `A_k` the outer hinge, the partner's
   guard `B_k` nested under `¬A_k` (the shape of `dich_WaryBot_vs_DupocBot`): `dich_DIMDID_vs_DupocBot`,
   `dich_DIMDID_vs_CIMCIC`, `dich_DIMDID_vs_PrudentBot`. `A_k ⇒ (D, D)` (DIMDID defects, the partner's guard is
   false by soundness); `¬A_k ⇒` DIMDID C, then `¬B_k ⇒` the partner defects — the engine side `(C, D)` — and
   `B_k ⇒` the partner cooperates (for Prudent, with its prudence guard FOUND: `prudence_found_vs_DIMDID`, the
   `k̂`-chain on the found probe of §2). Both hinges are bounded-consistency-type sentences: `A_k` says a short
   proof of `□_k A → ¬□_k B`-shaped consistency exists, `B_k` that the partner's guard — true only through DIMDID's
   else-play — is provable within `k`. Registered in `Outcome/Floors.lean`, censused by `#check_floorA_theorems` on
   THIS file.

Conventions (`docs/notes/ARITH_TRAPS.md`): every threshold EXISTENTIAL; `simp` never sees a closed quote;
`omega` is never asked about `V`; at `V = ℕ` the V-generic `≤` is bridged by `le_def`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

/-! ### 1. The code, the self-defeating guard, the plays -/

section code

/-- DIMDID's guard: "my defecting implies your defecting" — `phiC.transpose`. -/
def phiDd : PD.Formula := .impl (.plays .self .opp .D) (.plays .opp .self .D)


theorem fragP_CIMCIC (k : ℕ) : fragP (CIMCIC k) = true := rfl

lemma properPlayer_DIMDID (k : ℕ) : ProperPlayer (DIMDID k) := ⟨by simp [DIMDID], by simp [DIMDID]⟩

lemma progCode_DIMDID_search (k : ℕ) :
    progCode (DIMDID k) = pSearch k (templateCode phiDd) (pConst 1) (pConst 0) := by
  rw [DIMDID, progCode_search_noSnap _ _ _ _ rfl]; simp [phiDd, actCode]


lemma lMap_swap_gI_D : Semiformula.lMap swap (gI .D) = gI .C := lMap_swap_template _ rfl

/-- **The engine's `DIMDID k` is the generic searcher `SV (gI .D) 1 k`** (then-branch `D`). -/
theorem progCode_DIMDID_SV (k : ℕ) : progCode (DIMDID k) = SV (V := ℕ) (gI .D) 1 k := by
  rw [progCode_DIMDID_search, SV_nat, templateCode_eq_quote_template phiDd rfl]; rfl

/-- **DIMDID's guard against an opponent that cooperates with it is SELF-DEFEATING**: a proof of "I play D
against `opp` ⇒ `opp` plays D against me" makes DIMDID defect, so by soundness `opp` defects — against the
fact. So it is never found (`cimcic_selfref_not_found` with the actions exchanged). -/
theorem dimdid_selfref_not_found (k : ℕ) {opp : PD.Prog} (hopp : ProperPlayer opp) {N : ℕ}
    (h : EvalGraph N (progCode opp) (progCode (DIMDID k)) (progCode opp) 0) :
    ¬ LenBox TAct k (guardCode (templateCode phiDd) (progCode (DIMDID k)) (progCode opp)) := by
  intro hf
  have hD : EvalGraph 2 (progCode (DIMDID k)) (progCode opp) (progCode (DIMDID k)) 1 := by
    rw [progCode_DIMDID_search] at hf ⊢
    exact search_then phiDd hf (const_play _ _ _ _)
  have hT : ℕ↓[LAct] ⊧ sentenceAt (DIMDID k) opp phiDd :=
    models_sentenceAt_of_lenBox (φ := phiDd) (me := DIMDID k) (opp := opp) hf
  rw [← sentenceAt_subst (DIMDID k) opp (properPlayer_DIMDID k) hopp phiDd rfl] at hT
  change ℕ↓[LAct] ⊧ sentenceAt (DIMDID k) opp (.impl (.plays (DIMDID k) opp .D) (.plays opp (DIMDID k) .D)) at hT
  rw [models_sentenceAt_impl, models_sentenceAt_plays _ _ _ _ _ (properPlayer_DIMDID k) hopp,
    models_sentenceAt_plays _ _ _ _ _ hopp (properPlayer_DIMDID k)] at hT
  obtain ⟨N', hN'⟩ := hT ⟨2, hD⟩
  exact absurd (EvalGraph.unique' hN' h) (by decide)

/-- DIMDID cooperates with any proper opponent that cooperates with it (fuel 2). -/
theorem dimdid_C_of_probe (k : ℕ) {opp : PD.Prog} (hopp : ProperPlayer opp) {N : ℕ}
    (h : EvalGraph N (progCode opp) (progCode (DIMDID k)) (progCode opp) 0) :
    EvalGraph 2 (progCode (DIMDID k)) (progCode opp) (progCode (DIMDID k)) 0 := by
  have hn := dimdid_selfref_not_found k hopp h
  rw [progCode_DIMDID_search] at hn ⊢
  exact search_else phiDd hn (const_play _ _ _ _)

/-- DIMDID defects when it FINDS its guard (fuel 2). -/
theorem dimdid_D_of_found (k : ℕ) {opp : PD.Prog}
    (hy : LenBox TAct k (guardCode (templateCode phiDd) (progCode (DIMDID k)) (progCode opp))) :
    EvalGraph 2 (progCode (DIMDID k)) (progCode opp) (progCode (DIMDID k)) 1 := by
  rw [progCode_DIMDID_search] at hy ⊢
  exact search_then phiDd hy (const_play _ _ _ _)

/-- DIMDID cooperates when its guard is NOT found (fuel 2). -/
theorem dimdid_C_of_not_found (k : ℕ) {opp : PD.Prog}
    (hn : ¬ LenBox TAct k (guardCode (templateCode phiDd) (progCode (DIMDID k)) (progCode opp))) :
    EvalGraph 2 (progCode (DIMDID k)) (progCode opp) (progCode (DIMDID k)) 0 := by
  rw [progCode_DIMDID_search] at hn ⊢
  exact search_else phiDd hn (const_play _ _ _ _)

/-- DIMDID cooperates with `.bot CooperateBot` (self-defeating guard), every `k`. -/
theorem snd_DIMDID_vs_botCB (k : ℕ) :
    EvalGraph 2 (progCode (DIMDID k)) (pBot (pConst 0)) (progCode (DIMDID k)) 0 := by
  have := dimdid_C_of_probe k (opp := .bot CooperateBot) properPlayer_botCB (N := 2)
    (by rw [progCode_botCB]; exact bot_const_play 0 _ _ _)
  rwa [progCode_botCB] at this

end code

/-! ### 2. The found probe: DIMDID defects against `.bot DefectBot` in every model (and its τ-twin) -/

section probe

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The implication guard "if I play `a` against the opponent, it plays `b` against me" filled with two
triples** (`eval_qT_plays_opp_self` for the implication shape, both actions free). -/
theorem eval_qT_impl (a b : PD.Action) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) (k : V) {me opp : V}
    (hme : revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
      (X.val (s := stdReadingV V) ![k] Empty.elim) = me)
    (hopp : revalue (U'.val (s := stdReadingV V) ![] Empty.elim) (W'.val (s := stdReadingV V) ![] Empty.elim)
      (X'.val (s := stdReadingV V) ![k] Empty.elim) = opp) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim
        (qT (template (.impl (.plays .self .opp a) (.plays .opp .self b))) X U W X' U' W') ↔
      ((∃ n, EvalGraph n me opp me (actCode a : V)) → (∃ n, EvalGraph n opp me opp (actCode b : V))) := by
  rw [eval_qT_iff, template_impl]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq,
    eval_template_plays_self_opp_V, eval_template_plays_opp_self_V, Matrix.cons_val]
  rw [hme, hopp]

/-- DIMDID's guard against `.bot DefectBot` as a fixed formula: "I play D against `.bot DefectBot` ⇒
`.bot DefectBot` plays D against me" (DIMDID by its `SV` triple, the probe by `(cl TB0, cterm D, cterm C)`). -/
noncomputable def qDdB1 : Semisentence LAct 1 :=
  qT (gI .D) (TS (gI .D) 1) (uS (gI .D) 1) (wS (gI .D) 1) (cl TB0) (cterm Act.D) (cterm Act.C)

theorem guardCode_DdB1 (k : V) :
    guardCode (⌜gI .D⌝ : V) (SV (gI .D) 1 k) (pBot (pConst 1)) = instB (⌜qDdB1⌝ : V) k :=
  guardCode_qT_eq_instB (gI .D) k _ _ _ _ _ _ (hX_SV (gI .D) 1 (Or.inr rfl) k) (hU_SV (gI .D) 1 (Or.inr rfl) k)
    (hW_SV (gI .D) 1 (Or.inr rfl) k) (hX_bot_one k) hU_D_bot_one hW_C_bot_one

/-- `qDdB1` is a `TAct`-theorem in `k`: its consequent is a closed truth in both readings. -/
theorem tact_qDdB1 : TAct ⊢ ∀¹ qDdB1 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qDdB1, eval_qT_impl .D .D _ _ _ _ _ _ x (desc_SV (gI .D) 1 (Or.inr rfl) x) (val_desc_bot_one x),
      actCode_D_cast]
    exact fun _ ↦ bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qDdB1, eval_qT_swap, lMap_swap_gI_D, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_D, lMap_swap_cterm_C,
      eval_qT_impl .C .C _ _ _ _ _ _ x (descT_SV (gI .D) 1 (Or.inr rfl) x) (val_desc_bot_zero x),
      actCode_C_cast]
    exact fun _ ↦ bot_const_play_V _ _ _

/-- **DIMDID defects against `.bot DefectBot` in every model, above a standard threshold** (fuel 2). -/
theorem dimdid_botDB_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (SV (gI .D) 1 k) (pBot (pConst 1)) (SV (gI .D) 1 k) 1 := by
  obtain ⟨kHat, h⟩ := found_of_all_V tact_qDdB1
  refine ⟨kHat, fun V _ _ k hk ↦ ?_⟩
  have := SV_then_V (gI .D) 1 k (SV (gI .D) 1 k) (pBot (pConst 1)) (by rw [guardCode_DdB1]; exact h V k hk)
  rwa [Nat.cast_one] at this

/-- The τ-twin: CIMCIC's guard against `.bot CooperateBot` on CIMCIC's `SV` triple. -/
noncomputable def qCiSB0 : Semisentence LAct 1 :=
  qT (gI .C) (TS (gI .C) 0) (uS (gI .C) 0) (wS (gI .C) 0) (cl TB0) (cterm Act.C) (cterm Act.D)

theorem guardCode_CiSB0 (k : V) :
    guardCode (⌜gI .C⌝ : V) (SV (gI .C) 0 k) (pBot (pConst 0)) = instB (⌜qCiSB0⌝ : V) k :=
  guardCode_qT_eq_instB (gI .C) k _ _ _ _ _ _ (hX_SV (gI .C) 0 (Or.inl rfl) k) (hU_SV (gI .C) 0 (Or.inl rfl) k)
    (hW_SV (gI .C) 0 (Or.inl rfl) k) (hX_bot_zero k) hU_C_bot_zero hW_D_bot_zero

theorem tact_qCiSB0 : TAct ⊢ ∀¹ qCiSB0 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCiSB0, eval_qT_impl .C .C _ _ _ _ _ _ x (desc_SV (gI .C) 0 (Or.inl rfl) x) (val_desc_bot_zero x),
      actCode_C_cast]
    exact fun _ ↦ bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCiSB0, eval_qT_swap, lMap_swap_gI_C, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_impl .D .D _ _ _ _ _ _ x (descT_SV (gI .C) 0 (Or.inl rfl) x) (val_desc_bot_one x),
      actCode_D_cast]
    exact fun _ ↦ bot_const_play_V _ _ _

/-- **CIMCIC cooperates with `.bot CooperateBot` in every model, above a standard threshold** (fuel 2), on its
`SV` code — the τ-twin of `dimdid_botDB_V` (`cimcic_botCB_V` of `Cells/KhatCells.lean` is the same fact on the hand twin `CimcicV`). -/
theorem cimcicS_botCB_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (SV (gI .C) 0 k) (pBot (pConst 0)) (SV (gI .C) 0 k) 0 := by
  obtain ⟨kHat, h⟩ := found_of_all_V tact_qCiSB0
  refine ⟨kHat, fun V _ _ k hk ↦ ?_⟩
  have := SV_then_V (gI .C) 0 k (SV (gI .C) 0 k) (pBot (pConst 0)) (by rw [guardCode_CiSB0]; exact h V k hk)
  rwa [Nat.cast_zero] at this

/-- **DIMDID defects against `.bot DefectBot` for all large `k`** (its guard is found: a `TAct`-theorem instance). -/
theorem pos_DIMDID_vs_botDB :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (progCode (DIMDID k)) (pBot (pConst 1)) (progCode (DIMDID k)) 1 := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qDdB1
    (fun k ↦ guardCode (templateCode phiDd) (progCode (DIMDID k)) (pBot (pConst 1)))
    (fun k ↦ by rw [progCode_DIMDID_SV, templateCode_eq_quote_template phiDd rfl]; exact guardCode_DdB1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hg := h k hk
  rw [progCode_DIMDID_search] at hg ⊢
  exact search_then phiDd hg (const_play _ _ _ _)

/-- **Prudent's prudence guard against `DIMDID k` is FOUND for all large `k`**: DIMDID's defection against
`.bot DefectBot` is its then-branch on a `TAct`-theorem (the `k̂`-chain, `prudence_found_of_SV`). -/
theorem prudence_found_vs_DIMDID :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode phiPi) (progCode (PrudentBot k)) (progCode (DIMDID k))) := by
  obtain ⟨k₀, h⟩ := prudence_found_of_SV (gI .D) 1 (Or.inr rfl) dimdid_botDB_V
    (by rw [lMap_swap_gI_D]; exact cimcicS_botCB_V)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [progCode_PrudentBot, progCode_DIMDID_SV, templateCode_phiPi]
  exact h k hk

end probe

/-! ### 3. The SND/POS cells -/

section sndPos

/-- `DIMDID × CooperateBot = (C, C)` at every `k`: the guard is self-defeating. -/
theorem snd_DIMDID_vs_CooperateBot (k : ℕ) :
    EvalGraph 2 (progCode (DIMDID k)) (progCode CooperateBot) (progCode (DIMDID k)) (actCode .C) ∧
    EvalGraph 2 (progCode CooperateBot) (progCode (DIMDID k)) (progCode CooperateBot) (actCode .C) :=
  ⟨dimdid_C_of_probe k sfp_CooperateBot.1 (by rw [progCode_CB]; exact const_play 0 _ _ 0),
   by rw [progCode_CB]; exact const_play 1 _ _ _⟩

/-- `DIMDID × TitForTatBot = (C, C)` at every `k` (fuel 4): TFT sees DIMDID cooperate with `.bot CooperateBot`. -/
theorem snd_DIMDID_vs_TitForTatBot (k : ℕ) :
    EvalGraph 4 (progCode (DIMDID k)) (progCode TitForTatBot) (progCode (DIMDID k)) (actCode .C) ∧
    EvalGraph 4 (progCode TitForTatBot) (progCode (DIMDID k)) (progCode TitForTatBot) (actCode .C) := by
  have hT := tft_C_of_probe_C (snd_DIMDID_vs_botCB k)
  exact ⟨EvalGraph.mono_le (by omega) (dimdid_C_of_probe k sfp_TitForTatBot.1 hT), hT⟩

/-- DIMDID's and Cupod's templates differ: at the frame `(CooperateBot, CooperateBot)` DIMDID's guard is true
(its antecedent is false) while "the opponent defects against me" is false. -/
lemma models_phiDd_at_CB_CB : ℕ↓[LAct] ⊧ sentenceAt CooperateBot CooperateBot phiDd := by
  rw [← sentenceAt_subst CooperateBot CooperateBot sfp_CooperateBot.1 sfp_CooperateBot.1 _ rfl]
  show ℕ↓[LAct] ⊧ sentenceAt CooperateBot CooperateBot
    (.impl (.plays CooperateBot CooperateBot .D) (.plays CooperateBot CooperateBot .D))
  rw [models_sentenceAt_impl]
  exact id

lemma not_models_phiCu_at_CB_CB : ¬ ℕ↓[LAct] ⊧ sentenceAt CooperateBot CooperateBot phiCu := by
  rw [← sentenceAt_subst CooperateBot CooperateBot sfp_CooperateBot.1 sfp_CooperateBot.1 _ rfl]
  show ¬ ℕ↓[LAct] ⊧ sentenceAt CooperateBot CooperateBot (.plays CooperateBot CooperateBot .D)
  rw [models_sentenceAt_plays _ _ _ _ _ sfp_CooperateBot.1 sfp_CooperateBot.1]
  rintro ⟨N, hN⟩
  have hC : EvalGraph 1 (progCode CooperateBot) (progCode CooperateBot) (progCode CooperateBot) 0 := by
    rw [progCode_CB]; exact const_play 0 _ _ 0
  exact absurd (EvalGraph.unique' hN hC) (by decide)

lemma templateCode_phiDd_ne_phiCu : templateCode phiDd ≠ templateCode phiCu :=
  templateCode_ne_of_models CooperateBot CooperateBot models_phiDd_at_CB_CB not_models_phiCu_at_CB_CB

lemma progCode_DIMDID_ne_CupodBot (k : ℕ) : progCode (DIMDID k) ≠ progCode (CupodBot k) := by
  rw [progCode_DIMDID_search, progCode_CupodBot]
  intro e
  exact templateCode_phiDd_ne_phiCu (pSearch_inj e).2.1

/-- `DIMDID × CupodTrollBot = (C, C)` at every `k`: the troll's `.eq` guard is false (DIMDID is not CupodBot),
so it cooperates, and DIMDID's guard is then self-defeating. -/
theorem snd_DIMDID_vs_CupodTrollBot (k : ℕ) :
    EvalGraph 2 (progCode (DIMDID k)) (progCode (CupodTrollBot k)) (progCode (DIMDID k)) (actCode .C) ∧
    EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (DIMDID k)) (progCode (CupodTrollBot k)) (actCode .C) := by
  have hT := ctb_C_of_ne k (properPlayer_DIMDID k) (progCode_DIMDID_ne_CupodBot k)
  exact ⟨dimdid_C_of_probe k (properPlayer_CupodTrollBot k) hT, hT⟩

/-- `DIMDID × DBot = (C, C)` for all large `k` (fuel 4): DBot sees DIMDID defect against `.bot DefectBot` (found)
and cooperates; DIMDID's guard against DBot is then self-defeating. -/
theorem pos_DIMDID_vs_DBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 4 (progCode (DIMDID k)) (progCode DBot) (progCode (DIMDID k)) (actCode .C) ∧
      EvalGraph 4 (progCode DBot) (progCode (DIMDID k)) (progCode DBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := pos_DIMDID_vs_botDB
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hD := dbot_C_of_probe_D (h k hk)
  exact ⟨EvalGraph.mono_le (by omega) (dimdid_C_of_probe k sfp_DBot.1 hD), hD⟩

/-- `DIMDID × EBot = (C, C)` for all large `k` (fuel 5): EBot sees DIMDID defect against `.bot DefectBot` and
cooperate with `.bot CooperateBot`, and cooperates. -/
theorem pos_DIMDID_vs_EBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 5 (progCode (DIMDID k)) (progCode EBot) (progCode (DIMDID k)) (actCode .C) ∧
      EvalGraph 5 (progCode EBot) (progCode (DIMDID k)) (progCode EBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := pos_DIMDID_vs_botDB
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hE := ebot_C_of_probes (h k hk) (snd_DIMDID_vs_botCB k)
  exact ⟨EvalGraph.mono_le (by omega) (dimdid_C_of_probe k sfp_EBot.1 hE), hE⟩

end sndPos

/-! ### 4. The Löb cells: conjunction families over described players -/

section loebKit

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Every guard of a list family is FOUND within the budget, for all large `k`, with its transposition**
(`found_world` without the world: `family_found` at `boundedInnerNec_sixteen`, then `boxes_pL_nat`). -/
theorem found_pL (q : Semisentence LAct 1) (rs : List (Semisentence LAct 1))
    (core : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
      (∀ r ∈ q :: rs, LenBox TAct k (instB (⌜r⌝ : V) k) ∧ LenBox TAct k (instB (⌜Semiformula.lMap swap r⌝ : V) k)) →
      ∀ r ∈ q :: rs, Semiformula.Eval (s := stdReading V) ![k] Empty.elim r ∧
        Semiformula.Eval (s := stdReading V) ![k] Empty.elim (Semiformula.lMap swap r)) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ∀ r ∈ q :: rs,
      LenBox TAct k (instB (⌜r⌝ : ℕ) k) ∧ LenBox TAct k (instB (⌜Semiformula.lMap swap r⌝ : ℕ) k) := by
  obtain ⟨k₀, hf⟩ := family_found _ boundedInnerNec_sixteen (loebSound_pL_above q rs 0 (fun V _ _ k _ hb ↦ core V k hb))
  refine ⟨k₀, fun k hk r hr ↦ ?_⟩
  obtain ⟨a, ha, hbox⟩ := hf k hk
  exact boxes_pL_nat _ _ 0 k a ha hbox r hr

/-- **A generic searcher's then-clause in a described frame**: its guard in the frame `(me, opp)` found within `k`
⇒ `SV g a k` plays `a` there (fuel 2). -/
theorem SV_then_qF (g : Semisentence LAct 6) (a : ℕ) (me opp : DP) (k : V)
    (h : LenBox TAct k (instB (⌜qF g me opp⌝ : V) k)) : EvalGraph 2 (me.val k) (opp.val k) (SV g a k) (a : V) := by
  rw [← guardCode_qF] at h
  exact SV_then_V g a k _ _ h

/-- A generic searcher always plays in any frame (fuel 3), whatever the verdict. -/
theorem SV_total3_V (g : Semisentence LAct 6) (a : ℕ) (k me opp : V) :
    ∃ r, EvalGraph 3 me opp (SV g a k) r := by
  rw [show (3 : V) = 1 + 1 + 1 by norm_num]
  show ∃ r, EvalGraph (1 + 1 + 1) me opp (pSearch k (⌜g⌝ : V) (pConst (a : V)) (pConst ((1 - a : ℕ) : V))) r
  by_cases h : LenBox TAct k (guardCode (⌜g⌝ : V) me opp)
  · refine ⟨(a : V), ?_⟩
    rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ g)]
    exact Or.inl ⟨h, EvalGraph.const_iff.mpr rfl⟩
  · refine ⟨((1 - a : ℕ) : V), ?_⟩
    rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ g)]
    exact Or.inr ⟨h, EvalGraph.const_iff.mpr rfl⟩

/-- The implication guard "if I play `a` against the opponent, it plays `b` against me" in a described frame
(`eval_qF_impl` with the two actions free). -/
theorem eval_qF_impl₂ (a b : PD.Action) (me opp : DP) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim
        (qF (template (.impl (.plays .self .opp a) (.plays .opp .self b))) me opp) ↔
      ((∃ n, EvalGraph n (me.val k) (opp.val k) (me.val k) (actCode a : V)) →
        (∃ n, EvalGraph n (opp.val k) (me.val k) (opp.val k) (actCode b : V))) :=
  eval_qT_impl a b _ _ _ _ _ _ k rfl rfl

/-- **A closed program as a described player** (`describes_closed` in both orientations). -/
noncomputable def DP.ofClosed (P : ℕ) : DP :=
  ⟨cl (canonicalMeta P), revalueUMeta P, revalueWMeta P, describes_closed P, by
    rw [lMap_swap_cl, lMap_swap_canonicalMeta, lMap_swap_revalueUMeta, lMap_swap_revalueWMeta]
    exact describes_closed (transposeCode P)⟩

lemma DP.ofClosed_val (P : ℕ) (k : V) : (DP.ofClosed P).val k = (P : V) := descVal_closed P k
lemma DP.ofClosed_tr_val (P : ℕ) (k : V) : (DP.ofClosed P).tr.val k = transposeCode (P : V) := descVal_closed_T P k

/-- DIMDID as a described player: the engine searcher `SV (gI .D) 1`. -/
noncomputable abbrev dpDd : DP := DP.ofSV (gI .D) 1 (Or.inr rfl)
/-- DIMCID as a described player: `SV (template phiD) 1` (`progCode_DIMCID_SV`). -/
noncomputable abbrev dpDi : DP := DP.ofSV (template phiD) 1 (Or.inr rfl)
/-- OBot as a described player. -/
noncomputable abbrev dpOB : DP := DP.ofClosed (progCode OBot)
/-- `.bot DefectBot` as a described player. -/
noncomputable abbrev dpBD : DP := DP.ofClosed (pBot (pConst 1))

lemma template_phiD_eq : template phiD = template (.impl (.plays .self .opp .C) (.plays .opp .self .D)) := rfl
lemma lMap_swap_template_phiD :
    Semiformula.lMap swap (template phiD) = template (.impl (.plays .self .opp .D) (.plays .opp .self .C)) :=
  lMap_swap_template phiD rfl

theorem progCode_DIMCID_SV (k : ℕ) : progCode (DIMCID k) = SV (V := ℕ) (template phiD) 1 k := by
  rw [progCode_DIMCID_search, SV_nat, templateCode_eq_quote_template phiD rfl]

lemma dpDd_val (k : V) : dpDd.val k = SV (gI .D) 1 k := DP.ofSV_val _ _ _ k
lemma dpDd_tr_val (k : V) : dpDd.tr.val k = SV (gI .C) 0 k := by
  rw [DP.ofSV_tr_val, lMap_swap_gI_D]
lemma dpDi_val (k : V) : dpDi.val k = SV (template phiD) 1 k := DP.ofSV_val _ _ _ k
lemma dpDi_tr_val (k : V) :
    dpDi.tr.val k = SV (template (.impl (.plays .self .opp .D) (.plays .opp .self .C))) 0 k := by
  rw [DP.ofSV_tr_val, lMap_swap_template_phiD]

/-! #### OBot in every model -/

/-- OBot's code in every model: `ite (sim opp (bot CooperateBot)) C (ite (sim opp (bot DefectBot)) C C D) D`. -/
noncomputable def OBotV : V :=
  pIte (pSim pOpp (pBot (pConst 0))) 0 (pIte (pSim pOpp (pBot (pConst 1))) 0 (pConst 0) (pConst 1)) (pConst 1)

/-- The transposed OBot: `ite (sim opp (bot DefectBot)) D (ite (sim opp (bot CooperateBot)) D D C) C`. -/
noncomputable def OBotTV : V :=
  pIte (pSim pOpp (pBot (pConst 1))) 1 (pIte (pSim pOpp (pBot (pConst 0))) 1 (pConst 1) (pConst 0)) (pConst 0)

lemma progCode_OBot_eq :
    progCode OBot = pIte (pSim pOpp (pBot (pConst 0))) 0 (pIte (pSim pOpp (pBot (pConst 1))) 0 (pConst 0) (pConst 1)) (pConst 1) := by
  simp [OBot, CooperateBot, DefectBot, actCode]

lemma OBotV_nat : OBotV (V := ℕ) = progCode OBot := by rw [progCode_OBot_eq]; rfl

lemma cast_OBot : ((progCode OBot : ℕ) : V) = OBotV := by
  rw [progCode_OBot_eq]
  simp [cast_pIte, cast_pSim, cast_pOpp, cast_pBot, cast_pConst, OBotV]

theorem transposeCode_OBotV : transposeCode (OBotV : V) = OBotTV := by
  unfold OBotV OBotTV transposeCode
  simp [revalueAction]

/-- OBot defects against `x` whenever `x` defects against `.bot DefectBot`, whatever `x` plays against
`.bot CooperateBot` (as long as it plays), in every model (fuel `+3`). -/
theorem obot_D_of_any_V {x n r : V} (h1 : EvalGraph (n + 1) x (pBot (pConst 0)) x r)
    (h2 : EvalGraph n x (pBot (pConst 1)) x 1) :
    EvalGraph (n + 1 + 1 + 1) OBotV x OBotV 1 := by
  unfold OBotV
  rw [EvalGraph.ite_iff]
  refine ⟨r, ?_, ?_⟩
  · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]; exact h1
  · by_cases hr : r = 0
    · refine Or.inl ⟨hr, ?_⟩
      rw [EvalGraph.ite_iff]
      refine ⟨1, ?_, Or.inr ⟨_root_.one_ne_zero, EvalGraph.const_iff.mpr rfl⟩⟩
      rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]; exact h2
    · exact Or.inr ⟨hr, EvalGraph.const_iff.mpr rfl⟩

/-- The transposed OBot cooperates with `x` whenever `x` cooperates with `.bot CooperateBot`, whatever `x` plays
against `.bot DefectBot` (as long as it plays), in every model (fuel `+3`). -/
theorem obotT_C_of_any_V {x n r : V} (h1 : EvalGraph (n + 1) x (pBot (pConst 1)) x r)
    (h2 : EvalGraph n x (pBot (pConst 0)) x 0) :
    EvalGraph (n + 1 + 1 + 1) OBotTV x OBotTV 0 := by
  unfold OBotTV
  rw [EvalGraph.ite_iff]
  refine ⟨r, ?_, ?_⟩
  · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]; exact h1
  · by_cases hr : r = 1
    · refine Or.inl ⟨hr, ?_⟩
      rw [EvalGraph.ite_iff]
      refine ⟨0, ?_, Or.inr ⟨_root_.zero_ne_one, EvalGraph.const_iff.mpr rfl⟩⟩
      rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]; exact h2
    · exact Or.inr ⟨hr, EvalGraph.const_iff.mpr rfl⟩

lemma dpOB_val (k : V) : dpOB.val k = OBotV := by rw [DP.ofClosed_val, cast_OBot]
lemma dpOB_tr_val (k : V) : dpOB.tr.val k = OBotTV := by rw [DP.ofClosed_tr_val, cast_OBot, transposeCode_OBotV]
lemma dpBD_val (k : V) : dpBD.val k = pBot (pConst 1) := by
  rw [DP.ofClosed_val, cast_pBot, cast_pConst, Nat.cast_one]
lemma dpBD_tr_val (k : V) : dpBD.tr.val k = pBot (pConst 0) := by
  rw [DP.ofClosed_tr_val, cast_pBot, cast_pConst, Nat.cast_one, transposeCode_pBot, transposeCode_pConst_one]

end loebKit

/-! #### DIMDID × OBot `(D, D)` -/

section dimdidOBot

/-- DIMDID's guard against OBot. -/
noncomputable def obQ : Semisentence LAct 1 := qF (gI .D) dpDd dpOB
/-- DIMDID's guard against `.bot DefectBot` (OBot's second probe). -/
noncomputable def obR : List (Semisentence LAct 1) := [qF (gI .D) dpDd dpBD]

/-- **The semantic core of DIMDID × OBot, in every model**: the boxes make DIMDID defect against OBot and against
`.bot DefectBot`, so OBot defects against DIMDID (the consequent of DIMDID's guard), and `.bot DefectBot` defects
against anyone; the transposed side is CIMCIC against the transposed OBot. -/
theorem ob_core (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V)
    (hb : ∀ r ∈ obQ :: obR, LenBox TAct k (instB (⌜r⌝ : V) k) ∧ LenBox TAct k (instB (⌜Semiformula.lMap swap r⌝ : V) k)) :
    (EvalGraph 2 (SV (gI .D) 1 k) OBotV (SV (gI .D) 1 k) 1 ∧ EvalGraph 5 OBotV (SV (gI .D) 1 k) OBotV 1) ∧
    ∀ r ∈ obQ :: obR, Semiformula.Eval (s := stdReading V) ![k] Empty.elim r ∧
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim (Semiformula.lMap swap r) := by
  have b₁ := hb obQ (by simp)
  have b₂ := hb (qF (gI .D) dpDd dpBD) (by simp [obR])
  -- the standard side
  have e₁ := SV_then_qF (gI .D) 1 dpDd dpOB k b₁.1
  rw [dpDd_val, dpOB_val, Nat.cast_one] at e₁
  have e₂ := SV_then_qF (gI .D) 1 dpDd dpBD k b₂.1
  rw [dpDd_val, dpBD_val, Nat.cast_one] at e₂
  obtain ⟨r₀, h₀⟩ := SV_total3_V (gI .D) 1 k (SV (gI .D) 1 k) (pBot (pConst 0))
  have eO : EvalGraph 5 OBotV (SV (gI .D) 1 k) OBotV 1 := by
    have := obot_D_of_any_V (n := 2) (by rw [show (2 : V) + 1 = 3 by norm_num]; exact h₀) e₂
    rwa [show (2 : V) + 1 + 1 + 1 = 5 by norm_num] at this
  -- the transposed side
  have b₁' : LenBox TAct k (instB (⌜qF (gI .C) dpDd.tr dpOB.tr⌝ : V) k) := by
    have := b₁.2; rwa [obQ, lMap_swap_qF, lMap_swap_gI_D] at this
  have b₂' : LenBox TAct k (instB (⌜qF (gI .C) dpDd.tr dpBD.tr⌝ : V) k) := by
    have := b₂.2; rwa [lMap_swap_qF, lMap_swap_gI_D] at this
  have e₁' := SV_then_qF (gI .C) 0 dpDd.tr dpOB.tr k b₁'
  rw [dpDd_tr_val, dpOB_tr_val, Nat.cast_zero] at e₁'
  have e₂' := SV_then_qF (gI .C) 0 dpDd.tr dpBD.tr k b₂'
  rw [dpDd_tr_val, dpBD_tr_val, Nat.cast_zero] at e₂'
  obtain ⟨r₁, h₁⟩ := SV_total3_V (gI .C) 0 k (SV (gI .C) 0 k) (pBot (pConst 1))
  have eOT : EvalGraph 5 OBotTV (SV (gI .C) 0 k) OBotTV 0 := by
    have := obotT_C_of_any_V (n := 2) (by rw [show (2 : V) + 1 = 3 by norm_num]; exact h₁) e₂'
    rwa [show (2 : V) + 1 + 1 + 1 = 5 by norm_num] at this
  refine ⟨⟨e₁, eO⟩, fun r hr ↦ ?_⟩
  simp only [obR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [← stdReadingV_eq_stdReading]
  rcases hr with rfl | rfl
  · rw [obQ, lMap_swap_qF, lMap_swap_gI_D, eval_qF_impl .D, eval_qF_impl .C]
    simp only [dpDd_val, dpOB_val, dpDd_tr_val, dpOB_tr_val, actCode_D_cast, actCode_C_cast]
    exact ⟨fun _ ↦ ⟨5, eO⟩, fun _ ↦ ⟨5, eOT⟩⟩
  · rw [lMap_swap_qF, lMap_swap_gI_D, eval_qF_impl .D, eval_qF_impl .C]
    simp only [dpDd_val, dpBD_val, dpDd_tr_val, dpBD_tr_val, actCode_D_cast, actCode_C_cast]
    exact ⟨fun _ ↦ bot_const_play_V _ _ _, fun _ ↦ bot_const_play_V _ _ _⟩

/-- **The two guards of the DIMDID × OBot family are found within the budget, for all large `k`** (bounded Löb). -/
theorem ob_found : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ∀ r ∈ obQ :: obR,
    LenBox TAct k (instB (⌜r⌝ : ℕ) k) ∧ LenBox TAct k (instB (⌜Semiformula.lMap swap r⌝ : ℕ) k) :=
  found_pL obQ obR (fun V _ _ k hb ↦ (ob_core V k hb).2)

/-- **DIMDID × OBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional: DIMDID's guard "I defect against
OBot ⇒ OBot defects against me" is found — its consequent is forced by DIMDID's found defection against
`.bot DefectBot` — and OBot, seeing that defection, defects (fuel 5). -/
theorem loeb_DIMDID_vs_OBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DIMDID k)) (progCode OBot) (progCode (DIMDID k)) (actCode .D) ∧
      EvalGraph 5 (progCode OBot) (progCode (DIMDID k)) (progCode OBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := ob_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hp := (ob_core ℕ k (h k hk)).1
  rw [OBotV_nat, ← progCode_DIMDID_SV] at hp
  exact hp


end dimdidOBot

/-! #### DIMDID × DIMCID `(D, D)` -/

section dimdidDimcid

/-- DIMDID's guard against DIMCID: "I defect against DIMCID ⇒ DIMCID defects against me". -/
noncomputable def diQ : Semisentence LAct 1 := qF (gI .D) dpDd dpDi
/-- DIMCID's guard against DIMDID: "I cooperate with DIMDID ⇒ DIMDID defects against me". -/
noncomputable def diR : List (Semisentence LAct 1) := [qF (template phiD) dpDi dpDd]

/-- **The semantic core of DIMDID × DIMCID, in every model**: each box makes its searcher defect, and each
defection is the consequent of the other's guard; on the transposed side CIMCIC and the transposed DIMCID
cooperate, with the same exchange. -/
theorem di_core (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V)
    (hb : ∀ r ∈ diQ :: diR, LenBox TAct k (instB (⌜r⌝ : V) k) ∧ LenBox TAct k (instB (⌜Semiformula.lMap swap r⌝ : V) k)) :
    (EvalGraph 2 (SV (gI .D) 1 k) (SV (template phiD) 1 k) (SV (gI .D) 1 k) 1 ∧
      EvalGraph 2 (SV (template phiD) 1 k) (SV (gI .D) 1 k) (SV (template phiD) 1 k) 1) ∧
    ∀ r ∈ diQ :: diR, Semiformula.Eval (s := stdReading V) ![k] Empty.elim r ∧
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim (Semiformula.lMap swap r) := by
  have b₁ := hb diQ (by simp)
  have b₂ := hb (qF (template phiD) dpDi dpDd) (by simp [diR])
  have e₁ := SV_then_qF (gI .D) 1 dpDd dpDi k b₁.1
  rw [dpDd_val, dpDi_val, Nat.cast_one] at e₁
  have e₂ := SV_then_qF (template phiD) 1 dpDi dpDd k b₂.1
  rw [dpDd_val, dpDi_val, Nat.cast_one] at e₂
  have b₁' : LenBox TAct k (instB (⌜qF (gI .C) dpDd.tr dpDi.tr⌝ : V) k) := by
    have := b₁.2; rwa [diQ, lMap_swap_qF, lMap_swap_gI_D] at this
  have b₂' : LenBox TAct k
      (instB (⌜qF (template (.impl (.plays .self .opp .D) (.plays .opp .self .C))) dpDi.tr dpDd.tr⌝ : V) k) := by
    have := b₂.2; rwa [lMap_swap_qF, lMap_swap_template_phiD] at this
  have e₁' := SV_then_qF (gI .C) 0 dpDd.tr dpDi.tr k b₁'
  rw [dpDd_tr_val, dpDi_tr_val, Nat.cast_zero] at e₁'
  have e₂' := SV_then_qF (template (.impl (.plays .self .opp .D) (.plays .opp .self .C))) 0 dpDi.tr dpDd.tr k b₂'
  rw [dpDd_tr_val, dpDi_tr_val, Nat.cast_zero] at e₂'
  refine ⟨⟨e₁, e₂⟩, fun r hr ↦ ?_⟩
  simp only [diR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [← stdReadingV_eq_stdReading]
  rcases hr with rfl | rfl
  · rw [diQ, lMap_swap_qF, lMap_swap_gI_D, eval_qF_impl .D, eval_qF_impl .C]
    simp only [dpDd_val, dpDi_val, dpDd_tr_val, dpDi_tr_val, actCode_D_cast, actCode_C_cast]
    exact ⟨fun _ ↦ ⟨2, e₂⟩, fun _ ↦ ⟨2, e₂'⟩⟩
  · rw [lMap_swap_qF, lMap_swap_template_phiD, template_phiD_eq, eval_qF_impl₂ .C .D, eval_qF_impl₂ .D .C]
    simp only [dpDd_val, dpDi_val, dpDd_tr_val, dpDi_tr_val, actCode_D_cast, actCode_C_cast]
    exact ⟨fun _ ↦ ⟨2, e₁⟩, fun _ ↦ ⟨2, e₁'⟩⟩

/-- **The two guards of the DIMDID × DIMCID family are found within the budget, for all large `k`.** -/
theorem di_found : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ∀ r ∈ diQ :: diR,
    LenBox TAct k (instB (⌜r⌝ : ℕ) k) ∧ LenBox TAct k (instB (⌜Semiformula.lMap swap r⌝ : ℕ) k) :=
  found_pL diQ diR (fun V _ _ k hb ↦ (di_core V k hb).2)

/-- **DIMDID × DIMCID is `(D, D)` in PA-`S'`**, for all large `k`, unconditional (fuel 2): the mutual family —
DIMDID's "I defect ⇒ you defect" and DIMCID's "I cooperate ⇒ you defect" — each guard's consequent is the
other searcher's found defection. -/
theorem loeb_DIMDID_vs_DIMCID :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DIMDID k)) (progCode (DIMCID k)) (progCode (DIMDID k)) (actCode .D) ∧
      EvalGraph 2 (progCode (DIMCID k)) (progCode (DIMDID k)) (progCode (DIMCID k)) (actCode .D) := by
  obtain ⟨k₀, h⟩ := di_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hp := (di_core ℕ k (h k hk)).1
  rw [← progCode_DIMDID_SV, ← progCode_DIMCID_SV] at hp
  exact hp


end dimdidDimcid

/-! ### 5. The floors: three two-hinge dichotomies, DIMDID's own guard the outer hinge -/

section floors

/-- **DIMDID × Dupoc**: two hinges, NESTED — `A` = DIMDID's guard "I defect against Dupoc ⇒ Dupoc defects against
me" (outer split), `B` = Dupoc's guard "DIMDID cooperates with me". `A ⇒ (D, D)` (DIMDID defects, so `B` is false by
soundness); `¬A ⇒` DIMDID C, then `¬B ⇒ Dupoc D` (the engine's `+k` world, `(C, D)`: DIMDID exploited) and
`B ⇒ Dupoc C` (`(C, C)`). Both hinges are provability-within-`k` of sentences true only through an else-play:
`A` through Dupoc's, `B` through DIMDID's. -/
theorem dich_DIMDID_vs_DupocBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenBox TAct k (guardCodeB (templateCode phiDd) (progCode (DIMDID k)) (progCode (DupocBot k)) k) →
        EvalGraph 2 (progCode (DIMDID k)) (progCode (DupocBot k)) (progCode (DIMDID k)) (actCode .D) ∧
        EvalGraph 2 (progCode (DupocBot k)) (progCode (DIMDID k)) (progCode (DupocBot k)) (actCode .D)) ∧
      (¬ LenBox TAct k (guardCodeB (templateCode phiDd) (progCode (DIMDID k)) (progCode (DupocBot k)) k) →
        EvalGraph 2 (progCode (DIMDID k)) (progCode (DupocBot k)) (progCode (DIMDID k)) (actCode .C) ∧
        (¬ LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (DIMDID k)) k) →
          EvalGraph 2 (progCode (DupocBot k)) (progCode (DIMDID k)) (progCode (DupocBot k)) (actCode .D)) ∧
        (LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (DIMDID k)) k) →
          EvalGraph 2 (progCode (DupocBot k)) (progCode (DIMDID k)) (progCode (DupocBot k)) (actCode .C))) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiDd, hingeB phiDu]
  constructor
  · intro hA
    have hDD := dimdid_D_of_found k hA
    exact ⟨hDD, dupoc_D_of_probe k (properPlayer_DIMDID k) hDD⟩
  · intro hn
    refine ⟨dimdid_C_of_not_found k hn, fun hB ↦ ?_, fun hB ↦ ?_⟩
    · rw [progCode_DupocBot_search] at hB ⊢
      exact search_else phiDu hB (const_play 0 _ _ _)
    · rw [progCode_DupocBot_search] at hB ⊢
      exact search_then phiDu hB (const_play 0 _ _ _)

/-- **DIMDID × CIMCIC** (the self-dual pair: CIMCIC is DIMDID's transposition): two hinges, NESTED — `A` = DIMDID's
guard "I defect against CIMCIC ⇒ CIMCIC defects against me" (outer split), `B` = CIMCIC's guard "I cooperate with
DIMDID ⇒ DIMDID cooperates with me". `A ⇒ (D, D)` (DIMDID defects, so `B` is self-refuting); `¬A ⇒` DIMDID C, then
`¬B ⇒ CIMCIC D` (the engine's world, `(C, D)`) and `B ⇒ CIMCIC C` (`(C, C)`). -/
theorem dich_DIMDID_vs_CIMCIC :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenBox TAct k (guardCodeB (templateCode phiDd) (progCode (DIMDID k)) (progCode (CIMCIC k)) k) →
        EvalGraph 2 (progCode (DIMDID k)) (progCode (CIMCIC k)) (progCode (DIMDID k)) (actCode .D) ∧
        EvalGraph 2 (progCode (CIMCIC k)) (progCode (DIMDID k)) (progCode (CIMCIC k)) (actCode .D)) ∧
      (¬ LenBox TAct k (guardCodeB (templateCode phiDd) (progCode (DIMDID k)) (progCode (CIMCIC k)) k) →
        EvalGraph 2 (progCode (DIMDID k)) (progCode (CIMCIC k)) (progCode (DIMDID k)) (actCode .C) ∧
        (¬ LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (DIMDID k)) k) →
          EvalGraph 2 (progCode (CIMCIC k)) (progCode (DIMDID k)) (progCode (CIMCIC k)) (actCode .D)) ∧
        (LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (DIMDID k)) k) →
          EvalGraph 2 (progCode (CIMCIC k)) (progCode (DIMDID k)) (progCode (CIMCIC k)) (actCode .C))) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiDd, hingeB phiC]
  constructor
  · intro hA
    have hDD := dimdid_D_of_found k hA
    have hn := cimcic_selfref_not_found k (properPlayer_DIMDID k) hDD
    refine ⟨hDD, ?_⟩
    rw [progCode_CIMCIC_search] at hn ⊢
    exact search_else phiC hn (const_play 0 _ _ _)
  · intro hn
    refine ⟨dimdid_C_of_not_found k hn, fun hB ↦ ?_, fun hB ↦ ?_⟩
    · rw [progCode_CIMCIC_search] at hB ⊢
      exact search_else phiC hB (const_play 0 _ _ _)
    · rw [progCode_CIMCIC_search] at hB ⊢
      exact search_then phiC hB (const_play 0 _ _ _)

/-- **DIMDID × Prudent**: two hinges, NESTED, the prudence guard DISCHARGED (`prudence_found_vs_DIMDID`) — `A` =
DIMDID's guard "I defect against Prudent ⇒ Prudent defects against me" (outer split), `B` = Prudent's outer guard
"DIMDID cooperates with me". `A ⇒ (D, D)` (DIMDID defects, so `B` is false by soundness); `¬A ⇒` DIMDID C, then
`¬B ⇒ Prudent D` (the engine's world, `(C, D)`) and `B ⇒ Prudent C` (`(C, C)`: its prudence guard "DIMDID defects
against `.bot DefectBot`" is found for all large `k`). Fuel 3 (Prudent's two searches). -/
theorem dich_DIMDID_vs_PrudentBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenBox TAct k (guardCodeB (templateCode phiDd) (progCode (DIMDID k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (DIMDID k)) (progCode (PrudentBot k)) (progCode (DIMDID k)) (actCode .D) ∧
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (DIMDID k)) (progCode (PrudentBot k)) (actCode .D)) ∧
      (¬ LenBox TAct k (guardCodeB (templateCode phiDd) (progCode (DIMDID k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (DIMDID k)) (progCode (PrudentBot k)) (progCode (DIMDID k)) (actCode .C) ∧
        (¬ LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (DIMDID k)) k) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (DIMDID k)) (progCode (PrudentBot k)) (actCode .D)) ∧
        (LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (DIMDID k)) k) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (DIMDID k)) (progCode (PrudentBot k)) (actCode .C))) := by
  obtain ⟨k₀, hP⟩ := prudence_found_vs_DIMDID
  refine ⟨k₀, fun k hk ↦ ?_⟩
  simp only [hingeB phiDd, hingeB phiPo]
  constructor
  · intro hA
    have hDD := dimdid_D_of_found k hA
    exact ⟨EvalGraph.mono_le (by omega) hDD,
      EvalGraph.mono_le (by omega) (prudent_D_of_probe k (properPlayer_DIMDID k) hDD)⟩
  · intro hn
    refine ⟨EvalGraph.mono_le (by omega) (dimdid_C_of_not_found k hn), fun hB ↦ ?_, fun hB ↦ ?_⟩
    · rw [progCode_PrudentBot_search] at hB ⊢
      exact EvalGraph.mono_le (by omega) (search_else phiPo hB (const_play 1 _ _ _))
    · have hi := hP k hk
      rw [progCode_PrudentBot_search] at hB hi ⊢
      exact search_then phiPo hB (search_then phiPi hi (const_play 0 _ _ _))

end floors

end ArithS
