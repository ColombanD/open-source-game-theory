import ArithS.Cells.CupodTrollEngine
import ArithS.Cells.FloorDichotomy
import PrisonersDilemma.Bots.DupocTrollBot

/-!
# ArithS.Cells.DupocTrollBot — the cells of `DupocTrollBot` ("defect iff the opponent IS `DupocBot k`")

`DupocTrollBot k := .search k (.eq .opp (DupocBot k)) D C` (`engine/.../Bots/DupocTrollBot.lean`, 2026-10-13):
the troll aimed at the Löbian cooperator, the mirror image of `CupodTrollBot` (which targets CupodBot). It has
NO engine cell — every cell below is an `S'`-only result (`docs/notes/ROUTE_B_CENSUS.md`, "S'-only cells").
Twelve cells, DupocTroll on the left: the ten `body` bots, CIMCIC, and itself.

1. **Its code and its simple-member form.** Like CupodTroll, its guard freezes a budget-carrying snapshot, so the
   stored template is ABSTRACTED (route (c), generic): `progCode (DupocTrollBot k) = pSearch k (templateCodeAt
   (phiTT k) k) (pConst 1) (pConst 0)` (`progCode_DupocTrollBot`; `phiTT` is the `.eq .opp (DupocBot k)` guard of
   `Cells/CupodTrollEngine.lean`, where it appears as the TRANSPOSE of CupodTroll's guard). It is the simple member
   `sTd := ⟨gEq (gP .C) (actCode .C), actCode .D, _⟩` — the `.eq` template of "the opponent IS `SV (gP .C) 0 ·`",
   then-action D (`progCode_DupocTrollBot_sT`; `sTc .C` of `CupodTrollEngine` has the same guard with then-action C).
2. **The `.eq` guard against the zoo**: `dtb_C_of_ne` — against any proper opponent whose code is not
   `DupocBot k`'s the guard is FALSE, never found (soundness), else-branch C. The code disjointness lemmas
   `progCode_<X>_ne_DupocBot` (§3): by the branch constants where they differ, by the SEMANTIC template separation
   `templateCode_phiC_ne_phiDu` for CIMCIC (same branches as Dupoc), and `progCode_DupocTrollBot_ne_CupodBot` (the
   stored `.eq` template against Cupod's, separated at the frame `(CooperateBot, DefectBot)` — the primed form
   `templateCodeAt_ne_templateCode_of_models'`, the stored template FALSE and the plain one TRUE).
3. **The cells.** SND (9): × CooperateBot, DefectBot, DBot, EBot, OBot, TitForTatBot, CupodBot, CupodTrollBot and
   itself — the troll cooperates, the partner plays as it does against any cooperator (Cupod's guard "the opponent
   defects against me" is false too). POS (1): × DupocBot `(D, D)` — the troll FINDS the reflexive equation
   "`DupocBot k` IS `DupocBot k`" (a `TAct`-theorem in both readings, `tact_qTD`; `found_of_all_V`) and defects;
   Dupoc's guard "the troll cooperates with me" is then false, so Dupoc defects (`pos_DupocTrollBot_vs_DupocBot`).
   LOEB (1): × DIMCID `(C, D)` — `dimcid_vs_described sTd.describes`, DIMCID's self-fulfilling guard against the
   described troll (`loeb_DupocTrollBot_vs_DIMCID`). GENUINE FLOOR (1): × CIMCIC — CIMCIC's guard "I cooperate with
   the troll ⇒ it cooperates with me" is TRUE (its consequent is the troll's else-play on a false `.eq`), and its
   provability within `k` is the bounded-consistency hinge; the settled halves `floor_DupocTrollBot_vs_CIMCIC_right`
   / `_true` and the hypothesis-free dichotomy `dich_DupocTrollBot_vs_CIMCIC` (engine side `(C, D)`, hinge side
   `(C, C)`), registered in `Outcome/Floors.lean` and checked by `#check_floorA_theorems` on THIS file.

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
open ArithS.Tau

/-! ### 1. The code and the simple-member form -/

section code

/-- DupocTroll's stored template is ABSTRACTED (its guard freezes the budget-carrying `DupocBot k`): the code
stores `templateCodeAt (phiTT k) k`, a constant (route (c), generic). -/
lemma progCode_DupocTrollBot (k : ℕ) :
    progCode (DupocTrollBot k) = pSearch k (templateCodeAt (phiTT k) k) (pConst 1) (pConst 0) := by
  simp [DupocTrollBot, phiTT, actCode]

lemma properPlayer_DupocTrollBot (k : ℕ) : ProperPlayer (DupocTrollBot k) :=
  ⟨by simp [DupocTrollBot], by simp [DupocTrollBot]⟩

/-- **DupocTroll as a simple member**: the searcher on the stored `.eq` template "the opponent IS
`SV (gP .C) 0 ·`" (= `DupocBot ·`), then-action D. -/
noncomputable def sTd : SM := ⟨gEq (gP .C) (actCode .C), actCode .D, actCode_zero_or_one .D⟩

/-- **The engine's `DupocTrollBot k` is the simple member `sTd` at the budget `k`.** -/
theorem progCode_DupocTrollBot_sT (k : ℕ) : progCode (DupocTrollBot k) = sTd.code (V := ℕ) k := by
  rw [progCode_DupocTrollBot]
  unfold SM.code templateCodeAt
  rw [templateAt_phiTT]
  simp only [natCast_nat]
  rfl

/-- The engine DupocTroll, as a described player. -/
noncomputable def dpTd : DP := DP.ofSM sTd
/-- The engine Dupoc, as a described player. -/
noncomputable def dpDu : DP := DP.ofSV (gP .C) (actCode .C) (actCode_zero_or_one .C)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma dpTd_val (k : V) : dpTd.val k = sTd.code k := DP.ofSM_val _ k
lemma dpDu_val (k : V) : dpDu.val k = SV (gP .C) (actCode .C) k := DP.ofSV_val _ _ _ k
lemma dpDu_tr_val (k : V) : dpDu.tr.val k = SV (gP .D) (actCode .D) k := by
  rw [dpDu, DP.ofSV_tr_val, lMap_swap_gP_C]; rfl

end code

/-! ### 2. The `.eq` guard against the zoo: false, never found, else-branch C -/

section eqGuard

/-- DupocTroll cooperates with any proper opponent whose code is not `DupocBot k`'s. -/
theorem dtb_C_of_ne (k : ℕ) {opp : PD.Prog} (hopp : ProperPlayer opp)
    (hne : progCode opp ≠ progCode (DupocBot k)) :
    EvalGraph 2 (progCode (DupocTrollBot k)) (progCode opp) (progCode (DupocTrollBot k)) 0 := by
  have hn := not_found_eq_opp (properPlayer_DupocTrollBot k) hopp (Q := DupocBot k) rfl hne k
  rw [progCode_DupocTrollBot] at hn ⊢
  exact search_else_at (phiTT k) hn (const_play _ _ _ _)

/-- DupocTroll cooperates with `.bot CooperateBot`. -/
theorem snd_DupocTrollBot_vs_botCB (k : ℕ) :
    EvalGraph 2 (progCode (DupocTrollBot k)) (pBot (pConst 0)) (progCode (DupocTrollBot k)) 0 := by
  have := dtb_C_of_ne k (opp := .bot CooperateBot) properPlayer_botCB
    (by rw [progCode_botCB, progCode_DupocBot_search]; exact pBot_ne_pSearch _ _ _ _ _)
  rwa [progCode_botCB] at this

/-- DupocTroll cooperates with `.bot DefectBot`. -/
theorem snd_DupocTrollBot_vs_botDB (k : ℕ) :
    EvalGraph 2 (progCode (DupocTrollBot k)) (pBot (pConst 1)) (progCode (DupocTrollBot k)) 0 := by
  have := dtb_C_of_ne k (opp := .bot DefectBot) properPlayer_botDB
    (by rw [progCode_botDB, progCode_DupocBot_search]; exact pBot_ne_pSearch _ _ _ _ _)
  rwa [progCode_botDB] at this

end eqGuard

/-! ### 3. Code disjointness against `DupocBot k` -/

section disjoint

lemma progCode_CB_ne_DupocBot (k : ℕ) : progCode CooperateBot ≠ progCode (DupocBot k) := by
  rw [progCode_CB, progCode_DupocBot_search]; exact pConst_ne_pSearch _ _ _ _ _
lemma progCode_DB_ne_DupocBot (k : ℕ) : progCode DefectBot ≠ progCode (DupocBot k) := by
  rw [progCode_DB, progCode_DupocBot_search]; exact pConst_ne_pSearch _ _ _ _ _
lemma progCode_DBot_ne_DupocBot (k : ℕ) : progCode DBot ≠ progCode (DupocBot k) := by
  simp only [DBot, DefectBot, progCode_ite, progCode_sim, progCode_opp, progCode_bot, progCode_const,
    progCode_DupocBot_search]
  exact pIte_ne_pSearch _ _ _ _ _ _ _ _
lemma progCode_EBot_ne_DupocBot (k : ℕ) : progCode EBot ≠ progCode (DupocBot k) := by
  simp only [EBot, DefectBot, CooperateBot, MirrorBot, progCode_ite, progCode_sim, progCode_opp, progCode_self,
    progCode_bot, progCode_const, progCode_DupocBot_search]
  exact pIte_ne_pSearch _ _ _ _ _ _ _ _
lemma progCode_OBot_ne_DupocBot (k : ℕ) : progCode OBot ≠ progCode (DupocBot k) := by
  simp only [OBot, DefectBot, CooperateBot, progCode_ite, progCode_sim, progCode_opp, progCode_bot, progCode_const,
    progCode_DupocBot_search]
  exact pIte_ne_pSearch _ _ _ _ _ _ _ _
lemma progCode_TFT_ne_DupocBot (k : ℕ) : progCode TitForTatBot ≠ progCode (DupocBot k) := by
  simp only [TitForTatBot, CooperateBot, progCode_ite, progCode_sim, progCode_opp, progCode_bot, progCode_const,
    progCode_DupocBot_search]
  exact pIte_ne_pSearch _ _ _ _ _ _ _ _

/-- The branch constants differ (Cupod: then D, else C; Dupoc: then C, else D). -/
lemma progCode_CupodBot_ne_DupocBot (k : ℕ) : progCode (CupodBot k) ≠ progCode (DupocBot k) := by
  rw [progCode_CupodBot, progCode_DupocBot_search]
  intro e
  exact pConst_zero_ne_one (pSearch_inj e).2.2.1.symm

lemma progCode_CupodTrollBot_ne_DupocBot (k : ℕ) : progCode (CupodTrollBot k) ≠ progCode (DupocBot k) := by
  rw [progCode_CupodTrollBot, progCode_DupocBot_search]
  intro e
  exact pConst_zero_ne_one (pSearch_inj e).2.2.1.symm

lemma progCode_DupocTrollBot_ne_DupocBot (k : ℕ) : progCode (DupocTrollBot k) ≠ progCode (DupocBot k) := by
  rw [progCode_DupocTrollBot, progCode_DupocBot_search]
  intro e
  exact pConst_zero_ne_one (pSearch_inj e).2.2.1.symm

lemma progCode_DIMCID_ne_DupocBot (k : ℕ) : progCode (DIMCID k) ≠ progCode (DupocBot k) := by
  rw [progCode_DIMCID_search, progCode_DupocBot_search]
  intro e
  exact pConst_zero_ne_one (pSearch_inj e).2.2.1.symm

/-- CIMCIC's and Dupoc's templates differ: at the frame `(DefectBot, DefectBot)`, "I play C against DefectBot ⇒
DefectBot plays C against me" is true (a false antecedent) while "DefectBot plays C against me" is false. -/
lemma templateCode_phiC_ne_phiDu : templateCode phiC ≠ templateCode phiDu := by
  refine templateCode_ne_of_models DefectBot DefectBot ?_ ?_
  · rw [← sentenceAt_subst DefectBot DefectBot sfp_DefectBot.1 sfp_DefectBot.1 _ rfl]
    show ℕ↓[LAct] ⊧ sentenceAt DefectBot DefectBot
      (.impl (.plays DefectBot DefectBot .C) (.plays DefectBot DefectBot .C))
    rw [models_sentenceAt_impl, models_sentenceAt_plays _ _ _ _ _ sfp_DefectBot.1 sfp_DefectBot.1]
    rintro ⟨N, hN⟩
    rw [progCode_DB] at hN
    exact absurd (EvalGraph.unique' hN (const_play 0 _ _ 1)) (by decide)
  · rw [← sentenceAt_subst DefectBot DefectBot sfp_DefectBot.1 sfp_DefectBot.1 _ rfl]
    show ¬ ℕ↓[LAct] ⊧ sentenceAt DefectBot DefectBot (.plays DefectBot DefectBot .C)
    rw [models_sentenceAt_plays _ _ _ _ _ sfp_DefectBot.1 sfp_DefectBot.1]
    rintro ⟨N, hN⟩
    rw [progCode_DB] at hN
    exact absurd (EvalGraph.unique' hN (const_play 0 _ _ 1)) (by decide)

/-- CIMCIC and Dupoc have the same branch constants; their templates separate them. -/
lemma progCode_CIMCIC_ne_DupocBot (k : ℕ) : progCode (CIMCIC k) ≠ progCode (DupocBot k) := by
  rw [progCode_CIMCIC_search, progCode_DupocBot_search]
  intro e
  exact templateCode_phiC_ne_phiDu (pSearch_inj e).2.1

/-- `templateCodeAt_ne_templateCode_of_models` with the truth values the other way round: the STORED template
FALSE and the plain one TRUE at one frame. -/
lemma templateCodeAt_ne_templateCode_of_models' {φ ψ : PD.Formula} (k : ℕ) (me opp : PD.Prog)
    (h1 : ¬ ℕ↓[LAct] ⊧ sentenceAt me opp φ) (h2 : ℕ↓[LAct] ⊧ sentenceAt me opp ψ)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) (hψ : noSelfIdxF ψ = true := by noSelfIdx_tac) :
    templateCodeAt φ k ≠ templateCode ψ := by
  intro e
  apply h1
  have hg : guardCode (templateCode φ) (progCode me) (progCode opp) =
      guardCode (templateCode ψ) (progCode me) (progCode opp) := by
    rw [← guardCodeB_templateCodeAt φ (progCode me) (progCode opp) k hφ, e,
      guardCodeB_of_template (isSemiformula_templateCode ψ hψ)]
  have hq : (⌜sentenceAt me opp φ⌝ : ℕ) = ⌜sentenceAt me opp ψ⌝ := by
    rw [quote_sentenceAt me opp φ hφ, quote_sentenceAt me opp ψ hψ, hg]
  rw [(Sentence.quote_inj_iff (V := ℕ)).mp hq]
  exact h2

/-- At the frame `(CooperateBot, DefectBot)`: "the opponent IS `DupocBot k`" is false … -/
lemma not_models_phiTT_at_CB_DB (k : ℕ) : ¬ ℕ↓[LAct] ⊧ sentenceAt CooperateBot DefectBot (phiTT k) := by
  rw [← sentenceAt_subst CooperateBot DefectBot sfp_CooperateBot.1 sfp_DefectBot.1 _ rfl]
  show ¬ ℕ↓[LAct] ⊧ sentenceAt CooperateBot DefectBot (.eq DefectBot (DupocBot k))
  rw [models_sentenceAt_eq _ _ _ _ sfp_DefectBot.1]
  exact progCode_DB_ne_DupocBot k

/-- … while "the opponent defects against me" is true. -/
lemma models_phiCu_at_CB_DB : ℕ↓[LAct] ⊧ sentenceAt CooperateBot DefectBot phiCu := by
  rw [← sentenceAt_subst CooperateBot DefectBot sfp_CooperateBot.1 sfp_DefectBot.1 _ rfl]
  show ℕ↓[LAct] ⊧ sentenceAt CooperateBot DefectBot (.plays DefectBot CooperateBot .D)
  rw [models_sentenceAt_plays _ _ _ _ _ sfp_DefectBot.1 sfp_CooperateBot.1, progCode_DB]
  exact ⟨1, const_play 0 _ _ 1⟩

/-- DupocTroll's STORED `.eq` template differs from Cupod's. -/
lemma templateCodeAt_phiTT_ne_phiCu (k : ℕ) : templateCodeAt (phiTT k) k ≠ templateCode phiCu :=
  templateCodeAt_ne_templateCode_of_models' k CooperateBot DefectBot (not_models_phiTT_at_CB_DB k)
    models_phiCu_at_CB_DB

lemma progCode_DupocTrollBot_ne_CupodBot (k : ℕ) : progCode (DupocTrollBot k) ≠ progCode (CupodBot k) := by
  rw [progCode_DupocTrollBot, progCode_CupodBot]
  intro e
  exact templateCodeAt_phiTT_ne_phiCu k (pSearch_inj e).2.1

end disjoint

/-! ### 4. The SND cells: the `.eq` guard is false, the troll cooperates -/

section sndCells

/-- `DupocTrollBot × CooperateBot = (C, C)`. -/
theorem snd_DupocTrollBot_vs_CooperateBot (k : ℕ) :
    EvalGraph 2 (progCode (DupocTrollBot k)) (progCode CooperateBot) (progCode (DupocTrollBot k)) (actCode .C) ∧
    EvalGraph 2 (progCode CooperateBot) (progCode (DupocTrollBot k)) (progCode CooperateBot) (actCode .C) :=
  ⟨dtb_C_of_ne k sfp_CooperateBot.1 (progCode_CB_ne_DupocBot k), by rw [progCode_CB]; exact const_play 1 _ _ _⟩

/-- `DupocTrollBot × DefectBot = (C, D)`. -/
theorem snd_DupocTrollBot_vs_DefectBot (k : ℕ) :
    EvalGraph 2 (progCode (DupocTrollBot k)) (progCode DefectBot) (progCode (DupocTrollBot k)) (actCode .C) ∧
    EvalGraph 2 (progCode DefectBot) (progCode (DupocTrollBot k)) (progCode DefectBot) (actCode .D) :=
  ⟨dtb_C_of_ne k sfp_DefectBot.1 (progCode_DB_ne_DupocBot k), by rw [progCode_DB]; exact const_play 1 _ _ _⟩

/-- `DupocTrollBot × DBot = (C, D)`: DBot sees the troll cooperate with `.bot DefectBot` and defects. -/
theorem snd_DupocTrollBot_vs_DBot (k : ℕ) :
    EvalGraph 4 (progCode (DupocTrollBot k)) (progCode DBot) (progCode (DupocTrollBot k)) (actCode .C) ∧
    EvalGraph 4 (progCode DBot) (progCode (DupocTrollBot k)) (progCode DBot) (actCode .D) :=
  ⟨EvalGraph.mono_le (by omega) (dtb_C_of_ne k sfp_DBot.1 (progCode_DBot_ne_DupocBot k)),
   dbot_D_of_probe_C (snd_DupocTrollBot_vs_botDB k)⟩

/-- `DupocTrollBot × EBot = (C, D)`. -/
theorem snd_DupocTrollBot_vs_EBot (k : ℕ) :
    EvalGraph 4 (progCode (DupocTrollBot k)) (progCode EBot) (progCode (DupocTrollBot k)) (actCode .C) ∧
    EvalGraph 4 (progCode EBot) (progCode (DupocTrollBot k)) (progCode EBot) (actCode .D) :=
  ⟨EvalGraph.mono_le (by omega) (dtb_C_of_ne k sfp_EBot.1 (progCode_EBot_ne_DupocBot k)),
   ebot_D_of_probe1_C (snd_DupocTrollBot_vs_botDB k)⟩

/-- `DupocTrollBot × OBot = (C, C)`. -/
theorem snd_DupocTrollBot_vs_OBot (k : ℕ) :
    EvalGraph 5 (progCode (DupocTrollBot k)) (progCode OBot) (progCode (DupocTrollBot k)) (actCode .C) ∧
    EvalGraph 5 (progCode OBot) (progCode (DupocTrollBot k)) (progCode OBot) (actCode .C) :=
  ⟨EvalGraph.mono_le (by omega) (dtb_C_of_ne k sfp_OBot.1 (progCode_OBot_ne_DupocBot k)),
   obot_C_of_probes (snd_DupocTrollBot_vs_botCB k) (snd_DupocTrollBot_vs_botDB k)⟩

/-- `DupocTrollBot × TitForTatBot = (C, C)`. -/
theorem snd_DupocTrollBot_vs_TitForTatBot (k : ℕ) :
    EvalGraph 4 (progCode (DupocTrollBot k)) (progCode TitForTatBot) (progCode (DupocTrollBot k)) (actCode .C) ∧
    EvalGraph 4 (progCode TitForTatBot) (progCode (DupocTrollBot k)) (progCode TitForTatBot) (actCode .C) :=
  ⟨EvalGraph.mono_le (by omega) (dtb_C_of_ne k sfp_TitForTatBot.1 (progCode_TFT_ne_DupocBot k)),
   tft_C_of_probe_C (snd_DupocTrollBot_vs_botCB k)⟩

/-- `DupocTrollBot × CupodBot = (C, C)`: the troll's `.eq` guard is false (Cupod is not Dupoc), and Cupod's guard
"the opponent defects against me" is false too — both else-branches, both C. -/
theorem snd_DupocTrollBot_vs_CupodBot (k : ℕ) :
    EvalGraph 2 (progCode (DupocTrollBot k)) (progCode (CupodBot k)) (progCode (DupocTrollBot k)) (actCode .C) ∧
    EvalGraph 2 (progCode (CupodBot k)) (progCode (DupocTrollBot k)) (progCode (CupodBot k)) (actCode .C) := by
  have hT := dtb_C_of_ne k (properPlayer_CupodBot k) (progCode_CupodBot_ne_DupocBot k)
  exact ⟨hT, cupod_C_of_probe k (properPlayer_DupocTrollBot k) hT⟩

/-- `DupocTrollBot × CupodTrollBot = (C, C)`: two false `.eq` guards. -/
theorem snd_DupocTrollBot_vs_CupodTrollBot (k : ℕ) :
    EvalGraph 2 (progCode (DupocTrollBot k)) (progCode (CupodTrollBot k)) (progCode (DupocTrollBot k)) (actCode .C) ∧
    EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (DupocTrollBot k)) (progCode (CupodTrollBot k)) (actCode .C) :=
  ⟨dtb_C_of_ne k (properPlayer_CupodTrollBot k) (progCode_CupodTrollBot_ne_DupocBot k),
   ctb_C_of_ne k (properPlayer_DupocTrollBot k) (progCode_DupocTrollBot_ne_CupodBot k)⟩

/-- `DupocTrollBot × DupocTrollBot = (C, C)`. -/
theorem snd_DupocTrollBot_vs_DupocTrollBot (k : ℕ) :
    EvalGraph 3 (progCode (DupocTrollBot k)) (progCode (DupocTrollBot k)) (progCode (DupocTrollBot k)) (actCode .C) ∧
    EvalGraph 3 (progCode (DupocTrollBot k)) (progCode (DupocTrollBot k)) (progCode (DupocTrollBot k)) (actCode .C) :=
  ⟨EvalGraph.mono_le (by omega) (dtb_C_of_ne k (properPlayer_DupocTrollBot k) (progCode_DupocTrollBot_ne_DupocBot k)),
   EvalGraph.mono_le (by omega) (dtb_C_of_ne k (properPlayer_DupocTrollBot k) (progCode_DupocTrollBot_ne_DupocBot k))⟩

end sndCells

/-! ### 5. The POS cell: DupocTrollBot × DupocBot `(D, D)` -/

section trollDupoc

/-- **DupocTroll's guard against Dupoc**: "the opponent IS `DupocBot k`", in the frame `(DupocTroll k, Dupoc k)`. -/
noncomputable def qTD : Semisentence LAct 1 := qF13 (gEq (gP .C) (actCode .C)) dpTd dpDu

lemma lMap_swap_qTD : Semiformula.lMap swap qTD = qF13 (gEq (gP .D) (actCode .D)) dpTd.tr dpDu.tr := by
  unfold qTD
  rw [lMap_swap_qF13, lMap_swap_gEq _ _ (actCode_zero_or_one .C), lMap_swap_gP_C]
  rfl

/-- `TAct ⊢ ∀¹ qTD`: the reflexive equation is true in both readings (the engine's `eqRefl`). -/
theorem tact_qTD : TAct ⊢ ∀¹ qTD := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    exact (eval_qF13_eq _ _ (actCode_zero_or_one .C) dpTd dpDu x).mpr (dpDu_val x)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [eval_swappedReading, ← stdReadingV_eq_stdReading, lMap_swap_qTD]
    exact (eval_qF13_eq _ _ (actCode_zero_or_one .D) dpTd.tr dpDu.tr x).mpr (dpDu_tr_val x)

/-- **DupocTroll finds "the opponent IS `DupocBot k`" against `DupocBot k` in every model, above a threshold**
(found ⇒ D, fuel 2). -/
theorem trollD_vs_dupoc_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (dpTd.val k) (dpDu.val k) (dpTd.val k) ((actCode .D : ℕ) : V) := by
  obtain ⟨kHat, h⟩ := found_of_all_V tact_qTD
  refine ⟨kHat, fun V _ _ k hk ↦ ?_⟩
  have hb := h V k hk
  unfold qTD at hb
  rw [← guardCodeB_qF13 _ (isSemiformula7_gEq_C V)] at hb
  have e := SM.then_V sTd k (dpTd.val k) (dpDu.val k) hb
  rw [← dpTd_val] at e
  exact e

/-- **At ℕ, on the engine's codes**: `DupocTrollBot k` defects against `DupocBot k` for all large `k`. -/
theorem khat_DupocTrollBot_vs_DupocBot_engine :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DupocTrollBot k)) (progCode (DupocBot k)) (progCode (DupocTrollBot k)) (actCode .D) := by
  obtain ⟨kHat, h⟩ := trollD_vs_dupoc_V
  refine ⟨kHat, fun k hk ↦ ?_⟩
  have e := h ℕ k (le_def.mpr (Or.inr (by rw [natCast_nat]; omega)))
  rw [dpTd_val, dpDu_val, ← progCode_DupocTrollBot_sT] at e
  have eDu : progCode (DupocBot k) = SV (V := ℕ) (gP .C) (actCode .C) k := progCode_DupocBot_SV k
  rw [← eDu] at e
  exact e

/-- **DupocTrollBot × DupocBot is `(D, D)` in PA-`S'`**, for all large `k`: the troll FINDS the reflexive
equation and defects; Dupoc's guard "the troll cooperates with me" is then false, never found (soundness), so
Dupoc defects too. No Löb. -/
theorem pos_DupocTrollBot_vs_DupocBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DupocTrollBot k)) (progCode (DupocBot k)) (progCode (DupocTrollBot k)) (actCode .D) ∧
      EvalGraph 2 (progCode (DupocBot k)) (progCode (DupocTrollBot k)) (progCode (DupocBot k)) (actCode .D) := by
  obtain ⟨k₀, h⟩ := khat_DupocTrollBot_vs_DupocBot_engine
  exact ⟨k₀, fun k hk ↦ ⟨h k hk, dupoc_D_of_probe k (properPlayer_DupocTrollBot k) (h k hk)⟩⟩

end trollDupoc

/-! ### 6. The LOEB cell: DupocTrollBot × DIMCID `(C, D)` -/

section dimcidTroll

/-- **DIMCID defects against the described `DupocTrollBot k` and FINDS its guard, for all large `k`** (the
self-fulfilling refutation, `dimcid_vs_described` on the simple member's own tower). -/
theorem loeb_DIMCID_vs_DupocTrollBot_core :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DIMCID k)) (progCode (DupocTrollBot k)) (progCode (DIMCID k)) 1 ∧
      LenBox TAct k (guardCode (templateCode phiD) (progCode (DIMCID k)) (progCode (DupocTrollBot k))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described sTd.describes
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rw [templateCode_eq_quote_template phiD rfl]
  rwa [SM.descVal_TU, ← progCode_DupocTrollBot_sT, ← progCode_DIMCID] at this

/-- **DupocTrollBot × DIMCID is `(C, D)` in PA-`S'`**, for all large `k`: the troll's `.eq` guard "DIMCID is
`DupocBot k`" is false, never found, so it cooperates (every `k`); DIMCID's guard against the described troll is
self-fulfilling and found, so DIMCID defects (`dimcid_vs_closed` for a budget-indexed family). -/
theorem loeb_DupocTrollBot_vs_DIMCID :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DupocTrollBot k)) (progCode (DIMCID k)) (progCode (DupocTrollBot k)) (actCode .C) ∧
      EvalGraph 2 (progCode (DIMCID k)) (progCode (DupocTrollBot k)) (progCode (DIMCID k)) (actCode .D) := by
  obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_DupocTrollBot_core
  exact ⟨k₀, fun k hk ↦ ⟨dtb_C_of_ne k (properPlayer_DIMCID k) (progCode_DIMCID_ne_DupocBot k), (h k hk).1⟩⟩

end dimcidTroll

/-! ### 7. The genuine floor: DupocTrollBot × CIMCIC -/

section floor

/-- **DupocTroll cooperates with `CIMCIC k` at every `k`** (the settled half): its `.eq` guard is false. -/
theorem floor_DupocTrollBot_vs_CIMCIC_right (k : ℕ) :
    EvalGraph 2 (progCode (DupocTrollBot k)) (progCode (CIMCIC k)) (progCode (DupocTrollBot k)) (actCode .C) :=
  dtb_C_of_ne k (properPlayer_CIMCIC k) (progCode_CIMCIC_ne_DupocBot k)


/-- **DupocTroll × CIMCIC** (engine-side value `(C, D)`, the `+k` floor stipulation; the troll has no engine cell).
Hinge: CIMCIC's guard "I cooperate with the troll ⇒ it cooperates with me" (TRUE: its consequent is the troll's
else-play). Under `¬A_k` CIMCIC defects; under `A_k` it cooperates; the troll cooperates either way. -/
theorem dich_DupocTrollBot_vs_CIMCIC :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (DupocTrollBot k)) k) →
        EvalGraph 2 (progCode (DupocTrollBot k)) (progCode (CIMCIC k)) (progCode (DupocTrollBot k)) (actCode .C) ∧
        EvalGraph 2 (progCode (CIMCIC k)) (progCode (DupocTrollBot k)) (progCode (CIMCIC k)) (actCode .D)) ∧
      (LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (DupocTrollBot k)) k) →
        EvalGraph 2 (progCode (DupocTrollBot k)) (progCode (CIMCIC k)) (progCode (DupocTrollBot k)) (actCode .C) ∧
        EvalGraph 2 (progCode (CIMCIC k)) (progCode (DupocTrollBot k)) (progCode (CIMCIC k)) (actCode .C)) := by
  refine ⟨0, fun k _ ↦ ?_⟩
  simp only [hingeB phiC]
  constructor
  · intro hn
    refine ⟨floor_DupocTrollBot_vs_CIMCIC_right k, ?_⟩
    rw [progCode_CIMCIC_search] at hn ⊢
    exact search_else phiC hn (const_play 0 _ _ _)
  · intro hf
    refine ⟨floor_DupocTrollBot_vs_CIMCIC_right k, ?_⟩
    rw [progCode_CIMCIC_search] at hf ⊢
    exact search_then phiC hf (const_play 0 _ _ _)

end floor

end ArithS
