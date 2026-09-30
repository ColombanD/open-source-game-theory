import ArithS.Bridge.Inst
import ArithS.Eval.SimTest
import PrisonersDilemma.Theorems.CooperateBot.vs_CooperateBot
import PrisonersDilemma.Theorems.CooperateBot.vs_DefectBot
import PrisonersDilemma.Theorems.DBot.vs_CooperateBot
import PrisonersDilemma.Theorems.DBot.vs_DBot
import PrisonersDilemma.Theorems.DBot.vs_DefectBot
import PrisonersDilemma.Theorems.DefectBot.vs_DefectBot
import PrisonersDilemma.Theorems.EBot.vs_CooperateBot
import PrisonersDilemma.Theorems.EBot.vs_DBot
import PrisonersDilemma.Theorems.EBot.vs_DefectBot
import PrisonersDilemma.Theorems.EBot.vs_EBot
import PrisonersDilemma.Theorems.EBot.vs_MirrorBot
import PrisonersDilemma.Theorems.EBot.vs_OBot
import PrisonersDilemma.Theorems.EBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.MirrorBot.vs_CooperateBot
import PrisonersDilemma.Theorems.MirrorBot.vs_DBot
import PrisonersDilemma.Theorems.MirrorBot.vs_DefectBot
import PrisonersDilemma.Theorems.MirrorBot.vs_MirrorBot
import PrisonersDilemma.Theorems.MirrorBot.vs_OBot
import PrisonersDilemma.Theorems.MirrorBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.OBot.vs_CooperateBot
import PrisonersDilemma.Theorems.OBot.vs_DBot
import PrisonersDilemma.Theorems.OBot.vs_DefectBot
import PrisonersDilemma.Theorems.OBot.vs_OBot
import PrisonersDilemma.Theorems.OBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.TitForTatBot.vs_CooperateBot
import PrisonersDilemma.Theorems.TitForTatBot.vs_DBot
import PrisonersDilemma.Theorems.TitForTatBot.vs_DefectBot
import PrisonersDilemma.Theorems.TitForTatBot.vs_TitForTatBot

/-!
# ArithS.Cells.SearchFree — the 28 search-free cells of the census in PA-`S'`

`Research/Notes/ROUTE_B_SCOPE.md` §3 Phase 4, class **SF** of `ROUTE_B_CENSUS.md` (2026-09-23):
both players in {CooperateBot, DefectBot, MirrorBot, TitForTatBot, DBot, EBot, OBot} — `const/sim/ite`
only, no `.search` node anywhere, so the arithmetized evaluator NEVER consults `□_k` and the cells
are unconditional: no oracle (`GuardAgree`), no Löb, no floor, no budget. Every cell is the engine's
`OutcomeSpec .nobudget pad` theorem TRANSFERRED to `EvalGraph` at ℕ, at the SAME fuel (the pad).

1. **The search-free transfer at the same fuel.** `AgentConverse.evalGraph_of_eval` is the
   engine → arithmetic direction under `GuardAgree` and with an EXISTENTIAL arithmetized fuel; here
   the same clause-by-clause induction (`Inv true`: the invariant forbids search nodes, so the
   `.search` arm is vacuous — `Inv.search` yields `true = false`) shows the fuels COINCIDE:
   `evalGraph_of_eval_searchFree : PD.eval n me opp body = some a → EvalGraph n ⌜me⌝ ⌜opp⌝ ⌜body⌝ a`
   — the engine's `eval` and `EvalGraph` step in lockstep on `const/self/opp/bot/sim/ite`
   (`Eval.lean`'s clause lemmas mirror `Dynamics.eval`'s equations one to one). This file never
   unfolds the `search` clause of `EvalGraph` and never names the consulted guard code.
2. **The bridge**: `outcome_evalGraph_of_searchFree` (an engine `outcome n L R = some (a, b)` on
   search-free proper modest players is the pair of arithmetized plays at fuel `n`) and its
   template form `outcomeSpec_evalGraph_of_searchFree` (from `OutcomeSpec .nobudget pad`, at fuel
   `pad`, the `fuel = 0` instance of the cofinite statement).
3. **The seven players** are `SearchFreePlayer` (proper, modest, search-free), each by `rfl`/`simp`.
4. **The 27 terminating cells** `sf_<L>_vs_<R> : EvalGraph pad ⌜L⌝ ⌜R⌝ ⌜L⌝ a ∧ EvalGraph pad ⌜R⌝ ⌜L⌝
   ⌜R⌝ b`, one line each, at the engine's pad; **`sf_MirrorBot_vs_MirrorBot`**, the `none` cell, is
   NON-termination at every fuel (`SimTest.mirror_vs_mirror`, through `progCode_MirrorBot`).
5. **PA proves every positive atom**: `pa_proves_sentenceAt_of_evalGraph` (an arithmetized play at ℕ makes
   the instantiated atom sentence a PA theorem — `models_sentenceAt_plays` + `models_inst` +
   Σ₁-completeness, the body of `Inst.pa_proves_sentenceAt_inst_searchFree` without the engine
   certificate), `pa_cell_of_evalGraph` (both atoms of a cell as `Aι`, the `Leaf.atom` shape of
   T2-CORE), and the 27 instances `pa_<L>_vs_<R>`.
6. **The census in one line**: `searchFree_census` (the 28 cells) and `searchFree_pa_census`
   (the 54 atoms).

Route per cell: TRANSFER for all 27 terminating cells (cheaper than unfolding: the engine's proofs
already did the evaluation and the fuels coincide); the `none` cell cites `SimTest`. Fuels = the
engine's pads: 1 (const × const), 3 (one `sim` probe against a constant), 5–8, 11 (`EBot × EBot`).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open PD.Bots PD.Theorems

/-! ### 1. The search-free transfer at the same fuel -/

/-- The core induction: on a search-free frame (`Inv true`), an engine run at fuel `n` is an
arithmetized run at the SAME fuel `n`. Clause by clause as `AgentConverse.evalGraph_of_eval_core`;
the `.search` arm is unreachable (`Inv.search` gives `true = false`). -/
theorem evalGraph_of_eval_searchFree_core :
    ∀ (n : ℕ) (me opp body : PD.Prog) (a : PD.Action), Inv true me opp body →
      PD.eval n me opp body = some a →
      EvalGraph n (progCode me) (progCode opp) (progCode body) (actCode a) := by
  intro n
  induction n with
  | zero => intro me opp body a _ h; simp [PD.eval] at h
  | succ n ih =>
    intro me opp body a hI h
    cases body with
    | const c =>
      have hc : c = a := by simpa [PD.eval] using h
      subst hc
      rw [progCode_const]
      exact EvalGraph.const_iff.mpr rfl
    | self =>
      rw [PD.eval] at h
      rw [progCode_self, EvalGraph.self_iff]
      exact ih me opp me a (Inv.self hI) h
    | opp =>
      rw [PD.eval] at h
      rw [progCode_opp, EvalGraph.opp_iff]
      exact ih me opp opp a (Inv.opp hI) h
    | bot p =>
      rw [PD.eval] at h
      rw [progCode_bot, EvalGraph.bot_iff]
      exact ih me opp p a (Inv.bot hI) h
    | sim p q =>
      rw [PD.eval] at h
      have hN := ih _ _ _ a (Inv.sim hI) h
      have hmb := hI.2.2.2.2.1
      simp only [modestP, Bool.and_eq_true] at hmb
      rw [progCode_subst hI.1 hI.2.1 p (fragP_of_modestP p hmb.1.2),
        progCode_subst hI.1 hI.2.1 q (fragP_of_modestP q hmb.2)] at hN
      rw [progCode_sim, EvalGraph.sim_iff]
      exact hN
    | ite b c p q =>
      obtain ⟨hIb, hIp, hIq⟩ := Inv.ite hI
      rw [PD.eval] at h
      cases hb : PD.eval n me opp b with
      | none => simp [hb] at h
      | some r =>
        rw [hb] at h
        simp only [bind, Option.bind] at h
        have h₁ := ih me opp b r hIb hb
        rw [progCode_ite, EvalGraph.ite_iff]
        by_cases hr : (r == c) = true
        · rw [if_pos hr] at h
          exact ⟨actCode r, h₁, Or.inl ⟨actCode_eq_of_beq hr, ih me opp p a hIp h⟩⟩
        · rw [if_neg hr] at h
          exact ⟨actCode r, h₁,
            Or.inr ⟨actCode_ne_of_beq_false (Bool.eq_false_iff.mpr hr), ih me opp q a hIq h⟩⟩
    | search k φ p q => exact absurd (Inv.search hI).1 (by decide)
    | tvote v θ p q => exact (Inv.tvote hI).elim
    | sys defs i => exact (Inv.sys hI).elim
    | selfIdx j => exact (Inv.selfIdx hI).elim

/-- A search-free player: proper (not a bare pronoun), modest, no `.search` node. -/
def SearchFreePlayer (p : PD.Prog) : Prop :=
  ProperPlayer p ∧ modestP p = true ∧ p.hasSearch = false

/-- **The search-free transfer, same fuel**: no oracle, no certificate. -/
theorem evalGraph_of_eval_searchFree {me opp body : PD.Prog} {a : PD.Action} {n : ℕ}
    (h : PD.eval n me opp body = some a) (hme : SearchFreePlayer me) (hopp : SearchFreePlayer opp)
    (hb : modestP body = true) (hsb : body.hasSearch = false) :
    EvalGraph n (progCode me) (progCode opp) (progCode body) (actCode a) :=
  evalGraph_of_eval_searchFree_core n me opp body a
    ⟨hme.1, hopp.1, hme.2.1, hopp.2.1, hb, fun _ ↦ ⟨hme.2.2, hopp.2.2, hsb⟩⟩ h

/-- The play form (`eval me opp me`). -/
theorem play_evalGraph_of_searchFree {me opp : PD.Prog} {a : PD.Action} {n : ℕ}
    (h : PD.play n me opp = some a) (hme : SearchFreePlayer me) (hopp : SearchFreePlayer opp) :
    EvalGraph n (progCode me) (progCode opp) (progCode me) (actCode a) :=
  evalGraph_of_eval_searchFree h hme hopp hme.2.1 hme.2.2

/-! ### 2. The bridge -/

/-- **The bridge**: an engine outcome on search-free players is the pair of arithmetized plays at
the same fuel. -/
theorem outcome_evalGraph_of_searchFree {L R : PD.Prog} {a b : PD.Action} {n : ℕ}
    (h : PD.outcome n L R = some (a, b)) (hL : SearchFreePlayer L) (hR : SearchFreePlayer R) :
    EvalGraph n (progCode L) (progCode R) (progCode L) (actCode a) ∧
    EvalGraph n (progCode R) (progCode L) (progCode R) (actCode b) :=
  let ⟨ha, hb⟩ := (outcome_eq_some_iff n L R a b).mp h
  ⟨play_evalGraph_of_searchFree ha hL hR, play_evalGraph_of_searchFree hb hR hL⟩

/-- The template form: from the engine's `OutcomeSpec .nobudget pad` (cofinite in the fuel) to
the arithmetized cell at fuel `pad` (its `fuel = 0` instance). -/
theorem outcomeSpec_evalGraph_of_searchFree {pad : ℕ} {L R : PD.Prog} {a b : PD.Action}
    (h : PD.OutcomeSpec .nobudget pad (fun _ => L) (fun _ => R) (some (a, b)))
    (hL : SearchFreePlayer L) (hR : SearchFreePlayer R) :
    EvalGraph pad (progCode L) (progCode R) (progCode L) (actCode a) ∧
    EvalGraph pad (progCode R) (progCode L) (progCode R) (actCode b) := by
  have h0 : PD.outcome (0 + pad) L R = some (a, b) := h 0
  rw [Nat.zero_add] at h0
  exact outcome_evalGraph_of_searchFree h0 hL hR

/-- **PA proves the atom of an arithmetized play** (no engine certificate, no oracle): a run of
`EvalGraph` at ℕ makes the instantiated atom sentence true (`models_sentenceAt_plays`, `models_inst`),
hence a PA theorem by Σ₁-completeness. -/
theorem pa_proves_sentenceAt_of_evalGraph (me' opp' : PD.Prog) {me opp : PD.Prog} {a : PD.Action} {N : ℕ}
    (h : EvalGraph N (progCode me) (progCode opp) (progCode me) (actCode a))
    (hme : ProperPlayer me) (hopp : ProperPlayer opp) :
    𝗣𝗔 ⊢ Semiformula.lMap inst (sentenceAt me' opp' (.plays me opp a)) :=
  sigma_one_completeness (T := 𝗣𝗔) (hierarchy_lMap_inst_sentenceAt_plays me' opp' me opp a)
    ((models_inst _).mpr ((models_sentenceAt_plays me' opp' me opp a hme hopp).mpr ⟨N, h⟩))

/-- Both atoms of a cell, as the T2-CORE realization `Aι` (`Aι L R a = lMap inst (sentenceAt L R
(.plays L R a))`, the `Leaf.atom` shape). -/
theorem pa_cell_of_evalGraph {L R : PD.Prog} {a b : PD.Action} {n : ℕ}
    (h : EvalGraph n (progCode L) (progCode R) (progCode L) (actCode a) ∧
      EvalGraph n (progCode R) (progCode L) (progCode R) (actCode b))
    (hL : ProperPlayer L) (hR : ProperPlayer R) :
    𝗣𝗔 ⊢ Aι L R a ∧ 𝗣𝗔 ⊢ Aι R L b :=
  ⟨pa_proves_sentenceAt_of_evalGraph L R h.1 hL hR, pa_proves_sentenceAt_of_evalGraph R L h.2 hR hL⟩

/-! ### 3. The seven search-free players -/

theorem sfp_CooperateBot : SearchFreePlayer CooperateBot :=
  ⟨⟨by simp [CooperateBot], by simp [CooperateBot]⟩, rfl, rfl⟩

theorem sfp_DefectBot : SearchFreePlayer DefectBot :=
  ⟨⟨by simp [DefectBot], by simp [DefectBot]⟩, rfl, rfl⟩

theorem sfp_MirrorBot : SearchFreePlayer MirrorBot :=
  ⟨⟨by simp [MirrorBot], by simp [MirrorBot]⟩, rfl, rfl⟩

theorem sfp_TitForTatBot : SearchFreePlayer TitForTatBot :=
  ⟨⟨by simp [TitForTatBot], by simp [TitForTatBot]⟩, rfl, rfl⟩

theorem sfp_DBot : SearchFreePlayer DBot :=
  ⟨⟨by simp [DBot], by simp [DBot]⟩, rfl, rfl⟩

theorem sfp_EBot : SearchFreePlayer EBot :=
  ⟨⟨by simp [EBot], by simp [EBot]⟩, rfl, rfl⟩

theorem sfp_OBot : SearchFreePlayer OBot :=
  ⟨⟨by simp [OBot], by simp [OBot]⟩, rfl, rfl⟩

/-- The code of the engine's `MirrorBot` is `SimTest.Mirror`. -/
theorem progCode_MirrorBot : progCode MirrorBot = Mirror := by
  simp [MirrorBot, Mirror]

/-! ### 4. The 27 terminating cells, by transfer at the engine's pad -/

/-- `CooperateBot × CooperateBot = (C, C)` at fuel 1 (engine `outcome_CooperateBot_vs_CooperateBot`, pad 1). -/
theorem sf_CooperateBot_vs_CooperateBot :
    EvalGraph 1 (progCode CooperateBot) (progCode CooperateBot) (progCode CooperateBot) (actCode .C) ∧
    EvalGraph 1 (progCode CooperateBot) (progCode CooperateBot) (progCode CooperateBot) (actCode .C) :=
  outcomeSpec_evalGraph_of_searchFree outcome_CooperateBot_vs_CooperateBot sfp_CooperateBot sfp_CooperateBot

/-- `CooperateBot × DefectBot = (C, D)` at fuel 1 (engine `outcome_CooperateBot_vs_DefectBot`, pad 1). -/
theorem sf_CooperateBot_vs_DefectBot :
    EvalGraph 1 (progCode CooperateBot) (progCode DefectBot) (progCode CooperateBot) (actCode .C) ∧
    EvalGraph 1 (progCode DefectBot) (progCode CooperateBot) (progCode DefectBot) (actCode .D) :=
  outcomeSpec_evalGraph_of_searchFree outcome_CooperateBot_vs_DefectBot sfp_CooperateBot sfp_DefectBot

/-- `DBot × CooperateBot = (D, C)` at fuel 3 (engine `outcome_DBot_vs_CooperateBot`, pad 3). -/
theorem sf_DBot_vs_CooperateBot :
    EvalGraph 3 (progCode DBot) (progCode CooperateBot) (progCode DBot) (actCode .D) ∧
    EvalGraph 3 (progCode CooperateBot) (progCode DBot) (progCode CooperateBot) (actCode .C) :=
  outcomeSpec_evalGraph_of_searchFree outcome_DBot_vs_CooperateBot sfp_DBot sfp_CooperateBot

/-- `DBot × DBot = (D, D)` at fuel 6 (engine `outcome_DBot_vs_DBot`, pad 6). -/
theorem sf_DBot_vs_DBot :
    EvalGraph 6 (progCode DBot) (progCode DBot) (progCode DBot) (actCode .D) ∧
    EvalGraph 6 (progCode DBot) (progCode DBot) (progCode DBot) (actCode .D) :=
  outcomeSpec_evalGraph_of_searchFree outcome_DBot_vs_DBot sfp_DBot sfp_DBot

/-- `DBot × DefectBot = (C, D)` at fuel 3 (engine `outcome_DBot_vs_DefectBot`, pad 3). -/
theorem sf_DBot_vs_DefectBot :
    EvalGraph 3 (progCode DBot) (progCode DefectBot) (progCode DBot) (actCode .C) ∧
    EvalGraph 3 (progCode DefectBot) (progCode DBot) (progCode DefectBot) (actCode .D) :=
  outcomeSpec_evalGraph_of_searchFree outcome_DBot_vs_DefectBot sfp_DBot sfp_DefectBot

/-- `DefectBot × DefectBot = (D, D)` at fuel 1 (engine `outcome_DefectBot_vs_DefectBot`, pad 1). -/
theorem sf_DefectBot_vs_DefectBot :
    EvalGraph 1 (progCode DefectBot) (progCode DefectBot) (progCode DefectBot) (actCode .D) ∧
    EvalGraph 1 (progCode DefectBot) (progCode DefectBot) (progCode DefectBot) (actCode .D) :=
  outcomeSpec_evalGraph_of_searchFree outcome_DefectBot_vs_DefectBot sfp_DefectBot sfp_DefectBot

/-- `EBot × CooperateBot = (D, C)` at fuel 3 (engine `outcome_EBot_vs_CooperateBot`, pad 3). -/
theorem sf_EBot_vs_CooperateBot :
    EvalGraph 3 (progCode EBot) (progCode CooperateBot) (progCode EBot) (actCode .D) ∧
    EvalGraph 3 (progCode CooperateBot) (progCode EBot) (progCode CooperateBot) (actCode .C) :=
  outcomeSpec_evalGraph_of_searchFree outcome_EBot_vs_CooperateBot sfp_EBot sfp_CooperateBot

/-- `EBot × DBot = (D, C)` at fuel 8 (engine `outcome_EBot_vs_DBot`, pad 8). -/
theorem sf_EBot_vs_DBot :
    EvalGraph 8 (progCode EBot) (progCode DBot) (progCode EBot) (actCode .D) ∧
    EvalGraph 8 (progCode DBot) (progCode EBot) (progCode DBot) (actCode .C) :=
  outcomeSpec_evalGraph_of_searchFree outcome_EBot_vs_DBot sfp_EBot sfp_DBot

/-- `EBot × DefectBot = (D, D)` at fuel 5 (engine `outcome_EBot_vs_DefectBot`, pad 5). -/
theorem sf_EBot_vs_DefectBot :
    EvalGraph 5 (progCode EBot) (progCode DefectBot) (progCode EBot) (actCode .D) ∧
    EvalGraph 5 (progCode DefectBot) (progCode EBot) (progCode DefectBot) (actCode .D) :=
  outcomeSpec_evalGraph_of_searchFree outcome_EBot_vs_DefectBot sfp_EBot sfp_DefectBot

/-- `EBot × EBot = (C, C)` at fuel 11 (engine `outcome_EBot_vs_EBot`, pad 11). -/
theorem sf_EBot_vs_EBot :
    EvalGraph 11 (progCode EBot) (progCode EBot) (progCode EBot) (actCode .C) ∧
    EvalGraph 11 (progCode EBot) (progCode EBot) (progCode EBot) (actCode .C) :=
  outcomeSpec_evalGraph_of_searchFree outcome_EBot_vs_EBot sfp_EBot sfp_EBot

/-- `EBot × MirrorBot = (C, C)` at fuel 8 (engine `outcome_EBot_vs_MirrorBot`, pad 8). -/
theorem sf_EBot_vs_MirrorBot :
    EvalGraph 8 (progCode EBot) (progCode MirrorBot) (progCode EBot) (actCode .C) ∧
    EvalGraph 8 (progCode MirrorBot) (progCode EBot) (progCode MirrorBot) (actCode .C) :=
  outcomeSpec_evalGraph_of_searchFree outcome_EBot_vs_MirrorBot sfp_EBot sfp_MirrorBot

/-- `EBot × OBot = (C, D)` at fuel 8 (engine `outcome_EBot_vs_OBot`, pad 8). -/
theorem sf_EBot_vs_OBot :
    EvalGraph 8 (progCode EBot) (progCode OBot) (progCode EBot) (actCode .C) ∧
    EvalGraph 8 (progCode OBot) (progCode EBot) (progCode OBot) (actCode .D) :=
  outcomeSpec_evalGraph_of_searchFree outcome_EBot_vs_OBot sfp_EBot sfp_OBot

/-- `EBot × TitForTatBot = (C, D)` at fuel 7 (engine `outcome_EBot_vs_TitForTatBot`, pad 7). -/
theorem sf_EBot_vs_TitForTatBot :
    EvalGraph 7 (progCode EBot) (progCode TitForTatBot) (progCode EBot) (actCode .C) ∧
    EvalGraph 7 (progCode TitForTatBot) (progCode EBot) (progCode TitForTatBot) (actCode .D) :=
  outcomeSpec_evalGraph_of_searchFree outcome_EBot_vs_TitForTatBot sfp_EBot sfp_TitForTatBot

/-- `MirrorBot × CooperateBot = (C, C)` at fuel 3 (engine `outcome_MirrorBot_vs_CooperateBot`, pad 3). -/
theorem sf_MirrorBot_vs_CooperateBot :
    EvalGraph 3 (progCode MirrorBot) (progCode CooperateBot) (progCode MirrorBot) (actCode .C) ∧
    EvalGraph 3 (progCode CooperateBot) (progCode MirrorBot) (progCode CooperateBot) (actCode .C) :=
  outcomeSpec_evalGraph_of_searchFree outcome_MirrorBot_vs_CooperateBot sfp_MirrorBot sfp_CooperateBot

/-- `MirrorBot × DBot = (C, C)` at fuel 6 (engine `outcome_MirrorBot_vs_DBot`, pad 6). -/
theorem sf_MirrorBot_vs_DBot :
    EvalGraph 6 (progCode MirrorBot) (progCode DBot) (progCode MirrorBot) (actCode .C) ∧
    EvalGraph 6 (progCode DBot) (progCode MirrorBot) (progCode DBot) (actCode .C) :=
  outcomeSpec_evalGraph_of_searchFree outcome_MirrorBot_vs_DBot sfp_MirrorBot sfp_DBot

/-- `MirrorBot × DefectBot = (D, D)` at fuel 3 (engine `outcome_MirrorBot_vs_DefectBot`, pad 3). -/
theorem sf_MirrorBot_vs_DefectBot :
    EvalGraph 3 (progCode MirrorBot) (progCode DefectBot) (progCode MirrorBot) (actCode .D) ∧
    EvalGraph 3 (progCode DefectBot) (progCode MirrorBot) (progCode DefectBot) (actCode .D) :=
  outcomeSpec_evalGraph_of_searchFree outcome_MirrorBot_vs_DefectBot sfp_MirrorBot sfp_DefectBot

/-- `MirrorBot × OBot = (D, D)` at fuel 7 (engine `outcome_MirrorBot_vs_OBot`, pad 7). -/
theorem sf_MirrorBot_vs_OBot :
    EvalGraph 7 (progCode MirrorBot) (progCode OBot) (progCode MirrorBot) (actCode .D) ∧
    EvalGraph 7 (progCode OBot) (progCode MirrorBot) (progCode OBot) (actCode .D) :=
  outcomeSpec_evalGraph_of_searchFree outcome_MirrorBot_vs_OBot sfp_MirrorBot sfp_OBot

/-- `MirrorBot × TitForTatBot = (C, C)` at fuel 6 (engine `outcome_MirrorBot_vs_TitForTatBot`, pad 6). -/
theorem sf_MirrorBot_vs_TitForTatBot :
    EvalGraph 6 (progCode MirrorBot) (progCode TitForTatBot) (progCode MirrorBot) (actCode .C) ∧
    EvalGraph 6 (progCode TitForTatBot) (progCode MirrorBot) (progCode TitForTatBot) (actCode .C) :=
  outcomeSpec_evalGraph_of_searchFree outcome_MirrorBot_vs_TitForTatBot sfp_MirrorBot sfp_TitForTatBot

/-- `OBot × CooperateBot = (C, C)` at fuel 5 (engine `outcome_OBot_vs_CooperateBot`, pad 5). -/
theorem sf_OBot_vs_CooperateBot :
    EvalGraph 5 (progCode OBot) (progCode CooperateBot) (progCode OBot) (actCode .C) ∧
    EvalGraph 5 (progCode CooperateBot) (progCode OBot) (progCode CooperateBot) (actCode .C) :=
  outcomeSpec_evalGraph_of_searchFree outcome_OBot_vs_CooperateBot sfp_OBot sfp_CooperateBot

/-- `OBot × DBot = (D, C)` at fuel 6 (engine `outcome_OBot_vs_DBot`, pad 6). -/
theorem sf_OBot_vs_DBot :
    EvalGraph 6 (progCode OBot) (progCode DBot) (progCode OBot) (actCode .D) ∧
    EvalGraph 6 (progCode DBot) (progCode OBot) (progCode DBot) (actCode .C) :=
  outcomeSpec_evalGraph_of_searchFree outcome_OBot_vs_DBot sfp_OBot sfp_DBot

/-- `OBot × DefectBot = (D, D)` at fuel 3 (engine `outcome_OBot_vs_DefectBot`, pad 3). -/
theorem sf_OBot_vs_DefectBot :
    EvalGraph 3 (progCode OBot) (progCode DefectBot) (progCode OBot) (actCode .D) ∧
    EvalGraph 3 (progCode DefectBot) (progCode OBot) (progCode DefectBot) (actCode .D) :=
  outcomeSpec_evalGraph_of_searchFree outcome_OBot_vs_DefectBot sfp_OBot sfp_DefectBot

/-- `OBot × OBot = (D, D)` at fuel 7 (engine `outcome_OBot_vs_OBot`, pad 7). -/
theorem sf_OBot_vs_OBot :
    EvalGraph 7 (progCode OBot) (progCode OBot) (progCode OBot) (actCode .D) ∧
    EvalGraph 7 (progCode OBot) (progCode OBot) (progCode OBot) (actCode .D) :=
  outcomeSpec_evalGraph_of_searchFree outcome_OBot_vs_OBot sfp_OBot sfp_OBot

/-- `OBot × TitForTatBot = (D, C)` at fuel 7 (engine `outcome_OBot_vs_TitForTatBot`, pad 7). -/
theorem sf_OBot_vs_TitForTatBot :
    EvalGraph 7 (progCode OBot) (progCode TitForTatBot) (progCode OBot) (actCode .D) ∧
    EvalGraph 7 (progCode TitForTatBot) (progCode OBot) (progCode TitForTatBot) (actCode .C) :=
  outcomeSpec_evalGraph_of_searchFree outcome_OBot_vs_TitForTatBot sfp_OBot sfp_TitForTatBot

/-- `TitForTatBot × CooperateBot = (C, C)` at fuel 3 (engine `outcome_TitForTatBot_vs_CooperateBot`, pad 3). -/
theorem sf_TitForTatBot_vs_CooperateBot :
    EvalGraph 3 (progCode TitForTatBot) (progCode CooperateBot) (progCode TitForTatBot) (actCode .C) ∧
    EvalGraph 3 (progCode CooperateBot) (progCode TitForTatBot) (progCode CooperateBot) (actCode .C) :=
  outcomeSpec_evalGraph_of_searchFree outcome_TitForTatBot_vs_CooperateBot sfp_TitForTatBot sfp_CooperateBot

/-- `TitForTatBot × DBot = (D, C)` at fuel 6 (engine `outcome_TitForTatBot_vs_DBot`, pad 6). -/
theorem sf_TitForTatBot_vs_DBot :
    EvalGraph 6 (progCode TitForTatBot) (progCode DBot) (progCode TitForTatBot) (actCode .D) ∧
    EvalGraph 6 (progCode DBot) (progCode TitForTatBot) (progCode DBot) (actCode .C) :=
  outcomeSpec_evalGraph_of_searchFree outcome_TitForTatBot_vs_DBot sfp_TitForTatBot sfp_DBot

/-- `TitForTatBot × DefectBot = (D, D)` at fuel 3 (engine `outcome_TitForTatBot_vs_DefectBot`, pad 3). -/
theorem sf_TitForTatBot_vs_DefectBot :
    EvalGraph 3 (progCode TitForTatBot) (progCode DefectBot) (progCode TitForTatBot) (actCode .D) ∧
    EvalGraph 3 (progCode DefectBot) (progCode TitForTatBot) (progCode DefectBot) (actCode .D) :=
  outcomeSpec_evalGraph_of_searchFree outcome_TitForTatBot_vs_DefectBot sfp_TitForTatBot sfp_DefectBot

/-- `TitForTatBot × TitForTatBot = (C, C)` at fuel 6 (engine `outcome_TitForTatBot_vs_TitForTatBot`, pad 6). -/
theorem sf_TitForTatBot_vs_TitForTatBot :
    EvalGraph 6 (progCode TitForTatBot) (progCode TitForTatBot) (progCode TitForTatBot) (actCode .C) ∧
    EvalGraph 6 (progCode TitForTatBot) (progCode TitForTatBot) (progCode TitForTatBot) (actCode .C) :=
  outcomeSpec_evalGraph_of_searchFree outcome_TitForTatBot_vs_TitForTatBot sfp_TitForTatBot sfp_TitForTatBot

/-- `MirrorBot × MirrorBot = none`: NON-termination at every fuel (`SimTest.mirror_vs_mirror`;
engine `outcome_MirrorBot_vs_MirrorBot`, the library's only proven no-outcome cell). -/
theorem sf_MirrorBot_vs_MirrorBot :
    ∀ n a, ¬ EvalGraph n (progCode MirrorBot) (progCode MirrorBot) (progCode MirrorBot) a := by
  rw [progCode_MirrorBot]; exact mirror_vs_mirror

/-! ### 5. PA proves every positive atom of the 27 terminating cells -/

theorem pa_CooperateBot_vs_CooperateBot : 𝗣𝗔 ⊢ Aι CooperateBot CooperateBot .C ∧ 𝗣𝗔 ⊢ Aι CooperateBot CooperateBot .C :=
  pa_cell_of_evalGraph sf_CooperateBot_vs_CooperateBot sfp_CooperateBot.1 sfp_CooperateBot.1

theorem pa_CooperateBot_vs_DefectBot : 𝗣𝗔 ⊢ Aι CooperateBot DefectBot .C ∧ 𝗣𝗔 ⊢ Aι DefectBot CooperateBot .D :=
  pa_cell_of_evalGraph sf_CooperateBot_vs_DefectBot sfp_CooperateBot.1 sfp_DefectBot.1

theorem pa_DBot_vs_CooperateBot : 𝗣𝗔 ⊢ Aι DBot CooperateBot .D ∧ 𝗣𝗔 ⊢ Aι CooperateBot DBot .C :=
  pa_cell_of_evalGraph sf_DBot_vs_CooperateBot sfp_DBot.1 sfp_CooperateBot.1

theorem pa_DBot_vs_DBot : 𝗣𝗔 ⊢ Aι DBot DBot .D ∧ 𝗣𝗔 ⊢ Aι DBot DBot .D :=
  pa_cell_of_evalGraph sf_DBot_vs_DBot sfp_DBot.1 sfp_DBot.1

theorem pa_DBot_vs_DefectBot : 𝗣𝗔 ⊢ Aι DBot DefectBot .C ∧ 𝗣𝗔 ⊢ Aι DefectBot DBot .D :=
  pa_cell_of_evalGraph sf_DBot_vs_DefectBot sfp_DBot.1 sfp_DefectBot.1

theorem pa_DefectBot_vs_DefectBot : 𝗣𝗔 ⊢ Aι DefectBot DefectBot .D ∧ 𝗣𝗔 ⊢ Aι DefectBot DefectBot .D :=
  pa_cell_of_evalGraph sf_DefectBot_vs_DefectBot sfp_DefectBot.1 sfp_DefectBot.1

theorem pa_EBot_vs_CooperateBot : 𝗣𝗔 ⊢ Aι EBot CooperateBot .D ∧ 𝗣𝗔 ⊢ Aι CooperateBot EBot .C :=
  pa_cell_of_evalGraph sf_EBot_vs_CooperateBot sfp_EBot.1 sfp_CooperateBot.1

theorem pa_EBot_vs_DBot : 𝗣𝗔 ⊢ Aι EBot DBot .D ∧ 𝗣𝗔 ⊢ Aι DBot EBot .C :=
  pa_cell_of_evalGraph sf_EBot_vs_DBot sfp_EBot.1 sfp_DBot.1

theorem pa_EBot_vs_DefectBot : 𝗣𝗔 ⊢ Aι EBot DefectBot .D ∧ 𝗣𝗔 ⊢ Aι DefectBot EBot .D :=
  pa_cell_of_evalGraph sf_EBot_vs_DefectBot sfp_EBot.1 sfp_DefectBot.1

theorem pa_EBot_vs_EBot : 𝗣𝗔 ⊢ Aι EBot EBot .C ∧ 𝗣𝗔 ⊢ Aι EBot EBot .C :=
  pa_cell_of_evalGraph sf_EBot_vs_EBot sfp_EBot.1 sfp_EBot.1

theorem pa_EBot_vs_MirrorBot : 𝗣𝗔 ⊢ Aι EBot MirrorBot .C ∧ 𝗣𝗔 ⊢ Aι MirrorBot EBot .C :=
  pa_cell_of_evalGraph sf_EBot_vs_MirrorBot sfp_EBot.1 sfp_MirrorBot.1

theorem pa_EBot_vs_OBot : 𝗣𝗔 ⊢ Aι EBot OBot .C ∧ 𝗣𝗔 ⊢ Aι OBot EBot .D :=
  pa_cell_of_evalGraph sf_EBot_vs_OBot sfp_EBot.1 sfp_OBot.1

theorem pa_EBot_vs_TitForTatBot : 𝗣𝗔 ⊢ Aι EBot TitForTatBot .C ∧ 𝗣𝗔 ⊢ Aι TitForTatBot EBot .D :=
  pa_cell_of_evalGraph sf_EBot_vs_TitForTatBot sfp_EBot.1 sfp_TitForTatBot.1

theorem pa_MirrorBot_vs_CooperateBot : 𝗣𝗔 ⊢ Aι MirrorBot CooperateBot .C ∧ 𝗣𝗔 ⊢ Aι CooperateBot MirrorBot .C :=
  pa_cell_of_evalGraph sf_MirrorBot_vs_CooperateBot sfp_MirrorBot.1 sfp_CooperateBot.1

theorem pa_MirrorBot_vs_DBot : 𝗣𝗔 ⊢ Aι MirrorBot DBot .C ∧ 𝗣𝗔 ⊢ Aι DBot MirrorBot .C :=
  pa_cell_of_evalGraph sf_MirrorBot_vs_DBot sfp_MirrorBot.1 sfp_DBot.1

theorem pa_MirrorBot_vs_DefectBot : 𝗣𝗔 ⊢ Aι MirrorBot DefectBot .D ∧ 𝗣𝗔 ⊢ Aι DefectBot MirrorBot .D :=
  pa_cell_of_evalGraph sf_MirrorBot_vs_DefectBot sfp_MirrorBot.1 sfp_DefectBot.1

theorem pa_MirrorBot_vs_OBot : 𝗣𝗔 ⊢ Aι MirrorBot OBot .D ∧ 𝗣𝗔 ⊢ Aι OBot MirrorBot .D :=
  pa_cell_of_evalGraph sf_MirrorBot_vs_OBot sfp_MirrorBot.1 sfp_OBot.1

theorem pa_MirrorBot_vs_TitForTatBot : 𝗣𝗔 ⊢ Aι MirrorBot TitForTatBot .C ∧ 𝗣𝗔 ⊢ Aι TitForTatBot MirrorBot .C :=
  pa_cell_of_evalGraph sf_MirrorBot_vs_TitForTatBot sfp_MirrorBot.1 sfp_TitForTatBot.1

theorem pa_OBot_vs_CooperateBot : 𝗣𝗔 ⊢ Aι OBot CooperateBot .C ∧ 𝗣𝗔 ⊢ Aι CooperateBot OBot .C :=
  pa_cell_of_evalGraph sf_OBot_vs_CooperateBot sfp_OBot.1 sfp_CooperateBot.1

theorem pa_OBot_vs_DBot : 𝗣𝗔 ⊢ Aι OBot DBot .D ∧ 𝗣𝗔 ⊢ Aι DBot OBot .C :=
  pa_cell_of_evalGraph sf_OBot_vs_DBot sfp_OBot.1 sfp_DBot.1

theorem pa_OBot_vs_DefectBot : 𝗣𝗔 ⊢ Aι OBot DefectBot .D ∧ 𝗣𝗔 ⊢ Aι DefectBot OBot .D :=
  pa_cell_of_evalGraph sf_OBot_vs_DefectBot sfp_OBot.1 sfp_DefectBot.1

theorem pa_OBot_vs_OBot : 𝗣𝗔 ⊢ Aι OBot OBot .D ∧ 𝗣𝗔 ⊢ Aι OBot OBot .D :=
  pa_cell_of_evalGraph sf_OBot_vs_OBot sfp_OBot.1 sfp_OBot.1

theorem pa_OBot_vs_TitForTatBot : 𝗣𝗔 ⊢ Aι OBot TitForTatBot .D ∧ 𝗣𝗔 ⊢ Aι TitForTatBot OBot .C :=
  pa_cell_of_evalGraph sf_OBot_vs_TitForTatBot sfp_OBot.1 sfp_TitForTatBot.1

theorem pa_TitForTatBot_vs_CooperateBot : 𝗣𝗔 ⊢ Aι TitForTatBot CooperateBot .C ∧ 𝗣𝗔 ⊢ Aι CooperateBot TitForTatBot .C :=
  pa_cell_of_evalGraph sf_TitForTatBot_vs_CooperateBot sfp_TitForTatBot.1 sfp_CooperateBot.1

theorem pa_TitForTatBot_vs_DBot : 𝗣𝗔 ⊢ Aι TitForTatBot DBot .D ∧ 𝗣𝗔 ⊢ Aι DBot TitForTatBot .C :=
  pa_cell_of_evalGraph sf_TitForTatBot_vs_DBot sfp_TitForTatBot.1 sfp_DBot.1

theorem pa_TitForTatBot_vs_DefectBot : 𝗣𝗔 ⊢ Aι TitForTatBot DefectBot .D ∧ 𝗣𝗔 ⊢ Aι DefectBot TitForTatBot .D :=
  pa_cell_of_evalGraph sf_TitForTatBot_vs_DefectBot sfp_TitForTatBot.1 sfp_DefectBot.1

theorem pa_TitForTatBot_vs_TitForTatBot : 𝗣𝗔 ⊢ Aι TitForTatBot TitForTatBot .C ∧ 𝗣𝗔 ⊢ Aι TitForTatBot TitForTatBot .C :=
  pa_cell_of_evalGraph sf_TitForTatBot_vs_TitForTatBot sfp_TitForTatBot.1 sfp_TitForTatBot.1

/-! ### 6. The census in one line -/

/-- **The search-free census**: all 28 SF cells of `ROUTE_B_CENSUS.md` hold in PA-`S'` at ℕ, at
the engine's pads; `MirrorBot × MirrorBot` is the non-termination cell. -/
theorem searchFree_census :
    (EvalGraph 1 (progCode CooperateBot) (progCode CooperateBot) (progCode CooperateBot) (actCode .C) ∧
      EvalGraph 1 (progCode CooperateBot) (progCode CooperateBot) (progCode CooperateBot) (actCode .C)) ∧
    (EvalGraph 1 (progCode CooperateBot) (progCode DefectBot) (progCode CooperateBot) (actCode .C) ∧
      EvalGraph 1 (progCode DefectBot) (progCode CooperateBot) (progCode DefectBot) (actCode .D)) ∧
    (EvalGraph 3 (progCode DBot) (progCode CooperateBot) (progCode DBot) (actCode .D) ∧
      EvalGraph 3 (progCode CooperateBot) (progCode DBot) (progCode CooperateBot) (actCode .C)) ∧
    (EvalGraph 6 (progCode DBot) (progCode DBot) (progCode DBot) (actCode .D) ∧
      EvalGraph 6 (progCode DBot) (progCode DBot) (progCode DBot) (actCode .D)) ∧
    (EvalGraph 3 (progCode DBot) (progCode DefectBot) (progCode DBot) (actCode .C) ∧
      EvalGraph 3 (progCode DefectBot) (progCode DBot) (progCode DefectBot) (actCode .D)) ∧
    (EvalGraph 1 (progCode DefectBot) (progCode DefectBot) (progCode DefectBot) (actCode .D) ∧
      EvalGraph 1 (progCode DefectBot) (progCode DefectBot) (progCode DefectBot) (actCode .D)) ∧
    (EvalGraph 3 (progCode EBot) (progCode CooperateBot) (progCode EBot) (actCode .D) ∧
      EvalGraph 3 (progCode CooperateBot) (progCode EBot) (progCode CooperateBot) (actCode .C)) ∧
    (EvalGraph 8 (progCode EBot) (progCode DBot) (progCode EBot) (actCode .D) ∧
      EvalGraph 8 (progCode DBot) (progCode EBot) (progCode DBot) (actCode .C)) ∧
    (EvalGraph 5 (progCode EBot) (progCode DefectBot) (progCode EBot) (actCode .D) ∧
      EvalGraph 5 (progCode DefectBot) (progCode EBot) (progCode DefectBot) (actCode .D)) ∧
    (EvalGraph 11 (progCode EBot) (progCode EBot) (progCode EBot) (actCode .C) ∧
      EvalGraph 11 (progCode EBot) (progCode EBot) (progCode EBot) (actCode .C)) ∧
    (EvalGraph 8 (progCode EBot) (progCode MirrorBot) (progCode EBot) (actCode .C) ∧
      EvalGraph 8 (progCode MirrorBot) (progCode EBot) (progCode MirrorBot) (actCode .C)) ∧
    (EvalGraph 8 (progCode EBot) (progCode OBot) (progCode EBot) (actCode .C) ∧
      EvalGraph 8 (progCode OBot) (progCode EBot) (progCode OBot) (actCode .D)) ∧
    (EvalGraph 7 (progCode EBot) (progCode TitForTatBot) (progCode EBot) (actCode .C) ∧
      EvalGraph 7 (progCode TitForTatBot) (progCode EBot) (progCode TitForTatBot) (actCode .D)) ∧
    (EvalGraph 3 (progCode MirrorBot) (progCode CooperateBot) (progCode MirrorBot) (actCode .C) ∧
      EvalGraph 3 (progCode CooperateBot) (progCode MirrorBot) (progCode CooperateBot) (actCode .C)) ∧
    (EvalGraph 6 (progCode MirrorBot) (progCode DBot) (progCode MirrorBot) (actCode .C) ∧
      EvalGraph 6 (progCode DBot) (progCode MirrorBot) (progCode DBot) (actCode .C)) ∧
    (EvalGraph 3 (progCode MirrorBot) (progCode DefectBot) (progCode MirrorBot) (actCode .D) ∧
      EvalGraph 3 (progCode DefectBot) (progCode MirrorBot) (progCode DefectBot) (actCode .D)) ∧
    (∀ n a, ¬ EvalGraph n (progCode MirrorBot) (progCode MirrorBot) (progCode MirrorBot) a) ∧
    (EvalGraph 7 (progCode MirrorBot) (progCode OBot) (progCode MirrorBot) (actCode .D) ∧
      EvalGraph 7 (progCode OBot) (progCode MirrorBot) (progCode OBot) (actCode .D)) ∧
    (EvalGraph 6 (progCode MirrorBot) (progCode TitForTatBot) (progCode MirrorBot) (actCode .C) ∧
      EvalGraph 6 (progCode TitForTatBot) (progCode MirrorBot) (progCode TitForTatBot) (actCode .C)) ∧
    (EvalGraph 5 (progCode OBot) (progCode CooperateBot) (progCode OBot) (actCode .C) ∧
      EvalGraph 5 (progCode CooperateBot) (progCode OBot) (progCode CooperateBot) (actCode .C)) ∧
    (EvalGraph 6 (progCode OBot) (progCode DBot) (progCode OBot) (actCode .D) ∧
      EvalGraph 6 (progCode DBot) (progCode OBot) (progCode DBot) (actCode .C)) ∧
    (EvalGraph 3 (progCode OBot) (progCode DefectBot) (progCode OBot) (actCode .D) ∧
      EvalGraph 3 (progCode DefectBot) (progCode OBot) (progCode DefectBot) (actCode .D)) ∧
    (EvalGraph 7 (progCode OBot) (progCode OBot) (progCode OBot) (actCode .D) ∧
      EvalGraph 7 (progCode OBot) (progCode OBot) (progCode OBot) (actCode .D)) ∧
    (EvalGraph 7 (progCode OBot) (progCode TitForTatBot) (progCode OBot) (actCode .D) ∧
      EvalGraph 7 (progCode TitForTatBot) (progCode OBot) (progCode TitForTatBot) (actCode .C)) ∧
    (EvalGraph 3 (progCode TitForTatBot) (progCode CooperateBot) (progCode TitForTatBot) (actCode .C) ∧
      EvalGraph 3 (progCode CooperateBot) (progCode TitForTatBot) (progCode CooperateBot) (actCode .C)) ∧
    (EvalGraph 6 (progCode TitForTatBot) (progCode DBot) (progCode TitForTatBot) (actCode .D) ∧
      EvalGraph 6 (progCode DBot) (progCode TitForTatBot) (progCode DBot) (actCode .C)) ∧
    (EvalGraph 3 (progCode TitForTatBot) (progCode DefectBot) (progCode TitForTatBot) (actCode .D) ∧
      EvalGraph 3 (progCode DefectBot) (progCode TitForTatBot) (progCode DefectBot) (actCode .D)) ∧
    (EvalGraph 6 (progCode TitForTatBot) (progCode TitForTatBot) (progCode TitForTatBot) (actCode .C) ∧
      EvalGraph 6 (progCode TitForTatBot) (progCode TitForTatBot) (progCode TitForTatBot) (actCode .C)) :=
  ⟨sf_CooperateBot_vs_CooperateBot, sf_CooperateBot_vs_DefectBot, sf_DBot_vs_CooperateBot, sf_DBot_vs_DBot, sf_DBot_vs_DefectBot, sf_DefectBot_vs_DefectBot, sf_EBot_vs_CooperateBot, sf_EBot_vs_DBot, sf_EBot_vs_DefectBot, sf_EBot_vs_EBot, sf_EBot_vs_MirrorBot, sf_EBot_vs_OBot, sf_EBot_vs_TitForTatBot, sf_MirrorBot_vs_CooperateBot, sf_MirrorBot_vs_DBot, sf_MirrorBot_vs_DefectBot, sf_MirrorBot_vs_MirrorBot, sf_MirrorBot_vs_OBot, sf_MirrorBot_vs_TitForTatBot, sf_OBot_vs_CooperateBot, sf_OBot_vs_DBot, sf_OBot_vs_DefectBot, sf_OBot_vs_OBot, sf_OBot_vs_TitForTatBot, sf_TitForTatBot_vs_CooperateBot, sf_TitForTatBot_vs_DBot, sf_TitForTatBot_vs_DefectBot, sf_TitForTatBot_vs_TitForTatBot⟩

/-- **The PA census**: PA proves the 54 positive atoms (`Aι`, the `Leaf.atom` shape of T2-CORE
at the instantiation `c_C ↦ 0, c_D ↦ 1`) of the 27 terminating SF cells. -/
theorem searchFree_pa_census :
    (𝗣𝗔 ⊢ Aι CooperateBot CooperateBot .C ∧ 𝗣𝗔 ⊢ Aι CooperateBot CooperateBot .C) ∧
    (𝗣𝗔 ⊢ Aι CooperateBot DefectBot .C ∧ 𝗣𝗔 ⊢ Aι DefectBot CooperateBot .D) ∧
    (𝗣𝗔 ⊢ Aι DBot CooperateBot .D ∧ 𝗣𝗔 ⊢ Aι CooperateBot DBot .C) ∧
    (𝗣𝗔 ⊢ Aι DBot DBot .D ∧ 𝗣𝗔 ⊢ Aι DBot DBot .D) ∧
    (𝗣𝗔 ⊢ Aι DBot DefectBot .C ∧ 𝗣𝗔 ⊢ Aι DefectBot DBot .D) ∧
    (𝗣𝗔 ⊢ Aι DefectBot DefectBot .D ∧ 𝗣𝗔 ⊢ Aι DefectBot DefectBot .D) ∧
    (𝗣𝗔 ⊢ Aι EBot CooperateBot .D ∧ 𝗣𝗔 ⊢ Aι CooperateBot EBot .C) ∧
    (𝗣𝗔 ⊢ Aι EBot DBot .D ∧ 𝗣𝗔 ⊢ Aι DBot EBot .C) ∧
    (𝗣𝗔 ⊢ Aι EBot DefectBot .D ∧ 𝗣𝗔 ⊢ Aι DefectBot EBot .D) ∧
    (𝗣𝗔 ⊢ Aι EBot EBot .C ∧ 𝗣𝗔 ⊢ Aι EBot EBot .C) ∧
    (𝗣𝗔 ⊢ Aι EBot MirrorBot .C ∧ 𝗣𝗔 ⊢ Aι MirrorBot EBot .C) ∧
    (𝗣𝗔 ⊢ Aι EBot OBot .C ∧ 𝗣𝗔 ⊢ Aι OBot EBot .D) ∧
    (𝗣𝗔 ⊢ Aι EBot TitForTatBot .C ∧ 𝗣𝗔 ⊢ Aι TitForTatBot EBot .D) ∧
    (𝗣𝗔 ⊢ Aι MirrorBot CooperateBot .C ∧ 𝗣𝗔 ⊢ Aι CooperateBot MirrorBot .C) ∧
    (𝗣𝗔 ⊢ Aι MirrorBot DBot .C ∧ 𝗣𝗔 ⊢ Aι DBot MirrorBot .C) ∧
    (𝗣𝗔 ⊢ Aι MirrorBot DefectBot .D ∧ 𝗣𝗔 ⊢ Aι DefectBot MirrorBot .D) ∧
    (𝗣𝗔 ⊢ Aι MirrorBot OBot .D ∧ 𝗣𝗔 ⊢ Aι OBot MirrorBot .D) ∧
    (𝗣𝗔 ⊢ Aι MirrorBot TitForTatBot .C ∧ 𝗣𝗔 ⊢ Aι TitForTatBot MirrorBot .C) ∧
    (𝗣𝗔 ⊢ Aι OBot CooperateBot .C ∧ 𝗣𝗔 ⊢ Aι CooperateBot OBot .C) ∧
    (𝗣𝗔 ⊢ Aι OBot DBot .D ∧ 𝗣𝗔 ⊢ Aι DBot OBot .C) ∧
    (𝗣𝗔 ⊢ Aι OBot DefectBot .D ∧ 𝗣𝗔 ⊢ Aι DefectBot OBot .D) ∧
    (𝗣𝗔 ⊢ Aι OBot OBot .D ∧ 𝗣𝗔 ⊢ Aι OBot OBot .D) ∧
    (𝗣𝗔 ⊢ Aι OBot TitForTatBot .D ∧ 𝗣𝗔 ⊢ Aι TitForTatBot OBot .C) ∧
    (𝗣𝗔 ⊢ Aι TitForTatBot CooperateBot .C ∧ 𝗣𝗔 ⊢ Aι CooperateBot TitForTatBot .C) ∧
    (𝗣𝗔 ⊢ Aι TitForTatBot DBot .D ∧ 𝗣𝗔 ⊢ Aι DBot TitForTatBot .C) ∧
    (𝗣𝗔 ⊢ Aι TitForTatBot DefectBot .D ∧ 𝗣𝗔 ⊢ Aι DefectBot TitForTatBot .D) ∧
    (𝗣𝗔 ⊢ Aι TitForTatBot TitForTatBot .C ∧ 𝗣𝗔 ⊢ Aι TitForTatBot TitForTatBot .C) :=
  ⟨pa_CooperateBot_vs_CooperateBot, pa_CooperateBot_vs_DefectBot, pa_DBot_vs_CooperateBot, pa_DBot_vs_DBot, pa_DBot_vs_DefectBot, pa_DefectBot_vs_DefectBot, pa_EBot_vs_CooperateBot, pa_EBot_vs_DBot, pa_EBot_vs_DefectBot, pa_EBot_vs_EBot, pa_EBot_vs_MirrorBot, pa_EBot_vs_OBot, pa_EBot_vs_TitForTatBot, pa_MirrorBot_vs_CooperateBot, pa_MirrorBot_vs_DBot, pa_MirrorBot_vs_DefectBot, pa_MirrorBot_vs_OBot, pa_MirrorBot_vs_TitForTatBot, pa_OBot_vs_CooperateBot, pa_OBot_vs_DBot, pa_OBot_vs_DefectBot, pa_OBot_vs_OBot, pa_OBot_vs_TitForTatBot, pa_TitForTatBot_vs_CooperateBot, pa_TitForTatBot_vs_DBot, pa_TitForTatBot_vs_DefectBot, pa_TitForTatBot_vs_TitForTatBot⟩

end ArithS
