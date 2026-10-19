import ArithS.Tau.Spec
import ArithS.Cells.SoundnessCells

/-!
# ArithS.Tau.Columns — what the hypotheses' instances play, on codes (Phase 3)

A tau bit is the base cell on the compiled instances (`Research/Notes/SPRIME_SOURCE_OF_TRUTH.md` §3, "a tau bit
at point mass IS the base cell"): the row of a search-free template at hypothesis `T` is decided by what `T`'s
instance at a NAMED target plays against itself — τ(TFTSim)'s row is the `coop` column of the table
(`instCode k T .coop` run in its own frame), τ(DBot)'s row the `defect` column negated, τ(OBot)'s and τ(EBot)'s
rows cascades over both columns (and τ(EBot)'s third watch, the `mirror` column). This module proves those
column bits once, as `bitEventually T B a` (`Tau/Spec.lean`), so that every row file is a case split over
`paperOrder` citing them — and so that the next rows (τ(Dupoc)'s `coop` slot IS `col_dupoc_coop`, …) reuse them.

Methods, per bit (the base cell's, replayed on the instance code):
* **const / SF** — the instance is a constant or a `.sim`/`.ite` tree over constants: direct evaluation by the
  inversion lemmas (`watch_fires`/`watch_falls`/`sim_bot_plays`), no transfer from the engine needed;
* **SND (closed guard)** — a `.search` on a CLOSED, `k`-free guard that is FALSE in ℕ: never found at any budget
  (`snd_else_of_false`), else branch (`closed_not_found` + `search_else`);
* **POS (closed guard)** — a `.search` on a closed, `k`-free guard that is a `TAct`-theorem: found at every
  budget above its (fixed) proof length (`tact_proves_plays_closed`/`tact_eq_const` + `found_of_tact`), in ANY
  frame (`sentenceAt_closed_eq`: a closed formula's realization ignores the frame);
* **SND (self-refuting implication)** — CIMCIC's instance at the defector: a proof of its guard would make it
  cooperate, which falsifies the guard (`cimcic_selfref_not_found`'s argument, in the instance's own frame,
  transferred to the probe frame by `guardOf_self_guard_frame`);
* **bridge** — the natives' instances at `coop`/`defect` are Dupoc's by `rfl` (`inst_maxconfidence_eq_dupoc`).

The three bits whose guard names the instance ITSELF — `col_cimcic_coop`, `col_dimcid_defect` (POS on the
bot-wrapped instance's own description) and `col_dimcid_coop` (the Löb FLIP) — are in `Tau/Described.lean`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open PD PD.Tau

/-! ### 1. Run-stage watches and sim copies on codes -/

/-- A frozen instance `c` run in its own frame (`.bot c` on both sides) plays `r`: the `.sim (.bot c) (.bot c)`
node plays `r` in ANY frame. -/
theorem sim_bot_plays {n me opp c r : ℕ} (h : EvalGraph n (pBot c) (pBot c) c r) :
    EvalGraph (n + 2) me opp (pSim (pBot c) (pBot c)) r := by
  show EvalGraph (n + 1 + 1) me opp (pSim (pBot c) (pBot c)) r
  rw [EvalGraph.sim_iff, substCode_bot, EvalGraph.bot_iff]
  exact h

/-- A run-stage watch FIRES: the watched instance plays the test value, the then-branch decides. -/
theorem watch_fires {n me opp c test p q a : ℕ} (hc : EvalGraph n (pBot c) (pBot c) c test)
    (hp : EvalGraph n me opp p a) :
    EvalGraph (n + 3) me opp (pIte (pSim (pBot c) (pBot c)) test p q) a := by
  show EvalGraph (n + 2 + 1) me opp (pIte (pSim (pBot c) (pBot c)) test p q) a
  rw [EvalGraph.ite_iff]
  exact ⟨test, sim_bot_plays hc, Or.inl ⟨rfl, EvalGraph.mono_le (by omega) hp⟩⟩

/-- A run-stage watch FALLS through: the watched instance plays something else, the else-branch decides. -/
theorem watch_falls {n me opp c test r p q a : ℕ} (hc : EvalGraph n (pBot c) (pBot c) c r) (hr : r ≠ test)
    (hq : EvalGraph n me opp q a) :
    EvalGraph (n + 3) me opp (pIte (pSim (pBot c) (pBot c)) test p q) a := by
  show EvalGraph (n + 2 + 1) me opp (pIte (pSim (pBot c) (pBot c)) test p q) a
  rw [EvalGraph.ite_iff]
  exact ⟨r, sim_bot_plays hc, Or.inr ⟨hr, EvalGraph.mono_le (by omega) hq⟩⟩

/-- The fuel of a watch, lifted to a common `n` on both sides. -/
theorem watch_fires' {n m me opp c test p q a : ℕ} (hc : EvalGraph n (pBot c) (pBot c) c test)
    (hp : EvalGraph m me opp p a) :
    EvalGraph (n + m + 3) me opp (pIte (pSim (pBot c) (pBot c)) test p q) a :=
  watch_fires (EvalGraph.mono_le (by omega) hc) (EvalGraph.mono_le (by omega) hp)

theorem watch_falls' {n m me opp c test r p q a : ℕ} (hc : EvalGraph n (pBot c) (pBot c) c r) (hr : r ≠ test)
    (hq : EvalGraph m me opp q a) :
    EvalGraph (n + m + 3) me opp (pIte (pSim (pBot c) (pBot c)) test p q) a :=
  watch_falls (EvalGraph.mono_le (by omega) hc) hr (EvalGraph.mono_le (by omega) hq)

/-! ### 2. Closed guards: the realization ignores the frame; found / not found -/

/-- A CLOSED fragment formula realizes to the same sentence in every frame (`sentenceAt_subst` with
`φ.subst me opp = φ`). -/
theorem sentenceAt_closed_eq (φ : PD.Formula) (hc : closedF φ = true) (hf : fragF φ = true) {me opp : PD.Prog}
    (hme : ProperPlayer me) (hopp : ProperPlayer opp) (me' opp' : PD.Prog) :
    sentenceAt me' opp' φ = sentenceAt me opp φ := by
  have h := sentenceAt_subst me' opp' hme hopp φ hf
  rwa [subst_of_closedF φ me opp hc] at h

/-- **A closed guard that is a `TAct`-theorem is found at every large budget in EVERY frame** (the proof
length is fixed: the sentence does not depend on the frame, hence not on `k`). -/
theorem closed_found {φ : PD.Formula} (hc : closedF φ = true) (hf : fragF φ = true) {X Y : PD.Prog}
    (hX : ProperPlayer X) (hY : ProperPlayer Y) (h : TAct ⊢ sentenceAt X Y φ) :
    ∃ L : ℕ, ∀ k : ℕ, L ≤ k → ∀ me opp : PD.Prog,
      LenBox TAct k (guardCode (templateCode φ) (progCode me) (progCode opp)) := by
  have hns : noSelfIdxF φ = true := noSelfIdxF_of_fragF φ hf
  obtain ⟨L, hL⟩ := found_of_tact h hns
  refine ⟨L, fun k hk me opp ↦ ?_⟩
  have := hL k hk
  rwa [← quote_sentenceAt X Y φ hns, ← sentenceAt_closed_eq φ hc hf hX hY me opp, quote_sentenceAt me opp φ hns] at this

/-- **A guard FALSE in ℕ is never found** (soundness), stated on the instance's frame. -/
theorem closed_not_found {φ : PD.Formula} (hns : noSelfIdxF φ = true) {me opp : PD.Prog}
    (h : ¬ ℕ↓[LAct] ⊧ sentenceAt me opp φ) (k : ℕ) :
    ¬ LenBox TAct k (guardCode (templateCode φ) (progCode me) (progCode opp)) :=
  snd_else_of_false h hns

/-- A play atom over proper programs is FALSE in ℕ when the subject plays something else. -/
theorem not_models_plays {me' opp' P Q : PD.Prog} (hP : ProperPlayer P) (hQ : ProperPlayer Q) {a b : PD.Action}
    (hab : b ≠ a) {N : ℕ} (h : EvalGraph N (progCode P) (progCode Q) (progCode P) (actCode b)) :
    ¬ ℕ↓[LAct] ⊧ sentenceAt me' opp' (.plays P Q a) := by
  rw [models_sentenceAt_plays me' opp' P Q a hP hQ]
  rintro ⟨N', h'⟩
  exact hab (actCode_inj (EvalGraph.unique' h h'))

/-! #### The frozen constants -/

/-- `.bot (.const a)` is a search-free player. -/
theorem sfp_botConst (a : PD.Action) : SearchFreePlayer (.bot (.const a)) := ⟨⟨by simp, by simp⟩, rfl, rfl⟩

theorem progCode_botConst (a : PD.Action) : progCode (.bot (.const a)) = pBot (pConst (actCode a)) := by simp

theorem transpose_botConst (a : PD.Action) : (PD.Prog.bot (.const a)).transpose = .bot (.const a.swap) := by
  cases a <;> rfl

/-- **The true probe of a frozen constant is a `TAct`-theorem**: `.bot (.const a)` plays `a` against itself,
in both readings (the transposed probe is the transposed constant's). -/
theorem tact_probe_const (a : PD.Action) :
    TAct ⊢ sentenceAt (.bot (.const a)) (.bot (.const a)) (.plays (.bot (.const a)) (.bot (.const a)) a) := by
  refine tact_proves_plays_closed (sfp_botConst a) (sfp_botConst a) a (N := 2) ?_ (N' := 2) ?_
  · rw [progCode_botConst]; exact bot_const_play 0 _ _ _
  · rw [transpose_botConst, progCode_botConst]; exact bot_const_play 0 _ _ _

/-- The probe `.plays (.bot (.const a)) (.bot (.const a)) a` is FOUND at every large budget, in every frame. -/
theorem probe_const_found (a : PD.Action) :
    ∃ L : ℕ, ∀ k : ℕ, L ≤ k → ∀ me opp : PD.Prog,
      LenBox TAct k (guardCode (templateCode (.plays (.bot (.const a)) (.bot (.const a)) a)) (progCode me) (progCode opp)) :=
  closed_found (by cases a <;> rfl) (by cases a <;> rfl) (properPlayer_bot _) (properPlayer_bot _) (tact_probe_const a)

/-- The false probe `.plays (.bot (.const a)) (.bot (.const a)) b`, `b ≠ a`, is never found. -/
theorem probe_const_not_found {a b : PD.Action} (hab : a ≠ b) (me opp : PD.Prog) (k : ℕ) :
    ¬ LenBox TAct k (guardCode (templateCode (.plays (.bot (.const a)) (.bot (.const a)) b)) (progCode me) (progCode opp)) :=
  closed_not_found (by cases a <;> cases b <;> rfl)
    (not_models_plays (properPlayer_bot _) (properPlayer_bot _) hab (N := 2)
      (by rw [progCode_botConst]; exact bot_const_play 0 _ _ _)) k

/-! #### The `.eq` guard on constants (τ(CupodTroll)'s index-decided identity) -/

/-- `.eq (.const a) (.const b)` with `a ≠ b` is FALSE in ℕ (code inequality), hence never found. -/
theorem eq_const_not_found {a b : PD.Action} (hab : a ≠ b) (me opp : PD.Prog) (k : ℕ) :
    ¬ LenBox TAct k (guardCode (templateCode (.eq (.const a) (.const b))) (progCode me) (progCode opp)) := by
  refine closed_not_found (by cases a <;> cases b <;> rfl) ?_ k
  rw [models_sentenceAt_eq me opp _ _ ⟨by simp, by simp⟩, progCode_const, progCode_const]
  intro h
  exact hab (actCode_inj (pConst_inj h))

/-! #### The `.eq` guard FOUND: the true identity on a constant, in both readings -/

/-- The realization of the `.eq` atom in every model: the (cast) codes coincide. -/
theorem eval_sentenceAt_eq_V {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (me opp P Q : PD.Prog) (hP : ProperPlayer P) :
    Semiformula.Eval (s := stdReadingV V) ![] Empty.elim (sentenceAt me opp (.eq P Q)) ↔
      ((progCode P : ℕ) : V) = ((progCode Q : ℕ) : V) := by
  unfold sentenceAt
  rw [template_eq]
  unfold progGraph
  rw [progAux_of_ne hP.1 hP.2]
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, eval_closedDesc_V, Semiformula.eval_rel, stdReadingV_rel_eq, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_one, Semiterm.val_bvar]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, _, rfl, rfl, h⟩

/-- τ on a realized fragment formula (the generic form of `lMap_swap_sentenceAt_plays`). -/
theorem lMap_swap_sentenceAt {me opp : PD.Prog} (hme : fragP me = true) (hopp : fragP opp = true) (φ : PD.Formula)
    (hφ : fragF φ = true) :
    Semiformula.lMap swap (sentenceAt me opp φ) = sentenceAt me.transpose opp.transpose φ.transpose := by
  unfold sentenceAt
  rw [Semiformula.lMap_subst, lMap_swap_template φ hφ]
  congr 1
  funext i
  fin_cases i <;> simp [descriptionTerms, lMap_swap_canonicalMeta, lMap_swap_revalueUMeta, lMap_swap_revalueWMeta,
    transposeCode_progCode me hme, transposeCode_progCode opp hopp]

/-- **The true identity on a constant is a `TAct`-theorem**: in both readings the two description codes are
the same code. -/
theorem tact_eq_const (a : PD.Action) :
    TAct ⊢ sentenceAt (.const a) (.const a) (.eq (.const a) (.const a)) := by
  refine TAct_complete_of_readings _ fun M _ _ ↦ ?_
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  constructor
  · rw [← stdReadingV_eq_stdReading]
    exact (eval_sentenceAt_eq_V _ _ _ _ ⟨by simp, by simp⟩).mpr rfl
  · refine (Semiformula.eval_lMap (s₂ := stdReading M) (Φ := swap)).mp ?_
    rw [lMap_swap_sentenceAt rfl rfl _ (by cases a <;> rfl), ← stdReadingV_eq_stdReading]
    exact (eval_sentenceAt_eq_V _ _ _ _ ⟨by cases a <;> simp [PD.Prog.transpose], by cases a <;> simp [PD.Prog.transpose]⟩).mpr rfl

/-- `.eq (.const a) (.const a)` is FOUND at every large budget, in every frame. -/
theorem eq_const_found (a : PD.Action) :
    ∃ L : ℕ, ∀ k : ℕ, L ≤ k → ∀ me opp : PD.Prog,
      LenBox TAct k (guardCode (templateCode (.eq (.const a) (.const a))) (progCode me) (progCode opp)) :=
  closed_found (by cases a <;> rfl) (by cases a <;> rfl) ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ (tact_eq_const a)

/-! #### A `.self`-only implication guard ignores the frame's opponent -/

/-- The consulted guard of `.impl (.plays .self (.bot (.const d)) a) (.plays (.bot (.const d)) .self b)` (CIMCIC's
and DIMCID's instances at a constant target) is the same code for every opponent in the frame: the template
mentions no `.opp`, so its closed instantiation depends on `me` alone. -/
theorem guardOf_implConst_frame {me opp opp' : PD.Prog} (hme : ProperPlayer me) (hopp : ProperPlayer opp)
    (hopp' : ProperPlayer opp') (hme' : noSelfIdxP me = true) (hopp₁ : noSelfIdxP opp = true)
    (hopp₂ : noSelfIdxP opp' = true) (d a b : PD.Action) :
    guardOf (.impl (.plays .self (.bot (.const d)) a) (.plays (.bot (.const d)) .self b)) me opp =
      guardOf (.impl (.plays .self (.bot (.const d)) a) (.plays (.bot (.const d)) .self b)) me opp' := by
  have hf : fragF (.impl (.plays .self (.bot (.const d)) a) (.plays (.bot (.const d)) .self b)) = true := by
    cases d <;> rfl
  rw [guardOf_eq_templateCode_subst hme hopp _ hf hme' hopp₁, guardOf_eq_templateCode_subst hme hopp' _ hf hme' hopp₂]
  rfl

/-! ### 3. The instance codes the rows consult -/

/-- "The frozen constant `a` plays `b` against itself" — the probe atoms of Dupoc's/Cupod's/Prudent's
instances at a constant target. -/
abbrev prC (a b : PD.Action) : PD.Formula := .plays (.bot (.const a)) (.bot (.const a)) b

/-- CIMCIC's (`a = b = C`) and DIMCID's (`a = C`, `b = D`) guards at the constant target `d`. -/
abbrev implC (d a b : PD.Action) : PD.Formula := .impl (.plays .self (.bot (.const d)) a) (.plays (.bot (.const d)) .self b)

lemma progCode_bot_inst (k : ℕ) (A T : Tmpl) : progCode (.bot (inst (tauZoo k) A T)) = pBot (instCode k A T) := by
  rw [progCode_bot]; rfl

/-- The players of a bit's frame are proper and pronoun-free. -/
lemma properPlayer_botInst (k : ℕ) (A T : Tmpl) : ProperPlayer (.bot (inst (tauZoo k) A T)) := properPlayer_bot _

theorem instCode_dupoc_coop (k : ℕ) : instCode k .dupoc .coop = pSearch k (templateCode (prC .C .C)) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .dupoc .coop = .search k (prC .C .C) (.const .C) (.const .D) from rfl]
  rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

theorem instCode_dupoc_defect (k : ℕ) : instCode k .dupoc .defect = pSearch k (templateCode (prC .D .C)) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .dupoc .defect = .search k (prC .D .C) (.const .C) (.const .D) from rfl]
  rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

theorem instCode_cupod_coop (k : ℕ) : instCode k .cupod .coop = pSearch k (templateCode (prC .C .D)) (pConst 1) (pConst 0) := by
  unfold instCode
  rw [show inst (tauZoo k) .cupod .coop = .search k (prC .C .D) (.const .D) (.const .C) from rfl]
  rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

theorem instCode_cupod_defect (k : ℕ) : instCode k .cupod .defect = pSearch k (templateCode (prC .D .D)) (pConst 1) (pConst 0) := by
  unfold instCode
  rw [show inst (tauZoo k) .cupod .defect = .search k (prC .D .D) (.const .D) (.const .C) from rfl]
  rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

theorem instCode_prudent_coop (k : ℕ) : instCode k .prudent .coop =
    pSearch k (templateCode (prC .C .C)) (pSearch k (templateCode (prC .C .D)) (pConst 0) (pConst 1)) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .prudent .coop =
    .search k (prC .C .C) (.search k (prC .C .D) (.const .C) (.const .D)) (.const .D) from rfl]
  rw [progCode_search_noSnap _ _ _ _ rfl, progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

theorem instCode_prudent_defect (k : ℕ) : instCode k .prudent .defect =
    pSearch k (templateCode (prC .D .C)) (pSearch k (templateCode (prC .D .D)) (pConst 0) (pConst 1)) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .prudent .defect =
    .search k (prC .D .C) (.search k (prC .D .D) (.const .C) (.const .D)) (.const .D) from rfl]
  rw [progCode_search_noSnap _ _ _ _ rfl, progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

theorem instCode_cimcic_coop (k : ℕ) : instCode k .cimcic .coop = pSearch k (templateCode (implC .C .C .C)) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .cimcic .coop = .search k (implC .C .C .C) (.const .C) (.const .D) from rfl]
  rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

theorem instCode_cimcic_defect (k : ℕ) : instCode k .cimcic .defect = pSearch k (templateCode (implC .D .C .C)) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .cimcic .defect = .search k (implC .D .C .C) (.const .C) (.const .D) from rfl]
  rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

theorem instCode_dimcid_coop (k : ℕ) : instCode k .dimcid .coop = pSearch k (templateCode (implC .C .C .D)) (pConst 1) (pConst 0) := by
  unfold instCode
  rw [show inst (tauZoo k) .dimcid .coop = .search k (implC .C .C .D) (.const .D) (.const .C) from rfl]
  rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

theorem instCode_dimcid_defect (k : ℕ) : instCode k .dimcid .defect = pSearch k (templateCode (implC .D .C .D)) (pConst 1) (pConst 0) := by
  unfold instCode
  rw [show inst (tauZoo k) .dimcid .defect = .search k (implC .D .C .D) (.const .D) (.const .C) from rfl]
  rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

/-- τ(Mirror)'s instance at a constant: the bare forwarder of the frozen constant. -/
theorem instCode_mirror_coop (k : ℕ) : instCode k .mirror .coop = pSim (pBot (pConst 0)) (pBot (pConst 0)) := by
  unfold instCode
  rw [show inst (tauZoo k) .mirror .coop = .sim (.bot (.const .C)) (.bot (.const .C)) from rfl]
  simp [actCode]

theorem instCode_mirror_defect (k : ℕ) : instCode k .mirror .defect = pSim (pBot (pConst 1)) (pBot (pConst 1)) := by
  unfold instCode
  rw [show inst (tauZoo k) .mirror .defect = .sim (.bot (.const .D)) (.bot (.const .D)) from rfl]
  simp [actCode]

/-- The natives' instances at a hypothesis other than the three Dupoc-spec self-probers and `.just` are
Dupoc's (`Tau/Zoo.lean`, by `rfl`). -/
theorem instCode_maxconfidence_eq (k : ℕ) (T : Tmpl) (h1 : T ≠ .dupoc) (h2 : T ≠ .maxconfidence) (h3 : T ≠ .just) :
    instCode k .maxconfidence T = instCode k .dupoc T := by
  unfold instCode; rw [inst_maxconfidence_eq_dupoc k T h1 h2 h3]

theorem instCode_minconfidence_eq (k : ℕ) (T : Tmpl) (h1 : T ≠ .dupoc) (h2 : T ≠ .maxconfidence)
    (h3 : T ≠ .minconfidence) (h4 : T ≠ .just) :
    instCode k .minconfidence T = instCode k .dupoc T := by
  unfold instCode; rw [inst_minconfidence_eq_dupoc k T h1 h2 h3 h4]

theorem bitPlays_congr {k : ℕ} {A T A' T' : Tmpl} (h : instCode k A T = instCode k A' T') (a : PD.Action) :
    bitPlays k A T a ↔ bitPlays k A' T' a := by
  unfold bitPlays; rw [h]

/-! ### 4. The `coop` column: `instCode k T .coop` in its own frame -/

/-- A search node on a closed `TAct`-theorem guard: the then-branch, for all large `k`, as a bit. -/
theorem bit_search_found {A T : Tmpl} {φ : PD.Formula} {p q : ℕ} {a : PD.Action}
    (hc : ∀ k, instCode k A T = pSearch k (templateCode φ) p q)
    (hf : ∃ L : ℕ, ∀ k : ℕ, L ≤ k → ∀ me opp : PD.Prog,
      LenBox TAct k (guardCode (templateCode φ) (progCode me) (progCode opp)))
    (hp : ∀ x y : ℕ, EvalGraph 1 x y p (actCode a)) (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    bitEventually A T a := by
  obtain ⟨L, hL⟩ := hf
  refine ⟨L, fun k hk ↦ bitPlays_of_eq (hc k) ?_⟩
  have h := hL k (le_of_lt hk) (.bot (inst (tauZoo k) A T)) (.bot (inst (tauZoo k) A T))
  rw [progCode_bot_inst, hc k] at h
  exact ⟨_, search_then φ h (hp _ _) hφ⟩

/-- A search node on a guard never found: the else-branch, at every `k`, as a bit. -/
theorem bit_search_not_found {A T : Tmpl} {φ : PD.Formula} {p q : ℕ} {a : PD.Action} (k : ℕ)
    (hc : instCode k A T = pSearch k (templateCode φ) p q)
    (hn : ∀ me opp : PD.Prog, ¬ LenBox TAct k (guardCode (templateCode φ) (progCode me) (progCode opp)))
    (hq : ∀ x y, EvalGraph 1 x y q (actCode a)) (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    bitPlays k A T a := by
  refine bitPlays_of_eq hc ?_
  have h := hn (.bot (inst (tauZoo k) A T)) (.bot (inst (tauZoo k) A T))
  rw [progCode_bot_inst, hc] at h
  exact ⟨_, search_else φ h (hq _ _) hφ⟩

/-- `bit_search_found` on a STORED (budget-abstracted) template `templateCodeAt φ k`. -/
theorem bit_search_found_at {A T : Tmpl} {φ : PD.Formula} {p q : ℕ} {a : PD.Action}
    (hc : ∀ k, instCode k A T = pSearch k (templateCodeAt φ k) p q)
    (hf : ∃ L : ℕ, ∀ k : ℕ, L ≤ k → ∀ me opp : PD.Prog,
      LenBox TAct k (guardCode (templateCode φ) (progCode me) (progCode opp)))
    (hp : ∀ x y : ℕ, EvalGraph 1 x y p (actCode a)) (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    bitEventually A T a := by
  obtain ⟨L, hL⟩ := hf
  refine ⟨L, fun k hk ↦ bitPlays_of_eq (hc k) ?_⟩
  have h := hL k (le_of_lt hk) (.bot (inst (tauZoo k) A T)) (.bot (inst (tauZoo k) A T))
  rw [progCode_bot_inst, hc k] at h
  exact ⟨_, search_then_at φ h (hp _ _) hφ⟩

/-- `bit_search_not_found` on a STORED (budget-abstracted) template `templateCodeAt φ k`. -/
theorem bit_search_not_found_at {A T : Tmpl} {φ : PD.Formula} {p q : ℕ} {a : PD.Action} (k : ℕ)
    (hc : instCode k A T = pSearch k (templateCodeAt φ k) p q)
    (hn : ∀ me opp : PD.Prog, ¬ LenBox TAct k (guardCode (templateCode φ) (progCode me) (progCode opp)))
    (hq : ∀ x y, EvalGraph 1 x y q (actCode a)) (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    bitPlays k A T a := by
  refine bitPlays_of_eq hc ?_
  have h := hn (.bot (inst (tauZoo k) A T)) (.bot (inst (tauZoo k) A T))
  rw [progCode_bot_inst, hc] at h
  exact ⟨_, search_else_at φ h (hq _ _) hφ⟩

theorem col_coop_coop (k : ℕ) : bitPlays k .coop .coop .C :=
  bitPlays_of_eq (instCode_coop k _) ⟨_, const_play 0 _ _ _⟩

theorem col_defect_coop (k : ℕ) : bitPlays k .defect .coop .D :=
  bitPlays_of_eq (instCode_defect k _) ⟨_, const_play 0 _ _ _⟩

/-- τ(TFTSim) at the cooperator copies the cooperator: C. -/
theorem col_tftSim_coop (k : ℕ) : bitPlays k .tftSim .coop .C := by
  apply bitPlays_of_eq (instCode_tftSim k _)
  rw [instCode_coop]
  exact ⟨_, watch_fires (const_play 0 _ _ 0) (const_play 0 _ _ _)⟩

/-- τ(Dupoc) at the cooperator: the probe of the frozen cooperator is a `TAct`-theorem — POS, C. -/
theorem col_dupoc_coop : bitEventually .dupoc .coop .C :=
  bit_search_found instCode_dupoc_coop (probe_const_found .C) (fun _ _ ↦ const_play 0 _ _ _)

/-- τ(EBot) at the cooperator: its exploit watch sees the cooperator cooperate with the defector — D. -/
theorem col_ebot_coop (k : ℕ) : bitPlays k .ebot .coop .D := by
  apply bitPlays_of_eq (instCode_ebot k _)
  rw [instCode_coop, instCode_coop, instCode_coop]
  exact ⟨_, watch_fires (const_play 0 _ _ 0) (const_play 0 _ _ _)⟩

/-- τ(OBot) at the cooperator: neither defection watch fires — C. -/
theorem col_obot_coop (k : ℕ) : bitPlays k .obot .coop .C := by
  apply bitPlays_of_eq (instCode_obot k _)
  rw [instCode_coop, instCode_coop]
  exact ⟨_, watch_falls' (const_play 0 _ _ 0) (by decide) (watch_falls (const_play 0 _ _ 0) (by decide) (const_play 0 _ _ _))⟩

/-- τ(DBot) at the cooperator: the cooperator trusts the defector, the punisher fires — D. -/
theorem col_dbot_coop (k : ℕ) : bitPlays k .dbot .coop .D := by
  apply bitPlays_of_eq (instCode_dbot k _)
  rw [instCode_coop]
  exact ⟨_, watch_fires (const_play 0 _ _ 0) (const_play 0 _ _ _)⟩

/-- τ(CupodTroll) at the cooperator: the identity is decidably false — SND, C. -/
theorem col_cupodTroll_coop (k : ℕ) : bitPlays k .cupodTroll .coop .C :=
  bit_search_not_found k (instCode_cupodTroll k _ (by decide)) (fun me opp ↦ eq_const_not_found (by decide) me opp k)
    (fun _ _ ↦ const_play 0 _ _ _)

/-- τ(DupocTroll) (2026-10-19) at a hypothesis whose source is not Dupoc's: the identity is decidably false — SND, C,
at every budget. -/
theorem dupocTroll_C (k : ℕ) (T : Tmpl) (h : tmplSpec T ≠ tauDupocSpec) : bitPlays k .dupocTroll T .C :=
  bit_search_not_found k (instCode_dupocTroll k T h) (fun me opp ↦ eq_const_not_found (by decide) me opp k)
    (fun _ _ ↦ const_play 0 _ _ _)

/-- …and at a hypothesis with Dupoc's source the identity is a `TAct`-theorem: D for all large budgets. -/
theorem dupocTroll_rec_D (T : Tmpl) (h : tmplSpec T = tauDupocSpec) : bitEventually .dupocTroll T .D :=
  bit_search_found (fun k ↦ instCode_dupocTroll_rec k T h) (eq_const_found .C) (fun _ _ ↦ const_play 0 _ _ _)

theorem col_dupocTroll_coop (k : ℕ) : bitPlays k .dupocTroll .coop .C := dupocTroll_C k _ (by decide)

/-- τ(Cupod) at the cooperator: "the cooperator defects against itself" is false — SND, C. -/
theorem col_cupod_coop (k : ℕ) : bitPlays k .cupod .coop .C :=
  bit_search_not_found k (instCode_cupod_coop k) (fun me opp ↦ probe_const_not_found (by decide) me opp k)
    (fun _ _ ↦ const_play 0 _ _ _)

/-- τ(Prudent) at the cooperator: whatever the outer verdict, the prudence check "the cooperator defects
against itself" fails — D on both branches. -/
theorem col_prudent_coop (k : ℕ) : bitPlays k .prudent .coop .D := by
  apply bitPlays_of_eq (instCode_prudent_coop k)
  have hn := probe_const_not_found (a := .C) (b := .D) (by decide) (.bot (inst (tauZoo k) .prudent .coop))
    (.bot (inst (tauZoo k) .prudent .coop)) k
  rw [progCode_bot_inst, instCode_prudent_coop] at hn
  exact ⟨_, search_either (prC .C .C) (search_else (prC .C .D) hn (const_play 0 _ _ _)) (const_play 1 _ _ _)⟩

theorem col_maxconfidence_coop : bitEventually .maxconfidence .coop .C := by
  obtain ⟨k₂, h⟩ := col_dupoc_coop
  exact ⟨k₂, fun k hk ↦ (bitPlays_congr (instCode_maxconfidence_eq k .coop (by decide) (by decide) (by decide)) _).mpr (h k hk)⟩

theorem col_minconfidence_coop : bitEventually .minconfidence .coop .C := by
  obtain ⟨k₂, h⟩ := col_dupoc_coop
  exact ⟨k₂, fun k hk ↦ (bitPlays_congr (instCode_minconfidence_eq k .coop (by decide) (by decide) (by decide) (by decide)) _).mpr (h k hk)⟩

/-! ### 5. The `defect` column: `instCode k T .defect` in its own frame -/

theorem col_coop_defect (k : ℕ) : bitPlays k .coop .defect .C :=
  bitPlays_of_eq (instCode_coop k _) ⟨_, const_play 0 _ _ _⟩

theorem col_defect_defect (k : ℕ) : bitPlays k .defect .defect .D :=
  bitPlays_of_eq (instCode_defect k _) ⟨_, const_play 0 _ _ _⟩

/-- τ(TFTSim) at the defector copies the defector: D. -/
theorem col_tftSim_defect (k : ℕ) : bitPlays k .tftSim .defect .D := by
  apply bitPlays_of_eq (instCode_tftSim k _)
  rw [instCode_defect]
  exact ⟨_, watch_falls (const_play 0 _ _ 1) (by decide) (const_play 0 _ _ _)⟩

/-- τ(Dupoc) at the defector: "the defector cooperates with itself" is false — SND, D. -/
theorem col_dupoc_defect (k : ℕ) : bitPlays k .dupoc .defect .D :=
  bit_search_not_found k (instCode_dupoc_defect k) (fun me opp ↦ probe_const_not_found (by decide) me opp k)
    (fun _ _ ↦ const_play 0 _ _ _)

/-- τ(EBot) at the defector: all three watches fall — D. -/
theorem col_ebot_defect (k : ℕ) : bitPlays k .ebot .defect .D := by
  apply bitPlays_of_eq (instCode_ebot k _)
  rw [instCode_defect, instCode_defect, instCode_defect]
  exact ⟨_, watch_falls' (const_play 0 _ _ 1) (by decide)
    (watch_falls' (const_play 0 _ _ 1) (by decide) (watch_falls (const_play 0 _ _ 1) (by decide) (const_play 0 _ _ _)))⟩

/-- τ(OBot) at the defector: the first defection watch fires — D. -/
theorem col_obot_defect (k : ℕ) : bitPlays k .obot .defect .D := by
  apply bitPlays_of_eq (instCode_obot k _)
  rw [instCode_defect, instCode_defect]
  exact ⟨_, watch_fires (const_play 0 _ _ 1) (const_play 0 _ _ _)⟩

/-- τ(DBot) at the defector: the defector is no pushover — trust, C. -/
theorem col_dbot_defect (k : ℕ) : bitPlays k .dbot .defect .C := by
  apply bitPlays_of_eq (instCode_dbot k _)
  rw [instCode_defect]
  exact ⟨_, watch_falls (const_play 0 _ _ 1) (by decide) (const_play 0 _ _ _)⟩

/-- τ(CupodTroll) at the defector: the identity is decidably false — SND, C. -/
theorem col_cupodTroll_defect (k : ℕ) : bitPlays k .cupodTroll .defect .C :=
  bit_search_not_found k (instCode_cupodTroll k _ (by decide)) (fun me opp ↦ eq_const_not_found (by decide) me opp k)
    (fun _ _ ↦ const_play 0 _ _ _)

theorem col_dupocTroll_defect (k : ℕ) : bitPlays k .dupocTroll .defect .C := dupocTroll_C k _ (by decide)

/-- τ(Cupod) at the defector: "the defector defects against itself" is a `TAct`-theorem — POS, D. -/
theorem col_cupod_defect : bitEventually .cupod .defect .D :=
  bit_search_found instCode_cupod_defect (probe_const_found .D) (fun _ _ ↦ const_play 0 _ _ _)

/-- τ(Prudent) at the defector: the outer probe "the defector cooperates with itself" is false — SND, D. -/
theorem col_prudent_defect (k : ℕ) : bitPlays k .prudent .defect .D := by
  apply bitPlays_of_eq (instCode_prudent_defect k)
  have hn := probe_const_not_found (a := .D) (b := .C) (by decide) (.bot (inst (tauZoo k) .prudent .defect))
    (.bot (inst (tauZoo k) .prudent .defect)) k
  rw [progCode_bot_inst, instCode_prudent_defect] at hn
  exact ⟨_, search_else (prC .D .C) hn (const_play 1 _ _ _)⟩

/-- **τ(CIMCIC) at the defector is SELF-REFUTING** (`cimcic_selfref_not_found` on the instance): a proof of
"if I cooperate with the frozen defector, it cooperates with me" would make the instance cooperate with it,
so by soundness the defector would cooperate — against the fact. Never found, D. -/
theorem cimcic_defect_not_found (k : ℕ) :
    ¬ LenBox TAct k (guardOf (implC .D .C .C) (.bot (inst (tauZoo k) .cimcic .defect)) (.bot (inst (tauZoo k) .cimcic .defect))) := by
  intro hf
  set me : PD.Prog := .bot (inst (tauZoo k) .cimcic .defect) with hme_def
  have hme : ProperPlayer me := properPlayer_bot _
  have hme' : noSelfIdxP me = true := by
    rw [hme_def]
    show noSelfIdxP (.bot (.search k (implC .D .C .C) (.const .C) (.const .D))) = true
    rfl
  -- the same verdict in the probe frame `(me, .bot DefectBot)`
  have hf' : LenBox TAct k (guardOf (implC .D .C .C) me (.bot (.const .D))) := by
    rw [← guardOf_implConst_frame hme hme (properPlayer_bot _) hme' hme' rfl .D .C .C]
    exact hf
  -- so the instance cooperates with the frozen defector
  have hC : EvalGraph 3 (progCode me) (pBot (pConst 1)) (progCode me) 0 := by
    unfold guardOf at hf'
    rw [progCode_botConst] at hf'
    rw [hme_def, progCode_bot_inst] at hf' ⊢
    show EvalGraph (2 + 1) _ _ _ _
    rw [EvalGraph.bot_iff, instCode_cimcic_defect] at *
    exact search_then (implC .D .C .C) hf' (const_play 0 _ _ _)
  -- by soundness the guard is true in ℕ: the defector cooperates with the instance — against the fact
  have hT : ℕ↓[LAct] ⊧ sentenceAt me me (implC .D .C .C) := models_sentenceAt_of_lenBox hf
  rw [← sentenceAt_subst me me hme hme (implC .D .C .C) rfl] at hT
  change ℕ↓[LAct] ⊧ sentenceAt me me (.impl (.plays me (.bot (.const .D)) .C) (.plays (.bot (.const .D)) me .C)) at hT
  rw [models_sentenceAt_impl, models_sentenceAt_plays _ _ _ _ _ hme (properPlayer_bot _),
    models_sentenceAt_plays _ _ _ _ _ (properPlayer_bot _) hme, progCode_botConst] at hT
  obtain ⟨N', hN'⟩ := hT ⟨3, hC⟩
  exact absurd (EvalGraph.unique' hN' (bot_const_play 0 _ _ _)) (by decide)

theorem col_cimcic_defect (k : ℕ) : bitPlays k .cimcic .defect .D := by
  apply bitPlays_of_eq (instCode_cimcic_defect k)
  have hn := cimcic_defect_not_found k
  unfold guardOf at hn
  rw [progCode_bot_inst, instCode_cimcic_defect] at hn
  exact ⟨_, search_else (implC .D .C .C) hn (const_play 0 _ _ _)⟩

/-- τ(CIMCIC) at the cooperator PLAYS (some action): a search node always commits (`search_either`'s
case split). Its value, C, is `col_cimcic_coop` (Phase 3b); the totality already decides τ(OBot)'s slot. -/
theorem col_cimcic_coop_total (k : ℕ) : ∃ r, bitPlays k .cimcic .coop r := by
  by_cases hg : LenBox TAct k (guardCode (templateCode (implC .C .C .C)) (pBot (instCode k .cimcic .coop)) (pBot (instCode k .cimcic .coop)))
  · refine ⟨.C, bitPlays_of_eq (instCode_cimcic_coop k) ?_⟩
    rw [instCode_cimcic_coop] at hg
    exact ⟨_, search_then (implC .C .C .C) hg (const_play 0 _ _ _)⟩
  · refine ⟨.D, bitPlays_of_eq (instCode_cimcic_coop k) ?_⟩
    rw [instCode_cimcic_coop] at hg
    exact ⟨_, search_else (implC .C .C .C) hg (const_play 0 _ _ _)⟩

/-- τ(DIMCID) at the cooperator PLAYS (some action); its value, D (the FLIP), is `col_dimcid_coop` (Phase 3b). -/
theorem col_dimcid_coop_total (k : ℕ) : ∃ r, bitPlays k .dimcid .coop r := by
  by_cases hg : LenBox TAct k (guardCode (templateCode (implC .C .C .D)) (pBot (instCode k .dimcid .coop)) (pBot (instCode k .dimcid .coop)))
  · refine ⟨.D, bitPlays_of_eq (instCode_dimcid_coop k) ?_⟩
    rw [instCode_dimcid_coop] at hg
    exact ⟨_, search_then (implC .C .C .D) hg (const_play 0 _ _ _)⟩
  · refine ⟨.C, bitPlays_of_eq (instCode_dimcid_coop k) ?_⟩
    rw [instCode_dimcid_coop] at hg
    exact ⟨_, search_else (implC .C .C .D) hg (const_play 0 _ _ _)⟩

theorem col_maxconfidence_defect (k : ℕ) : bitPlays k .maxconfidence .defect .D :=
  (bitPlays_congr (instCode_maxconfidence_eq k .defect (by decide) (by decide) (by decide)) _).mpr (col_dupoc_defect k)

theorem col_minconfidence_defect (k : ℕ) : bitPlays k .minconfidence .defect .D :=
  (bitPlays_congr (instCode_minconfidence_eq k .defect (by decide) (by decide) (by decide) (by decide)) _).mpr
    (col_dupoc_defect k)

/-! ### 6. The `mirror` column, where τ(EBot)'s third watch needs it -/

theorem col_defect_mirror (k : ℕ) : bitPlays k .defect .mirror .D :=
  bitPlays_of_eq (instCode_defect k _) ⟨_, const_play 0 _ _ _⟩

/-- τ(Mirror) at a constant copies it. -/
theorem col_mirror_coop (k : ℕ) : bitPlays k .mirror .coop .C :=
  bitPlays_of_eq (instCode_mirror_coop k) ⟨_, sim_bot_plays (const_play 0 _ _ _)⟩

theorem col_mirror_defect (k : ℕ) : bitPlays k .mirror .defect .D :=
  bitPlays_of_eq (instCode_mirror_defect k) ⟨_, sim_bot_plays (const_play 0 _ _ _)⟩

/-- τ(EBot) at the mirror: the exploit watch falls (the mirror defects against the defector), the reciprocity
watch fires (it cooperates with the cooperator) — C. -/
theorem col_ebot_mirror (k : ℕ) : bitPlays k .ebot .mirror .C := by
  apply bitPlays_of_eq (instCode_ebot k _)
  obtain ⟨n₁, h₁⟩ := col_mirror_defect k
  obtain ⟨n₂, h₂⟩ := col_mirror_coop k
  exact ⟨_, watch_falls' h₁ (by decide) (watch_fires' h₂ (const_play 0 _ _ _))⟩

end ArithS.Tau
