import ArithS.Tau.Columns
import ArithS.Bridge.Agent
import ArithS.Eval.TauCheck

/-!
# ArithS.Tau.Entangled.Base — the entangled systems on codes, at ℕ (Phase 3, the entangled bits)

An ENTANGLED pair `(A, T)` (both self-probers, `A ≠ T`) compiles to the two-member system
`.sys [sysGo 1 A T (spec A), sysGo 0 T A (spec T)] 0` (`Tau/Spec.lean`): member `0` is `A` probing its
partner through the pronoun `.bot (.selfIdx 1)`, member `1` is `T` probing `.bot (.selfIdx 0)`. This module
is the ℕ-level kit every entangled bit rests on:

* the five member shapes the seven self-probers emit (`dm`, `cm`, `cim`, `dim`, `pm`) and the mirror member
  `mm` (τ(EBot)'s third watch at a self-probing hypothesis), the two-member list `sys2`, and the compiled
  instances of the 44 in-scope pairs as `.sys (sys2 m₀ m₁) 0` — all by `rfl` (Gate D1);
* **`bitPlays_of_member`**: a bit is the self-play of the bot-wrapped system, which `EvalGraph.sys_iff` turns
  into a run of the CLOSED member `0` (`progCode_sysClose_member`: the engine's `sysClose`, on codes);
* the closed members spelled out (`dm_sysClose`, …) — searchers on guards that name the partner
  `.bot (.sys defs j)` by its closed code — and the search clauses on them (`member_then`, `member_else`);
* the truth equations at ℕ of the two atom shapes a closed member guard carries: the closed probe
  "`.bot (.sys defs j)` plays `a` against itself" (`models_sentenceAt_plays`) and the `.self` atoms of the
  `.impl` guards, "me plays `a` against the partner" / "the partner plays `b` against me"
  (`models_plays_self_closed`, `models_plays_closed_self` — the ℕ twins of `Tau/Described.lean`'s
  `eval_template_plays_self_closed_V`).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open PD PD.Tau

/-! ### 1. The member shapes and the systems -/

/-- Dupoc's member: "the partner (`.selfIdx j`), bot-wrapped, plays C against itself" ⇒ C else D. -/
def dm (j k : ℕ) : Prog := .search k (.plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) .C) (.const .C) (.const .D)
/-- Cupod's member: "the partner plays D against itself" ⇒ D else C. -/
def cm (j k : ℕ) : Prog := .search k (.plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) .D) (.const .D) (.const .C)
/-- CIMCIC's member: "if I play C against the partner, it plays C against me" ⇒ C else D. -/
def cim (j k : ℕ) : Prog :=
  .search k (.impl (.plays .self (.bot (.selfIdx j)) .C) (.plays (.bot (.selfIdx j)) .self .C)) (.const .C) (.const .D)
/-- DIMCID's member: "if I play C against the partner, it plays D against me" ⇒ D else C. -/
def dim (j k : ℕ) : Prog :=
  .search k (.impl (.plays .self (.bot (.selfIdx j)) .C) (.plays (.bot (.selfIdx j)) .self .D)) (.const .D) (.const .C)
/-- Prudent's member at the hypothesis `H`: the partner's self-cooperation, then the prudence check on `H`'s
instance at the defector (a FROZEN third party, `k` inside unless `H = .mirror`). -/
def pm (j k : ℕ) (H : Tmpl) : Prog :=
  .search k (.plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) .C)
    (.search k (.plays (.bot (inst (tauZoo k) H .defect)) (.bot (inst (tauZoo k) H .defect)) .D) (.const .C) (.const .D))
    (.const .D)
/-- Mirror's member: run the partner against itself and copy. -/
def mm (j : ℕ) : Prog := .sim (.bot (.selfIdx j)) (.bot (.selfIdx j))

/-- The two-member list. -/
def sys2 (m₀ m₁ : Prog) : ProgList := .cons m₀ (.cons m₁ .nil)

/-! #### The compiled instances (Gate D1: every equation is `rfl`) -/

theorem inst_dupoc_cupod (k : ℕ) : inst (tauZoo k) .dupoc .cupod = .sys (sys2 (dm 1 k) (cm 0 k)) 0 := rfl
theorem inst_cupod_dupoc (k : ℕ) : inst (tauZoo k) .cupod .dupoc = .sys (sys2 (cm 1 k) (dm 0 k)) 0 := rfl
theorem inst_dupoc_cimcic (k : ℕ) : inst (tauZoo k) .dupoc .cimcic = .sys (sys2 (dm 1 k) (cim 0 k)) 0 := rfl
theorem inst_cimcic_dupoc (k : ℕ) : inst (tauZoo k) .cimcic .dupoc = .sys (sys2 (cim 1 k) (dm 0 k)) 0 := rfl
theorem inst_dupoc_dimcid (k : ℕ) : inst (tauZoo k) .dupoc .dimcid = .sys (sys2 (dm 1 k) (dim 0 k)) 0 := rfl
theorem inst_dimcid_dupoc (k : ℕ) : inst (tauZoo k) .dimcid .dupoc = .sys (sys2 (dim 1 k) (dm 0 k)) 0 := rfl
theorem inst_dupoc_prudent (k : ℕ) : inst (tauZoo k) .dupoc .prudent = .sys (sys2 (dm 1 k) (pm 0 k .dupoc)) 0 := rfl
theorem inst_prudent_dupoc (k : ℕ) : inst (tauZoo k) .prudent .dupoc = .sys (sys2 (pm 1 k .dupoc) (dm 0 k)) 0 := rfl
theorem inst_cupod_cimcic (k : ℕ) : inst (tauZoo k) .cupod .cimcic = .sys (sys2 (cm 1 k) (cim 0 k)) 0 := rfl
theorem inst_cimcic_cupod (k : ℕ) : inst (tauZoo k) .cimcic .cupod = .sys (sys2 (cim 1 k) (cm 0 k)) 0 := rfl
theorem inst_cupod_dimcid (k : ℕ) : inst (tauZoo k) .cupod .dimcid = .sys (sys2 (cm 1 k) (dim 0 k)) 0 := rfl
theorem inst_dimcid_cupod (k : ℕ) : inst (tauZoo k) .dimcid .cupod = .sys (sys2 (dim 1 k) (cm 0 k)) 0 := rfl
theorem inst_cupod_prudent (k : ℕ) : inst (tauZoo k) .cupod .prudent = .sys (sys2 (cm 1 k) (pm 0 k .cupod)) 0 := rfl
theorem inst_prudent_cupod (k : ℕ) : inst (tauZoo k) .prudent .cupod = .sys (sys2 (pm 1 k .cupod) (cm 0 k)) 0 := rfl
theorem inst_cimcic_dimcid (k : ℕ) : inst (tauZoo k) .cimcic .dimcid = .sys (sys2 (cim 1 k) (dim 0 k)) 0 := rfl
theorem inst_dimcid_cimcic (k : ℕ) : inst (tauZoo k) .dimcid .cimcic = .sys (sys2 (dim 1 k) (cim 0 k)) 0 := rfl
theorem inst_cimcic_prudent (k : ℕ) : inst (tauZoo k) .cimcic .prudent = .sys (sys2 (cim 1 k) (pm 0 k .cimcic)) 0 := rfl
theorem inst_prudent_cimcic (k : ℕ) : inst (tauZoo k) .prudent .cimcic = .sys (sys2 (pm 1 k .cimcic) (cim 0 k)) 0 := rfl
theorem inst_dimcid_prudent (k : ℕ) : inst (tauZoo k) .dimcid .prudent = .sys (sys2 (dim 1 k) (pm 0 k .dimcid)) 0 := rfl
theorem inst_prudent_dimcid (k : ℕ) : inst (tauZoo k) .prudent .dimcid = .sys (sys2 (pm 1 k .dimcid) (dim 0 k)) 0 := rfl

/-- The symmetric Dupoc-spec system (`cfdSys`): the SAME term in all six native orientations. -/
theorem inst_maxconfidence_dupoc (k : ℕ) : inst (tauZoo k) .maxconfidence .dupoc = .sys (sys2 (dm 1 k) (dm 0 k)) 0 := rfl
theorem inst_dupoc_maxconfidence (k : ℕ) : inst (tauZoo k) .dupoc .maxconfidence = .sys (sys2 (dm 1 k) (dm 0 k)) 0 := rfl
theorem inst_minconfidence_dupoc (k : ℕ) : inst (tauZoo k) .minconfidence .dupoc = .sys (sys2 (dm 1 k) (dm 0 k)) 0 := rfl
theorem inst_dupoc_minconfidence (k : ℕ) : inst (tauZoo k) .dupoc .minconfidence = .sys (sys2 (dm 1 k) (dm 0 k)) 0 := rfl
theorem inst_maxconfidence_minconfidence (k : ℕ) :
    inst (tauZoo k) .maxconfidence .minconfidence = .sys (sys2 (dm 1 k) (dm 0 k)) 0 := rfl
theorem inst_minconfidence_maxconfidence (k : ℕ) :
    inst (tauZoo k) .minconfidence .maxconfidence = .sys (sys2 (dm 1 k) (dm 0 k)) 0 := rfl
theorem sys2_dm_eq_cfdSys (k : ℕ) : sys2 (dm 1 k) (dm 0 k) = cfdSys k := rfl

/-- The natives in the ROW role are Dupoc's systems (Dupoc's spec, `rfl`). -/
theorem inst_maxconfidence_cupod (k : ℕ) : inst (tauZoo k) .maxconfidence .cupod = .sys (sys2 (dm 1 k) (cm 0 k)) 0 := rfl
theorem inst_minconfidence_cupod (k : ℕ) : inst (tauZoo k) .minconfidence .cupod = .sys (sys2 (dm 1 k) (cm 0 k)) 0 := rfl
theorem inst_maxconfidence_cimcic (k : ℕ) : inst (tauZoo k) .maxconfidence .cimcic = .sys (sys2 (dm 1 k) (cim 0 k)) 0 := rfl
theorem inst_minconfidence_cimcic (k : ℕ) : inst (tauZoo k) .minconfidence .cimcic = .sys (sys2 (dm 1 k) (cim 0 k)) 0 := rfl
theorem inst_maxconfidence_dimcid (k : ℕ) : inst (tauZoo k) .maxconfidence .dimcid = .sys (sys2 (dm 1 k) (dim 0 k)) 0 := rfl
theorem inst_minconfidence_dimcid (k : ℕ) : inst (tauZoo k) .minconfidence .dimcid = .sys (sys2 (dm 1 k) (dim 0 k)) 0 := rfl
theorem inst_maxconfidence_prudent (k : ℕ) :
    inst (tauZoo k) .maxconfidence .prudent = .sys (sys2 (dm 1 k) (pm 0 k .maxconfidence)) 0 := rfl
theorem inst_minconfidence_prudent (k : ℕ) :
    inst (tauZoo k) .minconfidence .prudent = .sys (sys2 (dm 1 k) (pm 0 k .minconfidence)) 0 := rfl
/-- …and in the HYPOTHESIS role too: the partner's third-party probes name `inst native .defect = inst dupoc .defect`. -/
theorem inst_cupod_maxconfidence (k : ℕ) : inst (tauZoo k) .cupod .maxconfidence = .sys (sys2 (cm 1 k) (dm 0 k)) 0 := rfl
theorem inst_cupod_minconfidence (k : ℕ) : inst (tauZoo k) .cupod .minconfidence = .sys (sys2 (cm 1 k) (dm 0 k)) 0 := rfl
theorem inst_cimcic_maxconfidence (k : ℕ) : inst (tauZoo k) .cimcic .maxconfidence = .sys (sys2 (cim 1 k) (dm 0 k)) 0 := rfl
theorem inst_cimcic_minconfidence (k : ℕ) : inst (tauZoo k) .cimcic .minconfidence = .sys (sys2 (cim 1 k) (dm 0 k)) 0 := rfl
theorem inst_dimcid_maxconfidence (k : ℕ) : inst (tauZoo k) .dimcid .maxconfidence = .sys (sys2 (dim 1 k) (dm 0 k)) 0 := rfl
theorem inst_dimcid_minconfidence (k : ℕ) : inst (tauZoo k) .dimcid .minconfidence = .sys (sys2 (dim 1 k) (dm 0 k)) 0 := rfl
theorem inst_prudent_maxconfidence (k : ℕ) :
    inst (tauZoo k) .prudent .maxconfidence = .sys (sys2 (pm 1 k .maxconfidence) (dm 0 k)) 0 := rfl
theorem inst_prudent_minconfidence (k : ℕ) :
    inst (tauZoo k) .prudent .minconfidence = .sys (sys2 (pm 1 k .minconfidence) (dm 0 k)) 0 := rfl
/-- The prudence probes of the natives are Dupoc's. -/
theorem pm_maxconfidence (j k : ℕ) : pm j k .maxconfidence = pm j k .dupoc := rfl
theorem pm_minconfidence (j k : ℕ) : pm j k .minconfidence = pm j k .dupoc := rfl

/-- τ(EBot)'s third watch at a self-probing hypothesis: the hypothesis entangled with the mirror. -/
theorem inst_dimcid_mirror (k : ℕ) : inst (tauZoo k) .dimcid .mirror = .sys (sys2 (dim 1 k) (mm 0)) 0 := rfl
theorem inst_prudent_mirror (k : ℕ) : inst (tauZoo k) .prudent .mirror = .sys (sys2 (pm 1 k .mirror) (mm 0)) 0 := rfl

/-! ### 2. A bit is a run of the closed member `0` -/

/-- The members are compiled members (`memberP`): their guards are member guards. -/
theorem memberP_dm (j k : ℕ) (hj : j ≤ 1) : memberP (dm j k) = true := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl <;> rfl
theorem memberP_cm (j k : ℕ) (hj : j ≤ 1) : memberP (cm j k) = true := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl <;> rfl
theorem memberP_cim (j k : ℕ) (hj : j ≤ 1) : memberP (cim j k) = true := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl <;> rfl
theorem memberP_dim (j k : ℕ) (hj : j ≤ 1) : memberP (dim j k) = true := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl <;> rfl
theorem memberP_mm (j : ℕ) : memberP (mm j) = true := rfl

/-- Prudent's member is a compiled member: the inner probe is a closed, pronoun-free third party. -/
theorem memberP_pm (j k : ℕ) (hj : j ≤ 1) (H : Tmpl) : memberP (pm j k H) = true := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl <;> cases H <;> rfl

/-- The code of a two-member system. -/
theorem progCode_sys2 (m₀ m₁ : Prog) (i : ℕ) :
    progCode (.sys (sys2 m₀ m₁) i) = pSys (pCons (progCode m₀) (pCons (progCode m₁) pNil)) i := by
  simp [sys2]

/-- **A bit from a run of the closed member `0`**: the self-play of the bot-wrapped system `.sys defs 0`
unfolds (`sys_iff`) to the closed member `m₀.sysClose defs` in the same frame. -/
theorem bitPlays_of_member {k : ℕ} {A T : Tmpl} {m₀ m₁ : Prog} (h : inst (tauZoo k) A T = .sys (sys2 m₀ m₁) 0)
    (hm : memberP m₀ = true) {a : Action} {N : ℕ}
    (hr : EvalGraph N (pBot (progCode (.sys (sys2 m₀ m₁) 0))) (pBot (progCode (.sys (sys2 m₀ m₁) 0)))
      (progCode (m₀.sysClose (sys2 m₀ m₁))) (actCode a)) :
    bitPlays k A T a := by
  refine bitPlays_of_eq (by unfold instCode; rw [h]) ⟨N + 1, ?_⟩
  rw [progCode_sys, EvalGraph.sys_iff]
  refine ⟨progCode m₀, listGet_progListCode_some _ 0 _ rfl, ?_⟩
  rw [← progCode_sysClose_member _ _ hm]
  exact hr

/-- The frame of a bit: the bot-wrapped system on both sides. -/
abbrev sysFrame (m₀ m₁ : Prog) : Prog := .bot (.sys (sys2 m₀ m₁) 0)

/-- The partner-probe, closed: member `j` of the system, bot-wrapped. -/
abbrev partner (m₀ m₁ : Prog) (j : ℕ) : Prog := .bot (.sys (sys2 m₀ m₁) j)

lemma progCode_sysFrame (m₀ m₁ : Prog) : progCode (sysFrame m₀ m₁) = pBot (progCode (.sys (sys2 m₀ m₁) 0)) := by
  simp

/-! ### 3. The closed members -/

theorem dm_sysClose (j k : ℕ) (defs : ProgList) :
    (dm j k).sysClose defs = .search k (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) .C) (.const .C) (.const .D) := rfl
theorem cm_sysClose (j k : ℕ) (defs : ProgList) :
    (cm j k).sysClose defs = .search k (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) .D) (.const .D) (.const .C) := rfl
theorem cim_sysClose (j k : ℕ) (defs : ProgList) :
    (cim j k).sysClose defs =
      .search k (.impl (.plays .self (.bot (.sys defs j)) .C) (.plays (.bot (.sys defs j)) .self .C)) (.const .C) (.const .D) := rfl
theorem dim_sysClose (j k : ℕ) (defs : ProgList) :
    (dim j k).sysClose defs =
      .search k (.impl (.plays .self (.bot (.sys defs j)) .C) (.plays (.bot (.sys defs j)) .self .D)) (.const .D) (.const .C) := rfl
theorem mm_sysClose (j : ℕ) (defs : ProgList) : (mm j).sysClose defs = .sim (.bot (.sys defs j)) (.bot (.sys defs j)) := rfl

/-- Prudent's closed member: the inner probe is pronoun-free, so the closer fixes it (`noSelfIdxP`). -/
theorem pm_sysClose (j k : ℕ) (H : Tmpl) (defs : ProgList) :
    (pm j k H).sysClose defs =
      .search k (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) .C)
        (.search k (.plays (.bot (inst (tauZoo k) H .defect)) (.bot (inst (tauZoo k) H .defect)) .D) (.const .C) (.const .D))
        (.const .D) := by
  have hI : (inst (tauZoo k) H .defect).sysClose defs = inst (tauZoo k) H .defect := by cases H <;> rfl
  simp only [pm, Prog.sysClose, Formula.sysClose, hI]

/-! ### 4. The search clauses on a closed member, in the bit's frame -/

/-- The then-branch of a closed member whose guard is found in the frame `(x, y)`. -/
theorem member_then {k n a x y : ℕ} (φ : Formula) {p q : Prog}
    (hf : LenBox TAct k (guardCode (templateCode φ) x y)) (h : EvalGraph n x y (progCode p) a)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    EvalGraph (n + 1) x y (progCode (.search k φ p q)) a := by
  rw [progCode_search]; exact search_then_at φ hf h

theorem member_else {k n a x y : ℕ} (φ : Formula) {p q : Prog}
    (hn : ¬ LenBox TAct k (guardCode (templateCode φ) x y)) (h : EvalGraph n x y (progCode q) a)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    EvalGraph (n + 1) x y (progCode (.search k φ p q)) a := by
  rw [progCode_search]; exact search_else_at φ hn h

/-! ### 5. The truth equations at ℕ of the closed-member atoms -/

/-- The `.plays .self q a` atom of `template` for a closed `q`, at ℕ (the twin of
`Tau/Described.lean`'s `eval_template_plays_self_closed_V`). -/
lemma eval_template_plays_self_closed_nat (q : Prog) (hq1 : q ≠ .self) (hq2 : q ≠ .opp) (a : Action) (b : Fin 6 → ℕ) :
    Semiformula.Eval (s := stdReadingNat) b Empty.elim (template (.plays .self q a)) ↔
      ∃ n, EvalGraph n (revalue (b 1) (b 2) (b 0)) (progCode q) (revalue (b 1) (b 2) (b 0)) (actCode a) := by
  rw [template_plays]
  unfold progGraph
  rw [progAux_self, progAux_of_ne hq1 hq2]
  unfold descF
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc, eval_evalG, eval_closedDesc,
    stdReadingNat_rel_eq, Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl, val_actT]
  constructor
  · rintro ⟨x, y, N, ⟨d, rfl, rfl⟩, rfl, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, ⟨_, rfl, rfl⟩, rfl, h⟩

/-- The `.plays p .self a` atom of `template` for a closed `p`, at ℕ. -/
lemma eval_template_plays_closed_self_nat (p : Prog) (hp1 : p ≠ .self) (hp2 : p ≠ .opp) (a : Action) (b : Fin 6 → ℕ) :
    Semiformula.Eval (s := stdReadingNat) b Empty.elim (template (.plays p .self a)) ↔
      ∃ n, EvalGraph n (progCode p) (revalue (b 1) (b 2) (b 0)) (progCode p) (actCode a) := by
  rw [template_plays]
  unfold progGraph
  rw [progAux_of_ne hp1 hp2, progAux_self]
  unfold descF
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc, eval_evalG, eval_closedDesc,
    stdReadingNat_rel_eq, Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl, val_actT]
  constructor
  · rintro ⟨x, y, N, rfl, ⟨d, rfl, rfl⟩, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, rfl, ⟨_, rfl, rfl⟩, h⟩

/-- The me-triple of `descriptionTerms` reconstructs the frame player. -/
lemma revalue_descriptionTerms_me (me opp : ℕ) :
    revalue ((descriptionTerms me opp 1).val (s := stdReadingNat) ![] Empty.elim)
      ((descriptionTerms me opp 2).val (s := stdReadingNat) ![] Empty.elim)
      ((descriptionTerms me opp 0).val (s := stdReadingNat) ![] Empty.elim) = me := by
  simp only [descriptionTerms, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, val_canonicalMeta]
  exact revalue_val_desc me

/-- **"Me plays `a` against the closed `q`" at ℕ**: the frame player `me` plays `a` against `q`. -/
theorem models_plays_self_closed (me opp q : Prog) (hq1 : q ≠ .self) (hq2 : q ≠ .opp) (a : Action) :
    ℕ↓[LAct] ⊧ sentenceAt me opp (.plays .self q a) ↔
      ∃ N, EvalGraph N (progCode me) (progCode q) (progCode me) (actCode a) := by
  rw [models_iff]
  unfold sentenceAt Semiformula.Realize
  rw [Semiformula.eval_substs, eval_template_plays_self_closed_nat q hq1 hq2]
  simp only [Function.comp_def]
  rw [revalue_descriptionTerms_me]

/-- **"The closed `p` plays `a` against me" at ℕ.** -/
theorem models_plays_closed_self (me opp p : Prog) (hp1 : p ≠ .self) (hp2 : p ≠ .opp) (a : Action) :
    ℕ↓[LAct] ⊧ sentenceAt me opp (.plays p .self a) ↔
      ∃ N, EvalGraph N (progCode p) (progCode me) (progCode p) (actCode a) := by
  rw [models_iff]
  unfold sentenceAt Semiformula.Realize
  rw [Semiformula.eval_substs, eval_template_plays_closed_self_nat p hp1 hp2]
  simp only [Function.comp_def]
  rw [revalue_descriptionTerms_me]

/-- The closed probe of a partner: "`.bot (.sys defs j)` plays `a` against itself". -/
theorem models_partner_probe (me opp : Prog) (defs : ProgList) (j : ℕ) (a : Action) :
    ℕ↓[LAct] ⊧ sentenceAt me opp (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) a) ↔
      ∃ N, EvalGraph N (pBot (progCode (.sys defs j))) (pBot (progCode (.sys defs j))) (pBot (progCode (.sys defs j))) (actCode a) := by
  rw [models_sentenceAt_plays me opp _ _ a (properPlayer_bot _) (properPlayer_bot _), progCode_bot]

/-- A play atom about a frame is decided by uniqueness: `b ≠ a` and a run to `b` refute "plays `a`". -/
theorem not_exists_evalGraph_of_ne {x y p : ℕ} {a b : Action} (hab : b ≠ a) {N : ℕ}
    (h : EvalGraph N x y p (actCode b)) : ¬ ∃ N', EvalGraph N' x y p (actCode a) := by
  rintro ⟨N', h'⟩
  exact hab (actCode_inj (EvalGraph.unique' h h'))

/-- The guard a closed member consults in the frame `(me, opp)`, as `guardOf`. -/
lemma guardOf_eq (φ : Formula) (me opp : Prog) :
    guardCode (templateCode φ) (progCode me) (progCode opp) = guardOf φ me opp := rfl

end ArithS.Tau

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open LAct
open PD PD.Tau

/-! ### 6. Floor bits on a system: the hinge is the box the member's own search consults -/

/-- A hinge stated on the instance code (`□[k] (guardCodeB (templateCode φ) (pBot (instCode k A T)) … k)`, the
convention of `Tau/Rows/*.lean`) is the box of the closed guard in the system's frame. -/
theorem not_found_of_not_hinge {k : ℕ} {A T : Tmpl} {m₀ m₁ : Prog} (h : inst (tauZoo k) A T = .sys (sys2 m₀ m₁) 0)
    (φ : Formula)
    (hn : ¬ □[k] (guardCodeB (templateCode φ) (pBot (instCode k A T)) (pBot (instCode k A T)) k))
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    ¬ LenBox TAct k (guardCode (templateCode φ) (progCode (sysFrame m₀ m₁)) (progCode (sysFrame m₀ m₁))) := by
  rwa [guardCodeB_of_template (isSemiformula_templateCode φ), ← progCode_bot_inst, h] at hn

theorem found_of_hinge {k : ℕ} {A T : Tmpl} {m₀ m₁ : Prog} (h : inst (tauZoo k) A T = .sys (sys2 m₀ m₁) 0)
    (φ : Formula)
    (hf : □[k] (guardCodeB (templateCode φ) (pBot (instCode k A T)) (pBot (instCode k A T)) k))
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    LenBox TAct k (guardCode (templateCode φ) (progCode (sysFrame m₀ m₁)) (progCode (sysFrame m₀ m₁))) := by
  rwa [guardCodeB_of_template (isSemiformula_templateCode φ), ← progCode_bot_inst, h] at hf

/-- The else-play of a Dupoc-shaped member `0` (then `C`, else `D`), when its probe is not found. -/
theorem bit_D_of_dm_else {k : ℕ} {A T : Tmpl} {m₁ : Prog} (h : inst (tauZoo k) A T = .sys (sys2 (dm 1 k) m₁) 0)
    (hn : ¬ LenBox TAct k (guardCode (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) m₁) 1)) (.bot (.sys (sys2 (dm 1 k) m₁) 1)) .C))
      (progCode (sysFrame (dm 1 k) m₁)) (progCode (sysFrame (dm 1 k) m₁)))) :
    bitPlays k A T .D :=
  bitPlays_of_member h (memberP_dm 1 k (by decide))
    (by rw [dm_sysClose]; exact member_else _ hn (const_play 0 _ _ _))

/-- The then-play of a Dupoc-shaped member `0`. -/
theorem bit_C_of_dm_then {k : ℕ} {A T : Tmpl} {m₁ : Prog} (h : inst (tauZoo k) A T = .sys (sys2 (dm 1 k) m₁) 0)
    (hf : LenBox TAct k (guardCode (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) m₁) 1)) (.bot (.sys (sys2 (dm 1 k) m₁) 1)) .C))
      (progCode (sysFrame (dm 1 k) m₁)) (progCode (sysFrame (dm 1 k) m₁)))) :
    bitPlays k A T .C :=
  bitPlays_of_member h (memberP_dm 1 k (by decide))
    (by rw [dm_sysClose]; exact member_then _ hf (const_play 0 _ _ _))

/-- The else-play of a Cupod-shaped member `0` (then `D`, else `C`). -/
theorem bit_C_of_cm_else {k : ℕ} {A T : Tmpl} {m₁ : Prog} (h : inst (tauZoo k) A T = .sys (sys2 (cm 1 k) m₁) 0)
    (hn : ¬ LenBox TAct k (guardCode (templateCode (.plays (.bot (.sys (sys2 (cm 1 k) m₁) 1)) (.bot (.sys (sys2 (cm 1 k) m₁) 1)) .D))
      (progCode (sysFrame (cm 1 k) m₁)) (progCode (sysFrame (cm 1 k) m₁)))) :
    bitPlays k A T .C :=
  bitPlays_of_member h (memberP_cm 1 k (by decide))
    (by rw [cm_sysClose]; exact member_else _ hn (const_play 0 _ _ _))

theorem bit_D_of_cm_then {k : ℕ} {A T : Tmpl} {m₁ : Prog} (h : inst (tauZoo k) A T = .sys (sys2 (cm 1 k) m₁) 0)
    (hf : LenBox TAct k (guardCode (templateCode (.plays (.bot (.sys (sys2 (cm 1 k) m₁) 1)) (.bot (.sys (sys2 (cm 1 k) m₁) 1)) .D))
      (progCode (sysFrame (cm 1 k) m₁)) (progCode (sysFrame (cm 1 k) m₁)))) :
    bitPlays k A T .D :=
  bitPlays_of_member h (memberP_cm 1 k (by decide))
    (by rw [cm_sysClose]; exact member_then _ hf (const_play 0 _ _ _))

/-- The else-play of a CIMCIC-shaped member `0` (then `C`, else `D`). -/
theorem bit_D_of_cim_else {k : ℕ} {A T : Tmpl} {m₁ : Prog} (h : inst (tauZoo k) A T = .sys (sys2 (cim 1 k) m₁) 0)
    (hn : ¬ LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot (.sys (sys2 (cim 1 k) m₁) 1)) .C)
      (.plays (.bot (.sys (sys2 (cim 1 k) m₁) 1)) .self .C)))
      (progCode (sysFrame (cim 1 k) m₁)) (progCode (sysFrame (cim 1 k) m₁)))) :
    bitPlays k A T .D :=
  bitPlays_of_member h (memberP_cim 1 k (by decide))
    (by rw [cim_sysClose]; exact member_else _ hn (const_play 0 _ _ _))

theorem bit_C_of_cim_then {k : ℕ} {A T : Tmpl} {m₁ : Prog} (h : inst (tauZoo k) A T = .sys (sys2 (cim 1 k) m₁) 0)
    (hf : LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot (.sys (sys2 (cim 1 k) m₁) 1)) .C)
      (.plays (.bot (.sys (sys2 (cim 1 k) m₁) 1)) .self .C)))
      (progCode (sysFrame (cim 1 k) m₁)) (progCode (sysFrame (cim 1 k) m₁)))) :
    bitPlays k A T .C :=
  bitPlays_of_member h (memberP_cim 1 k (by decide))
    (by rw [cim_sysClose]; exact member_then _ hf (const_play 0 _ _ _))

/-- The then-play of a DIMCID-shaped member `0` (then `D`, else `C`). -/
theorem bit_D_of_dim_then {k : ℕ} {A T : Tmpl} {m₁ : Prog} (h : inst (tauZoo k) A T = .sys (sys2 (dim 1 k) m₁) 0)
    (hf : LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot (.sys (sys2 (dim 1 k) m₁) 1)) .C)
      (.plays (.bot (.sys (sys2 (dim 1 k) m₁) 1)) .self .D)))
      (progCode (sysFrame (dim 1 k) m₁)) (progCode (sysFrame (dim 1 k) m₁)))) :
    bitPlays k A T .D :=
  bitPlays_of_member h (memberP_dim 1 k (by decide))
    (by rw [dim_sysClose]; exact member_then _ hf (const_play 0 _ _ _))

/-- The OUTER else-play of a Prudent-shaped member `0` (outer then: the prudence check; else `D`). -/
theorem bit_D_of_pm_else {k : ℕ} {A T : Tmpl} {m₁ : Prog} {H : Tmpl} (h : inst (tauZoo k) A T = .sys (sys2 (pm 1 k H) m₁) 0)
    (hn : ¬ LenBox TAct k (guardCode (templateCode (.plays (.bot (.sys (sys2 (pm 1 k H) m₁) 1)) (.bot (.sys (sys2 (pm 1 k H) m₁) 1)) .C))
      (progCode (sysFrame (pm 1 k H) m₁)) (progCode (sysFrame (pm 1 k H) m₁)))) :
    bitPlays k A T .D :=
  bitPlays_of_member h (memberP_pm 1 k (by decide) H)
    (by rw [pm_sysClose]; exact member_else _ hn (const_play 0 _ _ _))

end ArithS.Tau
