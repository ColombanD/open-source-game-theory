import ArithS.Agent

/-!
# ArithS.AgentConverse — the converse of T2-AGENT: `eval ↔ EvalGraph` on modest programs

**Given agreement on the consulted `□_k` facts, the arithmetized evaluator and the engine's
evaluator compute the same plays on modest programs (an equivalence).**

`ArithS.Agent` (T2-AGENT) turns an engine CERTIFICATE (`PlaysProof`) into a run of the
arithmetized evaluator, under the two one-directional oracle hypotheses `GuardAgreeT`/
`GuardAgreeF`. This module works with the engine's evaluator `PD.eval` itself and a SINGLE
two-sided oracle, and proves both directions:

* `GuardAgree` — the engine's `Pf` verdict and the arithmetized `□_k` verdict AGREE on the
  guards a modest match can consult: for a fragment formula `φ` (`fragF φ`) and proper modest
  players, `PD.Pf k (φ.subst me opp) ↔ LenProvableV TAct k (guardOf φ me opp)`. It is restricted
  to exactly the guards that are consulted, so it is the WEAKEST hypothesis both directions
  need. `GuardAgree.toT`/`GuardAgree.toF` show it subsumes the modest instances of both
  T2-AGENT hypotheses — the refutation form `F` falls out of engine soundness
  (`PD.BaseTheorems.Pf_sound`): a refuted guard cannot also be `Pf`-derivable, hence, by the
  `Iff`, cannot be found by the arithmetized search.
* `evalGraph_of_eval` — `PD.eval n me opp body = some a → ∃ N, EvalGraph N ⌜me⌝ ⌜opp⌝ ⌜body⌝ a`,
  by induction on the engine's fuel, unfolding `PD.eval` clause by clause (the `.ite` clause's
  `do`/`BEq` and the `.search` clause's `if proofSearch …` are bridged by `actCode_eq_of_beq`
  and `proofSearch_spec`). This does NOT go through `PlaysProof`, so it needs no refutation
  hypothesis at all.
* `eval_of_evalGraph` — the CONVERSE: `EvalGraph N ⌜me⌝ ⌜opp⌝ ⌜body⌝ r → ∃ a, r = actCode a ∧
  ∃ n, PD.eval n me opp body = some a`, by induction on the arithmetized fuel through the
  inversion lemmas of `ArithS.EvalN`. The result is generalized to an arbitrary code `r`:
  the `.ite` clause's guard result is a bare natural on the arithmetic side, and the induction
  must first learn that it is an action code. No injectivity of `pcode` is needed — the
  induction is on the fuel with the ENGINE program in the frame, `pcode` is unfolded by its
  equations, and the `.sim` step is `pcode_subst` read backwards.
* `eval_iff_evalGraph`, `play_iff_evalGraph`, `outcome_iff_evalGraph` — THE EQUIVALENCE, for
  bodies, plays and outcomes; `playsProof_evalGraph_of_guardAgree` re-derives T2-AGENT from the
  single `Iff` oracle (through `PD.BaseTheorems.playsProof_sound`).
* `plays_interp_iff` — for proper modest players the engine's truth of the atom
  `(.plays me opp a).interp` IS the truth in `ℕ` of its arithmetical translation
  `trAt me' opp' (.plays me opp a)` (via `models_trAt_plays`).

The tau constructors are excluded by `modestP` (their code is `0`); `Inv false` from
`ArithS.Agent` carries the frame invariant (proper modest players, modest body).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

/-! ### The two-sided oracle -/

/-- **Agreement on the consulted guards**: on a fragment guard `φ` and proper modest players,
the engine's bounded provability of the closed instantiation and the arithmetized `□_k` of
the realized guard coincide. Restricted to exactly what a modest match can consult. -/
def GuardAgree : Prop :=
  ∀ (φ : PD.Formula) (me opp : PD.Prog) (k : ℕ), fragF φ = true → Proper me → Proper opp →
    modestP me = true → modestP opp = true →
    (PD.Pf k (φ.subst me opp) ↔ LenProvableV TAct k (guardOf φ me opp))

/-- The unrestricted `Iff` (the literal two-sided agreement) implies `GuardAgree`. -/
theorem GuardAgree.of_forall
    (h : ∀ (φ : PD.Formula) (me opp : PD.Prog) (k : ℕ),
      PD.Pf k (φ.subst me opp) ↔ LenProvableV TAct k (guardOf φ me opp)) : GuardAgree :=
  fun φ me opp k _ _ _ _ _ ↦ h φ me opp k

/-- `GuardAgreeT` together with its converse gives `GuardAgree`. -/
theorem GuardAgree.of_T (hT : GuardAgreeT)
    (hC : ∀ (φ : PD.Formula) (me opp : PD.Prog) (k : ℕ),
      LenProvableV TAct k (guardOf φ me opp) → PD.Pf k (φ.subst me opp)) : GuardAgree :=
  GuardAgree.of_forall fun φ me opp k ↦ ⟨hT φ me opp k, hC φ me opp k⟩

/-- The modest instance of `GuardAgreeT` (bounded D1 on the consulted guards). -/
theorem GuardAgree.toT (h : GuardAgree) (φ : PD.Formula) (me opp : PD.Prog) (k : ℕ)
    (hφ : fragF φ = true) (hme : Proper me) (hopp : Proper opp)
    (hm : modestP me = true) (hm' : modestP opp = true) :
    PD.Pf k (φ.subst me opp) → LenProvableV TAct k (guardOf φ me opp) :=
  (h φ me opp k hφ hme hopp hm hm').mp

/-- The modest instance of `GuardAgreeF`, DERIVED: an engine refutation of the closed guard
excludes an arithmetized proof of it, because a found guard would be `Pf`-derivable (the
`Iff`), and `S` cannot derive both a sentence and its negation (`PD.BaseTheorems.Pf_sound`). -/
theorem GuardAgree.toF (h : GuardAgree) (φ : PD.Formula) (me opp : PD.Prog) (k m : ℕ)
    (hφ : fragF φ = true) (hme : Proper me) (hopp : Proper opp)
    (hm : modestP me = true) (hm' : modestP opp = true)
    (hneg : PD.Pf m (.neg (φ.subst me opp))) : ¬ LenProvableV TAct k (guardOf φ me opp) :=
  fun hl ↦ not_interp_of_pf_neg hneg
    (PD.BaseTheorems.Pf_sound k _ ((h φ me opp k hφ hme hopp hm hm').mpr hl))

/-! ### The engine's `BEq` on actions, read through `actCode` -/

lemma beq_of_actCode_eq {r a : PD.Action} (h : actCode r = actCode a) : (r == a) = true := by
  cases r <;> cases a <;> first | rfl | exact absurd h (by decide)

lemma beq_false_of_actCode_ne {r a : PD.Action} (h : actCode r ≠ actCode a) : (r == a) = false := by
  cases r <;> cases a <;> first | exact absurd rfl h | rfl

/-- The guard the arithmetized `.search` clause consults on a coded frame is `guardOf`. -/
lemma guardCode_tcode_pcode (φ : PD.Formula) (me opp : PD.Prog) :
    guardCode (tcode φ) (pcode me) (pcode opp) = guardOf φ me opp := rfl

lemma Inv.selfIdx {sf : Bool} {me op : PD.Prog} {j : ℕ} (h : Inv sf me op (.selfIdx j)) : False := by
  simpa [modestP] using h.2.2.2.2.1

lemma Inv.fragF_of_search {sf : Bool} {me op : PD.Prog} {k : ℕ} {φ : PD.Formula} {p q : PD.Prog}
    (h : Inv sf me op (.search k φ p q)) : fragF φ = true := by
  have := h.2.2.2.2.1
  simp only [modestP, Bool.and_eq_true] at this
  exact this.1.1

/-- The oracle, at a search node of a modest match. -/
lemma GuardAgree.at_node (hga : GuardAgree) {me op : PD.Prog} {k : ℕ} {φ : PD.Formula}
    {p q : PD.Prog} (hI : Inv false me op (.search k φ p q)) :
    PD.Pf k (φ.subst me op) ↔ LenProvableV TAct k (guardOf φ me op) :=
  hga φ me op k (Inv.fragF_of_search hI) hI.1 hI.2.1 hI.2.2.1 hI.2.2.2.1

/-! ### Engine → arithmetic: induction on the engine's fuel -/

/-- The forward direction, with the invariant as a premise. -/
theorem evalGraph_of_eval_core (hga : GuardAgree) :
    ∀ (n : ℕ) (me opp body : PD.Prog) (a : PD.Action), Inv false me opp body →
      PD.eval n me opp body = some a →
      ∃ N, EvalGraph N (pcode me) (pcode opp) (pcode body) (actCode a) := by
  intro n
  induction n with
  | zero => intro me opp body a _ h; simp [PD.eval] at h
  | succ n ih =>
    intro me opp body a hI h
    cases body with
    | const c =>
      have hc : c = a := by simpa [PD.eval] using h
      subst hc
      exact ⟨1, by rw [pcode_const]; exact (EvalGraph.const_iff (n := 0)).mpr rfl⟩
    | self =>
      rw [PD.eval] at h
      obtain ⟨N, hN⟩ := ih me opp me a (Inv.self hI) h
      exact ⟨N + 1, by rw [pcode_self, EvalGraph.self_iff]; exact hN⟩
    | opp =>
      rw [PD.eval] at h
      obtain ⟨N, hN⟩ := ih me opp opp a (Inv.opp hI) h
      exact ⟨N + 1, by rw [pcode_opp, EvalGraph.opp_iff]; exact hN⟩
    | bot p =>
      rw [PD.eval] at h
      obtain ⟨N, hN⟩ := ih me opp p a (Inv.bot hI) h
      exact ⟨N + 1, by rw [pcode_bot, EvalGraph.bot_iff]; exact hN⟩
    | sim p q =>
      rw [PD.eval] at h
      obtain ⟨N, hN⟩ := ih _ _ _ a (Inv.sim hI) h
      have hmb := hI.2.2.2.2.1
      simp only [modestP, Bool.and_eq_true] at hmb
      rw [pcode_subst hI.1 hI.2.1 p (fragP_of_modestP p hmb.1.2),
        pcode_subst hI.1 hI.2.1 q (fragP_of_modestP q hmb.2)] at hN
      exact ⟨N + 1, by rw [pcode_sim, EvalGraph.sim_iff]; exact hN⟩
    | ite b c p q =>
      obtain ⟨hIb, hIp, hIq⟩ := Inv.ite hI
      rw [PD.eval] at h
      cases hb : PD.eval n me opp b with
      | none => simp [hb] at h
      | some r =>
        rw [hb] at h
        simp only [bind, Option.bind] at h
        obtain ⟨N₁, h₁⟩ := ih me opp b r hIb hb
        by_cases hr : (r == c) = true
        · rw [if_pos hr] at h
          obtain ⟨N₂, h₂⟩ := ih me opp p a hIp h
          refine ⟨max N₁ N₂ + 1, ?_⟩
          rw [pcode_ite, EvalGraph.ite_iff]
          exact ⟨actCode r, EvalGraph.mono_le (le_max_left _ _) h₁,
            Or.inl ⟨actCode_eq_of_beq hr, EvalGraph.mono_le (le_max_right _ _) h₂⟩⟩
        · rw [if_neg hr] at h
          obtain ⟨N₂, h₂⟩ := ih me opp q a hIq h
          refine ⟨max N₁ N₂ + 1, ?_⟩
          rw [pcode_ite, EvalGraph.ite_iff]
          exact ⟨actCode r, EvalGraph.mono_le (le_max_left _ _) h₁,
            Or.inr ⟨actCode_ne_of_beq_false (Bool.eq_false_iff.mpr hr),
              EvalGraph.mono_le (le_max_right _ _) h₂⟩⟩
    | search k φ p q =>
      obtain ⟨_, hIp, hIq⟩ := Inv.search hI
      rw [PD.eval] at h
      by_cases hg : PD.proofSearch k (φ.subst me opp) = true
      · rw [if_pos hg] at h
        obtain ⟨N, hN⟩ := ih me opp p a hIp h
        refine ⟨N + 1, ?_⟩
        rw [pcode_search, EvalGraph.search_iff, guardCode_tcode_pcode]
        exact Or.inl ⟨(hga.at_node hI).mp ((PD.BaseTheorems.proofSearch_spec k _).mp hg), hN⟩
      · rw [if_neg hg] at h
        obtain ⟨N, hN⟩ := ih me opp q a hIq h
        refine ⟨N + 1, ?_⟩
        rw [pcode_search, EvalGraph.search_iff, guardCode_tcode_pcode]
        exact Or.inr ⟨fun hl ↦ hg ((PD.BaseTheorems.proofSearch_spec k _).mpr
          ((hga.at_node hI).mpr hl)), hN⟩
    | tvote v θ p q => exact (Inv.tvote hI).elim
    | sys defs i => exact (Inv.sys hI).elim
    | selfIdx j => exact (Inv.selfIdx hI).elim

/-- **Engine → arithmetic.** A successful engine run on a modest frame is a run of the
arithmetized evaluator, given `GuardAgree`. No certificate, no refutation hypothesis. -/
theorem evalGraph_of_eval (hga : GuardAgree) {me opp body : PD.Prog} {a : PD.Action} {n : ℕ}
    (h : PD.eval n me opp body = some a) (hme : Proper me) (hopp : Proper opp)
    (hm : modestP me = true) (hm' : modestP opp = true) (hb : modestP body = true) :
    ∃ N, EvalGraph N (pcode me) (pcode opp) (pcode body) (actCode a) :=
  evalGraph_of_eval_core hga n me opp body a
    ⟨hme, hopp, hm, hm', hb, fun h ↦ absurd h Bool.false_ne_true⟩ h

/-! ### Arithmetic → engine: induction on the arithmetized fuel -/

/-- The converse, with the invariant as a premise and the result an arbitrary code `r`: on a
coded modest frame every result of the arithmetized evaluator is an action code, and the
engine plays that action. -/
theorem eval_of_evalGraph_core (hga : GuardAgree) :
    ∀ (N : ℕ) (me opp body : PD.Prog) (r : ℕ), Inv false me opp body →
      EvalGraph N (pcode me) (pcode opp) (pcode body) r →
      ∃ a : PD.Action, r = actCode a ∧ ∃ n, PD.eval n me opp body = some a := by
  intro N
  induction N with
  | zero => intro me opp body r _ h; exact absurd h EvalGraph.zero_iff
  | succ N ih =>
    intro me opp body r hI h
    cases body with
    | const c =>
      rw [pcode_const, EvalGraph.const_iff] at h
      exact ⟨c, h, 1, by simp [PD.eval]⟩
    | self =>
      rw [pcode_self, EvalGraph.self_iff] at h
      obtain ⟨a, rfl, n, hn⟩ := ih me opp me r (Inv.self hI) h
      exact ⟨a, rfl, n + 1, by rw [PD.eval]; exact hn⟩
    | opp =>
      rw [pcode_opp, EvalGraph.opp_iff] at h
      obtain ⟨a, rfl, n, hn⟩ := ih me opp opp r (Inv.opp hI) h
      exact ⟨a, rfl, n + 1, by rw [PD.eval]; exact hn⟩
    | bot p =>
      rw [pcode_bot, EvalGraph.bot_iff] at h
      obtain ⟨a, rfl, n, hn⟩ := ih me opp p r (Inv.bot hI) h
      exact ⟨a, rfl, n + 1, by rw [PD.eval]; exact hn⟩
    | sim p q =>
      have hmb := hI.2.2.2.2.1
      simp only [modestP, Bool.and_eq_true] at hmb
      rw [pcode_sim, EvalGraph.sim_iff,
        ← pcode_subst hI.1 hI.2.1 p (fragP_of_modestP p hmb.1.2),
        ← pcode_subst hI.1 hI.2.1 q (fragP_of_modestP q hmb.2)] at h
      obtain ⟨a, rfl, n, hn⟩ := ih _ _ _ r (Inv.sim hI) h
      exact ⟨a, rfl, n + 1, by rw [PD.eval]; exact hn⟩
    | ite b c p q =>
      obtain ⟨hIb, hIp, hIq⟩ := Inv.ite hI
      rw [pcode_ite, EvalGraph.ite_iff] at h
      obtain ⟨r', hb, hc⟩ := h
      obtain ⟨a', rfl, n₁, h₁⟩ := ih me opp b r' hIb hb
      rcases hc with ⟨e, hp⟩ | ⟨e, hq⟩
      · obtain ⟨a, rfl, n₂, h₂⟩ := ih me opp p r hIp hp
        refine ⟨a, rfl, max n₁ n₂ + 1, ?_⟩
        rw [PD.eval, PD.BaseTheorems.eval_mono_le h₁ _ (le_max_left _ _)]
        simp only [bind, Option.bind]
        rw [if_pos (beq_of_actCode_eq e)]
        exact PD.BaseTheorems.eval_mono_le h₂ _ (le_max_right _ _)
      · obtain ⟨a, rfl, n₂, h₂⟩ := ih me opp q r hIq hq
        refine ⟨a, rfl, max n₁ n₂ + 1, ?_⟩
        rw [PD.eval, PD.BaseTheorems.eval_mono_le h₁ _ (le_max_left _ _)]
        simp only [bind, Option.bind]
        rw [if_neg (Bool.eq_false_iff.mp (beq_false_of_actCode_ne e))]
        exact PD.BaseTheorems.eval_mono_le h₂ _ (le_max_right _ _)
    | search k φ p q =>
      obtain ⟨_, hIp, hIq⟩ := Inv.search hI
      rw [pcode_search, EvalGraph.search_iff, guardCode_tcode_pcode] at h
      rcases h with ⟨hl, hp⟩ | ⟨hl, hq⟩
      · obtain ⟨a, rfl, n, hn⟩ := ih me opp p r hIp hp
        have hg : PD.proofSearch k (φ.subst me opp) = true :=
          (PD.BaseTheorems.proofSearch_spec k _).mpr ((hga.at_node hI).mpr hl)
        exact ⟨a, rfl, n + 1, by rw [PD.eval, if_pos hg]; exact hn⟩
      · obtain ⟨a, rfl, n, hn⟩ := ih me opp q r hIq hq
        have hg : ¬ PD.proofSearch k (φ.subst me opp) = true := fun hg ↦
          hl ((hga.at_node hI).mp ((PD.BaseTheorems.proofSearch_spec k _).mp hg))
        exact ⟨a, rfl, n + 1, by rw [PD.eval, if_neg hg]; exact hn⟩
    | tvote v θ p q => exact (Inv.tvote hI).elim
    | sys defs i => exact (Inv.sys hI).elim
    | selfIdx j => exact (Inv.selfIdx hI).elim

/-- **Arithmetic → engine (the converse of T2-AGENT).** A run of the arithmetized evaluator
on a coded modest frame is a successful engine run with the same action, given `GuardAgree`. -/
theorem eval_of_evalGraph (hga : GuardAgree) {me opp body : PD.Prog} {a : PD.Action} {N : ℕ}
    (h : EvalGraph N (pcode me) (pcode opp) (pcode body) (actCode a))
    (hme : Proper me) (hopp : Proper opp)
    (hm : modestP me = true) (hm' : modestP opp = true) (hb : modestP body = true) :
    ∃ n, PD.eval n me opp body = some a := by
  obtain ⟨a', e, n, hn⟩ := eval_of_evalGraph_core hga N me opp body (actCode a)
    ⟨hme, hopp, hm, hm', hb, fun h ↦ absurd h Bool.false_ne_true⟩ h
  rw [actCode_inj e]
  exact ⟨n, hn⟩

/-- On a coded modest frame the arithmetized evaluator only ever returns action codes. -/
theorem evalGraph_actCode (hga : GuardAgree) {me opp body : PD.Prog} {r N : ℕ}
    (h : EvalGraph N (pcode me) (pcode opp) (pcode body) r)
    (hme : Proper me) (hopp : Proper opp)
    (hm : modestP me = true) (hm' : modestP opp = true) (hb : modestP body = true) :
    ∃ a : PD.Action, r = actCode a := by
  obtain ⟨a, e, _⟩ := eval_of_evalGraph_core hga N me opp body r
    ⟨hme, hopp, hm, hm', hb, fun h ↦ absurd h Bool.false_ne_true⟩ h
  exact ⟨a, e⟩

/-! ### The equivalence -/

/-- **THE EQUIVALENCE.** Given agreement on the consulted `□_k` facts, the arithmetized
evaluator and the engine's evaluator compute the same plays on modest programs. -/
theorem eval_iff_evalGraph (hga : GuardAgree) {me opp body : PD.Prog}
    (hme : Proper me) (hopp : Proper opp)
    (hm : modestP me = true) (hm' : modestP opp = true) (hb : modestP body = true)
    (a : PD.Action) :
    (∃ n, PD.eval n me opp body = some a) ↔
      ∃ N, EvalGraph N (pcode me) (pcode opp) (pcode body) (actCode a) :=
  ⟨fun ⟨_, h⟩ ↦ evalGraph_of_eval hga h hme hopp hm hm' hb,
   fun ⟨_, h⟩ ↦ eval_of_evalGraph hga h hme hopp hm hm' hb⟩

/-- The equivalence for `play` (`eval me opp me`). -/
theorem play_iff_evalGraph (hga : GuardAgree) {me opp : PD.Prog}
    (hme : Proper me) (hopp : Proper opp) (hm : modestP me = true) (hm' : modestP opp = true)
    (a : PD.Action) :
    (∃ n, PD.play n me opp = some a) ↔
      ∃ N, EvalGraph N (pcode me) (pcode opp) (pcode me) (actCode a) :=
  eval_iff_evalGraph hga hme hopp hm hm' hm a

/-- An engine outcome is a pair of plays at a common fuel. -/
lemma outcome_eq_some_iff (n : ℕ) (p q : PD.Prog) (a b : PD.Action) :
    PD.outcome n p q = some (a, b) ↔ PD.play n p q = some a ∧ PD.play n q p = some b := by
  unfold PD.outcome
  cases PD.play n p q <;> cases PD.play n q p <;> simp [and_comm, eq_comm]

/-- The equivalence for outcomes: two independent runs of the arithmetized `play`. -/
theorem outcome_iff_evalGraph (hga : GuardAgree) {me opp : PD.Prog}
    (hme : Proper me) (hopp : Proper opp) (hm : modestP me = true) (hm' : modestP opp = true)
    (a b : PD.Action) :
    (∃ n, PD.outcome n me opp = some (a, b)) ↔
      (∃ N, EvalGraph N (pcode me) (pcode opp) (pcode me) (actCode a)) ∧
      (∃ N, EvalGraph N (pcode opp) (pcode me) (pcode opp) (actCode b)) := by
  rw [← play_iff_evalGraph hga hme hopp hm hm' a, ← play_iff_evalGraph hga hopp hme hm' hm b]
  constructor
  · rintro ⟨n, h⟩
    obtain ⟨ha, hb⟩ := (outcome_eq_some_iff n me opp a b).mp h
    exact ⟨⟨n, ha⟩, ⟨n, hb⟩⟩
  · rintro ⟨⟨n₁, ha⟩, ⟨n₂, hb⟩⟩
    refine ⟨max n₁ n₂, (outcome_eq_some_iff _ me opp a b).mpr ⟨?_, ?_⟩⟩
    · exact PD.BaseTheorems.eval_mono_le ha _ (le_max_left _ _)
    · exact PD.BaseTheorems.eval_mono_le hb _ (le_max_right _ _)

/-- T2-AGENT re-derived from the single two-sided oracle: an engine certificate is a real
play (`playsProof_sound`), hence a run of the arithmetized evaluator. -/
theorem playsProof_evalGraph_of_guardAgree (hga : GuardAgree)
    {me opp body : PD.Prog} {a : PD.Action} {n : ℕ} (h : PD.PlaysProof me opp body a n)
    (hme : Proper me) (hopp : Proper opp)
    (hm : modestP me = true) (hm' : modestP opp = true) (hb : modestP body = true) :
    ∃ N, EvalGraph N (pcode me) (pcode opp) (pcode body) (actCode a) :=
  (eval_iff_evalGraph hga hme hopp hm hm' hb a).mp (PD.BaseTheorems.playsProof_sound h)

/-! ### The truth equation, engine side -/

/-- **Truth of an engine atom = truth in `ℕ` of its translation.** For proper modest players
(every zoo bot), `⊨ (.plays me opp a)` (the engine's `Formula.interp`) holds iff the
arithmetical translation `trAt me' opp' (.plays me opp a)` is true in `ℕ`, given `GuardAgree`;
the frame `(me', opp')` is irrelevant for proper programs. -/
theorem plays_interp_iff (hga : GuardAgree) (me' opp' me opp : PD.Prog) (a : PD.Action)
    (hme : Proper me) (hopp : Proper opp)
    (hm : modestP me = true) (hm' : modestP opp = true) :
    (PD.Formula.plays me opp a).interp ↔ ℕ↓[LAct] ⊧ trAt me' opp' (.plays me opp a) := by
  rw [models_trAt_plays me' opp' me opp a hme hopp]
  exact play_iff_evalGraph hga hme hopp hm hm' a

end ArithS
