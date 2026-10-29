import ArithS.Bridge.AgentConverse

/-!
# ArithS.Inst — the instantiation `c_C ↦ 0, c_D ↦ 1`: PA proves the atom sentences of modest plays

Closes results-note boundary 2 (`ARITHMETIZED_S_RESULTS.md` §4) in its honest form.

The realized atom sentence `sentenceAt me' opp' (.plays me opp a)` (`ArithS.Code`) is a sentence of
`LAct = ℒₒᵣ + {c_C, c_D}`; it is TRUE in `ℕ` (`c_C ↦ 0, c_D ↦ 1`, `stdReadingNat`) exactly when the
arithmetized `play` yields `a` (`models_sentenceAt_plays`), which under `GuardAgree` is exactly when
the engine's `play` does (`play_iff_evalGraph`). Foundation's Σ₁-completeness is stated for
theories over `ℒₒᵣ`; `TAct` is over `LAct` and leaves the two constants uninterpreted, so the
sentence is not transportable as it stands. What IS provable, and proved here, is the sentence
with the constants INSTANTIATED by their standard values:

* `inst : LAct →ᵥ ℒₒᵣ` — the instantiation hom: `ℒₒᵣ`-symbols to themselves, `c_C ↦ 0`,
  `c_D ↦ 1`. It retracts `emb` (`inst_emb_func`, `lMap_inst_emb`) and the standard model of
  `ℒₒᵣ` pulls back along it to `stdReadingNat` (`lMap_inst_std`), so truth transfers
  (`models_inst : ℕ↓[ℒₒᵣ] ⊧ lMap inst σ ↔ ℕ↓[LAct] ⊧ σ`).
* `hierarchy_lMap_inst_sentenceAt_plays` — the instantiated atom sentence is `Σ₁`: `template (.plays …)`
  is `∃∃∃ (D ∧ D ∧ EvalGraph)` with the descriptions and `EvalGraph` the `emb`-images of `Σ₁`
  semisentences, which `lMap inst` sends back to themselves. For EVERY `me opp a` (the
  placeholders included: their descriptions are the frame's triples, also `Σ₁`).
* **`pa_proves_sentenceAt_inst`** — for proper modest players (every zoo bot, searchers included:
  `closedP` is NOT required, only `ProperPlayer` = not a bare pronoun), given `GuardAgree`,
  `(∃ n, play n me opp = some a) → 𝗣𝗔 ⊢ lMap inst (sentenceAt me' opp' (.plays me opp a))`, by
  `sigma_one_completeness` (`𝗥₀ ⪯ 𝗣𝗔`). `…_of_atomProvable` is the certificate form
  (`AtomProvable k (.plays me opp a)`), and `…_searchFree` the UNCONDITIONAL one (no oracle):
  on search-free players a certificate is a run of the arithmetized evaluator outright
  (`atomProvable_evalGraph_searchFree`).
* **Composition with T2-CORE** (the translation `tr`, removed 2026-10-29 with the bridge). `Aι := fun p q a ↦ lMap inst (sentenceAt p q
  (.plays p q a))` (the frame is the pair itself — irrelevant for proper programs).
  `leaf_atom_sound` discharges the `Leaf.atom` shape of `Core.Pf_core_sound` on proper modest
  players; `leaf_atomBoxImpl_sound` discharges `Leaf.atomBoxImpl` for ALL programs and
  budgets, certificate or not (formalized Σ₁-completeness, `provable_sigma_one_complete`);
  `Core.leaf_eqRefl_sound`/`leaf_eqNeg_sound` already discharge the two identity leaves.
  `transfer_of_leaves` is `Pf_core_sound` at `Aι`.

**What remains a hypothesis in `transfer_of_leaves`** (the `Leaf` constructors NOT discharged
here, and why):
* the SOURCE-READING rules `searchBranch, simStep, botSimStep, botSearchStep, botSysSearchStep,
  botSysSimStep, botSysSearchThenSearch, iteBranchSearch_t, searchThenSearch_t, searchChain,
  ctxChain, searchElseChain` — their conclusions are `□_g(guard) → plays me opp a` (or the
  `sim` analogue). Under `tr` the box is PA's UNBOUNDED provability predicate of the
  budget-erased guard, while the play-atom's evaluator consults the LENGTH-BOUNDED `□_k` of the
  realized guard (`LenBox TAct k (guardOf …)`): the two boxes are different sentences,
  and relating them is bounded D1 in both directions — `GuardAgree` again, now inside PA. This
  is boundary 1 (`.box` under length-bounded provability), not a gap in the evaluator.
* `atomNeg` — its conclusion `¬ plays p q aN` is `Π₁` (the negation of a `Σ₁` sentence), so
  Σ₁-completeness does not apply; PA would have to prove determinism of `EvalGraph`
  INTERNALLY (`EvalGraph.unique'` holds in every model of `𝗜𝚺₁`, so the route is the
  completeness theorem + upward transfer of the positive run + internal uniqueness), and the
  descriptions' evaluation lemmas (`val_binNumeralMeta`, `revalue_val_desc`) are stated for `ℕ` only.
  Not built; recorded in `ARITHMETIZED_S_RESULTS.md` §4.
* `atom` on players that are NOT proper modest (bare pronouns, tau constructors) — outside the
  translation.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

namespace LAct

/-! ### The instantiation hom -/

/-- The instantiation `c_C ↦ 0`, `c_D ↦ 1`; every `ℒₒᵣ`-symbol to itself. -/
def inst : LAct →ᵥ ℒₒᵣ where
  func {k} f := match k, f with
    | _, Sum.inl f => f
    | 0, Sum.inr (Language.Constant.Func.const Act.C) => Language.Zero.zero
    | 0, Sum.inr (Language.Constant.Func.const Act.D) => Language.One.one
  rel {_k} r := match r with
    | Sum.inl r => r
    | Sum.inr e => PEmpty.elim e


/-- The standard model of `ℒₒᵣ` pulled back along `inst` is `stdReadingNat`: both read `c_C` as `0`,
`c_D` as `1`, and the arithmetic symbols standardly. -/
lemma lMap_inst_std : Structure.lMap inst (standardModel ℕ) = stdReadingNat := by
  refine Structure.ext ?_ ?_
  · funext k f v
    rcases f with f | ⟨(_ | _)⟩ <;> rfl
  · funext k r v
    rcases r with r | e
    · rfl
    · exact e.elim

/-- **Truth transfer**: the instantiated sentence is true in `ℕ` iff the `LAct`-sentence is. -/
theorem models_inst (σ : Sentence LAct) :
    ℕ↓[ℒₒᵣ] ⊧ Semiformula.lMap inst σ ↔ ℕ↓[LAct] ⊧ σ := by
  have := Semiformula.models_lMap (s₂ := standardModel ℕ) (Φ := inst) (σ := σ) (M := ℕ)
  rw [lMap_inst_std] at this
  exact this

/-! ### The simp set of `inst` (restored 2026-10-29: `simp` uses them without a trace in the proof terms) -/

@[simp] lemma inst_inl {k : ℕ} (f : Language.Func ℒₒᵣ k) : inst.func (Sum.inl f : LAct.Func k) = f := rfl

@[simp] lemma inst_C : inst.func (const Act.C) = Language.Zero.zero := rfl

@[simp] lemma inst_D : inst.func (const Act.D) = Language.One.one := rfl

@[simp] lemma inst_rel_inl {k : ℕ} (r : Language.Rel ℒₒᵣ k) : inst.rel (Sum.inl r : LAct.Rel k) = r := rfl

/-- `inst` retracts the inclusion: `inst ∘ emb = id` on symbols. -/
@[simp] lemma inst_emb_func {k : ℕ} (f : Language.Func ℒₒᵣ k) : inst.func (emb.func f) = f := rfl

@[simp] lemma inst_emb_rel {k : ℕ} (r : Language.Rel ℒₒᵣ k) : inst.rel (emb.rel r) = r := rfl

/-! ### `inst ∘ emb = id` on terms and formulas -/

lemma term_lMap_inst_emb {n : ℕ} {ξ : Type*} (t : Semiterm ℒₒᵣ ξ n) :
    Semiterm.lMap inst (Semiterm.lMap emb t) = t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih => simp [Semiterm.lMap_func, Function.comp_def, ih]

lemma lMap_inst_emb {n : ℕ} {ξ : Type*} (φ : Semiformula ℒₒᵣ ξ n) :
    Semiformula.lMap inst (Semiformula.lMap emb φ) = φ := by
  induction φ with
  | rel R v => simp [Semiformula.lMap_rel, Function.comp_def, term_lMap_inst_emb]
  | nrel R v => simp [Semiformula.lMap_nrel, Function.comp_def, term_lMap_inst_emb]
  | verum =>
    change Semiformula.lMap inst (Semiformula.lMap emb ⊤) = ⊤
    simp
  | falsum =>
    change Semiformula.lMap inst (Semiformula.lMap emb ⊥) = ⊥
    simp
  | and φ ψ ihφ ihψ =>
    change Semiformula.lMap inst (Semiformula.lMap emb (φ ⋏ ψ)) = φ ⋏ ψ
    simp [ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    change Semiformula.lMap inst (Semiformula.lMap emb (φ ⋎ ψ)) = φ ⋎ ψ
    simp [ihφ, ihψ]
  | all φ ih =>
    change Semiformula.lMap inst (Semiformula.lMap emb (∀¹ φ)) = ∀¹ φ
    simp [ih]
  | exs φ ih =>
    change Semiformula.lMap inst (Semiformula.lMap emb (∃¹ φ)) = ∃¹ φ
    simp [ih]

end LAct

/-! ### The instantiated atom sentence is Σ₁ -/

lemma lMap_inst_relDesc : Semiformula.lMap inst relDesc = revalueDef.val := lMap_inst_emb _
lemma lMap_inst_evalG : Semiformula.lMap inst evalG = evalGraphDef.val := lMap_inst_emb _

lemma hierarchy_lMap_inst_descF {n : ℕ} (X T U W : Semiterm LAct Empty (n + 1)) :
    Hierarchy 𝚺 1 (Semiformula.lMap inst (descF X T U W)) := by
  unfold descF
  rw [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_rel,
    Semiformula.lMap_subst, lMap_inst_relDesc]
  simp

lemma hierarchy_lMap_inst_progAux (p : PD.Prog) (c : ℕ) :
    Hierarchy 𝚺 1 (Semiformula.lMap inst (progAux p c)) := by
  unfold progAux closedDesc
  split_ifs <;> exact hierarchy_lMap_inst_descF _ _ _ _

/-- The template of a play-atom, instantiated, is `Σ₁` — for every pair of programs. -/
theorem hierarchy_lMap_inst_template_plays (p q : PD.Prog) (a : PD.Action) :
    Hierarchy 𝚺 1 (Semiformula.lMap inst (template (.plays p q a))) := by
  rw [template_plays]
  unfold progGraph
  simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
    lMap_inst_evalG]
  simp [hierarchy_lMap_inst_progAux]

/-- **The instantiated atom sentence is `Σ₁`**, for every frame and every pair of programs. -/
theorem hierarchy_lMap_inst_sentenceAt_plays (me' opp' me opp : PD.Prog) (a : PD.Action) :
    Hierarchy 𝚺 1 (Semiformula.lMap inst (sentenceAt me' opp' (.plays me opp a))) := by
  unfold sentenceAt
  rw [Semiformula.lMap_subst]
  simpa using hierarchy_lMap_inst_template_plays me opp a

/-! ### PA proves the atom sentences of modest plays -/


/-! ### Composition with T2-CORE -/


end ArithS
