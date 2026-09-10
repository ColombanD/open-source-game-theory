import PrisonersDilemma.ProofSystem
import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.Incompleteness.Definability

/-!
# ArithS.Core.Tr — the budget-erased translation of the engine's `Formula` into PA

T2-CORE, part 1 (`Research/Notes/ARITHMETIZED_S_ROADMAP.md`, "M3 DESIGN DECISION").

Fix an arbitrary ATOM REALIZATION `A : Prog → Prog → Action → Sentence ℒₒᵣ` (what the
play-atoms `p(q) = a` mean in arithmetic — left abstract here; T2-AGENT supplies one).
`tr A` sends every engine `Formula` to an arithmetic sentence, ERASING the budgets:

* `.plays p q a ↦ A p q a`; `.impl ↦ 🡒`; `.neg ↦ ∼`;
* `.eq p q ↦ ⊤` if `p = q` else `⊥` (structural identity is decidable);
* `.box k ψ ↦ provabilityPred 𝗣𝗔 (tr ψ)` — Foundation's STANDARD provability predicate of
  PA, `Bew_PA(⌜tr ψ⌝)`; the subscript `k` is forgotten;
* `.diag g tgt ↦ fixedpoint “x. Bew_PA x → tr tgt”` — the Gödel–Löb fixed point of the
  Kreisel-style predicate, so that `𝗣𝗔 ⊢ tr(.diag g tgt) 🡘 (□ tr(.diag g tgt) 🡒 tr tgt)`
  (`tr_diag_spec`), which is exactly what the engine's `diagF`/`diagB` rules read off
  `Formula.diag` (whose engine meaning IS the fixpoint by design).

`Leaf ψ` is the shape predicate of the NON-core `Pf` rules: one constructor per reading /
execution-bridge rule, mirroring that rule's CONCLUSION and its non-`Pf` side conditions
(the `hme`/`hget` shape equations, `AtomProvable`, `p ≠ q`, `b ≠ aN`) with no budget. The
two mixed rules `searchThenSearch_t`/`botSysSearchThenSearch` drop their `Pf m …` premise
and are recorded by their conclusion shape only. `Core/Sound.lean` proves that every
`Pf`-derivation whose leaves are PA-provable under `A` translates to a PA theorem.
-/

namespace ArithS.Core

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PD

/-- An atom realization: the arithmetic meaning of a play-atom `p(q) = a`. Arbitrary here. -/
abbrev AtomRealization := PD.Prog → PD.Prog → PD.Action → ArithmeticSentence

/-- The Kreisel-style one-variable predicate whose fixed point translates `.diag`:
`“x. Bew_PA(x) → σ”`. -/
noncomputable def diagPred (σ : ArithmeticSentence) : ArithmeticSemisentence 1 :=
  “x. !(provable 𝗣𝗔) x → !σ”

/-- **The budget-erased translation** of an engine formula into an arithmetic sentence. -/
noncomputable def tr (A : AtomRealization) : PD.Formula → ArithmeticSentence
  | .plays p q a => A p q a
  | .impl φ ψ    => tr A φ 🡒 tr A ψ
  | .neg φ       => ∼ tr A φ
  | .box _ ψ     => provabilityPred 𝗣𝗔 (tr A ψ)
  | .eq p q      => if p = q then ⊤ else ⊥
  | .diag _ tgt  => fixedpoint (diagPred (tr A tgt))

variable (A : AtomRealization)

@[simp] lemma tr_plays (p q : PD.Prog) (a : PD.Action) : tr A (.plays p q a) = A p q a := rfl
@[simp] lemma tr_impl (φ ψ : PD.Formula) : tr A (.impl φ ψ) = (tr A φ 🡒 tr A ψ) := rfl
@[simp] lemma tr_neg (φ : PD.Formula) : tr A (.neg φ) = ∼ tr A φ := rfl
@[simp] lemma tr_box (k : ℕ) (ψ : PD.Formula) :
    tr A (.box k ψ) = provabilityPred 𝗣𝗔 (tr A ψ) := rfl
@[simp] lemma tr_eq (p q : PD.Prog) : tr A (.eq p q) = if p = q then ⊤ else ⊥ := rfl
@[simp] lemma tr_diag (g : ℕ) (tgt : PD.Formula) :
    tr A (.diag g tgt) = fixedpoint (diagPred (tr A tgt)) := rfl

lemma tr_eq_self (p : PD.Prog) : tr A (.eq p p) = ⊤ := by simp
lemma tr_eq_of_ne {p q : PD.Prog} (h : p ≠ q) : tr A (.eq p q) = ⊥ := by simp [h]

/-- Budget erasure: the box subscript is invisible to `tr`. -/
lemma tr_box_budget_irrel (a b : ℕ) (ψ : PD.Formula) : tr A (.box a ψ) = tr A (.box b ψ) := rfl

/-- The translated box IS Foundation's standard provability predicate of PA (the
`Provability 𝗜𝚺₁ 𝗣𝗔` object that carries D1/D2/D3 and Löb). -/
lemma tr_box_eq_standardProvability (k : ℕ) (ψ : PD.Formula) :
    tr A (.box k ψ) = (𝗣𝗔.standardProvability) (tr A ψ) := rfl

/-- The translated `.diag` is the Kreisel fixed point of `ProvabilityAbstraction`. -/
lemma tr_diag_eq_kreisel (g : ℕ) (tgt : PD.Formula) :
    tr A (.diag g tgt) = ProvabilityAbstraction.kreisel (𝗣𝗔.standardProvability) (tr A tgt) := rfl

/-- **The fixed-point specification of the translated `.diag`**: in PA,
`tr(.diag g tgt) ↔ (Bew_PA ⌜tr(.diag g tgt)⌝ → tr tgt)` — the engine's
`(.diag g tgt).interp = Pf g (.diag g tgt) → tgt.interp`, budget erased. -/
theorem tr_diag_spec (g : ℕ) (tgt : PD.Formula) :
    𝗣𝗔 ⊢ tr A (.diag g tgt) 🡘 (provabilityPred 𝗣𝗔 (tr A (.diag g tgt)) 🡒 tr A tgt) := by
  have := ProvabilityAbstraction.kreisel_spec (T₀ := 𝗜𝚺₁) (T := 𝗣𝗔)
    (𝔅 := 𝗣𝗔.standardProvability) (σ := tr A tgt)
  rw [tr_diag_eq_kreisel]
  exact Entailment.WeakerThan.pbl this

/-! ## The leaf predicate — the non-core rules by conclusion shape -/

/-- `Leaf ψ`: `ψ` is the conclusion of one of the NON-core `Pf` rules (execution bridge,
refutation suppliers, source-transparency readers, structural identity, the atom
Σ₁-completeness rule, and the two mixed rules with their `Pf` premise dropped), with the
rule's non-`Pf` side conditions and no budget. -/
inductive Leaf : PD.Formula → Prop where
  | atom (k : ℕ) (φ : PD.Formula) : PD.AtomProvable k φ → Leaf φ
  | atomNeg (p q : PD.Prog) (b aN : PD.Action) (m : ℕ) :
      PD.AtomProvable m (.plays p q b) → b ≠ aN → Leaf (.neg (.plays p q aN))
  | eqRefl (p : PD.Prog) : Leaf (.eq p p)
  | eqNeg (p q : PD.Prog) (hne : p ≠ q) : Leaf (.neg (.eq p q))
  | searchBranch (g : ℕ) (ψ : PD.Formula) (a b : PD.Action) (me opponent : PD.Prog)
      (hme : me = .search g ψ (.const a) (.const b)) :
      Leaf (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a))
  | simStep (me p q opponent : PD.Prog) (a : PD.Action) (hme : me = .sim p q) :
      Leaf (.impl (.plays (p.subst me opponent) (q.subst me opponent) a) (.plays me opponent a))
  | botSimStep (me p q opponent : PD.Prog) (a : PD.Action) (hme : me = .bot (.sim p q)) :
      Leaf (.impl (.plays (p.subst me opponent) (q.subst me opponent) a) (.plays me opponent a))
  | botSearchStep (g : ℕ) (ψ : PD.Formula) (a b : PD.Action) (me opponent : PD.Prog)
      (hme : me = .bot (.search g ψ (.const a) (.const b))) :
      Leaf (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a))
  | botSysSearchStep (defs : PD.ProgList) (i g : ℕ) (ψ : PD.Formula) (a b : PD.Action)
      (me opponent : PD.Prog)
      (hme : me = .bot (.sys defs i))
      (hget : defs.get? i = some (.search g ψ (.const a) (.const b))) :
      Leaf (.impl (.box g ((ψ.sysClose defs).subst me opponent)) (.plays me opponent a))
  | botSysSimStep (defs : PD.ProgList) (i j : ℕ) (a : PD.Action) (me opponent : PD.Prog)
      (hme : me = .bot (.sys defs i))
      (hget : defs.get? i = some (.sim (.bot (.selfIdx j)) (.bot (.selfIdx j)))) :
      Leaf (.impl (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) a) (.plays me opponent a))
  | botSysSearchThenSearch (defs : PD.ProgList) (i k₁ k₂ : ℕ) (ψ₁ ψ₂ : PD.Formula)
      (c0 c1 : PD.Action) (q me opponent : PD.Prog)
      (hme : me = .bot (.sys defs i))
      (hget : defs.get? i = some (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q)) :
      Leaf (.impl (.box k₁ ((ψ₁.sysClose defs).subst me opponent)) (.plays me opponent c0))
  | iteBranchSearch_t (g : ℕ) (z : PD.Prog) (a' c0 c1 : PD.Action) (ψ : PD.Formula)
      (q me opponent : PD.Prog)
      (hme : me = .ite (.sim .opp (.bot z)) a' (.search g ψ (.const c0) (.const c1)) q) :
      Leaf (.impl (.plays opponent (.bot z) a')
        (.impl (.box g (ψ.subst me opponent)) (.plays me opponent c0)))
  | searchThenSearch_t (k₁ k₂ : ℕ) (ψ₁ ψ₂ : PD.Formula) (c0 c1 : PD.Action)
      (q me opponent : PD.Prog)
      (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) :
      Leaf (.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0))
  | searchChain (g₁ : ℕ) (ψ₁ : PD.Formula) (e₁ : PD.Prog)
      (L : List (ℕ × PD.Formula × PD.Prog)) (a : PD.Action) (me opponent : PD.Prog)
      (hme : me = .search g₁ ψ₁ (PD.searchPlug L (.const a)) e₁) :
      Leaf (.impl (.box g₁ (ψ₁.subst me opponent))
        (PD.implChain (PD.searchGuards me opponent L) (.plays me opponent a)))
  | ctxChain (hd : PD.CtxLayer) (L : List PD.CtxLayer) (a : PD.Action) (me opponent : PD.Prog)
      (hme : me = PD.ctxPlug (hd :: L) (.const a)) :
      Leaf (.impl (PD.ctxGuard me opponent hd)
        (PD.implChain (PD.ctxGuards me opponent L) (.plays me opponent a)))
  | searchElseChain (hd : PD.SearchLayer2) (L : List PD.SearchLayer2) (a : PD.Action)
      (me opponent : PD.Prog)
      (hme : me = PD.plug2 (hd :: L) (.const a)) :
      Leaf (.impl (PD.guard2 me opponent hd)
        (PD.implChain (PD.guards2 me opponent L) (.plays me opponent a)))
  | atomBoxImpl (kBox : ℕ) (p q : PD.Prog) (a : PD.Action) :
      PD.AtomProvable kBox (.plays p q a) →
      Leaf (.impl (.plays p q a) (.box kBox (.plays p q a)))

/-- The two structural-identity leaves are PA-provable under EVERY realization: `⊤` and
`∼⊥`. (They are listed in `Leaf` to keep one constructor per non-core rule; a caller
instantiating the leaf hypothesis discharges them with these.) -/
theorem leaf_eqRefl_sound (p : PD.Prog) : 𝗣𝗔 ⊢ tr A (.eq p p) := by
  rw [tr_eq_self]; exact Entailment.verum

theorem leaf_eqNeg_sound {p q : PD.Prog} (h : p ≠ q) : 𝗣𝗔 ⊢ tr A (.neg (.eq p q)) := by
  rw [tr_neg, tr_eq_of_ne A h]; exact Entailment.NO

end ArithS.Core
