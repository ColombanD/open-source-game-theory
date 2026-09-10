import ArithS.Core.Tr

/-!
# ArithS.Core.Sound — `Pf_core_sound`: the modal-propositional core of `S` is sound over PA

T2-CORE, part 2 (`Research/Notes/ARITHMETIZED_S_ROADMAP.md`, "M3 DESIGN DECISION").

**The claim, in English.** The engine's Löbian core is a fragment of GL over PA: every
`Pf`-derivation whose atom-layer conclusions (the `Leaf` shapes — execution certificates,
refutations, source-transparency readings, structural identity, atom Σ₁-completeness) are
PA-provable under the atom realization `A` yields a PA proof of its budget-erased
translation `tr A φ`. The CORE rules
`mp implTrans weakenImpl impS2 implRefl implK implS contrapose negElim`
(propositional glue) and
`boxIntro axK axKf box4 boxMono diagF diagB`
(the bounded HBL/Löb tier) are discharged, budget forgotten, by Foundation's classical
propositional API and by the standard provability predicate of PA: D1 (`provable_D1`), D2
(`provable_D2`), D3 (`provable_D3`) and the Kreisel fixed point (`kreisel_spec`, via
`tr_diag_spec`) — all stated in `𝗜𝚺₁` and lifted along `𝗜𝚺₁ ⪯ 𝗣𝗔`. The `Pf pm (…)` Löb-premise
gate of `diagF`/`diagB` and every budget inequality are ignored: they exist to keep the
engine's transcript accounting honest, not for the soundness of the reading. Budget-KEEPING
soundness (a PA proof of length matching the engine's `k`) is Critch's assumption (d) and is
milestone M4, not this theorem.
-/

namespace ArithS.Core

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open Entailment
open PD

variable (A : AtomRealization)

/-! ## The core rules, one lemma each (budget erased) -/

/-- `boxIntro` (bounded necessitation, HBL D1): `𝗣𝗔 ⊢ σ → 𝗣𝗔 ⊢ □σ`. -/
theorem box_of_provable {σ : ArithmeticSentence} (h : 𝗣𝗔 ⊢ σ) :
    𝗣𝗔 ⊢ provabilityPred 𝗣𝗔 σ :=
  WeakerThan.pbl (provable_D1 h)

/-- `axKf` (K as an object formula, HBL D2). -/
theorem box_K (σ π : ArithmeticSentence) :
    𝗣𝗔 ⊢ provabilityPred 𝗣𝗔 (σ 🡒 π) 🡒 provabilityPred 𝗣𝗔 σ 🡒 provabilityPred 𝗣𝗔 π :=
  WeakerThan.pbl provable_D2

/-- `axK` (K in rule form). -/
theorem box_K_rule {σ π : ArithmeticSentence} (h : 𝗣𝗔 ⊢ provabilityPred 𝗣𝗔 (σ 🡒 π)) :
    𝗣𝗔 ⊢ provabilityPred 𝗣𝗔 σ 🡒 provabilityPred 𝗣𝗔 π :=
  box_K σ π ⨀ h

/-- `box4` (HBL D3). -/
theorem box_4 (σ : ArithmeticSentence) :
    𝗣𝗔 ⊢ provabilityPred 𝗣𝗔 σ 🡒 provabilityPred 𝗣𝗔 (provabilityPred 𝗣𝗔 σ) :=
  WeakerThan.pbl provable_D3

/-- `diagF`: the forward leg of the fixed point. -/
theorem diag_forward (g : ℕ) (tgt : PD.Formula) :
    𝗣𝗔 ⊢ tr A (.diag g tgt) 🡒 (provabilityPred 𝗣𝗔 (tr A (.diag g tgt)) 🡒 tr A tgt) :=
  K_left (tr_diag_spec A g tgt)

/-- `diagB`: the backward leg of the fixed point. -/
theorem diag_backward (g : ℕ) (tgt : PD.Formula) :
    𝗣𝗔 ⊢ (provabilityPred 𝗣𝗔 (tr A (.diag g tgt)) 🡒 tr A tgt) 🡒 tr A (.diag g tgt) :=
  K_right (tr_diag_spec A g tgt)

/-! ## The theorem -/

/-- **T2-CORE.** Fix an atom realization `A`. If every `Leaf` shape (the conclusions of the
non-core `Pf` rules) is PA-provable under `A`, then every `S`-theorem `⊢_k φ` translates,
budget erased, to a PA theorem `𝗣𝗔 ⊢ tr A φ`. The engine's Löbian core is a fragment of GL
over PA. -/
theorem Pf_core_sound (hleaf : ∀ ψ, Leaf ψ → 𝗣𝗔 ⊢ tr A ψ) {k : ℕ} {φ : PD.Formula}
    (h : PD.Pf k φ) : 𝗣𝗔 ⊢ tr A φ := by
  induction h using PD.Pf.induct with
  -- ═══ leaves: rebuild the `Leaf` witness from the arm's data ═══
  | atom k φ hatom => exact hleaf _ (.atom k φ hatom)
  | atomNeg k p q b aN m hatom hne _ => exact hleaf _ (.atomNeg p q b aN m hatom hne)
  | searchBranch k g ψ a b me opponent hme _ =>
      exact hleaf _ (.searchBranch g ψ a b me opponent hme)
  | simStep k me p q opponent a hme _ => exact hleaf _ (.simStep me p q opponent a hme)
  | botSimStep k me p q opponent a hme _ => exact hleaf _ (.botSimStep me p q opponent a hme)
  | botSearchStep k g ψ a b me opponent hme _ =>
      exact hleaf _ (.botSearchStep g ψ a b me opponent hme)
  | botSysSearchStep k defs i g ψ a b me opponent hme hget _ =>
      exact hleaf _ (.botSysSearchStep defs i g ψ a b me opponent hme hget)
  | botSysSimStep k defs i j a me opponent hme hget _ =>
      exact hleaf _ (.botSysSimStep defs i j a me opponent hme hget)
  | botSysSearchThenSearch k defs i k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hget _ _ _ _ =>
      exact hleaf _ (.botSysSearchThenSearch defs i k₁ k₂ ψ₁ ψ₂ c0 c1 q me opponent hme hget)
  | iteBranchSearch_t k g z a' c0 c1 ψ q me opponent hme _ =>
      exact hleaf _ (.iteBranchSearch_t g z a' c0 c1 ψ q me opponent hme)
  | searchThenSearch_t k k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme _ _ _ _ =>
      exact hleaf _ (.searchThenSearch_t k₁ k₂ ψ₁ ψ₂ c0 c1 q me opponent hme)
  | searchChain k g₁ ψ₁ e₁ L a me opponent hme _ =>
      exact hleaf _ (.searchChain g₁ ψ₁ e₁ L a me opponent hme)
  | ctxChain k hd L a me opponent hme _ => exact hleaf _ (.ctxChain hd L a me opponent hme)
  | searchElseChain k hd L a me opponent hme _ =>
      exact hleaf _ (.searchElseChain hd L a me opponent hme)
  | eqRefl k p _ => exact hleaf _ (.eqRefl p)
  | eqNeg k p q hne _ => exact hleaf _ (.eqNeg p q hne)
  | atomBoxImpl k kBox p q a hatom _ => exact hleaf _ (.atomBoxImpl kBox p q a hatom)
  -- ═══ propositional glue ═══
  | mp k m₁ m₂ φ α _ _ _ ih1 ih2 => exact ih1 ⨀ ih2
  | implTrans k φ ψ χ a b _ _ _ ih1 ih2 => exact C_trans ih1 ih2
  | weakenImpl k φ ψ m _ _ ih => exact C_of_conseq ih
  | impS2 φ ψ χ m₁ m₂ K _ _ _ ih1 ih2 => exact mdp₁ ih1 ih2
  | implRefl k φ _ => exact C_id
  | implK k φ ψ _ => exact implyK
  | implS k φ ψ χ _ => exact implyS
  | contrapose k φ ψ m _ _ ih => exact contra ih
  | negElim k φ ψ m₁ m₂ _ _ _ ih1 ih2 => exact of_O (neg_mdp ih1 ih2)
  -- ═══ the modal / Löb tier ═══
  | boxIntro kIn K φ _ _ ih => exact box_of_provable ih
  | axK a b c m K φ α _ _ _ ih => exact box_K_rule ih
  | axKf a b c K φ α _ _ => exact box_K _ _
  | box4 a b K φ _ _ => exact box_4 _
  | boxMono a b K φ _ _ => exact C_id
  | diagF pm fb g K tgt _ _ _ => exact diag_forward A g tgt
  | diagB pm fb g K tgt _ _ _ => exact diag_backward A g tgt

/-! ## Remark: the `atomBoxImpl` leaf under a Σ₁ realization

`atomBoxImpl` concludes `plays p q a → □(plays p q a)`, i.e. `tr` sends it to
`A p q a 🡒 provabilityPred 𝗣𝗔 (A p q a)`. When the realization is Σ₁ — `Hierarchy 𝚺 1 (A p q a)`,
as any honest arithmetization of "the bounded evaluator outputs `a`" is — this leaf needs no
hypothesis at all: it is formalized Σ₁-completeness, `provable_sigma_one_complete` (stated in
`𝗜𝚺₁`, lifted along `𝗜𝚺₁ ⪯ 𝗣𝗔`), certificate or not. Not built here: `A` is arbitrary in
T2-CORE, and the Σ₁ realization is T2-AGENT's business. -/

end ArithS.Core
