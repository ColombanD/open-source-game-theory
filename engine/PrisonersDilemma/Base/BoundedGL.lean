import PrisonersDilemma.Base.Loeb

/-!
# Base/BoundedGL — the abstract bounded-GL interface: `S`'s modal core as a structure (2026-08-27)

Promoted 2026-08-27 from `Research/Spikes/bounded_gl/BoundedGLSpike.lean` (the spike keeps
the `#print axioms` audit). Design record: `Research/Notes/DESIGN_CHOICES.md`, the
2026-08-27 entry — it closes the "interface formalization (middle path)" row of the
2026-08-20 entry "Why `S` is a RULE SET, not an arithmetized theory".

**What it is.** `BoundedGL Sent` packages the bounded modal schemes the engine's proofs of
Löbian cooperation rely on — budget-indexed necessitation, K-distribution, 4, upward
subscript monotonicity, and the Löb-premise-relative fixpoint legs — as the FIELDS of one
structure over an abstract sentence type, each with the EXACT transcript cost of the
same-named `Pf` constructor. It is "GL with proof-length-bounded modalities" (the framing
suggested by Foundation's maintainers on Zulip, #Formalized Formal Logic, 2026-08-27), not
a provability PREDICATE inside a first-order theory (Foundation's
`ProvabilityAbstraction.Provability`): `box` is a connective, and "provable in a theory" is
one interpretation of it.

**Contents.**
* `BoundedGL` — the structure (10 fields: `mono`, `mp`, `implTrans`, `impS2`, `boxIntro`,
  `axKf`, `box4`, `boxMono`, `diagF`, `diagB`) and the `Prop` mixin `BoundedGL.SizeExact`
  (the three `Formula.size` equations).
* `pfBoundedGL : BoundedGL Formula` — THE ENGINE IS A MODEL: every field is the constructor
  of the same name, verbatim (no eta wrappers, no cost slack); `pfBoundedGL_sizeExact`.
* `BoundedGL.mutual_loeb`, `BoundedGL.bloeb`, `BoundedGL.pblt`, `BoundedGL.pblt_bounded` —
  `Base/Loeb`'s `mutual_loeb` / `bloeb_engine` / `pblt_engine` / `pblt_engine_bounded`
  proved AGAINST THE STRUCTURE. `bloeb`/`mutual_loeb` use no size law at all.
* Four `example : @<engine theorem> = pfBoundedGL.<generic> := rfl` — statement-level
  identity: the engine's theorems ARE the `Pf` instances (proof irrelevance closes the
  `Eq`; the `Eq` only TYPECHECKS if the field binders match the constructors exactly —
  this is the drift canary).

**Field ↔ constructor** (`ProofSystem.lean`, family B glue and family C Löb machinery):
`mono` = `Pf_mono`; `mp`/`implTrans`/`impS2` = `Pf.mp`/`Pf.implTrans`/`Pf.impS2`;
`boxIntro` (HBL D1) / `axKf` (HBL D2, object form) / `box4` (HBL D3) / `boxMono` /
`diagF` / `diagB` = the same-named `Pf` constructors. Deliberately EXCLUDED: `neg` and the
propositional `contrapose`/`negElim`/`implK`/`implS`/`implRefl`/`weakenImpl` (unused by the
three theorems), the rule-form `axK` (unused; `axKf` + `mp` up to slack), and EVERY
source-reading rule (`atom`, `searchBranch`, `simStep`, …, `atomBoxImpl`) — the atom theory
is the model-specific half of `S` and stays per-rule.

**The gate is kept.** `diagF`/`diagB` demand a HELD Löb premise `Proves pm (imp (box fb tgt)
tgt)` and charge its transcript `pm`, unlike the textbook unconditional diagonal lemma.
Three reasons: it is strictly WEAKER as a scheme, so any ungated model discharges it a
fortiori (nothing is lost for a future arithmetized instance — state the ungated law, derive
the gated one by monotonicity); the generic derivation always holds `hLoeb` when it takes a
leg; and in the engine the gate is load-bearing for the exclusion censuses (`Base/Exclusion`
reaches the tail invariant on a leg's conclusion through the induction hypothesis ON THE
GATE PREMISE — an ungated leg would have no IH there).

**`SizeExact` is the ONE engine-specific commitment.** `Formula.size`-shaped costs
(`size (imp φ ψ) = |φ| + |ψ| + 1`, `size (box k φ) = numCost k + |φ| + 1`, same for
`diag`). Only the asymptotic wrappers `pblt`/`pblt_bounded` consult it — their 21
side-conditions are discharged by rewriting with these equations and `omega`. Inequality
laws with additive slack do NOT suffice (`omega` cannot see through the nested
`size (imp (diag g φ) …)` atoms; tested in the spike's design pass), and a Gödel-coded
model (`box k φ := Bew_k(⌜φ⌝)`, size LINEAR in `|φ|` with a constant) would not satisfy
even those — such a model gets `bloeb`/`mutual_loeb` for free and owes its own asymptotic
wrapper. That is a v2 item, recorded in the design note.

**NOT covered — deliberately.** SOUNDNESS (`Pf_sound` — an interp-level property, not a
scheme), the τ-INVOLUTION (`Base/Transpose`), and the TRANSPARENCY family (the reading
rules) are NOT fields: the 2026-08-20 row listed them, and the 2026-08-25 entry already
predicted the split (the transpose proof factors through soundness as an interface
property; the floor/census proofs use the cost stipulations DIRECTLY and never will).
Extending the interface with a soundness field is possible (`Proves k φ → interp φ` for a
`interp : Sent → Prop` datum) but buys nothing until a second model exists.

**Models and non-models.** `pfBoundedGL` is the one model. Candidate second model: the
Metatheory's `Type`-valued `ProvT` (`Decidability/T49TreeSubstrate.lean`) via
`Nonempty (ProvT k φ)` — same seven modal constructors; NOT here because `Metatheory` is a
separate lake target the engine never imports. NOT a model: the gated strata `PfG`
(`Decidability/T42PfB.lean`) — cuts are gated on the cut formula, so `mp` is not
dischargeable unconditionally. THE OPEN OBLIGATION: an arithmetized model over PA (a
budget-indexed provability predicate validating these ten schemes at these costs) — no
costed derivability conditions are formalized in any prover; Foundation's
`RestrictedProvability` (`∃ d < 2^e, Proof T d φ`, with the classical no-short-proof
lower bound for its Gödel sentence) is the closest object and has none of the schemes.
Its Solovay-style converse ("is this the complete logic of bounded provability?") is the
precise form of the faithfulness question of the 2026-08-20 entry.

**Provenance.** The pre-`Pf` attempt `Research/Spikes/pblt/PbltInterfaceSpike.lean`
(`structure BPS`, 2026-06) recorded `nec`/`boxMono`/`impI`/`diag` as undischargeable by the
then `Derivation`/`Provable` split; the transcript cost model (2026-07-02) and
`Formula.diag` (2026-07-01) dissolved every blocker — today each field is a constructor.
-/

open PD
namespace PD.BaseTheorems

/-- **Bounded GL, abstract**: budget-indexed modal schemes with explicit transcript costs,
    over an abstract sentence type. The `→/□/diag` fragment. Every field is the same-named
    `Pf` constructor of `ProofSystem.lean` with `Formula` replaced by `Sent` (binder shapes
    included — `mp`/`implTrans` carry an implicit output budget `{k}`, the rest an explicit
    `K`), so `pfBoundedGL` below is literally `mp := Pf.mp` etc. -/
structure BoundedGL (Sent : Type) where
  imp  : Sent → Sent → Sent
  box  : Nat → Sent → Sent
  diag : Nat → Sent → Sent
  size : Sent → Nat
  Proves : Nat → Sent → Prop
  /-- Budget monotonicity (`Pf_mono`). -/
  mono : ∀ {k₁ : Nat} {φ : Sent}, Proves k₁ φ → ∀ {k₂ : Nat}, k₁ ≤ k₂ → Proves k₂ φ
  /-- Modus ponens, transcript = both subtrees + conclusion (`Pf.mp`). -/
  mp : ∀ {k : Nat} (m₁ m₂ : Nat) (φ α : Sent),
    Proves m₁ (imp φ α) → Proves m₂ φ → m₁ + m₂ + size α ≤ k → Proves k α
  /-- Transitivity of implication (`Pf.implTrans`). -/
  implTrans : ∀ {k : Nat} (φ ψ χ : Sent) (a b : Nat),
    Proves a (imp φ ψ) → Proves b (imp ψ χ) → a + b + size (imp φ χ) ≤ k →
    Proves k (imp φ χ)
  /-- Closed S-composition (`Pf.impS2`). -/
  impS2 : ∀ (φ ψ χ : Sent) (m₁ m₂ K : Nat),
    Proves m₁ (imp φ (imp ψ χ)) → Proves m₂ (imp φ ψ) → m₁ + m₂ + size (imp φ χ) ≤ K →
    Proves K (imp φ χ)
  /-- Bounded necessitation, HBL D1 (`Pf.boxIntro`). -/
  boxIntro : ∀ (kIn K : Nat) (φ : Sent),
    Proves kIn φ → kIn + size (box kIn φ) ≤ K → Proves K (box kIn φ)
  /-- Bounded K-distribution as an object formula, HBL D2 (`Pf.axKf`). -/
  axKf : ∀ (a b c K : Nat) (φ α : Sent),
    a + b + size α ≤ c →
    size (imp (box a (imp φ α)) (imp (box b φ) (box c α))) ≤ K →
    Proves K (imp (box a (imp φ α)) (imp (box b φ) (box c α)))
  /-- Bounded 4 / object necessitation, HBL D3 (`Pf.box4`). -/
  box4 : ∀ (a b K : Nat) (φ : Sent),
    a + size (box a φ) ≤ b →
    size (imp (box a φ) (box b (box a φ))) ≤ K →
    Proves K (imp (box a φ) (box b (box a φ)))
  /-- Upward box-subscript monotonicity (`Pf.boxMono`). -/
  boxMono : ∀ (a b K : Nat) (φ : Sent),
    a ≤ b → size (imp (box a φ) (box b φ)) ≤ K → Proves K (imp (box a φ) (box b φ))
  /-- Löb-fixpoint leg, forward: `ψ → (□_g ψ → tgt)` for `ψ := diag g tgt`, GATED on a held
      Löb premise whose transcript it charges (`Pf.diagF`). -/
  diagF : ∀ (pm fb g K : Nat) (tgt : Sent),
    Proves pm (imp (box fb tgt) tgt) →
    pm + size (imp (diag g tgt) (imp (box g (diag g tgt)) tgt)) ≤ K →
    Proves K (imp (diag g tgt) (imp (box g (diag g tgt)) tgt))
  /-- Löb-fixpoint leg, backward: `(□_g ψ → tgt) → ψ` (`Pf.diagB`). -/
  diagB : ∀ (pm fb g K : Nat) (tgt : Sent),
    Proves pm (imp (box fb tgt) tgt) →
    pm + size (imp (imp (box g (diag g tgt)) tgt) (diag g tgt)) ≤ K →
    Proves K (imp (imp (box g (diag g tgt)) tgt) (diag g tgt))

/-- `Formula.size`-shaped cost laws (`Program.lean`, `Formula.size`). The ONE engine-specific
    commitment of the interface; only the asymptotic wrappers (`pblt`, `pblt_bounded`)
    consult it — `bloeb`/`mutual_loeb` are cost-shape-free. -/
structure BoundedGL.SizeExact {Sent : Type} (B : BoundedGL Sent) : Prop where
  size_imp  : ∀ φ ψ, B.size (B.imp φ ψ) = B.size φ + B.size ψ + 1
  size_box  : ∀ k φ, B.size (B.box k φ) = numCost k + B.size φ + 1
  size_diag : ∀ g φ, B.size (B.diag g φ) = numCost g + B.size φ + 1

/-- **The engine is a model.** Every field is the constructor of the same name — no eta
    wrappers, no cost slack. -/
def pfBoundedGL : BoundedGL Formula where
  imp := .impl
  box := .box
  diag := .diag
  size := Formula.size
  Proves := Pf
  mono := Pf_mono
  mp := Pf.mp
  implTrans := Pf.implTrans
  impS2 := Pf.impS2
  boxIntro := Pf.boxIntro
  axKf := Pf.axKf
  box4 := Pf.box4
  boxMono := Pf.boxMono
  diagF := Pf.diagF
  diagB := Pf.diagB

theorem pfBoundedGL_sizeExact : pfBoundedGL.SizeExact :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

namespace BoundedGL

variable {Sent : Type} (B : BoundedGL Sent)

/-- **Mutual bounded Löb premise, generic** — `Base/Loeb.mutual_loeb` with `Pf` replaced
    by `B.Proves`. From `legPD : □_kP A → B` and `legDP : □_kD B → A`, build `□_fb A → A`
    at the lowered subscript `fb`. -/
theorem mutual_loeb (A C : Sent) (kP kD fb n m c pA pB : Nat)
    (d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ K : Nat)
    (legPD : B.Proves pA (B.imp (B.box kP A) C))
    (legDP : B.Proves pB (B.imp (B.box kD C) A))
    (H1 : fb ≤ kP)
    (H2 : B.size (B.imp (B.box fb A) (B.box kP A)) ≤ d₁)
    (H3 : d₁ + pA + B.size (B.imp (B.box fb A) C) ≤ d₂)
    (H4 : d₂ ≤ n)
    (H5 : n + B.size (B.box n (B.imp (B.box fb A) C)) ≤ d₃)
    (H6 : n + m + B.size C ≤ c)
    (H7 : B.size (B.imp (B.box n (B.imp (B.box fb A) C))
            (B.imp (B.box m (B.box fb A)) (B.box c C))) ≤ d₄)
    (H8 : d₄ + d₃ + B.size (B.imp (B.box m (B.box fb A)) (B.box c C)) ≤ d₅)
    (H9 : fb + B.size (B.box fb A) ≤ m)
    (H10 : B.size (B.imp (B.box fb A) (B.box m (B.box fb A))) ≤ d₆)
    (H11 : d₆ + d₅ + B.size (B.imp (B.box fb A) (B.box c C)) ≤ d₇)
    (H12 : c ≤ kD)
    (H13 : B.size (B.imp (B.box c C) (B.box kD C)) ≤ d₈)
    (H14 : d₇ + d₈ + B.size (B.imp (B.box fb A) (B.box kD C)) ≤ d₉)
    (H15 : d₉ + pB + B.size (B.imp (B.box fb A) A) ≤ K) :
    B.Proves K (B.imp (B.box fb A) A) := by
  have s1 : B.Proves d₁ (B.imp (B.box fb A) (B.box kP A)) := B.boxMono fb kP d₁ A H1 H2
  have s2 : B.Proves d₂ (B.imp (B.box fb A) C) :=
    B.implTrans _ _ _ d₁ pA s1 legPD H3
  have s3 : B.Proves d₃ (B.box n (B.imp (B.box fb A) C)) :=
    B.boxIntro n d₃ _ (B.mono s2 H4) H5
  have s4 : B.Proves d₄ (B.imp (B.box n (B.imp (B.box fb A) C))
      (B.imp (B.box m (B.box fb A)) (B.box c C))) :=
    B.axKf n m c d₄ (B.box fb A) C H6 H7
  have s5 : B.Proves d₅ (B.imp (B.box m (B.box fb A)) (B.box c C)) :=
    B.mp d₄ d₃ _ _ s4 s3 H8
  have s6 : B.Proves d₆ (B.imp (B.box fb A) (B.box m (B.box fb A))) :=
    B.box4 fb m d₆ A H9 H10
  have s7 : B.Proves d₇ (B.imp (B.box fb A) (B.box c C)) :=
    B.implTrans _ _ _ d₆ d₅ s6 s5 H11
  have s8 : B.Proves d₈ (B.imp (B.box c C) (B.box kD C)) := B.boxMono c kD d₈ C H12 H13
  have s9 : B.Proves d₉ (B.imp (B.box fb A) (B.box kD C)) :=
    B.implTrans _ _ _ d₇ d₈ s7 s8 H14
  exact B.implTrans _ _ _ d₉ pB s9 legDP H15

/-- **Bounded Löb, generic** — `Base/Loeb.bloeb_engine` against the interface: the 14-step
    internalized GL derivation from the tight premise `□_fb φ → φ`, fixpoint at the free
    subscript `g` (`H19 : c₁₃ ≤ g` absorbs the fixpoint's whole transcript). Uses only
    `diagF/diagB/boxIntro/axKf/box4/boxMono/implTrans/impS2/mp/mono` — no size law. -/
theorem bloeb (φ : Sent) (pm fb g n₁ n₃ n₄ n₅ : Nat)
    (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ c₁₄ K : Nat)
    (hLoeb : B.Proves pm (B.imp (B.box fb φ) φ))
    (H1 : pm + B.size (B.imp (B.diag g φ) (B.imp (B.box g (B.diag g φ)) φ)) ≤ c₁)
    (H2 : pm + B.size (B.imp (B.imp (B.box g (B.diag g φ)) φ) (B.diag g φ)) ≤ c₂)
    (H3 : c₁ ≤ n₁)
    (H4 : n₁ + B.size (B.box n₁ (B.imp (B.diag g φ) (B.imp (B.box g (B.diag g φ)) φ))) ≤ c₃)
    (H5 : n₁ + g + B.size (B.imp (B.box g (B.diag g φ)) φ) ≤ n₃)
    (H6 : B.size (B.imp (B.box n₁ (B.imp (B.diag g φ) (B.imp (B.box g (B.diag g φ)) φ)))
            (B.imp (B.box g (B.diag g φ)) (B.box n₃ (B.imp (B.box g (B.diag g φ)) φ)))) ≤ c₄)
    (H7 : c₄ + c₃ + B.size (B.imp (B.box g (B.diag g φ))
            (B.box n₃ (B.imp (B.box g (B.diag g φ)) φ))) ≤ c₅)
    (H8 : n₃ + n₄ + B.size φ ≤ n₅)
    (H9 : B.size (B.imp (B.box n₃ (B.imp (B.box g (B.diag g φ)) φ))
            (B.imp (B.box n₄ (B.box g (B.diag g φ))) (B.box n₅ φ))) ≤ c₆)
    (H10 : g + B.size (B.box g (B.diag g φ)) ≤ n₄)
    (H11 : B.size (B.imp (B.box g (B.diag g φ)) (B.box n₄ (B.box g (B.diag g φ)))) ≤ c₇)
    (H12 : c₅ + c₆ + B.size (B.imp (B.box g (B.diag g φ))
            (B.imp (B.box n₄ (B.box g (B.diag g φ))) (B.box n₅ φ))) ≤ c₈)
    (H13 : c₈ + c₇ + B.size (B.imp (B.box g (B.diag g φ)) (B.box n₅ φ)) ≤ c₉)
    (H14 : n₅ ≤ fb)
    (H15 : B.size (B.imp (B.box n₅ φ) (B.box fb φ)) ≤ c₁₀)
    (H16 : c₉ + c₁₀ + B.size (B.imp (B.box g (B.diag g φ)) (B.box fb φ)) ≤ c₁₁)
    (H17 : c₁₁ + pm + B.size (B.imp (B.box g (B.diag g φ)) φ) ≤ c₁₂)
    (H18 : c₂ + c₁₂ + B.size (B.diag g φ) ≤ c₁₃)
    (H19 : c₁₃ ≤ g)
    (H20 : g + B.size (B.box g (B.diag g φ)) ≤ c₁₄)
    (H21 : c₁₂ + c₁₄ + B.size φ ≤ K) :
    B.Proves K φ := by
  have legF : B.Proves c₁ (B.imp (B.diag g φ) (B.imp (B.box g (B.diag g φ)) φ)) :=
    B.diagF pm fb g c₁ φ hLoeb H1
  have legB : B.Proves c₂ (B.imp (B.imp (B.box g (B.diag g φ)) φ) (B.diag g φ)) :=
    B.diagB pm fb g c₂ φ hLoeb H2
  have hnec : B.Proves c₃ (B.box n₁ (B.imp (B.diag g φ) (B.imp (B.box g (B.diag g φ)) φ))) :=
    B.boxIntro n₁ c₃ _ (B.mono legF H3) H4
  have hK1 : B.Proves c₄ (B.imp (B.box n₁ (B.imp (B.diag g φ) (B.imp (B.box g (B.diag g φ)) φ)))
      (B.imp (B.box g (B.diag g φ)) (B.box n₃ (B.imp (B.box g (B.diag g φ)) φ)))) :=
    B.axKf n₁ g n₃ c₄ (B.diag g φ) (B.imp (B.box g (B.diag g φ)) φ) H5 H6
  have h2 : B.Proves c₅ (B.imp (B.box g (B.diag g φ)) (B.box n₃ (B.imp (B.box g (B.diag g φ)) φ))) :=
    B.mp c₄ c₃ _ _ hK1 hnec H7
  have hK2 : B.Proves c₆ (B.imp (B.box n₃ (B.imp (B.box g (B.diag g φ)) φ))
      (B.imp (B.box n₄ (B.box g (B.diag g φ))) (B.box n₅ φ))) :=
    B.axKf n₃ n₄ n₅ c₆ (B.box g (B.diag g φ)) φ H8 H9
  have hfour : B.Proves c₇ (B.imp (B.box g (B.diag g φ)) (B.box n₄ (B.box g (B.diag g φ)))) :=
    B.box4 g n₄ c₇ (B.diag g φ) H10 H11
  have h4 : B.Proves c₈ (B.imp (B.box g (B.diag g φ))
      (B.imp (B.box n₄ (B.box g (B.diag g φ))) (B.box n₅ φ))) :=
    B.implTrans _ _ _ c₅ c₆ h2 hK2 H12
  have h6 : B.Proves c₉ (B.imp (B.box g (B.diag g φ)) (B.box n₅ φ)) :=
    B.impS2 _ _ _ c₈ c₇ c₉ h4 hfour H13
  have hmono : B.Proves c₁₀ (B.imp (B.box n₅ φ) (B.box fb φ)) :=
    B.boxMono n₅ fb c₁₀ φ H14 H15
  have h6' : B.Proves c₁₁ (B.imp (B.box g (B.diag g φ)) (B.box fb φ)) :=
    B.implTrans _ _ _ c₉ c₁₀ h6 hmono H16
  have hE : B.Proves c₁₂ (B.imp (B.box g (B.diag g φ)) φ) :=
    B.implTrans _ _ _ c₁₁ pm h6' hLoeb H17
  have hF : B.Proves c₁₃ (B.diag g φ) := B.mp c₂ c₁₂ _ _ legB hE H18
  have hG : B.Proves c₁₄ (B.box g (B.diag g φ)) :=
    B.boxIntro g c₁₄ _ (B.mono hF H19) H20
  exact B.mp c₁₂ c₁₄ _ _ hE hG H21

/-- **Parametric bounded Löb (PBLT), generic** — `Base/Loeb.pblt_engine` against the
    interface. The only place the size laws enter: the 21 side-conditions of `bloeb` are
    discharged by rewriting with `hS` and `omega`. -/
theorem pblt (hS : B.SizeExact) (φ : Nat → Sent) (f pm : Nat → Nat) (k₁ : Nat)
    (hLoeb : ∀ k, k > k₁ → B.Proves (pm k) (B.imp (B.box (f k) (φ k)) (φ k)))
    (hsz : ∀ k, k > k₁ → 8192 * (pm k + B.size (φ k) + Nat.log2 (f k) + 8) ≤ f k) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, B.Proves m (φ k) := by
  refine ⟨k₁, fun k hk => ?_⟩
  obtain ⟨W, hW⟩ : ∃ W, W = pm k + B.size (φ k) + Nat.log2 (f k) + 8 := ⟨_, rfl⟩
  have hWk : 8192 * W ≤ f k := hW ▸ hsz k hk
  have hlg : Nat.log2 (1024 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₁ : Nat.log2 (32 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₃ : Nat.log2 (2048 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₅ : Nat.log2 (8192 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  refine ⟨4096 * W, B.bloeb (φ k) (pm k) (f k)
    (1024 * W) (32 * W) (2048 * W) (2048 * W) (8192 * W)
    (16 * W) (16 * W) (64 * W) (32 * W) (128 * W) (32 * W) (16 * W)
    (256 * W) (512 * W) (16 * W) (640 * W) (704 * W) (768 * W) (2048 * W) (4096 * W)
    (hLoeb k hk)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
  · (try simp only [hS.size_imp, hS.size_box, hS.size_diag, numCost]); omega

/-- **PBLT, budget-carrying, generic** — `Base/Loeb.pblt_engine_bounded`. -/
theorem pblt_bounded (hS : B.SizeExact) (φ : Nat → Sent) (f pm : Nat → Nat) (k₁ : Nat)
    (hLoeb : ∀ k, k > k₁ → B.Proves (pm k) (B.imp (B.box (f k) (φ k)) (φ k)))
    (hsz : ∀ k, k > k₁ → 8192 * (pm k + B.size (φ k) + Nat.log2 (f k) + 8) ≤ f k) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, 2 * m ≤ f k ∧ B.Proves m (φ k) := by
  refine ⟨k₁, fun k hk => ?_⟩
  obtain ⟨W, hW⟩ : ∃ W, W = pm k + B.size (φ k) + Nat.log2 (f k) + 8 := ⟨_, rfl⟩
  have hWk : 8192 * W ≤ f k := hW ▸ hsz k hk
  have hlg : Nat.log2 (1024 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₁ : Nat.log2 (32 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₃ : Nat.log2 (2048 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₅ : Nat.log2 (8192 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  refine ⟨4096 * W, by omega, B.bloeb (φ k) (pm k) (f k)
    (1024 * W) (32 * W) (2048 * W) (2048 * W) (8192 * W)
    (16 * W) (16 * W) (64 * W) (32 * W) (128 * W) (32 * W) (16 * W)
    (256 * W) (512 * W) (16 * W) (640 * W) (704 * W) (768 * W) (2048 * W) (4096 * W)
    (hLoeb k hk)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
  · (try simp only [hS.size_imp, hS.size_box, hS.size_diag, numCost]); omega

end BoundedGL

/-! ### The engine's theorems ARE the `Pf` instances

Statement-level identity: each `Eq` typechecks only if the generic theorem instantiated at
`pfBoundedGL` has DEFINITIONALLY the engine theorem's type (binder shapes and all);
proof irrelevance then makes the proofs equal by `rfl`. These are the canary for any drift
between the interface's fields and the constructors. -/

example : @mutual_loeb = pfBoundedGL.mutual_loeb := rfl
example : @bloeb_engine = pfBoundedGL.bloeb := rfl
example : @pblt_engine = pfBoundedGL.pblt pfBoundedGL_sizeExact := rfl
example : @pblt_engine_bounded = pfBoundedGL.pblt_bounded pfBoundedGL_sizeExact := rfl

end PD.BaseTheorems
