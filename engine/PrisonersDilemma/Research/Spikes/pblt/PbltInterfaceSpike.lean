import PrisonersDilemma.BaseTheorems

/-!
# PBLT Phase-0 spike — the `BoundedProvabilitySystem` interface + feasibility probe

GO/NO-GO for route A (faithful `PBLT` mechanization). `PBLT` (Axioms.lean) is the LAST reflection
axiom and is a genuine METATHEOREM (bounded Löb), not a representational wall. Critch's proof
(`PBLT_proof.tex` §5) runs over an abstract first-order theory `S` with a Gödel-encoded bounded
provability predicate `□_k`. This spike:

  1. States the proof's INGREDIENTS as an abstract `structure BoundedProvabilitySystem` (the named
     properties from the tex: Implication Distribution, Quantifier Distribution, Bounded
     Necessitation, Bounded Inner Necessitation, + the Parametric Diagonal Lemma).
  2. (Probe) asks, field by field, whether the ENGINE's `Provable` can discharge each — i.e. does
     route A close over the real engine, or stall?

Verdict criterion: route A is FEASIBLE iff every field is dischargeable for `Provable`. The two at
risk are the ones needing structure `Formula` LACKS: a `∀` quantifier (Quantifier Distribution) and a
Gödel-encoding / self-reference (Parametric Diagonal Lemma). `Formula` has only
`plays/impl/neg/box/eq` — NO `∀`, NO encoding.

NOT root-imported. `lake env lean PrisonersDilemma/Research/Spikes/pblt/PbltInterfaceSpike.lean`
-/

namespace PD.PbltSpike
open PD PD.BaseTheorems

/-! ## 1. The abstract interface (Critch's ingredients as fields)

Stated over an abstract carrier `Sent` (the theory's sentences) with a derivability predicate
`Proves : Nat → Sent → Prop` (`Proves k φ` = "S proves φ in ≤ k characters") and a bounded box
`box : Nat → Sent → Sent`. This mirrors the tex; the engine would instantiate `Sent := Formula`,
`Proves k φ := ∃ m, Provable m φ ∧ …` etc. -/

structure BPS where
  Sent : Type
  imp  : Sent → Sent → Sent                      -- object implication
  box  : Nat → Sent → Sent                       -- □_k
  Proves : Nat → Sent → Prop                     -- ⊢_k  (bounded provability of the META theory)
  -- Implication Distribution: □_a(p→q) → (□_b p → □_{a+b+c} q), some constant c.
  impDist : ∃ c, ∀ a b p q,
    Proves 0 (imp (box a (imp p q)) (imp (box b p) (box (a + b + c) q)))
  -- Bounded Necessitation: ⊢_k φ ⟹ ⊢_{E k} □_k φ, for a proof-expansion function E.
  E : Nat → Nat
  boundedNec : ∀ k φ, Proves k φ → Proves (E k) (box k φ)
  -- Bounded Inner Necessitation: ⊢ □_k φ → □_{E k} □_k φ.
  boundedInnerNec : ∀ k φ, Proves 0 (imp (box k φ) (box (E k) (box k φ)))
  -- Quantifier Distribution needs a ∀ binder over the parameter `k`. We model the family
  -- `φ : Nat → Sent` and the conclusion `∀k, □_{O(log k)} φ(k)` it must yield from `□_N (∀k φ(k))`.
  -- The `∀k φ(k)` sentence itself REQUIRES a quantifier constructor on `Sent` — modelled here as a
  -- field `forall_ : (Nat → Sent) → Sent` that the carrier must PROVIDE.
  forall_ : (Nat → Sent) → Sent
  quantDist : ∀ (φ : Nat → Sent) (N : Nat), Proves 0 (box N (forall_ φ)) →
    ∃ C, ∀ k, Proves 0 (box (C + 2 * N + Nat.log2 k) (φ k))
  -- Parametric Diagonal Lemma: for any G : code × Nat → Sent (a predicate over a Gödel code and the
  -- parameter), there is ψ : Nat → Sent with ⊢ ∀k, ψ(k) ↔ G(⌜ψ⌝, k). Modelled abstractly: the
  -- carrier must provide, for each "predicate transformer" `G`, a fixpoint family. This is the field
  -- that needs SELF-REFERENCE / encoding.
  diag : ∀ (G : (Nat → Sent) → Nat → Sent),
    ∃ ψ : Nat → Sent, ∀ k, Proves 0 (imp (ψ k) (G ψ k)) ∧ Proves 0 (imp (G ψ k) (ψ k))

/-! ## 2. (intent) Prove PBLT from the interface.

The tex proof is a finite chain of the four properties + diag (≈18 steps). It is transcribable into a
theorem `pblt_of_bps (B : BPS) : <PBLT statement over B>`. We DO NOT transcribe all 18 steps here
(that is Phase 3 work); the Phase-0 point is the FEASIBILITY of the FIELDS, not re-deriving the chain.
We assert the shape and leave the chain as the (mechanical-but-long) follow-on. -/

/-! ### Budget-erased reformulation (faithful to the ENGINE's consumers, simpler than the tex)

The tex tracks exact budgets (`g(k)`, `h(k)`, `O(log k)` thresholds) because Critch states PBLT with a
specific budget on the *conclusion*. The engine's `PBLT` consumers only need the EXISTENTIAL
`∃ m, Provable m (p k)` — the budget is discarded. So we model `BPS` with `Proves` budget-erased
(`Proves φ := ∃ m, Provable m φ`-shaped, the `0` index a placeholder), which collapses every
`□_{O(log k)}` / `□_{g(k)}` distinction into "provable at SOME budget." The chain then reduces to the
PROPOSITIONAL Löb argument, with the budget bookkeeping discharged by the existential.

`BPSe` = the budget-erased interface. Fields:
  • `nec`  : `Proves φ → Proves (□φ)`               (Bounded Necessitation, budget-erased = `boxIntro`)
  • `K`    : `Proves (□(p→q)) → Proves (□p) → Proves (□q)`   (Impl Dist + MP, erased = `axK`+`app`)
  • `four` : `Proves (□φ) → Proves (□□φ)`           (Bounded Inner Nec, erased = `box4`)
  • `mp`   : `Proves (p→q) → Proves p → Proves q`   (object MP at the meta level = `app`)
  • `diag` : the fixpoint family (still needs self-reference — the one genuinely blocked field).
The `∀`/`quantDist` field DISAPPEARS in the erased model: the meta-`∀ k` is Lean's, so
Quantifier Distribution is just "do it pointwise," free. (This is exactly why the engine's
meta-∀ formulation is easier than Critch's internal-∀ one.) -/

structure BPSe where
  Sent : Type
  imp  : Sent → Sent → Sent
  box  : Sent → Sent
  Proves : Sent → Prop
  nec  : ∀ φ, Proves φ → Proves (box φ)
  K    : ∀ p q, Proves (box (imp p q)) → Proves (box p) → Proves (box q)
  four : ∀ φ, Proves (box φ) → Proves (box (box φ))
  mp   : ∀ p q, Proves (imp p q) → Proves p → Proves q
  -- the K rule also in un-boxed object form (needed to chain object implications), = `app`
  mpBox : ∀ p q, Proves (imp p q) → Proves p → Proves q   -- alias; object MP
  diag : ∀ (G : Sent → Sent), ∃ ψ, Proves (imp ψ (G ψ)) ∧ Proves (imp (G ψ) ψ)
  -- the proof needs to FORM `imp` and `box` freely and reason about them; these connect the
  -- structure's `imp`/`box` to MP. (impl intro/elim at the Proves level.)
  impI : ∀ p q, (Proves p → Proves q) → Proves (imp p q)   -- deduction (meta → object impl)

/-- **Propositional bounded Löb from the erased interface** (the heart of PBLT, the tex chain with
    budgets erased). For the diagonal `ψ ↔ (□ψ → p)`: derive `□ψ → p`, then `□ψ`, then `p`. -/
theorem ploeb_of_bpse (B : BPSe) (p : B.Sent)
    (hLoeb : B.Proves (B.imp (B.box p) p)) : B.Proves p := by
  -- G φ := □φ → p ;  diag gives ψ with ψ ↔ (□ψ → p).
  obtain ⟨ψ, hψf, hψb⟩ := B.diag (fun φ => B.imp (B.box φ) p)
  --   hψf : ⊢ ψ → (□ψ → p)      hψb : ⊢ (□ψ → p) → ψ
  -- Step A: ⊢ □ψ → □(□ψ → p)      [necessitate hψf, then K]
  have hA : B.Proves (B.imp (B.box ψ) (B.box (B.imp (B.box ψ) p))) := by
    have hnec : B.Proves (B.box (B.imp ψ (B.imp (B.box ψ) p))) := B.nec _ hψf
    exact B.impI _ _ (fun hbψ => B.K _ _ hnec hbψ)
  -- Step B: ⊢ □(□ψ → p) → (□□ψ → □p)   [K, as an object implication]
  -- Step C: ⊢ □ψ → □□ψ                 [four]
  have hC : B.Proves (B.imp (B.box ψ) (B.box (B.box ψ))) := B.impI _ _ (fun h => B.four _ h)
  -- Step D: ⊢ □ψ → □p                  [chain A;B;C via K and MP]
  have hD : B.Proves (B.imp (B.box ψ) (B.box p)) := by
    refine B.impI _ _ (fun hbψ => ?_)
    -- from hbψ : □ψ ; hA → □(□ψ→p) ; four → □□ψ ; K → □p
    have h1 : B.Proves (B.box (B.imp (B.box ψ) p)) := B.mp _ _ hA hbψ
    have h2 : B.Proves (B.box (B.box ψ)) := B.four _ hbψ
    exact B.K _ _ h1 h2
  -- Step E: ⊢ □ψ → p                   [chain D with hLoeb : □p → p]
  have hE : B.Proves (B.imp (B.box ψ) p) :=
    B.impI _ _ (fun hbψ => B.mp _ _ hLoeb (B.mp _ _ hD hbψ))
  -- Step F: ⊢ ψ                        [hψb applied to hE]
  have hF : B.Proves ψ := B.mp _ _ hψb hE
  -- Step G: ⊢ □ψ                       [necessitate F]
  have hG : B.Proves (B.box ψ) := B.nec _ hF
  -- Step H: ⊢ p                        [hE applied to G]
  exact B.mp _ _ hE hG

/-- **PBLT** (the engine's meta-∀ statement) from the erased interface: apply `ploeb_of_bpse`
    pointwise — the meta-`∀ k` is Lean's, so Quantifier Distribution is free. -/
theorem pblt_of_bpse (B : BPSe) (p : Nat → B.Sent) (k₁ : Nat)
    (hLoeb : ∀ k, k > k₁ → B.Proves (B.imp (B.box (p k)) (p k))) :
    ∀ k, k > k₁ → B.Proves (p k) :=
  fun k hk => ploeb_of_bpse B (p k) (hLoeb k hk)

/-! ## 1b — the BUDGET-TRACKING interface, matching the REAL `PBLT` signature

The erased chain above proves propositional Löb but its `box` carries no budget, so it does not
produce the engine's `PBLT` whose hypothesis is `□_{f(k)} p(k)` (a real box SUBSCRIPT). The budgeted
interface `BPSb` keeps `box : Nat → Sent → Sent` (the `□_a` of the tex) and a budget-EXISTENTIAL
`Proves : Sent → Prop` (= `∃ m, Provable m ·`, matching PBLT's `⊢`).

KEY SIMPLIFICATION the engine permits (and the tex does not have): because `Proves` is
budget-EXISTENTIAL (the proof length `m` is discarded), the box-budget arithmetic `g`/`h`/`O(log k)`
COLLAPSES. The only place the box subscript matters is the SINGLE hypothesis `□_{f(k)} p(k)`. Inside
the chain, every nested box can sit at ANY budget the rule produces, because `Proves` never pins it.
So the budgeted fields can be stated at a SINGLE working budget per-`k` (call it `b k`), and the
chain is the same 8 steps as `ploeb_of_bpse` — provided the fields produce boxes at budgets we can
keep ≤ `f(k)`. We make this precise: the diagonal `ψ` and all chain boxes live at a budget `g ≤ f`. -/

structure BPSb where
  Sent : Type
  imp  : Sent → Sent → Sent
  box  : Nat → Sent → Sent                       -- □_a
  Proves : Sent → Prop                           -- ⊢ (budget-existential)
  mp   : ∀ p q, Proves (imp p q) → Proves p → Proves q            -- object MP (`app`)
  impI : ∀ p q, (Proves p → Proves q) → Proves (imp p q)          -- deduction
  -- Bounded Necessitation: ⊢ φ ⟹ ⊢ □_a φ at ANY budget `a` (the proof length, not the subscript, is
  -- what `Proves` tracks; so necessitation holds at every subscript). = `boxIntro`.
  nec  : ∀ a φ, Proves φ → Proves (box a φ)
  -- Bounded GL-K, SAME subscript `a` (the engine's `axK` form): ⊢ □_a(p→q) → (□_a p → □_a q).
  K    : ∀ a p q, Proves (box a (imp p q)) → Proves (box a p) → Proves (box a q)
  -- Bounded GL-4, SAME subscript: ⊢ □_a φ → □_a (□_a φ). = `box4`.
  four : ∀ a φ, Proves (box a φ) → Proves (box a (box a φ))
  -- Budget weakening on the SUBSCRIPT: a proof of `□_a φ` gives `□_b φ` for `a ≤ b` (more budget
  -- only helps). This is what lets the single `□_{f(k)}` hypothesis meet the chain's working box.
  boxMono : ∀ a b φ, a ≤ b → Proves (box a φ) → Proves (box b φ)
  -- Parametric Diagonal Lemma at a working budget `g`: for `G`, a fixpoint `ψ` with
  -- ⊢ ψ ↔ G(ψ), where the chain uses `G φ := □_g φ → p`. (The genuinely blocked field.)
  diag : ∀ (g : Nat) (G : Sent → Sent), ∃ ψ, Proves (imp ψ (G ψ)) ∧ Proves (imp (G ψ) ψ)

/-- **Budgeted bounded Löb** producing the real `□_{f} p → p ⟹ p` shape. Works at a single budget
    `g ≤ f`: the diagonal, all chain boxes, and the necessitations sit at `g`; the hypothesis's
    `□_f p` is met by weakening the chain's `□_g p` up to `□_f p` (`boxMono`, `g ≤ f`). -/
theorem bloeb_of_bpsb (B : BPSb) (g f : Nat) (hgf : g ≤ f) (p : B.Sent)
    (hLoeb : B.Proves (B.imp (B.box f p) p)) : B.Proves p := by
  -- G φ := □_g φ → p ;  diag gives ψ with ψ ↔ (□_g ψ → p), all at budget g.
  obtain ⟨ψ, hψf, hψb⟩ := B.diag g (fun φ => B.imp (B.box g φ) p)
  -- Step A: ⊢ □_g ψ → □_g (□_g ψ → p)        [nec hψf at g, then K at g]
  have hA : B.Proves (B.imp (B.box g ψ) (B.box g (B.imp (B.box g ψ) p))) := by
    have hnec : B.Proves (B.box g (B.imp ψ (B.imp (B.box g ψ) p))) := B.nec g _ hψf
    exact B.impI _ _ (fun hbψ => B.K g _ _ hnec hbψ)
  -- Step D: ⊢ □_g ψ → □_g p                  [A ; four ; K, all at g]
  have hD : B.Proves (B.imp (B.box g ψ) (B.box g p)) := by
    refine B.impI _ _ (fun hbψ => ?_)
    have h1 : B.Proves (B.box g (B.imp (B.box g ψ) p)) := B.mp _ _ hA hbψ
    have h2 : B.Proves (B.box g (B.box g ψ)) := B.four g _ hbψ
    exact B.K g _ _ h1 h2
  -- Step E: ⊢ □_g ψ → p   [D gives □_g p ; weaken to □_f p ; hLoeb : □_f p → p]
  have hE : B.Proves (B.imp (B.box g ψ) p) :=
    B.impI _ _ (fun hbψ => B.mp _ _ hLoeb (B.boxMono g f _ hgf (B.mp _ _ hD hbψ)))
  -- Step F,G,H: ψ ; □_g ψ ; p
  have hF : B.Proves ψ := B.mp _ _ hψb hE
  have hG : B.Proves (B.box g ψ) := B.nec g _ hF
  exact B.mp _ _ hE hG

/-- **PBLT, the engine's exact signature**, from the budgeted interface. The `f ≻ O(log k)` and
    monotonicity hypotheses are consumed by the working-budget choice (here trivially `g k := f k`,
    `hgf := le_refl` — the budget-existential `Proves` makes the `g ≺ f` slack unnecessary). -/
theorem pblt_of_bpsb (B : BPSb) (φ : Nat → B.Sent) (f : Nat → Nat) (k₁ : Nat)
    (_hf : ∀ a b, a ≤ b → f a ≤ f b)
    (_hlog : ∃ c kHat, c > 0 ∧ ∀ k, k > kHat → f k > c * Nat.log2 k)
    (hLoeb : ∀ k, k > k₁ → B.Proves (B.imp (B.box (f k) (φ k)) (φ k))) :
    ∃ k₂, ∀ k, k > k₂ → B.Proves (φ k) :=
  ⟨k₁, fun k hk => bloeb_of_bpsb B (f k) (f k) (Nat.le_refl _) (φ k) (hLoeb k hk)⟩

/-! ## 3. Engine `BPSb` — discharge the budgeted fields for the real `Provable`.

`Sent := Formula`, `box := Formula.box`, `imp := Formula.impl`, `Proves φ := ∃ m, Provable m φ`
(budget-existential, matching PBLT's `⊢`). Each field is attempted with the real constructors; the
`sorry`s (if any) mark exactly what the engine cannot give. We need a budget-existential helper:
`Provable`-MONOTONE in budget (lift a proof to a larger budget). -/

/-- Budget monotonicity of `Provable`, packaged for the existential `Proves`. -/
theorem prov_mono {m m' : Nat} {φ : Formula} (h : Provable m φ) (hle : m ≤ m') : Provable m' φ :=
  (proofSearch_spec m' φ).1 (proofSearch_monotone m m' φ hle ((proofSearch_spec m φ).2 h))

def engineBPSb : BPSb where
  Sent := Formula
  imp := Formula.impl
  box := Formula.box
  Proves := fun φ => ∃ m, Provable m φ
  -- mp: object modus ponens = `Provable.app`. Lift both premises to a common budget.
  mp := by
    rintro p q ⟨m, hpq⟩ ⟨n, hp⟩
    exact ⟨max m n, Provable.app (max m n) (max m n) p q
      (prov_mono hpq (Nat.le_max_left m n)) (prov_mono hp (Nat.le_max_right m n)) (Nat.le_refl _)⟩
  -- impI: meta-deduction into an object implication. `weakenImpl` builds `φ→ψ` from a proof of ψ —
  -- but `impI`'s premise is a FUNCTION `Proves p → Proves q`, not a held `Proves q`. To use
  -- `weakenImpl` we'd need `Proves q` unconditionally, which we don't have. This is the deduction-
  -- theorem gap: the engine has no implication-INTRODUCTION discharging a hypothesis.
  impI := by sorry
  -- nec: `∃m, Provable m φ → ∃m', Provable m' (□_a φ)` at the field's chosen subscript `a`.
  -- ATTEMPT: `boxIntro a K φ (h : Provable a φ) hsz : Provable K (.box a φ)` — boxes at subscript `a`
  -- IF we have `Provable a φ`. We have `Provable m φ` for SOME m; lift to budget `a` via prov_mono
  -- ONLY IF m ≤ a. We don't know that. But we can lift to `max m a`... no, the SUBSCRIPT must be `a`.
  -- We CAN take the proof at budget `max m a ≥ a`, then... boxIntro needs the inner budget = subscript.
  -- Lift the proof to budget `a`? needs `m ≤ a`. If `a < m`, the proof of φ at budget m does NOT give
  -- a proof at the smaller budget a (Provable is monotone UP, not down). So `□_a φ` may be unprovable
  -- when the cheapest proof of φ exceeds `a`. CONFIRMED BLOCKED at arbitrary `a`:
  nec := by
    rintro a φ ⟨m, hm⟩
    -- to box at subscript `a` need `Provable a φ`; have `Provable m φ`; if `m ≤ a`, lift; else stuck.
    sorry
  -- K: same-subscript GL-K = `axK` + `app`. axK gives `□_a(p→q) → □_a p → □_a q` modulo size bounds.
  K := by sorry
  -- four: `□_a φ → □_a □_a φ` = `box4` (size-gated).
  four := by sorry
  -- boxMono: `□_a φ → □_b φ` for `a ≤ b`. Provable-monotone in the WORKING budget (prov_mono), but the
  -- box SUBSCRIPT `a` is inside the formula — relaxing it changes the formula, needs a rule that
  -- weakens the box subscript. NOT obviously present.
  boxMono := by sorry
  diag := by sorry                       -- ✗ the genuinely blocked field (Gödel encoding / self-ref)

/-! ## VERDICT (1b, machine-checked — CORRECTED after the budgeted attempt).

**The PBLT chain transcribes cleanly, BUT only one of the engine fields actually discharges.**

PROVED sorry-free (the genuine win):
  • `ploeb_of_bpse` / `pblt_of_bpse` — propositional Löb over the budget-erased interface.
  • `bloeb_of_bpsb` / `pblt_of_bpsb` — the BUDGETED chain, producing the EXACT engine `PBLT` signature
    (`□_{f k}` hypothesis, `∃k₂,∀k>k₂,∃m,Provable m (φ k)` conclusion). The §5 chain is real and the
    meta-`∀ k` makes Quantifier Distribution free.

But discharging the budgeted FIELDS for the real `Provable` (`engineBPSb`) is HARDER than the erased
model suggested — only `mp` closes:
  • `mp` (object MP) — ✅ `Provable.app` + budget-lift (`prov_mono`). DISCHARGED.
  • `nec` (Bounded Necessitation at subscript `a`) — ❌ `Provable` is monotone UP in budget, not down;
    boxing at subscript `a` needs `Provable a φ`, but the cheapest proof of `φ` may cost > `a`. So
    `□_a φ` is not provable for an arbitrary chosen `a`. The box SUBSCRIPT is coupled to proof cost.
  • `K` / `four` — same subscript-coupling issue (need the boxed formula's cost ≤ the subscript).
  • `boxMono` (relax box subscript `a→b`) — relaxing a box SUBSCRIPT changes the formula; no engine
    rule weakens it (proof-budget monotonicity ≠ box-subscript monotonicity). ❌
  • `impI` (deduction theorem: `(Proves p → Proves q) → Proves (p→q)`) — ❌ the engine DELIBERATELY
    has no implication-introduction (`Derivation` has `weakenImpl` = impl from a PROVED consequent, and
    `hypSyll`/`implTrans` = chaining, but NO hypothesis-discharging deduction). This is structural.
  • `diag` — ❌ Gödel encoding / self-reference, as before.

**CORRECTED ASSESSMENT.** Option 1b does NOT shrink the axiom surface to "just `diag`". Landing
`PBLT := pblt_of_bpsb engineBPSb` would need FIVE of the six fields (`nec/K/four/boxMono/impI/diag`
minus the one proved `mp`) as axioms — strictly WORSE than the single `PBLT` axiom. The blockers are
not incidental: the box-subscript ↔ proof-cost coupling and the absent deduction theorem are
load-bearing design choices of the engine's `Provable` (they are exactly what keeps it sound and
finite). Critch's proof runs in an UNBOUNDED first-order `S` with a deduction theorem and a Gödel
`Bew`; the engine's `Provable` is a deliberately weaker, bounded, deduction-free object.

**Net (honest):** the abstract chain (`pblt_of_bpsb`) is a real, reusable artifact — it proves PBLT
from named hypotheses, and is sound to KEEP as documentation / a future-proof interface. But it does
NOT reduce the engine's axiom count or cleanly refactor `PBLT` into smaller pieces, because the engine
`Provable` cannot discharge the interface's fields (it lacks deduction + box-subscript weakening, by
design). So: **keep `PBLT` as the single honest axiom**; the `pblt_of_bpsb` chain is the abstract
justification (Critch §5 mechanized over an interface), not a path to fewer engine axioms. Option 2
(extend `Formula` with `∀` + encoding + a deduction-carrying proof layer) remains the only route to
remove `PBLT`, and it is a genuine separate development, not a refactor of the current engine. -/

#check @ploeb_of_bpse
#check @pblt_of_bpse
#check @bloeb_of_bpsb
#check @pblt_of_bpsb

end PD.PbltSpike
