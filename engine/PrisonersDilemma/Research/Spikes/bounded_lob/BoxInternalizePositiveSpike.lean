import PrisonersDilemma.ProofSystem
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems

/-!
# Spike — can `boxInternalize` be a THEOREM from positive constructors? (after the ctor route failed)

The naive constructor `boxInternalize : (Provable k φ → Provable k α) → … → Provable k (□φ→□α)` is
KERNEL-REJECTED: the transformer premise `Provable k φ → Provable k α` puts `Provable` in a NEGATIVE
position (non-positive occurrence). So box-internalization CANNOT be a `Provable` constructor — unlike
`boxIntro`, whose premise `Provable kIn φ` is positive. (This is the positivity wall, same family as
the false-guard `search_f` block.)

Remaining hope: keep `hfitD` as a META hypothesis (theorem, not constructor) and BUILD the conclusion
`□_k φ → □_k α` from the existing POSITIVE constructors (`boxIntro`, `weakenImpl`, `implTrans`, …).
This spike tests whether that is possible. The obstruction to watch: `weakenImpl φ' ψ' m` needs the
consequent `ψ' = □_k α` provable OUTRIGHT (`Provable m (□_k α)`), which via `boxIntro` needs
`Provable k α` — but at the fixpoint we only have `α`'s provability CONDITIONALLY (through `hfitD`
applied to `Provable k φ`), not unconditionally.

NOT root-imported.
-/

namespace PD.BoxInternalizePositiveSpike
open PD

/-! ## The target, as a theorem taking the meta-transformer as a hypothesis. -/

-- Can we PROVE this from positive constructors? (`sorry` marks the gap we are probing.)
example (k : Nat) (φ : Formula) (p q : Prog) (c : Action)
    (hfitD : Provable k φ → Provable k (.plays p q c))
    (hsz : (Formula.impl (.box k φ) (.box k (.plays p q c))).size ≤ k) :
    Provable k (.impl (.box k φ) (.box k (.plays p q c))) := by
  -- Attempt via `weakenImpl φ' ψ' m`: needs `Provable m (□_k α)` OUTRIGHT (the consequent).
  -- `boxIntro` gives `Provable (□_k α).size (□_k α)` only from `Provable k α` — which we DON'T have
  -- unconditionally (only `hfitD : Provable k φ → Provable k α`). No `Provable k φ` in hand.
  -- So `weakenImpl` is blocked. `implTrans` needs an existing implication chain to/from the boxes —
  -- none available. `atomBoxImpl`/`searchThenSearch_t` conclude different shapes. CONCLUSION: no
  -- positive constructor builds `□φ→□α` from a mere transformer. This is the obstruction.
  --
  -- EXPLICIT attempts (each fails to typecheck → recorded, not run):
  --   exact Provable.weakenImpl (.box k φ) (.box k (.plays p q c)) _ ?cons _ hsz
  --     -- ?cons : Provable _ (□_k α) — would need `Provable k α`, only have hfitD. NO PROOF.
  --   exact Provable.implTrans _ _ _ _ _ ?leg1 ?leg2 _ _ _ hsz
  --     -- needs a cut formula χ with `□φ→χ` and `χ→□α` both provable — none exists. NO PROOF.
  -- The `atomBoxImpl`/`searchThenSearch_t` conclusions are `.plays`-headed or `□guard→plays`,
  -- not `□φ→□α`, so they don't unify. The build below leaves the `sorry` as the located gap.
  sorry

/-! ## Live confirmation — the `weakenImpl` consequent is genuinely unprovable here.

`weakenImpl` would need `Provable m (□_k α)`. Try to build it: the only producer is `boxIntro`, which
needs `Provable k α`. We have only `hfitD`. So the consequent obligation is exactly `Provable k α`
unconditionally — which does NOT hold (α is a hypothetical fixpoint atom). Demonstrate that assuming
we COULD discharge it unconditionally would prove α for ANY α, i.e. the route is unsound, not just
unavailable: -/

-- If a positive build existed it would give `Provable k (□φ→□α)` for an ARBITRARY transformer; fed
-- the trivial transformer (`id` on `φ = α`) it would yield `Provable k (□α→□α)` — harmless — but to
-- get the DISTRIBUTED `□φ→□α` for distinct φ,α with α false and φ provable, it would have to
-- manufacture `Provable k α`. Concretely, the consequent-outright route is equivalent to having
-- `Provable k α` whenever the implication is used with a provable `□φ`, i.e. it is NOT weaker than
-- the axiom. So no purely-positive theorem exists. (Matches HonestKSpike's budget verdict from the
-- other direction: the object-K antecedent is the only positive handle, and it is budget-irreconcilable.)
example : True := trivial

/-! ## VERDICT (to record).

The transformer-as-constructor is non-positive (kernel-rejected). The transformer-as-hypothesis +
positive-constructor build is BLOCKED: `weakenImpl` needs the boxed consequent `□_k α` provable
outright (→ `Provable k α`), but the fixpoint only supplies `α`'s provability CONDITIONALLY via
`hfitD`. There is no positive constructor that consumes a conditional/transformer and emits the
distributed box-implication. So `boxInternalize` is NOT eliminable the way `box_provable` was —
the negative occurrence is essential to its content (it internalizes an implication-shaped fact whose
antecedent's provability is hypothetical, not held).

This is the genuine difference from `box_provable`: necessitation boxes a HELD proof (positive);
internalization boxes a TRANSFORMER (negative). `box_provable` fell to a local constructor;
`boxInternalize` does not. The remaining sound routes are the documented ones (keep the axiom; or the
faithful GL-K which is budget-irreconcilable, `HonestKSpike`). RECOMMEND: keep `boxInternalize` as an
axiom; it is the irreducible-by-positivity internalization, sound by `boxInternalize_sound`. -/

end PD.BoxInternalizePositiveSpike
