import PrisonersDilemma.ProofSystem
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.vs_DefectBot

/-!
# Spike — can `boxInternalize` become a `Provable` CONSTRUCTOR (no axiom)?

`boxInternalize` (Axioms.lean) takes a META transformer `hfitD : Provable k φ → Provable k α`
(α a play-atom) and asserts the object `Provable k (□_k φ → □_k α)`. Its `interp` is DEFINITIONALLY
`Provable k φ → Provable k α` = the transformer itself, so `boxInternalize_sound := hfitD` is a
tautology.

Like `boxIntro` (which just killed `box_provable`), the reason it's an axiom is purely
REPRESENTATIONAL: no `Provable` constructor takes a meta proof-transformer and emits an object
box-implication. A constructor CAN carry the transformer as a premise; its `Provable_sound` arm is
then the IDENTITY (conclusion interp = premise). Safety is the same as `boxIntro`: to fire it you
must SUPPLY the transformer, and for a false atom no transformer exists.

This spike checks the two load-bearing facts against the REAL engine, before editing the inductive:
  (1) `interp (□_k φ → □_k α)` is definitionally `Provable k φ → Provable k α` (so the soundness arm
      is `fun hfitD _hsz _ih => hfitD`); and
  (2) such a constructor is SAFE — it cannot box a false atom, because the transformer premise is
      unsatisfiable for one (no `Provable k φ → Provable k (DefectBot plays C)` from an inhabited
      antecedent, since the consequent is uninhabited and the antecedent may hold).

NOT root-imported. `lake env lean PrisonersDilemma/Research/Spikes/bounded_lob/BoxInternalizeConstructorSpike.lean`
-/

namespace PD.BoxInternalizeConstructorSpike
open PD

/-! ## (1) The soundness arm is the identity. -/

-- `interp (□_k φ → □_k α)` unfolds to `Provable k φ → Provable k α`.
example (k : Nat) (φ : Formula) (p q : Prog) (c : Action) :
    (Formula.impl (.box k φ) (.box k (.plays p q c))).interp
      = (Provable k φ → Provable k (.plays p q c)) := rfl

-- So the constructor's `Provable_sound` arm, given the transformer premise, IS that premise.
example (k : Nat) (φ : Formula) (p q : Prog) (c : Action)
    (hfitD : Provable k φ → Provable k (.plays p q c)) :
    (Formula.impl (.box k φ) (.box k (.plays p q c))).interp := hfitD

/-! ## (2) Safety — the transformer premise is unsatisfiable for a false atom.

If `α = .plays DefectBot q C` (false), then `Provable k α` is uninhabited (engine machinery:
DefectBot never plays C). A transformer `Provable k φ → Provable k α` would have to map an
inhabited antecedent into the empty `Provable k α`. So the only way to SUPPLY the premise for a
false atom is if `Provable k φ` is ALSO empty — in which case nothing is boxed that wasn't already
vacuous. The constructor cannot manufacture `Provable k (false atom)`. -/

-- We can't construct a transformer into a false atom from a TRUE antecedent. Concretely: a
-- transformer `Provable k φ → Provable k (DefectBot plays C)` applied to a real proof yields a
-- proof of the false atom — which is impossible. So holding both the transformer AND `Provable k φ`
-- is contradictory; the constructor is inert exactly there.
example (k : Nat) (φ : Formula) (q : Prog)
    (hfitD : Provable k φ → Provable k (.plays PD.Bots.DefectBot q .C))
    (hφ : Provable k φ) : False := by
  have hfalse : Provable k (.plays PD.Bots.DefectBot q .C) := hfitD hφ
  -- DefectBot-plays-C is interp-false; Provable_sound contradicts it.
  have : (Formula.plays PD.Bots.DefectBot q .C).interp := PD.BaseTheorems.Provable_sound k _ hfalse
  exact (PD.Theorems.interp_DefectBot_plays_C_false q) this

/-! ## VERDICT

PASS. `boxInternalize` is a LOCAL `Provable` constructor, exactly like `boxIntro`:
  • soundness arm = identity (conclusion interp ≡ the transformer premise);
  • SAFE — to fire it on a false atom you'd need a transformer into an empty type WHILE holding the
    antecedent, which is contradictory (the example above derives `False`). So nothing false boxes.
No size-index, no refactor: add the constructor, discharge the `Provable_sound`/`playsProof_sound`/
`proofSearch_monotone` arms (identity / trivial / re-apply), replace the axiom with a theorem
(or just rename the constructor `Provable.boxInternalize` and delete the axiom), repoint `mutual_loeb`.

CAVEAT to verify on landing: `proofSearch_monotone` must handle the new arm. Unlike `boxIntro` the
conclusion budget here is a free `k` (not `size`), with a `size ≤ k` premise — so it self-weakens the
same way (`size ≤ k₁ ≤ k₂`). -/

end PD.BoxInternalizeConstructorSpike
