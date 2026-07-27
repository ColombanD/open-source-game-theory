import PrisonersDilemma.ProofSystem
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems

/-!
# Spike — is `axK` (GL-K, proof-term premise) SOUND for the real engine? (the gate AFTER positivity)

`GLKPositiveSpike` showed `axK : Provable k (□(φ→α)) → Provable k (□φ → □α)` is POSITIVE (legal
constructor). But legality ≠ soundness. This spike tests the soundness OBLIGATION its `Provable_sound`
arm would create, against the REAL engine.

Soundness arm goal: `interp (□φ → □α)` from the premise.
  interp (□(φ→α)) = Provable k (φ→α)        -- the premise
  interp (□φ → □α) = Provable k φ → Provable k α   -- the conclusion
So the arm must prove:  Provable k (φ→α) → Provable k φ → Provable k α   (Provable-level modus ponens).

Via `Provable_sound`: from the two premises we get `α.interp`. But the conclusion needs
`Provable k α` — the INCOMPLETE direction (`α.interp → Provable k α` holds only for play-atoms via
`atom_complete`, AND only when the play fits budget `k`: `atom_cost fuel ≤ k`). This spike checks
whether that budget threshold is dischargeable or is the wall.

NOT root-imported.
-/

namespace PD.AxKSoundnessSpike
open PD PD.BaseTheorems

/-- The soundness obligation `axK` would create, stated directly. Can we prove it? -/
example (k : Nat) (φ : Formula) (p q : Prog) (c : Action)
    (himpl : Provable k (.impl φ (.plays p q c))) :
    Provable k φ → Provable k (.plays p q c) := by
  intro hφ
  -- From Provable_sound: himpl gives (φ→α).interp = φ.interp → α.interp; hφ gives φ.interp.
  have hi : (Formula.impl φ (.plays p q c)).interp := Provable_sound k _ himpl
  have hφi : φ.interp := Provable_sound k _ hφ
  have hαi : (Formula.plays p q c).interp := hi hφi
  -- hαi : ∃ n, play n p q = some c. Need: Provable k (.plays p q c).
  -- atom_complete gives AtomProvable (atom_cost fuel) — at budget atom_cost fuel, NOT k.
  -- atom_monotone lifts atom_cost fuel → k ONLY if atom_cost fuel ≤ k. NOT guaranteed.
  obtain ⟨n, hn⟩ := hαi
  have hac : AtomProvable (atom_cost n) (.plays p q c) := atom_complete p q c n hn
  -- To conclude `Provable k`, need `atom_cost n ≤ k`. We DON'T have it. This is the wall:
  sorry

/-! ## VERDICT (to record after running).

If the `sorry` cannot be closed, `axK`'s soundness arm is NOT dischargeable in general — the same
budget-threshold wall that kept `boxInternalize` an axiom (the conclusion `Provable k α` needs the
play to fit budget `k`, which a mere `Provable k (φ→α)` does not guarantee). Then adding `axK` as a
SOUND constructor to the real `Provable` is blocked, and `boxInternalize` stays an axiom in the
ABSTRACT engine — confirming the proposal's claim that it falls only under FULLY-explicit S (where
`Provable k α` is concrete data carrying its own budget, so the threshold is part of the term).

The toy `ExplicitSBoxInternalizeSpike` did NOT hit this because its atom layer was trivial
(`atomLeaf k` certified `trueAtom` at EVERY budget k). The real engine's atom budget is `atom_cost
fuel`, which is NOT ≤ k for free. -/

end PD.AxKSoundnessSpike
