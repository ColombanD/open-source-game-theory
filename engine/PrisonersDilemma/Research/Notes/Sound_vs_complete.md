# Soundness vs completeness

These are the two halves of "the proof system S matches reality (`eval`)." Reality is: bot p plays action a against q. `S` is: there's a bounded proof that p plays a.

Soundness = `S` never lies. If S proves it, it's true.

```text
Provable k (p plays a) ⟹ play fuel p q = some a
```

This is `Derivation.sound / proofSearch_spec.1` (BaseTheorems.lean:53). It's the one you must never break — an unsound `S` would certify false cooperations, and your whole "compilation == correctness" guarantee dies. This is why you ripped out `atom_box_provable_impl`: it was unsound.

Completeness = `S` misses nothing. If it's true, S can prove it.

```text
play fuel p q = some a ⟹ Provable (atom_cost fuel) (p plays a)
```

This is `atom_complete` (BaseTheorems.lean:32). Every real play has a bounded certificate. This is the direction the false-guard axiom lives in.

The asymmetry is the whole game:

- Soundness is "downhill" — you have a proof tree, you read off the play. Always constructive.
- Completeness is "uphill" — you have a play, you must manufacture a proof tree. Sometimes the play happened because a search failed ("I cooperate because I couldn't prove you'd defect"). To certify that play, S must certify the absence of a proof — `¬ Provable k (guard)`. That negative is the Π₁ residue.

So: completeness is where Π₁ shows up, because completeness is the direction that has to account for plays caused by failed searches.