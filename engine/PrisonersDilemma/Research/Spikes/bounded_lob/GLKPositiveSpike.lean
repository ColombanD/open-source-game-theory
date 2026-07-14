import PrisonersDilemma.ProofSystem

/-!
# Spike — is GL axiom-K with a proof-TERM premise POSITIVE in the REAL engine?

KEY REALIZATION (during Phase-0 impl): `boxInternalize`'s rejected premise was the *transformer*
`Provable k φ → Provable k α` (NEGATIVE occurrence). But the GL axiom-K route uses a different
premise — the object box-implication PROOF `Provable k (□(φ→α))` — which is `Provable` in a POSITIVE
position (a proof, not a transformer). `Derivation`/`Provable` are already `Type`/`Prop` *objects*;
the toy (`ExplicitSBoxInternalizeSpike`) showed `axK` over concrete terms is sound. The open question
this spike settles: is the `axK` constructor with a `Provable`-TERM premise KERNEL-LEGAL in the real
mutual block (positive), the way `boxIntro` was — i.e. does Phase 1 actually need the enumerator, or
just this constructor?

If `axK` typechecks here, Phase 1 is UNBLOCKED independent of the `Provable_k` enumerator (which is
the separate computable-eval thread). NOT root-imported.
-/

namespace PD.GLKPositiveSpike
open PD

/-- Probe: a candidate `axK` constructor, stated as a STANDALONE inductive extending the idea — does
    a `Provable`-TERM premise `Provable k (□(φ→α))` sit positively? We can't edit the real `Provable`
    from a spike, so we test the positivity by declaring a fresh inductive `PThenK` that embeds a real
    `Provable` premise positively and concludes the GL-K shape. If THIS is accepted, the same arm is
    addable to the real `Provable`. -/
inductive PThenK : Nat → Formula → Prop where
  | embed (k : Nat) (φ : Formula) : Provable k φ → PThenK k φ        -- positive Provable premise OK?
  | axK (k : Nat) (φ α : Formula) :
      Provable k (.box k (.impl φ α)) →                              -- the GL-K proof-TERM premise
      PThenK k (.impl (.box k φ) (.box k α))

/-- If `PThenK` is accepted (it compiles), the `axK` arm with a positive `Provable`-term premise is
    kernel-legal — so the same arm can be a real `Provable` constructor. Contrast the REJECTED
    transformer premise `Provable k φ → Provable k α` (negative). -/
example (k : Nat) (φ α : Formula) (h : Provable k (.box k (.impl φ α))) :
    PThenK k (.impl (.box k φ) (.box k α)) :=
  .axK k φ α h

/-! ## VERDICT

If this file compiles, the GL-K-with-proof-term-premise is POSITIVE and kernel-legal — so Phase 1
(adding `axK` to `Provable`, deriving `boxInternalize`, deleting the axiom) does NOT require the
`Provable_k` enumerator. The enumerator is the SEPARATE computable-eval thread (and is partly walled
anyway, S3′). This decouples the two threads the proposal had bundled into "Phase 0". -/

end PD.GLKPositiveSpike
