import PrisonersDilemma.Reflection.Native


/-!
# ⚑ HISTORICAL (2026-07-01): superseded by the INTERNALIZATION — `PBLT` is deleted.

This module belongs to the side-reflection route, which bottomed out at `provesN_play_extract`
(object→engine reflection). That route is CLOSED and MOOT: bounded Löb is now proven INSIDE the
engine's own `Provable` (`BaseTheorems.bloeb_engine`/`pblt_engine`, via `Formula.diag` — see
`Research/Notes/INTERNALIZATION_ROADMAP.md`), and the `PBLT` axiom is deleted. This file is kept as
the meta-justification/history of the diagonal's derivation (`repr_object` etc. justify that a
faithful arithmetization contains the fixpoint sentence `.diag` internalizes). Do not build on the
`ProvesN`/extraction machinery here.
-/

/-!
# Reflection layer — wiring object PBLT to the engine (assembly + the honest last gap)

Assembles the engine's `PBLT` from the native object PBLT (`object_pblt_native`) + the faithfulness
bridge (`encodeF`/`engineVal`/`atom_complete`) + the FWD leaf rule (`ProvesN.engineLeaf`). For the PBLT
family `φ k := .plays … .C` (cooperation outcomes) we derive `∃m, Provable m (φ k)`.

FWD side (done): the engine Löb premise `Provable m (□φ→φ)` transports via `engineLeaf` to
`ProvesN p [] (□p → p)` (`p := encodeF (φ k)`), and `object_pblt_native` gives `ProvesN p [] p`.

BWD side — the HONEST remaining gap. To turn `ProvesN p [] p` (p a play-atom) into `∃m, Provable m (φ
k)` we need the engine PLAY, i.e. `(φ k).interp`. Soundness (`provesN_sound` at `engineVal`) would give
it — BUT `provesN_sound` requires `interp p` as a hypothesis (the diagonal rules `diagFix`/`ctxUnfold`
are only sound when the outcome holds), which is exactly what we are trying to derive. This is NOT
vicious (the engine's own `PBLT` axiom delivers the outcome unconditionally, so it is achievable), but
it means the general soundness cannot extract it: we need a DEDICATED play-atom extraction that reads
the outcome from `bloeb`'s construction (the Löb premise + the fixpoint), not from the outcome-assuming
soundness. That extraction — `provesN_play_extract` below — is the last piece; stated, not yet proven.

The `atomCode` injectivity obligation is now DISCHARGED (`Bridge.atomCode_injective`, a concrete
head-tagged Gödel code), so `engine_pblt_plays` no longer carries an `hinj` hypothesis — the ONLY
remaining assumption is `provesN_play_extract` (the BWD extraction). NOT yet root-imported.
-/

namespace PD.Reflection
open PD PD.BaseTheorems

/-- **The last gap, stated precisely.** From an object proof of a play-atom `ProvesN (encodeF (.plays
    pr qr a)) [] (encodeF (.plays pr qr a))` — built by `bloeb_native` from a real engine Löb premise —
    extract the engine play `∃n, play n pr qr = some a`. This is the BWD extraction that does NOT go
    through outcome-assuming soundness; it must read the outcome from the Löb construction itself.
    (The engine's `PBLT` axiom witnesses this is achievable; here it is the remaining obligation.) -/
def provesN_play_extract : Prop :=
  ∀ (pr qr : Prog) (a : Action),
    ProvesN (encodeF (.plays pr qr a)) [] (encodeF (.plays pr qr a)) →
    ∃ n, play n pr qr = some a

/-- **Engine PBLT for a play-atom family**, assembled — modulo `atomCode` injectivity and the BWD
    extraction. FWD + object PBLT are DISCHARGED; only `hExtract` (the last gap) is assumed. -/
theorem engine_pblt_plays
    (hExtract : provesN_play_extract)
    (φ : Nat → Formula) (f : Nat → Nat) (k₁ : Nat)
    (hplays : ∀ k, ∃ pr qr a, φ k = .plays pr qr a)
    (hLoeb : ∀ k, k > k₁ → ∃ m, Provable m (.impl (.box (f k) (φ k)) (φ k))) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Provable m (φ k) := by
  refine ⟨k₁, ?_⟩
  intro k hk
  obtain ⟨pr, qr, a, hφ⟩ := hplays k
  obtain ⟨m, hm⟩ := hLoeb k hk
  -- FWD: engine Löb premise → ProvesN (encodeF (φ k)) [] (□(encodeF (φ k)) → encodeF (φ k)).
  have hLoebN : ProvesN (encodeF (φ k)) []
      (.imp (.box (encodeF (φ k))) (encodeF (φ k))) := by
    have henc : encodeF (.impl (.box (f k) (φ k)) (φ k))
        = OFml.imp (.box (encodeF (φ k))) (encodeF (φ k)) := by simp [encodeF]
    rw [← henc]; exact ProvesN.engineLeaf hm
  -- object PBLT (native): ProvesN (encodeF (φ k)) [] (encodeF (φ k)).
  have hpN : ProvesN (encodeF (φ k)) [] (encodeF (φ k)) :=
    object_pblt_native (encodeF (φ k)) (.atom 0) hLoebN
  -- BWD extraction → engine play → ∃m Provable via atom_complete.
  have hpN' : ProvesN (encodeF (.plays pr qr a)) [] (encodeF (.plays pr qr a)) := by
    rw [hφ] at hpN; exact hpN
  obtain ⟨n, hn⟩ := hExtract pr qr a hpN'
  refine ⟨atom_cost n, ?_⟩
  rw [hφ]
  exact Provable.atom (atom_complete pr qr a n hn)

/-! ## VERDICT — the assembly is COMPLETE modulo one precise BWD-extraction lemma.

⚠️ CORRECTED FRAMING (2026-07-01): `provesN_play_extract` below is NOT an irreducible crux — it is an
ARTIFACT of THIS `ProvesN` formulation, where `box := ProvesN`-provability and the diagonal predicate
`gApp`/`ctxUnfold` are OPAQUE (sound only via the outcome-relative `Gctx`/`hp0`). The faithful route
(construct `gApp`/`box` as real `Bew`-formulas, so `ContextRepr` is definitional — Critch §5) DISSOLVES
this obligation: `bloeb_object` (base `Proves`, sorry-free) + `bridge_BWD_plays` (sorry-free) then close
the engine PBLT with NO extraction lemma. See `Research/Notes/PBLT_REMOVAL_ROADMAP.md` (corrected). The
paragraphs below describe why THIS (ProvesN) route incurs the obligation — accurate for this route, but
this route is superseded by the constructed-`Bew` plan.

`engine_pblt_plays` derives the engine's exact `∃m, Provable m (φ k)` PBLT conclusion for the play-atom
family, with:
  • FWD fully discharged (`ProvesN.engineLeaf` transports the engine Löb premise);
  • object PBLT fully discharged (`object_pblt_native`, sorry-free);
  • BWD reduced to `provesN_play_extract` — read the engine play from an object proof of a play-atom.

`provesN_play_extract` is the last gap, and it is DEEPER than "run soundness":
  • `provesN_sound` at `engineVal` would give `interpN p engineVal p` (= the play) — but it REQUIRES
    `interp p` (the diagonal rules `diagFix`/`ctxUnfold` are only sound when the outcome holds). Circular.
  • The tempting escape — get `interp p` from the LÖB PREMISE `□p → p` applied to `hpN : ProvesN [] p`
    — RELOCATES the circularity, it doesn't remove it (explored, machine-checked): the object premise
    `interpN (imp (box p) p) = (ProvesN [] p → interpN p)` has a `ProvesN`-box antecedent; obtaining it
    from the ENGINE premise (a `Provable`-box) via faithfulness requires proving "object-provable
    play-atom ⟹ engine-true", which IS the outcome-assuming BWD. So the Löb-premise route lands back on
    the same soundness obligation.
  • Net: `provesN_play_extract` is essentially "the object system is sound for the play-atoms it proves
    THROUGH the diagonal" — and the diagonal's soundness is exactly the conditional (`hp0`) one. It is
    achievable (the engine `PBLT` axiom witnesses the outcome DOES follow — that is the whole content of
    bounded Löb), but capturing it needs a genuinely different argument: a soundness for `ProvesN` that
    derives the fixpoint's truth from the Löb premise INTERNALLY (a proof-theoretic Löb, not a model
    argument), OR a cut-elimination / normalization showing the object proof of a play-atom reduces to a
    play witness. That is now the SOLE remaining obligation — `hinj` (concrete injective `atomCode`) is
    discharged (`Bridge.atomCode_injective`). -/

#check @engine_pblt_plays
#check @provesN_play_extract

end PD.Reflection
