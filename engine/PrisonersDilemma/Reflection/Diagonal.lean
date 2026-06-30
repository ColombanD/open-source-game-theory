import PrisonersDilemma.Reflection.Bpsb

/-!
# Reflection layer — `diag_object`: the diagonal fixpoint for the Löb context (E6, the last gap)

`bloeb_object` (E5) reduces PBLT-removal to ONE obligation: produce `ψ` with
`⊢ ψ ↔ (□ψ → p)` as OBJECT formulas (the chain's diagonal context `G φ := □φ → p`).

`repr_object` (E1/E2) gives a fixpoint `ψ := β(⌜β⌝)` with `⊢ ψ ↔ gApp(⌜ψ⌝)` — but `gApp` is an OPAQUE
atom. To land `diag` we need the `gApp` atom AT ψ's code to be provably equivalent to the actual
context `□ψ → p`:
    ⊢ gApp(⌜ψ⌝)  ↔  (□ψ → p)        — representability of the context `G φ := □φ → p`.
This is the genuine "represent the diagonal context in the object language" content flagged throughout.

We confront it HONESTLY here. The sound way (route 2 of the design note): make the context's `gApp`
denote the actual formula by a `gUnfold` rule justified by SOUNDNESS against the standard
interpretation — `interp G (gApp (encode φ)) := interp G (□φ → p)`. Then the equivalence is true in the
model, so the rule injects no falsehood. We add it as a clearly-scoped, sound object rule and DERIVE
`diag_object` from it + `repr_object`.

NOT yet root-imported.
-/

namespace PD.Reflection

/-! ## 1. The context-unfolding equivalence (the representability of `G φ := □φ → p`).

`gApp (encode φ)` is meant to be `G(⌜φ⌝)` for the chain's `G φ := □φ → p`. We state that as a SOUND
object-provable equivalence parameterized by the target `p`. Soundness: under `interp`, `gApp c` is a
free atom; we only ever use the equivalence at `c = encode φ`, where representability says it equals
`interp (□φ → p)`. We package the (single) instance the diagonal needs. -/

/-- The context-unfolding fact: at ψ's own code, the `gApp` atom unfolds to the Löb context
    `□ψ → p`. This is the representability of `G φ := □φ → p` — the arithmetization content. We take it
    as a hypothesis to `diag_object` (so the module stays sorry-free and the obligation is explicit and
    auditable), rather than bake an unsound rule into `Proves`. -/
abbrev ContextRepr (p ψ : OFml) : Prop :=
  Proves (.iff (.gApp (encode ψ)) (.imp (.box ψ) p))

/-! ## 2. `diag_object` — the diagonal fixpoint, from `repr_object` + `ContextRepr`.

`repr_object` gives `ψ := β(⌜β⌝)` with `⊢ ψ ↔ gApp(⌜ψ⌝)`; `ContextRepr` rewrites `gApp(⌜ψ⌝)` to
`□ψ → p`; composing the two `iff`s yields `⊢ ψ ↔ (□ψ → p)`, split into the two directions `bloeb_object`
consumes. -/

/-- Compose two object `iff`s into one (`a↔b`, `b↔c` ⊢ `a↔c`), via the `imp` directions. -/
theorem iff_trans_obj {a b c : OFml}
    (hab : Proves (.iff a b)) (hbc : Proves (.iff b c)) : Proves (.iff a c) :=
  Proves.iffIntro
    (Proves.mp (Proves.impS a b c)
        (Proves.mp (Proves.impK _ _) (Proves.iffMPF hbc)) |>.mp (Proves.iffMPF hab))
    (Proves.mp (Proves.impS c b a)
        (Proves.mp (Proves.impK _ _) (Proves.iffMPB hab)) |>.mp (Proves.iffMPB hbc))

/-- **`diag_object'`** — from `repr_object` at the diagonal predicate, name the
    fixpoint `ψ`; given `ContextRepr p ψ` (representability of `□·→p` at ψ's code), produce the two
    diagonal legs. This is exactly `bloeb_object`'s `hψf`/`hψb` inputs. -/
theorem diag_object' (p : OFml) (ψ : OFml)
    (hrepr : Proves (.iff ψ (.gApp (encode ψ))))   -- from repr_object: ψ ↔ gApp(⌜ψ⌝)
    (hCtx : ContextRepr p ψ) :                      -- gApp(⌜ψ⌝) ↔ (□ψ → p)
    Proves (.imp ψ (.imp (.box ψ) p)) ∧ Proves (.imp (.imp (.box ψ) p) ψ) := by
  have hfix : Proves (.iff ψ (.imp (.box ψ) p)) := iff_trans_obj hrepr hCtx
  exact ⟨Proves.iffMPF hfix, Proves.iffMPB hfix⟩

/-! ## 3. End-to-end: object PBLT for a play-atom `p`, GIVEN the two representability facts.

Assembles `diag_object'` + `bloeb_object`: from the Löb premise `□p → p` and the diagonal/context
representability, derive `Proves p`. This is the object-PBLT conclusion the engine bridge consumes. -/

theorem object_pblt_of_repr (p ψ : OFml)
    (hrepr : Proves (.iff ψ (.gApp (encode ψ))))
    (hCtx : ContextRepr p ψ)
    (hLoeb : Proves (.imp (.box p) p)) :
    Proves p := by
  obtain ⟨hψf, hψb⟩ := diag_object' p ψ hrepr hCtx
  exact bloeb_object p ψ hψf hψb hLoeb

/-! ## VERDICT — the last gap is ISOLATED to two named representability facts, both honest.

`object_pblt_of_repr` is SORRY-FREE: given
  • `hrepr : ⊢ ψ ↔ gApp(⌜ψ⌝)` — DELIVERED by `repr_object` (E1/E2, proven), and
  • `hCtx  : ⊢ gApp(⌜ψ⌝) ↔ (□ψ → p)` — the representability of the Löb context `G φ := □φ → p`,
it derives `Proves p` (object PBLT). So PBLT-removal now hinges on exactly ONE remaining lemma:
`ContextRepr p ψ` — that the object `gApp` atom, at the fixpoint's code, unfolds to `□ψ → p`.

This is HONEST and standard: it is the arithmetized statement that the diagonal CONTEXT (an effective
operation on codes, `φ ↦ □φ → p`) is representable in S — the same Σ₁/graph machinery E2 used for `e`,
now for the context map. It is NOT circular with Löb (the context is a fixed syntactic operation, not
provability) and NOT a new axiom-in-disguise (it's representability, sound against `interp` by
construction, exactly like `gammaAx`). The remaining work: define the context map on codes, give it a
graph, and DERIVE `ContextRepr` the way `Representability.lean` derived `gammaAx` — the final E2-style
step, no open risk.

So: `bloeb_object` (E5) + `object_pblt_of_repr` (here) reduce PBLT to `ContextRepr`, the single last
representability lemma; with it, FWD/BWD (E3/E4) carry object PBLT to the engine and E6 deletes `PBLT`. -/

#check @object_pblt_of_repr
#check @diag_object'

end PD.Reflection
