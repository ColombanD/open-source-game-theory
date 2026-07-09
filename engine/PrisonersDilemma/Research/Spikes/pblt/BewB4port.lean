import PrisonersDilemma.Research.Spikes.reflection.Bpsb
import PrisonersDilemma.Research.Spikes.reflection.Diagonal

/-!
# B4-port verification: with `selfApply θ := betaA θ` in Syntax.lean, the REAL `repr_object` now gives
the SELF-CODE fixpoint, so `diag_object'`'s `hrepr` is DERIVED (base Proves, outcome-free).
-/

namespace PD.Reflection.BewB4port
open PD PD.Reflection

-- With the ported selfApply, real repr_object gives betaA θ ↔ gApp(⌜betaA θ⌝) (self-code).
theorem diagFix_real (θ : OFml) :
    Proves (.iff (.betaA θ) (.gApp (encode (.betaA θ)))) := by
  have h := repr_object θ            -- betaA θ ↔ gApp(⌜selfApply θ⌝)
  simp only [selfApply] at h
  exact h

-- diag_object' needs hrepr : Proves (iff ψ (gApp (encode ψ))) with ψ := betaA θ. diagFix_real IS that.
theorem hrepr_derived (θ : OFml) :
    Proves (.iff (.betaA θ) (.gApp (encode (.betaA θ)))) := diagFix_real θ

/-- **The diagonal legs, base-Proves, OUTCOME-FREE** — feed `diag_object'` the DERIVED `hrepr`
    (`diagFix_real`) + `hCtx` (`ContextRepr`, from the B3/Gw-sound ctxUnfold). This gives
    `ψ → (□ψ→p)` and `(□ψ→p) → ψ` with ψ := betaA θ, NO hp0 — the input `bloeb_object` consumes. -/
theorem diag_legs_real (p θ : OFml) (hCtx : ContextRepr p (.betaA θ)) :
    Proves (.imp (.betaA θ) (.imp (.box (.betaA θ)) p))
      ∧ Proves (.imp (.imp (.box (.betaA θ)) p) (.betaA θ)) :=
  diag_object' p (.betaA θ) (diagFix_real θ) hCtx

/-- **object PBLT, base Proves, from the DERIVED diagonal + Löb premise.** `ContextRepr` supplied as a
    hypothesis here (B3 shows it is Gw-sound outcome-free; final wiring provides it as a theorem). -/
theorem object_pblt_real (p θ : OFml)
    (hCtx : ContextRepr p (.betaA θ))
    (hLoeb : Proves (.imp (.box p) p)) :
    Proves p :=
  object_pblt_of_repr p (.betaA θ) (diagFix_real θ) hCtx hLoeb

#check @diagFix_real
#check @diag_legs_real
#check @object_pblt_real

/-! ## VERDICT — B4-PORT LANDS: the real `repr_object` (with ported `selfApply`) DERIVES the self-code
    fixpoint, so the base-`Proves` Löb chain (`diag_object'`/`bloeb_object`) runs with the diagonal as a
    THEOREM — no `diagFix` axiom, no `hp0` in the fixpoint. The ONLY remaining input is `ContextRepr`,
    which B3 proved Gw-sound OUTCOME-FREE. So `object_pblt_real` derives `Proves p` from just the Löb
    premise + the (outcome-free) `ContextRepr` — the object PBLT the engine bridge consumes, with NO
    `provesN_play_extract`. Next: supply `ContextRepr` as a base-Proves theorem via the Gw soundness
    (B3), then wire `bridge_BWD_plays` → engine PBLT, delete the axiom. -/

end PD.Reflection.BewB4port
