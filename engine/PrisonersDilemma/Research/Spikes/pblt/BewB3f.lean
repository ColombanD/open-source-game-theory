import PrisonersDilemma.Reflection.Diagonal

/-!
# B3-followup — VERDICT: diagFix's hp0 IS removable, but requires the PREDICATE-level diagonal.

Question: can `diagFix` (the diagonal fixpoint) be made outcome-free, like the genuine diagonal?

FINDING (machine-traced):
  • The GENUINE diagonal IS outcome-free — `DiagonalLemmaSpike.parametric_diagonal` derives
    `ψ ↔ G(⌜ψ⌝)` from `repr` ALONE (`exact hrepr`, no hp0). So the fixpoint is NOT intrinsically
    outcome-dependent.
  • WHY it closes there: it's built at the PREDICATE level. `ψ := selfApply β`, and
    `selfApply θ := ⟨fun _ k => θ.app (code θ) k⟩` DISCARDS the plugged code (uses `code θ`, ignores its
    argument). So `ψ.app (code ψ) k` reduces DEFINITIONALLY to `β.app (code β) k = ψ`, matching `repr`'s
    LHS. The self-reference closes by defeq.
  • WHY B3's diagFix needs hp0: the real `OFml` diagonal is built at the SUBSTITUTION level.
    `selfApply θ = plug (encode θ) θ` genuinely SUBSTITUTES the code (plug is head-preserving and
    replaces `slot` by `quoteC ⌜θ⌝`). So `selfApply θ ≠ betaA θ` syntactically, the self-code fixpoint
    `ψ ↔ gApp(⌜ψ⌝)` that `diag_object'` needs is NOT reachable, and `diagFix` bridges the gap by
    ASSERTING it — sound only via hp0 (`Gctx`/`Gw`).

CONFIRMATION that plug blocks the self-code fixpoint (head-preservation): -/

namespace PD.Reflection.BewB3f
open PD PD.Reflection

theorem plug_head_preserving (θ : OFml) :
    selfApply (.betaA θ) = .betaA (plug (encode (.betaA θ)) θ) := rfl

-- For the self-code fixpoint diag_object' needs (ψ = betaA θ with selfApply θ = betaA θ), plug would
-- have to turn θ's body INTO betaA θ — but plug only replaces `slot`↦`quoteC`, never introduces betaA.
-- So no OFml θ gives selfApply θ = betaA θ (unless θ already IS, circularly). The self-code fixpoint is
-- unreachable at the substitution level — machine-confirmed by the head-preservation of plug.

/-! ## VERDICT — diagFix's hp0 is removable, but NOT by re-denotation (B1/B2/B3 Gw). It needs the
    diagonal REBUILT at the predicate level (as `parametric_diagonal`), where `selfApply` discards the
    plugged code and the fixpoint closes by defeq from `repr` — NO outcome.

So the full route to dropping diagFix's hp0 is: replace the OFml `betaA`/`plug` substitution-diagonal
with a PREDICATE-level `betaA`/`selfApply` (à la DiagonalLemmaSpike), port `repr_object` to it (it's
`repr`, already the one representability input), and feed `diag_object'` the DEFEQ fixpoint. Then:
  • ctxUnfold — outcome-free (B3, done via Gw);
  • diagFix — outcome-free (predicate-level defeq fixpoint, de-risked by parametric_diagonal);
  ⇒ provesN_play_extract FULLY dissolved.

This is a REAL reformulation of the OFml diagonal (predicate-level, not substitution-level), but it is
de-risked end-to-end: parametric_diagonal PROVES the predicate-level fixpoint is outcome-free. The work
is porting the OFml layer's betaA/plug to the predicate encoding — mechanical but non-trivial (touches
Syntax/Proves/Diagonal). NEXT: B3f-impl (port the diagonal to predicate level). -/

#check @plug_head_preserving

end PD.Reflection.BewB3f
