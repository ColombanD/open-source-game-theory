import PrisonersDilemma.Tau.Roster

/-!
# TauCIMCIC — conditional commitment, lifted (the first `.impl`-guard bot)

Base CIMCIC: "cooperate iff I can prove that MY cooperation implies THEIRS" — one
`.search` whose guard is an IMPLICATION between two plays-atoms,
`.impl (.plays .self .opp C) (.plays .opp .self C)`.

**Why it needed BOTH extensions.** Its guard mentions `.self` AND `.opp`, so it is
a SELF-PROBER (`Gate D1 caught this on the first lift attempt, 2026-08-20`) — the
`.sys` binder cuts its cycles with the other self-probers (`dupoc`, `cupod`). And
its guard is an implication, so `Mode.proveImpl` compiles it: the antecedent's
subject stays the `.self` pronoun (the instance being compiled cannot contain
itself), the probed instance fills the other slot.

**Why the modality matters.** `Pf.weakenImpl` proves an implication from its
CONSEQUENT alone, so this guard fires whenever "they cooperate with me" is provable
— but ALSO on its own DIAGONAL, where the substituted guard is literally `φ → φ`
and `Pf.implRefl` closes it: **the conditional cooperator trivially satisfies its
own condition**, no Löb needed. Conditional commitment is a weaker ask than the
plain probe, and reflexivity is the degenerate case where it is free.
-/

namespace PD.Tau

/-- τ(CIMCIC): "can I prove my cooperation induces theirs? then C, else D." -/
def tauCIMCICSpec : Spec Tmpl :=
  .search .proveImpl .self .C (.const .C) (.const .D)

end PD.Tau
