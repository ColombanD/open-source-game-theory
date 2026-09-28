import ArithS.Box.ProperV
import ArithS.Cells.RedCell

/-!
# ArithS.Audit.Box — the axiom census of the arithmetized layer: Box

This file covers the box layer (`Box/`): bounded D2 in rule form (`Cut`), on codes in every
model (`CutV`), and properness in every model (`ProperV`).

Split out of the former single `ArithS/Audit.lean` on 2026-09-28; every `#print axioms` line and its
comment block are verbatim (the comment blocks are the historical record). `ArithS/Audit.lean` imports
the nine per-layer files; each line must read `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArithS

-- M4, first field — bounded D2 in rule form: PA-S closes under modus ponens at additive
-- cost `k₁ + k₂ + 10(|φ| + |ψ|) + 9` (sharp: `5|φ| + 10|ψ| + 9`); budget monotonicity; verum.
#print axioms lenProvable_mp
#print axioms lenProvable_mp_sharp
#print axioms lenProvableV_mp
#print axioms lenProvable_fbound_mono
#print axioms lenProvable_verum
#print axioms mlen_cutMP

-- M4, bounded D2 INSIDE every model of IΣ₁ (CutV): the cut on codes with dlen accounting —
-- unconditional for `LenDerivable` (no code bound), under `ProperV` for `LenProvableV`
-- (a theorem at ℕ), and as ONE ℒₒᵣ-sentence proved by IΣ₁/PA/TAct via the completeness theorem.
#print axioms lenDerivable_cut_V
#print axioms lenProvableV_cut_V
#print axioms lenProvableV_mono_V
#print axioms properV_nat_TAct
#print axioms pa_proves_cutSentence
#print axioms tact_proves_cutSentence

-- M4, properness INSIDE every model of IΣ₁ (ProperV): the code/length chain of `Proper.lean`
-- redone on internal codes by the internal induction principles (no quotes) — `ProperV V TAct`
-- is a THEOREM, so bounded D2 for `LenProvableV` is unconditional and the Σ₁ box
-- `LenDerivable` (the Löb argument's) coincides with the Δ₁ box `LenProvableV` (the evaluator's).
#print axioms properV_of_small
#print axioms properV_TAct
#print axioms lenProvableV_cut_V'
#print axioms lenDerivable_iff_lenProvableV

end ArithS
