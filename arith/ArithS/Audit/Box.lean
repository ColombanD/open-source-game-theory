import ArithS.Box.ProperBound
import ArithS.Cells.RedCell

/-!
# ArithS.Audit.Box — the axiom census of the arithmetized layer: Box

This file covers the box layer (`Box/`): bounded D2 in rule form (`Cut`), on codes in every
model (`CutV`), and properness in every model (`ProperBound`).

Split out of the former single `ArithS/Audit.lean` on 2026-09-28; every `#print axioms` line and its
comment block are verbatim (the comment blocks are the historical record). `ArithS/Audit.lean` imports
the nine per-layer files; each line must read `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArithS

-- M4, first field — bounded D2 in rule form: PA-S closes under modus ponens at additive
-- cost `k₁ + k₂ + 10(|φ| + |ψ|) + 9` (sharp: `5|φ| + 10|ψ| + 9`); budget monotonicity; verum.
#print axioms lenBoxNat_mp
#print axioms lenBoxNat_mp_sharp
#print axioms lenBox_mp_nat
#print axioms lenBoxNat_codeBound_mono
#print axioms lenBoxNat_verum
#print axioms proofLenMeta_cutMP

-- M4, bounded D2 INSIDE every model of IΣ₁ (CutV): the cut on codes with proofLen accounting —
-- unconditional for `LenBoxUnbounded` (no code bound), under `ProperBound` for `LenBox`
-- (a theorem at ℕ), and as ONE ℒₒᵣ-sentence proved by IΣ₁/PA/TAct via the completeness theorem.
#print axioms lenBoxUnbounded_mp
#print axioms lenBox_cut_V
#print axioms lenBox_mono_V
#print axioms properBound_nat_TAct
#print axioms pa_proves_cutSentence
#print axioms tact_proves_cutSentence

-- M4, properness INSIDE every model of IΣ₁ (ProperBound): the code/length chain of `ProperPlayer.lean`
-- redone on internal codes by the internal induction principles (no quotes) — `ProperBound V TAct`
-- is a THEOREM, so bounded D2 for `LenBox` is unconditional and the Σ₁ box
-- `LenBoxUnbounded` (the Löb argument's) coincides with the Δ₁ box `LenBox` (the evaluator's).
#print axioms properBound_of_small
#print axioms properBound_TAct
#print axioms lenBox_mp
#print axioms lenBoxUnbounded_iff_lenBox

end ArithS
