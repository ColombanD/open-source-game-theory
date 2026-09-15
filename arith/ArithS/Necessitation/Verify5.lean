import ArithS.Necessitation.Verify4
import ArithS.Necessitation.Assemble
import ArithS.Necessitation.Bounds

/-!
# ArithS.Necessitation.Verify5 — the size half of the verification list

`Verify4.verifyGraph''_ok4` tracks `ListOK`/`NoDrop'`/`shiftsV`/the goal fact of a `VerifyGraph''` list, but NOT
`len` and NOT `SizeOK`. `Assemble.lean` §6 names that gap `VerifySizeOracle` and §8 packages it as `SizeOracle`,
the last hypothesis of `boundedInnerNec_sixteen_of_size` / `dupoc_self_coop_of_size`.

**`SizeOracle` as stated in `Assemble.lean` §8 is NOT PROVABLE** (machine-checked, 2026-09-15): it binds the numeral
table `T` universally with NO `NumTableOK T N' B'` hypothesis, while every prologue size lemma
(`Prologue.sizeOK_layoutSteps`, `sizeOK_proIns`, `sizeOK_proOr`, `sizeOK_proWk`, `sizeOK_proShift`, `sizeOK_proSS`,
`sizeOK_proAll`, `sizeOK_proExs`, `sizeOK_proIns0`) REQUIRES one and lands in the class
`(layQ B B' D, layD N' B' D)`, whose only route to the kit class `(kitQ Cz B E, kitD Cz d)` is `Assemble.layQ_le` /
`layD_le` — and those need `N'`, `B'` as NUMBERS. With `T` free Lean cannot even elaborate the application:
`don't know how to synthesize implicit argument N'`. `Assemble.vList_full` escapes exactly because it CARRIES
`htblN : NumTableOK T (N' : V) (B' : V)` as a hypothesis (it proves `layQ_le`/`layD_le` for its own `layoutSteps {x}`
block that way) and consumes the oracle's output already in kit shape.

So this file proves the `NumTableOK`-CARRYING variant `verifySizeOracle_of` — the same content, with the hypothesis
its own proof obligations require — and then BYPASSES `SizeOracle` by re-assembling the package locally: the only
consumer, `Assemble.kitPackage'''_of_size`, applies the oracle at the CANONICAL numeral table of
`NumSteps.exists_numTable`, where `N'`/`B'` ARE fixed naturals. The headline theorems are unchanged.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

/-! ## 1. Monotonicity of the layout size class in its size parameter -/

section layMono

lemma lenQ_mono (B' : V) {a b : V} (h : a ≤ b) : lenQ B' a ≤ lenQ B' b :=
  mul_le_mul_of_nonneg_left (cTE_mono h) zero_le

lemma lenD_mono (N' B' : V) {a b : V} (h : a ≤ b) : lenD N' B' a ≤ lenD N' B' b := by
  unfold lenD
  exact mul_le_mul (mul_le_mul (add_le_add h le_rfl) (add_le_add (length_monotone h) le_rfl) zero_le zero_le)
    (nodeCost_mono (cTE_mono h)) zero_le zero_le

lemma sum2Q_mono (B : V) {a b : V} (h : a ≤ b) : sum2Q B a ≤ sum2Q B b := by
  unfold sum2Q
  exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (length_monotone h) zero_le) le_rfl) zero_le

lemma sum2D_mono (N' B' : V) {a b : V} (h : a ≤ b) : sum2D N' B' a ≤ sum2D N' B' b := by
  unfold sum2D
  have hl : ‖a‖ ≤ ‖b‖ := length_monotone h
  have hE : 18 * ‖a‖ + 7 ≤ 18 * ‖b‖ + 7 := add_le_add (mul_le_mul_of_nonneg_left hl zero_le) le_rfl
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (mul_le_mul (add_le_add hl le_rfl) (add_le_add hl le_rfl) zero_le zero_le)
      (nodeCost_mono hE) zero_le zero_le) zero_le

lemma layQ_mono (B B' : V) {a b : V} (h : a ≤ b) : layQ B B' a ≤ layQ B B' b := by
  unfold layQ; exact add_le_add (lenQ_mono B' h) (sum2Q_mono B h)

lemma layD_mono (N' B' : V) {a b : V} (h : a ≤ b) : layD N' B' a ≤ layD N' B' b := by
  unfold layD; exact add_le_add (lenD_mono N' B' h) (sum2D_mono N' B' h)

end layMono
/-! ## 2. The size invariant of the verification list

The `NumTableOK`-carrying variant of `Assemble.VerifySizeOracle`. The ten arms of the
`Derivation.induction1` glue are, for now, one explicitly named hypothesis (`ArmHyps`);
they are discharged in turn below, mirroring `Verify4.verifyGraph''_ok4` arm for arm with
`len`/`SizeOK` in place of `shiftsV`.

The size classes that occur, and how each lands in the kit class:

* the LAYOUT class `(layQ B B' D, layD N' B' D)` of every prologue (`Prologue.sizeOK_pro*`),
  lifted by `layQ_mono`/`layD_mono` of section 1 to `D = 2d` and then by `Assemble.layQ_le`/`layD_le`;
* the GOAL-FACT class `4 * |goalFact &j u|` of `postIns`/`goalElim` and each node's goal step,
  landed directly by `Assemble.goalFact4_le_kitQ`;
* the `axm` ENTRY class `entryB Cv p`, already carried by `Verify3.AxmEntryOK'`.
-/

section sizeInvariant

/-- The per-arm obligations of the size glue, as ONE named hypothesis (discharged arm by arm below).
This is a scaffold: with it assumed, `verifySizeOracle_of` is immediate; the mathematics is in
replacing it. -/
def ArmHyps (tbl B Wl Wc W₁ W₂ W T : V) (Cz : ℕ) : Prop :=
  ∀ {E A Cv ρ L : V}, AxmTableOK' tbl E walkPieces A Cv → Derivation TAct ρ →
    VerifyGraph'' walkPieces Wl Wc W₁ W₂ W T A ρ L →
    len L ≤ (Cz : V) * (dlen TAct ρ + 1) ^ 4 ∧
      SizeOK (kitQ (Cz : V) B E) (kitD (Cz : V) (dlen TAct ρ)) L

/-- **The size oracle, with the numeral-table hypothesis its proof requires.**

`Assemble.SizeOracle` binds the numeral table `T` with no `NumTableOK`, which makes it unprovable
(see this file's header); this is the same statement with `NumTableOK T N' B'` restored, so `Cz`
may depend on the fixed naturals `N'`, `B'`. Its only consumer, `Assemble.kitPackage'''_of_size`,
applies the oracle at the canonical numeral table of `NumSteps.exists_numTable`, where `N'` and
`B'` are fixed. -/
theorem verifySizeOracle_of_arms {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {tbl B T : V} {Cz : ℕ}
    (harms : ArmHyps tbl B layoutPieces certPieces frag1Pieces frag2Pieces proPieces T Cz) :
    VerifySizeOracle tbl B layoutPieces certPieces frag1Pieces frag2Pieces proPieces T Cz := by
  intro E A Cv rho L hA hd hL
  exact harms hA hd hL

end sizeInvariant

end ArithS
