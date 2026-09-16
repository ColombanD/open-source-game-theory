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
/-! ## 3. The node codes' derivation lengths, in the layout size class

`Frag1.sizeOK_fragAxL` / `sizeOK_nodeAnd` / … each take `dlen TAct (leafCode tblN L n) ≤ D` (resp. `bin2Code`,
`bin3Code`) as a HYPOTHESIS, and no caller in the tree ever discharges it: `NumSteps` stops at the raw
decompositions `dlen_leafCode_le` / `dlen_bin2Code_le` / `dlen_bin3Code_le` (and one compact `dlen_bin3Code_poly`
with no users). This section supplies the missing bounds, in the shape the layout class already uses:
`Prologue.dlen_sum2Code_le' : dlen (sum2Code T a b n) ≤ sum2D N' B' Dz`, whose proof is the template — with
`K := (‖Dz‖ + 1)(‖Dz‖ + 2) * nodeCost N' B' (18‖Dz‖ + 7)` and `sum2D N' B' Dz = 4 * K`.

Summand counts against `K`: `succCode ≤ K`, `addCode ≤ K`, `leCode ≤ 2K`, the node's own `nodeCost ≤ K`. So
`leafCode ≤ 4K = sum2D`, `bin2Code ≤ 5K` and `bin3Code ≤ 6K`, i.e. all three land in `2 * sum2D N' B' Dz`.
-/

section nodeCodes

variable {T N' B' : V}

/-- The common cubic budget of the layout class: `sum2D N' B' Dz = 4 * codeK N' B' Dz`. -/
noncomputable def codeK (N' B' Dz : V) : V :=
  (‖Dz‖ + 1) * (‖Dz‖ + 2) * nodeCost N' B' (18 * ‖Dz‖ + 7)

lemma sum2D_eq_four_codeK (N' B' Dz : V) : sum2D N' B' Dz = 4 * codeK N' B' Dz := by
  unfold sum2D codeK; rfl

lemma one_le_lenBox (Dz : V) : (1 : V) ≤ (‖Dz‖ + 1) * (‖Dz‖ + 2) :=
  le_trans (by norm_num : (1 : V) ≤ 1 * 2) (mul_le_mul le_add_self le_add_self zero_le zero_le)

lemma nodeCost_le_codeK (N' B' Dz : V) : nodeCost N' B' (18 * ‖Dz‖ + 7) ≤ codeK N' B' Dz := by
  unfold codeK; exact le_mul_of_one_le_left zero_le (one_le_lenBox Dz)

lemma one_le_len_succ (Dz : V) : (1 : V) ≤ ‖Dz‖ + 2 :=
  le_trans (by norm_num : (1 : V) ≤ 2) le_add_self

lemma nodeCost_bk_le_codeK {n Dz : V} (hn : n ≤ Dz) : nodeCost N' B' (18 * ‖n‖ + 7) ≤ codeK N' B' Dz :=
  le_trans (nodeCost_mono (add_le_add (mul_le_mul_of_nonneg_left (length_monotone hn) zero_le) le_rfl))
    (nodeCost_le_codeK N' B' Dz)

/-- `nodeCost` at any `12x + 3` with `x ≤ ‖Dz‖` is below the node budget. -/
lemma nodeCost_add_le (N' B' Dz : V) {x : V} (hx : x ≤ ‖Dz‖) :
    nodeCost N' B' (12 * x + 3) ≤ nodeCost N' B' (18 * ‖Dz‖ + 7) :=
  nodeCost_mono (add_le_add (le_trans (mul_le_mul_of_nonneg_left hx zero_le)
    (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) (by norm_num))

lemma dlen_succCode_le_codeK (htblN : NumTableOK T N' B') {z Dz : V} (hz : z + 1 ≤ Dz) :
    dlen TAct (succCode T z) ≤ codeK N' B' Dz := by
  refine le_trans (dlen_succCode_le htblN z) ?_
  unfold codeK
  have hl : ‖z‖ ≤ ‖Dz‖ := length_monotone (le_trans le_self_add hz)
  -- the node argument: `6‖z+1‖+3 ≤ 12‖Dz‖+3 ≤ 18‖Dz‖+7`
  have hnc : nodeCost N' B' (6 * ‖z + 1‖ + 3) ≤ nodeCost N' B' (18 * ‖Dz‖ + 7) :=
    nodeCost_mono (le_trans (succE_le_addE hz) (addE_le_bkE Dz))
  -- the count: `‖z‖ + 1 ≤ (‖Dz‖ + 1) * (‖Dz‖ + 2)`
  have hcnt : ‖z‖ + 1 ≤ (‖Dz‖ + 1) * (‖Dz‖ + 2) :=
    le_trans (add_le_add hl le_rfl) (le_mul_of_one_le_right zero_le (one_le_len_succ Dz))
  exact mul_le_mul hcnt hnc zero_le zero_le

lemma dlen_addCode_le_codeK (htblN : NumTableOK T N' B') {a b Dz : V} (hab : a + b ≤ Dz) :
    dlen TAct (addCode T a b) ≤ codeK N' B' Dz := by
  refine le_trans (dlen_addCode_le htblN a b) ?_
  unfold codeK
  have hla : ‖a‖ ≤ ‖Dz‖ := length_monotone (le_trans le_self_add hab)
  have hlab : ‖a + b‖ ≤ ‖Dz‖ := length_monotone hab
  exact mul_le_mul (mul_le_mul (add_le_add hla le_rfl) (add_le_add hlab le_rfl) zero_le zero_le)
    (nodeCost_add_le N' B' Dz hlab) zero_le zero_le

lemma dlen_leCode_le_codeK (htblN : NumTableOK T N' B') {a b Dz : V} (hab : a ≤ b) (hb : b ≤ Dz) :
    dlen TAct (leCode T a b) ≤ codeK N' B' Dz + codeK N' B' Dz := by
  refine le_trans (dlen_leCode_le htblN hab) (add_le_add ?_ ?_)
  · refine dlen_addCode_le_codeK htblN ?_
    rw [add_tsub_cancel_of_le hab]; exact hb
  · exact le_trans (nodeCost_add_le N' B' Dz (length_monotone hb)) (nodeCost_le_codeK N' B' Dz)

/-- **`leafCode` lands in the layout class**: `succCode + leCode + nodeCost ≤ K + 2K + K = sum2D`. -/
theorem dlen_leafCode_le' (htblN : NumTableOK T N' B') {a n Dz : V} (h : a + 1 ≤ n) (hn : n ≤ Dz) :
    dlen TAct (leafCode T a n) ≤ sum2D N' B' Dz := by
  have hK := dlen_leafCode_le htblN h
  rw [sum2D_eq_four_codeK]
  refine le_trans hK ?_
  have b1 : dlen TAct (succCode T a) ≤ codeK N' B' Dz :=
    dlen_succCode_le_codeK htblN (le_trans h hn)
  have b2 : dlen TAct (leCode T (a + 1) n) ≤ codeK N' B' Dz + codeK N' B' Dz :=
    dlen_leCode_le_codeK htblN h hn
  have b3 : nodeCost N' B' (18 * ‖n‖ + 7) ≤ codeK N' B' Dz := nodeCost_bk_le_codeK hn
  calc dlen TAct (succCode T a) + dlen TAct (leCode T (a + 1) n) + nodeCost N' B' (18 * ‖n‖ + 7)
      ≤ codeK N' B' Dz + (codeK N' B' Dz + codeK N' B' Dz) + codeK N' B' Dz :=
        add_le_add (add_le_add b1 b2) b3
    _ = 4 * codeK N' B' Dz := by ring

/-- **`bin2Code` lands in twice the layout class**: `addCode + succCode + leCode + nodeCost ≤ 5K ≤ 8K`. -/
theorem dlen_bin2Code_le' (htblN : NumTableOK T N' B') {a b n Dz : V} (h : a + b + 1 ≤ n) (hn : n ≤ Dz) :
    dlen TAct (bin2Code T a b n) ≤ 2 * sum2D N' B' Dz := by
  have hK := dlen_bin2Code_le htblN h
  rw [sum2D_eq_four_codeK]
  refine le_trans hK ?_
  have hab : a + b ≤ Dz := le_trans (le_trans le_self_add h) hn
  have b1 : dlen TAct (addCode T a b) ≤ codeK N' B' Dz := dlen_addCode_le_codeK htblN hab
  have b2 : dlen TAct (succCode T (a + b)) ≤ codeK N' B' Dz :=
    dlen_succCode_le_codeK htblN (le_trans h hn)
  have b3 : dlen TAct (leCode T (a + b + 1) n) ≤ codeK N' B' Dz + codeK N' B' Dz :=
    dlen_leCode_le_codeK htblN h hn
  have b4 : nodeCost N' B' (18 * ‖n‖ + 7) ≤ codeK N' B' Dz := nodeCost_bk_le_codeK hn
  calc dlen TAct (addCode T a b) + dlen TAct (succCode T (a + b)) + dlen TAct (leCode T (a + b + 1) n)
        + nodeCost N' B' (18 * ‖n‖ + 7)
      ≤ codeK N' B' Dz + codeK N' B' Dz + (codeK N' B' Dz + codeK N' B' Dz) + codeK N' B' Dz :=
        add_le_add (add_le_add (add_le_add b1 b2) b3) b4
    _ ≤ 2 * (4 * codeK N' B' Dz) := by
        refine le_of_add_eq' (c := 3 * codeK N' B' Dz) ?_; ring

/-- **`bin3Code` lands in twice the layout class**: two `addCode`, one `succCode`, one `leCode`, one node: `6K ≤ 8K`. -/
theorem dlen_bin3Code_le' (htblN : NumTableOK T N' B') {a b c n Dz : V} (h : a + b + c + 1 ≤ n) (hn : n ≤ Dz) :
    dlen TAct (bin3Code T a b c n) ≤ 2 * sum2D N' B' Dz := by
  have hK := dlen_bin3Code_le htblN h
  rw [sum2D_eq_four_codeK]
  refine le_trans hK ?_
  have habc : a + b + c ≤ Dz := le_trans (le_trans le_self_add h) hn
  have hab : a + b ≤ Dz := le_trans le_self_add habc
  have b1 : dlen TAct (addCode T a b) ≤ codeK N' B' Dz := dlen_addCode_le_codeK htblN hab
  have b2 : dlen TAct (addCode T (a + b) c) ≤ codeK N' B' Dz := dlen_addCode_le_codeK htblN habc
  have b3 : dlen TAct (succCode T (a + b + c)) ≤ codeK N' B' Dz :=
    dlen_succCode_le_codeK htblN (le_trans h hn)
  have b4 : dlen TAct (leCode T (a + b + c + 1) n) ≤ codeK N' B' Dz + codeK N' B' Dz :=
    dlen_leCode_le_codeK htblN h hn
  have b5 : nodeCost N' B' (18 * ‖n‖ + 7) ≤ codeK N' B' Dz := nodeCost_bk_le_codeK hn
  calc dlen TAct (addCode T a b) + dlen TAct (addCode T (a + b) c) + dlen TAct (succCode T (a + b + c))
        + dlen TAct (leCode T (a + b + c + 1) n) + nodeCost N' B' (18 * ‖n‖ + 7)
      ≤ codeK N' B' Dz + codeK N' B' Dz + codeK N' B' Dz + (codeK N' B' Dz + codeK N' B' Dz)
        + codeK N' B' Dz := add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) b5
    _ ≤ 2 * (4 * codeK N' B' Dz) := by
        refine le_of_add_eq' (c := 2 * codeK N' B' Dz) ?_; ring

/-- All three node codes land in `2 * layD N' B' Dz` (`sum2D ≤ layD` by `layD = lenD + sum2D`). -/
lemma sum2D_le_layD (N' B' Dz : V) : sum2D N' B' Dz ≤ layD N' B' Dz := by
  unfold layD; exact le_add_self

end nodeCodes


/-! ## 4. The size-class landing lemmas and the `axm` arm

The three classes of §2's docstring, each landed in the kit class `(kitQ Cz B E, kitD Cz d)`:

* `entryB_le_kitQ` / `entryB_le_kitD` — the `axm` ENTRY class `entryB Cv p = Cv·(|p|+1)³`
  (`Verify3.AxmEntryOK'` already carries `len pro ≤ entryB Cv p` and `SizeOK (entryB Cv p) (entryB Cv p) pro`),
  under `|p| + 1 ≤ d + 1` and the E-room `p3 (d+1) ≤ E`;
* `BE_le_kitQ` — the fragments' closed leaf/bin facts, which `Frag1.formulaLen_{leaf,bin2,bin3}Fact_le` bound by `B·E`;
* `goalFact_le_kitQ` — the goal fact at the SINGLE multiple (`Assemble.goalFact4_le_kitQ` gives `4·|goalFact|`).

Then the first arm: `vAxm' = pro ++ nodeAxm` (`Verify3` §2), so `len = len pro + 9` (`len_nodeAxm`, structural —
the applicability hypotheses of `Frag2.nodeAxm_ok` are NOT needed for the length) and the sizes are the entry's
lifted class appended to `Frag2.sizeOK_nodeAxm`, whose `dlen (leafCode …) ≤ D` side condition is exactly what §3's
`dlen_leafCode_le'` was written to discharge.
-/

section landing

/-- `E ≤ (B + 1)(E + 1)` — the factor `kitQ` hides. -/
lemma le_kitQ_factor (B E : V) : E ≤ (B + 1) * (E + 1) :=
  le_trans le_self_add (le_mul_of_one_le_left zero_le le_add_self)

/-- **The fragments' closed facts land**: `Frag1.formulaLen_{leaf,bin2,bin3}Fact_le` all conclude `≤ B·E`. -/
lemma BE_le_kitQ {Cz B E : V} (hCz : 1 ≤ Cz) : B * E ≤ kitQ Cz B E := by
  unfold kitQ
  calc B * E ≤ (B + 1) * (E + 1) := mul_le_mul le_self_add le_self_add zero_le zero_le
    _ = 1 * ((B + 1) * (E + 1)) := by ring
    _ ≤ Cz * ((B + 1) * (E + 1)) := mul_le_mul_of_nonneg_right hCz zero_le

/-- **The goal fact lands at the single multiple** (`Assemble.goalFact4_le_kitQ` states the quadruple). -/
lemma goalFact_le_kitQ {Cz B E j u : V} (hE1 : 1 ≤ E) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hj : j + 1 ≤ E) (hu : IsSemiterm LAct 0 u) (hlu : termLen LAct u ≤ E)
    (hC : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Cz) :
    formulaLen LAct (goalFact (^&j) u) ≤ kitQ Cz B E :=
  le_trans (le_mul_of_one_le_left zero_le (by norm_num : (1 : V) ≤ 4))
    (goalFact4_le_kitQ hE1 hPle hj hu hlu hC)

/-- **The `axm` entry's `Q` lands**, under the E-room `p3 (d+1) ≤ E` (which `Verify4`'s cap supplies through
`p3_le_p4`) and `Cv ≤ Cz`. -/
lemma entryB_le_kitQ {Cv Cz B E p d : V} (hpd : formulaLen LAct p + 1 ≤ d + 1)
    (hE : p3 (d + 1) ≤ E) (hC : Cv ≤ Cz) : entryB Cv p ≤ kitQ Cz B E := by
  unfold entryB kitQ
  calc Cv * p3 (formulaLen LAct p + 1) ≤ Cz * E :=
        mul_le_mul hC (le_trans (p3_mono hpd) hE) zero_le zero_le
    _ ≤ Cz * ((B + 1) * (E + 1)) := mul_le_mul_of_nonneg_left (le_kitQ_factor B E) zero_le

/-- **The `axm` entry's `D` lands** — `entryB` is cubic and `kitD Cz d = Cz·(d+1)³` (`pow3_eq_p3`). -/
lemma entryB_le_kitD {Cv Cz p d : V} (hpd : formulaLen LAct p + 1 ≤ d + 1) (hC : Cv ≤ Cz) :
    entryB Cv p ≤ kitD Cz d := by
  unfold entryB kitD
  rw [pow3_eq_p3]
  exact mul_le_mul hC (p3_mono hpd) zero_le zero_le

/-- `len (nodeAxm …) = 9`, STRUCTURALLY — `Frag2.nodeAxm_ok` proves the same equation but only under its full
applicability hypotheses, which the size glue does not have at hand. -/
lemma len_nodeAxm (W tblN is il ip L n : V) : len (nodeAxm W tblN is il ip L n) = 9 := by
  unfold nodeAxm nodeAxmHead goalTailLeaf dlenLeafSteps
  rw [len_appendV, len_appendV]
  simp [len_adjoin]
  norm_num

/-- `|p| + 1 ≤ dlen (axm s p) + 1` for `p ∈ s` (`dlen_axm : dlen = setLen s + 1`). -/
lemma axm_hpd {s p : V} (hD : Derivation TAct (axm s p)) (hp : p ∈ s) :
    formulaLen LAct p + 1 ≤ dlen TAct (axm s p) + 1 := by
  rw [dlen_axm hD]
  exact add_le_add (le_trans (formulaLen_le_setLen_of_mem (L := LAct) hp) le_self_add) le_rfl

end landing

section axmArm

/-- **THE `axm` ARM, length half**: `vAxm' = pro ++ nodeAxm`, and the node is nine steps. -/
theorem axm_arm_len (Wc W₂ T s p pro : V) :
    len (vAxm' walkPieces Wc W₂ T s p pro) = len pro + 9 := by
  unfold vAxm'
  rw [len_appendV, len_nodeAxm]

/-- **THE `axm` ARM, size half**: the certificate's own class (`Verify3.AxmEntryOK'`) lifted into the kit class,
appended to `Frag2.sizeOK_nodeAxm` — whose `leafFact` side condition goes through `BE_le_kitQ`, whose goal-fact side
condition through `goalFact_le_kitQ`, and whose `dlen (leafCode …) ≤ D` side condition is §3's `dlen_leafCode_le'`. -/
theorem axm_arm_size {Wc W₂ T s p pro B E Cv Cz : V}
    (hW₂ : W₂ = frag2Pieces)
    (hs : IsFormulaSet LAct s) (hp : p ∈ s) (hax : p ∈ TAct.Δ₁Class)
    (hsz : SizeOK (entryB Cv p) (entryB Cv p) pro)
    (hCv : Cv ≤ Cz) (hCz1 : 1 ≤ Cz)
    (hE1 : 1 ≤ E) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hp3E : p3 (dlen TAct (axm s p) + 1) ≤ E)
    (hgoalE : len (memberList s) + 1 + shiftsV pro + 1 + 1 ≤ E)
    (hbn : termLen LAct (bnum (dlen TAct (axm s p))) ≤ E)
    (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Cz)
    (hleaf : dlen TAct (leafCode T (setLen LAct s) (dlen TAct (axm s p))) ≤ kitD Cz (dlen TAct (axm s p)))
    (hLn : setLen LAct s + 1 ≤ dlen TAct (axm s p))
    (hnE : 18 * ‖dlen TAct (axm s p)‖ + 7 ≤ E) :
    SizeOK (kitQ Cz B E) (kitD Cz (dlen TAct (axm s p))) (vAxm' walkPieces Wc W₂ T s p pro) := by
  have hD : Derivation TAct (axm s p) := Derivation.axm hs hp hax
  have hpd := axm_hpd hD hp
  unfold vAxm'
  refine sizeOK_appendV (hsz.mono (entryB_le_kitQ hpd hp3E hCv) (entryB_le_kitD hpd hCv)) ?_
  refine sizeOK_nodeAxm hW₂ ?_ hleaf ?_
  · exact le_trans (formulaLen_leafFact_le hE1 hPle hnE (le_trans le_self_add hLn)) (BE_le_kitQ hCz1)
  · exact goalFact_le_kitQ hE1 hPle hgoalE (isSemiterm_bnum_LAct 0 _) hbn hcG

end axmArm


/-! ## 5. The `axL` and `verumIntro` arms

The two LEAF arms, and the cheapest after `axm`: `vAxL = proAxL ++ fragAxL` and `vVerum = fragVerum` (no prologue
at all — `Prologue.layout_verum` reads the node's facts straight off the layout). Both fragments are
`head (four steps) ++ goalTailLeaf (five steps)`, so their lengths are `9` structurally, exactly as `len_nodeAxm`.

The size half needs NO layout class: `proAxL = reidxL (certNeg …)` is HORN-ONLY (`Prologue.proAxL_ok`'s third
conjunct), so `Cert.sizeOK_of_hornOnly` places it at ANY class, and the fragment goes through
`Frag1.sizeOK_fragAxL`/`sizeOK_fragVerum` with §4's landing lemmas — `BE_le_kitQ` for the closed `leafFact`,
`goalFact_le_kitQ` for the goal fact, and §3's `dlen_leafCode_le'` for the `dlen (leafCode …) ≤ D` side condition.
-/

section leafArms

lemma len_fragAxL (W tblN is il ip inp L n : V) : len (fragAxL W tblN is il ip inp L n) = 9 := by
  unfold fragAxL fragAxLHead goalTailLeaf dlenLeafSteps
  rw [len_appendV, len_appendV]
  simp [len_adjoin]
  norm_num

lemma len_fragVerum (W tblN is il iv L n : V) : len (fragVerum W tblN is il iv L n) = 9 := by
  unfold fragVerum fragVerumHead goalTailLeaf dlenLeafSteps
  rw [len_appendV, len_appendV]
  simp [len_adjoin]
  norm_num

/-- **The `axL` arm, length half**: the Horn prologue plus the nine-step fragment. -/
theorem axL_arm_len (Ww Wc W₁ T s p : V) :
    len (vAxL Ww Wc W₁ T s p) = len (proAxL Ww Wc T s p 0) + 9 := by
  unfold vAxL
  rw [len_appendV, len_fragAxL]

/-- **The `verumIntro` arm, length half**: the list IS the fragment. -/
theorem verum_arm_len (Ww Wc W₁ T s : V) : len (vVerum Ww Wc W₁ T s) = 9 := by
  unfold vVerum
  rw [len_fragVerum]

/-- **The `axL` arm, size half**, given the prologue's `HornOnly` (`Prologue.proAxL_ok`). -/
theorem axL_arm_size {Ww Wc W₁ T s p B E Cz L n is il ip inp : V} (hW₁ : W₁ = frag1Pieces)
    (hho : HornOnly (proAxL Ww Wc T s p 0))
    (hCz1 : 1 ≤ Cz) (hE1 : 1 ≤ E) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hnE : 18 * ‖n‖ + 7 ≤ E) (hLn : L + 1 ≤ n)
    (hgoalE : is + 1 + 1 ≤ E) (hbn : termLen LAct (bnum n) ≤ E)
    (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Cz)
    (hleaf : dlen TAct (leafCode T L n) ≤ kitD Cz n) :
    SizeOK (kitQ Cz B E) (kitD Cz n) (appendV (proAxL Ww Wc T s p 0) (fragAxL W₁ T is il ip inp L n)) := by
  refine sizeOK_appendV (sizeOK_of_hornOnly hho) ?_
  refine sizeOK_fragAxL hW₁ ?_ hleaf ?_
  · exact le_trans (formulaLen_leafFact_le hE1 hPle hnE (le_trans le_self_add hLn)) (BE_le_kitQ hCz1)
  · exact goalFact_le_kitQ hE1 hPle hgoalE (isSemiterm_bnum_LAct 0 _) hbn hcG

/-- **The `verumIntro` arm, size half**: the fragment alone. -/
theorem verum_arm_size {W₁ T B E Cz L n is il iv : V} (hW₁ : W₁ = frag1Pieces)
    (hCz1 : 1 ≤ Cz) (hE1 : 1 ≤ E) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hnE : 18 * ‖n‖ + 7 ≤ E) (hLn : L + 1 ≤ n)
    (hgoalE : is + 1 + 1 ≤ E) (hbn : termLen LAct (bnum n) ≤ E)
    (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Cz)
    (hleaf : dlen TAct (leafCode T L n) ≤ kitD Cz n) :
    SizeOK (kitQ Cz B E) (kitD Cz n) (fragVerum W₁ T is il iv L n) := by
  refine sizeOK_fragVerum hW₁ ?_ hleaf ?_
  · exact le_trans (formulaLen_leafFact_le hE1 hPle hnE (le_trans le_self_add hLn)) (BE_le_kitQ hCz1)
  · exact goalFact_le_kitQ hE1 hPle hgoalE (isSemiterm_bnum_LAct 0 _) hbn hcG

end leafArms


/-! ## 6. The REUSABLE CORE: the layout class lands in the kit class; the recovery blocks

Every remaining arm (`wk`, `shift`, `and`, `or`, `cut`, `all`, `exs`) is
`prologue ++ child ++ recovery ++ node`, and the prologue's size class is ALWAYS the layout class
`(layQ B B' D, layD N' B' D)` of `Prologue.sizeOK_pro*`. This section lands that class in the kit class once
and for all — which is exactly why the size oracle must CARRY `NumTableOK T N' B'`: `Assemble.layQ_le`/`layD_le`
need `N'` and `B'` as numbers (the defect this file works around, see the header).

`layD_le_kitD`'s cube step goes through `pow3_eq_p3` + `Verify3.p3_mono`; Mathlib's `pow_le_pow_left` does not
exist at this structure (machine-checked).

The RECOVERY blocks are the other half: `Frag1.goalElim` (five steps, recovering a child's goal) and
`Prologue.postIns` (six steps) both sit at the goal-fact class `4·|goalFact …|`, which `Assemble.goalFact4_le_kitQ`
lands directly — at ANY `D`, so they never touch the layout class.
-/

section layoutLanding

/-- **The layout `Q` lands**: `layQ B B' D ≤ kitQ Cz B E` for `D ≤ E` and `19B' + 25 ≤ Cz`. -/
lemma layQ_le_kitQ {B B' D E Cz : V} (hDE : D ≤ E) (hC : 19 * B' + 25 ≤ Cz) :
    layQ B B' D ≤ kitQ Cz B E := by
  unfold kitQ
  exact le_trans (layQ_le B B' D E hDE) (mul_le_mul_of_nonneg_right hC zero_le)

/-- **The layout `D` lands**: `layD N' B' D ≤ kitD Cz d` for `D ≤ d` and `27N' + 525600B' ≤ Cz`. -/
lemma layD_le_kitD {N' B' D d Cz : V} (hDd : D ≤ d) (hC : 27 * N' + 525600 * B' ≤ Cz) :
    layD N' B' D ≤ kitD Cz d := by
  unfold kitD
  refine le_trans (layD_le N' B' D) (mul_le_mul hC ?_ zero_le zero_le)
  rw [pow3_eq_p3, pow3_eq_p3]
  exact p3_mono (add_le_add hDd le_rfl)

/-- **The recovery block `goalElim` lands** (at any `D` — it carries no derivation). -/
lemma sizeOK_goalElim_kit {Cz B E j u D : V} (hE1 : 1 ≤ E)
    (hPle : formulaLen LAct (Ple : V) ≤ B) (hj : j + 1 ≤ E)
    (hu : IsSemiterm LAct 0 u) (hlu : termLen LAct u ≤ E)
    (hC : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Cz) :
    SizeOK (kitQ Cz B E) D (goalElim (^&j) u) :=
  (sizeOK_goalElim (hf_ j) hu).mono (goalFact4_le_kitQ hE1 hPle hj hu hlu hC) le_rfl

/-- **The recovery block `postIns` lands** (likewise at any `D`). -/
lemma sizeOK_postIns_kit {W Cz B E s'' cp n D : V} (hWp : W = proPieces) (hE1 : 1 ≤ E)
    (hPle : formulaLen LAct (Ple : V) ≤ B) (hj : s'' + 1 ≤ E)
    (hbn : termLen LAct (bnum n) ≤ E)
    (hC : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Cz) :
    SizeOK (kitQ Cz B E) D (postIns W s'' cp n) :=
  (sizeOK_postIns hWp D).mono
    (goalFact4_le_kitQ hE1 hPle hj (isSemiterm_bnum_LAct 0 n) hbn hC) le_rfl

end layoutLanding

/-! ## 7. The `wk` and `shift` tier: the node and selector lengths

`vWk = wkPro ++ L' ++ goalElim ++ nodeWk` and `vShift = shiftPro ++ L' ++ goalElim ++ nodeShift`
(`Verify2.lean` §5). The nodes are nine steps, structurally, exactly as `len_nodeAxm`; the SELECTORS split on
the empty child (`Verify2.wkPro`/`shiftPro`), and in the empty branch the pieces are closed lists whose lengths
are literals — `proWk0 ++ emptyFsetPi` is `7 + 4 = 11`, and `proShift0 ++ reset0 ++ emptyFsetPi` is
`11 + 8 + 4 = 23`. In the nonempty branch the length is the prologue's own, bounded by `Prologue.len_proWk_le` /
`len_proShift_le`.
-/

section wkShiftLengths

lemma len_nodeWk (W tblN is il ic id in₁ L m₁ n : V) :
    len (nodeWk W tblN is il ic id in₁ L m₁ n) = 9 := by
  unfold nodeWk nodeWkHead goalTailUnary dlenUnarySteps
  rw [len_appendV, len_appendV]
  simp [len_adjoin]
  norm_num

lemma len_nodeShift (W tblN is il ic id in₁ L m₁ n : V) :
    len (nodeShift W tblN is il ic id in₁ L m₁ n) = 9 := by
  unfold nodeShift nodeShiftHead goalTailUnary dlenUnarySteps
  rw [len_appendV, len_appendV]
  simp [len_adjoin]
  norm_num

lemma len_emptyFsetPi (W : V) : len (emptyFsetPi W) = 4 := by
  unfold emptyFsetPi; simp [len_adjoin]; norm_num

lemma len_reset0 (W : V) : len (reset0 W) = 8 := by
  unfold reset0
  rw [len_appendV, len_layoutSteps0]
  simp [len_adjoin]
  norm_num

/-- The `wk` selector's length, by branch. -/
lemma len_wkPro (Ww Wl Wc W T s c : V) :
    len (wkPro Ww Wl Wc W T s c) =
      if memberList c = 0 then 11 else len (proWk Ww Wl Wc W T s c 0) := by
  unfold wkPro
  by_cases h : memberList c = 0
  · rw [if_pos h, if_pos h, len_appendV, len_proWk0, len_emptyFsetPi]; norm_num
  · rw [if_neg h, if_neg h]

/-- The `shift` selector's length, by branch. -/
lemma len_shiftPro (Ww Wl Wc W T s c : V) :
    len (shiftPro Ww Wl Wc W T s c) =
      if memberList c = 0 then 23 else len (proShift Ww Wl Wc W T s c 0) := by
  unfold shiftPro
  by_cases h : memberList c = 0
  · rw [if_pos h, if_pos h, len_appendV, len_appendV, len_proShift0, len_reset0, len_emptyFsetPi]; norm_num
  · rw [if_neg h, if_neg h]

end wkShiftLengths


/-! ## 8. The `wk`/`shift` selectors' sizes, and the node codes in the kit class

The SELECTORS (`Verify2.wkPro`/`shiftPro`) split on the empty child, so their size discipline needs both branches:
the empty one is closed Horn material (`Prologue.sizeOK_proWk0`/`sizeOK_proShift0` hold at EVERY class; the two
pieces `emptyFsetPi` and `reset0` had no size lemma in the tree and get one here, by tag inspection — rows 81/157/82/84
and `layoutSteps0` + 42/43/158, all tag `0`), and the nonempty one is the layout class of
`Prologue.sizeOK_proWk`/`sizeOK_proShift`.

The unary/binary NODE CODES land too: §3 bounds them by `2·sum2D N' B' Dz`, and `sum2D ≤ layD` absorbs one factor,
so the doubling is absorbed into the kit constant (`2·(27N' + 525600B') ≤ Cz`). These are what `Frag1`/`Frag2`'s
`sizeOK_node*` need for their `dlen (bin2Code …) ≤ D` side conditions at the non-leaf tags.
-/

section selectorSizes

/-- `emptyFsetPi` is size-disciplined at every class (four Horn steps: rows 81, 157, 82, 84). -/
lemma sizeOK_emptyFsetPi {W : V} (hWp : W = proPieces) (Q Dd : V) :
    SizeOK Q Dd (emptyFsetPi W) := by
  have e81 : ∀ ev : V, mkStep proPieces (81 : V) ev = mkStep layoutPieces (81 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 81 (by decide) ev; simpa using this
  have e82 : ∀ ev : V, mkStep proPieces (82 : V) ev = mkStep layoutPieces (82 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 82 (by decide) ev; simpa using this
  have e84 : ∀ ev : V, mkStep proPieces (84 : V) ev = mkStep layoutPieces (84 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 84 (by decide) ev; simpa using this
  unfold emptyFsetPi
  subst hWp
  refine sizeOK_cons (stepSizeOK_of_tag ?_) (sizeOK_cons (stepSizeOK_of_tag ?_)
    (sizeOK_cons (stepSizeOK_of_tag ?_) (sizeOK_single (stepSizeOK_of_tag ?_))))
  · rw [e81, ltag_emptySubsetC rfl]; simp
  · rw [ptag_congSubsetL rfl]; simp
  · rw [e82, ltag_fsetOfSubsetZeroC rfl]; simp
  · rw [e84, ltag_fsetSigmaPiC rfl]; simp

/-- `reset0` is size-disciplined at every class (`layoutSteps0` + rows 42, 43, 158). -/
lemma sizeOK_reset0 {W : V} (hWp : W = proPieces) (Q Dd : V) : SizeOK Q Dd (reset0 W) := by
  have e42 : ∀ ev : V, mkStep proPieces (42 : V) ev = mkStep layoutPieces (42 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 42 (by decide) ev; simpa using this
  have e43 : ∀ ev : V, mkStep proPieces (43 : V) ev = mkStep layoutPieces (43 : V) ev := fun ev ↦ by
    have := mkStep_pro_layout 43 (by decide) ev; simpa using this
  unfold reset0
  subst hWp
  refine sizeOK_appendV (sizeOK_layoutSteps0 rfl Q Dd)
    (sizeOK_cons (stepSizeOK_of_tag ?_) (sizeOK_cons (stepSizeOK_of_tag ?_)
      (sizeOK_single (stepSizeOK_of_tag ?_))))
  · rw [e42, ltag_eqSymm rfl]; simp
  · rw [e43, ltag_eqTrans rfl]; simp
  · rw [ptag_congSetShiftR rfl]; simp

/-- **The `wk` selector is size-disciplined in BOTH branches**, at the layout class. -/
lemma sizeOK_wkPro {Wl Wc W T s c : V} (hWp : W = proPieces)
    {tbl N N' B' B D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hc : c ⊆ s) (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : 0 + 14 * D + 5 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s 0) :
    SizeOK (layQ B B' D) (layD N' B' D) (wkPro walkPieces Wl Wc W T s c) := by
  unfold wkPro
  by_cases h : memberList c = 0
  · rw [if_pos h]
    exact sizeOK_appendV (sizeOK_proWk0 hWp s 0 _ _) (sizeOK_emptyFsetPi hWp _ _)
  · rw [if_neg h]
    exact sizeOK_proWk htbl hP htblN hWl hWc hWp hPle hs hc (one_le_len_memberList_of_ne h) hsD hcD hE hiE hΓ hLay

/-- **The `shift` selector is size-disciplined in BOTH branches**, at the layout class. -/
lemma sizeOK_shiftPro {Wl Wc W T s c : V} (hWp : W = proPieces)
    {tbl N N' B' B D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hc : IsFormulaSet LAct c) (hsc : s = setShift LAct c)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : 0 + 16 * D + 8 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s 0) :
    SizeOK (layQ B B' D) (layD N' B' D) (shiftPro walkPieces Wl Wc W T s c) := by
  unfold shiftPro
  by_cases h : memberList c = 0
  · rw [if_pos h]
    exact sizeOK_appendV (sizeOK_proShift0 hWp 0 _ _)
      (sizeOK_appendV (sizeOK_reset0 hWp _ _) (sizeOK_emptyFsetPi hWp _ _))
  · rw [if_neg h]
    exact sizeOK_proShift htbl hP htblN hWl hWc hWp hPle hs hc hsc (one_le_len_memberList_of_ne h)
      hsD hcD hE hiE hΓ hLay

end selectorSizes

section nodeCodeKit

/-- **`bin2Code` lands in the kit class** (§3's `2·sum2D`, one factor absorbed by `sum2D ≤ layD`). -/
lemma dlen_bin2Code_le_kitD {T N' B' Cz L m n d : V} (htblN : NumTableOK T N' B')
    (h : L + m + 1 ≤ n) (hn : n ≤ 2 * d) (hC : 2 * (27 * N' + 525600 * B') ≤ Cz) :
    dlen TAct (bin2Code T L m n) ≤ kitD Cz (2 * d) := by
  refine le_trans (dlen_bin2Code_le' htblN h hn) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (sum2D_le_layD N' B' (2 * d)) zero_le) ?_
  refine le_trans (mul_le_mul_of_nonneg_left
    (layD_le_kitD (d := 2 * d) le_rfl (le_refl (27 * N' + 525600 * B'))) zero_le) ?_
  unfold kitD
  calc 2 * ((27 * N' + 525600 * B') * (2 * d + 1) ^ 3)
      = (2 * (27 * N' + 525600 * B')) * (2 * d + 1) ^ 3 := by ring
    _ ≤ Cz * (2 * d + 1) ^ 3 := mul_le_mul_of_nonneg_right hC zero_le

/-- **`bin3Code` lands in the kit class**, likewise. -/
lemma dlen_bin3Code_le_kitD {T N' B' Cz L m₁ m₂ n d : V} (htblN : NumTableOK T N' B')
    (h : L + m₁ + m₂ + 1 ≤ n) (hn : n ≤ 2 * d) (hC : 2 * (27 * N' + 525600 * B') ≤ Cz) :
    dlen TAct (bin3Code T L m₁ m₂ n) ≤ kitD Cz (2 * d) := by
  refine le_trans (dlen_bin3Code_le' htblN h hn) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (sum2D_le_layD N' B' (2 * d)) zero_le) ?_
  refine le_trans (mul_le_mul_of_nonneg_left
    (layD_le_kitD (d := 2 * d) le_rfl (le_refl (27 * N' + 525600 * B'))) zero_le) ?_
  unfold kitD
  calc 2 * ((27 * N' + 525600 * B') * (2 * d + 1) ^ 3)
      = (2 * (27 * N' + 525600 * B')) * (2 * d + 1) ^ 3 := by ring
    _ ≤ Cz * (2 * d + 1) ^ 3 := mul_le_mul_of_nonneg_right hC zero_le

end nodeCodeKit


/-! ## 9. The size statement in the shape the package consumes

`Package.lean` §1 names the statement the size glue must deliver: `SizeThm N' B' Cz`, i.e.
`VerifySizeOracle` universally quantified over the models and the tables with `NumTableOK T (N' : V) (B' : V)`
RESTORED — the hypothesis `Assemble.SizeOracle` drops and every prologue size lemma needs. `SizeThmAll` is
`∀ N' B', ∃ Cz, SizeThm N' B' Cz`; the quantifier ORDER is the bypass (`N'`, `B'` fixed first by
`NumSteps.exists_numTable`, `Cz` chosen after, so `Cz` may depend on them).

This section states that shape modulo the ten induction arms, which remain the named hypothesis of §2 lifted
uniformly over the models (`ArmHypsAll`). With the arms discharged, `verifyGraph''_size4_of_arms` IS
`Package.SizeThm N' B' Cz`, and `SizeThmAll` follows by choosing `Cz` per `(N', B')`.

**Status of the arms** (2026-09-16): `axm` (§4), `axL` and `verumIntro` (§5) are PROVED as standalone arm lemmas;
the reusable machinery every remaining arm needs is in place — the layout-class landing (§6 `layQ_le_kitQ`,
`layD_le_kitD`), the recovery blocks (§6 `sizeOK_goalElim_kit`, `sizeOK_postIns_kit`), the `wk`/`shift` node and
selector lengths (§7) and selector sizes (§8 `sizeOK_wkPro`, `sizeOK_shiftPro`), and the node codes in the kit
class (§8 `dlen_bin2Code_le_kitD`, `dlen_bin3Code_le_kitD`). What remains is the assembly of the seven non-leaf
arms (`wk`, `shift`, `and`, `or`, `cut`, `all`, `exs`) from those blocks and the `Derivation.induction1 𝚷`
recursion that threads them — the shape of `Verify4.verifyGraph''_ok4`, with `len`/`SizeOK` in place of `shiftsV`.
-/

section packageShape

/-- The ten arms, uniformly in the model, at a FIXED numeral table (`N'`, `B'` naturals). -/
def ArmHypsAll (N' B' Cz : ℕ) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (tbl B T : V), IndRecTable tbl →
    (∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) → NumTableOK T (N' : V) (B' : V) →
    ArmHyps tbl B layoutPieces certPieces frag1Pieces frag2Pieces proPieces T Cz

/-- **The size theorem in `Package.SizeThm`'s shape**, modulo the ten arms: on every `IndRec` table with its
row-body bound and every numeral table described by the fixed naturals `N'`, `B'`, every graph list of a
`VerifyGraph''` is `≤ Cz·(dlen ρ + 1)^4` long and size-disciplined at the kit class. -/
theorem verifyGraph''_size4_of_arms (N' B' : ℕ) {Cz : ℕ} (harms : ArmHypsAll N' B' Cz) :
    ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (tbl B T : V), IndRecTable tbl →
      (∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) → NumTableOK T (N' : V) (B' : V) →
      VerifySizeOracle tbl B layoutPieces certPieces frag1Pieces frag2Pieces proPieces T Cz :=
  fun V _ _ tbl B T hPA hB htblN ↦ verifySizeOracle_of_arms (harms V tbl B T hPA hB htblN)

end packageShape


/-! ## 10. The `wk` and `shift` arms

The first two NON-LEAF arms, and the template for the remaining five: each list is
`selector ++ (child ++ (recovery ++ node))`, a right-nested `appendV` (`Verify2.lean` §5), so

* the LENGTH is `len selector + (len L' + (5 + 9))` — `len_goalElim = 5` and §7's `len_nodeWk`/`len_nodeShift`;
* the SIZES are `sizeOK_appendV` over the four blocks: the selector at the LAYOUT class (§8's
  `sizeOK_wkPro`/`sizeOK_shiftPro`, covering BOTH branches of the empty-child split) lifted by §6's
  `layQ_le_kitQ`/`layD_le_kitD`; the child from the induction hypothesis; the recovery by §6's
  `sizeOK_goalElim_kit`; and the node by `Frag1.sizeOK_nodeWk`/`Frag2.sizeOK_nodeShift`, whose three side
  conditions are `formulaLen_bin2Fact_le` + §4's `BE_le_kitQ`, §8's `dlen_bin2Code_le_kitD`, and §4's
  `goalFact_le_kitQ`.

The kit class is stated at `kitD Cz (2 * d)` throughout, matching `Verify4`'s `D = 2d` convention (`dlen_bin2Code_le_kitD`
is stated there). TRAP: the recovery block's goal fact is at the CHILD's `dlen d'` while the node's is at the PARENT's
`dlen (wkRule s d')`, so the two term-length hypotheses `hbn`/`hbn'` are genuinely different and both are needed.
-/

section wkShiftArms

/-- **The `wk` arm, length half.** -/
theorem len_vWk_eq (Ww Wl Wc W₁ W T s d' L' : V) :
    len (vWk Ww Wl Wc W₁ W T s d' L') =
      len (wkPro Ww Wl Wc W T s (fstIdx d')) + (len L' + (5 + 9)) := by
  unfold vWk
  rw [len_appendV, len_appendV, len_appendV, len_goalElim, len_nodeWk]

/-- **The `shift` arm, length half.** -/
theorem len_vShift_eq (Ww Wl Wc W₂ W T s d' L' : V) :
    len (vShift Ww Wl Wc W₂ W T s d' L') =
      len (shiftPro Ww Wl Wc W T s (fstIdx d')) + (len L' + (5 + 9)) := by
  unfold vShift
  rw [len_appendV, len_appendV, len_appendV, len_goalElim, len_nodeShift]

/-- **The `wk` arm, size half.** -/
theorem wk_arm_size {Wl Wc W₁ W T s d' L' B E Cz N' B' D d Γ : V}
    (hWp : W = proPieces) (hW₁ : W₁ = frag1Pieces)
    {tbl N : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (htblN : NumTableOK T N' B')
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hsub : fstIdx d' ⊆ s)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (fstIdx d') ≤ D)
    (hEpro : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiEpro : 0 + 14 * D + 5 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s 0)
    (hDE : D ≤ E) (hDd : D ≤ 2 * d)
    (hCQ : 19 * B' + 25 ≤ Cz) (hCD : 27 * N' + 525600 * B' ≤ Cz) (hCz1 : 1 ≤ Cz)
    (hchild : SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) L')
    (hE1 : 1 ≤ E) (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Cz)
    (hgE : len (memberList (fstIdx d')) + 1 + shiftsV L' + 1 ≤ E)
    (hbn : termLen LAct (bnum (dlen TAct d')) ≤ E)
    (hbn' : termLen LAct (bnum (dlen TAct (wkRule s d'))) ≤ E)
    (hnE : 18 * ‖dlen TAct (wkRule s d')‖ + 7 ≤ E)
    (hLn : setLen LAct s + dlen TAct d' + 1 ≤ dlen TAct (wkRule s d'))
    (hnd : dlen TAct (wkRule s d') ≤ 2 * d)
    (hgE2 : shiftsV (wkPro walkPieces Wl Wc W T s (fstIdx d')) + shiftsV L' + 2 + (len (memberList s) + 1) + 1 + 1 ≤ E)
    (hCbin : 2 * (27 * N' + 525600 * B') ≤ Cz) :
    SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) (vWk walkPieces Wl Wc W₁ W T s d' L') := by
  unfold vWk
  refine sizeOK_appendV ?_ (sizeOK_appendV hchild (sizeOK_appendV ?_ ?_))
  · exact (sizeOK_wkPro hWp htbl hP htblN hWl hWc hPle hs hsub hsD hcD hEpro hiEpro hΓ hLay).mono
      (layQ_le_kitQ hDE hCQ) (layD_le_kitD hDd hCD)
  · exact sizeOK_goalElim_kit hE1 hPle hgE (isSemiterm_bnum_LAct 0 _) hbn hcG
  · refine sizeOK_nodeWk hW₁ ?_ ?_ ?_
    · exact le_trans (formulaLen_bin2Fact_le hE1 hPle hnE
        (le_trans (le_trans le_self_add le_self_add) hLn) (le_trans (le_trans le_add_self le_self_add) hLn))
        (BE_le_kitQ hCz1)
    · exact dlen_bin2Code_le_kitD htblN hLn hnd hCbin
    · exact goalFact_le_kitQ hE1 hPle hgE2 (isSemiterm_bnum_LAct 0 _) hbn' hcG

/-- **The `shift` arm, size half.** -/
theorem shift_arm_size {Wl Wc W₂ W T s d' L' B E Cz N' B' D d Γ : V}
    (hWp : W = proPieces) (hW₂ : W₂ = frag2Pieces)
    {tbl N : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (htblN : NumTableOK T N' B')
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hc : IsFormulaSet LAct (fstIdx d')) (hsc : s = setShift LAct (fstIdx d'))
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (fstIdx d') ≤ D)
    (hEpro : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiEpro : 0 + 16 * D + 8 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s 0)
    (hDE : D ≤ E) (hDd : D ≤ 2 * d)
    (hCQ : 19 * B' + 25 ≤ Cz) (hCD : 27 * N' + 525600 * B' ≤ Cz) (hCz1 : 1 ≤ Cz)
    (hchild : SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) L')
    (hE1 : 1 ≤ E) (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Cz)
    (hgE : len (memberList (fstIdx d')) + 1 + shiftsV L' + 1 ≤ E)
    (hbn : termLen LAct (bnum (dlen TAct d')) ≤ E)
    (hbn' : termLen LAct (bnum (dlen TAct (shiftRule s d'))) ≤ E)
    (hnE : 18 * ‖dlen TAct (shiftRule s d')‖ + 7 ≤ E)
    (hLn : setLen LAct s + dlen TAct d' + 1 ≤ dlen TAct (shiftRule s d'))
    (hnd : dlen TAct (shiftRule s d') ≤ 2 * d)
    (hgE2 : shiftsV (shiftPro walkPieces Wl Wc W T s (fstIdx d')) + shiftsV L' + 2 + (len (memberList s) + 1) + 1 + 1 ≤ E)
    (hCbin : 2 * (27 * N' + 525600 * B') ≤ Cz) :
    SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) (vShift walkPieces Wl Wc W₂ W T s d' L') := by
  unfold vShift
  refine sizeOK_appendV ?_ (sizeOK_appendV hchild (sizeOK_appendV ?_ ?_))
  · exact (sizeOK_shiftPro hWp htbl hP htblN hWl hWc hPle hs hc hsc hsD hcD hEpro hiEpro hΓ hLay).mono
      (layQ_le_kitQ hDE hCQ) (layD_le_kitD hDd hCD)
  · exact sizeOK_goalElim_kit hE1 hPle hgE (isSemiterm_bnum_LAct 0 _) hbn hcG
  · refine sizeOK_nodeShift hW₂ ?_ ?_ ?_
    · exact le_trans (formulaLen_bin2Fact_le hE1 hPle hnE
        (le_trans (le_trans le_self_add le_self_add) hLn) (le_trans (le_trans le_add_self le_self_add) hLn))
        (BE_le_kitQ hCz1)
    · exact dlen_bin2Code_le_kitD htblN hLn hnd hCbin
    · exact goalFact_le_kitQ hE1 hPle hgE2 (isSemiterm_bnum_LAct 0 _) hbn' hcG

end wkShiftArms


/-! ## 11. The `or` arm, and the binary nodes' lengths

`vOr = proOr ++ (L' ++ (postIns ++ nodeOr))` — the four-block shape of §10 with `Prologue.postIns` (six steps) as the
recovery block in place of `goalElim` (five), so the tail contributes `6 + 9`. The size halves differ from `wk`/`shift`
only in the prologue (`Prologue.sizeOK_proOr`, which additionally wants the two dossier hypotheses `DossF … p`/`… q`
that `Prologue.layout_or` supplies at the glue level) and in the recovery block (§6's `sizeOK_postIns_kit`).

The three NON-LEAF node lengths are proved here together: `nodeOr` sits on the UNARY tail (`goalTailUnary`), `nodeAnd`
and `nodeCut` on the BINARY one (`goalTailBinary`), and all three are `head (four steps) ++ tail (five steps) = 9`,
the same structural computation as `len_nodeAxm`. `len_nodeAnd`/`len_nodeCut` are advance work for §12.
-/

section orArm

lemma len_nodeOr (W tblN is il ir ip iq id icq ic in₁ L m₁ n : V) :
    len (nodeOr W tblN is il ir ip iq id icq ic in₁ L m₁ n) = 9 := by
  unfold nodeOr nodeOrHead goalTailUnary dlenUnarySteps
  rw [len_appendV, len_appendV]
  simp [len_adjoin]
  norm_num

lemma len_nodeAnd (W tblN is il ir ip iq id₁ id₂ icp icq in₁ in₂ L m₁ m₂ n : V) :
    len (nodeAnd W tblN is il ir ip iq id₁ id₂ icp icq in₁ in₂ L m₁ m₂ n) = 9 := by
  unfold nodeAnd nodeAndHead goalTailBinary dlenBinarySteps
  rw [len_appendV, len_appendV]
  simp [len_adjoin]
  norm_num

lemma len_nodeCut (W tblN is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂ L m₁ m₂ n : V) :
    len (nodeCut W tblN is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂ L m₁ m₂ n) = 9 := by
  unfold nodeCut nodeCutHead goalTailBinary dlenBinarySteps
  rw [len_appendV, len_appendV]
  simp [len_adjoin]
  norm_num

/-- **The `or` arm, length half** (`postIns` is six steps, so the tail is `6 + 9`). -/
theorem len_vOr_eq (Ww Wl Wc W₁ W T s p q d' L' : V) :
    len (vOr Ww Wl Wc W₁ W T s p q d' L') =
      len (proOr Ww Wl Wc W T s p q 0 (memTop Ww Wc T s (p ^⋎ q) 0 + descCountF Ww 0 q + 1)
        (memTop Ww Wc T s (p ^⋎ q) 0 + 1)) + (len L' + (6 + 9)) := by
  unfold vOr
  rw [len_appendV, len_appendV, len_appendV, len_postIns, len_nodeOr]

/-- **The `or` arm, size half.** -/
theorem or_arm_size {Wl Wc W₁ W T s p q d' L' B E Cz N' B' D d Γ : V}
    (hWp : W = proPieces) (hW₁ : W₁ = frag1Pieces)
    {tbl N : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (htblN : NumTableOK T N' B')
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p) (hq : IsSemiformula LAct 0 q)
    (hk1 : 1 ≤ len (memberList s)) (hsD : setLen LAct (insert p (insert q s)) ≤ D)
    (hEpro : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiEpro : 0 + 14 * D + 5 ≤ E)
    (hipE : memTop walkPieces Wc T s (p ^⋎ q) 0 + descCountF walkPieces 0 q + 1 + 14 * D + 6 ≤ E)
    (hiqE : memTop walkPieces Wc T s (p ^⋎ q) 0 + 1 + 8 * D + 4 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s 0)
    (hDp : DossF walkPieces Γ 0 p (memTop walkPieces Wc T s (p ^⋎ q) 0 + descCountF walkPieces 0 q + 1))
    (hDq : DossF walkPieces Γ 0 q (memTop walkPieces Wc T s (p ^⋎ q) 0 + 1))
    (hDE : D ≤ E) (hDd : D ≤ 2 * d)
    (hCQ : 19 * B' + 25 ≤ Cz) (hCD : 27 * N' + 525600 * B' ≤ Cz) (hCz1 : 1 ≤ Cz)
    (hchild : SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) L')
    (hE1 : 1 ≤ E) (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Cz)
    (hgE : len (memberList (insert p (insert q s))) + 1 + shiftsV L' + 1 ≤ E)
    (hbn : termLen LAct (bnum (dlen TAct d')) ≤ E)
    (hbn' : termLen LAct (bnum (dlen TAct (orIntro s p q d'))) ≤ E)
    (hnE : 18 * ‖dlen TAct (orIntro s p q d')‖ + 7 ≤ E)
    (hLn : setLen LAct s + dlen TAct d' + 1 ≤ dlen TAct (orIntro s p q d'))
    (hnd : dlen TAct (orIntro s p q d') ≤ 2 * d)
    (hgE2 : 1 + proSig walkPieces Wl Wc W T (insert q s) +
      (1 + proSig walkPieces Wl Wc W T (insert p (insert q s))) + shiftsV L' + 2 + (len (memberList s) + 1) + 1 + 1 ≤ E)
    (hCbin : 2 * (27 * N' + 525600 * B') ≤ Cz) :
    SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) (vOr walkPieces Wl Wc W₁ W T s p q d' L') := by
  unfold vOr
  refine sizeOK_appendV ?_ (sizeOK_appendV hchild (sizeOK_appendV ?_ ?_))
  · exact (sizeOK_proOr htbl hP htblN hWl hWc hWp hPle hs hp hq hk1 hsD hEpro hiEpro hipE hiqE hΓ hLay hDp hDq).mono
      (layQ_le_kitQ hDE hCQ) (layD_le_kitD hDd hCD)
  · exact sizeOK_postIns_kit hWp hE1 hPle hgE hbn hcG
  · refine sizeOK_nodeOr hW₁ ?_ ?_ ?_
    · exact le_trans (formulaLen_bin2Fact_le hE1 hPle hnE
        (le_trans (le_trans le_self_add le_self_add) hLn) (le_trans (le_trans le_add_self le_self_add) hLn))
        (BE_le_kitQ hCz1)
    · exact dlen_bin2Code_le_kitD htblN hLn hnd hCbin
    · exact goalFact_le_kitQ hE1 hPle hgE2 (isSemiterm_bnum_LAct 0 _) hbn' hcG

end orArm


/-! ## 12. The `and` and `cut` arms

The two-child arms. `vAnd` is SEVEN blocks — `proIns ++ L₁ ++ postIns ++ proIns ++ L₂ ++ postIns ++ nodeAnd` — and
`vCut` is EIGHT: `proCutPre ++ cutPro ++ L₁ ++ postIns ++ cutPro ++ L₂ ++ postIns ++ nodeCut`. Both nodes sit on the
BINARY tail, so their side conditions are `bin3Fact`/`bin3Code` (§8's `dlen_bin3Code_le_kitD`).

Two new landing lemmas are needed and proved here:

* `sizeOK_proCutPre_kit` — `Prologue.sizeOK_proCutPre` lands in `(lenQ B' D + Q', lenD N' B' D + D')` at ANY `Q'`,
  `D'`, NOT the layout class; instantiating `Q' = D' = 0` and routing `lenQ ≤ layQ` (`lenQ_le_layQ`, by definition
  since `layQ = lenQ + sum2Q`) puts it in the kit class;
* `sizeOK_cutPro` — the `cut` selector splits on the EMPTY PARENT (`proIns0` vs `proIns`), the third and last
  selector split in the file (§8 did `wkPro`/`shiftPro`, which split on the empty CHILD).

The second `proIns`/`cutPro` of each arm runs in a LATER context (after the first child and its `postIns`), so the
arms take that context and its layout as separate hypotheses — the glue supplies them by transport. TRAP: a context
variable introduced only in a hypothesis is autobound AFTER the section's `variable {V …}`, leaving its `V` a
metavariable and stalling instance search ("typeclass instance problem is stuck"); bind it in the binder list.
-/

section andCutArms

/-- `lenQ ≤ layQ`, by definition (`layQ = lenQ + sum2Q`). -/
lemma lenQ_le_layQ (B B' Dz : V) : lenQ B' Dz ≤ layQ B B' Dz := by unfold layQ; exact le_self_add

/-- `lenD ≤ layD`, by definition (`layD = lenD + sum2D`). -/
lemma lenD_le_layD (N' B' Dz : V) : lenD N' B' Dz ≤ layD N' B' Dz := by unfold layD; exact le_self_add

/-- **`proCutPre` lands in the kit class**: its class is `(lenQ B' D + Q', lenD N' B' D + D')` at ANY `Q'`, `D'`,
so instantiate `Q' := 0`, `D' := 0` and route `lenQ ≤ layQ ≤ kitQ`. -/
lemma sizeOK_proCutPre_kit {tbl N N' B' T Wc p B E Cz D d Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWc : Wc = certPieces)
    (hp : IsSemiformula LAct 0 p) (hpD : formulaLen LAct p ≤ D) (hnpD : formulaLen LAct (neg LAct p) ≤ D)
    (hE : 13 * D + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hDE : D ≤ E) (hDd : D ≤ 2 * d)
    (hCQ : 19 * B' + 25 ≤ Cz) (hCD : 27 * N' + 525600 * B' ≤ Cz) :
    SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) (proCutPre walkPieces Wc T p) := by
  have h := sizeOK_proCutPre (B' := B') (Q' := 0) (D' := 0) htbl hP htblN hWc hp hpD hnpD hE hΓ
  refine h.mono ?_ ?_
  · rw [add_zero]; exact le_trans (lenQ_le_layQ B B' D) (layQ_le_kitQ hDE hCQ)
  · rw [add_zero]; exact le_trans (lenD_le_layD N' B' D) (layD_le_kitD hDd hCD)

/-- **The `cut` selector is size-disciplined in BOTH branches** (the empty-PARENT split), at the layout class. -/
lemma sizeOK_cutPro {Wl Wc W T s p i ip : V} (hWp : W = proPieces)
    {tbl N N' B' B D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p)
    (hsD : setLen LAct (insert p s) ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E) (hiE : i + 14 * D + 5 ≤ E) (hipE : ip + 8 * D + 4 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hDp : DossF walkPieces Γ 0 p ip)
    (hLay : Layout walkPieces Wc T Γ s i) (hLay0 : Layout0 walkPieces Wc T Γ i)
    (hsD0 : setLen LAct (insert p (0 : V)) ≤ D) :
    SizeOK (layQ B B' D) (layD N' B' D) (cutPro walkPieces Wl Wc W T s p i ip) := by
  unfold cutPro
  by_cases h : memberList s = 0
  · rw [if_pos h]
    exact sizeOK_proIns0 htbl hP htblN hWl hWc hWp hPle hp hsD0 hE hiE hipE hΓ hLay0 hDp
  · rw [if_neg h]
    exact sizeOK_proIns htbl hP htblN hWl hWc hWp hPle hs hp (one_le_len_memberList_of_ne h) hsD hE hiE hipE hΓ hLay hDp

/-- **The `and` arm, length half**: seven blocks, two `postIns` (six each), the node (nine). -/
theorem len_vAnd_eq (Ww Wl Wc W₁ W T s p q dp dq L₁ L₂ : V) :
    len (vAnd Ww Wl Wc W₁ W T s p q dp dq L₁ L₂) =
      len (proIns Ww Wl Wc W T s p 0 (memTop Ww Wc T s (p ^⋏ q) 0 + descCountF Ww 0 q + 1)) +
      (len L₁ + (6 +
        (len (proIns Ww Wl Wc W T s q (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2)
          (memTop Ww Wc T s (p ^⋏ q) 0 + 1 + (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2))) +
          (len L₂ + (6 + 9))))) := by
  unfold vAnd
  rw [len_appendV, len_appendV, len_appendV, len_appendV, len_appendV, len_appendV,
    len_postIns, len_postIns, len_nodeAnd]

/-- **The `cut` arm, length half**: eight blocks. -/
theorem len_vCut_eq (Ww Wl Wc W₁ W T s p d₁ d₂ L₁ L₂ : V) :
    len (vCut Ww Wl Wc W₁ W T s p d₁ d₂ L₁ L₂) =
      len (proCutPre Ww Wc T p) +
      (len (cutPro Ww Wl Wc W T s p (mShift Ww Wc T p + mShift Ww Wc T (neg LAct p))
        (mLen Wc T p + mShift Ww Wc T (neg LAct p))) +
        (len L₁ + (6 +
          (len (cutPro Ww Wl Wc W T s (neg LAct p)
            (mShift Ww Wc T p + mShift Ww Wc T (neg LAct p) + (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2))
            (mLen Wc T (neg LAct p) + (1 + proSig Ww Wl Wc W T (insert p s) + shiftsV L₁ + 2))) +
            (len L₂ + (6 + 9)))))) := by
  unfold vCut
  rw [len_appendV, len_appendV, len_appendV, len_appendV, len_appendV, len_appendV, len_appendV,
    len_postIns, len_postIns, len_nodeCut]

/-- **The `and` arm, size half** — seven blocks, two children, two `postIns`, a `bin3` node. -/
theorem and_arm_size {Wl Wc W₁ W T s p q dp dq L₁ L₂ B E Cz N' B' D d Γ Γ₃ : V}
    (hWp : W = proPieces) (hW₁ : W₁ = frag1Pieces)
    {tbl N : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (htblN : NumTableOK T N' B')
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p) (hq : IsSemiformula LAct 0 q)
    (hk1 : 1 ≤ len (memberList s))
    (hsDp : setLen LAct (insert p s) ≤ D) (hsDq : setLen LAct (insert q s) ≤ D)
    (hEpro : 13 * D + 18 * ‖D‖ + 12 ≤ E)
    (hiE₁ : 0 + 14 * D + 5 ≤ E)
    (hipE₁ : memTop walkPieces Wc T s (p ^⋏ q) 0 + descCountF walkPieces 0 q + 1 + 8 * D + 4 ≤ E)
    (hiE₂ : 1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2 + 14 * D + 5 ≤ E)
    (hipE₂ : memTop walkPieces Wc T s (p ^⋏ q) 0 + 1 +
      (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2) + 8 * D + 4 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s 0)
    (hDp : DossF walkPieces Γ 0 p (memTop walkPieces Wc T s (p ^⋏ q) 0 + descCountF walkPieces 0 q + 1))
    (hΓ₃ : IsFormulaSet LAct Γ₃)
    (hLay₃ : Layout walkPieces Wc T Γ₃ s (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2))
    (hDq₃ : DossF walkPieces Γ₃ 0 q (memTop walkPieces Wc T s (p ^⋏ q) 0 + 1 +
      (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2)))
    (hDE : D ≤ E) (hDd : D ≤ 2 * d)
    (hCQ : 19 * B' + 25 ≤ Cz) (hCD : 27 * N' + 525600 * B' ≤ Cz) (hCz1 : 1 ≤ Cz)
    (hchild₁ : SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) L₁)
    (hchild₂ : SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) L₂)
    (hE1 : 1 ≤ E) (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Cz)
    (hgE₁ : len (memberList (insert p s)) + 1 + shiftsV L₁ + 1 ≤ E)
    (hgE₂ : len (memberList (insert q s)) + 1 + shiftsV L₂ + 1 ≤ E)
    (hbn₁ : termLen LAct (bnum (dlen TAct dp)) ≤ E)
    (hbn₂ : termLen LAct (bnum (dlen TAct dq)) ≤ E)
    (hbn' : termLen LAct (bnum (dlen TAct (andIntro s p q dp dq))) ≤ E)
    (hnE : 18 * ‖dlen TAct (andIntro s p q dp dq)‖ + 7 ≤ E)
    (hLn : setLen LAct s + dlen TAct dp + dlen TAct dq + 1 ≤ dlen TAct (andIntro s p q dp dq))
    (hnd : dlen TAct (andIntro s p q dp dq) ≤ 2 * d)
    (hgE3 : 1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2 +
      (1 + proSig walkPieces Wl Wc W T (insert q s) + shiftsV L₂ + 2) + (len (memberList s) + 1) + 1 + 1 ≤ E)
    (hCbin : 2 * (27 * N' + 525600 * B') ≤ Cz) :
    SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) (vAnd walkPieces Wl Wc W₁ W T s p q dp dq L₁ L₂) := by
  unfold vAnd
  refine sizeOK_appendV ?_ (sizeOK_appendV hchild₁ (sizeOK_appendV ?_
    (sizeOK_appendV ?_ (sizeOK_appendV hchild₂ (sizeOK_appendV ?_ ?_)))))
  · exact (sizeOK_proIns htbl hP htblN hWl hWc hWp hPle hs hp hk1 hsDp hEpro hiE₁ hipE₁ hΓ hLay hDp).mono
      (layQ_le_kitQ hDE hCQ) (layD_le_kitD hDd hCD)
  · exact sizeOK_postIns_kit hWp hE1 hPle hgE₁ hbn₁ hcG
  · exact (sizeOK_proIns htbl hP htblN hWl hWc hWp hPle hs hq hk1 hsDq hEpro hiE₂ hipE₂ hΓ₃ hLay₃ hDq₃).mono
      (layQ_le_kitQ hDE hCQ) (layD_le_kitD hDd hCD)
  · exact sizeOK_postIns_kit hWp hE1 hPle hgE₂ hbn₂ hcG
  · refine sizeOK_nodeAnd hW₁ ?_ ?_ ?_
    · exact le_trans (formulaLen_bin3Fact_le hE1 hPle hnE
        (le_trans (le_trans (le_trans le_self_add le_self_add) le_self_add) hLn)
        (le_trans (le_trans (le_trans le_add_self le_self_add) le_self_add) hLn)
        (le_trans (le_trans le_add_self le_self_add) hLn))
        (BE_le_kitQ hCz1)
    · exact dlen_bin3Code_le_kitD htblN hLn hnd hCbin
    · exact goalFact_le_kitQ hE1 hPle hgE3 (isSemiterm_bnum_LAct 0 _) hbn' hcG

/-- **The `cut` arm, size half** — eight blocks: `proCutPre`, two `cutPro` selectors, two children, two `postIns`,
the node. -/
theorem cut_arm_size {Wl Wc W₁ W T s p d₁ d₂ L₁ L₂ B E Cz N' B' D d Γ Γ₄ Γc : V}
    (hWp : W = proPieces) (hW₁ : W₁ = frag1Pieces)
    {tbl N : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (htblN : NumTableOK T N' B')
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p)
    (hpD : formulaLen LAct p ≤ D) (hnpD : formulaLen LAct (neg LAct p) ≤ D)
    (hsDp : setLen LAct (insert p s) ≤ D) (hsDnp : setLen LAct (insert (neg LAct p) s) ≤ D)
    (hsD0p : setLen LAct (insert p (0 : V)) ≤ D) (hsD0np : setLen LAct (insert (neg LAct p) (0 : V)) ≤ D)
    (hEpre : 13 * D + 8 ≤ E) (hEpro : 13 * D + 18 * ‖D‖ + 12 ≤ E)
    (hiE₁ : mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) + 14 * D + 5 ≤ E)
    (hipE₁ : mLen Wc T p + mShift walkPieces Wc T (neg LAct p) + 8 * D + 4 ≤ E)
    (hiE₂ : mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) +
      (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2) + 14 * D + 5 ≤ E)
    (hipE₂ : mLen Wc T (neg LAct p) + (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2) + 8 * D + 4 ≤ E)
    (hΓ : IsFormulaSet LAct Γ)
    (hLay₁ : Layout walkPieces Wc T Γ s (mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p)))
    (hLay0₁ : Layout0 walkPieces Wc T Γ (mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p)))
    (hDp₁ : DossF walkPieces Γ 0 p (mLen Wc T p + mShift walkPieces Wc T (neg LAct p)))
    (hΓ₄ : IsFormulaSet LAct Γ₄)
    (hLay₄ : Layout walkPieces Wc T Γ₄ s (mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) +
      (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2)))
    (hLay0₄ : Layout0 walkPieces Wc T Γ₄ (mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) +
      (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2)))
    (hDnp₄ : DossF walkPieces Γ₄ 0 (neg LAct p)
      (mLen Wc T (neg LAct p) + (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2)))
    (hΓc : IsFormulaSet LAct Γc)
    (hDE : D ≤ E) (hDd : D ≤ 2 * d)
    (hCQ : 19 * B' + 25 ≤ Cz) (hCD : 27 * N' + 525600 * B' ≤ Cz) (hCz1 : 1 ≤ Cz)
    (hchild₁ : SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) L₁)
    (hchild₂ : SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) L₂)
    (hE1 : 1 ≤ E) (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Cz)
    (hgE₁ : len (memberList (insert p s)) + 1 + shiftsV L₁ + 1 ≤ E)
    (hgE₂ : len (memberList (insert (neg LAct p) s)) + 1 + shiftsV L₂ + 1 ≤ E)
    (hbn₁ : termLen LAct (bnum (dlen TAct d₁)) ≤ E)
    (hbn₂ : termLen LAct (bnum (dlen TAct d₂)) ≤ E)
    (hbn' : termLen LAct (bnum (dlen TAct (cutRule s p d₁ d₂))) ≤ E)
    (hnE : 18 * ‖dlen TAct (cutRule s p d₁ d₂)‖ + 7 ≤ E)
    (hLn : setLen LAct s + dlen TAct d₁ + dlen TAct d₂ + 1 ≤ dlen TAct (cutRule s p d₁ d₂))
    (hnd : dlen TAct (cutRule s p d₁ d₂) ≤ 2 * d)
    (hgE3 : mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) +
      (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2) +
      (1 + proSig walkPieces Wl Wc W T (insert (neg LAct p) s) + shiftsV L₂ + 2) + (len (memberList s) + 1) + 1 + 1 ≤ E)
    (hCbin : 2 * (27 * N' + 525600 * B') ≤ Cz) :
    SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) (vCut walkPieces Wl Wc W₁ W T s p d₁ d₂ L₁ L₂) := by
  unfold vCut
  refine sizeOK_appendV ?_ (sizeOK_appendV ?_ (sizeOK_appendV hchild₁ (sizeOK_appendV ?_
    (sizeOK_appendV ?_ (sizeOK_appendV hchild₂ (sizeOK_appendV ?_ ?_))))))
  · exact sizeOK_proCutPre_kit (B := B) (d := d) htbl hP htblN hWc hp hpD hnpD hEpre hΓc hDE hDd hCQ hCD
  · exact (sizeOK_cutPro hWp htbl hP htblN hWl hWc hPle hs hp hsDp hEpro hiE₁ hipE₁ hΓ hDp₁ hLay₁ hLay0₁ hsD0p).mono
      (layQ_le_kitQ hDE hCQ) (layD_le_kitD hDd hCD)
  · exact sizeOK_postIns_kit hWp hE1 hPle hgE₁ hbn₁ hcG
  · exact (sizeOK_cutPro hWp htbl hP htblN hWl hWc hPle hs hp.neg hsDnp hEpro hiE₂ hipE₂ hΓ₄ hDnp₄ hLay₄ hLay0₄ hsD0np).mono
      (layQ_le_kitQ hDE hCQ) (layD_le_kitD hDd hCD)
  · exact sizeOK_postIns_kit hWp hE1 hPle hgE₂ hbn₂ hcG
  · refine sizeOK_nodeCut hW₁ ?_ ?_ ?_
    · exact le_trans (formulaLen_bin3Fact_le hE1 hPle hnE
        (le_trans (le_trans (le_trans le_self_add le_self_add) le_self_add) hLn)
        (le_trans (le_trans (le_trans le_add_self le_self_add) le_self_add) hLn)
        (le_trans (le_trans le_add_self le_self_add) hLn))
        (BE_le_kitQ hCz1)
    · exact dlen_bin3Code_le_kitD htblN hLn hnd hCbin
    · exact goalFact_le_kitQ hE1 hPle hgE3 (isSemiterm_bnum_LAct 0 _) hbn' hcG

end andCutArms


/-! ## 13. The `all` and `exs` arms — the last two, and all ten are now proved

Both quantifier arms have the FOUR-block shape of `or` (`Verify2.lean` §5): `proAll ++ (L' ++ (postIns ++ nodeAll))`
and `proExs ++ (L' ++ (postIns ++ nodeExs))`, so their lengths are `len pro + (len L' + (6 + 9))` exactly as
`len_vOr_eq`, and the size halves are the prologue at the LAYOUT class (`Prologue.sizeOK_proAll`/`sizeOK_proExs`,
whose extra `hEQ`/`hiE` hypotheses are the QUADRATIC E-rooms of the certification blocks) lifted by §6, the child
from the induction hypothesis, §6's `sizeOK_postIns_kit`, and the node.

The two nodes differ in their tail: `nodeAll` sits on the UNARY one (`bin2Fact`/`bin2Code`, the child's `dlen`
alone), `nodeExs` on the BINARY one (`bin3Fact`/`bin3Code`, with `Lt = termLen t` as the second summand — the
witness term's length enters the node's arithmetic).

With these, ALL TEN arms have standalone size and length lemmas: `axm` (§4), `axL`/`verumIntro` (§5),
`wk`/`shift` (§10), `or` (§11), `and`/`cut` (§12), `all`/`exs` (here).
-/

section allExsArms

lemma len_nodeAll (W tblN is il ir ip ifp iss ic id in₁ L m₁ n : V) :
    len (nodeAll W tblN is il ir ip ifp iss ic id in₁ L m₁ n) = 9 := by
  unfold nodeAll nodeAllHead goalTailUnary dlenUnarySteps
  rw [len_appendV, len_appendV]
  simp [len_adjoin]
  norm_num

lemma len_nodeExs (W tblN is il ir ip it ipt ic id ilt in₁ L Lt m₁ n : V) :
    len (nodeExs W tblN is il ir ip it ipt ic id ilt in₁ L Lt m₁ n) = 9 := by
  unfold nodeExs nodeExsHead goalTailBinary dlenBinarySteps
  rw [len_appendV, len_appendV]
  simp [len_adjoin]
  norm_num

/-- **The `all` arm, length half.** -/
theorem len_vAll_eq (Ww Wl Wc W₂ W T s p d' L' : V) :
    len (vAll Ww Wl Wc W₂ W T s p d' L') =
      len (proAll Ww Wl Wc W T s p 0) + (len L' + (6 + 9)) := by
  unfold vAll
  rw [len_appendV, len_appendV, len_appendV, len_postIns, len_nodeAll]

/-- **The `exs` arm, length half.** -/
theorem len_vExs_eq (Ww Wl Wc W₂ W T s p t d' L' : V) :
    len (vExs Ww Wl Wc W₂ W T s p t d' L') =
      len (proExs Ww Wl Wc W T s p t 0) + (len L' + (6 + 9)) := by
  unfold vExs
  rw [len_appendV, len_appendV, len_appendV, len_postIns, len_nodeExs]

/-- **The `all` arm, size half** (the node is on the UNARY tail: `bin2Fact`/`bin2Code`). -/
theorem all_arm_size {Wl Wc W₂ W T s p d' L' B E Cz N' B' D d Γ : V}
    (hWp : W = proPieces) (hW₂ : W₂ = frag2Pieces)
    {tbl N : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (htblN : NumTableOK T N' B')
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 1 p) (hr : (^∀ p) ∈ s)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (insert (free LAct p) (setShift LAct s)) ≤ D)
    (hspD : formulaLen LAct (shift LAct p) ≤ D)
    (hEpro : 13 * D + 18 * ‖D‖ + 12 ≤ E)
    (hEQ : 2 * ((1 + D) * (1 + D + 1)) * (D + 1) + 4 * D + 11 ≤ E)
    (hiE : 0 + 2 * ((1 + D) * (1 + D + 1)) * D + 40 * D + 20 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s 0)
    (hDE : D ≤ E) (hDd : D ≤ 2 * d)
    (hCQ : 19 * B' + 25 ≤ Cz) (hCD : 27 * N' + 525600 * B' ≤ Cz) (hCz1 : 1 ≤ Cz)
    (hchild : SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) L')
    (hE1 : 1 ≤ E) (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Cz)
    (hgE : len (memberList (insert (free LAct p) (setShift LAct s))) + 1 + shiftsV L' + 1 ≤ E)
    (hbn : termLen LAct (bnum (dlen TAct d')) ≤ E)
    (hbn' : termLen LAct (bnum (dlen TAct (allIntro s p d'))) ≤ E)
    (hnE : 18 * ‖dlen TAct (allIntro s p d')‖ + 7 ≤ E)
    (hLn : setLen LAct s + dlen TAct d' + 1 ≤ dlen TAct (allIntro s p d'))
    (hnd : dlen TAct (allIntro s p d') ≤ 2 * d)
    (hgE2 : allCertSig walkPieces Wc p +
      (proSig walkPieces Wl Wc W T (setShift LAct s) + (1 + (len (memberList s) + 1) + proSig walkPieces Wl Wc W T s)) +
      (1 + proSig walkPieces Wl Wc W T (insert (free LAct p) (setShift LAct s))) + shiftsV L' + 2 +
      (len (memberList s) + 1) + 1 + 1 ≤ E)
    (hCbin : 2 * (27 * N' + 525600 * B') ≤ Cz) :
    SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) (vAll walkPieces Wl Wc W₂ W T s p d' L') := by
  unfold vAll
  refine sizeOK_appendV ?_ (sizeOK_appendV hchild (sizeOK_appendV ?_ ?_))
  · exact (sizeOK_proAll htbl hP htblN hWl hWc hWp hPle hs hp hr hsD hcD hspD hEpro hEQ hiE hΓ hLay).mono
      (layQ_le_kitQ hDE hCQ) (layD_le_kitD hDd hCD)
  · exact sizeOK_postIns_kit hWp hE1 hPle hgE hbn hcG
  · refine sizeOK_nodeAll hW₂ ?_ ?_ ?_
    · exact le_trans (formulaLen_bin2Fact_le hE1 hPle hnE
        (le_trans (le_trans le_self_add le_self_add) hLn) (le_trans (le_trans le_add_self le_self_add) hLn))
        (BE_le_kitQ hCz1)
    · exact dlen_bin2Code_le_kitD htblN hLn hnd hCbin
    · exact goalFact_le_kitQ hE1 hPle hgE2 (isSemiterm_bnum_LAct 0 _) hbn' hcG

/-- **The `exs` arm, size half** (the node is on the BINARY tail: `bin3Fact`/`bin3Code` with `Lt = termLen t`). -/
theorem exs_arm_size {Wl Wc W₂ W T s p t d' L' B E Cz N' B' D d Γ : V}
    (hWp : W = proPieces) (hW₂ : W₂ = frag2Pieces)
    {tbl N : V} (htbl : TableOK tbl N) (hP : ProTable tbl) (htblN : NumTableOK T N' B')
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 1 p) (hr : (^∃ p) ∈ s)
    (ht : IsSemiterm LAct 0 t)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (insert (substs1 LAct t p) s) ≤ D)
    (htD : termLen LAct t ≤ D)
    (hEpro : 13 * D + 18 * ‖D‖ + 12 ≤ E)
    (hEQ : 2 * ((1 + D) * (1 + D + D)) * (D + 1) + 4 * D + 11 ≤ E)
    (hiE : 0 + 2 * ((1 + D) * (1 + D + D)) * D + 40 * D + 20 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s 0)
    (hDE : D ≤ E) (hDd : D ≤ 2 * d)
    (hCQ : 19 * B' + 25 ≤ Cz) (hCD : 27 * N' + 525600 * B' ≤ Cz) (hCz1 : 1 ≤ Cz)
    (hchild : SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) L')
    (hE1 : 1 ≤ E) (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Cz)
    (hgE : len (memberList (insert (substs1 LAct t p) s)) + 1 + shiftsV L' + 1 ≤ E)
    (hbn : termLen LAct (bnum (dlen TAct d')) ≤ E)
    (hbn' : termLen LAct (bnum (dlen TAct (exsIntro s p t d'))) ≤ E)
    (hnE : 18 * ‖dlen TAct (exsIntro s p t d')‖ + 7 ≤ E)
    (hLn : setLen LAct s + termLen LAct t + dlen TAct d' + 1 ≤ dlen TAct (exsIntro s p t d'))
    (hnd : dlen TAct (exsIntro s p t d') ≤ 2 * d)
    (hgE2 : exsSig walkPieces Wc T s p t 0 +
      (1 + proSig walkPieces Wl Wc W T (insert (substs1 LAct t p) s)) + shiftsV L' + 2 +
      (len (memberList s) + 1) + 1 + 1 ≤ E)
    (hCbin : 2 * (27 * N' + 525600 * B') ≤ Cz) :
    SizeOK (kitQ Cz B E) (kitD Cz (2 * d)) (vExs walkPieces Wl Wc W₂ W T s p t d' L') := by
  unfold vExs
  refine sizeOK_appendV ?_ (sizeOK_appendV hchild (sizeOK_appendV ?_ ?_))
  · exact (sizeOK_proExs htbl hP htblN hWl hWc hWp hPle hs hp hr ht hsD hcD htD hEpro hEQ hiE hΓ hLay).mono
      (layQ_le_kitQ hDE hCQ) (layD_le_kitD hDd hCD)
  · exact sizeOK_postIns_kit hWp hE1 hPle hgE hbn hcG
  · refine sizeOK_nodeExs hW₂ ?_ ?_ ?_
    · exact le_trans (formulaLen_bin3Fact_le hE1 hPle hnE
        (le_trans (le_trans (le_trans le_self_add le_self_add) le_self_add) hLn)
        (le_trans (le_trans (le_trans le_add_self le_self_add) le_self_add) hLn)
        (le_trans (le_trans le_add_self le_self_add) hLn))
        (BE_le_kitQ hCz1)
    · exact dlen_bin3Code_le_kitD htblN hLn hnd hCbin
    · exact goalFact_le_kitQ hE1 hPle hgE2 (isSemiterm_bnum_LAct 0 _) hbn' hcG

end allExsArms


/-! ## 14. The selectors' lengths as BOUNDS — the length gap closed

§7's `len_wkPro`/`len_shiftPro` are branch EQUATIONS (`if memberList c = 0 then 11 else len (proWk …)`), and the
recursion needs a single `≤` covering both branches; `cutPro` had no length lemma at all. This section supplies all
three, in the `D`-shape the induction carries:

* `len_wkPro_le ≤ 44·D + 11` — the empty branch is the literal `11` (`proWk0 ++ emptyFsetPi`, `7 + 4`), the other
  is `Prologue.len_proWk_le`'s `44·setLen c + 7`;
* `len_shiftPro_le ≤ 62·D + 23` — the empty branch is `23` (`proShift0 ++ reset0 ++ emptyFsetPi`, `11 + 8 + 4`),
  the other is `len_proShift_le`'s `61·setLen c + setLen s + 20`, so BOTH size hypotheses are consumed;
* `len_cutPro_le ≤ 55·D + 13` — THE MISSING ONE. `cutPro` splits on the EMPTY PARENT, so the two branches are
  `Prologue.len_proIns0_le`'s `49·setLen (insert p 0) + 13` and `len_proIns_le`'s `55·setLen (insert p s) + 12`;
  the bound takes the larger coefficient from one and the larger constant from the other, and the empty-parent
  branch needs its own size hypothesis (`setLen (insert p 0) ≤ D`) since `insert p 0` is not `insert p s`.
-/

section selectorLengths

/-- **The `wk` selector's length, as a BOUND covering both branches.** -/
theorem len_wkPro_le {tbl N : V} (htbl : TableOK tbl N) (hP : ProTable tbl) {Wl Wc : V}
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (Ww W T s : V) {c D : V}
    (hc : IsFormulaSet LAct c) (hcD : setLen LAct c ≤ D) :
    len (wkPro Ww Wl Wc W T s c) ≤ 44 * D + 11 := by
  rw [len_wkPro]
  by_cases h : memberList c = 0
  · rw [if_pos h]; exact le_add_self
  · rw [if_neg h]
    refine le_trans (len_proWk_le htbl hP hWl hWc Ww W T s 0 hc) ?_
    exact add_le_add (mul_le_mul_of_nonneg_left hcD zero_le) (by norm_num : (7 : V) ≤ 11)

/-- **The `shift` selector's length, as a BOUND covering both branches.** -/
theorem len_shiftPro_le {Wc : V} (hWc : Wc = certPieces) (Ww Wl W T : V) {s c D : V}
    (hs : IsFormulaSet LAct s) (hc : IsFormulaSet LAct c)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct c ≤ D) :
    len (shiftPro Ww Wl Wc W T s c) ≤ 62 * D + 23 := by
  rw [len_shiftPro]
  by_cases h : memberList c = 0
  · rw [if_pos h]; exact le_add_self
  · rw [if_neg h]
    refine le_trans (len_proShift_le hWc Ww Wl W T 0 hs hc) ?_
    calc 61 * setLen LAct c + setLen LAct s + 20 ≤ 61 * D + D + 20 :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hcD zero_le) hsD) le_rfl
      _ = 62 * D + 20 := by ring
      _ ≤ 62 * D + 23 := add_le_add le_rfl (by norm_num : (20 : V) ≤ 23)

/-- **The `cut` selector's length** — the lemma the tree never had (`cutPro` splits on the EMPTY PARENT). -/
theorem len_cutPro_le {tbl N : V} (htbl : TableOK tbl N) (hP : ProTable tbl) {Wl Wc : V}
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (Ww W T i ip : V) {s p D : V}
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p)
    (hsDp : setLen LAct (insert p s) ≤ D) (hsD0 : setLen LAct (insert p (0 : V)) ≤ D) :
    len (cutPro Ww Wl Wc W T s p i ip) ≤ 55 * D + 13 := by
  unfold cutPro
  by_cases h : memberList s = 0
  · rw [if_pos h]
    refine le_trans (len_proIns0_le htbl hP hWl hWc Ww W T i ip hp) ?_
    exact add_le_add (le_trans (mul_le_mul_of_nonneg_left hsD0 zero_le)
      (mul_le_mul_of_nonneg_right (by norm_num : (49 : V) ≤ 55) zero_le)) le_rfl
  · rw [if_neg h]
    refine le_trans (len_proIns_le htbl hP hWl hWc Ww W T i ip hs hp) ?_
    exact add_le_add (mul_le_mul_of_nonneg_left hsDp zero_le) (by norm_num : (12 : V) ≤ 13)

end selectorLengths


/-! ## 15. Three lemmas the recursion needs: `kitD` monotone, the doubling, `leafCode` in the kit class

The arm lemmas of §§4–13 conclude at the class `kitD Cz n` with `n` the node's OWN `dlen`, while the recursion's
motive carries `kitD Cz (2 * dlen ρ)` (the `D = 2d` convention of `Verify4`, which §8's `dlen_bin2Code_le_kitD`
and `dlen_bin3Code_le_kitD` are already stated at). Widening one to the other is `kitD_mono` plus `le_two_mul_self`,
and the third lemma is the `leafCode` analogue of §8's two: §3 bounds it by a SINGLE `sum2D` (not the doubled one),
so no doubling constant is needed and `sum2D ≤ layD ≤ kitD` suffices.

TRAP: in `dlen_leafCode_le_kitD`'s chain the size argument is pinned at `Dz` by `sum2D_le_layD`, so `layD_le_kitD`
there takes `le_rfl`, NOT the `d ≤ 2 * d` widening — that step happens afterwards, through `kitD_mono`.
-/

section recursionPrep

/-- `kitD` is monotone in its size argument (`kitD Cz z = Cz·(z+1)³`). -/
lemma kitD_mono {Cz a b : V} (h : a ≤ b) : kitD Cz a ≤ kitD Cz b := by
  unfold kitD
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  rw [pow3_eq_p3, pow3_eq_p3]
  exact p3_mono (add_le_add h le_rfl)

/-- `d ≤ 2·d`. -/
lemma le_two_mul_self (d : V) : d ≤ 2 * d := le_of_add_eq' (c := d) (by ring)

/-- **`leafCode` lands in the kit class** — the `leafCode` analogue of §8's `dlen_bin2Code_le_kitD`, with NO
doubling constant (§3 bounds `leafCode` by a single `sum2D`). -/
lemma dlen_leafCode_le_kitD {T N' B' Cz a n d : V} (htblN : NumTableOK T N' B')
    (h : a + 1 ≤ n) (hn : n ≤ 2 * d) (hC : 27 * N' + 525600 * B' ≤ Cz) :
    dlen TAct (leafCode T a n) ≤ kitD Cz (2 * d) :=
  le_trans (dlen_leafCode_le' htblN h hn)
    (le_trans (sum2D_le_layD N' B' (2 * d)) (layD_le_kitD le_rfl hC))

end recursionPrep


/-! ## 16. The per-arm MOTIVE WRAPPERS — `axL`

TRAP 15 (Part 3) measured that filling one arm INSIDE the ten-arm `Derivation.induction1` body does not converge
(>40 min on the cheapest arm, against ~10 s standalone). The restructuring is one TOP-LEVEL theorem per arm, taking
the induction's binders and the cap as explicit hypotheses and concluding the MOTIVE at that node; the recursion
body then becomes ten one-line applications.

**TRAP 16 — the actual cost centre, and the fix.** The blowup is NOT the induction context: it is `isDefEq`
searching for the arm lemma's IMPLICIT arguments (`is`, `il`, `ip`, `inp`, `L`, `n`, …) against the large unfolded
list term. Pinning them by name turns that search into a check. Measured on this wrapper: unpinned, `isDefEq`
timeout at 2 000 000 heartbeats after 73 s; **pinned, green in 5 s** — the same content, a >480× collapse against
the in-body figure. Every remaining wrapper must pin its arm lemma's implicits the same way.

The wrapper also needs `set_option maxHeartbeats 2000000` (the default 200 000 is not enough even pinned) and its
constant hypotheses in the SHAPE the arithmetic lemmas expect — `lin_le_p3` wants `(12 : V) + 9 ≤ Czv`, not
`((21 : ℕ) : V) ≤ Czv`; a cast mismatch there reads as an application type error, not as a numeric one.
-/

section motiveWrappers

set_option maxHeartbeats 2000000 in
/-- **THE `axL` MOTIVE WRAPPER** — top-level, taking the induction's binders and the cap explicitly,
concluding the motive at an `axL` node. The E-room constructions live HERE, not in the recursion body. -/
theorem axL_wrapper {tbl N N' B' Wc W₁ T B E Czv Γ s p : V}
    (htbl : TableOK tbl N) (hP : ProTable tbl) (htblN : NumTableOK T N' B')
    (hWc : Wc = certPieces) (hW₁ : W₁ = frag1Pieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hCz1 : 1 ≤ Czv) (hCk : ∀ a : ℕ, a ≤ 1000000 → ((a : ℕ) : V) ≤ Czv)
    (hC21 : (12 : V) + 9 ≤ Czv)
    (hCD : 27 * N' + 525600 * B' ≤ Czv)
    (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Czv)
    (hs : IsFormulaSet LAct s) (hp : p ∈ s) (hnp : neg LAct p ∈ s)
    (hΓ : IsFormulaSet LAct Γ) (hLay : NodeLay walkPieces Wc T Γ s)
    (hE : Czv * p4 (dlen TAct (axL s p) + 1) ≤ E) :
    len (vAxL walkPieces Wc W₁ T s p) ≤ Czv * p4 (dlen TAct (axL s p)) ∧
    SizeOK (kitQ Czv B E) (kitD Czv (2 * dlen TAct (axL s p))) (vAxL walkPieces Wc W₁ T s p) := by
  have hD : Derivation TAct (axL s p) := Derivation.axL hs hp hnp
  have hd1 : 1 ≤ dlen TAct (axL s p) := one_le_dlen hD
  have hsD : setLen LAct s ≤ dlen TAct (axL s p) := by
    have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_axL] at this
  have hkD : len (memberList s) ≤ dlen TAct (axL s p) := le_trans (len_memberList_le_setLen hs) hsD
  have hpD : formulaLen LAct p ≤ dlen TAct (axL s p) :=
    formulaLen_le_dlen_of_mem hD (by rw [fstIdx_axL]; exact hp)
  have hdl : dlen TAct (axL s p) = setLen LAct s + 1 := dlen_axL hD
  obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (axL s p) := ⟨_, rfl⟩
  rw [← hdd] at hE hd1 hsD hkD hpD hdl ⊢
  have he1 : (1 : V) ≤ d + 1 := le_add_self
  have hE1 : (1 : V) ≤ E := le_trans (le_trans hd1 (le_p4_self hd1))
    (le_trans (le_mul_of_one_le_left zero_le hCz1)
      (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE))
  have hEax : 13 * d + 18 * ‖d‖ + 8 ≤ E := capE4' hE he1 (hCk 39 (by norm_num)) (by
    calc 13 * d + 18 * ‖d‖ + 8 ≤ (13 + 18 + 8) * (d + 1) := lin_cap 13 18 8 d
      _ = ((39 : ℕ) : V) * (d + 1) := by push_cast; ring)
  have hiEax : 0 + 8 * d + 3 ≤ E := capE4' hE he1 (hCk 11 (by norm_num)) (by
    push_cast; exact le_of_add_eq' (c := 3 * d + 8) (by ring))
  obtain ⟨-, -, hho, -, hlenp, -⟩ := proAxL_ok (D := d) htbl hP htblN hWc hs hp hnp hsD hEax hiEax hΓ hLay.layout
  have hnE : 18 * ‖d‖ + 7 ≤ E := capE4' hE he1 (hCk 25 (by norm_num)) (by
    calc 18 * ‖d‖ + 7 ≤ 0 * d + 18 * ‖d‖ + 7 := by rw [zero_mul, zero_add]
      _ ≤ (0 + 18 + 7) * (d + 1) := lin_cap 0 18 7 d
      _ = ((25 : ℕ) : V) * (d + 1) := by push_cast; ring)
  have hLn : setLen LAct s + 1 ≤ d := le_of_eq hdl.symm
  have hgoalE : len (memberList s) + 1 + 1 + 1 ≤ E := capE4' hE he1 (hCk 4 (by norm_num)) (by
    calc len (memberList s) + 1 + 1 + 1 ≤ d + 3 :=
          (add_le_add (add_le_add (add_le_add hkD le_rfl) le_rfl) le_rfl).trans (le_of_eq (by ring))
      _ ≤ ((4 : ℕ) : V) * (d + 1) := by push_cast; exact le_of_add_eq' (c := 3 * d + 1) (by ring))
  have hbn : termLen LAct (bnum d) ≤ E := capE4' hE he1 (hCk 7 (by norm_num)) (by
    refine le_trans (termLen_bnum_le_V d) ?_
    calc 6 * ‖d‖ + 1 ≤ 6 * (d + 1) + 1 * (d + 1) :=
          add_le_add (mul_le_mul_of_nonneg_left (le_trans (length_le d) le_self_add) zero_le)
            (by rw [one_mul]; exact le_add_self)
      _ = ((7 : ℕ) : V) * (d + 1) := by push_cast; ring)
  refine ⟨?_, ?_⟩
  · rw [axL_arm_len]
    refine le_trans (add_le_add (le_trans (le_trans le_self_add hlenp)
      (mul_le_mul_of_nonneg_left hpD zero_le)) (le_refl (9 : V))) ?_
    exact le_trans (lin_le_p3 hd1 hC21) (mul_le_mul_of_nonneg_left (p3_le_p4 hd1) zero_le)
  · unfold vAxL
    rw [← hdd]
    exact (axL_arm_size (Ww := walkPieces) (Wc := Wc) (W₁ := W₁) (T := T) (s := s) (p := p)
      (B := B) (E := E) (Cz := Czv)
      (is := len (memberList s) + 1) (il := 0)
      (ip := memTop walkPieces Wc T s p 0) (inp := memTop walkPieces Wc T s (neg LAct p) 0)
      (L := setLen LAct s) (n := d)
      hW₁ hho hCz1 hE1 hPle hnE hLn hgoalE hbn hcG
      (le_trans (dlen_leafCode_le' htblN (le_of_eq hdl.symm) le_rfl)
        (le_trans (sum2D_le_layD N' B' d) (layD_le_kitD le_rfl hCD)))).mono le_rfl
      (kitD_mono (le_two_mul_self d))


/-! ### 16.1 The `verumIntro` wrapper

The second wrapper, and the confirmation that the template generalises: green in 5 s, the same cost as `axL`.
`vVerum = fragVerum` alone (no prologue), so there is no `HornOnly` block and no `proAxL_ok` destructuring — just
the four E-rooms and `verum_arm_size` with its implicits pinned.

**TRAP 17 — `rw [← hdd]` must come AFTER the `unfold`.** The wrapper abbreviates `d = dlen TAct (…)` and rewrites
it through the goal in bulk at the top; `unfold vVerum` then RE-EXPOSES the raw `dlen` in the fragment's `n`
position, so the pinned `n := d` no longer matches and the application fails on a `SizeOK … (fragVerum … d)` versus
`SizeOK … (fragVerum … (dlen TAct (verumIntro s)))` mismatch. Repeating the rewrite after the unfold fixes it.
-/

set_option maxHeartbeats 2000000 in
/-- **THE `verumIntro` MOTIVE WRAPPER** — `vVerum = fragVerum` alone (no prologue). -/
theorem verum_wrapper {tbl N N' B' Wc W₁ T B E Czv Γ s : V}
    (htbl : TableOK tbl N) (hP : ProTable tbl) (htblN : NumTableOK T N' B')
    (hWc : Wc = certPieces) (hW₁ : W₁ = frag1Pieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hCz1 : 1 ≤ Czv) (hCk : ∀ a : ℕ, a ≤ 1000000 → ((a : ℕ) : V) ≤ Czv)
    (hC9 : (9 : V) ≤ Czv)
    (hCD : 27 * N' + 525600 * B' ≤ Czv)
    (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Czv)
    (hs : IsFormulaSet LAct s) (hv : (^⊤ : V) ∈ s)
    (hΓ : IsFormulaSet LAct Γ) (hLay : NodeLay walkPieces Wc T Γ s)
    (hE : Czv * p4 (dlen TAct (verumIntro s) + 1) ≤ E) :
    len (vVerum walkPieces Wc W₁ T s) ≤ Czv * p4 (dlen TAct (verumIntro s)) ∧
    SizeOK (kitQ Czv B E) (kitD Czv (2 * dlen TAct (verumIntro s))) (vVerum walkPieces Wc W₁ T s) := by
  have hD : Derivation TAct (verumIntro s) := Derivation.verumIntro hs hv
  have hd1 : 1 ≤ dlen TAct (verumIntro s) := one_le_dlen hD
  have hsD : setLen LAct s ≤ dlen TAct (verumIntro s) := by
    have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_verumIntro] at this
  have hkD : len (memberList s) ≤ dlen TAct (verumIntro s) := le_trans (len_memberList_le_setLen hs) hsD
  have hdl : dlen TAct (verumIntro s) = setLen LAct s + 1 := dlen_verumIntro hD
  obtain ⟨d, hdd⟩ : ∃ x, x = dlen TAct (verumIntro s) := ⟨_, rfl⟩
  rw [← hdd] at hE hd1 hsD hkD hdl ⊢
  have he1 : (1 : V) ≤ d + 1 := le_add_self
  have hE1 : (1 : V) ≤ E := le_trans (le_trans hd1 (le_p4_self hd1))
    (le_trans (le_mul_of_one_le_left zero_le hCz1)
      (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE))
  have hnE : 18 * ‖d‖ + 7 ≤ E := capE4' hE he1 (hCk 25 (by norm_num)) (by
    calc 18 * ‖d‖ + 7 ≤ 0 * d + 18 * ‖d‖ + 7 := by rw [zero_mul, zero_add]
      _ ≤ (0 + 18 + 7) * (d + 1) := lin_cap 0 18 7 d
      _ = ((25 : ℕ) : V) * (d + 1) := by push_cast; ring)
  have hLn : setLen LAct s + 1 ≤ d := le_of_eq hdl.symm
  have hgoalE : len (memberList s) + 1 + 1 + 1 ≤ E := capE4' hE he1 (hCk 4 (by norm_num)) (by
    calc len (memberList s) + 1 + 1 + 1 ≤ d + 3 :=
          (add_le_add (add_le_add (add_le_add hkD le_rfl) le_rfl) le_rfl).trans (le_of_eq (by ring))
      _ ≤ ((4 : ℕ) : V) * (d + 1) := by push_cast; exact le_of_add_eq' (c := 3 * d + 1) (by ring))
  have hbn : termLen LAct (bnum d) ≤ E := capE4' hE he1 (hCk 7 (by norm_num)) (by
    refine le_trans (termLen_bnum_le_V d) ?_
    calc 6 * ‖d‖ + 1 ≤ 6 * (d + 1) + 1 * (d + 1) :=
          add_le_add (mul_le_mul_of_nonneg_left (le_trans (length_le d) le_self_add) zero_le)
            (by rw [one_mul]; exact le_add_self)
      _ = ((7 : ℕ) : V) * (d + 1) := by push_cast; ring)
  refine ⟨?_, ?_⟩
  · rw [verum_arm_len]
    exact le_trans hC9 (le_mul_of_one_le_right zero_le (one_le_p4 hd1))
  · unfold vVerum
    rw [← hdd]
    exact (verum_arm_size (W₁ := W₁) (T := T) (B := B) (E := E) (Cz := Czv)
      (is := len (memberList s) + 1) (il := 0) (iv := memTop walkPieces Wc T s (^⊤ : V) 0)
      (L := setLen LAct s) (n := d)
      hW₁ hCz1 hE1 hPle hnE hLn hgoalE hbn hcG
      (le_trans (dlen_leafCode_le' htblN (le_of_eq hdl.symm) le_rfl)
        (le_trans (sum2D_le_layD N' B' d) (layD_le_kitD le_rfl hCD)))).mono le_rfl
      (kitD_mono (le_two_mul_self d))

end motiveWrappers


/-! ## 17. The E-room helper family

Part 5 spent its whole round on hand-built inequality chains: every wrapper's `hEpro`/`hiEpro`/`hnE`/`hbn` is the
same `capE4'`+`lin_cap`+`hCk` composition at a different coefficient triple, and each hand-rolling went wrong in a
different way (a leading `0 +` blocking `ring`, a mis-associated `le_of_add_eq'`, `44 + 25` written as `65`). This
section factors the three shapes once.

* `eroom_lin hE hCk a b c _ : (a : V)·D + (b : V)·‖D‖ + (c : V) ≤ E` — the general LINEAR room, subsuming the
  prologue room `(13, 18, 12)`, the node room `(0, 18, 7)`, the insert room `(14, 0, 5)`, and every other
  `lin_cap` chain in the wrappers;
* `eroom_bnum hE hCk hn : termLen LAct (bnum n) ≤ E` for `n ≤ D` — covers the parent's and the child's `dlen`
  alike (`termLen_bnum_le_V` at coefficient `7`);
* `eroom_off hE hCk hx c _ : x + (c : V) ≤ E` for `x ≤ D` — the goal-fact offset shape.

**Usage.** The helpers are stated with ℕ-casts on the coefficients so the constant side discharges by `norm_num`
against `hCk`; a call site wanting the literal `V`-shape follows with `push_cast at this`, and for a triple with
`a = 0` additionally `rw [zero_mul, zero_add] at this` — the leading zero is exactly what blocked `ring` when these
were hand-rolled. Both idioms are exercised by the smoke tests this section was validated against.
-/

section eroom

/-- **The general LINEAR E-room**: `a·D + b·‖D‖ + c ≤ E` under the cap, for `a + b + c ≤ 1000000`. -/
lemma eroom_lin {D E Czv : V} (hE : Czv * p4 (D + 1) ≤ E) (hCk : ∀ n : ℕ, n ≤ 1000000 → ((n : ℕ) : V) ≤ Czv)
    (a b c : ℕ) (habc : a + b + c ≤ 1000000) :
    ((a : ℕ) : V) * D + ((b : ℕ) : V) * ‖D‖ + ((c : ℕ) : V) ≤ E := by
  refine capE4' hE le_add_self (hCk (a + b + c) habc) ?_
  refine le_trans (lin_cap ((a : ℕ) : V) ((b : ℕ) : V) ((c : ℕ) : V) D) ?_
  exact le_of_eq (by push_cast; ring)

/-- **The `bnum` E-room**: `termLen (bnum n) ≤ E` for any `n ≤ D` (`termLen_bnum_le_V` at coefficient `7`). -/
lemma eroom_bnum {D E Czv n : V} (hE : Czv * p4 (D + 1) ≤ E)
    (hCk : ∀ m : ℕ, m ≤ 1000000 → ((m : ℕ) : V) ≤ Czv) (hn : n ≤ D) :
    termLen LAct (bnum n) ≤ E := by
  refine capE4' hE le_add_self (hCk 7 (by norm_num)) ?_
  refine le_trans (termLen_bnum_le_V n) ?_
  calc 6 * ‖n‖ + 1 ≤ 6 * (D + 1) + 1 * (D + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left
          (le_trans (length_monotone hn) (le_trans (length_le D) le_self_add)) zero_le)
          (by rw [one_mul]; exact le_add_self)
    _ = ((7 : ℕ) : V) * (D + 1) := by push_cast; ring

/-- **The OFFSET E-room**: `x + c ≤ E` for `x ≤ D` and a literal `c`. -/
lemma eroom_off {D E Czv x : V} (hE : Czv * p4 (D + 1) ≤ E)
    (hCk : ∀ m : ℕ, m ≤ 1000000 → ((m : ℕ) : V) ≤ Czv) (hx : x ≤ D)
    (c : ℕ) (hc : 1 + c ≤ 1000000) :
    x + ((c : ℕ) : V) ≤ E := by
  refine capE4' hE le_add_self (hCk (1 + c) hc) ?_
  calc x + ((c : ℕ) : V) ≤ D + ((c : ℕ) : V) := add_le_add hx le_rfl
    _ ≤ ((1 + c : ℕ) : V) * (D + 1) := by
        push_cast
        exact le_of_add_eq' (c := (c : V) * D + 1) (by ring)

end eroom

/-! ## 18. The `wk` motive wrapper

The third wrapper, and the first NON-LEAF one. Written UNABBREVIATED per TRAP 18 (`wk_arm_size` hard-wires
`dlen TAct (wkRule s d')` and `dlen TAct d'` in its hypothesis types), with the arm lemma's implicits pinned per
TRAP 16 and every E-room from §17's helper family.

The two goal-fact offsets and the length half all close the same way: a linear term plus the child's
`Czv·p4 (dlen d')`, absorbed by `Bounds.rec1₄` at `hdeq : dlen (wkRule s d') = dlen d' + (setLen s + 1)`.

**RESIDUAL (Part 6):** `lin_le_p3` concludes at `1 * D + c`, not `D + c`, so each of its uses here is followed by
`rw [one_mul] at …`. -/

section wkWrapper

set_option maxHeartbeats 2000000 in
/-- **THE `wk` MOTIVE WRAPPER.** -/
theorem wk_wrapper {tbl N N' B' Wl Wc W₁ W T B E Czv Γ s d' L' : V}
    (htbl : TableOK tbl N) (hP : ProTable tbl) (htblN : NumTableOK T N' B')
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces) (hW₁ : W₁ = frag1Pieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hCz1 : 1 ≤ Czv) (hCk : ∀ n : ℕ, n ≤ 1000000 → ((n : ℕ) : V) ≤ Czv)
    (hCQ : 19 * B' + 25 ≤ Czv) (hCD : 27 * N' + 525600 * B' ≤ Czv)
    (hCbin : 2 * (27 * N' + 525600 * B') ≤ Czv)
    (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Czv)
    (hs : IsFormulaSet LAct s) (hsub : fstIdx d' ⊆ s) (hd' : Derivation TAct d')
    (hΓ : IsFormulaSet LAct Γ) (hLay : NodeLay walkPieces Wc T Γ s)
    (hchildSz : SizeOK (kitQ Czv B E) (kitD Czv (2 * dlen TAct (wkRule s d'))) L')
    (hchildLen : len L' ≤ Czv * p4 (dlen TAct d'))
    (hE : Czv * p4 (dlen TAct (wkRule s d') + 1) ≤ E) :
    len (vWk walkPieces Wl Wc W₁ W T s d' L') ≤ Czv * p4 (dlen TAct (wkRule s d')) ∧
    SizeOK (kitQ Czv B E) (kitD Czv (2 * dlen TAct (wkRule s d'))) (vWk walkPieces Wl Wc W₁ W T s d' L') := by
  have hD : Derivation TAct (wkRule s d') := Derivation.wkRule hs hsub ⟨rfl, hd'⟩
  have hd1 : 1 ≤ dlen TAct (wkRule s d') := one_le_dlen hD
  have hsD : setLen LAct s ≤ dlen TAct (wkRule s d') := by
    have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_wkRule] at this
  have hcD : setLen LAct (fstIdx d') ≤ dlen TAct (wkRule s d') := setLen_child_le_dlen_wkRule hD
  have hdl : dlen TAct (wkRule s d') = setLen LAct s + dlen TAct d' + 1 := dlen_wkRule hD
  have hcs : IsFormulaSet LAct (fstIdx d') := DerivationOf.isFormulaSet ⟨rfl, hd'⟩
  have hkcD : len (memberList (fstIdx d')) ≤ dlen TAct (wkRule s d') :=
    le_trans (len_memberList_le_setLen hcs) hcD
  have hksD : len (memberList s) ≤ dlen TAct (wkRule s d') :=
    le_trans (len_memberList_le_setLen hs) hsD
  have he1 : (1 : V) ≤ dlen TAct (wkRule s d') + 1 := le_add_self
  have hyd : dlen TAct d' ≤ dlen TAct (wkRule s d') := by
    rw [hdl]; exact le_of_add_eq' (c := setLen LAct s + 1) (by ring)
  have hdeq : dlen TAct (wkRule s d') = dlen TAct d' + (setLen LAct s + 1) := by rw [hdl]; ring
  have hE1 : (1 : V) ≤ E := le_trans (le_trans hd1 (le_p4_self hd1))
    (le_trans (le_mul_of_one_le_left zero_le hCz1)
      (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE))
  have hDE : dlen TAct (wkRule s d') ≤ E := le_trans (le_p4_self hd1)
    (le_trans (le_mul_of_one_le_left zero_le hCz1)
      (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE))
  have hEpro : 13 * dlen TAct (wkRule s d') + 18 * ‖dlen TAct (wkRule s d')‖ + 12 ≤ E := by
    have := eroom_lin hE hCk 13 18 12 (by norm_num)
    push_cast at this
    exact this
  have hiEpro : 0 + 14 * dlen TAct (wkRule s d') + 5 ≤ E := by
    rw [zero_add]
    have := eroom_lin hE hCk 14 0 5 (by norm_num)
    push_cast at this
    rw [zero_mul, add_zero] at this
    exact this
  have hnE : 18 * ‖dlen TAct (wkRule s d')‖ + 7 ≤ E := by
    have := eroom_lin hE hCk 0 18 7 (by norm_num)
    push_cast at this
    rw [zero_mul, zero_add] at this
    exact this
  have hbnc : termLen LAct (bnum (dlen TAct d')) ≤ E := eroom_bnum hE hCk hyd
  have hbn' : termLen LAct (bnum (dlen TAct (wkRule s d'))) ≤ E := eroom_bnum hE hCk le_rfl
  have hLn : setLen LAct s + dlen TAct d' + 1 ≤ dlen TAct (wkRule s d') := le_of_eq hdl.symm
  have hnd : dlen TAct (wkRule s d') ≤ 2 * dlen TAct (wkRule s d') := le_two_mul_self _
  have hshL : shiftsV L' ≤ Czv * p4 (dlen TAct d') := le_trans (shiftsV_le_len L') hchildLen
  have hlenPro : len (wkPro walkPieces Wl Wc W T s (fstIdx d')) ≤ 44 * dlen TAct (wkRule s d') + 11 :=
    len_wkPro_le htbl hP hWl hWc walkPieces W T s hcs hcD
  have hshPro : shiftsV (wkPro walkPieces Wl Wc W T s (fstIdx d')) ≤ 44 * dlen TAct (wkRule s d') + 11 :=
    le_trans (shiftsV_le_len _) hlenPro
  have hgE : len (memberList (fstIdx d')) + 1 + shiftsV L' + 1 ≤ E := by
    have hlin : dlen TAct (wkRule s d') + 2 ≤ Czv * p3 (dlen TAct (wkRule s d')) := by
      have h3 := hCk 3 (by norm_num)
      push_cast at h3
      have := lin_le_p3 (a := 1) (b := 2) hd1 (by
        exact le_trans (le_of_eq (by norm_num : (1 : V) + 2 = 3)) h3)
      rw [one_mul] at this
      exact this
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    calc len (memberList (fstIdx d')) + 1 + shiftsV L' + 1
        ≤ dlen TAct (wkRule s d') + 1 + Czv * p4 (dlen TAct d') + 1 :=
          add_le_add (add_le_add (add_le_add hkcD le_rfl) hshL) le_rfl
      _ = (dlen TAct (wkRule s d') + 2) + Czv * p4 (dlen TAct d') := by ring
      _ ≤ Czv * p4 (dlen TAct (wkRule s d')) := rec1₄ le_add_self hdeq hlin
  have hgE2 : shiftsV (wkPro walkPieces Wl Wc W T s (fstIdx d')) + shiftsV L' + 2 +
      (len (memberList s) + 1) + 1 + 1 ≤ E := by
    have hlin : 45 * dlen TAct (wkRule s d') + 16 ≤ Czv * p3 (dlen TAct (wkRule s d')) := by
      have h61 := hCk 61 (by norm_num)
      push_cast at h61
      exact lin_le_p3 hd1 (le_trans (le_of_eq (by norm_num : (45 : V) + 16 = 61)) h61)
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    calc shiftsV (wkPro walkPieces Wl Wc W T s (fstIdx d')) + shiftsV L' + 2 +
          (len (memberList s) + 1) + 1 + 1
        ≤ (44 * dlen TAct (wkRule s d') + 11) + Czv * p4 (dlen TAct d') + 2 +
          (dlen TAct (wkRule s d') + 1) + 1 + 1 :=
          add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hshPro hshL) le_rfl)
            (add_le_add hksD le_rfl)) le_rfl) le_rfl
      _ = (45 * dlen TAct (wkRule s d') + 16) + Czv * p4 (dlen TAct d') := by ring
      _ ≤ Czv * p4 (dlen TAct (wkRule s d')) := rec1₄ le_add_self hdeq hlin
  refine ⟨?_, ?_⟩
  · rw [len_vWk_eq]
    have hX : 44 * dlen TAct (wkRule s d') + 25 ≤ Czv * p3 (dlen TAct (wkRule s d')) := by
      have h69 := hCk 69 (by norm_num)
      push_cast at h69
      exact lin_le_p3 hd1 (le_trans (le_of_eq (by norm_num : (44 : V) + 25 = 69)) h69)
    calc len (wkPro walkPieces Wl Wc W T s (fstIdx d')) + (len L' + (5 + 9))
        ≤ (44 * dlen TAct (wkRule s d') + 11) + (Czv * p4 (dlen TAct d') + 14) :=
          add_le_add hlenPro (add_le_add hchildLen (by norm_num))
      _ = (44 * dlen TAct (wkRule s d') + 25) + Czv * p4 (dlen TAct d') := by ring
      _ ≤ Czv * p4 (dlen TAct (wkRule s d')) := rec1₄ le_add_self hdeq hX
  · exact wk_arm_size (Wl := Wl) (Wc := Wc) (W₁ := W₁) (W := W) (T := T) (s := s) (d' := d') (L' := L')
      (B := B) (E := E) (Cz := Czv) (N' := N') (B' := B')
      (D := dlen TAct (wkRule s d')) (d := dlen TAct (wkRule s d')) (Γ := Γ)
      hWp hW₁ htbl hP htblN hWl hWc hPle hs hsub hsD hcD hEpro hiEpro hΓ hLay.layout
      hDE hnd hCQ hCD hCz1 hchildSz hE1 hcG hgE hbnc hbn' hnE hLn hnd hgE2 hCbin

end wkWrapper

/-! ## 19. The `shift` motive wrapper

The `wk` wrapper's twin. `shift_arm_size` differs from `wk_arm_size` in three places only: it wants the child's
`IsFormulaSet` and the shift equation (`hc`, `hsc : s = setShift LAct (fstIdx d')`) in place of `wk`'s `hsub`, and
its insert room is `0 + 16·D + 8` rather than `0 + 14·D + 5`. `dlen_shiftRule` has the same shape as `dlen_wkRule`
(`setLen s + dlen d + 1`), so `hdeq`, `hyd` and `hLn` transcribe unchanged.

The constants move with `len_shiftPro_le ≤ 62·D + 23` (against `wk`'s `44·D + 11`): the length half needs
`62 + 23 + 14 = 99` and `hgE2` needs `63·D + 28`, i.e. `91`. -/

section shiftWrapper

set_option maxHeartbeats 2000000 in
/-- **THE `shift` MOTIVE WRAPPER.** -/
theorem shift_wrapper {tbl N N' B' Wl Wc W₂ W T B E Czv Γ s d' L' : V}
    (htbl : TableOK tbl N) (hP : ProTable tbl) (htblN : NumTableOK T N' B')
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces) (hW₂ : W₂ = frag2Pieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hCz1 : 1 ≤ Czv) (hCk : ∀ n : ℕ, n ≤ 1000000 → ((n : ℕ) : V) ≤ Czv)
    (hCQ : 19 * B' + 25 ≤ Czv) (hCD : 27 * N' + 525600 * B' ≤ Czv)
    (hCbin : 2 * (27 * N' + 525600 * B') ≤ Czv)
    (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Czv)
    (hs : IsFormulaSet LAct s) (hsc : s = setShift LAct (fstIdx d')) (hd' : Derivation TAct d')
    (hΓ : IsFormulaSet LAct Γ) (hLay : NodeLay walkPieces Wc T Γ s)
    (hchildSz : SizeOK (kitQ Czv B E) (kitD Czv (2 * dlen TAct (shiftRule s d'))) L')
    (hchildLen : len L' ≤ Czv * p4 (dlen TAct d'))
    (hE : Czv * p4 (dlen TAct (shiftRule s d') + 1) ≤ E) :
    len (vShift walkPieces Wl Wc W₂ W T s d' L') ≤ Czv * p4 (dlen TAct (shiftRule s d')) ∧
    SizeOK (kitQ Czv B E) (kitD Czv (2 * dlen TAct (shiftRule s d')))
      (vShift walkPieces Wl Wc W₂ W T s d' L') := by
  have hD : Derivation TAct (shiftRule s d') := by
    have := Derivation.shiftRule (T := TAct) ⟨rfl, hd'⟩; rwa [← hsc] at this
  have hd1 : 1 ≤ dlen TAct (shiftRule s d') := one_le_dlen hD
  have hsD : setLen LAct s ≤ dlen TAct (shiftRule s d') := by
    have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_shiftRule] at this
  have hcD : setLen LAct (fstIdx d') ≤ dlen TAct (shiftRule s d') := setLen_child_le_dlen_shiftRule hD
  have hdl : dlen TAct (shiftRule s d') = setLen LAct s + dlen TAct d' + 1 := dlen_shiftRule hD
  have hcs : IsFormulaSet LAct (fstIdx d') := DerivationOf.isFormulaSet ⟨rfl, hd'⟩
  have hkcD : len (memberList (fstIdx d')) ≤ dlen TAct (shiftRule s d') :=
    le_trans (len_memberList_le_setLen hcs) hcD
  have hksD : len (memberList s) ≤ dlen TAct (shiftRule s d') :=
    le_trans (len_memberList_le_setLen hs) hsD
  have he1 : (1 : V) ≤ dlen TAct (shiftRule s d') + 1 := le_add_self
  have hyd : dlen TAct d' ≤ dlen TAct (shiftRule s d') := by
    rw [hdl]; exact le_of_add_eq' (c := setLen LAct s + 1) (by ring)
  have hdeq : dlen TAct (shiftRule s d') = dlen TAct d' + (setLen LAct s + 1) := by rw [hdl]; ring
  have hE1 : (1 : V) ≤ E := le_trans (le_trans hd1 (le_p4_self hd1))
    (le_trans (le_mul_of_one_le_left zero_le hCz1)
      (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE))
  have hDE : dlen TAct (shiftRule s d') ≤ E := le_trans (le_p4_self hd1)
    (le_trans (le_mul_of_one_le_left zero_le hCz1)
      (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE))
  have hEpro : 13 * dlen TAct (shiftRule s d') + 18 * ‖dlen TAct (shiftRule s d')‖ + 12 ≤ E := by
    have := eroom_lin hE hCk 13 18 12 (by norm_num)
    push_cast at this
    exact this
  have hiEpro : 0 + 16 * dlen TAct (shiftRule s d') + 8 ≤ E := by
    rw [zero_add]
    have := eroom_lin hE hCk 16 0 8 (by norm_num)
    push_cast at this
    rw [zero_mul, add_zero] at this
    exact this
  have hnE : 18 * ‖dlen TAct (shiftRule s d')‖ + 7 ≤ E := by
    have := eroom_lin hE hCk 0 18 7 (by norm_num)
    push_cast at this
    rw [zero_mul, zero_add] at this
    exact this
  have hbnc : termLen LAct (bnum (dlen TAct d')) ≤ E := eroom_bnum hE hCk hyd
  have hbn' : termLen LAct (bnum (dlen TAct (shiftRule s d'))) ≤ E := eroom_bnum hE hCk le_rfl
  have hLn : setLen LAct s + dlen TAct d' + 1 ≤ dlen TAct (shiftRule s d') := le_of_eq hdl.symm
  have hnd : dlen TAct (shiftRule s d') ≤ 2 * dlen TAct (shiftRule s d') := le_two_mul_self _
  have hshL : shiftsV L' ≤ Czv * p4 (dlen TAct d') := le_trans (shiftsV_le_len L') hchildLen
  have hlenPro : len (shiftPro walkPieces Wl Wc W T s (fstIdx d')) ≤
      62 * dlen TAct (shiftRule s d') + 23 :=
    len_shiftPro_le hWc walkPieces Wl W T hs hcs hsD hcD
  have hshPro : shiftsV (shiftPro walkPieces Wl Wc W T s (fstIdx d')) ≤
      62 * dlen TAct (shiftRule s d') + 23 :=
    le_trans (shiftsV_le_len _) hlenPro
  have hgE : len (memberList (fstIdx d')) + 1 + shiftsV L' + 1 ≤ E := by
    have hlin : dlen TAct (shiftRule s d') + 2 ≤ Czv * p3 (dlen TAct (shiftRule s d')) := by
      have h3 := hCk 3 (by norm_num)
      push_cast at h3
      have := lin_le_p3 (a := 1) (b := 2) hd1 (by
        exact le_trans (le_of_eq (by norm_num : (1 : V) + 2 = 3)) h3)
      rw [one_mul] at this
      exact this
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    calc len (memberList (fstIdx d')) + 1 + shiftsV L' + 1
        ≤ dlen TAct (shiftRule s d') + 1 + Czv * p4 (dlen TAct d') + 1 :=
          add_le_add (add_le_add (add_le_add hkcD le_rfl) hshL) le_rfl
      _ = (dlen TAct (shiftRule s d') + 2) + Czv * p4 (dlen TAct d') := by ring
      _ ≤ Czv * p4 (dlen TAct (shiftRule s d')) := rec1₄ le_add_self hdeq hlin
  have hgE2 : shiftsV (shiftPro walkPieces Wl Wc W T s (fstIdx d')) + shiftsV L' + 2 +
      (len (memberList s) + 1) + 1 + 1 ≤ E := by
    have hlin : 63 * dlen TAct (shiftRule s d') + 28 ≤ Czv * p3 (dlen TAct (shiftRule s d')) := by
      have h91 := hCk 91 (by norm_num)
      push_cast at h91
      exact lin_le_p3 hd1 (le_trans (le_of_eq (by norm_num : (63 : V) + 28 = 91)) h91)
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    calc shiftsV (shiftPro walkPieces Wl Wc W T s (fstIdx d')) + shiftsV L' + 2 +
          (len (memberList s) + 1) + 1 + 1
        ≤ (62 * dlen TAct (shiftRule s d') + 23) + Czv * p4 (dlen TAct d') + 2 +
          (dlen TAct (shiftRule s d') + 1) + 1 + 1 :=
          add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hshPro hshL) le_rfl)
            (add_le_add hksD le_rfl)) le_rfl) le_rfl
      _ = (63 * dlen TAct (shiftRule s d') + 28) + Czv * p4 (dlen TAct d') := by ring
      _ ≤ Czv * p4 (dlen TAct (shiftRule s d')) := rec1₄ le_add_self hdeq hlin
  refine ⟨?_, ?_⟩
  · rw [len_vShift_eq]
    have hX : 62 * dlen TAct (shiftRule s d') + 37 ≤ Czv * p3 (dlen TAct (shiftRule s d')) := by
      have h99 := hCk 99 (by norm_num)
      push_cast at h99
      exact lin_le_p3 hd1 (le_trans (le_of_eq (by norm_num : (62 : V) + 37 = 99)) h99)
    calc len (shiftPro walkPieces Wl Wc W T s (fstIdx d')) + (len L' + (5 + 9))
        ≤ (62 * dlen TAct (shiftRule s d') + 23) + (Czv * p4 (dlen TAct d') + 14) :=
          add_le_add hlenPro (add_le_add hchildLen (by norm_num))
      _ = (62 * dlen TAct (shiftRule s d') + 37) + Czv * p4 (dlen TAct d') := by ring
      _ ≤ Czv * p4 (dlen TAct (shiftRule s d')) := rec1₄ le_add_self hdeq hX
  · exact shift_arm_size (Wl := Wl) (Wc := Wc) (W₂ := W₂) (W := W) (T := T) (s := s) (d' := d') (L' := L')
      (B := B) (E := E) (Cz := Czv) (N' := N') (B' := B')
      (D := dlen TAct (shiftRule s d')) (d := dlen TAct (shiftRule s d')) (Γ := Γ)
      hWp hW₂ htbl hP htblN hWl hWc hPle hs hcs hsc hsD hcD hEpro hiEpro hΓ hLay.layout
      hDE hnd hCQ hCD hCz1 hchildSz hE1 hcG hgE hbnc hbn' hnE hLn hnd hgE2 hCbin

end shiftWrapper

/-! ## 20. The general E-room, and why the offset shapes need no bespoke helper

The `or`/`and`/`cut` arms want rooms over `memTop`, `descCountF` and `proSig` offsets — e.g. `or`'s
`hipE : memTop … (p ^⋎ q) 0 + descCountF … 0 q + 1 + 14·D + 6 ≤ E`. Those look like a new shape, but each
summand's own bound is already LINEAR in `D` (`Prologue.memTop_le ≤ i + 6·D + 1`,
`Verify2.descCountF_le_of_len ≤ 2·D`, `Prologue.proSig_le ≤ 6·D + 1`), so every such room COLLAPSES to
`a·D + c` once the summands are bounded — `hipE` to `22·D + 8`, `hiqE` to `14·D + 6`.

So the widening that was wanted is not a `memTop`-shaped helper but the general one: anything bounded by
`a·D + c` is bounded by `E`. `eroom_of_le` is that lemma, and it subsumes `eroom_lin`'s role at `b = 0` as
well as every offset room of the remaining arms.

**Usage.** Bound each summand by its own `k·D + c`, sum the coefficients, then
`refine eroom_of_le hE hCk a c (by norm_num) ?_; push_cast` and close with one `calc … := by ring`.
`Prologue.proSig_le` itself needs an E-room at `(13, 18, 8)`, supplied by `eroom_lin`. -/

section eroomGeneral

/-- **The GENERAL E-room**: anything bounded by `a·D + c` is bounded by `E`. -/
lemma eroom_of_le {D E Czv X : V} (hE : Czv * p4 (D + 1) ≤ E)
    (hCk : ∀ n : ℕ, n ≤ 1000000 → ((n : ℕ) : V) ≤ Czv)
    (a c : ℕ) (hac : a + c ≤ 1000000)
    (hX : X ≤ ((a : ℕ) : V) * D + ((c : ℕ) : V)) : X ≤ E := by
  refine le_trans hX ?_
  have := eroom_lin hE hCk a 0 c (by omega)
  rw [Nat.cast_zero, zero_mul, add_zero] at this
  exact this

end eroomGeneral

/-! ## 21. The `or` motive wrapper

The first arm with a `postIns` recovery block (six steps, against `goalElim`'s five) and with DOSSIER hypotheses.
Still one child and one context, so it transcribes like `wk`/`shift` with three differences:

* the tail is `6 + 9 = 15`, and `Prologue.len_proOr_le ≤ 110·setLen (insert p (insert q s)) + 25` with the `setLen`
  bounded by `setLen_child_le_dlen_orIntro`, so the length half's constant is `110 + 25 + 15 = 150`;
* the two OFFSET rooms go through §20's `eroom_of_le` after their summands are bounded —
  `hipE` collapses to `22·D + 8` (`memTop_le ≤ 0 + 6·D + 1`, `descCountF_le_of_len ≤ 2·D`) and `hiqE` to `14·D + 6`;
* `hgE2` carries two `proSig` terms, each `≤ 6·D + 1` by `Prologue.proSig_le`, which itself needs an E-room at
  `(13, 18, 8)`.

`dlen_orIntro` has the same `setLen s + dlen d' + 1` shape as `wk`/`shift`, so `hdeq`, `hyd` and `hLn` are unchanged. -/

section orWrapper

set_option maxHeartbeats 2000000 in
/-- **THE `or` MOTIVE WRAPPER.** -/
theorem or_wrapper {tbl N N' B' Wl Wc W₁ W T B E Czv Γ s p q d' L' : V}
    (htbl : TableOK tbl N) (hP : ProTable tbl) (htblN : NumTableOK T N' B')
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces) (hW₁ : W₁ = frag1Pieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hCz1 : 1 ≤ Czv) (hCk : ∀ n : ℕ, n ≤ 1000000 → ((n : ℕ) : V) ≤ Czv)
    (hCQ : 19 * B' + 25 ≤ Czv) (hCD : 27 * N' + 525600 * B' ≤ Czv)
    (hCbin : 2 * (27 * N' + 525600 * B') ≤ Czv)
    (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Czv)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p) (hq : IsSemiformula LAct 0 q)
    (hpq : (p ^⋎ q) ∈ s) (hd' : DerivationOf TAct d' (insert p (insert q s)))
    (hΓ : IsFormulaSet LAct Γ) (hLay : NodeLay walkPieces Wc T Γ s)
    (hchildSz : SizeOK (kitQ Czv B E) (kitD Czv (2 * dlen TAct (orIntro s p q d'))) L')
    (hchildLen : len L' ≤ Czv * p4 (dlen TAct d'))
    (hE : Czv * p4 (dlen TAct (orIntro s p q d') + 1) ≤ E) :
    len (vOr walkPieces Wl Wc W₁ W T s p q d' L') ≤ Czv * p4 (dlen TAct (orIntro s p q d')) ∧
    SizeOK (kitQ Czv B E) (kitD Czv (2 * dlen TAct (orIntro s p q d')))
      (vOr walkPieces Wl Wc W₁ W T s p q d' L') := by
  have hD : Derivation TAct (orIntro s p q d') := Derivation.orIntro hpq hd'
  have hd1 : 1 ≤ dlen TAct (orIntro s p q d') := one_le_dlen hD
  have hsD : setLen LAct s ≤ dlen TAct (orIntro s p q d') := by
    have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_orIntro] at this
  have hcD : setLen LAct (insert p (insert q s)) ≤ dlen TAct (orIntro s p q d') :=
    setLen_child_le_dlen_orIntro hD
  have hdl : dlen TAct (orIntro s p q d') = setLen LAct s + dlen TAct d' + 1 := dlen_orIntro hD
  have hcs : IsFormulaSet LAct (insert p (insert q s)) :=
    IsFormulaSet.insert_iff.mpr ⟨hp, IsFormulaSet.insert_iff.mpr ⟨hq, hs⟩⟩
  have hkcD : len (memberList (insert p (insert q s))) ≤ dlen TAct (orIntro s p q d') :=
    le_trans (len_memberList_le_setLen hcs) hcD
  have hksD : len (memberList s) ≤ dlen TAct (orIntro s p q d') :=
    le_trans (len_memberList_le_setLen hs) hsD
  have hk1 : 1 ≤ len (memberList s) := one_le_len_memberList_of_mem hpq
  have he1 : (1 : V) ≤ dlen TAct (orIntro s p q d') + 1 := le_add_self
  have hyd : dlen TAct d' ≤ dlen TAct (orIntro s p q d') := by
    rw [hdl]; exact le_of_add_eq' (c := setLen LAct s + 1) (by ring)
  have hdeq : dlen TAct (orIntro s p q d') = dlen TAct d' + (setLen LAct s + 1) := by rw [hdl]; ring
  have hqmem : q ∈ insert p (insert q s) := by simp
  have hqD : formulaLen LAct q ≤ dlen TAct (orIntro s p q d') :=
    le_trans (formulaLen_le_setLen_of_mem (L := LAct) hqmem) hcD
  have hE1 : (1 : V) ≤ E := le_trans (le_trans hd1 (le_p4_self hd1))
    (le_trans (le_mul_of_one_le_left zero_le hCz1)
      (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE))
  have hDE : dlen TAct (orIntro s p q d') ≤ E := le_trans (le_p4_self hd1)
    (le_trans (le_mul_of_one_le_left zero_le hCz1)
      (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE))
  have hEpro : 13 * dlen TAct (orIntro s p q d') + 18 * ‖dlen TAct (orIntro s p q d')‖ + 12 ≤ E := by
    have := eroom_lin hE hCk 13 18 12 (by norm_num)
    push_cast at this
    exact this
  have hE8 : 13 * dlen TAct (orIntro s p q d') + 18 * ‖dlen TAct (orIntro s p q d')‖ + 8 ≤ E := by
    have := eroom_lin hE hCk 13 18 8 (by norm_num)
    push_cast at this
    exact this
  have hiEpro : 0 + 14 * dlen TAct (orIntro s p q d') + 5 ≤ E := by
    rw [zero_add]
    have := eroom_lin hE hCk 14 0 5 (by norm_num)
    push_cast at this
    rw [zero_mul, add_zero] at this
    exact this
  have hnE : 18 * ‖dlen TAct (orIntro s p q d')‖ + 7 ≤ E := by
    have := eroom_lin hE hCk 0 18 7 (by norm_num)
    push_cast at this
    rw [zero_mul, zero_add] at this
    exact this
  have hmT : memTop walkPieces Wc T s (p ^⋎ q) 0 ≤ 0 + 6 * dlen TAct (orIntro s p q d') + 1 :=
    memTop_le htbl hP.walkTable hWc T hs hpq hsD
  have hdC : descCountF walkPieces 0 q ≤ 2 * dlen TAct (orIntro s p q d') :=
    descCountF_le_of_len htbl hP.walkTable hq hqD
  have hipE : memTop walkPieces Wc T s (p ^⋎ q) 0 + descCountF walkPieces 0 q + 1 +
      14 * dlen TAct (orIntro s p q d') + 6 ≤ E := by
    refine eroom_of_le hE hCk 22 8 (by norm_num) ?_
    push_cast
    calc memTop walkPieces Wc T s (p ^⋎ q) 0 + descCountF walkPieces 0 q + 1 +
          14 * dlen TAct (orIntro s p q d') + 6
        ≤ (0 + 6 * dlen TAct (orIntro s p q d') + 1) + 2 * dlen TAct (orIntro s p q d') + 1 +
          14 * dlen TAct (orIntro s p q d') + 6 :=
          add_le_add (add_le_add (add_le_add (add_le_add hmT hdC) le_rfl) le_rfl) le_rfl
      _ = 22 * dlen TAct (orIntro s p q d') + 8 := by ring
  have hiqE : memTop walkPieces Wc T s (p ^⋎ q) 0 + 1 + 8 * dlen TAct (orIntro s p q d') + 4 ≤ E := by
    refine eroom_of_le hE hCk 14 6 (by norm_num) ?_
    push_cast
    calc memTop walkPieces Wc T s (p ^⋎ q) 0 + 1 + 8 * dlen TAct (orIntro s p q d') + 4
        ≤ (0 + 6 * dlen TAct (orIntro s p q d') + 1) + 1 + 8 * dlen TAct (orIntro s p q d') + 4 :=
          add_le_add (add_le_add (add_le_add hmT le_rfl) le_rfl) le_rfl
      _ = 14 * dlen TAct (orIntro s p q d') + 6 := by ring
  have hbnc : termLen LAct (bnum (dlen TAct d')) ≤ E := eroom_bnum hE hCk hyd
  have hbn' : termLen LAct (bnum (dlen TAct (orIntro s p q d'))) ≤ E := eroom_bnum hE hCk le_rfl
  have hLn : setLen LAct s + dlen TAct d' + 1 ≤ dlen TAct (orIntro s p q d') := le_of_eq hdl.symm
  have hnd : dlen TAct (orIntro s p q d') ≤ 2 * dlen TAct (orIntro s p q d') := le_two_mul_self _
  have hshL : shiftsV L' ≤ Czv * p4 (dlen TAct d') := le_trans (shiftsV_le_len L') hchildLen
  have hlenPro : len (proOr walkPieces Wl Wc W T s p q 0
      (memTop walkPieces Wc T s (p ^⋎ q) 0 + descCountF walkPieces 0 q + 1)
      (memTop walkPieces Wc T s (p ^⋎ q) 0 + 1)) ≤
      110 * dlen TAct (orIntro s p q d') + 25 := by
    refine le_trans (len_proOr_le htbl hP hWl hWc walkPieces W T 0 _ _ hs hp hq) ?_
    exact add_le_add (mul_le_mul_of_nonneg_left hcD zero_le) le_rfl
  have hqsf : IsFormulaSet LAct (insert q s) := IsFormulaSet.insert_iff.mpr ⟨hq, hs⟩
  have hqsD : setLen LAct (insert q s) ≤ dlen TAct (orIntro s p q d') :=
    le_trans (setLen_le_insert p (insert q s)) hcD
  have hk1q : 1 ≤ len (memberList (insert q s)) :=
    one_le_len_memberList_of_mem (by simp : q ∈ insert q s)
  have hk1c : 1 ≤ len (memberList (insert p (insert q s))) :=
    one_le_len_memberList_of_mem (by simp : p ∈ insert p (insert q s))
  have hsig1 : proSig walkPieces Wl Wc W T (insert q s) ≤ 6 * dlen TAct (orIntro s p q d') + 1 :=
    proSig_le htbl hP hWc htblN hWl hWp hqsf hk1q hqsD hE8 hΓ
  have hsig2 : proSig walkPieces Wl Wc W T (insert p (insert q s)) ≤
      6 * dlen TAct (orIntro s p q d') + 1 :=
    proSig_le htbl hP hWc htblN hWl hWp hcs hk1c hcD hE8 hΓ
  have hgE : len (memberList (insert p (insert q s))) + 1 + shiftsV L' + 1 ≤ E := by
    have hlin : dlen TAct (orIntro s p q d') + 2 ≤ Czv * p3 (dlen TAct (orIntro s p q d')) := by
      have h3 := hCk 3 (by norm_num)
      push_cast at h3
      have := lin_le_p3 (a := 1) (b := 2) hd1 (by
        exact le_trans (le_of_eq (by norm_num : (1 : V) + 2 = 3)) h3)
      rw [one_mul] at this
      exact this
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    calc len (memberList (insert p (insert q s))) + 1 + shiftsV L' + 1
        ≤ dlen TAct (orIntro s p q d') + 1 + Czv * p4 (dlen TAct d') + 1 :=
          add_le_add (add_le_add (add_le_add hkcD le_rfl) hshL) le_rfl
      _ = (dlen TAct (orIntro s p q d') + 2) + Czv * p4 (dlen TAct d') := by ring
      _ ≤ Czv * p4 (dlen TAct (orIntro s p q d')) := rec1₄ le_add_self hdeq hlin
  have hgE2 : 1 + proSig walkPieces Wl Wc W T (insert q s) +
      (1 + proSig walkPieces Wl Wc W T (insert p (insert q s))) + shiftsV L' + 2 +
      (len (memberList s) + 1) + 1 + 1 ≤ E := by
    have hlin : 13 * dlen TAct (orIntro s p q d') + 9 ≤ Czv * p3 (dlen TAct (orIntro s p q d')) := by
      have h22 := hCk 22 (by norm_num)
      push_cast at h22
      exact lin_le_p3 hd1 (le_trans (le_of_eq (by norm_num : (13 : V) + 9 = 22)) h22)
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    calc 1 + proSig walkPieces Wl Wc W T (insert q s) +
          (1 + proSig walkPieces Wl Wc W T (insert p (insert q s))) + shiftsV L' + 2 +
          (len (memberList s) + 1) + 1 + 1
        ≤ 1 + (6 * dlen TAct (orIntro s p q d') + 1) +
          (1 + (6 * dlen TAct (orIntro s p q d') + 1)) + Czv * p4 (dlen TAct d') + 2 +
          (dlen TAct (orIntro s p q d') + 1) + 1 + 1 :=
          add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
            (add_le_add le_rfl hsig1) (add_le_add le_rfl hsig2)) hshL) le_rfl)
            (add_le_add hksD le_rfl)) le_rfl) le_rfl
      _ = (13 * dlen TAct (orIntro s p q d') + 9) + Czv * p4 (dlen TAct d') := by ring
      _ ≤ Czv * p4 (dlen TAct (orIntro s p q d')) := rec1₄ le_add_self hdeq hlin
  refine ⟨?_, ?_⟩
  · rw [len_vOr_eq]
    have hX : 110 * dlen TAct (orIntro s p q d') + 40 ≤ Czv * p3 (dlen TAct (orIntro s p q d')) := by
      have h150 := hCk 150 (by norm_num)
      push_cast at h150
      exact lin_le_p3 hd1 (le_trans (le_of_eq (by norm_num : (110 : V) + 40 = 150)) h150)
    calc len (proOr walkPieces Wl Wc W T s p q 0
          (memTop walkPieces Wc T s (p ^⋎ q) 0 + descCountF walkPieces 0 q + 1)
          (memTop walkPieces Wc T s (p ^⋎ q) 0 + 1)) + (len L' + (6 + 9))
        ≤ (110 * dlen TAct (orIntro s p q d') + 25) + (Czv * p4 (dlen TAct d') + 15) :=
          add_le_add hlenPro (add_le_add hchildLen (by norm_num))
      _ = (110 * dlen TAct (orIntro s p q d') + 40) + Czv * p4 (dlen TAct d') := by ring
      _ ≤ Czv * p4 (dlen TAct (orIntro s p q d')) := rec1₄ le_add_self hdeq hX
  · obtain ⟨-, hDp, hDq, -⟩ := layout_or htbl hP hp hq hpq hLay.layout
    exact or_arm_size (Wl := Wl) (Wc := Wc) (W₁ := W₁) (W := W) (T := T) (s := s) (p := p) (q := q)
      (d' := d') (L' := L') (B := B) (E := E) (Cz := Czv) (N' := N') (B' := B')
      (D := dlen TAct (orIntro s p q d')) (d := dlen TAct (orIntro s p q d')) (Γ := Γ)
      hWp hW₁ htbl hP htblN hWl hWc hPle hs hp hq hk1 hcD hEpro hiEpro hipE hiqE hΓ hLay.layout
      hDp hDq hDE hnd hCQ hCD hCz1 hchildSz hE1 hcG hgE hbnc hbn' hnE hLn hnd hgE2 hCbin

end orWrapper

/-! ## 22. The `and` motive wrapper

The first TWO-CHILD arm, and the first to need `Bounds.rec2₄` rather than `rec1₄`: `dlen_andIntro` is
`setLen s + dlen dp + dlen dq + 1`, so `hdeq` takes the shape `dlen (andIntro …) = dlen dp + dlen dq + (setLen s + 1)`
that `rec2₄`'s `d = y₁ + y₂ + m` wants.

Seven blocks (`proIns ++ L₁ ++ postIns ++ proIns ++ L₂ ++ postIns ++ nodeAnd`), so the length half is two
`Prologue.len_proIns_le ≤ 55·setLen (insert · s) + 12` — the two `setLen`s bounded by
`setLen_child_le_dlen_andIntro_left`/`_right` — plus `6 + 6 + 9 = 21`, i.e. the constant `110·D + 45 = 155`.

**The later-context hypotheses are EXPLICIT** (the Part-8 finding): the second `proIns` runs after the first child
and its `postIns`, so `hΓ₃`, `hLay₃` and `hDq₃` are wrapper hypotheses that the recursion supplies by transport.
`hDp` comes from `Prologue.layout_and` at the node's own layout. `shiftsV L₁ ≤ Czv·p4 (dlen dp)` (via
`shiftsV_le_len` on the first child's motive) is what bounds the later-context rooms `hiE₂`, `hipE₂` and `hgE3`. -/

section andWrapper

set_option maxHeartbeats 2000000 in
/-- **THE `and` MOTIVE WRAPPER.** -/
theorem and_wrapper {tbl N N' B' Wl Wc W₁ W T B E Czv Γ Γ₃ s p q dp dq L₁ L₂ : V}
    (htbl : TableOK tbl N) (hP : ProTable tbl) (htblN : NumTableOK T N' B')
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces) (hW₁ : W₁ = frag1Pieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hCz1 : 1 ≤ Czv) (hCk : ∀ n : ℕ, n ≤ 1000000 → ((n : ℕ) : V) ≤ Czv)
    (hCQ : 19 * B' + 25 ≤ Czv) (hCD : 27 * N' + 525600 * B' ≤ Czv)
    (hCbin : 2 * (27 * N' + 525600 * B') ≤ Czv)
    (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Czv)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p) (hq : IsSemiformula LAct 0 q)
    (hpq : (p ^⋏ q) ∈ s)
    (hdp : DerivationOf TAct dp (insert p s)) (hdq : DerivationOf TAct dq (insert q s))
    (hΓ : IsFormulaSet LAct Γ) (hLay : NodeLay walkPieces Wc T Γ s)
    (hΓ₃ : IsFormulaSet LAct Γ₃)
    (hLay₃ : Layout walkPieces Wc T Γ₃ s (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2))
    (hDq₃ : DossF walkPieces Γ₃ 0 q (memTop walkPieces Wc T s (p ^⋏ q) 0 + 1 +
      (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2)))
    (hchildSz₁ : SizeOK (kitQ Czv B E) (kitD Czv (2 * dlen TAct (andIntro s p q dp dq))) L₁)
    (hchildSz₂ : SizeOK (kitQ Czv B E) (kitD Czv (2 * dlen TAct (andIntro s p q dp dq))) L₂)
    (hchildLen₁ : len L₁ ≤ Czv * p4 (dlen TAct dp))
    (hchildLen₂ : len L₂ ≤ Czv * p4 (dlen TAct dq))
    (hE : Czv * p4 (dlen TAct (andIntro s p q dp dq) + 1) ≤ E) :
    len (vAnd walkPieces Wl Wc W₁ W T s p q dp dq L₁ L₂) ≤
      Czv * p4 (dlen TAct (andIntro s p q dp dq)) ∧
    SizeOK (kitQ Czv B E) (kitD Czv (2 * dlen TAct (andIntro s p q dp dq)))
      (vAnd walkPieces Wl Wc W₁ W T s p q dp dq L₁ L₂) := by
  have hD : Derivation TAct (andIntro s p q dp dq) := Derivation.andIntro hpq hdp hdq
  have hd1 : 1 ≤ dlen TAct (andIntro s p q dp dq) := one_le_dlen hD
  have hsD : setLen LAct s ≤ dlen TAct (andIntro s p q dp dq) := by
    have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_andIntro] at this
  have hcD₁ : setLen LAct (insert p s) ≤ dlen TAct (andIntro s p q dp dq) :=
    setLen_child_le_dlen_andIntro_left hD
  have hcD₂ : setLen LAct (insert q s) ≤ dlen TAct (andIntro s p q dp dq) :=
    setLen_child_le_dlen_andIntro_right hD
  have hdl : dlen TAct (andIntro s p q dp dq) = setLen LAct s + dlen TAct dp + dlen TAct dq + 1 :=
    dlen_andIntro hD
  have hdeq : dlen TAct (andIntro s p q dp dq) =
      dlen TAct dp + dlen TAct dq + (setLen LAct s + 1) := by rw [hdl]; ring
  have hps : IsFormulaSet LAct (insert p s) := IsFormulaSet.insert_iff.mpr ⟨hp, hs⟩
  have hqs : IsFormulaSet LAct (insert q s) := IsFormulaSet.insert_iff.mpr ⟨hq, hs⟩
  have hksD : len (memberList s) ≤ dlen TAct (andIntro s p q dp dq) :=
    le_trans (len_memberList_le_setLen hs) hsD
  have hk1 : 1 ≤ len (memberList s) := one_le_len_memberList_of_mem hpq
  have hkD₁ : len (memberList (insert p s)) ≤ dlen TAct (andIntro s p q dp dq) :=
    le_trans (len_memberList_le_setLen hps) hcD₁
  have hkD₂ : len (memberList (insert q s)) ≤ dlen TAct (andIntro s p q dp dq) :=
    le_trans (len_memberList_le_setLen hqs) hcD₂
  have he1 : (1 : V) ≤ dlen TAct (andIntro s p q dp dq) + 1 := le_add_self
  have hyp : dlen TAct dp ≤ dlen TAct (andIntro s p q dp dq) := by
    rw [hdeq]; exact le_trans le_self_add le_self_add
  have hyq : dlen TAct dq ≤ dlen TAct (andIntro s p q dp dq) := by
    rw [hdeq]; exact le_trans le_add_self le_self_add
  have hqmem : q ∈ insert q s := by simp
  have hqD : formulaLen LAct q ≤ dlen TAct (andIntro s p q dp dq) :=
    le_trans (formulaLen_le_setLen_of_mem (L := LAct) hqmem) hcD₂
  have hE1 : (1 : V) ≤ E := le_trans (le_trans hd1 (le_p4_self hd1))
    (le_trans (le_mul_of_one_le_left zero_le hCz1)
      (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE))
  have hDE : dlen TAct (andIntro s p q dp dq) ≤ E := le_trans (le_p4_self hd1)
    (le_trans (le_mul_of_one_le_left zero_le hCz1)
      (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE))
  have hEpro : 13 * dlen TAct (andIntro s p q dp dq) +
      18 * ‖dlen TAct (andIntro s p q dp dq)‖ + 12 ≤ E := by
    have := eroom_lin hE hCk 13 18 12 (by norm_num)
    push_cast at this
    exact this
  have hE8 : 13 * dlen TAct (andIntro s p q dp dq) +
      18 * ‖dlen TAct (andIntro s p q dp dq)‖ + 8 ≤ E := by
    have := eroom_lin hE hCk 13 18 8 (by norm_num)
    push_cast at this
    exact this
  have hiE₁ : 0 + 14 * dlen TAct (andIntro s p q dp dq) + 5 ≤ E := by
    rw [zero_add]
    have := eroom_lin hE hCk 14 0 5 (by norm_num)
    push_cast at this
    rw [zero_mul, add_zero] at this
    exact this
  have hnE : 18 * ‖dlen TAct (andIntro s p q dp dq)‖ + 7 ≤ E := by
    have := eroom_lin hE hCk 0 18 7 (by norm_num)
    push_cast at this
    rw [zero_mul, zero_add] at this
    exact this
  have hmT : memTop walkPieces Wc T s (p ^⋏ q) 0 ≤ 0 + 6 * dlen TAct (andIntro s p q dp dq) + 1 :=
    memTop_le htbl hP.walkTable hWc T hs hpq hsD
  have hdC : descCountF walkPieces 0 q ≤ 2 * dlen TAct (andIntro s p q dp dq) :=
    descCountF_le_of_len htbl hP.walkTable hq hqD
  have hshL₁ : shiftsV L₁ ≤ Czv * p4 (dlen TAct dp) := le_trans (shiftsV_le_len L₁) hchildLen₁
  have hshL₂ : shiftsV L₂ ≤ Czv * p4 (dlen TAct dq) := le_trans (shiftsV_le_len L₂) hchildLen₂
  have hsig₁ : proSig walkPieces Wl Wc W T (insert p s) ≤
      6 * dlen TAct (andIntro s p q dp dq) + 1 :=
    proSig_le htbl hP hWc htblN hWl hWp hps
      (one_le_len_memberList_of_mem (by simp : p ∈ insert p s)) hcD₁ hE8 hΓ
  have hsig₂ : proSig walkPieces Wl Wc W T (insert q s) ≤
      6 * dlen TAct (andIntro s p q dp dq) + 1 :=
    proSig_le htbl hP hWc htblN hWl hWp hqs
      (one_le_len_memberList_of_mem (by simp : q ∈ insert q s)) hcD₂ hE8 hΓ
  have hipE₁ : memTop walkPieces Wc T s (p ^⋏ q) 0 + descCountF walkPieces 0 q + 1 +
      8 * dlen TAct (andIntro s p q dp dq) + 4 ≤ E := by
    refine eroom_of_le hE hCk 16 6 (by norm_num) ?_
    push_cast
    calc memTop walkPieces Wc T s (p ^⋏ q) 0 + descCountF walkPieces 0 q + 1 +
          8 * dlen TAct (andIntro s p q dp dq) + 4
        ≤ (0 + 6 * dlen TAct (andIntro s p q dp dq) + 1) +
          2 * dlen TAct (andIntro s p q dp dq) + 1 +
          8 * dlen TAct (andIntro s p q dp dq) + 4 :=
          add_le_add (add_le_add (add_le_add (add_le_add hmT hdC) le_rfl) le_rfl) le_rfl
      _ = 16 * dlen TAct (andIntro s p q dp dq) + 6 := by ring
  have hiE₂ : 1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2 +
      14 * dlen TAct (andIntro s p q dp dq) + 5 ≤ E := by
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    have hlin : 20 * dlen TAct (andIntro s p q dp dq) + 9 ≤
        Czv * p3 (dlen TAct (andIntro s p q dp dq)) := by
      have h29 := hCk 29 (by norm_num)
      push_cast at h29
      exact lin_le_p3 hd1 (le_trans (le_of_eq (by norm_num : (20 : V) + 9 = 29)) h29)
    calc 1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2 +
          14 * dlen TAct (andIntro s p q dp dq) + 5
        ≤ 1 + (6 * dlen TAct (andIntro s p q dp dq) + 1) + Czv * p4 (dlen TAct dp) + 2 +
          14 * dlen TAct (andIntro s p q dp dq) + 5 :=
          add_le_add (add_le_add (add_le_add (add_le_add (add_le_add le_rfl hsig₁) hshL₁) le_rfl)
            le_rfl) le_rfl
      _ ≤ (20 * dlen TAct (andIntro s p q dp dq) + 9) +
          Czv * p4 (dlen TAct dp) + Czv * p4 (dlen TAct dq) :=
          le_of_add_eq' (c := Czv * p4 (dlen TAct dq)) (by ring)
      _ ≤ Czv * p4 (dlen TAct (andIntro s p q dp dq)) := rec2₄ le_add_self hdeq hlin
  have hipE₂ : memTop walkPieces Wc T s (p ^⋏ q) 0 + 1 +
      (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2) +
      8 * dlen TAct (andIntro s p q dp dq) + 4 ≤ E := by
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    have hlin2 : 20 * dlen TAct (andIntro s p q dp dq) + 10 ≤
        Czv * p3 (dlen TAct (andIntro s p q dp dq)) := by
      have h30 := hCk 30 (by norm_num)
      push_cast at h30
      exact lin_le_p3 hd1 (le_trans (le_of_eq (by norm_num : (20 : V) + 10 = 30)) h30)
    calc memTop walkPieces Wc T s (p ^⋏ q) 0 + 1 +
          (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2) +
          8 * dlen TAct (andIntro s p q dp dq) + 4
        ≤ (0 + 6 * dlen TAct (andIntro s p q dp dq) + 1) + 1 +
          (1 + (6 * dlen TAct (andIntro s p q dp dq) + 1) + Czv * p4 (dlen TAct dp) + 2) +
          8 * dlen TAct (andIntro s p q dp dq) + 4 :=
          add_le_add (add_le_add (add_le_add (add_le_add hmT le_rfl)
            (add_le_add (add_le_add (add_le_add le_rfl hsig₁) hshL₁) le_rfl)) le_rfl) le_rfl
      _ ≤ (20 * dlen TAct (andIntro s p q dp dq) + 10) +
          Czv * p4 (dlen TAct dp) + Czv * p4 (dlen TAct dq) :=
          le_of_add_eq' (c := Czv * p4 (dlen TAct dq)) (by ring)
      _ ≤ Czv * p4 (dlen TAct (andIntro s p q dp dq)) := rec2₄ le_add_self hdeq hlin2
  have hbn₁ : termLen LAct (bnum (dlen TAct dp)) ≤ E := eroom_bnum hE hCk hyp
  have hbn₂ : termLen LAct (bnum (dlen TAct dq)) ≤ E := eroom_bnum hE hCk hyq
  have hbn' : termLen LAct (bnum (dlen TAct (andIntro s p q dp dq))) ≤ E := eroom_bnum hE hCk le_rfl
  have hLn : setLen LAct s + dlen TAct dp + dlen TAct dq + 1 ≤
      dlen TAct (andIntro s p q dp dq) := le_of_eq hdl.symm
  have hnd : dlen TAct (andIntro s p q dp dq) ≤ 2 * dlen TAct (andIntro s p q dp dq) :=
    le_two_mul_self _
  have hgE₁ : len (memberList (insert p s)) + 1 + shiftsV L₁ + 1 ≤ E := by
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    have hlin : dlen TAct (andIntro s p q dp dq) + 2 ≤
        Czv * p3 (dlen TAct (andIntro s p q dp dq)) := by
      have h3 := hCk 3 (by norm_num)
      push_cast at h3
      have := lin_le_p3 (a := 1) (b := 2) hd1 (by
        exact le_trans (le_of_eq (by norm_num : (1 : V) + 2 = 3)) h3)
      rw [one_mul] at this
      exact this
    calc len (memberList (insert p s)) + 1 + shiftsV L₁ + 1
        ≤ dlen TAct (andIntro s p q dp dq) + 1 + Czv * p4 (dlen TAct dp) + 1 :=
          add_le_add (add_le_add (add_le_add hkD₁ le_rfl) hshL₁) le_rfl
      _ ≤ (dlen TAct (andIntro s p q dp dq) + 2) +
          Czv * p4 (dlen TAct dp) + Czv * p4 (dlen TAct dq) :=
          le_of_add_eq' (c := Czv * p4 (dlen TAct dq)) (by ring)
      _ ≤ Czv * p4 (dlen TAct (andIntro s p q dp dq)) := rec2₄ le_add_self hdeq hlin
  have hgE₂ : len (memberList (insert q s)) + 1 + shiftsV L₂ + 1 ≤ E := by
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    have hlin : dlen TAct (andIntro s p q dp dq) + 2 ≤
        Czv * p3 (dlen TAct (andIntro s p q dp dq)) := by
      have h3 := hCk 3 (by norm_num)
      push_cast at h3
      have := lin_le_p3 (a := 1) (b := 2) hd1 (by
        exact le_trans (le_of_eq (by norm_num : (1 : V) + 2 = 3)) h3)
      rw [one_mul] at this
      exact this
    calc len (memberList (insert q s)) + 1 + shiftsV L₂ + 1
        ≤ dlen TAct (andIntro s p q dp dq) + 1 + Czv * p4 (dlen TAct dq) + 1 :=
          add_le_add (add_le_add (add_le_add hkD₂ le_rfl) hshL₂) le_rfl
      _ ≤ (dlen TAct (andIntro s p q dp dq) + 2) +
          Czv * p4 (dlen TAct dp) + Czv * p4 (dlen TAct dq) :=
          le_of_add_eq' (c := Czv * p4 (dlen TAct dp)) (by ring)
      _ ≤ Czv * p4 (dlen TAct (andIntro s p q dp dq)) := rec2₄ le_add_self hdeq hlin
  have hgE3 : 1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2 +
      (1 + proSig walkPieces Wl Wc W T (insert q s) + shiftsV L₂ + 2) +
      (len (memberList s) + 1) + 1 + 1 ≤ E := by
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    have hlin : 13 * dlen TAct (andIntro s p q dp dq) + 11 ≤
        Czv * p3 (dlen TAct (andIntro s p q dp dq)) := by
      have h24 := hCk 24 (by norm_num)
      push_cast at h24
      exact lin_le_p3 hd1 (le_trans (le_of_eq (by norm_num : (13 : V) + 11 = 24)) h24)
    calc 1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2 +
          (1 + proSig walkPieces Wl Wc W T (insert q s) + shiftsV L₂ + 2) +
          (len (memberList s) + 1) + 1 + 1
        ≤ 1 + (6 * dlen TAct (andIntro s p q dp dq) + 1) + Czv * p4 (dlen TAct dp) + 2 +
          (1 + (6 * dlen TAct (andIntro s p q dp dq) + 1) + Czv * p4 (dlen TAct dq) + 2) +
          (dlen TAct (andIntro s p q dp dq) + 1) + 1 + 1 :=
          add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
            (add_le_add le_rfl hsig₁) hshL₁) le_rfl)
            (add_le_add (add_le_add (add_le_add le_rfl hsig₂) hshL₂) le_rfl))
            (add_le_add hksD le_rfl)) le_rfl) le_rfl
      _ = (13 * dlen TAct (andIntro s p q dp dq) + 11) +
          Czv * p4 (dlen TAct dp) + Czv * p4 (dlen TAct dq) := by ring
      _ ≤ Czv * p4 (dlen TAct (andIntro s p q dp dq)) := rec2₄ le_add_self hdeq hlin
  refine ⟨?_, ?_⟩
  · rw [len_vAnd_eq]
    have hlenPro₁ : len (proIns walkPieces Wl Wc W T s p 0
        (memTop walkPieces Wc T s (p ^⋏ q) 0 + descCountF walkPieces 0 q + 1)) ≤
        55 * dlen TAct (andIntro s p q dp dq) + 12 := by
      refine le_trans (len_proIns_le htbl hP hWl hWc walkPieces W T 0 _ hs hp) ?_
      exact add_le_add (mul_le_mul_of_nonneg_left hcD₁ zero_le) le_rfl
    have hlenPro₂ : len (proIns walkPieces Wl Wc W T s q
        (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2)
        (memTop walkPieces Wc T s (p ^⋏ q) 0 + 1 +
          (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2))) ≤
        55 * dlen TAct (andIntro s p q dp dq) + 12 := by
      refine le_trans (len_proIns_le htbl hP hWl hWc walkPieces W T _ _ hs hq) ?_
      exact add_le_add (mul_le_mul_of_nonneg_left hcD₂ zero_le) le_rfl
    have hX : 110 * dlen TAct (andIntro s p q dp dq) + 45 ≤
        Czv * p3 (dlen TAct (andIntro s p q dp dq)) := by
      have h155 := hCk 155 (by norm_num)
      push_cast at h155
      exact lin_le_p3 hd1 (le_trans (le_of_eq (by norm_num : (110 : V) + 45 = 155)) h155)
    calc len (proIns walkPieces Wl Wc W T s p 0
            (memTop walkPieces Wc T s (p ^⋏ q) 0 + descCountF walkPieces 0 q + 1)) +
          (len L₁ + (6 +
            (len (proIns walkPieces Wl Wc W T s q
              (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2)
              (memTop walkPieces Wc T s (p ^⋏ q) 0 + 1 +
                (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2))) +
              (len L₂ + (6 + 9)))))
        ≤ (55 * dlen TAct (andIntro s p q dp dq) + 12) +
          (Czv * p4 (dlen TAct dp) + (6 +
            ((55 * dlen TAct (andIntro s p q dp dq) + 12) +
              (Czv * p4 (dlen TAct dq) + 15)))) :=
          add_le_add hlenPro₁ (add_le_add hchildLen₁ (add_le_add le_rfl
            (add_le_add hlenPro₂ (add_le_add hchildLen₂ (by norm_num)))))
      _ = (110 * dlen TAct (andIntro s p q dp dq) + 45) +
          Czv * p4 (dlen TAct dp) + Czv * p4 (dlen TAct dq) := by ring
      _ ≤ Czv * p4 (dlen TAct (andIntro s p q dp dq)) := rec2₄ le_add_self hdeq hX
  · obtain ⟨-, hDp, -, -⟩ := layout_and htbl hP hp hq hpq hLay.layout
    exact and_arm_size (Wl := Wl) (Wc := Wc) (W₁ := W₁) (W := W) (T := T) (s := s) (p := p) (q := q)
      (dp := dp) (dq := dq) (L₁ := L₁) (L₂ := L₂)
      (B := B) (E := E) (Cz := Czv) (N' := N') (B' := B')
      (D := dlen TAct (andIntro s p q dp dq)) (d := dlen TAct (andIntro s p q dp dq))
      (Γ := Γ) (Γ₃ := Γ₃)
      hWp hW₁ htbl hP htblN hWl hWc hPle hs hp hq hk1 hcD₁ hcD₂ hEpro hiE₁ hipE₁ hiE₂ hipE₂
      hΓ hLay.layout hDp hΓ₃ hLay₃ hDq₃ hDE hnd hCQ hCD hCz1 hchildSz₁ hchildSz₂ hE1 hcG
      hgE₁ hgE₂ hbn₁ hbn₂ hbn' hnE hLn hnd hgE3 hCbin

end andWrapper

/-! ## 23. The `cut` motive wrapper

`and`'s shape with a `proCutPre` prefix and the two `cutPro` selectors, so EIGHT blocks and — being two-child —
every room on `Bounds.rec2₄` per TRAP 19. `dlen_cutRule` is `setLen s + dlen d₁ + dlen d₂ + 1`, the same shape as
`dlen_andIntro`.

Length half: `Prologue.len_proCutPre_le ≤ 64·|p|` (with `|p| ≤ D`) plus TWO `§14.len_cutPro_le ≤ 55·D + 13` plus
`6 + 6 + 9 = 21`, i.e. `174·D + 47 = 221`.

The rooms are stated over `mShift`/`mLen` rather than `memTop`/`descCountF`, bounded by `Prologue.mShift_le ≤ 4·|x|`
and `mLen_succ_le : mLen + 1 ≤ 2·|x|`, with `CutV.formulaLen_neg` turning `|neg p|` into `|p|`.

**The later-context AND the `Layout0` hypotheses are EXPLICIT.** `cut_arm_size` wants `Layout0` at both `cutPro`
offsets (`hLay0₁`, `hLay0₄`), and `NodeLay.layout` only supplies `Layout … s 0` — there is no lemma producing
`Layout0` at a shifted offset, so these are wrapper hypotheses the recursion discharges, alongside `hΓ₄`/`hLay₄`/
`hDnp₄` and the `proCutPre` context `hΓc`. -/

section cutWrapper

set_option maxHeartbeats 2000000 in
/-- **THE `cut` MOTIVE WRAPPER.** -/
theorem cut_wrapper {tbl N N' B' Wl Wc W₁ W T B E Czv Γ Γ₄ Γc s p d₁ d₂ L₁ L₂ : V}
    (htbl : TableOK tbl N) (hP : ProTable tbl) (htblN : NumTableOK T N' B')
    (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces) (hW₁ : W₁ = frag1Pieces)
    (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hCz1 : 1 ≤ Czv) (hCk : ∀ n : ℕ, n ≤ 1000000 → ((n : ℕ) : V) ≤ Czv)
    (hCQ : 19 * B' + 25 ≤ Czv) (hCD : 27 * N' + 525600 * B' ≤ Czv)
    (hCbin : 2 * (27 * N' + 525600 * B') ≤ Czv)
    (hcG : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Czv)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 0 p)
    (hd₁ : DerivationOf TAct d₁ (insert p s)) (hd₂ : DerivationOf TAct d₂ (insert (neg LAct p) s))
    (hsD0p : setLen LAct (insert p (0 : V)) ≤ dlen TAct (cutRule s p d₁ d₂))
    (hsD0np : setLen LAct (insert (neg LAct p) (0 : V)) ≤ dlen TAct (cutRule s p d₁ d₂))
    (hΓ : IsFormulaSet LAct Γ) (hLay : NodeLay walkPieces Wc T Γ s)
    (hLay₁ : Layout walkPieces Wc T Γ s (mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p)))
    (hLay0₁ : Layout0 walkPieces Wc T Γ (mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p)))
    (hDp₁ : DossF walkPieces Γ 0 p (mLen Wc T p + mShift walkPieces Wc T (neg LAct p)))
    (hΓ₄ : IsFormulaSet LAct Γ₄)
    (hLay₄ : Layout walkPieces Wc T Γ₄ s (mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) +
      (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2)))
    (hLay0₄ : Layout0 walkPieces Wc T Γ₄ (mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) +
      (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2)))
    (hDnp₄ : DossF walkPieces Γ₄ 0 (neg LAct p)
      (mLen Wc T (neg LAct p) + (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2)))
    (hΓc : IsFormulaSet LAct Γc)
    (hchildSz₁ : SizeOK (kitQ Czv B E) (kitD Czv (2 * dlen TAct (cutRule s p d₁ d₂))) L₁)
    (hchildSz₂ : SizeOK (kitQ Czv B E) (kitD Czv (2 * dlen TAct (cutRule s p d₁ d₂))) L₂)
    (hchildLen₁ : len L₁ ≤ Czv * p4 (dlen TAct d₁))
    (hchildLen₂ : len L₂ ≤ Czv * p4 (dlen TAct d₂))
    (hE : Czv * p4 (dlen TAct (cutRule s p d₁ d₂) + 1) ≤ E) :
    len (vCut walkPieces Wl Wc W₁ W T s p d₁ d₂ L₁ L₂) ≤ Czv * p4 (dlen TAct (cutRule s p d₁ d₂)) ∧
    SizeOK (kitQ Czv B E) (kitD Czv (2 * dlen TAct (cutRule s p d₁ d₂)))
      (vCut walkPieces Wl Wc W₁ W T s p d₁ d₂ L₁ L₂) := by
  have hD : Derivation TAct (cutRule s p d₁ d₂) := Derivation.cutRule hd₁ hd₂
  have hd1 : 1 ≤ dlen TAct (cutRule s p d₁ d₂) := one_le_dlen hD
  have hsD : setLen LAct s ≤ dlen TAct (cutRule s p d₁ d₂) := by
    have := setLen_fstIdx_le_dlen hD; rwa [fstIdx_cutRule] at this
  have hcD₁ : setLen LAct (insert p s) ≤ dlen TAct (cutRule s p d₁ d₂) :=
    setLen_child_le_dlen_cutRule_left hD
  have hcD₂ : setLen LAct (insert (neg LAct p) s) ≤ dlen TAct (cutRule s p d₁ d₂) :=
    setLen_child_le_dlen_cutRule_right hD
  have hdl : dlen TAct (cutRule s p d₁ d₂) = setLen LAct s + dlen TAct d₁ + dlen TAct d₂ + 1 :=
    dlen_cutRule hD
  have hdeq : dlen TAct (cutRule s p d₁ d₂) =
      dlen TAct d₁ + dlen TAct d₂ + (setLen LAct s + 1) := by rw [hdl]; ring
  have hps : IsFormulaSet LAct (insert p s) := IsFormulaSet.insert_iff.mpr ⟨hp, hs⟩
  have hnps : IsFormulaSet LAct (insert (neg LAct p) s) :=
    IsFormulaSet.insert_iff.mpr ⟨hp.neg, hs⟩
  have hksD : len (memberList s) ≤ dlen TAct (cutRule s p d₁ d₂) :=
    le_trans (len_memberList_le_setLen hs) hsD
  have hkD₁ : len (memberList (insert p s)) ≤ dlen TAct (cutRule s p d₁ d₂) :=
    le_trans (len_memberList_le_setLen hps) hcD₁
  have hkD₂ : len (memberList (insert (neg LAct p) s)) ≤ dlen TAct (cutRule s p d₁ d₂) :=
    le_trans (len_memberList_le_setLen hnps) hcD₂
  have he1 : (1 : V) ≤ dlen TAct (cutRule s p d₁ d₂) + 1 := le_add_self
  have hyp : dlen TAct d₁ ≤ dlen TAct (cutRule s p d₁ d₂) := by
    rw [hdeq]; exact le_trans le_self_add le_self_add
  have hyq : dlen TAct d₂ ≤ dlen TAct (cutRule s p d₁ d₂) := by
    rw [hdeq]; exact le_trans le_add_self le_self_add
  have hpmem : p ∈ insert p s := by simp
  have hpD : formulaLen LAct p ≤ dlen TAct (cutRule s p d₁ d₂) :=
    le_trans (formulaLen_le_setLen_of_mem (L := LAct) hpmem) hcD₁
  have hnpD : formulaLen LAct (neg LAct p) ≤ dlen TAct (cutRule s p d₁ d₂) := by
    rw [formulaLen_neg hp.isUFormula]; exact hpD
  have hE1 : (1 : V) ≤ E := le_trans (le_trans hd1 (le_p4_self hd1))
    (le_trans (le_mul_of_one_le_left zero_le hCz1)
      (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE))
  have hDE : dlen TAct (cutRule s p d₁ d₂) ≤ E := le_trans (le_p4_self hd1)
    (le_trans (le_mul_of_one_le_left zero_le hCz1)
      (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE))
  have hEpre : 13 * dlen TAct (cutRule s p d₁ d₂) + 8 ≤ E := by
    refine eroom_of_le hE hCk 13 8 (by norm_num) ?_
    push_cast
    exact le_rfl
  have hEpro : 13 * dlen TAct (cutRule s p d₁ d₂) +
      18 * ‖dlen TAct (cutRule s p d₁ d₂)‖ + 12 ≤ E := by
    have := eroom_lin hE hCk 13 18 12 (by norm_num)
    push_cast at this
    exact this
  have hE8 : 13 * dlen TAct (cutRule s p d₁ d₂) +
      18 * ‖dlen TAct (cutRule s p d₁ d₂)‖ + 8 ≤ E := by
    have := eroom_lin hE hCk 13 18 8 (by norm_num)
    push_cast at this
    exact this
  have hnE : 18 * ‖dlen TAct (cutRule s p d₁ d₂)‖ + 7 ≤ E := by
    have := eroom_lin hE hCk 0 18 7 (by norm_num)
    push_cast at this
    rw [zero_mul, zero_add] at this
    exact this
  have hmSp : mShift walkPieces Wc T p ≤ 4 * dlen TAct (cutRule s p d₁ d₂) :=
    le_trans (mShift_le htbl hP.walkTable hWc T hp) (mul_le_mul_of_nonneg_left hpD zero_le)
  have hmSnp : mShift walkPieces Wc T (neg LAct p) ≤ 4 * dlen TAct (cutRule s p d₁ d₂) :=
    le_trans (mShift_le htbl hP.walkTable hWc T hp.neg) (mul_le_mul_of_nonneg_left hnpD zero_le)
  have hmLp : mLen Wc T p ≤ 2 * dlen TAct (cutRule s p d₁ d₂) :=
    le_trans le_self_add (le_trans (mLen_succ_le hWc T hp) (mul_le_mul_of_nonneg_left hpD zero_le))
  have hmLnp : mLen Wc T (neg LAct p) ≤ 2 * dlen TAct (cutRule s p d₁ d₂) :=
    le_trans le_self_add
      (le_trans (mLen_succ_le hWc T hp.neg) (mul_le_mul_of_nonneg_left hnpD zero_le))
  have hshL₁ : shiftsV L₁ ≤ Czv * p4 (dlen TAct d₁) := le_trans (shiftsV_le_len L₁) hchildLen₁
  have hshL₂ : shiftsV L₂ ≤ Czv * p4 (dlen TAct d₂) := le_trans (shiftsV_le_len L₂) hchildLen₂
  have hsig₁ : proSig walkPieces Wl Wc W T (insert p s) ≤
      6 * dlen TAct (cutRule s p d₁ d₂) + 1 :=
    proSig_le htbl hP hWc htblN hWl hWp hps
      (one_le_len_memberList_of_mem hpmem) hcD₁ hE8 hΓ
  have hsig₂ : proSig walkPieces Wl Wc W T (insert (neg LAct p) s) ≤
      6 * dlen TAct (cutRule s p d₁ d₂) + 1 :=
    proSig_le htbl hP hWc htblN hWl hWp hnps
      (one_le_len_memberList_of_mem (by simp : neg LAct p ∈ insert (neg LAct p) s)) hcD₂ hE8 hΓ
  have hiE₁ : mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) +
      14 * dlen TAct (cutRule s p d₁ d₂) + 5 ≤ E := by
    refine eroom_of_le hE hCk 22 5 (by norm_num) ?_
    push_cast
    calc mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) +
          14 * dlen TAct (cutRule s p d₁ d₂) + 5
        ≤ 4 * dlen TAct (cutRule s p d₁ d₂) + 4 * dlen TAct (cutRule s p d₁ d₂) +
          14 * dlen TAct (cutRule s p d₁ d₂) + 5 :=
          add_le_add (add_le_add (add_le_add hmSp hmSnp) le_rfl) le_rfl
      _ = 22 * dlen TAct (cutRule s p d₁ d₂) + 5 := by ring
  have hipE₁ : mLen Wc T p + mShift walkPieces Wc T (neg LAct p) +
      8 * dlen TAct (cutRule s p d₁ d₂) + 4 ≤ E := by
    refine eroom_of_le hE hCk 14 4 (by norm_num) ?_
    push_cast
    calc mLen Wc T p + mShift walkPieces Wc T (neg LAct p) +
          8 * dlen TAct (cutRule s p d₁ d₂) + 4
        ≤ 2 * dlen TAct (cutRule s p d₁ d₂) + 4 * dlen TAct (cutRule s p d₁ d₂) +
          8 * dlen TAct (cutRule s p d₁ d₂) + 4 :=
          add_le_add (add_le_add (add_le_add hmLp hmSnp) le_rfl) le_rfl
      _ = 14 * dlen TAct (cutRule s p d₁ d₂) + 4 := by ring
  have hiE₂ : mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) +
      (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2) +
      14 * dlen TAct (cutRule s p d₁ d₂) + 5 ≤ E := by
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    have hlin : 28 * dlen TAct (cutRule s p d₁ d₂) + 9 ≤
        Czv * p3 (dlen TAct (cutRule s p d₁ d₂)) := by
      have h37 := hCk 37 (by norm_num)
      push_cast at h37
      exact lin_le_p3 hd1 (le_trans (le_of_eq (by norm_num : (28 : V) + 9 = 37)) h37)
    calc mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) +
          (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2) +
          14 * dlen TAct (cutRule s p d₁ d₂) + 5
        ≤ 4 * dlen TAct (cutRule s p d₁ d₂) + 4 * dlen TAct (cutRule s p d₁ d₂) +
          (1 + (6 * dlen TAct (cutRule s p d₁ d₂) + 1) + Czv * p4 (dlen TAct d₁) + 2) +
          14 * dlen TAct (cutRule s p d₁ d₂) + 5 :=
          add_le_add (add_le_add (add_le_add (add_le_add hmSp hmSnp)
            (add_le_add (add_le_add (add_le_add le_rfl hsig₁) hshL₁) le_rfl)) le_rfl) le_rfl
      _ ≤ (28 * dlen TAct (cutRule s p d₁ d₂) + 9) +
          Czv * p4 (dlen TAct d₁) + Czv * p4 (dlen TAct d₂) :=
          le_of_add_eq' (c := Czv * p4 (dlen TAct d₂)) (by ring)
      _ ≤ Czv * p4 (dlen TAct (cutRule s p d₁ d₂)) := rec2₄ le_add_self hdeq hlin
  have hipE₂ : mLen Wc T (neg LAct p) +
      (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2) +
      8 * dlen TAct (cutRule s p d₁ d₂) + 4 ≤ E := by
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    have hlin : 16 * dlen TAct (cutRule s p d₁ d₂) + 8 ≤
        Czv * p3 (dlen TAct (cutRule s p d₁ d₂)) := by
      have h24 := hCk 24 (by norm_num)
      push_cast at h24
      exact lin_le_p3 hd1 (le_trans (le_of_eq (by norm_num : (16 : V) + 8 = 24)) h24)
    calc mLen Wc T (neg LAct p) +
          (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2) +
          8 * dlen TAct (cutRule s p d₁ d₂) + 4
        ≤ 2 * dlen TAct (cutRule s p d₁ d₂) +
          (1 + (6 * dlen TAct (cutRule s p d₁ d₂) + 1) + Czv * p4 (dlen TAct d₁) + 2) +
          8 * dlen TAct (cutRule s p d₁ d₂) + 4 :=
          add_le_add (add_le_add (add_le_add hmLnp
            (add_le_add (add_le_add (add_le_add le_rfl hsig₁) hshL₁) le_rfl)) le_rfl) le_rfl
      _ ≤ (16 * dlen TAct (cutRule s p d₁ d₂) + 8) +
          Czv * p4 (dlen TAct d₁) + Czv * p4 (dlen TAct d₂) :=
          le_of_add_eq' (c := Czv * p4 (dlen TAct d₂)) (by ring)
      _ ≤ Czv * p4 (dlen TAct (cutRule s p d₁ d₂)) := rec2₄ le_add_self hdeq hlin
  have hbn₁ : termLen LAct (bnum (dlen TAct d₁)) ≤ E := eroom_bnum hE hCk hyp
  have hbn₂ : termLen LAct (bnum (dlen TAct d₂)) ≤ E := eroom_bnum hE hCk hyq
  have hbn' : termLen LAct (bnum (dlen TAct (cutRule s p d₁ d₂))) ≤ E := eroom_bnum hE hCk le_rfl
  have hLn : setLen LAct s + dlen TAct d₁ + dlen TAct d₂ + 1 ≤
      dlen TAct (cutRule s p d₁ d₂) := le_of_eq hdl.symm
  have hnd : dlen TAct (cutRule s p d₁ d₂) ≤ 2 * dlen TAct (cutRule s p d₁ d₂) :=
    le_two_mul_self _
  have hgE₁ : len (memberList (insert p s)) + 1 + shiftsV L₁ + 1 ≤ E := by
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    have hlin : dlen TAct (cutRule s p d₁ d₂) + 2 ≤
        Czv * p3 (dlen TAct (cutRule s p d₁ d₂)) := by
      have h3 := hCk 3 (by norm_num)
      push_cast at h3
      have := lin_le_p3 (a := 1) (b := 2) hd1 (by
        exact le_trans (le_of_eq (by norm_num : (1 : V) + 2 = 3)) h3)
      rw [one_mul] at this
      exact this
    calc len (memberList (insert p s)) + 1 + shiftsV L₁ + 1
        ≤ dlen TAct (cutRule s p d₁ d₂) + 1 + Czv * p4 (dlen TAct d₁) + 1 :=
          add_le_add (add_le_add (add_le_add hkD₁ le_rfl) hshL₁) le_rfl
      _ ≤ (dlen TAct (cutRule s p d₁ d₂) + 2) +
          Czv * p4 (dlen TAct d₁) + Czv * p4 (dlen TAct d₂) :=
          le_of_add_eq' (c := Czv * p4 (dlen TAct d₂)) (by ring)
      _ ≤ Czv * p4 (dlen TAct (cutRule s p d₁ d₂)) := rec2₄ le_add_self hdeq hlin
  have hgE₂ : len (memberList (insert (neg LAct p) s)) + 1 + shiftsV L₂ + 1 ≤ E := by
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    have hlin : dlen TAct (cutRule s p d₁ d₂) + 2 ≤
        Czv * p3 (dlen TAct (cutRule s p d₁ d₂)) := by
      have h3 := hCk 3 (by norm_num)
      push_cast at h3
      have := lin_le_p3 (a := 1) (b := 2) hd1 (by
        exact le_trans (le_of_eq (by norm_num : (1 : V) + 2 = 3)) h3)
      rw [one_mul] at this
      exact this
    calc len (memberList (insert (neg LAct p) s)) + 1 + shiftsV L₂ + 1
        ≤ dlen TAct (cutRule s p d₁ d₂) + 1 + Czv * p4 (dlen TAct d₂) + 1 :=
          add_le_add (add_le_add (add_le_add hkD₂ le_rfl) hshL₂) le_rfl
      _ ≤ (dlen TAct (cutRule s p d₁ d₂) + 2) +
          Czv * p4 (dlen TAct d₁) + Czv * p4 (dlen TAct d₂) :=
          le_of_add_eq' (c := Czv * p4 (dlen TAct d₁)) (by ring)
      _ ≤ Czv * p4 (dlen TAct (cutRule s p d₁ d₂)) := rec2₄ le_add_self hdeq hlin
  have hgE3 : mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) +
      (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2) +
      (1 + proSig walkPieces Wl Wc W T (insert (neg LAct p) s) + shiftsV L₂ + 2) +
      (len (memberList s) + 1) + 1 + 1 ≤ E := by
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (p4_mono le_self_add) zero_le) hE)
    have hlin : 21 * dlen TAct (cutRule s p d₁ d₂) + 11 ≤
        Czv * p3 (dlen TAct (cutRule s p d₁ d₂)) := by
      have h32 := hCk 32 (by norm_num)
      push_cast at h32
      exact lin_le_p3 hd1 (le_trans (le_of_eq (by norm_num : (21 : V) + 11 = 32)) h32)
    calc mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) +
          (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2) +
          (1 + proSig walkPieces Wl Wc W T (insert (neg LAct p) s) + shiftsV L₂ + 2) +
          (len (memberList s) + 1) + 1 + 1
        ≤ 4 * dlen TAct (cutRule s p d₁ d₂) + 4 * dlen TAct (cutRule s p d₁ d₂) +
          (1 + (6 * dlen TAct (cutRule s p d₁ d₂) + 1) + Czv * p4 (dlen TAct d₁) + 2) +
          (1 + (6 * dlen TAct (cutRule s p d₁ d₂) + 1) + Czv * p4 (dlen TAct d₂) + 2) +
          (dlen TAct (cutRule s p d₁ d₂) + 1) + 1 + 1 :=
          add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hmSp hmSnp)
            (add_le_add (add_le_add (add_le_add le_rfl hsig₁) hshL₁) le_rfl))
            (add_le_add (add_le_add (add_le_add le_rfl hsig₂) hshL₂) le_rfl))
            (add_le_add hksD le_rfl)) le_rfl) le_rfl
      _ = (21 * dlen TAct (cutRule s p d₁ d₂) + 11) +
          Czv * p4 (dlen TAct d₁) + Czv * p4 (dlen TAct d₂) := by ring
      _ ≤ Czv * p4 (dlen TAct (cutRule s p d₁ d₂)) := rec2₄ le_add_self hdeq hlin
  refine ⟨?_, ?_⟩
  · rw [len_vCut_eq]
    have hlenPre : len (proCutPre walkPieces Wc T p) ≤ 64 * dlen TAct (cutRule s p d₁ d₂) :=
      le_trans (len_proCutPre_le hWc walkPieces T hp) (mul_le_mul_of_nonneg_left hpD zero_le)
    have hlenCut₁ : len (cutPro walkPieces Wl Wc W T s p
        (mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p))
        (mLen Wc T p + mShift walkPieces Wc T (neg LAct p))) ≤
        55 * dlen TAct (cutRule s p d₁ d₂) + 13 :=
      len_cutPro_le htbl hP hWl hWc walkPieces W T _ _ hs hp hcD₁ hsD0p
    have hlenCut₂ : len (cutPro walkPieces Wl Wc W T s (neg LAct p)
        (mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) +
          (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2))
        (mLen Wc T (neg LAct p) +
          (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2))) ≤
        55 * dlen TAct (cutRule s p d₁ d₂) + 13 :=
      len_cutPro_le htbl hP hWl hWc walkPieces W T _ _ hs hp.neg hcD₂ hsD0np
    have hX : 174 * dlen TAct (cutRule s p d₁ d₂) + 47 ≤
        Czv * p3 (dlen TAct (cutRule s p d₁ d₂)) := by
      have h221 := hCk 221 (by norm_num)
      push_cast at h221
      exact lin_le_p3 hd1 (le_trans (le_of_eq (by norm_num : (174 : V) + 47 = 221)) h221)
    calc len (proCutPre walkPieces Wc T p) +
          (len (cutPro walkPieces Wl Wc W T s p
            (mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p))
            (mLen Wc T p + mShift walkPieces Wc T (neg LAct p))) +
            (len L₁ + (6 +
              (len (cutPro walkPieces Wl Wc W T s (neg LAct p)
                (mShift walkPieces Wc T p + mShift walkPieces Wc T (neg LAct p) +
                  (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2))
                (mLen Wc T (neg LAct p) +
                  (1 + proSig walkPieces Wl Wc W T (insert p s) + shiftsV L₁ + 2))) +
                (len L₂ + (6 + 9))))))
        ≤ 64 * dlen TAct (cutRule s p d₁ d₂) +
          ((55 * dlen TAct (cutRule s p d₁ d₂) + 13) +
            (Czv * p4 (dlen TAct d₁) + (6 +
              ((55 * dlen TAct (cutRule s p d₁ d₂) + 13) +
                (Czv * p4 (dlen TAct d₂) + 15))))) :=
          add_le_add hlenPre (add_le_add hlenCut₁ (add_le_add hchildLen₁ (add_le_add le_rfl
            (add_le_add hlenCut₂ (add_le_add hchildLen₂ (by norm_num))))))
      _ = (174 * dlen TAct (cutRule s p d₁ d₂) + 47) +
          Czv * p4 (dlen TAct d₁) + Czv * p4 (dlen TAct d₂) := by ring
      _ ≤ Czv * p4 (dlen TAct (cutRule s p d₁ d₂)) := rec2₄ le_add_self hdeq hX
  · exact cut_arm_size (Wl := Wl) (Wc := Wc) (W₁ := W₁) (W := W) (T := T) (s := s) (p := p)
      (d₁ := d₁) (d₂ := d₂) (L₁ := L₁) (L₂ := L₂)
      (B := B) (E := E) (Cz := Czv) (N' := N') (B' := B')
      (D := dlen TAct (cutRule s p d₁ d₂)) (d := dlen TAct (cutRule s p d₁ d₂))
      (Γ := Γ) (Γ₄ := Γ₄) (Γc := Γc)
      hWp hW₁ htbl hP htblN hWl hWc hPle hs hp hpD hnpD hcD₁ hcD₂ hsD0p hsD0np
      hEpre hEpro hiE₁ hipE₁ hiE₂ hipE₂ hΓ hLay₁ hLay0₁ hDp₁ hΓ₄ hLay₄ hLay0₄ hDnp₄ hΓc
      hDE hnd hCQ hCD hCz1 hchildSz₁ hchildSz₂ hE1 hcG hgE₁ hgE₂ hbn₁ hbn₂ hbn' hnE hLn hnd
      hgE3 hCbin

end cutWrapper

end ArithS
