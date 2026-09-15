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

end ArithS
