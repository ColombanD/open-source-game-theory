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

end ArithS
