import ArithS.Necessitation.Frag1
import ArithS.Necessitation.Frag2Rows

/-!
# ArithS.Necessitation.Frag2 — the four remaining per-tag fragments (`DESIGN_fragments.md` §4.5/4.6/4.8/4.10)

`Frag1.lean` delivers the six re-description-free tags (`axL`, `verumIntro`, `andIntro`, `orIntro`,
`wkRule`, `cutRule`). This file delivers the remaining four — `allIntro`, `exsIntro`, `shiftRule`,
`axm` — in exactly the same shape: a `node<Tag>Head` list of four steps (the totality, `fstIdx<Tag>`,
`Intro<Tag>`, `Dlen<Tag>`) followed by the `dlen` tail and `sGoal` of `Frag1` (§2 there), with a
`node<Tag>Head_ok`, a `node<Tag>_ok`, a `sizeOK_node<Tag>` and a `costSum_node<Tag>_le`.

**§0 — the tails on the Frag2 pieces.** `Frag1`'s `goalTail{Leaf,Unary,Binary}` are stated for
`W = frag1Pieces`; every step they emit reads a row index `< frag1RowCount`, so
`mkStep_frag2Pieces_lt` makes them literally EQUAL at `W = frag2Pieces`
(`dlen*Steps_frag2`, `goalTail*_frag2`) and the `_ok` theorems transfer verbatim (`goalTail*_ok'`).

**§1 `shiftRule`, §2 `allIntro`, §3 `exsIntro`, §4 `axm`.**

LAYOUT ASSUMED at `Γ` (the discipline of `Frag1` §4: every object is an eigenvariable `^&i` and
every fact it needs is `neg · ∈ Γ`). What the PROLOGUE must have established before the fragment
runs — i.e. what `Cert`'s producers (`certShift`/`certSubst`/`certFree`, `lenSteps`, `setLenSteps`)
and the `Layout` producers (`copySteps`/`chainSteps`/`eqSteps`) will supply, and which are stated
here as HYPOTHESES:

* every tag: the node's own sequent `s` at `is` with its length object `l` at `il`
  (`setLenFact &il &is`, `leFact &il (bnum L)`), and for the child its derivation object at `id`
  with `derFact`, its length object at `in₁` with `dlenFact` and the numeral bound
  `leFact &in₁ (bnum m₁)` — exactly what `goalElim` (`Frag1` §1) leaves;
* `shiftRule` (§4.8): the CHILD's sequent object `c` at `ic` (the chain over the unshifts), the
  `fstIdxFact &ic &id` moved onto it by `congFstIdx`, and the IDENTIFICATION
  `setShiftFact &is &ic` — "`s` is the setShift of `c`" — which the prologue gets from
  `setShiftTotal` + `setShiftInsert`/`setShiftFun` + `subsetAntisymm` + `congSetShiftL`
  (§4.8(2)–(3) there); the fragment itself does NOT redo that walk;
* `allIntro` (§4.5): the principal member `r` at `ir` with `allFact &ir &ip` and `memFact &ir &is`,
  the free instance `fp` at `ifp` with `freeFact &ifp &ip`, the shifted sequent `ss` at `iss` with
  `setShiftFact &iss &is`, and the child's row sequent `c` at `ic` with `insFact &ic &ifp &iss`
  and `fstIdxFact &ic &id`;
* `exsIntro` (§4.6): `r` at `ir` with `exsFact &ir &ip` and `memFact &ir &is`, the witness term
  `t` at `it` with `tPiFact (cT 0) &it` and `tlenFact &ilt &it`, the instance `pt` at `ipt` with
  `substs1Fact &ipt &it &ip`, and `c` at `ic` with `insFact &ic &ipt &is`, `fstIdxFact &ic &id`.
  Its `dlen` is the BINARY tail with `np := &ilt` bounded by `bnum Lt` (the term's length);
* `axm` (§4.10): `fsetPiFact &is`, the member `p` at `ip` with `memFact &ip &is`, and the
  RECOGNIZER fact `axchFact &ip` (`p ∈ TAct.Δ₁Class`). The recognizer chain that produces it —
  `axiomRec σ` for the finitely many standard axioms, `indRec` + the ℒₒᵣ/LAct bridge for the
  induction schema (`Lib/Bridge.lean`'s closing docstring) — is a PROLOGUE producer and is NOT in
  this file: `nodeAxm` consumes `axchFact` as a hypothesis. This is the one place where the
  fragment is weaker than `DESIGN_fragments` §4.10 describes, and it is deliberate: the chain
  needs `Cert`'s `pinSteps`/`certShift`/`certSubst`, none of which exists yet.

`L`, `m₁`, `Lt`, `n` are the VALUES `setLen s`, `dlen d`, `termLen t`, `dlen ν`; the closed `sLemma`
inside the tail needs the recurrence (`L + m₁ + 1 ≤ n`, resp. `L + Lt + m₁ + 1 ≤ n`, `L + 1 ≤ n`),
true by `DlenGraph.<tag>_iff`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 8000

/-! ## 0. The `Frag1` tails read from the `Frag2` pieces -/

section tails2

lemma mkStep_frag2_41 (ev : V) : mkStep frag2Pieces (41 : V) ev = mkStep frag1Pieces (41 : V) ev := by
  have := mkStep_frag2Pieces_lt 41 (by decide) ev; simpa using this
lemma mkStep_frag2_105 (ev : V) : mkStep frag2Pieces (105 : V) ev = mkStep frag1Pieces (105 : V) ev := by
  have := mkStep_frag2Pieces_lt 105 (by decide) ev; simpa using this
lemma mkStep_frag2_106 (ev : V) : mkStep frag2Pieces (106 : V) ev = mkStep frag1Pieces (106 : V) ev := by
  have := mkStep_frag2Pieces_lt 106 (by decide) ev; simpa using this
lemma mkStep_frag2_107 (ev : V) : mkStep frag2Pieces (107 : V) ev = mkStep frag1Pieces (107 : V) ev := by
  have := mkStep_frag2Pieces_lt 107 (by decide) ev; simpa using this
lemma mkStep_frag2_110 (ev : V) : mkStep frag2Pieces (110 : V) ev = mkStep frag1Pieces (110 : V) ev := by
  have := mkStep_frag2Pieces_lt 110 (by decide) ev; simpa using this

lemma dlenLeafSteps_frag2 (tblN l L n : V) :
    dlenLeafSteps (frag2Pieces : V) tblN l L n = dlenLeafSteps frag1Pieces tblN l L n := by
  unfold dlenLeafSteps; rw [mkStep_frag2_41, mkStep_frag2_105, mkStep_frag2_110]

lemma dlenUnarySteps_frag2 (tblN l n₁ L m₁ n : V) :
    dlenUnarySteps (frag2Pieces : V) tblN l n₁ L m₁ n = dlenUnarySteps frag1Pieces tblN l n₁ L m₁ n := by
  unfold dlenUnarySteps; rw [mkStep_frag2_41, mkStep_frag2_106, mkStep_frag2_110]

lemma dlenBinarySteps_frag2 (tblN l n₁ n₂ L m₁ m₂ n : V) :
    dlenBinarySteps (frag2Pieces : V) tblN l n₁ n₂ L m₁ m₂ n =
      dlenBinarySteps frag1Pieces tblN l n₁ n₂ L m₁ m₂ n := by
  unfold dlenBinarySteps; rw [mkStep_frag2_41, mkStep_frag2_107, mkStep_frag2_110]

lemma goalTailLeaf_frag2 (tblN l L n s : V) :
    goalTailLeaf (frag2Pieces : V) tblN l L n s = goalTailLeaf frag1Pieces tblN l L n s := by
  unfold goalTailLeaf; rw [dlenLeafSteps_frag2]

lemma goalTailUnary_frag2 (tblN l n₁ L m₁ n s : V) :
    goalTailUnary (frag2Pieces : V) tblN l n₁ L m₁ n s = goalTailUnary frag1Pieces tblN l n₁ L m₁ n s := by
  unfold goalTailUnary; rw [dlenUnarySteps_frag2]

lemma goalTailBinary_frag2 (tblN l n₁ n₂ L m₁ m₂ n s : V) :
    goalTailBinary (frag2Pieces : V) tblN l n₁ n₂ L m₁ m₂ n s =
      goalTailBinary frag1Pieces tblN l n₁ n₂ L m₁ m₂ n s := by
  unfold goalTailBinary; rw [dlenBinarySteps_frag2]

/-- The leaf tail at the `Frag2` pieces. -/
theorem goalTailLeaf_ok' {tbl N E Γ W tblN N' B' l L n s : V} (htbl : TableOK tbl N) (hF : Frag2Table tbl)
    (hWp : W = frag2Pieces) (htblN : NumTableOK tblN N' B') (hΓ : IsFormulaSet LAct Γ)
    (hl : l + 3 ≤ E) (hsE : s + 1 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + 1 ≤ n)
    (hle : neg LAct (leFact (^&l) (bnum L)) ∈ Γ) (hder : neg LAct (derFact (^&0 : V)) ∈ Γ)
    (hfst : neg LAct (fstIdxFact (^&s) (^&0)) ∈ Γ) (hdl : neg LAct (dlenFact (^&0 : V) (leafT l)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (goalTailLeaf W tblN l L n s) ∧ NoDrop' (goalTailLeaf W tblN l L n s) ∧
    shiftsV (goalTailLeaf W tblN l L n s) = 0 ∧ len (goalTailLeaf W tblN l L n s) = 5 ∧
    finalCtx Γ (goalTailLeaf W tblN l L n s) = insert (neg LAct (goalFact (^&s) (bnum n))) (dlenLeafCtx Γ l L n) ∧
    neg LAct (goalFact (^&s) (bnum n)) ∈ finalCtx Γ (goalTailLeaf W tblN l L n s) := by
  subst hWp; rw [goalTailLeaf_frag2]
  exact goalTailLeaf_ok htbl hF.frag1Table rfl htblN hΓ hl hsE hn hLn hle hder hfst hdl

/-- The unary tail at the `Frag2` pieces. -/
theorem goalTailUnary_ok' {tbl N E Γ W tblN N' B' l n₁ L m₁ n s : V} (htbl : TableOK tbl N) (hF : Frag2Table tbl)
    (hWp : W = frag2Pieces) (htblN : NumTableOK tblN N' B') (hΓ : IsFormulaSet LAct Γ)
    (hl : l + n₁ + 5 ≤ E) (hsE : s + 1 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + 1 ≤ n)
    (hle : neg LAct (leFact (^&l) (bnum L)) ∈ Γ) (hle₁ : neg LAct (leFact (^&n₁) (bnum m₁)) ∈ Γ)
    (hder : neg LAct (derFact (^&0 : V)) ∈ Γ) (hfst : neg LAct (fstIdxFact (^&s) (^&0)) ∈ Γ)
    (hdl : neg LAct (dlenFact (^&0 : V) (unaryT l n₁)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (goalTailUnary W tblN l n₁ L m₁ n s) ∧ NoDrop' (goalTailUnary W tblN l n₁ L m₁ n s) ∧
    shiftsV (goalTailUnary W tblN l n₁ L m₁ n s) = 0 ∧ len (goalTailUnary W tblN l n₁ L m₁ n s) = 5 ∧
    finalCtx Γ (goalTailUnary W tblN l n₁ L m₁ n s) =
      insert (neg LAct (goalFact (^&s) (bnum n))) (dlenUnaryCtx Γ l n₁ L m₁ n) ∧
    neg LAct (goalFact (^&s) (bnum n)) ∈ finalCtx Γ (goalTailUnary W tblN l n₁ L m₁ n s) := by
  subst hWp; rw [goalTailUnary_frag2]
  exact goalTailUnary_ok htbl hF.frag1Table rfl htblN hΓ hl hsE hn hLn hle hle₁ hder hfst hdl

/-- The binary tail at the `Frag2` pieces. -/
theorem goalTailBinary_ok' {tbl N E Γ W tblN N' B' l n₁ n₂ L m₁ m₂ n s : V} (htbl : TableOK tbl N)
    (hF : Frag2Table tbl) (hWp : W = frag2Pieces) (htblN : NumTableOK tblN N' B') (hΓ : IsFormulaSet LAct Γ)
    (hl : l + n₁ + n₂ + 7 ≤ E) (hsE : s + 1 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + m₂ + 1 ≤ n)
    (hle : neg LAct (leFact (^&l) (bnum L)) ∈ Γ) (hle₁ : neg LAct (leFact (^&n₁) (bnum m₁)) ∈ Γ)
    (hle₂ : neg LAct (leFact (^&n₂) (bnum m₂)) ∈ Γ)
    (hder : neg LAct (derFact (^&0 : V)) ∈ Γ) (hfst : neg LAct (fstIdxFact (^&s) (^&0)) ∈ Γ)
    (hdl : neg LAct (dlenFact (^&0 : V) (binaryT l n₁ n₂)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (goalTailBinary W tblN l n₁ n₂ L m₁ m₂ n s) ∧
    NoDrop' (goalTailBinary W tblN l n₁ n₂ L m₁ m₂ n s) ∧
    shiftsV (goalTailBinary W tblN l n₁ n₂ L m₁ m₂ n s) = 0 ∧
    len (goalTailBinary W tblN l n₁ n₂ L m₁ m₂ n s) = 5 ∧
    finalCtx Γ (goalTailBinary W tblN l n₁ n₂ L m₁ m₂ n s) =
      insert (neg LAct (goalFact (^&s) (bnum n))) (dlenBinaryCtx Γ l n₁ n₂ L m₁ m₂ n) ∧
    neg LAct (goalFact (^&s) (bnum n)) ∈ finalCtx Γ (goalTailBinary W tblN l n₁ n₂ L m₁ m₂ n s) := by
  subst hWp; rw [goalTailBinary_frag2]
  exact goalTailBinary_ok htbl hF.frag1Table rfl htblN hΓ hl hsE hn hLn hle hle₁ hle₂ hder hfst hdl

end tails2

end ArithS
