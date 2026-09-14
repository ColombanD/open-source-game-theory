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

/-! ## 1. `shiftRule` (`DESIGN_fragments.md` §4.8)

The node's sequent IS the shift of the child's: `introShiftB “e ss c d. fstIdxDef c d →
setShiftGraph ss c → derivation d → shiftRuleGraph e ss d → derivation e”`. So the fragment's
`ss` is the node's own sequent object at `is` and `c` is the CHILD's at `ic`; the identification
`setShiftFact &is &ic` is the prologue's job (§4.8(2)–(3)) and enters as a hypothesis. -/

section nodeShift

/-- The four node steps of `shiftRule`: `tot_shiftRule`, `fstIdx_shift`, `Intro_shift`, `Dlen_shift`. -/
noncomputable def nodeShiftHead (W is il ic id in₁ : V) : V :=
  mkStep W 128 ?[^&is, ^&id] ∷ mkStep W 142 ?[^&(is + 1), ^&(id + 1), ^&0] ∷
  mkStep W 132 ?[^&(id + 1), ^&(ic + 1), ^&(is + 1), ^&0] ∷
  mkStep W 135 ?[^&0, ^&(is + 1), ^&(id + 1), ^&(in₁ + 1), ^&(il + 1)] ∷ (0 : V)

/-- **The `shiftRule` node fragment**. -/
noncomputable def nodeShift (W tblN is il ic id in₁ L m₁ n : V) : V :=
  appendV (nodeShiftHead W is il ic id in₁) (goalTailUnary W tblN (il + 1) (in₁ + 1) L m₁ n (is + 1))

noncomputable def nodeShiftHeadCtx (Γ is il id in₁ : V) : V :=
  insert (neg LAct (dlenFact (^&0 : V) (unaryT (il + 1) (in₁ + 1))))
    (insert (neg LAct (derFact (^&0 : V)))
      (insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0)))
        (insert (neg LAct (shiftRuleFact (^&0 : V) (^&(is + 1)) (^&(id + 1)))) (setShift LAct Γ))))

theorem nodeShiftHead_ok {tbl N E Γ W is il ic id in₁ : V} (htbl : TableOK tbl N)
    (hF : Frag2Table tbl) (hWp : W = frag2Pieces) (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hil : il + 2 ≤ E) (hic : ic + 2 ≤ E) (hid : id + 2 ≤ E) (hin₁ : in₁ + 2 ≤ E)
    (hf : neg LAct (fstIdxFact (^&ic) (^&id)) ∈ Γ)
    (hss : neg LAct (setShiftFact (^&is) (^&ic)) ∈ Γ)
    (hd : neg LAct (derFact (^&id : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id : V) (^&in₁)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (nodeShiftHead W is il ic id in₁) ∧ NoDrop' (nodeShiftHead W is il ic id in₁) ∧
    shiftsV (nodeShiftHead W is il ic id in₁) = 1 ∧ len (nodeShiftHead W is il ic id in₁) = 4 ∧
    finalCtx Γ (nodeShiftHead W is il ic id in₁) = nodeShiftHeadCtx Γ is il id in₁ := by
  have his0 : IsSemiterm LAct 0 (^&is : V) := by simp
  have hisE : termLen LAct (^&is : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) his)
  have his1 : IsSemiterm LAct 0 (^&(is + 1) : V) := by simp
  have his1E : termLen LAct (^&(is + 1) : V) ≤ E := termLen_fvar_succ_le his
  have hil0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hilE : termLen LAct (^&il : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hil)
  have hil1 : IsSemiterm LAct 0 (^&(il + 1) : V) := by simp
  have hil1E : termLen LAct (^&(il + 1) : V) ≤ E := termLen_fvar_succ_le hil
  have hic0 : IsSemiterm LAct 0 (^&ic : V) := by simp
  have hicE : termLen LAct (^&ic : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hic)
  have hic1 : IsSemiterm LAct 0 (^&(ic + 1) : V) := by simp
  have hic1E : termLen LAct (^&(ic + 1) : V) ≤ E := termLen_fvar_succ_le hic
  have hid0 : IsSemiterm LAct 0 (^&id : V) := by simp
  have hidE : termLen LAct (^&id : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hid)
  have hid1 : IsSemiterm LAct 0 (^&(id + 1) : V) := by simp
  have hid1E : termLen LAct (^&(id + 1) : V) ≤ E := termLen_fvar_succ_le hid
  have hin₁0 : IsSemiterm LAct 0 (^&in₁ : V) := by simp
  have hin₁E : termLen LAct (^&in₁ : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hin₁)
  have hin₁1 : IsSemiterm LAct 0 (^&(in₁ + 1) : V) := by simp
  have hin₁1E : termLen LAct (^&(in₁ + 1) : V) ≤ E := termLen_fvar_succ_le hin₁
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hf0E : termLen LAct (^&0 : V) ≤ E :=
    termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) (le_trans le_add_self his))
  -- step 1: tot_shiftRule
  obtain ⟨ok₁, tg₁, cx₁⟩ := gok_totShiftRule htbl hF hWp hΓ his0 hisE hid0 hidE
  rw [termShift_fvar, termShift_fvar, Nat.cast_zero] at cx₁
  set F := neg LAct (shiftRuleFact (^&0 : V) (^&(is + 1)) (^&(id + 1))) with hFdef
  set Γ₁ := insert F (setShift LAct Γ) with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := cx₁ ▸ isFormulaSet_ctxAfter 8 htbl ok₁
  have tf : neg LAct (fstIdxFact (^&(ic + 1)) (^&(id + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hf
    rwa [shift_neg (isFormula_fstIdxFact hic0 hid0), shift_fstIdxFact hic0 hid0, termShift_fvar, termShift_fvar] at this
  have tss : neg LAct (setShiftFact (^&(is + 1)) (^&(ic + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hss
    rwa [shift_neg (isFormula_setShiftFact his0 hic0), shift_setShiftFact his0 hic0, termShift_fvar, termShift_fvar] at this
  have td : neg LAct (derFact (^&(id + 1) : V)) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hd
    rwa [shift_neg (isFormula_derFact hid0), shift_derFact hid0, termShift_fvar] at this
  have tn₁ : neg LAct (dlenFact (^&(id + 1) : V) (^&(in₁ + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hn₁
    rwa [shift_neg (isFormula_dlenFact hid0 hin₁0), shift_dlenFact hid0 hin₁0, termShift_fvar, termShift_fvar] at this
  have tsl : neg LAct (setLenFact (^&(il + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hsl
    rwa [shift_neg (isFormula_setLenFact hil0 his0), shift_setLenFact hil0 his0, termShift_fvar, termShift_fvar] at this
  -- step 2: fstIdx_shift
  obtain ⟨ok₂, tg₂, cx₂⟩ := gok_fstIdxShift htbl hF hWp hΓ₁ his1 his1E hid1 hid1E hf0 hf0E
    (by rw [hΓ₁def, hFdef]; simp)
  set Γ₂ := insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0))) Γ₁ with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := cx₂ ▸ isFormulaSet_ctxAfter 8 htbl ok₂
  -- step 3: Intro_shift
  obtain ⟨ok₃, tg₃, cx₃⟩ := gok_introShift htbl hF hWp hΓ₂ hid1 hid1E hic1 hic1E his1 his1E hf0 hf0E
    (by rw [hΓ₂def]; simp [tf]) (by rw [hΓ₂def]; simp [tss]) (by rw [hΓ₂def]; simp [td])
    (by rw [hΓ₂def, hΓ₁def, hFdef]; simp)
  set Γ₃ := insert (neg LAct (derFact (^&0 : V))) Γ₂ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := cx₃ ▸ isFormulaSet_ctxAfter 8 htbl ok₃
  -- step 4: Dlen_shift
  obtain ⟨ok₄, tg₄, cx₄⟩ := gok_dlenShift htbl hF hWp hΓ₃ hf0 hf0E his1 his1E hid1 hid1E hin₁1 hin₁1E hil1 hil1E
    (by rw [hΓ₃def, hΓ₂def, hΓ₁def, hFdef]; simp) (by rw [hΓ₃def, hΓ₂def]; simp [tn₁])
    (by rw [hΓ₃def, hΓ₂def]; simp [tsl])
  have hfin : finalCtx Γ (nodeShiftHead W is il ic id in₁) = nodeShiftHeadCtx Γ is il id in₁ := by
    unfold nodeShiftHead
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_single, cx₄]
    rfl
  refine ⟨?_, ?_, ?_, ?_, hfin⟩
  · unfold nodeShiftHead
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    exact listOK_single ok₄
  · unfold nodeShiftHead
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp)
      (noDrop'_cons (by rw [tg₃]; simp) (noDrop'_single (by rw [tg₄]; simp))))
  · unfold nodeShiftHead
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₃, tg₄]
    simp
  · unfold nodeShiftHead; simp [len_adjoin]; norm_num

/-- **`nodeShift` is applicable**. -/
theorem nodeShift_ok {tbl N E Γ W tblN N' B' is il ic id in₁ L m₁ n : V}
    (htbl : TableOK tbl N) (hF : Frag2Table tbl) (hWp : W = frag2Pieces) (htblN : NumTableOK tblN N' B')
    (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hic : ic + 2 ≤ E) (hid : id + 2 ≤ E)
    (hT : il + in₁ + 7 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + 1 ≤ n)
    (hf : neg LAct (fstIdxFact (^&ic) (^&id)) ∈ Γ)
    (hss : neg LAct (setShiftFact (^&is) (^&ic)) ∈ Γ)
    (hd : neg LAct (derFact (^&id : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id : V) (^&in₁)) ∈ Γ)
    (hle₁ : neg LAct (leFact (^&in₁) (bnum m₁)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (nodeShift W tblN is il ic id in₁ L m₁ n) ∧
    NoDrop' (nodeShift W tblN is il ic id in₁ L m₁ n) ∧
    shiftsV (nodeShift W tblN is il ic id in₁ L m₁ n) = 1 ∧
    len (nodeShift W tblN is il ic id in₁ L m₁ n) = 9 ∧
    neg LAct (goalFact (^&(is + 1)) (bnum n)) ∈ finalCtx Γ (nodeShift W tblN is il ic id in₁ L m₁ n) := by
  have hil : il + 2 ≤ E := le_trans (add_le_add le_self_add (by norm_num)) hT
  have hin₁ : in₁ + 2 ≤ E := le_trans (add_le_add le_add_self (by norm_num)) hT
  obtain ⟨hok, hnd, hsv, hlen, hfin⟩ := nodeShiftHead_ok htbl hF hWp hΓ his hil hic hid hin₁ hf hss hd hn₁ hsl
  have hΓ' : IsFormulaSet LAct (finalCtx Γ (nodeShiftHead W is il ic id in₁)) := finalCtx_isFormulaSet 8 htbl hΓ hok
  have hl0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hn10 : IsSemiterm LAct 0 (^&in₁ : V) := by simp
  have hbL : IsSemiterm LAct 0 (bnum L) := isSemiterm_bnum_LAct 0 L
  have hbm₁ : IsSemiterm LAct 0 (bnum m₁) := isSemiterm_bnum_LAct 0 m₁
  have tr : ∀ x ∈ Γ, shift LAct x ∈ finalCtx Γ (nodeShiftHead W is il ic id in₁) := by
    intro x hx; rw [hfin]; unfold nodeShiftHeadCtx; exact shift_mem_head3 hx
  have hle' : neg LAct (leFact (^&(il + 1)) (bnum L)) ∈ finalCtx Γ (nodeShiftHead W is il ic id in₁) := by
    have := tr _ hle
    rwa [shift_neg (isFormula_leFact hl0 hbL), shift_leFact hl0 hbL, termShift_fvar, termShift_bnum] at this
  have hle₁' : neg LAct (leFact (^&(in₁ + 1)) (bnum m₁)) ∈ finalCtx Γ (nodeShiftHead W is il ic id in₁) := by
    have := tr _ hle₁
    rwa [shift_neg (isFormula_leFact hn10 hbm₁), shift_leFact hn10 hbm₁, termShift_fvar, termShift_bnum] at this
  obtain ⟨tok, tnd, tsv, tlen, tfin, tmem⟩ := goalTailUnary_ok' htbl hF hWp htblN hΓ'
    (by rw [show il + 1 + (in₁ + 1) + 5 = il + in₁ + 7 by ring]; exact hT)
    (by rw [add_assoc, one_add_one_eq_two]; exact his) hn hLn hle' hle₁'
    (by rw [hfin]; unfold nodeShiftHeadCtx; simp) (by rw [hfin]; unfold nodeShiftHeadCtx; simp)
    (by rw [hfin]; unfold nodeShiftHeadCtx; simp)
  refine ⟨listOK_appendV hok tok, noDrop'_appendV hnd tnd, ?_, ?_, ?_⟩
  · unfold nodeShift; rw [shiftsV_appendV, hsv, tsv, add_zero]
  · unfold nodeShift; rw [len_appendV, hlen, tlen]; norm_num
  · unfold nodeShift; rw [finalCtx_appendV]; exact tmem

end nodeShift

/-! ## 2. `allIntro` (`DESIGN_fragments.md` §4.5)

`introAllB “e c ss fp r d p s. allIntroGraph e s p d → qqAllDef r p → r ∈ s → fstIdxDef c d →
freeGraph fp p → setShiftGraph ss s → insertDef c fp ss → derivation d → derivation e”`.
The three FRESH objects the prologue must supply — the free instance `fp` (`certFree`), the
shifted sequent `ss` (`setShiftTotal`) and the row's sequent `c` (`insertTotal`, identified with
the child's chain top) — enter with their facts as hypotheses. -/

section nodeAll

/-- The four node steps of `allIntro`: `tot_allIntro`, `fstIdx_all`, `Intro_all`, `Dlen_all`. -/
noncomputable def nodeAllHead (W is il ir ip ifp iss ic id in₁ : V) : V :=
  mkStep W 126 ?[^&is, ^&ip, ^&id] ∷ mkStep W 140 ?[^&(is + 1), ^&(ip + 1), ^&(id + 1), ^&0] ∷
  mkStep W 130 ?[^&(is + 1), ^&(ip + 1), ^&(id + 1), ^&(ir + 1), ^&(ifp + 1), ^&(iss + 1), ^&(ic + 1), ^&0] ∷
  mkStep W 133 ?[^&0, ^&(is + 1), ^&(ip + 1), ^&(id + 1), ^&(in₁ + 1), ^&(il + 1)] ∷ (0 : V)

/-- **The `allIntro` node fragment**. -/
noncomputable def nodeAll (W tblN is il ir ip ifp iss ic id in₁ L m₁ n : V) : V :=
  appendV (nodeAllHead W is il ir ip ifp iss ic id in₁)
    (goalTailUnary W tblN (il + 1) (in₁ + 1) L m₁ n (is + 1))

noncomputable def nodeAllHeadCtx (Γ is il ip id in₁ : V) : V :=
  insert (neg LAct (dlenFact (^&0 : V) (unaryT (il + 1) (in₁ + 1))))
    (insert (neg LAct (derFact (^&0 : V)))
      (insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0)))
        (insert (neg LAct (allIntroFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)) (^&(id + 1)))) (setShift LAct Γ))))

theorem nodeAllHead_ok {tbl N E Γ W is il ir ip ifp iss ic id in₁ : V} (htbl : TableOK tbl N)
    (hF : Frag2Table tbl) (hWp : W = frag2Pieces) (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hil : il + 2 ≤ E) (hir : ir + 2 ≤ E) (hip : ip + 2 ≤ E) (hifp : ifp + 2 ≤ E)
    (hiss : iss + 2 ≤ E) (hic : ic + 2 ≤ E) (hid : id + 2 ≤ E) (hin₁ : in₁ + 2 ≤ E)
    (hall : neg LAct (allFact (^&ir) (^&ip)) ∈ Γ) (hmr : neg LAct (memFact (^&ir) (^&is)) ∈ Γ)
    (hfst : neg LAct (fstIdxFact (^&ic) (^&id)) ∈ Γ)
    (hfree : neg LAct (freeFact (^&ifp) (^&ip)) ∈ Γ)
    (hsh : neg LAct (setShiftFact (^&iss) (^&is)) ∈ Γ)
    (hins : neg LAct (insFact (^&ic) (^&ifp) (^&iss)) ∈ Γ)
    (hd : neg LAct (derFact (^&id : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id : V) (^&in₁)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (nodeAllHead W is il ir ip ifp iss ic id in₁) ∧
    NoDrop' (nodeAllHead W is il ir ip ifp iss ic id in₁) ∧
    shiftsV (nodeAllHead W is il ir ip ifp iss ic id in₁) = 1 ∧
    len (nodeAllHead W is il ir ip ifp iss ic id in₁) = 4 ∧
    finalCtx Γ (nodeAllHead W is il ir ip ifp iss ic id in₁) = nodeAllHeadCtx Γ is il ip id in₁ := by
  have his0 : IsSemiterm LAct 0 (^&is : V) := by simp
  have hisE : termLen LAct (^&is : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) his)
  have his1 : IsSemiterm LAct 0 (^&(is + 1) : V) := by simp
  have his1E : termLen LAct (^&(is + 1) : V) ≤ E := termLen_fvar_succ_le his
  have hil0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hil1 : IsSemiterm LAct 0 (^&(il + 1) : V) := by simp
  have hil1E : termLen LAct (^&(il + 1) : V) ≤ E := termLen_fvar_succ_le hil
  have hir0 : IsSemiterm LAct 0 (^&ir : V) := by simp
  have hir1 : IsSemiterm LAct 0 (^&(ir + 1) : V) := by simp
  have hir1E : termLen LAct (^&(ir + 1) : V) ≤ E := termLen_fvar_succ_le hir
  have hip0 : IsSemiterm LAct 0 (^&ip : V) := by simp
  have hipE : termLen LAct (^&ip : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hip)
  have hip1 : IsSemiterm LAct 0 (^&(ip + 1) : V) := by simp
  have hip1E : termLen LAct (^&(ip + 1) : V) ≤ E := termLen_fvar_succ_le hip
  have hifp0 : IsSemiterm LAct 0 (^&ifp : V) := by simp
  have hifp1 : IsSemiterm LAct 0 (^&(ifp + 1) : V) := by simp
  have hifp1E : termLen LAct (^&(ifp + 1) : V) ≤ E := termLen_fvar_succ_le hifp
  have hiss0 : IsSemiterm LAct 0 (^&iss : V) := by simp
  have hiss1 : IsSemiterm LAct 0 (^&(iss + 1) : V) := by simp
  have hiss1E : termLen LAct (^&(iss + 1) : V) ≤ E := termLen_fvar_succ_le hiss
  have hic0 : IsSemiterm LAct 0 (^&ic : V) := by simp
  have hic1 : IsSemiterm LAct 0 (^&(ic + 1) : V) := by simp
  have hic1E : termLen LAct (^&(ic + 1) : V) ≤ E := termLen_fvar_succ_le hic
  have hid0 : IsSemiterm LAct 0 (^&id : V) := by simp
  have hidE : termLen LAct (^&id : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hid)
  have hid1 : IsSemiterm LAct 0 (^&(id + 1) : V) := by simp
  have hid1E : termLen LAct (^&(id + 1) : V) ≤ E := termLen_fvar_succ_le hid
  have hin₁0 : IsSemiterm LAct 0 (^&in₁ : V) := by simp
  have hin₁1 : IsSemiterm LAct 0 (^&(in₁ + 1) : V) := by simp
  have hin₁1E : termLen LAct (^&(in₁ + 1) : V) ≤ E := termLen_fvar_succ_le hin₁
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hf0E : termLen LAct (^&0 : V) ≤ E :=
    termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) (le_trans le_add_self his))
  -- step 1: tot_allIntro
  obtain ⟨ok₁, tg₁, cx₁⟩ := gok_totAllIntro htbl hF hWp hΓ his0 hisE hip0 hipE hid0 hidE
  rw [termShift_fvar, termShift_fvar, termShift_fvar, Nat.cast_zero] at cx₁
  set F := neg LAct (allIntroFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)) (^&(id + 1))) with hFdef
  set Γ₁ := insert F (setShift LAct Γ) with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := cx₁ ▸ isFormulaSet_ctxAfter 8 htbl ok₁
  have tall : neg LAct (allFact (^&(ir + 1)) (^&(ip + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hall
    rwa [shift_neg (isFormula_allFact hir0 hip0), shift_allFact hir0 hip0, termShift_fvar, termShift_fvar] at this
  have tmr : neg LAct (memFact (^&(ir + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hmr
    rwa [shift_neg (isFormula_memFact hir0 his0), shift_memFact hir0 his0, termShift_fvar, termShift_fvar] at this
  have tfst : neg LAct (fstIdxFact (^&(ic + 1)) (^&(id + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hfst
    rwa [shift_neg (isFormula_fstIdxFact hic0 hid0), shift_fstIdxFact hic0 hid0, termShift_fvar, termShift_fvar] at this
  have tfree : neg LAct (freeFact (^&(ifp + 1)) (^&(ip + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hfree
    rwa [shift_neg (isFormula_freeFact hifp0 hip0), shift_freeFact hifp0 hip0, termShift_fvar, termShift_fvar] at this
  have tsh : neg LAct (setShiftFact (^&(iss + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hsh
    rwa [shift_neg (isFormula_setShiftFact hiss0 his0), shift_setShiftFact hiss0 his0, termShift_fvar, termShift_fvar] at this
  have tins : neg LAct (insFact (^&(ic + 1)) (^&(ifp + 1)) (^&(iss + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hins
    rwa [shift_neg (isFormula_insFact hic0 hifp0 hiss0), shift_insFact hic0 hifp0 hiss0,
      termShift_fvar, termShift_fvar, termShift_fvar] at this
  have td : neg LAct (derFact (^&(id + 1) : V)) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hd
    rwa [shift_neg (isFormula_derFact hid0), shift_derFact hid0, termShift_fvar] at this
  have tn₁ : neg LAct (dlenFact (^&(id + 1) : V) (^&(in₁ + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hn₁
    rwa [shift_neg (isFormula_dlenFact hid0 hin₁0), shift_dlenFact hid0 hin₁0, termShift_fvar, termShift_fvar] at this
  have tsl : neg LAct (setLenFact (^&(il + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hsl
    rwa [shift_neg (isFormula_setLenFact hil0 his0), shift_setLenFact hil0 his0, termShift_fvar, termShift_fvar] at this
  -- step 2: fstIdx_all
  obtain ⟨ok₂, tg₂, cx₂⟩ := gok_fstIdxAll htbl hF hWp hΓ₁ his1 his1E hip1 hip1E hid1 hid1E hf0 hf0E
    (by rw [hΓ₁def, hFdef]; simp)
  set Γ₂ := insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0))) Γ₁ with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := cx₂ ▸ isFormulaSet_ctxAfter 8 htbl ok₂
  -- step 3: Intro_all
  obtain ⟨ok₃, tg₃, cx₃⟩ := gok_introAll htbl hF hWp hΓ₂ his1 his1E hip1 hip1E hid1 hid1E hir1 hir1E
    hifp1 hifp1E hiss1 hiss1E hic1 hic1E hf0 hf0E
    (by rw [hΓ₂def, hΓ₁def, hFdef]; simp) (by rw [hΓ₂def]; simp [tall]) (by rw [hΓ₂def]; simp [tmr])
    (by rw [hΓ₂def]; simp [tfst]) (by rw [hΓ₂def]; simp [tfree]) (by rw [hΓ₂def]; simp [tsh])
    (by rw [hΓ₂def]; simp [tins]) (by rw [hΓ₂def]; simp [td])
  set Γ₃ := insert (neg LAct (derFact (^&0 : V))) Γ₂ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := cx₃ ▸ isFormulaSet_ctxAfter 8 htbl ok₃
  -- step 4: Dlen_all
  obtain ⟨ok₄, tg₄, cx₄⟩ := gok_dlenAll htbl hF hWp hΓ₃ hf0 hf0E his1 his1E hip1 hip1E hid1 hid1E
    hin₁1 hin₁1E hil1 hil1E
    (by rw [hΓ₃def, hΓ₂def, hΓ₁def, hFdef]; simp) (by rw [hΓ₃def, hΓ₂def]; simp [tn₁])
    (by rw [hΓ₃def, hΓ₂def]; simp [tsl])
  have hfin : finalCtx Γ (nodeAllHead W is il ir ip ifp iss ic id in₁) = nodeAllHeadCtx Γ is il ip id in₁ := by
    unfold nodeAllHead
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_single, cx₄]
    rfl
  refine ⟨?_, ?_, ?_, ?_, hfin⟩
  · unfold nodeAllHead
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    exact listOK_single ok₄
  · unfold nodeAllHead
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp)
      (noDrop'_cons (by rw [tg₃]; simp) (noDrop'_single (by rw [tg₄]; simp))))
  · unfold nodeAllHead
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₃, tg₄]
    simp
  · unfold nodeAllHead; simp [len_adjoin]; norm_num

/-- **`nodeAll` is applicable**. -/
theorem nodeAll_ok {tbl N E Γ W tblN N' B' is il ir ip ifp iss ic id in₁ L m₁ n : V}
    (htbl : TableOK tbl N) (hF : Frag2Table tbl) (hWp : W = frag2Pieces) (htblN : NumTableOK tblN N' B')
    (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hir : ir + 2 ≤ E) (hip : ip + 2 ≤ E) (hifp : ifp + 2 ≤ E)
    (hiss : iss + 2 ≤ E) (hic : ic + 2 ≤ E) (hid : id + 2 ≤ E)
    (hT : il + in₁ + 7 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + 1 ≤ n)
    (hall : neg LAct (allFact (^&ir) (^&ip)) ∈ Γ) (hmr : neg LAct (memFact (^&ir) (^&is)) ∈ Γ)
    (hfst : neg LAct (fstIdxFact (^&ic) (^&id)) ∈ Γ)
    (hfree : neg LAct (freeFact (^&ifp) (^&ip)) ∈ Γ)
    (hsh : neg LAct (setShiftFact (^&iss) (^&is)) ∈ Γ)
    (hins : neg LAct (insFact (^&ic) (^&ifp) (^&iss)) ∈ Γ)
    (hd : neg LAct (derFact (^&id : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id : V) (^&in₁)) ∈ Γ)
    (hle₁ : neg LAct (leFact (^&in₁) (bnum m₁)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (nodeAll W tblN is il ir ip ifp iss ic id in₁ L m₁ n) ∧
    NoDrop' (nodeAll W tblN is il ir ip ifp iss ic id in₁ L m₁ n) ∧
    shiftsV (nodeAll W tblN is il ir ip ifp iss ic id in₁ L m₁ n) = 1 ∧
    len (nodeAll W tblN is il ir ip ifp iss ic id in₁ L m₁ n) = 9 ∧
    neg LAct (goalFact (^&(is + 1)) (bnum n)) ∈
      finalCtx Γ (nodeAll W tblN is il ir ip ifp iss ic id in₁ L m₁ n) := by
  have hil : il + 2 ≤ E := le_trans (add_le_add le_self_add (by norm_num)) hT
  have hin₁ : in₁ + 2 ≤ E := le_trans (add_le_add le_add_self (by norm_num)) hT
  obtain ⟨hok, hnd, hsv, hlen, hfin⟩ := nodeAllHead_ok htbl hF hWp hΓ his hil hir hip hifp hiss hic hid hin₁
    hall hmr hfst hfree hsh hins hd hn₁ hsl
  have hΓ' : IsFormulaSet LAct (finalCtx Γ (nodeAllHead W is il ir ip ifp iss ic id in₁)) :=
    finalCtx_isFormulaSet 8 htbl hΓ hok
  have hl0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hn10 : IsSemiterm LAct 0 (^&in₁ : V) := by simp
  have hbL : IsSemiterm LAct 0 (bnum L) := isSemiterm_bnum_LAct 0 L
  have hbm₁ : IsSemiterm LAct 0 (bnum m₁) := isSemiterm_bnum_LAct 0 m₁
  have tr : ∀ x ∈ Γ, shift LAct x ∈ finalCtx Γ (nodeAllHead W is il ir ip ifp iss ic id in₁) := by
    intro x hx; rw [hfin]; unfold nodeAllHeadCtx; exact shift_mem_head3 hx
  have hle' : neg LAct (leFact (^&(il + 1)) (bnum L)) ∈
      finalCtx Γ (nodeAllHead W is il ir ip ifp iss ic id in₁) := by
    have := tr _ hle
    rwa [shift_neg (isFormula_leFact hl0 hbL), shift_leFact hl0 hbL, termShift_fvar, termShift_bnum] at this
  have hle₁' : neg LAct (leFact (^&(in₁ + 1)) (bnum m₁)) ∈
      finalCtx Γ (nodeAllHead W is il ir ip ifp iss ic id in₁) := by
    have := tr _ hle₁
    rwa [shift_neg (isFormula_leFact hn10 hbm₁), shift_leFact hn10 hbm₁, termShift_fvar, termShift_bnum] at this
  obtain ⟨tok, tnd, tsv, tlen, tfin, tmem⟩ := goalTailUnary_ok' htbl hF hWp htblN hΓ'
    (by rw [show il + 1 + (in₁ + 1) + 5 = il + in₁ + 7 by ring]; exact hT)
    (by rw [add_assoc, one_add_one_eq_two]; exact his) hn hLn hle' hle₁'
    (by rw [hfin]; unfold nodeAllHeadCtx; simp) (by rw [hfin]; unfold nodeAllHeadCtx; simp)
    (by rw [hfin]; unfold nodeAllHeadCtx; simp)
  refine ⟨listOK_appendV hok tok, noDrop'_appendV hnd tnd, ?_, ?_, ?_⟩
  · unfold nodeAll; rw [shiftsV_appendV, hsv, tsv, add_zero]
  · unfold nodeAll; rw [len_appendV, hlen, tlen]; norm_num
  · unfold nodeAll; rw [finalCtx_appendV]; exact tmem

end nodeAll

/-! ## 3. `exsIntro` (`DESIGN_fragments.md` §4.6)

`introExsB “e c pt r d t p s. exsIntroGraph e s p t d → qqExsDef r p → r ∈ s → (isSemiterm).pi 0 t →
fstIdxDef c d → substs1Graph pt t p → insertDef c pt s → derivation d → derivation e”` (declared at
arity 9 with eight names: the last position is an unnamed dummy, instantiated at the literal `𝟎`,
exactly as `introCut` is in `Frag1` §4.4 — hence the cap `M = 9`).

`dlenExsB` charges the WITNESS TERM: `dlen ν = setLen s + termLen t + dlen d + 1`, so the tail is the
BINARY one with `n₁ := &ilt` (the term's length object, bounded by `bnum Lt`) and `n₂ := &(in₁+1)`.
The witness's description (`describeT` + the term `lenSteps`) and the instance's (`certSubst` +
`substsSubsts1`) are the prologue's job; here `tPiFact (cT 0) &it`, `tlenFact &ilt &it` and
`substs1Fact &ipt &it &ip` are hypotheses. -/

section nodeExs

/-- The four node steps of `exsIntro`: `tot_exsIntro`, `fstIdx_exs`, `Intro_exs`, `Dlen_exs`. -/
noncomputable def nodeExsHead (W is il ir ip it ipt ic id ilt in₁ : V) : V :=
  mkStep W 127 ?[^&is, ^&ip, ^&it, ^&id] ∷
  mkStep W 141 ?[^&(is + 1), ^&(ip + 1), ^&(it + 1), ^&(id + 1), ^&0] ∷
  mkStep W 131 ?[(𝟎 : V), ^&(is + 1), ^&(ip + 1), ^&(it + 1), ^&(id + 1), ^&(ir + 1), ^&(ipt + 1), ^&(ic + 1), ^&0] ∷
  mkStep W 134 ?[^&0, ^&(is + 1), ^&(ip + 1), ^&(it + 1), ^&(id + 1), ^&(in₁ + 1), ^&(il + 1), ^&(ilt + 1)] ∷ (0 : V)

/-- **The `exsIntro` node fragment**. -/
noncomputable def nodeExs (W tblN is il ir ip it ipt ic id ilt in₁ L Lt m₁ n : V) : V :=
  appendV (nodeExsHead W is il ir ip it ipt ic id ilt in₁)
    (goalTailBinary W tblN (il + 1) (ilt + 1) (in₁ + 1) L Lt m₁ n (is + 1))

noncomputable def nodeExsHeadCtx (Γ is il ip it id ilt in₁ : V) : V :=
  insert (neg LAct (dlenFact (^&0 : V) (binaryT (il + 1) (ilt + 1) (in₁ + 1))))
    (insert (neg LAct (derFact (^&0 : V)))
      (insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0)))
        (insert (neg LAct (exsIntroFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)) (^&(it + 1)) (^&(id + 1))))
          (setShift LAct Γ))))

theorem nodeExsHead_ok {tbl N E Γ W is il ir ip it ipt ic id ilt in₁ : V} (htbl : TableOK tbl N)
    (hF : Frag2Table tbl) (hWp : W = frag2Pieces) (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hil : il + 2 ≤ E) (hir : ir + 2 ≤ E) (hip : ip + 2 ≤ E) (hit : it + 2 ≤ E)
    (hipt : ipt + 2 ≤ E) (hic : ic + 2 ≤ E) (hid : id + 2 ≤ E) (hilt : ilt + 2 ≤ E) (hin₁ : in₁ + 2 ≤ E)
    (hexs : neg LAct (exsFact (^&ir) (^&ip)) ∈ Γ) (hmr : neg LAct (memFact (^&ir) (^&is)) ∈ Γ)
    (htpi : neg LAct (tPiFact (𝟎 : V) (^&it)) ∈ Γ)
    (hfst : neg LAct (fstIdxFact (^&ic) (^&id)) ∈ Γ)
    (hsub : neg LAct (substs1Fact (^&ipt) (^&it) (^&ip)) ∈ Γ)
    (hins : neg LAct (insFact (^&ic) (^&ipt) (^&is)) ∈ Γ)
    (hd : neg LAct (derFact (^&id : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id : V) (^&in₁)) ∈ Γ)
    (htl : neg LAct (tlenFact (^&ilt) (^&it)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) :
    ListOK tbl E ((9 : ℕ) : V) Γ (nodeExsHead W is il ir ip it ipt ic id ilt in₁) ∧
    NoDrop' (nodeExsHead W is il ir ip it ipt ic id ilt in₁) ∧
    shiftsV (nodeExsHead W is il ir ip it ipt ic id ilt in₁) = 1 ∧
    len (nodeExsHead W is il ir ip it ipt ic id ilt in₁) = 4 ∧
    finalCtx Γ (nodeExsHead W is il ir ip it ipt ic id ilt in₁) = nodeExsHeadCtx Γ is il ip it id ilt in₁ := by
  have h89 : ((8 : ℕ) : V) ≤ ((9 : ℕ) : V) := by exact_mod_cast (by decide : (8 : ℕ) ≤ 9)
  have his0 : IsSemiterm LAct 0 (^&is : V) := by simp
  have hisE : termLen LAct (^&is : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) his)
  have his1 : IsSemiterm LAct 0 (^&(is + 1) : V) := by simp
  have his1E : termLen LAct (^&(is + 1) : V) ≤ E := termLen_fvar_succ_le his
  have hil0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hil1 : IsSemiterm LAct 0 (^&(il + 1) : V) := by simp
  have hil1E : termLen LAct (^&(il + 1) : V) ≤ E := termLen_fvar_succ_le hil
  have hir0 : IsSemiterm LAct 0 (^&ir : V) := by simp
  have hir1 : IsSemiterm LAct 0 (^&(ir + 1) : V) := by simp
  have hir1E : termLen LAct (^&(ir + 1) : V) ≤ E := termLen_fvar_succ_le hir
  have hip0 : IsSemiterm LAct 0 (^&ip : V) := by simp
  have hipE : termLen LAct (^&ip : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hip)
  have hip1 : IsSemiterm LAct 0 (^&(ip + 1) : V) := by simp
  have hip1E : termLen LAct (^&(ip + 1) : V) ≤ E := termLen_fvar_succ_le hip
  have hit0 : IsSemiterm LAct 0 (^&it : V) := by simp
  have hitE : termLen LAct (^&it : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hit)
  have hit1 : IsSemiterm LAct 0 (^&(it + 1) : V) := by simp
  have hit1E : termLen LAct (^&(it + 1) : V) ≤ E := termLen_fvar_succ_le hit
  have hipt0 : IsSemiterm LAct 0 (^&ipt : V) := by simp
  have hipt1 : IsSemiterm LAct 0 (^&(ipt + 1) : V) := by simp
  have hipt1E : termLen LAct (^&(ipt + 1) : V) ≤ E := termLen_fvar_succ_le hipt
  have hic0 : IsSemiterm LAct 0 (^&ic : V) := by simp
  have hic1 : IsSemiterm LAct 0 (^&(ic + 1) : V) := by simp
  have hic1E : termLen LAct (^&(ic + 1) : V) ≤ E := termLen_fvar_succ_le hic
  have hid0 : IsSemiterm LAct 0 (^&id : V) := by simp
  have hidE : termLen LAct (^&id : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hid)
  have hid1 : IsSemiterm LAct 0 (^&(id + 1) : V) := by simp
  have hid1E : termLen LAct (^&(id + 1) : V) ≤ E := termLen_fvar_succ_le hid
  have hilt0 : IsSemiterm LAct 0 (^&ilt : V) := by simp
  have hilt1 : IsSemiterm LAct 0 (^&(ilt + 1) : V) := by simp
  have hilt1E : termLen LAct (^&(ilt + 1) : V) ≤ E := termLen_fvar_succ_le hilt
  have hin₁0 : IsSemiterm LAct 0 (^&in₁ : V) := by simp
  have hin₁1 : IsSemiterm LAct 0 (^&(in₁ + 1) : V) := by simp
  have hin₁1E : termLen LAct (^&(in₁ + 1) : V) ≤ E := termLen_fvar_succ_le hin₁
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hf0E : termLen LAct (^&0 : V) ≤ E :=
    termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) (le_trans le_add_self his))
  have hx0 : IsSemiterm LAct 0 (𝟎 : V) := isSemiterm_qqZero_LAct 0
  have hxE : termLen LAct (𝟎 : V) ≤ E := by
    rw [termLen_qqZero isFunc_LAct_zeroIndex]; exact le_trans (by norm_num) (le_trans le_add_self his)
  -- step 1: tot_exsIntro
  obtain ⟨ok₁, tg₁, cx₁⟩ := gok_totExsIntro htbl hF hWp hΓ his0 hisE hip0 hipE hit0 hitE hid0 hidE
  rw [termShift_fvar, termShift_fvar, termShift_fvar, termShift_fvar, Nat.cast_zero] at cx₁
  set F := neg LAct (exsIntroFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)) (^&(it + 1)) (^&(id + 1))) with hFdef
  set Γ₁ := insert F (setShift LAct Γ) with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := cx₁ ▸ isFormulaSet_ctxAfter 8 htbl ok₁
  have texs : neg LAct (exsFact (^&(ir + 1)) (^&(ip + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hexs
    rwa [shift_neg (isFormula_exsFact hir0 hip0), shift_exsFact hir0 hip0, termShift_fvar, termShift_fvar] at this
  have tmr : neg LAct (memFact (^&(ir + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hmr
    rwa [shift_neg (isFormula_memFact hir0 his0), shift_memFact hir0 his0, termShift_fvar, termShift_fvar] at this
  have ttpi : neg LAct (tPiFact (𝟎 : V) (^&(it + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) htpi
    rwa [shift_neg (isFormula_tPiFact hx0 hit0), shift_tPiFact hx0 hit0,
      termShift_qqZero isFunc_LAct_zeroIndex, termShift_fvar] at this
  have tfst : neg LAct (fstIdxFact (^&(ic + 1)) (^&(id + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hfst
    rwa [shift_neg (isFormula_fstIdxFact hic0 hid0), shift_fstIdxFact hic0 hid0, termShift_fvar, termShift_fvar] at this
  have tsub : neg LAct (substs1Fact (^&(ipt + 1)) (^&(it + 1)) (^&(ip + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hsub
    rwa [shift_neg (isFormula_substs1Fact hipt0 hit0 hip0), shift_substs1Fact hipt0 hit0 hip0,
      termShift_fvar, termShift_fvar, termShift_fvar] at this
  have tins : neg LAct (insFact (^&(ic + 1)) (^&(ipt + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hins
    rwa [shift_neg (isFormula_insFact hic0 hipt0 his0), shift_insFact hic0 hipt0 his0,
      termShift_fvar, termShift_fvar, termShift_fvar] at this
  have td : neg LAct (derFact (^&(id + 1) : V)) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hd
    rwa [shift_neg (isFormula_derFact hid0), shift_derFact hid0, termShift_fvar] at this
  have tn₁ : neg LAct (dlenFact (^&(id + 1) : V) (^&(in₁ + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hn₁
    rwa [shift_neg (isFormula_dlenFact hid0 hin₁0), shift_dlenFact hid0 hin₁0, termShift_fvar, termShift_fvar] at this
  have ttl : neg LAct (tlenFact (^&(ilt + 1)) (^&(it + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) htl
    rwa [shift_neg (isFormula_tlenFact hilt0 hit0), shift_tlenFact hilt0 hit0, termShift_fvar, termShift_fvar] at this
  have tsl : neg LAct (setLenFact (^&(il + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hsl
    rwa [shift_neg (isFormula_setLenFact hil0 his0), shift_setLenFact hil0 his0, termShift_fvar, termShift_fvar] at this
  -- step 2: fstIdx_exs
  obtain ⟨ok₂, tg₂, cx₂⟩ := gok_fstIdxExs htbl hF hWp hΓ₁ his1 his1E hip1 hip1E hit1 hit1E hid1 hid1E hf0 hf0E
    (by rw [hΓ₁def, hFdef]; simp)
  set Γ₂ := insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0))) Γ₁ with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := cx₂ ▸ isFormulaSet_ctxAfter 8 htbl ok₂
  -- step 3: Intro_exs
  obtain ⟨ok₃, tg₃, cx₃⟩ := gok_introExs htbl hF hWp hΓ₂ hx0 hxE his1 his1E hip1 hip1E hit1 hit1E
    hid1 hid1E hir1 hir1E hipt1 hipt1E hic1 hic1E hf0 hf0E
    (by rw [hΓ₂def, hΓ₁def, hFdef]; simp) (by rw [hΓ₂def]; simp [texs]) (by rw [hΓ₂def]; simp [tmr])
    (by rw [hΓ₂def]; simp [ttpi]) (by rw [hΓ₂def]; simp [tfst]) (by rw [hΓ₂def]; simp [tsub])
    (by rw [hΓ₂def]; simp [tins]) (by rw [hΓ₂def]; simp [td])
  set Γ₃ := insert (neg LAct (derFact (^&0 : V))) Γ₂ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := cx₃ ▸ isFormulaSet_ctxAfter 9 htbl ok₃
  -- step 4: Dlen_exs
  obtain ⟨ok₄, tg₄, cx₄⟩ := gok_dlenExs htbl hF hWp hΓ₃ hf0 hf0E his1 his1E hip1 hip1E hit1 hit1E
    hid1 hid1E hin₁1 hin₁1E hil1 hil1E hilt1 hilt1E
    (by rw [hΓ₃def, hΓ₂def, hΓ₁def, hFdef]; simp) (by rw [hΓ₃def, hΓ₂def]; simp [tn₁])
    (by rw [hΓ₃def, hΓ₂def]; simp [tsl]) (by rw [hΓ₃def, hΓ₂def]; simp [ttl])
  have hfin : finalCtx Γ (nodeExsHead W is il ir ip it ipt ic id ilt in₁) =
      nodeExsHeadCtx Γ is il ip it id ilt in₁ := by
    unfold nodeExsHead
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_single, cx₄]
    rfl
  refine ⟨?_, ?_, ?_, ?_, hfin⟩
  · unfold nodeExsHead
    refine listOK_cons (ok₁.mono h89) ?_
    rw [cx₁]
    refine listOK_cons (ok₂.mono h89) ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    exact listOK_single (ok₄.mono h89)
  · unfold nodeExsHead
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp)
      (noDrop'_cons (by rw [tg₃]; simp) (noDrop'_single (by rw [tg₄]; simp))))
  · unfold nodeExsHead
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₃, tg₄]
    simp
  · unfold nodeExsHead; simp [len_adjoin]; norm_num

/-- **`nodeExs` is applicable** (cap `M = 9`: `Intro_exs` has nine witnesses). -/
theorem nodeExs_ok {tbl N E Γ W tblN N' B' is il ir ip it ipt ic id ilt in₁ L Lt m₁ n : V}
    (htbl : TableOK tbl N) (hF : Frag2Table tbl) (hWp : W = frag2Pieces) (htblN : NumTableOK tblN N' B')
    (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hir : ir + 2 ≤ E) (hip : ip + 2 ≤ E) (hit : it + 2 ≤ E)
    (hipt : ipt + 2 ≤ E) (hic : ic + 2 ≤ E) (hid : id + 2 ≤ E)
    (hT : il + ilt + in₁ + 10 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + Lt + m₁ + 1 ≤ n)
    (hexs : neg LAct (exsFact (^&ir) (^&ip)) ∈ Γ) (hmr : neg LAct (memFact (^&ir) (^&is)) ∈ Γ)
    (htpi : neg LAct (tPiFact (𝟎 : V) (^&it)) ∈ Γ)
    (hfst : neg LAct (fstIdxFact (^&ic) (^&id)) ∈ Γ)
    (hsub : neg LAct (substs1Fact (^&ipt) (^&it) (^&ip)) ∈ Γ)
    (hins : neg LAct (insFact (^&ic) (^&ipt) (^&is)) ∈ Γ)
    (hd : neg LAct (derFact (^&id : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id : V) (^&in₁)) ∈ Γ)
    (hle₁ : neg LAct (leFact (^&in₁) (bnum m₁)) ∈ Γ)
    (htl : neg LAct (tlenFact (^&ilt) (^&it)) ∈ Γ) (hlet : neg LAct (leFact (^&ilt) (bnum Lt)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    ListOK tbl E ((9 : ℕ) : V) Γ (nodeExs W tblN is il ir ip it ipt ic id ilt in₁ L Lt m₁ n) ∧
    NoDrop' (nodeExs W tblN is il ir ip it ipt ic id ilt in₁ L Lt m₁ n) ∧
    shiftsV (nodeExs W tblN is il ir ip it ipt ic id ilt in₁ L Lt m₁ n) = 1 ∧
    len (nodeExs W tblN is il ir ip it ipt ic id ilt in₁ L Lt m₁ n) = 9 ∧
    neg LAct (goalFact (^&(is + 1)) (bnum n)) ∈
      finalCtx Γ (nodeExs W tblN is il ir ip it ipt ic id ilt in₁ L Lt m₁ n) := by
  have h89 : ((8 : ℕ) : V) ≤ ((9 : ℕ) : V) := by exact_mod_cast (by decide : (8 : ℕ) ≤ 9)
  have hil : il + 2 ≤ E := le_trans (add_le_add (le_trans le_self_add le_self_add) (by norm_num)) hT
  have hilt : ilt + 2 ≤ E := le_trans (add_le_add (le_trans le_add_self le_self_add) (by norm_num)) hT
  have hin₁ : in₁ + 2 ≤ E := le_trans (add_le_add le_add_self (by norm_num)) hT
  obtain ⟨hok, hnd, hsv, hlen, hfin⟩ := nodeExsHead_ok htbl hF hWp hΓ his hil hir hip hit hipt hic hid hilt hin₁
    hexs hmr htpi hfst hsub hins hd hn₁ htl hsl
  have hΓ' : IsFormulaSet LAct (finalCtx Γ (nodeExsHead W is il ir ip it ipt ic id ilt in₁)) :=
    finalCtx_isFormulaSet 9 htbl hΓ hok
  have hl0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hlt0 : IsSemiterm LAct 0 (^&ilt : V) := by simp
  have hn10 : IsSemiterm LAct 0 (^&in₁ : V) := by simp
  have hbL : IsSemiterm LAct 0 (bnum L) := isSemiterm_bnum_LAct 0 L
  have hbLt : IsSemiterm LAct 0 (bnum Lt) := isSemiterm_bnum_LAct 0 Lt
  have hbm₁ : IsSemiterm LAct 0 (bnum m₁) := isSemiterm_bnum_LAct 0 m₁
  have tr : ∀ x ∈ Γ, shift LAct x ∈ finalCtx Γ (nodeExsHead W is il ir ip it ipt ic id ilt in₁) := by
    intro x hx; rw [hfin]; unfold nodeExsHeadCtx; exact shift_mem_head3 hx
  have hle' : neg LAct (leFact (^&(il + 1)) (bnum L)) ∈
      finalCtx Γ (nodeExsHead W is il ir ip it ipt ic id ilt in₁) := by
    have := tr _ hle
    rwa [shift_neg (isFormula_leFact hl0 hbL), shift_leFact hl0 hbL, termShift_fvar, termShift_bnum] at this
  have hlet' : neg LAct (leFact (^&(ilt + 1)) (bnum Lt)) ∈
      finalCtx Γ (nodeExsHead W is il ir ip it ipt ic id ilt in₁) := by
    have := tr _ hlet
    rwa [shift_neg (isFormula_leFact hlt0 hbLt), shift_leFact hlt0 hbLt, termShift_fvar, termShift_bnum] at this
  have hle₁' : neg LAct (leFact (^&(in₁ + 1)) (bnum m₁)) ∈
      finalCtx Γ (nodeExsHead W is il ir ip it ipt ic id ilt in₁) := by
    have := tr _ hle₁
    rwa [shift_neg (isFormula_leFact hn10 hbm₁), shift_leFact hn10 hbm₁, termShift_fvar, termShift_bnum] at this
  obtain ⟨tok, tnd, tsv, tlen, tfin, tmem⟩ := goalTailBinary_ok' htbl hF hWp htblN hΓ'
    (by rw [show il + 1 + (ilt + 1) + (in₁ + 1) + 7 = il + ilt + in₁ + 10 by ring]; exact hT)
    (by rw [add_assoc, one_add_one_eq_two]; exact his) hn hLn hle' hlet' hle₁'
    (by rw [hfin]; unfold nodeExsHeadCtx; simp) (by rw [hfin]; unfold nodeExsHeadCtx; simp)
    (by rw [hfin]; unfold nodeExsHeadCtx; simp)
  refine ⟨listOK_appendV hok (tok.mono h89), noDrop'_appendV hnd tnd, ?_, ?_, ?_⟩
  · unfold nodeExs; rw [shiftsV_appendV, hsv, tsv, add_zero]
  · unfold nodeExs; rw [len_appendV, hlen, tlen]; norm_num
  · unfold nodeExs; rw [finalCtx_appendV]; exact tmem

end nodeExs

/-! ## 4. `axm` (`DESIGN_fragments.md` §4.10)

A LEAF: `introAxmB “e p s. (isFormulaSet).pi s → p ∈ s → (Theory.Δ₁ch TAct).sigma p → axmGraph e s p →
derivation e”` and `dlen ν = setLen s + 1`, so the leaf tail.

**The recognizer is a hypothesis.** `DESIGN_fragments` §4.10 splits the third antecedent into two
cases the constructor decides at the V level — (i) a standard axiom, pinned against the closed shape
facts of `⌜σ⌝` by `axiomRec σ`, and (ii) an induction instance, via `indRec` and the ℒₒᵣ/LAct bridge
chain of `Lib/Bridge.lean`. BOTH chains run `pinSteps`/`certShift`/`certSubst`, i.e. `Cert`'s
producers, which do not exist yet. `nodeAxm` therefore assumes `neg (axchFact &ip) ∈ Γ` outright:
when the recognizer producer lands it will discharge exactly this hypothesis, and nothing else about
this fragment changes. -/

section nodeAxm

/-- The four node steps of `axm`: `tot_axm`, `fstIdx_axm`, `Intro_axm`, `Dlen_axm`. -/
noncomputable def nodeAxmHead (W is il ip : V) : V :=
  mkStep W 129 ?[^&is, ^&ip] ∷ mkStep W 143 ?[^&(is + 1), ^&(ip + 1), ^&0] ∷
  mkStep W 137 ?[^&(is + 1), ^&(ip + 1), ^&0] ∷
  mkStep W 136 ?[^&0, ^&(is + 1), ^&(ip + 1), ^&(il + 1)] ∷ (0 : V)

/-- **The `axm` fragment**: the head, then the leaf tail closing `goalFact &(is+1) (bnum n)`. -/
noncomputable def nodeAxm (W tblN is il ip L n : V) : V :=
  appendV (nodeAxmHead W is il ip) (goalTailLeaf W tblN (il + 1) L n (is + 1))

noncomputable def nodeAxmHeadCtx (Γ is il ip : V) : V :=
  insert (neg LAct (dlenFact (^&0 : V) (leafT (il + 1))))
    (insert (neg LAct (derFact (^&0 : V)))
      (insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0)))
        (insert (neg LAct (axmFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)))) (setShift LAct Γ))))

theorem nodeAxmHead_ok {tbl N E Γ W is il ip : V} (htbl : TableOK tbl N)
    (hF : Frag2Table tbl) (hWp : W = frag2Pieces) (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hil : il + 2 ≤ E) (hip : ip + 2 ≤ E)
    (hfs : neg LAct (fsetPiFact (^&is)) ∈ Γ) (hmp : neg LAct (memFact (^&ip) (^&is)) ∈ Γ)
    (hax : neg LAct (axchFact (^&ip)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (nodeAxmHead W is il ip) ∧ NoDrop' (nodeAxmHead W is il ip) ∧
    shiftsV (nodeAxmHead W is il ip) = 1 ∧ len (nodeAxmHead W is il ip) = 4 ∧
    finalCtx Γ (nodeAxmHead W is il ip) = nodeAxmHeadCtx Γ is il ip := by
  have his0 : IsSemiterm LAct 0 (^&is : V) := by simp
  have hisE : termLen LAct (^&is : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) his)
  have his1 : IsSemiterm LAct 0 (^&(is + 1) : V) := by simp
  have his1E : termLen LAct (^&(is + 1) : V) ≤ E := termLen_fvar_succ_le his
  have hil0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hil1 : IsSemiterm LAct 0 (^&(il + 1) : V) := by simp
  have hil1E : termLen LAct (^&(il + 1) : V) ≤ E := termLen_fvar_succ_le hil
  have hip0 : IsSemiterm LAct 0 (^&ip : V) := by simp
  have hipE : termLen LAct (^&ip : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hip)
  have hip1 : IsSemiterm LAct 0 (^&(ip + 1) : V) := by simp
  have hip1E : termLen LAct (^&(ip + 1) : V) ≤ E := termLen_fvar_succ_le hip
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hf0E : termLen LAct (^&0 : V) ≤ E :=
    termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) (le_trans le_add_self his))
  -- step 1: tot_axm
  obtain ⟨ok₁, tg₁, cx₁⟩ := gok_totAxm htbl hF hWp hΓ his0 hisE hip0 hipE
  rw [termShift_fvar, termShift_fvar, Nat.cast_zero] at cx₁
  set F := neg LAct (axmFact (^&0 : V) (^&(is + 1)) (^&(ip + 1))) with hFdef
  set Γ₁ := insert F (setShift LAct Γ) with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := cx₁ ▸ isFormulaSet_ctxAfter 8 htbl ok₁
  have tfs : neg LAct (fsetPiFact (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hfs
    rwa [shift_neg (isFormula_fsetPiFact his0), shift_fsetPiFact his0, termShift_fvar] at this
  have tmp : neg LAct (memFact (^&(ip + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hmp
    rwa [shift_neg (isFormula_memFact hip0 his0), shift_memFact hip0 his0, termShift_fvar, termShift_fvar] at this
  have tax : neg LAct (axchFact (^&(ip + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hax
    rwa [shift_neg (isFormula_axchFact hip0), shift_axchFact hip0, termShift_fvar] at this
  have tsl : neg LAct (setLenFact (^&(il + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hsl
    rwa [shift_neg (isFormula_setLenFact hil0 his0), shift_setLenFact hil0 his0, termShift_fvar, termShift_fvar] at this
  -- step 2: fstIdx_axm
  obtain ⟨ok₂, tg₂, cx₂⟩ := gok_fstIdxAxm htbl hF hWp hΓ₁ his1 his1E hip1 hip1E hf0 hf0E
    (by rw [hΓ₁def, hFdef]; simp)
  set Γ₂ := insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0))) Γ₁ with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := cx₂ ▸ isFormulaSet_ctxAfter 8 htbl ok₂
  -- step 3: Intro_axm
  obtain ⟨ok₃, tg₃, cx₃⟩ := gok_introAxm htbl hF hWp hΓ₂ his1 his1E hip1 hip1E hf0 hf0E
    (by rw [hΓ₂def]; simp [tfs]) (by rw [hΓ₂def]; simp [tmp]) (by rw [hΓ₂def]; simp [tax])
    (by rw [hΓ₂def, hΓ₁def, hFdef]; simp)
  set Γ₃ := insert (neg LAct (derFact (^&0 : V))) Γ₂ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := cx₃ ▸ isFormulaSet_ctxAfter 8 htbl ok₃
  -- step 4: Dlen_axm
  obtain ⟨ok₄, tg₄, cx₄⟩ := gok_dlenAxm htbl hF hWp hΓ₃ hf0 hf0E his1 his1E hip1 hip1E hil1 hil1E
    (by rw [hΓ₃def, hΓ₂def, hΓ₁def, hFdef]; simp) (by rw [hΓ₃def, hΓ₂def]; simp [tsl])
  have hfin : finalCtx Γ (nodeAxmHead W is il ip) = nodeAxmHeadCtx Γ is il ip := by
    unfold nodeAxmHead
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_single, cx₄]
    rfl
  refine ⟨?_, ?_, ?_, ?_, hfin⟩
  · unfold nodeAxmHead
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    exact listOK_single ok₄
  · unfold nodeAxmHead
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp)
      (noDrop'_cons (by rw [tg₃]; simp) (noDrop'_single (by rw [tg₄]; simp))))
  · unfold nodeAxmHead
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₃, tg₄]
    simp
  · unfold nodeAxmHead; simp [len_adjoin]; norm_num

/-- **`nodeAxm` is applicable** (the recognizer fact `axchFact &ip` is a layout hypothesis). -/
theorem nodeAxm_ok {tbl N E Γ W tblN N' B' is il ip L n : V}
    (htbl : TableOK tbl N) (hF : Frag2Table tbl) (hWp : W = frag2Pieces) (htblN : NumTableOK tblN N' B')
    (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hil : il + 4 ≤ E) (hip : ip + 2 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + 1 ≤ n)
    (hfs : neg LAct (fsetPiFact (^&is)) ∈ Γ) (hmp : neg LAct (memFact (^&ip) (^&is)) ∈ Γ)
    (hax : neg LAct (axchFact (^&ip)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (nodeAxm W tblN is il ip L n) ∧ NoDrop' (nodeAxm W tblN is il ip L n) ∧
    shiftsV (nodeAxm W tblN is il ip L n) = 1 ∧ len (nodeAxm W tblN is il ip L n) = 9 ∧
    neg LAct (goalFact (^&(is + 1)) (bnum n)) ∈ finalCtx Γ (nodeAxm W tblN is il ip L n) := by
  have hil2 : il + 2 ≤ E := le_trans (by gcongr; norm_num) hil
  obtain ⟨hok, hnd, hsv, hlen, hfin⟩ := nodeAxmHead_ok htbl hF hWp hΓ his hil2 hip hfs hmp hax hsl
  have hΓ' : IsFormulaSet LAct (finalCtx Γ (nodeAxmHead W is il ip)) := finalCtx_isFormulaSet 8 htbl hΓ hok
  have hl0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hbL : IsSemiterm LAct 0 (bnum L) := isSemiterm_bnum_LAct 0 L
  have hle' : neg LAct (leFact (^&(il + 1)) (bnum L)) ∈ finalCtx Γ (nodeAxmHead W is il ip) := by
    rw [hfin]; unfold nodeAxmHeadCtx
    have := shift_mem_head3 (a := neg LAct (dlenFact (^&0 : V) (leafT (il + 1))))
      (b := neg LAct (derFact (^&0 : V))) (c := neg LAct (fstIdxFact (^&(is + 1)) (^&0)))
      (f := neg LAct (axmFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)))) hle
    rwa [shift_neg (isFormula_leFact hl0 hbL), shift_leFact hl0 hbL, termShift_fvar, termShift_bnum] at this
  obtain ⟨tok, tnd, tsv, tlen, tfin, tmem⟩ := goalTailLeaf_ok' htbl hF hWp htblN hΓ'
    (by rw [show il + 1 + 3 = il + 4 by ring]; exact hil) (by rw [add_assoc, one_add_one_eq_two]; exact his)
    hn hLn hle' (by rw [hfin]; unfold nodeAxmHeadCtx; simp) (by rw [hfin]; unfold nodeAxmHeadCtx; simp)
    (by rw [hfin]; unfold nodeAxmHeadCtx; simp)
  refine ⟨listOK_appendV hok tok, noDrop'_appendV hnd tnd, ?_, ?_, ?_⟩
  · unfold nodeAxm; rw [shiftsV_appendV, hsv, tsv, add_zero]
  · unfold nodeAxm; rw [len_appendV, hlen, tlen]; norm_num
  · unfold nodeAxm; rw [finalCtx_appendV]; exact tmem

end nodeAxm

end ArithS
