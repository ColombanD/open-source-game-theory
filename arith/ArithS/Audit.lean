import ArithS.Agent
import ArithS.AgentConverse
import ArithS.Core.Sound
import ArithS.Cut
import ArithS.CutV
import ArithS.ProperV
import ArithS.InstV
import ArithS.NumeralFacts
import ArithS.Diag
import ArithS.Det
import ArithS.FitBox
import ArithS.Inst
import ArithS.Instance
import ArithS.InstanceV
import ArithS.Transparency
import ArithS.Assembly.Prep
import ArithS.Assembly.Uniform
import ArithS.Assembly.Cell
import ArithS.Necessitation.Primitives
import ArithS.Necessitation.ShiftLen
import ArithS.Necessitation.Lib.Sets
import ArithS.Necessitation.Lib.Formulas
import ArithS.Necessitation.Lib.Lengths
import ArithS.Necessitation.Lib.Nodes
import ArithS.Necessitation.Lib.Bridge
import ArithS.Necessitation.Steps
import ArithS.Necessitation.Lib.Walk
import ArithS.Necessitation.Lib.Occ
import ArithS.Necessitation.Lib.Frag
import ArithS.Necessitation.WalkLemmas
import ArithS.Necessitation.RowInst
import ArithS.Necessitation.RowInstB
import ArithS.Necessitation.Chain
import ArithS.Necessitation.ChainOcc
import ArithS.Necessitation.Describe
import ArithS.Necessitation.Layout
import ArithS.Necessitation.Members
import ArithS.Necessitation.NumSteps
import ArithS.Necessitation.NumLength
import ArithS.Necessitation.NumMul
import ArithS.Necessitation.Cert
import ArithS.Necessitation.Dossier
import ArithS.Necessitation.Frag1
import ArithS.Necessitation.Frag2
import ArithS.Necessitation.Verify
import ArithS.Necessitation.Top
import ArithS.Necessitation.Prologue

/-!
# ArithS.Audit — the axiom census of the arithmetized layer

Every headline theorem of tiers T1 and T2, with `#print axioms`. Building this module (it is
the last import of `ArithS.lean`) prints the census; each line must read
`[propext, Classical.choice, Quot.sound]` — Lean's three standard axioms and nothing else.
The `example`s below FAIL TO COMPILE if any of these theorems disappears or changes its name,
so the census is also a freshness check for the paper's claims.
-/

namespace ArithS

-- T1: the red cell, at every shared budget, fuel 2; and its non-vacuity.
example : ∀ k : ℕ, EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 1 ∧ EvalGraph 2 (Cupod k) (Dupoc k) (Cupod k) 0 :=
  red_cell
#print axioms red_cell
#print axioms red_cell_unique
#print axioms guard_fits
#print axioms guard_fits'

-- τ-closure of TAct at every proof length (the engine's `Pf.transpose`, on codes).
#print axioms lenProvable_fbound_swap_iff
#print axioms swapcode_swapcode
#print axioms swapcode_psubst

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

-- M4, U1 + U3 (InstV): the bnum-instance operator `instB` (Σ₁ graph, code equation, length
-- `|instB n k| ≤ |n|·|bnum k|`), the parametric box `bewB` (Σ₁), and Quantifier Distribution
-- on codes with dlen accounting (`N + 5|χ[bnum k]| + 3|χ| + |bnum k| + 7`) — V-generic, its
-- meta twin at ℕ (the final PBLT step), and as ONE ℒₒᵣ-sentence proved by IΣ₁/PA/TAct.
#print axioms instB.defined
#print axioms quote_instB
#print axioms formulaLen_instB_le
#print axioms bewB.defined
#print axioms lenDerivable_inst_V
#print axioms lenDerivable_instB_V
#print axioms lenDerivable_instB_V'
#print axioms lenProvable_inst
#print axioms lenProvable_inst_size
#print axioms pa_proves_instSentence
#print axioms tact_proves_instSentence

-- M4, U9 step 2 (NumeralFacts): short TAct proofs of the antecedent `numeral c ≤ bnumT k` —
-- bit recursion on the binary numeral (two uniform PA lemmas cut in once per bit, base range
-- by completeness), length `C₀ + C₁·size k·size k`; the strict twin; the instance shape
-- (`(leF ↑c #0 🡒 ψ) ⇜ ![t] = leF ↑c t 🡒 ψ ⇜ ![t]`) and `lMap emb ↑c = ↑c`.
#print axioms lenProvable_of_provable
#print axioms lMap_emb_numeral
#print axioms substs_leF_imp
#print axioms tact_proves_leEvenA
#print axioms tact_proves_le_bnumT
#print axioms step_le
#print axioms lenProvable_le_bnumT
#print axioms lenProvable_lt_bnumT

-- M4, U6 (Diag): the parametric diagonal lemma over TAct for LAct formulas — Foundation's
-- construction transported along the reduct (`substNumeralParamsA` twin of `substNumeralParams`,
-- `tactFixedpoint`), through completeness with equality (`𝗘𝗤 LAct ⪯ TAct`, `tact_complete`);
-- the instances at `bnum k` (∀-elimination), their truth in every model and their internal
-- provability (D1).
#print axioms eqAxiom_weakerThan_TAct
#print axioms tact_complete
#print axioms tact_complete'
#print axioms substNumeralParamsA_app_quote
#print axioms tact_parametric_diagonal₁
#print axioms tact_parametric_diagonal
#print axioms tact_parametric_diagonal_inst
#print axioms models_tact_parametric_diagonal_inst
#print axioms provable_code_parametric_diagonal_inst

-- U0b (TheoryAct, 2026-09-12): the action axiom `axAct : (c_C = 0 ∧ c_D = 1) ∨ (c_C = 1 ∧ c_D = 0)`
-- — TAct proves it, its model class is exactly the two standard readings (`stdActS`/`swapActS`),
-- and ℕ satisfies it. Without it no guard sentence was TAct-provable (a vacuity).
#print axioms tact_proves_axAct
#print axioms models_axAct_iff
#print axioms eval_axAct_iff
#print axioms structure_eq_of_axAct
#print axioms models_axAct
#print axioms lMap_swap_axAct

-- M4 U0 — programs described by TERMS over the polynomial pairing: Dupoc's guard sentence
-- against itself is the `k`-instance `q ⇜ ![k̂]` of ONE fixed one-variable formula (meta), and on
-- codes `subst (bnum k ∷ 0) cq` (Critch's "source with `k` written in binary"); the description
-- of a program denotes its code (`val_progTT`) and codes are what the guard names (`quote_progTT`).
#print axioms exists_dupoc_instance
#print axioms exists_dupoc_instance_code
#print axioms exists_dupoc_instance_code_V
#print axioms quote_progTT
#print axioms val_progTT
#print axioms size_le_tlen_progTT

-- M4 U7 — Dupoc transparency (Critch's step 0) in EVERY model of IΣ₁, at every (possibly
-- nonstandard) budget `k : V`, in the `LAct`-structure `stdActV V` (`c_C ↦ 0`, `c_D ↦ 1`): the
-- description term denotes the canonical code, the truth equation of `qDupoc` ("Dupoc plays C
-- against itself"), the search clause at fuel 2, the Löb premise `bewB k ⌜qDupoc⌝ k → qDupoc(k)`
-- under `ProperV V TAct` (unconditional at ℕ), and the uniform ℒₒᵣ-sentence with the Δ₁ box,
-- provable in IΣ₁/PA (completeness) and in TAct along `emb`.
#print axioms val_TD_V
#print axioms eval_qDupoc_iff_V
#print axioms dupoc_search_V
#print axioms dupoc_search_instB_V
#print axioms dupoc_loeb_premise_V
#print axioms dupoc_loeb_premise_nat
#print axioms dupoc_loeb_premise_guardSentence
#print axioms dupoc_loeb_premise_evalGraph
#print axioms isigma1_proves_dupocPremise
#print axioms pa_proves_dupocPremise
#print axioms tact_proves_dupocPremise

-- M4 assembly prep (Assembly/Prep, 2026-09-12): Cupod's instance equation on codes and search
-- clause in every model; the truth equations in BOTH readings (`swapActS` pulled back to
-- `stdActS`); the conjunction family `pConj = qDupoc ⋏ qCupod` with `instB` distributing over
-- the code connectives and ∧-elimination on codes with dlen accounting (`a + 8(|x|+|y|) + 7`),
-- so a box of the `k`-instance of `pConj` makes BOTH searchers find their guards; the box
-- formula `Box_g` (`g k = ‖k‖³`) with its semantics, `θ` (`#0` = code slot, `#1` = budget) and
-- the fixed point `psi` with `TAct ⊢ ∀¹ (psi 🡘 (Box_g psi 🡒 pConj))`; Σ₁ upward transfer of a
-- bounded proof code from ℕ to every model, and a length for every `TAct`-theorem.
#print axioms guardCode_CupodV_eq_instB
#print axioms cupod_search_V
#print axioms eval_qCupod_iff_V
#print axioms eval_swapActS
#print axioms eval_qDupoc_swap_iff_V
#print axioms eval_qCupod_swap_iff_V
#print axioms instB_quote_pConj
#print axioms instB_imp
#print axioms lenDerivable_andL_V_sharp
#print axioms lenDerivable_andR_V_sharp
#print axioms lenDerivable_andL_V
#print axioms lenDerivable_andR_V
#print axioms pconj_both_V
#print axioms eval_pConj_iff_std
#print axioms eval_pConj_iff_swap
#print axioms gBudget.defined
#print axioms eval_Box_g_iff
#print axioms theta_subst_code
#print axioms psi_fixed_point
#print axioms models_psi_fixed_point
#print axioms lenDerivable_of_nat
#print axioms lenDerivable_of_proof
#print axioms exists_lenDerivable_V_of_proof

-- M4 U8 — the uniform PBLT chain (Assembly/Uniform, 2026-09-12), conditional on
-- `BoundedInnerNec d` (a per-χ constant, polynomial expansion `C_χ·(g(k)^d + 1)`):
-- `|bnum k| ≤ 6‖k‖ + 1` in every model; polynomials in the bit length are
-- eventually below `k` in EVERY model (standard threshold, nonstandard `k` included); the two
-- standard readings are models of `TAct`; the forward direction of the fixed point with a
-- length, instantiated; the chain (cut, necessitation, cut, ∧-elimination) with its budget
-- `chainBound ≤ C·‖k‖^{3d+3}`; `psi(k)` true in both readings for all large `k`; and
-- `TAct ⊢ ∀ k, (k̂ ≤ k → psi(k))`.
#print axioms termLen_bnum_le_V
#print axioms poly_size_le_eventually
#print axioms stdActS_models_TAct
#print axioms swapActS_models_TAct
#print axioms psi_forward
#print axioms forward_inst_V
#print axioms chain_core_V
#print axioms chain_V
#print axioms chain_guard_V
#print axioms chainBound_poly
#print axioms psi_true_V
#print axioms pblt_uniform

-- M4 U9 — the Löbian cell at ℕ (Assembly/Cell, 2026-09-12), conditional on `BoundedInnerNec d`:
-- `‖·‖ = Nat.size` at ℕ; the meta closure `LenProvable fbound (K₀ + K₁·size k + K₂·size k²) TAct
-- ⌜psi ⇜ ![bnumT k]⌝` (the uniform theorem instantiated, its antecedent cut away by
-- NumeralFacts); below the cube budget; and the cell: for all large `k`, `Dupoc k` cooperates
-- with itself and `Cupod k` defects against itself (fuel 2), and both FIND their guards
-- (`LenProvableV TAct k (guard)`) — Critch's Theorem 3.7 in PA-S.
#print axioms size_eq_length
#print axioms exists_psi_instance_length
#print axioms cell_core
#print axioms dupoc_self_coop
#print axioms dupoc_finds_guard

-- T2-CORE: the modal-propositional core is sound over PA (budget erased).
#print axioms Core.Pf_core_sound

-- T2-NEG: no budget-keeping transfer at any inflation.
#print axioms no_budget_keeping_transfer

-- T2-AGENT: engine certificates are arith evaluator runs, same budgets.
#print axioms playsProof_evalGraph
#print axioms playsProof_evalGraph_searchFree
#print axioms atomProvable_evalGraph
#print axioms models_trAt_plays

-- T2-AGENT converse: eval ↔ EvalGraph on modest programs under the two-sided oracle.
#print axioms eval_of_evalGraph
#print axioms evalGraph_of_eval
#print axioms eval_iff_evalGraph
#print axioms play_iff_evalGraph
#print axioms outcome_iff_evalGraph
#print axioms playsProof_evalGraph_of_guardAgree
#print axioms plays_interp_iff
#print axioms GuardAgree.toF

-- Instantiation `c_C ↦ 0, c_D ↦ 1`: PA proves the atom sentences of modest plays
-- (Σ₁-completeness); the `atom`/`atomBoxImpl` leaves of T2-CORE discharged at `Aι`.
#print axioms LAct.models_inst
#print axioms hierarchy_lMap_inst_trAt_plays
#print axioms pa_proves_trAt_inst
#print axioms pa_proves_trAt_inst_of_atomProvable
#print axioms pa_proves_trAt_inst_searchFree
#print axioms leaf_atom_sound
#print axioms leaf_atom_sound_searchFree
#print axioms leaf_atomBoxImpl_sound
#print axioms transfer_of_leaves

-- Code translation: substitution code equations and τ on the search-bot fragment.
#print axioms pcode_subst
#print axioms tcode_subst
#print axioms swapcode_pcode

-- Det: determinism in every model of IΣ₁; the negative atom; the atomNeg leaf of T2-CORE.
#print axioms EvalGraph.unique_V'
#print axioms models_trAt_plays_V
#print axioms pa_proves_neg_trAt_inst
#print axioms leaf_atomNeg_sound
#print axioms leaf_atomNeg_sound_searchFree

-- FitBox: Critch's (b) for box-carrying guards — the positive budget-linear bound and the
-- obstruction: under Cantor pairing a searcher whose guard names its own budget cannot fit.
#print axioms size_bnum_ge
#print axioms exists_flen_tmpl_const
#print axioms box_guard_never_fits
#print axioms legibleBot_guard_never_fits

-- U10 (Necessitation/Primitives, 2026-09-12): the two moves of the verification proof on
-- derivation codes with dlen accounting, V-generic, any Δ₁ theory. `useLemmaCode` (cut on a
-- stored `∀^m B`, the `exsIntro` chain at the witnesses; `dlen ≤ dlen dΛ + dlen d + (m+3)|Γ| + |Λ|
-- + (m+1)²·F + m·E + m + 3`, `F ≥ |B|·E + m`, every witness `≤ E`; `instOuter` is ONE simultaneous
-- substitution so `|B[ē]| ≤ |B|·E`), `elimExistsCode` (cut on `∃P` against `allIntro` with the fresh
-- eigenvariable; `dlen ≤ dlen D + dlen d + 3|Γ| + |setShift Γ| + 6|P| + 8`, and `≤ … + 5|Γ| + …`
-- via `setLen (setShift Γ) ≤ 2|Γ|` — the unary free-variable cost), `wkDropCode`.
#print axioms qqAlls_natCast
#print axioms formulaLen_instOuter_le
#print axioms exsChainCode_proof
#print axioms dlen_exsChainCode_le
#print axioms useLemmaCode_proof
#print axioms dlen_useLemmaCode
#print axioms dlen_useLemmaCode_le
#print axioms dlen_useLemmaCode_le'
#print axioms formulaLen_shift_le
#print axioms setLen_setShift_le
#print axioms elimExistsCode_proof
#print axioms dlen_elimExistsCode
#print axioms dlen_elimExistsCode_le
#print axioms dlen_elimExistsCode_le'
#print axioms wkDropCode_proof
#print axioms dlen_wkDropCode_le


-- U10 (Necessitation/Lib, 2026-09-12): the library rows A of the verification proof — the
-- `totality`, `sets`, `formulas`, `lengths` lemma-sentences of DESIGN §3.1, each an ℒₒᵣ-sentence
-- in prenex universal form over the target's own Σ₁/Δ₁ graphs, true in every model of IΣ₁,
-- hence a PA-theorem (`complete`) and a `Lib` sentence: a TAct-proof code of ONE standard
-- length in every model (`Lib.of_pa` = `tact_proves_lMap_emb` + `lenDerivable_of_proof` +
-- `lenDerivable_of_nat`); `quote_alls`/`Lib.univ_code` give the code `qqAlls ⌜B⌝ m` a
-- fragment instantiates. Sets 26 rows, Formulas 84, Lengths 35 (a representative dozen here).
#print axioms Lib.of_pa
#print axioms quote_alls
#print axioms Lib.univ_code
#print axioms lib_insertSubset
#print axioms lib_isFormulaSetInsert
#print axioms lib_memSetShiftInv
#print axioms lib_qqAndTotal
#print axioms lib_isSemiformulaSubst
#print axioms lib_negAnd
#print axioms lib_substsAll
#print axioms lib_shiftInvAnd
#print axioms lib_substsInvAll
#print axioms lib_setLenInsertLe
#print axioms lib_formulaLenAnd
#print axioms lib_bnumEven
#print axioms lib_twoMulOneAddOne
#print axioms lib_addLeAdd


-- U10 (Necessitation/Lib/Nodes, 2026-09-12): the node rows of the library — the ten
-- `Intro_tag` clauses of the derivation fixpoint (`Derivation.axL … axm` on codes, over
-- `!(derivation TAct).sigma`), the ten `Dlen_tag` clauses (`DlenGraph.*_iff` over
-- `!(dlenGraphDef LAct).sigma`), the ten node-graph totalities, the polarity bridges, and the
-- axiom recognizer: `axiomRec σ` for every `σ ∈ TAct` (i) and the induction scheme as ONE
-- universal sentence `indRec` (ii, the shape Foundation's `InductionR`/`chUniv` forces).
#print axioms lib_introAxL
#print axioms lib_introVerum
#print axioms lib_introAnd
#print axioms lib_introOr
#print axioms lib_introAll
#print axioms lib_introExs
#print axioms lib_introWk
#print axioms lib_introShift
#print axioms lib_introCut
#print axioms lib_introAxm
#print axioms lib_dlenAxL
#print axioms lib_dlenVerum
#print axioms lib_dlenAnd
#print axioms lib_dlenOr
#print axioms lib_dlenAll
#print axioms lib_dlenExs
#print axioms lib_dlenWk
#print axioms lib_dlenShift
#print axioms lib_dlenCut
#print axioms lib_dlenAxm
#print axioms lib_totAndIntro
#print axioms lib_derivationPiSigma
#print axioms lib_axiomRec_axAct
#print axioms lib_axiomRec_pa
#print axioms lib_indRec


-- U10 (Necessitation/Lib/Bridge, 2026-09-12): the ℒₒᵣ/LAct code bridges for the axiom
-- recognizer — language invariance of the code operations on ℒₒᵣ-codes (`subst_LAct_eq`,
-- `bv_LAct_eq`), the ℒₒᵣ → LAct lifts, the ℒₒᵣ formation rows, the graph bridges LAct → ℒₒᵣ,
-- `indBodyIntro` (the induction body from its constituents), and `axIsFormula`.
#print axioms subst_LAct_eq
#print axioms bv_LAct_eq
#print axioms lib_isSemiformulaLActOfLOR
#print axioms lib_isSemiformulaRelOR
#print axioms lib_fvarVecSemitermVecOR
#print axioms lib_indSubstConst0VecOR
#print axioms lib_substsGraphOROfLAct
#print axioms lib_bvGraphOROfLAct
#print axioms lib_indBodyIntro
#print axioms lib_isSemiformulaSigmaPiOR
#print axioms lib_axIsFormula

-- U10 (Necessitation/Steps, 2026-09-12): the three STEPS of the fragment protocol on derivation
-- codes — `useHornCode` (a Horn row whose antecedents are in context), `useHornAndCode` (a
-- conjunctive conclusion, both conjuncts delivered), `introFactCode` (a totality row, the witness
-- as the fresh eigenvariable `&0`), the leaves `axLFactCode`/`wkToCode`, each with its exact
-- `dlen` bound; the instantiation theorem `instOuterAt_subst` (a row instance is ONE simultaneous
-- substitution, so row pieces match canonical fact codes syntactically); and the smoke test
-- `describeAndCode` (rows `qqAndTotal`, `isSemiformulaAnd`, `isSemiformulaSigmaPi`).
#print axioms hornClose_proof
#print axioms dlen_hornClose_le
#print axioms useHornCode_proof
#print axioms dlen_useHornCode_le
#print axioms splitAndCode_proof
#print axioms dlen_splitAndCode_le
#print axioms useHornAndCode_proof
#print axioms dlen_useHornAndCode_le
#print axioms introFactCode_proof
#print axioms dlen_introFactCode_le
#print axioms axLFactCode_proof
#print axioms dlen_axLFactCode
#print axioms wkToCode_proof
#print axioms dlen_wkToCode
#print axioms instOuterAt_subst
#print axioms quote_lMap_emb_subst
#print axioms describeAndCode_proof
#print axioms dlen_describeAndCode_le
#print axioms describeAndCode_exists

-- U10 (Necessitation/ShiftLen, 2026-09-12): free-variable occurrence counts `fvOcc/fvOccF/fvOccS`
-- (Σ₁, the recursion schemes of the lengths) and the ADDITIVE shift laws — `termLen (termShift t) =
-- termLen t + fvOcc t`, `formulaLen (shift p) = formulaLen p + fvOccF p`, `setLen (setShift s) ≤
-- setLen s + fvOccS s`, the counts invariant under shift — so `n` shifts cost `n·fvOccS s`
-- (`setLen_setShiftIter_le`), not `2ⁿ·setLen s`; `dlen_elimExistsCode_le_occ` restates the
-- elimExists bound with `4|Γ| + fvOccS Γ` in place of `5|Γ|`.
#print axioms termLen_termShift_eq
#print axioms fvOcc_termShift
#print axioms formulaLen_shift_eq
#print axioms fvOccF_shift
#print axioms fvOccF_neg
#print axioms fvOccF_free_le
#print axioms fvOcc_le_termLen
#print axioms fvOccF_le_formulaLen
#print axioms fvOccS_le_setLen
#print axioms setLen_setShift_le_occ
#print axioms fvOccS_setShift_le
#print axioms setLen_setShiftIter_le
#print axioms dlen_elimExistsCode_le_occ

-- U10 (Necessitation/Steps + ChainOcc, 2026-09-13): the Horn-closing sub-bound of `introFactCode`
-- extracted, `dlen_introFactCode_le_occ` (the `(m + 2j + 10)|Γ|` of `dlen_introFactCode_le` becomes
-- `(m + 2j + 9)|Γ| + fvOccS Γ`, via `dlen_elimExistsCode_le_occ`), and the per-step bound
-- `dlen_applyStep_le_occ` with `stepCostOcc` (tags 2 and 3 charged additively; `introCostOcc ≤ introCost`).
#print axioms dlen_introFactCode_horn_le
#print axioms dlen_introFactCode_le_occ
#print axioms introCostOcc_le_introCost
#print axioms dlen_applyStep_le_occ

-- U10 (Necessitation/Lib/Walk + WalkLemmas, 2026-09-12): the formula walk's library gaps
-- (`DESIGN_describe.md` §10) — the `<` chain rows `zeroLtSucc`/`succLtSucc` on chain numerals, one
-- CLOSED row per `LAct` symbol (`isRelConst_eq/lt`, `isFuncConst_zero/one/add/mul/cC/cD`, arity and
-- code as `0 + 1 + ⋯ + 1`), the vector rows `isUTermVecOfSemitermVecLAct`/`isSemitermVecQVec`, the
-- bridge `substs1Substs`; the chain numeral `cTV` (Σ₁ by primitive recursion, `termLen = 2n + 1`,
-- fixed by shift/subst, no free variables) with `quote_cTT : ⌜0 + 1 + ⋯ + 1⌝ = cT n`; `bvOcc`/`bvOccF`
-- and the substitution occurrence bound `fvOccF (subst w p) ≤ fvOccF p + bvOccF p · M`, hence
-- `fvOccF (free p) ≤ fvOccF p + bvOccF p`; row instantiation at any width
-- (`instOuterAt_subst_bvList`); iterated `free` (`free_exsIter`, `freeIter_subst_listToVec`).
#print axioms lib_zeroLtSucc
#print axioms lib_succLtSucc
#print axioms lib_isRelConst_eq
#print axioms lib_isRelConst_lt
#print axioms lib_isFuncConst_zero
#print axioms lib_isFuncConst_one
#print axioms lib_isFuncConst_add
#print axioms lib_isFuncConst_mul
#print axioms lib_isFuncConst_cC
#print axioms lib_isFuncConst_cD
#print axioms lib_isUTermVecOfSemitermVecLAct
#print axioms lib_isSemitermVecQVec
#print axioms lib_substs1Substs
#print axioms quote_cTT
#print axioms cTV_semiterm
#print axioms termLen_cTV
#print axioms termShift_cTV
#print axioms termSubst_cTV
#print axioms fvOcc_cTV
#print axioms bvOcc_le_termLen
#print axioms bvOccF_le_formulaLen
#print axioms bvOccF_shift
#print axioms fvOcc_termBShift
#print axioms fvOccF_subst_le
#print axioms fvOccF_free_le'
#print axioms instOuterAt_subst_bvList
#print axioms free_exsIter
#print axioms freeIter_subst_listToVec

-- U10 (Necessitation/Chain, 2026-09-13): the vector twins of the step constructors, the step
-- language, the context vector and the primitive-recursive chain builder with its DerivationOf
-- and dlen theorems
#print axioms useHornV_vecOf
#print axioms useHornAndV_vecOf
#print axioms introFactV_vecOf
#print axioms applyStep_proof
#print axioms dlen_applyStep_le
#print axioms chainCode_proof
#print axioms dlen_chainCode_le
#print axioms ctxVec_isFormulaSet
#print axioms chainCode_two
-- U10 (Necessitation/Chain Part C, 2026-09-13): the goal-closing leaf `goalLeafCode` (tags 6/7)
#print axioms goalLeafCode_proof
#print axioms dlen_goalLeafCode_le
#print axioms chainCode_lemma_goal

-- U10 (Necessitation/RowInst, 2026-09-13): every row of the formula walk read off the DSL and
-- instantiated — the row-shape lemmas `quote_row_<row>` (`⌜lMap emb <row>B⌝ = impChain as c` with
-- explicit `subst ?[#i, …] P` pieces), the instantiation lemmas `inst_<row>` at arbitrary closed
-- witnesses (antecedents = canonical fact codes; existential conclusions after their eliminations
-- = conjunctions of facts about `&(a-1) … &0`, `freeIter`/`freeIterAt`), the canonical fact codes
-- with formula-ness, shift, length and occurrence bounds; the general instantiation and
-- introduction laws (`instOuter_subst_listToVec`, `instOuterAt_and`, `freeIter_exsIter`,
-- `freeIterAt_subst_listToVec`, `freeIterT_bv_ge`). 87 rows (a representative dozen here).
#print axioms quote_lMap_emb_subst'
#print axioms instOuter_subst_listToVec
#print axioms instOuterAt_and
#print axioms freeIter_exsIter
#print axioms freeIterAt_subst_listToVec
#print axioms freeIterT_bv_ge
#print axioms fvOccF_quote_sentence
#print axioms formulaLen_fact_le
#print axioms fvOccF_fact_le
#print axioms quote_row_qqAndTotal
#print axioms inst_qqAndTotal
#print axioms quote_row_isSemiformulaRel
#print axioms inst_isSemiformulaRel
#print axioms quote_row_isSemitermBvar
#print axioms inst_isSemitermBvar
#print axioms quote_row_zeroLtSucc
#print axioms inst_succLtSucc
#print axioms quote_row_isRelConst_lt
#print axioms inst_isFuncConst_add
#print axioms quote_row_negAnd
#print axioms inst_negAnd
#print axioms quote_row_substsAll
#print axioms inst_substsAll
#print axioms quote_row_freeAll
#print axioms inst_freeAll
#print axioms inst_isSemitermVecAdjoin
#print axioms shift_relFact
#print axioms formulaLen_tvPiFact_le
#print axioms fvOccF_negFact_le

-- U10 (Necessitation/Lib/Occ, 2026-09-13): the occurrence-count and shift-length rows for the
-- verification proof's `dlen` bookkeeping (`DESIGN_inner_necessitation.md` §4.1–4.2,
-- `DESIGN_describe.md` §9.2 item 15) — totality of `fvOcc`/`fvOccVec`/`fvOccF`/`fvOccS`/`bvOccF`,
-- the per-constructor equations, the exact shift laws `termLenShift`/`formulaLenShift` and the
-- additive `setLenSetShiftLe`, the `free`/`subst` occurrence bounds, and the §4.1 node rows
-- `dlenLeafLe`/`dlenUnaryLe`/`dlenBinaryLe` in DSL syntax with the bridge `dslSuccEqSuccO`
-- (DSL `1` vs `oneO`). 38 rows (a representative dozen here).
#print axioms lib_fvOccTotal
#print axioms lib_fvOccSTotal
#print axioms lib_bvOccFTotal
#print axioms lib_fvOccFunc
#print axioms lib_fvOccFAnd
#print axioms lib_fvOccSInsertLe
#print axioms lib_termLenShift
#print axioms lib_formulaLenShift
#print axioms lib_setLenSetShiftLe
#print axioms lib_fvOccFFreeLe'
#print axioms lib_fvOccFSubstLe
#print axioms lib_dlenBinaryLe
#print axioms lib_dslSuccEqSuccO
-- U10 (Necessitation/Lib/Walk §6 + RowInst §3.C, 2026-09-13): chain-numeral arity variants of
-- `isSemiformulaSubsts1`/`isFormulaFree` (`… (0 + 1) …`, arity code `cT 1`, so a walk instance at a
-- chain arity matches SYNTACTICALLY; `cTTm`/`quote_cTTm` read the level-`m` chain literal) and the
-- arity-1 bridge rows `piArityOneToC`/`piArityCToOne` (`piFact 𝟏 p ↔ piFact (cT 1) p`).
#print axioms lib_isSemiformulaSubsts1C
#print axioms lib_isFormulaFreeC
#print axioms lib_piArityOneToC
#print axioms lib_piArityCToOne
#print axioms quote_cTTm
#print axioms inst_isSemiformulaSubsts1C
#print axioms inst_isFormulaFreeC

-- U10 (Necessitation/Describe, 2026-09-13): the bottom-up syntax walk as a Σ₁ step-list producer —
-- the walk's row table (`exists_walkTable`: 40 rows, one standard bound, every model), the TERM walk
-- `describeT` (a `TermRec` construction over the piece table) with its applicability theorem
-- (`describeT_ok`: every step applicable at its context from any formula-set context, no drops,
-- `descCountT` eigenvariables `≤ 2|t| − 1`, `(isSemiterm LAct).pi n &0` in the final context) and
-- the derivation it yields (`describeT_chain`).
#print axioms exists_walkTable
#print axioms termOK_of_isSemiterm
#print axioms describeT_ok
#print axioms describeT_chain
-- … and the FORMULA walk (a `Fixpoint` on `⟪n, r, y⟫`, the arity changing under quantifiers):
-- `describeF_ok` (D3 for formulas), `describeF_chain`, the root's shape fact in the final context
-- (`describeF_shape_and`, D4), and the step counts `len (describeT/F) + 4 ≤ 12·|t|/|r|` (D5, sizes).
#print axioms formOK_of_isSemiformula
#print axioms describeF_ok
#print axioms describeF_chain
#print axioms describeF_shape_and
#print axioms describeF_shape_rel
#print axioms len_describeT_le
#print axioms len_describeF_le
-- … and the cost (D5): a Horn-only list costs `len · (stepK + 36 · ctxBound)` with additive
-- context growth; the walk is Horn-only; `dlen (chainCode tbl Γ (describeF n r) d) ≤ dlen d +
-- 12|r| · (stepK N E B + 36 · ctxBound E B Γ (12|r|))` — DESIGN_describe §6.3's polynomial.
#print axioms costSum_le_of_hornOnly
#print axioms hornOnly_describeF
#print axioms costSum_describeF_le
#print axioms dlen_describeF_chain_le

-- U10 (Necessitation/Lib/Frag + RowInstB, 2026-09-13): the FRAGMENT rows of DESIGN_fragments §8.1 —
-- 196 library rows generated from one table (copy-in/congruence, identification, functionality, sets,
-- the ten fstIdx<Tag>, the top's node rows, exact lengths, bottom-up certification of neg/shift/subst/
-- free and the term level, the numerals N4/N5, the axm(ii) shape rows) — each a PA-theorem read off the
-- DSL (`quote_row_`) and instantiated at closed witnesses (`inst_`); two per group.
#print axioms lib_eqTotal
#print axioms inst_congAnd
#print axioms lib_eqOfAnd
#print axioms inst_eqOfRel
#print axioms lib_qqAndFun
#print axioms inst_setLenFun
#print axioms lib_subsetAntisymm
#print axioms inst_setShiftInsert
#print axioms lib_fstIdxAnd
#print axioms inst_fstIdxShift
#print axioms lib_proofIntro
#print axioms inst_bnumEvenCert
#print axioms lib_formulaLenRelCert
#print axioms inst_termLenVecAdj
#print axioms lib_negAndCert
#print axioms inst_substsAllCert
#print axioms lib_freeCert
#print axioms inst_qVecNthSucc
#print axioms lib_twoMulMul
#print axioms inst_lengthTwoMul
#print axioms lib_bvAnd
#print axioms inst_fvarVecNth
#print axioms quote_row_bnumOddCert
#print axioms quote_row_eqTotal

-- U10 (Necessitation/NumSteps, 2026-09-13): Σ₁ provers producing DERIVATION CODES of closed binary-numeral
-- facts, consumed by `sLemma` — the row table (`exists_numTable`), the successor chain and addition as
-- Fixpoints (`succCode_proof`/`addCode_proof`, cubic `dlen` bounds), `≤`/`<`, the node bookkeeping facts
-- (`bin3Code`: `bnum a + bnum b + bnum c + 1 ≤ bnum n`), the chain numeral `cT z = bnum z`, packaging.
#print axioms exists_numTable
#print axioms succCode_proof
#print axioms dlen_succCode_le
#print axioms addCode_proof
#print axioms dlen_addCode_le
#print axioms leCode_proof
#print axioms ltCode_proof
#print axioms bin3Code_proof
#print axioms dlen_bin3Code_poly
#print axioms cTEqCode_proof
#print axioms cTLeCode_proof
#print axioms lemmaOK_add
#print axioms lemmaOK_bin3
#print axioms stepCost_lemma_bin3

-- U10 (Necessitation/Layout, 2026-09-13): the three layout producers of DESIGN_fragments §3.3–3.5 as
-- Σ₁ step-list functions with Π₁ applicability theorems — `copySteps` (a fresh eigenvariable equal to a
-- known object plus one congruence step per fact tag), `chainSteps` (the insert-chain of a sequent with
-- its membership/formula-set facts and its length object), `eqSteps` (the identification walk by the
-- injectivity rows, computed as a relocatable template), each Horn-only with its cost bound.
#print axioms exists_layoutTable
#print axioms copySteps_ok
#print axioms costSum_copySteps_le
#print axioms chainSteps_ok
#print axioms costSum_chainSteps_le
#print axioms eqSteps_ok
#print axioms costSum_eqSteps_le

-- U10 (2026-09-14): the term-level certification pass (`Cert`, the `PassT` fixpoint: every term of
-- a dossier is re-described and certified as the image of its source) and the first six per-tag
-- FRAGMENTS (`Frag1`: the leaves `axL`/`verumIntro` and the nodes `and`/`or`/`wk`/`cut`, each a
-- step list ending with the node's goal fact, with its `ListOK`/`NoDrop`/cost theorems).
#print axioms passTGraph_exists
#print axioms goalElim_ok
#print axioms fragAxL_ok
#print axioms fragVerum_ok
#print axioms nodeAnd_ok
#print axioms nodeOr_ok
#print axioms nodeWk_ok
#print axioms nodeCut_ok
#print axioms costSum_fragAxL_le
#print axioms costSum_nodeAnd_le
#print axioms costSum_nodeCut_le

-- U10 (2026-09-14): the four REMAINING per-tag fragments (`Frag2`: `allIntro`, `exsIntro`,
-- `shiftRule`, `axm`), on the extended table `frag2Rows = frag1Rows ++ 24 rows` (`Frag2Table`,
-- `frag2Pieces`). Each is the same four-step head plus a `Frag1` dlen tail; the prologue facts the
-- `Cert`/`Layout` producers will supply (the free/substituted instance, the setShift identification,
-- the `Δ₁ch` recognizer) are LAYOUT HYPOTHESES — see the file docstring.
#print axioms exists_frag2Table
#print axioms nodeShift_ok
#print axioms nodeAll_ok
#print axioms nodeExs_ok
#print axioms nodeAxm_ok
#print axioms costSum_nodeShift_le
#print axioms costSum_nodeAll_le
#print axioms costSum_nodeExs_le
#print axioms costSum_nodeAxm_le

-- U10 (2026-09-14): the FORMULA-level certification pass (`Cert` Part 2, the `PassF` fixpoint at
-- `ν = 1` = `neg`, `ν = 2` = `shift`): the pass exists and is unique for every semiformula at every
-- pair of offsets, so `passF` is a Σ₁ FUNCTION with per-constructor equations; the named producers
-- are `certNeg`/`certShift`. Both are shift-free (`NoDrop`, `shiftsV = 0`) and have `≤ 12|r|` steps.
-- Plus Part 3, the count half of the bridge `Layout.lean:53` left open.
#print axioms passTGraph_unique
#print axioms passVGraph_unique
#print axioms passT_graph
#print axioms passV_graph
#print axioms passFGraph_exists
#print axioms passFGraph_unique
#print axioms passF_graph
#print axioms passF_and
#print axioms passF_rel
#print axioms certShift_noDrop_shifts
#print axioms certNeg_noDrop_shifts
#print axioms len_certShift_le
#print axioms len_certNeg_le
#print axioms eqCount_eq_descCountF

-- U10 (Necessitation/Members + Layout §4.8, 2026-09-14): `memberList` — the ascending member list of
-- a bit-set (a `PR` on the indices), membership both ways, strict ascent, the length bounds and the
-- DISTINCTNESS lemma the chain's exact length rests on (`setLen s = Σ formulaLen (memberList s)`);
-- and the per-node dossier equations of `Layout` (`dossFacts_*`, `dossierAt_*` at `factPreds` in the
-- order `Cert`'s `dossF_*` deliver) that the dossier bridge `DossF → DossierAt` matches against.
#print axioms mem_memberList_iff
#print axioms memberList_sorted
#print axioms memberList_nodup
#print axioms len_memberList_le_length
#print axioms len_memberList_le_setLen
#print axioms setLen_eq_listSum_memberList
#print axioms dossFacts_and
#print axioms dossFacts_rel
#print axioms dossFactsV_succ
#print axioms dossierAt_and
#print axioms dossierAt_rel
#print axioms dossierAtV_succ
#print axioms dossierAtT_func

-- U10 (Necessitation/Dossier, 2026-09-14): THE DOSSIER BRIDGE — `Cert`'s walk-context dossier
-- (`DossF/DossT/DossV`, over `walkPieces`) IS `Layout`'s relocated-template dossier (`DossierAt`,
-- `DossierAtT/V` at `factPreds`), by one structural induction per syntactic class matching the two
-- decompositions node by node under the count bridges; hence the walk's final context holds
-- `dossFacts factPreds 0 r` (`Layout.lean:53`'s open sentence), transported to `shiftsV S` by any
-- further non-dropping list.
#print axioms dossierAtT_of_dossT
#print axioms dossierAtV_of_dossV
#print axioms dossierAt_of_dossF
#print axioms dossierAt_of_walk
#print axioms dossierAt_of_walk_transport
#print axioms dossierAt_of_dossF_transport
#print axioms dossierAtT_of_walk

-- U10 (Necessitation/NumLength, 2026-09-14): N5 — the closed length fact `bnum ‖k‖ = ‖bnum k‖`
-- (`lengthEqFact k := lengthFact (bnum ‖k‖) (bnum k)`) as a DERIVATION CODE: a `Fixpoint` bit
-- recursion over its own four-row table (`LenTableOK`: the Frag rows `lengthZero`/`lengthOne` and the
-- two COMBINED bit rows carrying the successor of the length numeral, cut in from `succCode`) plus the
-- numeral table (`ltCode` for `0 < x`); `dlen ≤ (‖k‖ + 1) · nodeCap`, quadratic in `‖k‖`; `sLemma`
-- packaging. A leaf file — `NumTableOK` and every existing row index are byte-stable.
#print axioms exists_lenTable
#print axioms lenGraph_exists
#print axioms lenGraph_unique
#print axioms lengthEqCode_proof
#print axioms dlen_lengthEqCode_le
#print axioms lemmaOK_lengthEq
#print axioms stepCost_lemma_lengthEq

-- U10 (Necessitation/NumMul, 2026-09-14): N4 — the closed product fact `bnum a · bnum b = bnum (a · b)`
-- (`mulFact a b`) as a DERIVATION CODE: a `Fixpoint` on `⟪a, b, d⟫` recursing on the bits of `b` over
-- its own five-row table (`MulTableOK`: `zeroMul`/`mulZero`/`mulOne` and the two COMBINED bit rows
-- `x·y = z → x·(2y) = 2z`, `x·y = z → 2z + x = w → x·(2y + 1) = w`, the odd bit cutting in `addCode`);
-- `dlen ≤ (‖b‖ + 1) · mulNodeCap`, cubic in the bit length; `sLemma` packaging. A leaf file.
#print axioms exists_mulTable
#print axioms mulGraph_exists
#print axioms mulGraph_unique
#print axioms mulEqCode_proof
#print axioms dlen_mulEqCode_le
#print axioms lemmaOK_mulEq
#print axioms stepCost_lemma_mulEq

-- U10 (2026-09-14, Cert Part 4): the certification passes are APPLICABLE. `certShift_ok`/`certNeg_ok`:
-- with the source's walk dossier at `i` and the freshly walked image's at `j`, the pass is `ListOK` at
-- cap 8, `NoDrop`, Horn-only, shift-free, and leaves `shiftFact &j &i` / `negFact &j &i` in its final
-- context; the term level (`passTGraph_shift_ok`, `passTGraph_eq_ok`) and the costs (the walk's
-- polynomial at `12|r|` steps). The `neg` atom needed the identification pass + `congRel/congNRel`
-- (the image's atom vector is fresh) — the former single-step `ν = 1` branch was unprovable.
#print axioms passTGraph_shift_ok
#print axioms passVGraph_shift_ok
#print axioms passTGraph_eq_ok
#print axioms passVGraph_eq_ok
#print axioms passFGraph_shift_ok
#print axioms passFGraph_neg_ok
#print axioms certShift_ok
#print axioms certNeg_ok
#print axioms costSum_certShift_le
#print axioms costSum_certNeg_le
#print axioms descCountF_certPieces
#print axioms descCountF_neg

-- U10 (2026-09-14, Cert Part 5): the exact-length producer `lenSteps` (§3.6 "lengths"). The term/vector
-- fixpoint `LenT` (`lenT`/`lenV`) and the formula fixpoint `LenF` (`lenSteps W T n r i`, `T` the NumSteps
-- table for the closed `succFact/addFact/cTEqFact` cuts), NOT shift-free (one `formulaLenTotal`/
-- `termLenTotal` per node, one `adjoinTotal` per vector entry; `shiftsV + 1 ≤ 2|r|`, `len ≤ 14|r|`),
-- `lenSteps_ok` (`ListOK` at cap 8, `NoDrop'`, `lenFact (bnum |r|) &(i + shifts)` in the final context)
-- and `costSum_lenSteps_le` (Frag1's size discipline at `14|r|` steps). Three rows APPENDED to the
-- certification table: `congAdd` (183), `congSucc` (184), `listSumAdjI` (185).
#print axioms lib_congAdd
#print axioms lib_congSucc
#print axioms lib_listSumAdjI
#print axioms cok_congSucc
#print axioms cok_listSumAdjI
#print axioms lenT_defined
#print axioms lenV_defined
#print axioms lenSteps_defined
#print axioms lenSteps_and
#print axioms lenSteps_struct
#print axioms lenTGraph_ok
#print axioms lenVGraph_ok_aux
#print axioms lenFGraph_ok
#print axioms lenSteps_ok
#print axioms sizeOK_lenSteps
#print axioms costSum_lenSteps_le

-- U10 (Necessitation/Top, 2026-09-14): THE TOP against an explicit kit. The target's code shape
-- `instB ⌜Box_g χ⌝ k = boxFact (numeral ⌜χ⌝) (bnum k)` for a VARIABLE χ, the three closing rows
-- (gIntroNum/lenDerIntro/boxIntro) and the top table, the root steps (walk + chain → RootLayout),
-- the closing steps (goalElim + N5/N4/N4/N2 sLemmas + five rows → the target fact), the assembly
-- `top_main` (a proof code of the box instance of length ≤ topBound), the cubic bound
-- (`topD_pb`, `topBound_pb`, through the graded `PB` calculus with u³ ≤ 8G), and
-- `boundedInnerNec_three_of_kit : KitPackage … → BoundedInnerNec 3`. The two kits (`VerifyKit` =
-- §6.3/§6.4/§5 for the relation `VerifyGraph`; `PinKit χ` = §7.1 steps 1–4/§7.2) are the remaining
-- `Verify`/`Cert` obligations; nothing below is an axiom.
#print axioms target_eq_boxFact
#print axioms termLen_qNum_le
#print axioms exists_topTable
#print axioms tok_boxIntro
#print axioms rootSteps_ok
#print axioms closeSteps_ok
#print axioms top_main
#print axioms topD_pb
#print axioms topBound_pb
#print axioms boundedInnerNec_three_of_kit

-- U10 (Necessitation/PrologueRows + Prologue, 2026-09-15): THE PROLOGUE PRODUCERS. The prologue table
-- `proRows := topRows ++ proExtraRows ++ certTailRows` (the row-index collision between the certification
-- rows at `100 + k` and the fragment rows resolved by RE-INDEXING certification lists, `reidxL`), the
-- canonical `Layout` of a sequent (member walk dossiers + lengths, chain, fresh length object + numeric
-- bound) with its transport, the builder `layoutSteps` (member blocks, chain, the `setLen` fold with the new
-- row `setLenSingLe`), the leaves (`proAxL` = re-indexed `certNeg`; `layout_verum`), the identification of an
-- `insert` object with the child's chain (`subChain`, `loopA`/`loopB`/`blockP`, `identIns`), the `insert`
-- child's prologue `proIns` and recovery `postIns`, the `and`/`or` readings, the `cut` prefix `proCutPre`
-- (walk + lengths of `p` and `neg p`, `certNeg`) and the `wk` prologue `proWk` (Loop W + the subset fold).
-- Nothing below is an axiom.
#print axioms exists_proTable
#print axioms listOK_reidxL
#print axioms costSum_reidxL
#print axioms pok_setLenSingLe
#print axioms Layout.transport
#print axioms memberBlocks_ok
#print axioms foldBlockS_ok
#print axioms lenFoldAux_ok
#print axioms layoutSteps_ok
#print axioms proAxL_ok
#print axioms layout_verum
#print axioms subChain_ok
#print axioms loopA_ok
#print axioms loopB_ok
#print axioms identIns_ok
#print axioms proIns_ok
#print axioms postIns_ok
#print axioms layout_and
#print axioms layout_or
#print axioms proCutPre_ok
#print axioms loopW_ok
#print axioms proWk_ok

end ArithS
