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
import ArithS.Necessitation.NumId
import ArithS.Necessitation.NumIdRows
import ArithS.Necessitation.Pin
import ArithS.Necessitation.ProAxmRows
import ArithS.Necessitation.ProAxm
import ArithS.Necessitation.IndRecRows
import ArithS.Necessitation.IndRec
import ArithS.Necessitation.NodeSize
import ArithS.Necessitation.Verify2
import ArithS.Necessitation.Verify3
import ArithS.Necessitation.Bounds
import ArithS.Necessitation.Verify4
import ArithS.Necessitation.Assemble
import ArithS.Necessitation.Verify5
import ArithS.Necessitation.Package

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

-- U10 (2026-09-15, Cert Part 6): `certSubst` / `certFree` (§3.6 "substitution" and "free instance"). The
-- `nth` chain `NthC` (`nthChainL`, Horn-only, shift-free), the two-mode term/vector pass `SubT` (`subT`/`subV`:
-- mode 0 substitution by the walked vector `w` — the bvar leaf reads `w.[z]` through the chain, re-walks it
-- in mode 1 against the image and identifies by the new row `congTSubstL` (186) — mode 1 the bound shift;
-- both shift-free, `len + 4 ≤ 12|t|(S + 1)`), and the formula pass `SubF` (`certSubst W Wd n m w iw r i j`,
-- W-parametric Σ₁): NOT shift-free — every quantifier WALKS `qVec w` (`qWalkP`, one `qVec` vector of sum ≤ Q,
-- hence `shiftsV ≤ 2Q·|r|`) and re-runs the vector pass in mode 1 for `qVecCert` (176). `subFGraph_ok`
-- (cap 9, `NoDrop`, Horn-only, `substFact &(j+σ) ⟨w⟩(iw+σ) &(i+σ)` at the moved offsets), `certSubst_ok`
-- (Part-5 shape: `ListOK … 9`, `NoDrop'`, `shiftsV ≤ 2Q|r|`, `len ≤ sfK L Q · |r|`, the fact),
-- `costSum_certSubst_le` (Frag1's size discipline at `Q = D = 0`, Horn-only). `certFree W Wd p ip isp ifp`
-- = the walk of `⟨&0⟩` + `certSubst` of `shift p` by `⟨&0⟩` + `certShift` + rows 166/165 → `freeFact`;
-- `certFree_ok`, `costSum_certFree_le`. Nothing below is an axiom.
#print axioms lib_congTSubstL
#print axioms cok_congTSubstL
#print axioms nthChainL_defined
#print axioms nthCGraph_struct
#print axioms nthCGraph_ok
#print axioms subT_defined
#print axioms subV_defined
#print axioms subTGraph_noDrop_shifts
#print axioms subVGraph_noDrop_shifts
#print axioms len_subTGraph_le
#print axioms subTGraph_ok
#print axioms subVGraph_ok
#print axioms certSubst_defined
#print axioms certSubst_graph
#print axioms subFGraph_exists
#print axioms len_subFGraph_le
#print axioms subFGraph_ok
#print axioms certSubst_ok
#print axioms costSum_certSubst_le
#print axioms certFree_ok
#print axioms costSum_certFree_le

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

-- U10 (Necessitation/NumId, 2026-09-15): NUMERAL IDENTIFICATION — `eqFact &x (numeral ⌜φ⌝)` from the walk
-- dossier of a STANDARD code (the quote of a Lean-level formula), the `pinSteps` of DESIGN §4.10(i)/§7.1
-- step 3. Per node one closed shape fact at the numerals (a `Lib` sentence: true in `ℕ` by the quote
-- equations, true everywhere by 𝚺₀-absoluteness, `Lib.of_models`; its code by `quote_lMap_emb_subst`)
-- cut in as an `sLemma`, then one identification row `eqOf<Kind>` at closed witnesses — SHIFT-FREE lists,
-- constants per formula (`Lib` lengths + the 𝚺₁-absolute `formulaLen`/`termLen`/`takeLast`). The meta
-- induction over `SyntacticSemiterm`/`Semiproposition`, the sentence form `numId_sentence` and the cost
-- (`Frag1.costSum_le_of_sizeOK`). Nothing below is an axiom.
#print axioms lib_cfact_of_nat
#print axioms closedDer_of_lib
#print axioms flN_cast
#print axioms lemmaThenHorn_ok
#print axioms termId_bvar
#print axioms vecId_succ
#print axioms numId_term
#print axioms formId_and
#print axioms formId_rel
#print axioms numId_formula
#print axioms numId_sentence
#print axioms numInv_cost

-- U10 (Necessitation/Prologue, 2026-09-15 evening): the `or` and `shift` prologues, the size classes and costs of every
-- prologue, and the rows 156–158 for the EMPTY sequent. `proOr` = two `proIns` + `congInsertS`; `proShift` = the chain
-- over the shifted members + the child's layout + Loop S (`certShift`) + Loop I (`setShiftInsert`) + Fold U
-- (`insertSubset`) + Loop M (`shiftMemSetShift`) + the parent's `subChain` + `subsetAntisymm` + `congSetShiftL`;
-- `sizeOK_layoutSteps` is standalone (`hornOnly_chainSteps` by the rows, the fold's `sum2` lemmas bounded by
-- `sum2Q`/`sum2D`); every `costSum_pro<Tag>_le` is `costSum_le_of_sizeOK 8`. Nothing below is an axiom.
#print axioms proOr_ok
#print axioms shBase_ok
#print axioms loopS_ok
#print axioms loopI_ok
#print axioms uSub_ok
#print axioms loopM_ok
#print axioms proShiftPre_ok
#print axioms shTail2_ok
#print axioms proShift_ok
#print axioms formulaLen_sum2Fact_le
#print axioms dlen_sum2Code_le'
#print axioms sizeOK_lenFoldAux
#print axioms hornOnly_chainSteps
#print axioms sizeOK_layoutSteps
#print axioms costSum_layoutSteps_le
#print axioms costSum_proAxL_le
#print axioms costSum_postIns_le
#print axioms sizeOK_proIns
#print axioms costSum_proIns_le
#print axioms sizeOK_proCutPre
#print axioms costSum_proCutPre_le
#print axioms sizeOK_proWk
#print axioms costSum_proWk_le
#print axioms sizeOK_proOr
#print axioms costSum_proOr_le
#print axioms sizeOK_proShift
#print axioms costSum_proShift_le
#print axioms layoutSteps0_ok
#print axioms proWk0_ok
#print axioms proShift0_ok

-- U10 (Necessitation/NumIdRows + Pin, 2026-09-15): TOWARDS `PinKit χ`. The pin's six rows on the prologue
-- table (`nIdx = proRowCount + k`; the NEW `bnumOddOfEven`, the odd bit-step through the even numeral — the
-- library's `bnumOddCert` has 12 witnesses, above cap 9), `NumIdTable`, the kernel `pinKernel_ok`
-- (`congSubstArg ∷ instBIntro`) and the assembly `pin_assembly`: every `pin` conjunct of `PinKit χ` except the
-- cost, from two producer ORACLES (`BnumOracle` = the bit-wise `bnum k` certification, `SubstOracle` =
-- `certSubst` re-indexed) — see `Pin.lean` §3 for what remains and why the cost conjunct as stated is out of
-- reach of the generic cost lemmas. Nothing below is an axiom.
#print axioms lib_bnumOddOfEven
#print axioms nok_bnumEvenCert
#print axioms nok_bnumOddOfEven
#print axioms exists_numIdTable
#print axioms NumIdTable.proTable
#print axioms pinKernel_ok
#print axioms transport_bnum
#print axioms pin_assembly

-- U10 (Necessitation/Top §9–§11, 2026-09-15): THE DEGREE-4 ASSEMBLY (BRIEF §11 THE FINDING). The kits
-- restated in the COARSE cost shape the repository's lemmas produce (`VerifyKit'`/`PinKit'`: costSum ≤
-- len·(costK N E B 9 (kitQ C B E) (kitD C size) + 38·(ctxBoundG (growK …) Γ len + …)) with the ctxBoundG
-- end-context bounds), `top_main'`, the quartic bound `topBound'_pb` and
-- `boundedInnerNec_four_of_kit : KitPackage' … → BoundedInnerNec 4`. Degree 4 (not 3) because the generic
-- accounting charges 4·B·E of context growth per step; `_three_of_kit` stays as the fine-kit target.
#print axioms costK9_le
#print axioms top_main'
#print axioms succ_quart_le
#print axioms topBound'_pb
#print axioms boundedInnerNec_four_of_kit

-- U10 (Necessitation/Prologue §13–§15, 2026-09-15): the `all` and `exs` prologues. `proAll_ok` (the fresh walks of
-- `shift p`/`free p` + the re-indexed `certFree`; `proSS` = the layout of `setShift s` + `proShift_ok` reused with the
-- roles `(setShift s, s, 0)` + Loop E/two subChains/subsetAntisymm/congSetShiftR; `proIns_ok` reused) and `proExs_ok`
-- (the vector walk of `⟨t⟩`, the term `lenT`, the length object `eqTotal/eqSymm/congTLenNum/leOfEqP`, the walk of
-- `substs1 t p`, the re-indexed `certSubst` at the singleton vector, `substsSubsts1`; `proIns_ok` reused) discharge every
-- `nodeAll_ok`/`nodeExs_ok` hypothesis except the child's own goal (`postIns`); costs in the `costSum_le_of_sizeOK 9`
-- shape. Nothing below is an axiom.
#print axioms loopE_ok
#print axioms ssIdent_ok
#print axioms proSS_ok
#print axioms allCert_ok
#print axioms layout_all
#print axioms proAll_ok
#print axioms ProTable.leOfEqP
#print axioms vecWalk_ok
#print axioms lenObj_ok
#print axioms layout_exs
#print axioms exsCert_ok
#print axioms proExs_ok
#print axioms sizeOK_proSS
#print axioms sizeOK_proAll
#print axioms costSum_proAll_le
#print axioms sizeOK_proExs
#print axioms costSum_proExs_le

-- U10 (Necessitation/BnumSteps + Pin §4–§7, 2026-09-15): `PinKit'` DISCHARGED FOR EVERY χ. `BnumSteps`: the
-- bit-wise certification `bnumSteps k j` (a Fixpoint over the bits of `k` with PACKED parameters — `definability`'s
-- comp rules stop at arity 5; per bit an `sLemma` `𝟏 ≤ bnum m` + one Horn `bnumEvenCert`/`bnumOddOfEven`, the two
-- `𝟏`s of `𝟐` identified by `eqRefl/eqOfFunc/eqRefl/congAdj`), `bnGraph_ok` (Π₁ order induction, the quote `Pbnum`
-- and the pieces/counts OPAQUE in the motive), `bnumSteps_ok` (cap 9, shift-free, len ≤ 8‖k‖+1, SizeOK) ⇒
-- `bnumOracle_of` (Cb = 27). `Pin` §5: `substSteps_ok`/`substOracle_of` — `certSubst_ok` re-indexed at `bnum k ∷ 0`
-- with `SubFPre` from `subFPre_single`; its LENGTH is linear in ‖k‖ through `len_subFGraph_le_lin` (`sfL L Q = L + 24Q
-- + 22`: `Cert.sfK`'s `12Q(Q+1)` is the mode-1 vector pass bounded at `S := Q`; at `S := 0` it is `12Q`). §6: `pin_full`
-- (the assembly with the real producers, `len ≤ Cχ(‖k‖+1)`, `SizeOK (Cχ(‖k‖+1)) (Cχ(‖k‖+1)³)`), `pinKit'_of` — the
-- three coarse cost conjuncts of `Top.PinKit'` in ONE `costSum_le_of_sizeOK` over the whole list. §7:
-- `exists_numIdTableB` (the row-body bound `rowsB`), `pinKit'_package` — the pin half of `KitPackage'`. Nothing below
-- is an axiom.
#print axioms bnEvenTail_ok
#print axioms bnOddTop_ok
#print axioms bnGraph_ok
#print axioms bnGraph_len_size
#print axioms bnumSteps_ok
#print axioms bnumOracle_of
#print axioms len_subFGraph_le_lin
#print axioms substSteps_ok
#print axioms substOracle_of
#print axioms pin_full
#print axioms pinKit'_of
#print axioms exists_numIdTableB
#print axioms pinKit'_package

-- U10 (Necessitation/Prologue §16–§17, 2026-09-15): the `insert` child of the EMPTY parent (`proIns0_ok`: `cut` at `∅`,
-- `identIns0` = Loop A + the child's subChain + emptySubsetC + congSubsetL + the p block + insertSubset +
-- subsetAntisymm) and the `0`-producers' size discipline and costs. Nothing below is an axiom.
#print axioms identIns0_ok
#print axioms proIns0_ok
#print axioms sizeOK_layoutSteps0
#print axioms sizeOK_proWk0
#print axioms sizeOK_proShift0
#print axioms costSum_layoutSteps0_le
#print axioms costSum_proWk0_le
#print axioms costSum_proShift0_le
#print axioms sizeOK_proIns0
#print axioms costSum_proIns0_le

-- U10 (Necessitation/ProAxm + ProAxmRows, 2026-09-15): the `axm` prologue. The `V`-level case split of `Δ₁ch TAct`
-- (`mem_TAct_class_cases`: a standard axiom's code — `StdAxiom`, the four action sentences and `𝗣𝗔⁻` along `emb`,
-- FINITE — or an induction instance, `InductionR`), read off `Theory.Δ₁.singleton`/`ofList`/`ofFinite` for VARIABLE
-- sentences over a VARIABLE language (never a closed quote). Case (i) DISCHARGED per model on NumId's route: the
-- closed `Lib` fact `axchNum ⌜σ⌝` (= `axchFact (numeral ⌜σ⌝)`, TRUE by `Δ₁Class.mem_iff`) as an `sLemma`, then ONE
-- Horn step at the NEW row `congAxch` (`!axch x → y = x → !axch y`, one row for every σ — `axiomRec σ` would need
-- one per σ): `axmStd_ok` (at the dossier), `proAxmStd_ok` (at the `Layout`, `memTop_le`), `proAxm_std` (ONE
-- constant over `StdAxiom` by `Set.Finite.bddAbove`), `proAxm_ok` (both cases; case (ii) is the explicitly named,
-- UNDISCHARGED hypothesis `AxmIndOracle`), `costSum_proAxm_le` (= `numInv_cost`). NOT a Σ₁ producer (NumId's
-- `sLemma` derivations are per model) — see the file docstring. Nothing below is an axiom.
#print axioms lib_congAxch
#print axioms aok_congAxch
#print axioms exists_proAxmTableB
#print axioms eval_singleton_ch
#print axioms eval_ofList_ch
#print axioms eval_paMinus_ch
#print axioms stdAxiom_finite
#print axioms mem_TAct_class_cases
#print axioms lib_axchNum
#print axioms code_axchNum
#print axioms axmStd_ok
#print axioms proAxmStd_ok
#print axioms proAxm_std
#print axioms proAxm_ok
#print axioms costSum_proAxm_le


-- U10 (Necessitation/NodeSize + Prologue §18, 2026-09-15): every node's sizes are charged in its own `dlen`
-- (`setLen_fstIdx_le_dlen`, the principal formulas / the `exs` witness / the children `≤ dlen`), and the LENGTHS and
-- SHIFTS of every prologue producer made concrete (`len_eqSteps_le` by a double walk; the loops via `preSum`; `and`/`or`/
-- `cut`/`wk`/`shift`/`∅` linear in the node sizes; `all`/`exs` degree 5 in `D` through `Cert`'s `sfK L Q` — see §18's
-- head docstring), with the cost corollaries `costSum_pro*_le'` at the concrete lengths. Nothing below is an axiom.
#print axioms one_le_dlen
#print axioms setLen_fstIdx_le_dlen
#print axioms formulaLen_le_dlen_of_mem
#print axioms dlen_dp_succ_le_andIntro
#print axioms termLen_le_dlen_exsIntro
#print axioms setLen_child_le_dlen_cutRule_right
#print axioms preSum_len_eq
#print axioms len_eqSteps_le
#print axioms len_loopA_le
#print axioms len_layoutSteps_le
#print axioms len_identIns_le
#print axioms len_proIns_le
#print axioms len_proOr_le
#print axioms len_proWk_le
#print axioms len_proShift_le
#print axioms len_proSS_le
#print axioms len_certSubst_le_sfK
#print axioms len_certSubst_single_le
#print axioms len_allCert_le
#print axioms len_proAll_le
#print axioms len_exsCert_le
#print axioms len_proExs_le
#print axioms len_proIns0_le
#print axioms costSum_proIns_le'
#print axioms costSum_proShift_le'
#print axioms costSum_proAll_le'
#print axioms costSum_proExs_le'
#print axioms shiftsV_proIns_le'
#print axioms shiftsV_proAll_le

-- U10 (Necessitation/Top §12–§14, 2026-09-15): THE POLYNOMIAL-LENGTH KITS (BRIEF §11, THE SECOND ACCOUNTING
-- FINDING). `VerifyKit'' … m` (list length `Ck·(dlen ρ+1)^m`, cap `Ck·((dlen ρ+1)^m + i) ≤ E`), its `m = 1`
-- coincidence with `VerifyKit'`, `KitPackage''`, `top_main''`, the general-degree tools
-- (`succ_pow_le`, `PB.final_pow`), `topBound''_pb` (degree 4n) and
-- `boundedInnerNec_of_kit'' : KitPackage'' … m → BoundedInnerNec (deg m)`, `deg m = 4·max m 1`
-- (`deg 1 = 4`, `deg 3 = 12`: the cap forces E ~ G^m, so cost ~ L·(L²·growK) ~ G^{4m}).
#print axioms verifyKit''_one_iff
#print axioms top_main''
#print axioms succ_pow_le
#print axioms PB.final_pow
#print axioms topBound''_pb
#print axioms deg_one
#print axioms deg_three
#print axioms boundedInnerNec_of_kit''

-- U10 (Necessitation/Verify2, 2026-09-15): THE VERIFY GRAPH WITH COMPUTED PROLOGUES. `VerifyGraph'` is the Δ₁
-- fixpoint on ⟪ρ, L⟫ whose lists are the ten assemblers `v<Tag>` (prologue ++ child ++ recovery ++ node, every node at
-- offset 0); the axm certificates are a TABLE parameter `A` (`AxmTableOK`, Δ₁), monotone (`VerifyGraph'.mono_A`);
-- existence from the induction oracle `AxmIndOracleC` (`verifyGraph'_exists`); context monotonicity of `ListOK`
-- (`listOK_mono_subset`, no shift-freeness needed); the per-tag `ok` lemmas and the glued node invariant
-- `verifyGraph'_ok`: `shiftsV L ≤ Cs·(dlen ρ)^6` under `Ck·(dlen ρ + 1)^6 ≤ E` (degree 6, forced by the quintic
-- `shiftsV_proAll_le`/`shiftsV_proExs_le`); `verifyGraph'_ok_pow` is the `(dlen ρ + 1)^m` form, `m = 6`.
#print axioms VerifyGraph'.case_iff
#print axioms VerifyGraph'.mono_A
#print axioms verifyGraph'_exists
#print axioms listOK_mono_subset
#print axioms axmEntry_exists
#print axioms vAxL_ok
#print axioms vVerum_ok
#print axioms vAxm_ok
#print axioms vAnd_ok
#print axioms vOr_ok
#print axioms vWk_ok
#print axioms vShift_ok
#print axioms vCut_ok
#print axioms vAll_ok
#print axioms vExs_ok
#print axioms verifyGraph'_ok
#print axioms verifyGraph'_ok_pow

-- U10 (Necessitation/IndRecRows + IndRec, 2026-09-15): CASE (ii) OF THE `axm` PROLOGUE — the induction-instance
-- recognizer `indRecL` (Lib rows for `bs` = ℒₒᵣ-formation + exact `bv`, `fvSeq`, `isC0`/`isC1`, `bodyShape`,
-- `indBodyL`, `indRecL`, six closed `isFuncOR`/`isRelOR` rows; the ℒₒᵣ/LAct wall crossed semantically in
-- `inductionR_of_L`), the per-model passes (`qqAllsWalk_ok`, `leChain_ok`, `bsT_ok`/`bsV_of_entries`/`bsF_ok`,
-- `fvSeq_ok`, `shiftSelf_ok`), the two stages (`stageA` with eigenvariables, `stageB` shift-free) and the producer
-- `axmInd_ok`: from `p`'s dossier a cap-9 `NoDrop'` Horn-only list with `shiftsV ≤ 100 Z³`, `len ≤ 4100 Z⁵`, leaving
-- `axchFact &(ip + shiftsV P)`. The HONEST oracle `AxmIndOracle'` (shifts allowed, the fact at the moved offset,
-- `C : V` polynomial in `D`, `i`) is discharged by `axmIndOracle_of`; `ProAxm.AxmIndOracle` (shift-free, standard
-- `C`) is unsatisfiable for nonstandard `p` — the consumer is to be adjusted (see `IndRec.lean`'s docstring).
#print axioms inductionR_of_L
#print axioms qqAllsWalk_ok
#print axioms leChain_ok
#print axioms bsT_ok
#print axioms bsV_of_entries
#print axioms bsF_ok
#print axioms fvSeq_ok
#print axioms shiftSelf_ok
#print axioms indBodyVal_shape
#print axioms stageWalks
#print axioms bodyDoss
#print axioms stageA
#print axioms stageB
#print axioms axmInd_ok
#print axioms axmIndOracle_of


-- U10 (Necessitation/IndRec §7 + Verify3, 2026-09-15): THE SEAM — the recognizer plugged into the recursion.
-- IndRec §7: `formulaLen_subst_fvarVec_le` (`|subst (fvarVec m) b| ≤ |b|`: substitution by an index-bounded variable
-- vector never lengthens, `VarInv` preserved by `qVec`), `certSubst_winv'`/`substInst_*'` with `Pin`'s LINEAR `sfL`
-- bound, `stageA'`/`stageB'` with the offset moved to the E-room, and `axmInd_ok' : |p| ≤ D → ip + 200(D+1)³ ≤ E →
-- … shiftsV ≤ 100(D+1)³ ∧ len ≤ 1400(D+1)³` — DEGREE 3 in `D`, offset-independent; `axmIndOracle_of'` (C = 1400(D+1)³).
-- Verify3: shifted certificate entries `AxmEntryOK'`/`AxmTableOK'` (bound `entryB Cv p = Cv·(|p|+1)³`), the shifted
-- assembler `vAxm'`, `VerifyGraph''` (`VerifyGraph'` with the `axm` clause on `vAxm'`), the oracle `AxmIndOracleC'`
-- DISCHARGED (`axmIndOracleC'_of_indRec`), `verifyGraph''_exists_unconditional` (NO oracle hypothesis),
-- `vAxm_ok'`, `verifyGraph''_ok` (re-glued at m = 6; constants `Cs + Cv`, `Ck + 5·Cv`), `verifyGraph''_ok_pow`.
#print axioms formulaLen_subst_fvarVec_le
#print axioms stageA'
#print axioms stageB'
#print axioms axmInd_ok'
#print axioms axmIndOracle_of'
#print axioms VerifyGraph''.case_iff
#print axioms VerifyGraph''.mono_A
#print axioms axmIndOracleC'_of_indRec
#print axioms axmEntry_exists'
#print axioms verifyGraph''_exists'
#print axioms verifyGraph''_exists_unconditional
#print axioms vAxm_ok'
#print axioms verifyGraph''_ok
#print axioms verifyGraph''_ok_pow

-- U10 (Necessitation/Bounds, 2026-09-15): CUBIC `all`/`exs` bounds — the verification list can run at m = 4. The
-- substitution certificate through `Pin`'s LINEAR `sfL` at the `Cert` §6.7 caps: `len_certSubst_single_le_cubic ≤
-- 144·p3 (D+1)`; `Prologue`'s parametric `_of` lemmas instantiated: `len_allCert_le_cubic ≤ 196·p3 (D+1)`,
-- `len_proAll_le_cubic ≤ 402·p3 (D+1)`, `len_exsCert_le_cubic ≤ 189·p3 (D+1)`, `len_proExs_le_cubic ≤ 256·p3 (D+1)`
-- (same hypotheses as the quintic `len_pro*_le`); shifts through `shiftsV ≤ len` (`shiftsV_pro*_le_cubic`) and SHARP
-- from the `_ok`s (`shiftsV_proAll_le_sharp ≤ 2(1+D)(2+D)D + 23D + 8`, `shiftsV_proExs_le_sharp ≤ 2(1+D)(1+2D)D + 12D +
-- 3` — cubic inherently: the `qVec` iterate's unary bvar lengths sum to `Σ_{i<e}(i+1)`); the recursion arithmetic at
-- m = 4 (`p4`, `p4_split`, `rec1₄`/`rec2₄`, the node caps `allEQ_p3`/`alliE_p3`/`exsEQ_p3`/`exsiE_p3`/`allE_p4`/
-- `exsE_p4`/`allNode_p4`/`axmLeaf_p4`) and the LOCAL step at m = 3 (`rec1_local`/`rec2_local`); the cost corollaries
-- `costSum_pro{All,Exs}_le''`.
#print axioms len_certSubst_single_le_cubic
#print axioms len_allCert_le_cubic
#print axioms len_proAll_le_cubic
#print axioms len_exsCert_le_cubic
#print axioms len_proExs_le_cubic
#print axioms shiftsV_proAll_le_cubic
#print axioms shiftsV_proExs_le_cubic
#print axioms shiftsV_proAll_le_sharp
#print axioms shiftsV_proExs_le_sharp
#print axioms rec1₄
#print axioms rec2₄
#print axioms allNode_p4
#print axioms axmLeaf_p4
#print axioms allE_p4
#print axioms exsE_p4
#print axioms rec1_local
#print axioms costSum_proAll_le''
#print axioms costSum_proExs_le''

-- U10 (Necessitation/Verify4, 2026-09-15): THE RECURSION INVARIANT AT m = 4 — `Verify3.verifyGraph''_ok` re-glued with
-- `p6 ↦ p4` throughout on `Bounds`' cubic `all`/`exs` shifts (`shiftsV_proAll/proExs_le_cubic` at `D = 2d`, landed in
-- `402·p3 (2(d+1))`) and the `m = 4` arithmetic (`rec1₄`/`rec2₄`, `allNode_p4`, `axmLeaf_p4`, `allE_p4`/`exsE_p4`,
-- `allEQ_p3`…`exsiE_p3` lifted by `p3_le_p4`, `capE4`/`capE4'`, `child_bound4`, `lin_le_p3`, `one_le_Cs_p4`):
-- `verifyGraph''_ok4` — E-room `(Ck + 5·Cv)·p4 (dlen ρ + 1) ≤ E`, list `shiftsV L ≤ (Cs + Cv)·p4 (dlen ρ)`, constants
-- `Cs = 25731`, `Ck = 128655 = 5·Cs`; `verifyGraph''_ok_pow4` — the `VerifyKit''` shape at exponent 4
-- (`Ck·(Cv+1)·(dlen ρ+1)^4`), so `deg 4 = 16`. Every arm closes at m = 4; m = 3 needs per-node accounting (not done).
#print axioms verifyGraph''_ok4
#print axioms verifyGraph''_ok_pow4

-- U10 (Necessitation/Assemble, 2026-09-15): THE KIT OVER `VerifyGraph''` AND THE ASSEMBLY. The root bridge (the top's
-- `RootLayout` re-laid canonically by `layoutSteps {x}`, the two copies identified by `identRoot` — `eqSteps` + set rows —
-- and the goal RETARGETED onto the root sequent by `retargetRoot` = `goalElim`/`congFstIdx`/`sGoal`), the bridged list
-- `vList = layoutSteps {x} ++ identRoot ++ L ++ retargetRoot` with `vList_full` (ok + len + SizeOK, `Ck = (asmCk … + cG)·(Cv+1)`
-- over `Verify4.verifyGraph''_ok_pow4` at exponent 4), `VerifyKit'''` (Top's `VerifyKit''` over `VerifyGraph''`/`AxmTableOK'`
-- with the bridge folded in), `verifyKit'''_of`, `KitPackage'''`, `top_main'''`/`boundedInnerNec_of_kit''' (m ≥ 3)`,
-- `exists_indRecTableB`, `kitPackage'''_of_size` (the `axm` case UNCONDITIONAL via `verifyGraph''_exists_unconditional`),
-- **`boundedInnerNec_sixteen_of_size : SizeOracle Cz → BoundedInnerNec 16`** and **`dupoc_self_coop_of_size`** — conditional
-- on ONE named hypothesis, `SizeOracle` (`len L ≤ Cz·(dlen ρ+1)^4 ∧ SizeOK (kitQ …) (kitD …) L` for the graph's lists; the
-- glue `verifyGraph''_ok4` does not track `len`/`SizeOK`). TRAP: `exists_cGoal` — a `def` of `4·(cDer + …)` (`flen`s of the
-- giant `derivation` sentence) stalls every `push_cast`/`omega` that touches it; packaged existentially, cast identity by `rw`.
#print axioms len_memberList_single
#print axioms layout_single
#print axioms identRoot_ok
#print axioms retargetRoot_ok
#print axioms sizeOK_retargetRoot
#print axioms formulaLen_goalFact_le
#print axioms exists_cGoal
#print axioms layQ_le
#print axioms layD_le
#print axioms goalFact4_le_kitQ
#print axioms vList_full
#print axioms verifyKit'''_of
#print axioms top_main'''
#print axioms boundedInnerNec_of_kit'''
#print axioms exists_indRecTableB
#print axioms kitPackage'''_of_size
#print axioms deg_four
#print axioms boundedInnerNec_sixteen_of_size
#print axioms dupoc_self_coop_of_size

-- U10 (Necessitation/Verify5, 2026-09-15): THE SIZE HALF, PART 1 — the layout size class is MONOTONE
-- (`layQ_mono`/`layD_mono` from `lenQ`/`lenD`/`sum2Q`/`sum2D`), and the NODE CODES' derivation lengths land in it:
-- `dlen_leafCode_le' ≤ sum2D N' B' Dz`, `dlen_bin2Code_le'`/`dlen_bin3Code_le' ≤ 2·sum2D N' B' Dz`, through
-- `codeK N' B' Dz = (‖Dz‖+1)(‖Dz‖+2)·nodeCost N' B' (18‖Dz‖+7)` and the summand bounds `dlen_succCode_le_codeK`,
-- `dlen_addCode_le_codeK`, `dlen_leCode_le_codeK` (modelled on `Prologue.dlen_sum2Code_le'`). These discharge the
-- `dlen TAct (leafCode …) ≤ D` hypotheses of `Frag1`/`Frag2`'s `sizeOK_frag*`/`sizeOK_node*`, which NO caller in the
-- tree had ever discharged. NOTE: `Assemble.SizeOracle` is NOT PROVABLE as stated (it binds the numeral table `T`
-- with no `NumTableOK`, while every prologue size lemma needs one and lands at `layD N' B' D`; machine-checked:
-- `sizeOK_layoutSteps` cannot even be elaborated with `T` free). `verifySizeOracle_of_arms` is the
-- `NumTableOK`-carrying interface; the ten induction arms are still the named hypothesis `ArmHyps`.
#print axioms lenQ_mono
#print axioms lenD_mono
#print axioms sum2Q_mono
#print axioms sum2D_mono
#print axioms layQ_mono
#print axioms layD_mono
#print axioms sum2D_eq_four_codeK
#print axioms nodeCost_le_codeK
#print axioms nodeCost_bk_le_codeK
#print axioms dlen_succCode_le_codeK
#print axioms dlen_addCode_le_codeK
#print axioms dlen_leCode_le_codeK
#print axioms dlen_leafCode_le'
#print axioms dlen_bin2Code_le'
#print axioms dlen_bin3Code_le'
#print axioms sum2D_le_layD
#print axioms verifySizeOracle_of_arms

-- U10 (Necessitation/Verify5, 2026-09-15): THE SIZE HALF, PART 2 — the size-class LANDING lemmas and the `axm` ARM.
-- The three classes of the glue each land in the kit class `(kitQ Cz B E, kitD Cz d)`: the `axm` ENTRY class
-- `entryB Cv p = Cv·(|p|+1)³` by `entryB_le_kitQ` (under the E-room `p3 (d+1) ≤ E`, which `Verify4`'s cap supplies
-- through `p3_le_p4`) and `entryB_le_kitD` (`pow3_eq_p3`); the fragments' closed leaf/bin facts, which
-- `Frag1.formulaLen_{leaf,bin2,bin3}Fact_le` bound by `B·E`, through `BE_le_kitQ`; and the goal fact at the SINGLE
-- multiple through `goalFact_le_kitQ` (`Assemble.goalFact4_le_kitQ` states the quadruple). `len_nodeAxm` computes
-- `len (nodeAxm …) = 9` STRUCTURALLY — `Frag2.nodeAxm_ok` proves the same equation but only under its full
-- applicability hypotheses, which the size glue does not have at hand. Then the FIRST of the ten arms:
-- `axm_arm_len : len (vAxm' …) = len pro + 9` and `axm_arm_size : SizeOK (kitQ Cz B E) (kitD Cz (dlen (axm s p))) (vAxm' …)`
-- — the certificate's own class (`Verify3.AxmEntryOK'`) lifted and appended to `Frag2.sizeOK_nodeAxm`, whose
-- `dlen (leafCode …) ≤ D` side condition is exactly what §3's `dlen_leafCode_le'` was written to discharge.
#print axioms le_kitQ_factor
#print axioms BE_le_kitQ
#print axioms goalFact_le_kitQ
#print axioms entryB_le_kitQ
#print axioms entryB_le_kitD
#print axioms len_nodeAxm
#print axioms axm_hpd
#print axioms axm_arm_len
#print axioms axm_arm_size

-- U10 (Necessitation/Verify5, 2026-09-15): THE SIZE HALF, PART 3 — the two LEAF arms, `axL` and `verumIntro`.
-- `vAxL = proAxL ++ fragAxL` and `vVerum = fragVerum` (no prologue: `Prologue.layout_verum` reads the node's facts
-- straight off the layout). Both fragments are `head (four steps) ++ goalTailLeaf (five steps)`, so `len_fragAxL`
-- and `len_fragVerum` compute `9` structurally, exactly as `len_nodeAxm`; hence `axL_arm_len` and `verum_arm_len`.
-- The size halves need NO layout class: `proAxL = reidxL (certNeg …)` is HORN-ONLY (`Prologue.proAxL_ok`'s third
-- conjunct), so `Cert.sizeOK_of_hornOnly` places it at ANY class, and the fragments go through
-- `Frag1.sizeOK_fragAxL`/`sizeOK_fragVerum` with §4's landing lemmas (`BE_le_kitQ` for the closed `leafFact`,
-- `goalFact_le_kitQ` for the goal fact) and §3's `dlen_leafCode_le'` for the `dlen (leafCode …) ≤ D` condition.
#print axioms len_fragAxL
#print axioms len_fragVerum
#print axioms axL_arm_len
#print axioms verum_arm_len
#print axioms axL_arm_size
#print axioms verum_arm_size

-- U10 (Necessitation/Verify5, 2026-09-15): THE SIZE HALF, PART 4 — the REUSABLE CORE and the `wk`/`shift` tier.
-- Every remaining arm is `prologue ++ child ++ recovery ++ node`, and the prologue's size class is ALWAYS the
-- layout class `(layQ B B' D, layD N' B' D)` of `Prologue.sizeOK_pro*`. `layQ_le_kitQ`/`layD_le_kitD` land that
-- class in the kit class once and for all — which is exactly why the size oracle must CARRY `NumTableOK T N' B'`:
-- `Assemble.layQ_le`/`layD_le` need `N'`, `B'` as NUMBERS (the defect this file works around). TRAP: the cube step
-- of `layD_le_kitD` goes through `pow3_eq_p3` + `Verify3.p3_mono`; Mathlib's `pow_le_pow_left` does NOT exist at
-- this structure (machine-checked). The RECOVERY blocks `Frag1.goalElim` (five steps) and `Prologue.postIns`
-- (six steps) sit at the goal-fact class `4·|goalFact …|`, landed by `Assemble.goalFact4_le_kitQ` at ANY `D`, so
-- they never touch the layout class (`sizeOK_goalElim_kit`, `sizeOK_postIns_kit`). Then the `wk`/`shift` tier's
-- lengths: the nodes are nine steps structurally (`len_nodeWk`, `len_nodeShift`), and the SELECTORS split on the
-- empty child — `proWk0 ++ emptyFsetPi` is `7 + 4 = 11`, `proShift0 ++ reset0 ++ emptyFsetPi` is `11 + 8 + 4 = 23`
-- (`len_wkPro`, `len_shiftPro`, on `len_emptyFsetPi = 4` and `len_reset0 = 8`).
#print axioms layQ_le_kitQ
#print axioms layD_le_kitD
#print axioms sizeOK_goalElim_kit
#print axioms sizeOK_postIns_kit
#print axioms len_nodeWk
#print axioms len_nodeShift
#print axioms len_emptyFsetPi
#print axioms len_reset0
#print axioms len_wkPro
#print axioms len_shiftPro

-- U10 (Necessitation/Verify5, 2026-09-16): THE SIZE HALF, PART 5 — the `wk`/`shift` SELECTORS' sizes and the node
-- codes in the kit class. The selectors (`Verify2.wkPro`/`shiftPro`) split on the empty child, so their size
-- discipline needs BOTH branches: the empty one is closed Horn material (`Prologue.sizeOK_proWk0`/`sizeOK_proShift0`
-- hold at EVERY class; the two pieces `emptyFsetPi` and `reset0` had NO size lemma in the tree and get one here by
-- tag inspection — rows 81/157/82/84, and `layoutSteps0` + 42/43/158, all tag `0`), and the nonempty one is the
-- layout class of `Prologue.sizeOK_proWk`/`sizeOK_proShift`. The unary/binary NODE CODES land too: §3 bounds them by
-- `2·sum2D N' B' Dz` and `sum2D ≤ layD` absorbs one factor, so the doubling goes into the kit constant
-- (`2·(27N' + 525600B') ≤ Cz`) — `dlen_bin2Code_le_kitD`/`dlen_bin3Code_le_kitD` are what `Frag1`/`Frag2`'s
-- `sizeOK_node*` need for their `dlen (bin2Code …) ≤ D` side conditions at the non-leaf tags.
#print axioms sizeOK_emptyFsetPi
#print axioms sizeOK_reset0
#print axioms sizeOK_wkPro
#print axioms sizeOK_shiftPro
#print axioms dlen_bin2Code_le_kitD
#print axioms dlen_bin3Code_le_kitD

-- U10 (Necessitation/Verify5, 2026-09-16): THE SIZE HALF, PART 6 — the statement in the shape the package consumes.
-- `Package.lean` §1 names what the size glue must deliver: `SizeThm N' B' Cz`, i.e. `Assemble.VerifySizeOracle`
-- quantified over the models and tables with `NumTableOK T (N' : V) (B' : V)` RESTORED (the hypothesis
-- `Assemble.SizeOracle` drops and every prologue size lemma needs); `SizeThmAll` is `∀ N' B', ∃ Cz, SizeThm N' B' Cz`,
-- the quantifier ORDER being the bypass. `ArmHypsAll` lifts §2's named per-model hypothesis `ArmHyps` uniformly over
-- the models at a FIXED numeral table, and `verifyGraph''_size4_of_arms` IS `Package.SizeThm N' B' Cz` modulo it.
-- ARMS PROVED so far: `axm` (§4), `axL`/`verumIntro` (§5). The reusable machinery for the remaining seven is in
-- place — the layout-class landing (§6), the recovery blocks `goalElim`/`postIns` (§6), the `wk`/`shift` node and
-- selector lengths (§7) and selector sizes (§8), and the node codes in the kit class (§8). What remains is the
-- assembly of the seven non-leaf arms and the `Derivation.induction1 𝚷` recursion threading them.
#print axioms ArmHypsAll
#print axioms verifyGraph''_size4_of_arms

-- U10 (Necessitation/Verify5, 2026-09-16): THE SIZE HALF, PART 7 — the `wk` and `shift` ARMS (5 of 10 arms done).
-- The first two NON-LEAF arms, and the template for the remaining five: each list is
-- `selector ++ (child ++ (recovery ++ node))`, a right-nested `appendV` (`Verify2.lean` §5), so the LENGTH is
-- `len selector + (len L' + (5 + 9))` (`len_goalElim = 5`, §7's `len_nodeWk`/`len_nodeShift`) and the SIZES are
-- `sizeOK_appendV` over the four blocks: the selector at the LAYOUT class (§8's `sizeOK_wkPro`/`sizeOK_shiftPro`,
-- covering BOTH branches of the empty-child split) lifted by §6's `layQ_le_kitQ`/`layD_le_kitD`; the child from the
-- induction hypothesis; the recovery by §6's `sizeOK_goalElim_kit`; the node by `Frag1.sizeOK_nodeWk` /
-- `Frag2.sizeOK_nodeShift`, whose three side conditions are `formulaLen_bin2Fact_le` + §4's `BE_le_kitQ`, §8's
-- `dlen_bin2Code_le_kitD`, and §4's `goalFact_le_kitQ`. The kit class is stated at `kitD Cz (2 * d)` throughout,
-- matching `Verify4`'s `D = 2d` convention. TRAP: the recovery block's goal fact is at the CHILD's `dlen d'` while
-- the node's is at the PARENT's `dlen (wkRule s d')`, so the two term-length hypotheses are genuinely different.
#print axioms len_vWk_eq
#print axioms len_vShift_eq
#print axioms wk_arm_size
#print axioms shift_arm_size

-- U10 (Necessitation/Verify5, 2026-09-16): THE SIZE HALF, PART 8 — the `or` ARM and the binary nodes' lengths
-- (6 of 10 arms done). `vOr = proOr ++ (L' ++ (postIns ++ nodeOr))` — the four-block shape of §10 with
-- `Prologue.postIns` (SIX steps) as the recovery block in place of `goalElim` (five), so the tail contributes
-- `6 + 9`. The size halves differ from `wk`/`shift` only in the prologue (`Prologue.sizeOK_proOr`, which
-- additionally wants the two dossier hypotheses `DossF … p`/`… q` that `Prologue.layout_or` supplies at the glue
-- level) and in the recovery block (§6's `sizeOK_postIns_kit`). The three NON-LEAF node lengths are proved here
-- together: `nodeOr` sits on the UNARY tail (`goalTailUnary`), `nodeAnd` and `nodeCut` on the BINARY one
-- (`goalTailBinary`), and all three are `head (four) ++ tail (five) = 9`, the same structural computation as
-- `len_nodeAxm`; `len_nodeAnd`/`len_nodeCut` are advance work for the `and`/`cut` arms.
#print axioms len_nodeOr
#print axioms len_nodeAnd
#print axioms len_nodeCut
#print axioms len_vOr_eq
#print axioms or_arm_size

-- U10 (Necessitation/Verify5, 2026-09-16): THE SIZE HALF, PART 9 — the `and` and `cut` ARMS (8 of 10 arms done).
-- The two-child arms: `vAnd` is SEVEN blocks (`proIns ++ L₁ ++ postIns ++ proIns ++ L₂ ++ postIns ++ nodeAnd`) and
-- `vCut` is EIGHT (`proCutPre ++ cutPro ++ L₁ ++ postIns ++ cutPro ++ L₂ ++ postIns ++ nodeCut`); both nodes sit on
-- the BINARY tail, so their side conditions are `bin3Fact`/`bin3Code` (§8's `dlen_bin3Code_le_kitD`). Two new
-- landing lemmas: `sizeOK_proCutPre_kit` — `Prologue.sizeOK_proCutPre` lands in `(lenQ B' D + Q', lenD N' B' D + D')`
-- at ANY `Q'`, `D'`, NOT the layout class, so instantiate `Q' = D' = 0` and route `lenQ ≤ layQ` (`lenQ_le_layQ`, by
-- definition since `layQ = lenQ + sum2Q`); and `sizeOK_cutPro` — the `cut` selector splits on the EMPTY PARENT
-- (`proIns0` vs `proIns`), the third and last selector split in the file (§8 did the empty-CHILD splits). The second
-- `proIns`/`cutPro` of each arm runs in a LATER context, taken as separate hypotheses (the glue supplies them by
-- transport). TRAP: a context variable introduced only in a hypothesis is autobound AFTER the section's
-- `variable {V …}`, leaving its `V` a metavariable and stalling instance search ("typeclass instance problem is
-- stuck"); bind it in the binder list.
#print axioms lenQ_le_layQ
#print axioms lenD_le_layD
#print axioms sizeOK_proCutPre_kit
#print axioms sizeOK_cutPro
#print axioms len_vAnd_eq
#print axioms len_vCut_eq
#print axioms and_arm_size
#print axioms cut_arm_size

-- U10 (Necessitation/Verify5, 2026-09-16): THE SIZE HALF, PART 10 — the `all` and `exs` ARMS; ALL TEN ARMS PROVED.
-- Both quantifier arms have the FOUR-block shape of `or` (`Verify2.lean` §5): `proAll ++ (L' ++ (postIns ++ nodeAll))`
-- and `proExs ++ (L' ++ (postIns ++ nodeExs))`, so their lengths are `len pro + (len L' + (6 + 9))` exactly as
-- `len_vOr_eq`, and the size halves are the prologue at the LAYOUT class (`Prologue.sizeOK_proAll`/`sizeOK_proExs`,
-- whose extra `hEQ`/`hiE` hypotheses are the QUADRATIC E-rooms of the certification blocks) lifted by §6, the child
-- from the induction hypothesis, §6's `sizeOK_postIns_kit`, and the node. The two nodes differ in their tail:
-- `nodeAll` sits on the UNARY one (`bin2Fact`/`bin2Code`, the child's `dlen` alone), `nodeExs` on the BINARY one
-- (`bin3Fact`/`bin3Code`, with `Lt = termLen t` as the second summand — the witness term's length enters the node's
-- arithmetic). With these, ALL TEN arms have standalone size and length lemmas: `axm` (§4), `axL`/`verumIntro` (§5),
-- `wk`/`shift` (§10), `or` (§11), `and`/`cut` (§12), `all`/`exs` (§13). What remains is the `Derivation.induction1 𝚷`
-- recursion threading them, which discharges `ArmHyps`/`ArmHypsAll`.
#print axioms len_nodeAll
#print axioms len_nodeExs
#print axioms len_vAll_eq
#print axioms len_vExs_eq
#print axioms all_arm_size
#print axioms exs_arm_size

-- U10 (Necessitation/Verify5, 2026-09-16): THE SIZE HALF, PART 11 — the selectors' lengths as BOUNDS; the length
-- gap CLOSED. §7's `len_wkPro`/`len_shiftPro` are branch EQUATIONS (`if memberList c = 0 then 11 else …`) and the
-- recursion needs a single `≤` covering both branches; `cutPro` had NO length lemma at all. All three are supplied
-- here in the `D`-shape the induction carries: `len_wkPro_le ≤ 44·D + 11` (empty branch the literal `11` =
-- `proWk0 ++ emptyFsetPi` = `7 + 4`, the other `Prologue.len_proWk_le`'s `44·setLen c + 7`); `len_shiftPro_le ≤
-- 62·D + 23` (empty branch `23` = `proShift0 ++ reset0 ++ emptyFsetPi` = `11 + 8 + 4`, the other
-- `len_proShift_le`'s `61·setLen c + setLen s + 20`, so BOTH size hypotheses are consumed); and `len_cutPro_le ≤
-- 55·D + 13` — THE MISSING ONE, whose split is on the EMPTY PARENT, so its branches are `len_proIns0_le`'s
-- `49·setLen (insert p 0) + 13` and `len_proIns_le`'s `55·setLen (insert p s) + 12`; the bound takes the larger
-- coefficient from one and the larger constant from the other, and the empty-parent branch needs its OWN size
-- hypothesis (`setLen (insert p 0) ≤ D`), since `insert p 0` is not `insert p s`.
#print axioms len_wkPro_le
#print axioms len_shiftPro_le
#print axioms len_cutPro_le

-- U10 (Necessitation/Verify5, 2026-09-16): THE SIZE HALF, PART 12 — three lemmas the RECURSION needs. The arm
-- lemmas of §§4–13 conclude at the class `kitD Cz n` with `n` the node's OWN `dlen`, while the recursion's motive
-- carries `kitD Cz (2 * dlen ρ)` (the `D = 2d` convention of `Verify4`, which §8's `dlen_bin2Code_le_kitD` and
-- `dlen_bin3Code_le_kitD` are already stated at); widening one to the other is `kitD_mono` plus `le_two_mul_self`.
-- The third, `dlen_leafCode_le_kitD`, is the `leafCode` analogue of §8's two, with NO doubling constant (§3 bounds
-- `leafCode` by a SINGLE `sum2D`, not the doubled one). TRAP: in its chain the size argument is pinned at `Dz` by
-- `sum2D_le_layD`, so `layD_le_kitD` there takes `le_rfl`, NOT the `d ≤ 2 * d` widening — that step happens
-- afterwards, through `kitD_mono`.
#print axioms kitD_mono
#print axioms le_two_mul_self
#print axioms dlen_leafCode_le_kitD

-- U10 (Necessitation/Verify5, 2026-09-16): §15, TWO LEMMAS ADDED for the recursion — the DOUBLING MISMATCH and its
-- fix. Scoping the ten-arm recursion (Part 16) showed the ten motive wrappers conclude at `kitD Cz (2·dlen ρ)` while
-- `ArmHyps`/`Assemble.VerifySizeOracle` demand the UNDOUBLED `kitD Cz (dlen ρ)`. `kitD Cz z = Cz·(z+1)³` is
-- INCREASING in `z`, and `kitD_mono` and `SizeOK.mono` both weaken only UPWARD, so nothing in the tree bridged them:
-- the doubling is a genuine strengthening of the size class, not a notational difference. `kitD_two_mul_le` absorbs
-- it into the CONSTANT instead — `2d + 1 ≤ 2(d + 1)`, so `Cz·(2d+1)³ ≤ Cz·(2(d+1))³ = 8·Cz·(d+1)³` — giving
-- `kitD Cz (2·d) ≤ kitD (8·Cz) d`; since `ArmHypsAll` quantifies `Cz` AFTER the fixed naturals `N'`, `B'`, arming the
-- recursion at `8·Czv` costs nothing and leaves `ArmHyps` BYTE-IDENTICAL, which `Package.lean` requires.
-- `kitQ_mono_const` is the `Q`-side companion (monotonicity in the constant). It did NOT exist anywhere in the tree:
-- §4's family (`le_kitQ_factor`, `BE_le_kitQ`, `goalFact_le_kitQ`, `entryB_le_kitQ`) all LAND a quantity in the class
-- and none of them varies the constant.
#print axioms kitD_two_mul_le
#print axioms kitQ_mono_const

-- U10 (Necessitation/Verify5, 2026-09-16): THE SIZE HALF, PART 13 — the per-arm MOTIVE WRAPPERS begin (`axL`).
-- TRAP 15 measured that filling one arm INSIDE the ten-arm `Derivation.induction1` body does not converge (>40 min
-- on the cheapest arm, against ~10 s standalone). The restructuring is one TOP-LEVEL theorem per arm, taking the
-- induction's binders and the cap as explicit hypotheses and concluding the MOTIVE at that node; the recursion body
-- then becomes ten one-line applications. **TRAP 16 — the actual cost centre, and the fix.** The blowup is NOT the
-- induction context: it is `isDefEq` searching for the arm lemma's IMPLICIT arguments (`is`, `il`, `ip`, `inp`,
-- `L`, `n`, …) against the large unfolded list term. Pinning them by name turns that search into a check. Measured
-- on `axL_wrapper`: unpinned, `isDefEq` timeout at 2 000 000 heartbeats after 73 s; PINNED, green in 5 s — the same
-- content, a >480× collapse against the in-body figure. Every remaining wrapper must pin its arm lemma's implicits
-- the same way. The wrapper also needs `maxHeartbeats 2000000` (the default 200 000 is not enough even pinned) and
-- its constant hypotheses in the SHAPE the arithmetic lemmas expect — `lin_le_p3` wants `(12 : V) + 9 ≤ Czv`, not
-- `((21 : ℕ) : V) ≤ Czv`; a cast mismatch there reads as an application type error, not as a numeric one.
#print axioms axL_wrapper

-- U10 (Necessitation/Verify5, 2026-09-16): §16.1 — the `verumIntro` WRAPPER, and the confirmation that the template
-- GENERALISES: green in 5 s, the same cost as `axL` (2 of 10 wrappers). `vVerum = fragVerum` alone (no prologue),
-- so there is no `HornOnly` block and no `proAxL_ok` destructuring — just the four E-rooms and `verum_arm_size`
-- with its implicits pinned per TRAP 16. **TRAP 17 — `rw [← hdd]` must come AFTER the `unfold`.** The wrapper
-- abbreviates `d = dlen TAct (…)` and rewrites it through the goal in bulk at the top; `unfold vVerum` then
-- RE-EXPOSES the raw `dlen` in the fragment's `n` position, so the pinned `n := d` no longer matches and the
-- application fails on a `SizeOK … (fragVerum … d)` versus `SizeOK … (fragVerum … (dlen TAct (verumIntro s)))`
-- mismatch. Repeating the rewrite after the unfold fixes it.
#print axioms verum_wrapper

-- U10 (Necessitation/Verify5, 2026-09-16): §17 — the E-ROOM HELPER FAMILY. Part 5 spent its whole round on
-- hand-built inequality chains: every wrapper's `hEpro`/`hiEpro`/`hnE`/`hbn` is the SAME `capE4'`+`lin_cap`+`hCk`
-- composition at a different coefficient triple, and each hand-rolling went wrong differently (a leading `0 +`
-- blocking `ring`, a mis-associated `le_of_add_eq'`, `44 + 25` written as `65`). The three shapes are factored
-- once: `eroom_lin hE hCk a b c _ : (a:V)·D + (b:V)·‖D‖ + (c:V) ≤ E` — the general LINEAR room, subsuming the
-- prologue room (13,18,12), the node room (0,18,7), the insert room (14,0,5) and every other `lin_cap` chain;
-- `eroom_bnum hE hCk hn : termLen (bnum n) ≤ E` for `n ≤ D` — parent's and child's `dlen` alike; and
-- `eroom_off hE hCk hx c _ : x + (c:V) ≤ E` for `x ≤ D` — the goal-fact offset shape. USAGE: the coefficients
-- carry ℕ-casts so the constant side discharges by `norm_num` against `hCk`; a call site wanting the literal
-- `V`-shape follows with `push_cast at this`, and for a triple with `a = 0` additionally
-- `rw [zero_mul, zero_add] at this` — that leading zero is exactly what blocked `ring` when these were hand-rolled.
#print axioms eroom_lin
#print axioms eroom_bnum
#print axioms eroom_off

-- U10 (Necessitation/Verify5, 2026-09-16): §18 — the `wk` MOTIVE WRAPPER (3 of 10), the first NON-LEAF one.
-- Written UNABBREVIATED per TRAP 18 (`wk_arm_size` hard-wires `dlen TAct (wkRule s d')` and `dlen TAct d'` in its
-- hypothesis TYPES), with the arm lemma's implicits pinned per TRAP 16 and every E-room from §17's helper family —
-- `eroom_lin` at (13,18,12), (14,0,5) and (0,18,7), `eroom_bnum` for the child's and the parent's `dlen`. The two
-- goal-fact offsets and the length half all close the same way: a linear term plus the child's `Czv·p4 (dlen d')`,
-- absorbed by `Bounds.rec1₄` at `hdeq : dlen (wkRule s d') = dlen d' + (setLen s + 1)`. RESIDUAL (Part 6):
-- `lin_le_p3` concludes at `1 * D + c`, so its use in `hgE` pins `(a := 1) (b := 2)` and rewrites by `one_mul`;
-- where the coefficient is already a literal (`45 *`, `44 *`) no rewrite is needed. Transcribed LITERALLY in one
-- pass (Edit, no scripting) and green in 5 s at the first attempt — the two prior scripted splices each cost a round.
#print axioms wk_wrapper

-- U10 (Necessitation/Verify5, 2026-09-16): §19 — the `shift` MOTIVE WRAPPER (4 of 10), the `wk` wrapper's twin.
-- `shift_arm_size` differs from `wk_arm_size` in three places only: it wants the child's `IsFormulaSet` and the
-- shift equation (`hc`, `hsc : s = setShift LAct (fstIdx d')`) in place of `wk`'s `hsub`, and its insert room is
-- `0 + 16·D + 8` rather than `0 + 14·D + 5`. `dlen_shiftRule` has the SAME shape as `dlen_wkRule`
-- (`setLen s + dlen d + 1`), so `hdeq`, `hyd` and `hLn` transcribe unchanged. The constants move with
-- `len_shiftPro_le ≤ 62·D + 23` (against `wk`'s `44·D + 11`): the length half needs `62 + 37 = 99` and `hgE2`
-- needs `63·D + 28`, i.e. `91`. Transcribed literally in one pass and green in 7 s at the first attempt.
#print axioms shift_wrapper

-- U10 (Necessitation/Verify5, 2026-09-16): §20 — the GENERAL E-room, and why the offset shapes need NO bespoke
-- helper. The `or`/`and`/`cut` arms want rooms over `memTop`/`descCountF`/`proSig` offsets (e.g. `or`'s
-- `hipE : memTop … (p ^⋎ q) 0 + descCountF … 0 q + 1 + 14·D + 6 ≤ E`), which look like a new shape; but each
-- summand's own bound is already LINEAR in `D` (`Prologue.memTop_le ≤ i + 6·D + 1`,
-- `Verify2.descCountF_le_of_len ≤ 2·D`, `Prologue.proSig_le ≤ 6·D + 1`), so every such room COLLAPSES to `a·D + c`
-- once the summands are bounded — `hipE` to `22·D + 8`, `hiqE` to `14·D + 6`. So the widening wanted was not a
-- `memTop`-shaped helper but the general one: `eroom_of_le` takes `X ≤ a·D + c` to `X ≤ E`, subsuming `eroom_lin`
-- at `b = 0` and every offset room of the remaining arms. USAGE: bound each summand by its own `k·D + c`, sum the
-- coefficients, then `refine eroom_of_le hE hCk a c (by norm_num) ?_; push_cast` and close with `calc … := by ring`;
-- `proSig_le` itself needs an E-room at `(13, 18, 8)`, supplied by `eroom_lin`. Validated against `or`'s actual
-- `hipE` composition before landing.
#print axioms eroom_of_le

-- U10 (Necessitation/Verify5, 2026-09-16): §21 — the `or` MOTIVE WRAPPER (5 of 10). The first arm with a `postIns`
-- recovery block (SIX steps, against `goalElim`'s five) and with DOSSIER hypotheses, but still one child and one
-- context, so it transcribes like `wk`/`shift` with three differences: the tail is `6 + 9 = 15` and
-- `Prologue.len_proOr_le ≤ 110·setLen (insert p (insert q s)) + 25` (the `setLen` bounded by
-- `setLen_child_le_dlen_orIntro`), so the length half's constant is `110 + 40 = 150`; the two OFFSET rooms go
-- through §20's `eroom_of_le` after their summands are bounded — `hipE` collapses to `22·D + 8`
-- (`memTop_le ≤ 0 + 6·D + 1`, `descCountF_le_of_len ≤ 2·D`) and `hiqE` to `14·D + 6`; and `hgE2` carries two
-- `proSig` terms, each `≤ 6·D + 1` by `Prologue.proSig_le`, which itself needs an E-room at `(13, 18, 8)`.
-- `dlen_orIntro` has the same `setLen s + dlen d' + 1` shape as `wk`/`shift`, so `hdeq`/`hyd`/`hLn` are unchanged.
-- The dossiers `hDp`/`hDq` come from `Prologue.layout_or` at the node's own layout. TRAP: `hgE2`'s summed constant
-- is `13·D + 9` (paired with `22`), not `13·D + 10` — the IDE's residual goal gives the true normal form, and an
-- exact `= by ring` step is safer than an inequality with invented slack.
#print axioms or_wrapper

-- U10 (Necessitation/Verify5, 2026-09-16): §22 — the `and` MOTIVE WRAPPER (6 of 10), the first TWO-CHILD arm.
-- `dlen_andIntro` is `setLen s + dlen dp + dlen dq + 1`, so `hdeq` takes the `d = y₁ + y₂ + m` shape that
-- `Bounds.rec2₄` wants — and TRAP 19: EVERY room in a two-child arm must use `rec2₄`, not `rec1₄`, even the ones
-- that mention only ONE child (`hiE₂`, `hipE₂`, `hgE₁`, `hgE₂`). `rec1₄` wants `d = y + m`, and a two-child `dlen`
-- cannot be written that way — the other child's `dlen` has nowhere to go; the residual goal shows it as
-- `… + dlen dq = …` with the summand simply missing. Each such room adds the absent child's `Czv·p4` as slack via
-- `le_of_add_eq'` and then closes with `rec2₄`. Seven blocks, so the length half is two
-- `Prologue.len_proIns_le ≤ 55·setLen (insert · s) + 12` (the `setLen`s by `setLen_child_le_dlen_andIntro_left`/
-- `_right`) plus `6 + 6 + 9 = 21`, i.e. `110·D + 45 = 155`. The later-context hypotheses `hΓ₃`/`hLay₃`/`hDq₃` are
-- EXPLICIT wrapper hypotheses (the Part-8 finding), `hDp` comes from `Prologue.layout_and`, and
-- `shiftsV L₁ ≤ Czv·p4 (dlen dp)` (via `shiftsV_le_len`) bounds the later-context rooms. Constants, all read off
-- the residual goals rather than guessed: `hipE₁` `16·D + 6`, `hiE₂` `20·D + 9`, `hipE₂` `20·D + 10`,
-- `hgE₃` `13·D + 11`.
#print axioms and_wrapper

-- U10 (Necessitation/Verify5, 2026-09-16): §23 — the `cut` MOTIVE WRAPPER (7 of 10), GREEN AT THE FIRST ATTEMPT.
-- `and`'s shape with a `proCutPre` prefix and the two `cutPro` selectors, so EIGHT blocks and — being two-child —
-- every room on `Bounds.rec2₄` per TRAP 19, which is precisely why it needed no repair hunks: the trap found in
-- `and` told the transcription what to do in advance. Length half: `Prologue.len_proCutPre_le ≤ 64·|p|` plus TWO
-- `§14.len_cutPro_le ≤ 55·D + 13` plus `6 + 6 + 9 = 21`, i.e. `174·D + 47 = 221`. The rooms are stated over
-- `mShift`/`mLen` rather than `memTop`/`descCountF`, bounded by `Prologue.mShift_le ≤ 4·|x|` and
-- `mLen_succ_le : mLen + 1 ≤ 2·|x|`, with `CutV.formulaLen_neg` turning `|neg p|` into `|p|`; constants
-- `hiE₁ 22·D+5`, `hipE₁ 14·D+4`, `hiE₂ 28·D+9`, `hipE₂ 16·D+8`, `hgE3 21·D+11`. TRAP 20: `cut_arm_size` wants
-- `Layout0` at BOTH `cutPro` offsets (`hLay0₁`, `hLay0₄`), and `NodeLay.layout` only supplies `Layout … s 0` —
-- there is no lemma producing `Layout0` at a shifted offset, so those, like the later-context `hΓ₄`/`hLay₄`/`hDnp₄`
-- and the `proCutPre` context `hΓc`, are EXPLICIT wrapper hypotheses for the recursion to discharge.
#print axioms cut_wrapper

-- U10 (Necessitation/Verify5, 2026-09-16): §24 — the `all` MOTIVE WRAPPER (8 of 10), the first QUADRATIC arm and
-- the first whose `D` is NOT the node's `dlen`. TRAP 21: `all` runs at `D := 2·dlen (allIntro s p d')`, forced
-- twice over — `hspD : formulaLen (shift p) ≤ D` holds only at TWICE the `dlen`
-- (`Primitives.formulaLen_shift_le ≤ 2·|p|`, `|p| ≤ |∀p| ≤ dlen` by `formulaLen_all_le_dlen_allIntro`), and
-- `Bounds.allEQ_p3`/`alliE_p3` are stated at exactly `D = 2d`. The motive's `d` stays `dlen (allIntro …)`, so
-- `hDd` is `le_rfl` and `hsD`/`hcD` weaken by `le_two_mul_self`. NO new helper was needed (Part 11's finding): the
-- two quadratic rooms go through `allEQ_p3 ≤ 27·p3 (d+1)` and `alliE_p3 ≤ 96·p3 (d+1)`, lifted by `p3_le_p4` and
-- capped by `capE4`. The CUBIC length half goes through `len_proAll_le_cubic ≤ 402·p3 (D+1)` at `D = 2·dlen`:
-- `p3_mono` takes `2d+1 ≤ 2(d+1)`, `p3_two_mul` gives `8·p3 (d+1)`, `p3_succ_le` gives `64·p3 d`, so the constant
-- is `402·64 = 25728`, capped at `25743`. `hgE2` carries `allCertSig`, bounded by `Prologue.allCert_ok`'s SIXTH
-- conjunct (`≤ 4·D + 2 + 2·((1+D)(1+D+1))·D`), plus three `proSig ≤ 6·D + 1` — one at `setShift s`, via
-- `hs.setShift` and `one_le_len_memberList_setShift` — and closes against `alliE_p3` at constant `768`.
-- TRAP 22: that closing step is a genuine `≤`, NOT an `=`: the summed bound normalises to `13 + 56·d + 24·d² +
-- 16·d³` while `alliE_p3`'s left side is `20 + 88·d + 24·d² + 16·d³` — cubic and quadratic terms agree, so the
-- slack is exactly `7 + 32·d`, READ OFF the residual goal rather than guessed.
#print axioms all_wrapper

-- U10 (Necessitation/Verify5, 2026-09-16): §25 — the `exs` MOTIVE WRAPPER (9 of 10), mechanically `all`'s twin at
-- `D := 2·dlen (exsIntro s p t d')` (TRAP 21 again), with four differences: the quadratic rooms carry `(1 + D + D)`
-- rather than `(1 + D + 1)`, matching `Bounds.exsEQ_p3 ≤ 43·p3 (d+1)` and `exsiE_p3 ≤ 112·p3 (d+1)`;
-- `dlen_exsIntro = setLen s + termLen t + dlen d' + 1`, so `hdeq` is `dlen d' + (setLen s + termLen t + 1)` — the
-- WITNESS TERM's length joins the `rec1₄` remainder; the arm wants `ht`/`htD` (`termLen_le_dlen_exsIntro`); and
-- `hgE2` carries `exsSig`, bounded by `Prologue.exsCert_ok`'s FIFTH conjunct
-- (`≤ 2·((1+D)(1+D+D))·D + 6·D + 1`), whose own `hptD` comes from `formulaLen_substs1_le_dlen_exsIntro`. The cubic
-- length half is `len_proExs_le_cubic ≤ 256·p3 (D+1)` at `D = 2·dlen`, so `256·64 = 16384`, capped at `16399`.
-- TRAP 23: when `le_of_add_eq'` supplies the slack, the slack is folded INTO the left side before normalisation, so
-- each attempt shows a DIFFERENT residual goal and chasing it term-by-term loops. Two readings pin it
-- algebraically: `c := 40·d` gave left `8 + 70·d`, `c := 12 + 14·d` gave `20 + 44·d`, target `20 + 84·d`; hence
-- base `8 + 30·d` and the true slack `12 + 54·d`. Solve the two equations rather than iterating a third time.
#print axioms exs_wrapper

-- U10 (Necessitation/Verify5, 2026-09-16): §26 — the `axm` MOTIVE WRAPPER, the TENTH AND LAST, and the only one
-- whose prologue the wrapper does NOT build: `pro` arrives from the shifted CERTIFICATE TABLE, so its three facts
-- (`SizeOK (entryB Cv p) (entryB Cv p) pro`, `len pro ≤ entryB Cv p`, `shiftsV pro ≤ entryB Cv p`) are EXPLICIT
-- wrapper hypotheses, which the recursion supplies by destructuring `AxmTableOK'` at the node's entry exactly as
-- `Verify4`'s `axm` arm does. Written UNABBREVIATED per TRAP 18: `axm_arm_size` hard-wires `dlen TAct (axm s p)` in
-- `hp3E`/`hgoalE`/`hbn`/`hleaf`/`hLn`/`hnE` and in its conclusion's class, so no `d` abbreviation can be pinned in.
-- The arm concludes at `kitD Cz (dlen (axm s p))` while the motive wants `kitD Czv (2·dlen)`, so the result is
-- widened by `.mono le_rfl (kitD_mono (le_two_mul_self _))` — the one place a wrapper CHANGES the size class.
-- `hleaf` CANNOT use §15's `dlen_leafCode_le_kitD` (that is stated at `kitD Cz (2·d)`, the wrong shape here); it
-- takes the raw route `dlen_leafCode_le' htblN hLn le_rfl` → `sum2D_le_layD` → `layD_le_kitD le_rfl hCD`, landing
-- at `kitD Czv (dlen)` exactly. The length half is LINEAR, not cubic: `axm_arm_len` gives `len pro + 9`, and
-- `entryB Cv p = Cv·p3 (|p|+1)` is pushed to `dlen+1` by `axm_hpd` and then to `8·Cv·p3 dlen` by `p3_succ_le`, so
-- the single constant is `8·Cv + 9 ≤ Czv` — no `capE4`, no `rec1₄`/`rec2₄` room at all, since `axm` is a LEAF.
#print axioms axm_wrapper

-- U10 (Necessitation/Verify5, 2026-09-16): §26.1 — A NODE CONTEXT EXISTS AT EVERY SEQUENT, built from the EMPTY
-- context. The recursion's arms hand each wrapper a `Γ` with `NodeLay walkPieces certPieces T Γ s` at the node's own
-- sequent (the wrappers feed `hLay.layout` to `proAxL_ok`/`sizeOK_wkPro`/`layout_or`/`layout_and`), and with a
-- CONTEXT-FREE motive (TRAP 24) nothing threads one through the induction — so each arm BUILDS one. Nonempty
-- sequent: `layoutSteps_ok` AT `Γ := 0` already concludes `Layout … (finalCtx 0 (layoutSteps …)) s 0`, so
-- `NodeLay`'s first disjunct is immediate. Empty sequent: the second disjunct wants `Layout0 … Γ 0` AND
-- `fsetPiFact (^&1) ∈ Γ`; `layoutSteps0_ok` gives the former, and `Layout0`'s OWN second conjunct at `i = 0` IS
-- `eqFactB (^&1) 𝟎` — exactly `emptyFsetPi_ok`'s precondition — so appending `emptyFsetPi` gives the latter, with
-- `Layout0.mono` carrying the layout across on that lemma's context-monotonicity conjunct. The two branches split on
-- `memberList s = 0` via `eq_zero_of_memberList_eq_zero`. THE POINT: the obligation is DISCHARGEABLE, not merely
-- relocatable — no `∃ Γ` hypothesis is added to `ArmHyps` or `VerifySizeOracle`, which stay byte-identical.
#print axioms nodeCtx_exists

-- U10 (Necessitation/Verify5, 2026-09-16): §27 — THE TEN-ARM RECURSION, `Verify4.verifyGraph''_ok4`'s shape with
-- `len`/`SizeOK` in place of `shiftsV`: one `Derivation.induction1 𝚷` whose arms are one-line applications of
-- §§16–26's motive wrappers (TRAP 15 — the constructions must NOT sit in the induction body).
-- **TRAP 24 — THE MOTIVE IS CONTEXT-FREE.** `Verify4`'s motive carries `∀ L Γ, … → NodeLay … Γ (fstIdx ρ) → …`
-- because its conjuncts MENTION the context (`ListOK tbl E 9 Γ L`, `… ∈ finalCtx Γ L`). `ArmHyps`' two conjuncts do
-- NOT: `len L ≤ Cz·(dlen ρ+1)^4` and `SizeOK (kitQ …) (kitD …) L` are context-free. Copying `Verify4`'s binders made
-- the induction hypothesis UNUSABLE at a child — discharging it would need a `NodeLay` at the CHILD's sequent, and
-- every `NodeLay` in the tree (`Verify2` 2295/2511/2578/2867, `Assemble` 698) is `Or.inl ⟨one_le_len_memberList_insert
-- _, layC⟩` from a `Layout` at a PROLOGUE's `finalCtx`, with no from-nothing constructor. Dropping `Γ` from the
-- motive removes the obligation outright: the `ih` then applies to a child directly, with NO context argument.
-- Diagnosed by compiling a motive SKELETON (arms left unfilled) rather than by reading — the structural question was
-- settled in seven seconds after three rounds of reading had not settled it.
-- The per-arm E-room for §26.1 is `capE4' hE he1 (hCk 39 _) (lin_cap 13 18 8 D)` and `capE4' hE he1 (hCk 2 _) _`,
-- with `a` supplied POSITIONALLY — `refine capE4' hE he1 ?_ ?_` leaves `capE4'`'s implicit `a` unsolved.
-- Eight arms were discharged from the banked wrappers directly; `and` and `cut` were briefly NAMED HYPOTHESES
-- (`hAndArm`, `hCutArm`) because `and_arm_size` binds `Γ₃` and `cut_arm_size` binds `Γ₄`/`Γc` in their OWN
-- signatures, at SHIFTED offsets (`1 + proSig (insert p s) + shiftsV L₁ + 2`, `mShift p + mShift (neg p) + …`)
-- that §26.1's offset-0 construction does not reach. Both are now DISCHARGED by the transport chains
-- (§§26.4–26.6 for `and`, §§26.7–26.8 for `cut`), and `armHyps_of_arms` takes no arm hypothesis at all.
-- U10 (Necessitation/Verify5, 2026-09-16): the `Ck` THREADING. `armHyps_of_arms` briefly carried
-- `hCk5 : ((128655 : ℕ) : V) + 5·Cv ≤ Czv`, naming `Verify4.verifyGraph''_ok4`'s constant as a LITERAL. That binder
-- is unusable: `verifyGraph''_ok4 : ∃ Cs Ck : ℕ, ∀ …`, so `128655` is a witness chosen inside its own proof and
-- never appears in the statement — after `obtain ⟨Cs, Ck, h⟩` the `Ck` is OPAQUE and no literal can discharge its
-- E-room. Replaced by `{Ck : ℕ}` in the implicit group plus `hCkDom : ((Ck : ℕ) : V) + 5·(Cv : V) ≤ Czv`, the
-- `Assemble.verifyKit'''_of` precedent (obtain the existential FIRST, choose the constant as a function of it).
-- The blast radius is this theorem alone: `Ck` occurs only in the proof obligation, never in the conclusion, so
-- `ArmHyps`, `ArmHypsAll` and `verifyGraph''_size4_of_arms` are byte-identical (diff: 2 insertions, 2 deletions,
-- both on binder lines).
-- FOURTH instance of one pattern: a constant fixed BEFORE the quantifier ranging over what it must dominate
-- (`SizeOracle`'s table, `ArmHyps`' `Cv`, `VerifySizeOracle`'s `Cv`, now `Verify4`'s `Ck`). Order constants LAST.
-- The `Ck` threading needed a second step: `hCkDom` alone names a constant the body cannot connect to anything,
-- because an `obtain ⟨Cs, Ck', h⟩ := verifyGraph''_ok4` INSIDE the body introduces a FRESH `Ck'` unrelated to the
-- signature's `Ck`. So `armHyps_of_arms` also takes `hV4`, `verifyGraph''_ok4`'s CONCLUSION at the signature's
-- `Cs`/`Ck` — the `Assemble.vList_full` precedent, which threads `hV` the same way. The caller supplies both by its
-- own `obtain ⟨Cs, Ck, hV4⟩ := verifyGraph''_ok4`; nothing applies `armHyps_of_arms` yet, so the cost is zero today.
-- Probe-verified before transcription: with `hV4` at the signature's `Ck`, the child triple extracts and `hE4`
-- follows from `hCkDom` plus `p4_mono (le_trans hy₁ le_self_add)`.
-- **`hAndArm` IS DISCHARGED.** The `and` arm no longer takes the arm's conclusion as a hypothesis: it proves it,
-- by chaining §26.4 `and_input` → §26.5 `and_cross` → §26.6 `and_trans` → `rwa [finalCtx_appendV]` → §22
-- `and_wrapper`, with two `have`s the arm lacked (`setLen_child_le_dlen_andIntro_left`,
-- `formulaLen_q_le_dlen_andIntro`) and the two `postIns` rooms from §26.3 (`and_roomS`, `and_roomC`).
-- The child's `ListOK`/`NoDrop'`/goal fact come from `hV4` INSTANTIATED AT `Γ₁` — the context `and_input` itself
-- produces — not at a separately built one: `and_cross` wants them at `Γ₁`, and `hV4` is universally quantified
-- over the context, so drawing them there costs nothing and removes a second `nodeCtx_exists` call. The child
-- `NodeLay` at `Γ₁` is `Or.inl ⟨one_le_len_memberList_insert _ _, h2⟩` after `hdp.1` rewrites `fstIdx dp`, the
-- `Verify2`:2295 idiom, with `h2` being `and_input`'s SECOND component.
-- A first attempt drew the child facts at a separate `Γc` and failed on exactly that mismatch — the fix was
-- reordering, not a bridge lemma.
-- `hCutArm` is DISCHARGED too (§§26.7–26.8): `armHyps_of_arms` is UNCONDITIONAL — its binders are the tables,
-- the constants, `hV4` and `hA`, with no arm hypothesis of any kind.
-- TRAP 31: `set_option … in` binds to the NEXT declaration, so a sentinel planted BETWEEN the `set_option` and its
-- theorem steals the raise and the theorem then elaborates at the default 200000 heartbeats — here the motive's
-- `simp only [VerifyGraph'', p4, kitQ, kitD]; definability` times out, which reads as a real failure but is an
-- artifact of the probe's placement. Sentinels go ABOVE the `set_option` line, never between it and its
-- declaration; and a sentinel run that changes the file's options is not a valid check of the unmodified file.
#print axioms armHyps_of_arms

-- U10 (Necessitation/Verify5, 2026-09-16): §26.2 — THE `and` TRANSPORT CHAIN'S E-ROOMS, the first banked piece of
-- the `and` chain. `Prologue.proIns_ok`, `proSig_le`, `memTop_le`, `descCountF_le_of_len` and `postIns_ok` each want
-- a LINEAR room (`13·D + 18·‖D‖ + 12`, `i + 14·D + 5`, `ip + 8·D + 4`, …), while the recursion's arms carry only the
-- `p4` cap `Czv·p4 (dlen ρ + 1) ≤ E`. Each lemma bridges that by ONE `Bounds.capE4'` at its own constant, with the
-- offset inputs at the bounds the tree actually delivers: `memTop_le ≤ i + 6·D + 1` (so `≤ 6·D + 1` at `i = 0`),
-- `descCountF_le_of_len ≤ 2·D` (hence `ir₀ + cq + 1 ≤ 8·D + 2`), `proSig_le ≤ 6·D + 1`.
-- Constants: `43`, `39`, `26` (folded `20·D + 6`), `22` (folded `16·D + 6`).
-- TRAP 25: `capE4'`'s `a` is IMPLICIT and `refine capE4' hE he1 ?_ ?_` leaves it unsolved — the `ha` argument must
-- be supplied POSITIONALLY. Verified by probe before transcription.
-- The two REMAINING rooms (`postIns_ok`'s `hsE`/`hcE`) carry the CHILD's shift and are NOT in this commit:
-- `hsE`'s linear part is `D + 4`, which fits under one `p3 (D+1)` (`lin4_le_p3succ`, `D+4 ≤ p3 (D+1)` at `1 ≤ D`),
-- but `hcE`'s is `6·D + 4`, and `6·D + 4 ≤ p3 (D+1)` is FALSE at `D = 1` (`10 ≤ 8`) — so that room needs either
-- `2 ≤ D` or a doubled cap, which is the next piece rather than a proof-search failure.
#print axioms and_room13
#print axioms and_room8
#print axioms and_roomI
#print axioms and_roomIP

-- U10 (Necessitation/Verify5, 2026-09-16): §26.3 — THE TWO CHILD-CARRYING ROOMS. `postIns_ok`'s `hsE`/`hcE` carry
-- the CHILD's shift `sv` on the left, so they are not pure linear caps; both still close at the arm's OWN single cap
-- `Czv·p4 (D+1) ≤ E`, by splitting it with `Bounds.p4_split D 1 : p4 D + p3 (D+1) ≤ p4 (D+1)` — the child term
-- under `p4 D` (`child_bound4`), the linear part under the spare `p3 (D+1)`.
-- The two differ in whether that spare suffices: `hsE`'s linear part is `D + 4`, covered from `1 ≤ D`
-- (`lin4_le_p3succ`, `5 ≤ 8` at `D = 1`); `hcE`'s is `6·D + 4`, and `6·D + 4 ≤ p3 (D+1)` is FALSE at `D = 1`
-- (`10 ≤ 8`). It needs `2 ≤ D`, which the STRICT DESCENT supplies: `1 ≤ y` (`one_le_dlen`) and `y + 1 ≤ D`
-- (`dlen_dp_succ_le_andIntro`), both already bound in the `and` arm — so the room is CALLABLE at the single cap,
-- with no doubled cap and no second constant. An earlier doubled-cap form compiled but was uncallable, since the
-- arm holds `hE` at a single `Czv` and cannot manufacture a multiple of it.
-- TRAP 26: in `hD2`'s `calc (2:V) = 1 + 1 ≤ y + 1 ≤ D`, the `1` on the right of `add_le_add hy0 _` must be pinned
-- `(le_refl (1 : V))`; plain `le_rfl` elaborates it as `Nat.unaryCast 1` against `hy1` and the application fails.
#print axioms lin4_le_p3succ
#print axioms lin6_le_p3succ
#print axioms and_roomS
#print axioms and_roomC

-- U10 (Necessitation/Verify5, 2026-09-16): §26.4 — THE `and` CHAIN'S INPUT BLOCK, the first seam of the transport
-- chain. From the node's own layout it runs `Prologue.layout_and` and the first `proIns`, and carries the
-- `q`-dossier across by `dossF_transport'`. The first `proIns` is at OFFSET `0` with dossier index `ir₀ + cq + 1`,
-- where `ir₀ = memTop … 0 ≤ 6·D + 1` (`memTop_le` at `i = 0`, after `zero_add`) and `cq = descCountF 0 q ≤ 2·D`
-- (`descCountF_le_of_len`) — so `proIns_ok`'s three E-rooms are EXACTLY §26.2's `and_room13`, `and_roomI` at
-- `i := 0`, and `and_roomIP` at `ip ≤ 8·D + 2`. That the banked rooms discharged every argument at a real call site,
-- rather than only in isolation, is what this block validates.
-- TRAP 27: `proIns_ok`'s `i` is INFERRED from whichever room supplies `hiE`. Passing `and_roomI hCk hir₀ hE`
-- unifies `i` with `memTop … 0` and the layouts stop lining up; the offset must be pinned `(i := 0)` with the room
-- instantiated at `(0 : V) ≤ 6·D + 1`.
-- TRAP 28: `Prologue.IdFrame` has NAMED fields (`child`, `parent`, `dp`, `cp`). The parent layout is `fr₁.parent`;
-- an anonymous `fr₁.2.1` descends into `parent`'s own conjunction and the type mismatch prints the whole unfolded
-- `Layout` body.
-- The block returns FIVE components; the fifth is `proIns_ok`'s sixth conjunct (the `eqFactB` on the row object),
-- which §26.5's crossing consumes as `heq₁`. An earlier four-component form was green but did NOT COMPOSE with the
-- next seam — the same failure class as a green-but-uncallable lemma, caught by checking the composition before
-- banking rather than at the call site afterwards.
#print axioms and_input

-- U10 (Necessitation/Verify5, 2026-09-16): §26.5 — THE `and` CHAIN'S CHILD CROSSING, the second seam. Given the
-- input block's `Γ₁` and the child's own facts, it crosses `L₁` and applies `postIns_ok`. The child's facts come
-- from `Verify4.verifyGraph''_ok4` INSTANTIATED AT `dp` — the sourcing that avoids adding a third conjunct
-- (`NoDrop' L`) to the recursion's motive, since that theorem already proves `ListOK ∧ NoDrop' ∧ shiftsV ∧ goalFact`
-- for the same `VerifyGraph''` object under the same table hypotheses.
-- The two shapes line up with no adjustment: `cgoal₁` arrives at
-- `^&(len (memberList (fstIdx dp)) + 1 + shiftsV L₁)`, which is `postIns_ok`'s `hg` at
-- `s'' := len (memberList (insert p s)) + 1 + shiftsV L₁` once `hdp.1` rewrites `fstIdx dp`; and `heq₁₂` is
-- `proIns_ok`'s SIXTH conjunct pushed across `L₁` by `tr_fact`, normalised by `shiftIterV_eqFactB` + two
-- `termShiftIterV_fvar` + `zero_add`, giving `heq` at `cp := proSig (insert p s) + shiftsV L₁`.
-- `postIns_ok` has EIGHT conclusion conjuncts (ListOK, NoDrop', shiftsV, len, derFact, fstIdxFact, dlenFact,
-- leFact); only the first three are used here.
#print axioms and_cross

-- U10 (Necessitation/Verify5, 2026-09-16): §26.6 — THE `and` CHAIN'S THREE TRANSPORTS, the third seam and the LAST
-- new mathematics for `and`. Carries the input block's parent layout and `q`-dossier across `appendV L₁ postIns`,
-- landing exactly on `and_arm_size`'s `hLay₃`/`hDq₃`. `Γ₃` is `finalCtx (finalCtx Γ₁ L₁) postIns` as §26.5 returns
-- it; the transports want the APPENDED form `finalCtx Γ₁ (appendV L₁ postIns)` (`finalCtx_appendV`). The block's
-- shift is `shiftsV L₁ + 2` (`shiftsV_appendV` + `postIns_ok`'s `shiftsV … = 2`) and its `NoDrop'` is
-- `noDrop'_appendV cnd₁ qnd₁`.
-- TRAP 30: both normalisations need an explicit `show … = … by ring`, NOT chained `← add_assoc`.
-- `Layout.transport`/`dossF_transport'` deliver `i + shiftsV S` fully LEFT-nested while the targets carry an inner
-- group, so associativity rewrites peel the wrong way; `Verify2`'s own chain uses the same `show … by ring` idiom.
-- SCOPE NOTE: with this seam `and_wrapper` already supplies every remaining `and_arm_size` input internally
-- (`hbn₁`/`hbn₂`/`hbn'` by `eroom_bnum`, `hLn` by `le_of_eq hdl.symm`, `hnd` by `le_two_mul_self`, and
-- `hgE₁`/`hgE₂`/`hgE3` by `rec2₄` derivations), and it takes `hΓ₃`/`hLay₃`/`hDq₃` as HYPOTHESES — exactly what
-- §§26.4–26.6 produce. So `hAndArm`'s discharge is a short chain of four existing pieces, not a re-derivation.
#print axioms and_trans

-- U10 (Necessitation/Verify5, 2026-09-16): §§26.7–26.8 — THE `cut` TRANSPORT CHAIN, and with it `hCutArm`'s
-- discharge. TWO seams, not three: §26.5 `and_cross` is REUSED VERBATIM (its binders are parametric in the
-- context and its `heq₁` is exactly the `eqFactB` §26.7 returns), so the child crossing is shared between the
-- arms — checked by compiling the application before writing anything, the second planned `cut` lemma to
-- dissolve on inspection after `cutPro_ok`. §26.6 `and_trans` does NOT transfer: it carries a
-- `Layout … (0 + 1 + proSig …)` while `cut`'s parent is a `PLay` — the empty-parent case is live — at the
-- prefix's own shift `mShift p + mShift (neg p) + (1 + proSig …)`, so §26.8 restates the transports over
-- `PLay.transport`.
-- §26.7 `cut_input`'s statement deliberately does NOT mention `cutPro`: a first draft tried
-- `rw [cutPro, if_pos hs0]` and failed ("Failed to rewrite using equation theorems") because the goal is an
-- `∃ Γ₁, …` whose body never contains the selector. `cutBlock_ok`/`sizeOK_cutPro` can unfold it only because
-- their own conclusions name it. Each branch supplies its own witness and which produced it is invisible
-- downstream; the selector is re-assembled later inside `sizeOK_cutPro`, which does its own split.
-- Offsets come from `mShift`/`mLen`, so §26.2's `and_roomI`/`and_roomIP` do NOT apply (they want `i ≤ 6·D + 1`,
-- `ip ≤ 8·D + 2`, against `cut`'s `8·D`/`6·D`): the two offset rooms come from the general `eroom_of_le` at
-- `22·D + 5` and `14·D + 4`, preferring the existing general machinery to new special cases.
-- The discharge's one structural subtlety: `cut_input` does NOT supply `cut_wrapper`'s `Γ`/`hLay₁`. Those are
-- the PRE-selector, post-`proCutPre` context, one block EARLIER; `cut_input`'s `Γ₁` is the CROSSING context,
-- one block LATER. Both name the same `proCutPre` term, so the two invocations agree definitionally and no
-- bridging lemma is needed. `ChildOK` is IRRELEVANT to the size half (it appears nowhere in `Verify5`;
-- `cut_wrapper` takes plain `SizeOK` + `len`), which also dissolved an apparent sixth instance of the
-- constant-ordering class — a missing `Cs` domination binder that turned out to be an artifact of drafting
-- toward `cutBlock_ok` (applicability side) instead of `cut_wrapper`.
#print axioms cut_input
#print axioms cut_trans

-- U10 (Necessitation/Package, 2026-09-15): THE PACKAGE AND THE HEADLINE THEOREMS, with `Assemble.SizeOracle`
-- BYPASSED. `SizeOracle` is NOT PROVABLE as stated (it binds the numeral table `T` with no `NumTableOK T N' B'`,
-- while every prologue size lemma requires one and lands at `layQ B B' D`/`layD N' B' D`; `NumTableOK` is never a
-- conclusion anywhere). It is not proved here but bypassed: its ONLY consumer, `Assemble.kitPackage'''_of_size`,
-- instantiates it at the CANONICAL numeral table of `NumSteps.exists_numTable`, where `N'`/`B'` ARE fixed naturals,
-- so the `NumTableOK`-CARRYING statement `SizeThm N' B' Cz` suffices. `SizeThmAll` (= `∀ N' B', ∃ Cz, SizeThm N' B' Cz`)
-- is the shape the size glue delivers; the quantifier ORDER is the whole point (`N'`, `B'` fixed first, `Cz` chosen
-- after, so `Cz` may depend on them). `kitPackage'''_of_size'` re-derives the package from it exactly as
-- `kitPackage'''_of_size` does, and the three headline theorems follow: `BoundedInnerNec 16` (`deg 4 = 16`),
-- Dupoc's self-cooperation (`Assembly/Cell.dupoc_self_coop` at `d = 16`) and the uniform PBLT
-- (`Assembly/Uniform.pblt_uniform` at `d = 16`) — each conditional ONLY on `SizeThmAll`.
#print axioms SizeThm
#print axioms SizeThmAll
#print axioms verifySizeOracle_of_sizeThm
#print axioms kitPackage'''_of_size'
#print axioms boundedInnerNec_sixteen_of_sizeThm
#print axioms dupoc_self_coop_of_sizeThm
#print axioms pblt_of_sizeThm

-- U10 (Necessitation/Verify5 §28 + Package §2.5, 2026-09-16): **`SizeThmAll` IS DISCHARGED.**
-- With the ten arms unconditional (§27), `ArmHypsAll` is a matter of CHOOSING the constant, and the constant is
-- chosen LAST — the standing lesson from the six ordering bugs. `Cz := 8·Cn` is FORCED, not chosen: the recursion's
-- size conjunct sits at `kitD Czv (2·dlen ρ)` (the arms double `D`) while `ArmHyps` demands the UNDOUBLED
-- `kitD Cz (dlen ρ)`, and §15's `kitD_two_mul_le` bridges exactly that at the cost of a factor `8`; the `Q` side
-- rides along by §15's `kitQ_mono_const`, the length side by `p4_mono le_self_add` + `pow4_eq_p4` (the recursion's
-- `p4 (dlen ρ)` is SMALLER than `ArmHyps`' `(dlen ρ + 1)^4`, so that direction is free). `Cn` collects each of the
-- nine domination constants as a SUMMAND, with `cG` (`Assemble.exists_cGoal`) and `Ck` (`Verify4.verifyGraph''_ok4`)
-- OPAQUE throughout — `exists_cGoal` exists precisely because a `def` of `4·(cDer + …)` stalls the kernel.
-- THREE interface binders were missing and were threaded first, each a hypothesis written before its consumer's
-- requirements were known: `TableOK tbl N` (no table predicate in the chain mentions `rowD`, so no `N` bounds the
-- proof codes); the E-cap `(Cz:V)·(dlen ρ + 1)^4 ≤ E` (absent, and FALSE at small `E` — `kitQ C B E` SHRINKS with
-- `E`, so a small cap makes the conclusion strictly stronger, while `AxmTableOK'` is vacuous at `A = 0` and can
-- bound nothing); and `hPle` (`Ple` is never a `rowB`, and `cPle` is an opaque `flen`). Each witness already existed
-- at the consumer, so all three cost one argument at `kitPackage'''_of_size'`.
-- TRAP: §28 must sit AFTER §27 — `armHyps_of_arms` is declared at the file's end, and a first attempt beside
-- `ArmHypsAll`'s definition in §2 failed with `Unknown identifier armHyps_of_arms`.
-- TRAP: `ArmHyps` binds `{E A ρ L}` IMPLICITLY; the arm goal is reached by the tactic `intro E A rho L hA hd hL
-- hEcap`, mirroring `verifySizeOracle_of_arms`. A term-mode `fun … ↦` binds the wrong slots and shifts the context
-- by one, silently.
-- With `sizeThmAll_holds`, `boundedInnerNec_sixteen_of_sizeThm`, `dupoc_self_coop_of_sizeThm` and `pblt_of_sizeThm`
-- are UNCONDITIONAL: `BoundedInnerNec 16`, Critch's Theorem 3.7 in PA-`S` (Dupoc's self-cooperation) and the uniform
-- PBLT each hold outright on [propext, Classical.choice, Quot.sound].
#print axioms armHypsAll_of_arms
#print axioms sizeThmAll_holds

end ArithS
