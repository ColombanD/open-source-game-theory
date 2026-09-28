import ArithS.Assembly.Cell

/-!
# ArithS.Audit.Loeb — the axiom census of the arithmetized layer: Loeb

This file covers the Löb layer (`Loeb/`, `Assembly/`): `InstV`, `NumeralFacts`, `Diag`, and the
M4 assembly (Prep, Uniform, Cell, Family).

Split out of the former single `ArithS/Audit.lean` on 2026-09-28; every `#print axioms` line and its
comment block are verbatim (the comment blocks are the historical record). `ArithS/Audit.lean` imports
the nine per-layer files; each line must read `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArithS

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

-- Route B Phase 1 — the family-parametric assembly (Assembly/Family, 2026-09-23): everything U8/U9
-- did for the one family `pConj` is done for an ARBITRARY target `p : Semisentence LAct 1` with a
-- slack `(S₀, S₁)` (the budget the consumer needs after the box of `p(k)`, `S₀ + S₁·|p(k)|`):
-- `psiF p = tactFixedpoint (boxCoreA 🡒 (p ⇜ ![#1]))` with its fixed point in `TAct`, the chain
-- `chain_core_VF` with the polynomial budget `chainBoundF`, and the bounded Löb premise as ONE
-- named hypothesis `LoebSound p S₀ S₁` ("a proof of the `k`-instance of `p` within budget `k`,
-- minus the slack, makes `p(k)` true in both readings" — □p → p). Outputs: `pblt_uniformF`
-- (`TAct ⊢ ∀ k, (k̂ ≤ k → psiF p (k))`) and `family_found`, the arithmetized `pblt_engine` (the
-- family's box found within its budget with the slack to spare, for all large `k : ℕ`), both
-- conditional on `BoundedInnerNec d` + `LoebSound p S₀ S₁`. `loebSound_pConj : LoebSound pConj 7 8`
-- (∧-elimination + search clauses + truth equations) makes Uniform/Cell the `pConj` instance:
-- `psi = psiF pConj` by `rfl`, every U8/U9 statement above byte-identical, `Package.lean` untouched.
#print axioms thetaF_subst_code
#print axioms psiF_fixed_point
#print axioms chain_core_VF
#print axioms chainBoundF_poly
#print axioms psiF_true_V
#print axioms pblt_uniformF
#print axioms exists_psiF_instance_length
#print axioms family_found
#print axioms loebSound_pConj

end ArithS
