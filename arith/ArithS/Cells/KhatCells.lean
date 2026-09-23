import ArithS.Cells.PositiveCells
import ArithS.Cells.JustSlot

/-!
# ArithS.Cells.KhatCells — the `k̂`-chain cells in PA-`S'`: the TFT probes and CupodTroll × Cupod

`Research/Notes/ROUTE_B_SCOPE.md` §6 (Phase 4 addendum): the four POS cells skipped by
`Cells/PositiveCells.lean` — Dupoc × TFT, Just × TFT, CIMCIC × TFT, CupodTroll × Cupod. In each the
searcher's guard is TRUE only ABOVE a standard threshold `k̂`: the opponent's play in a model `V`
needs the searcher's own guard (or a probe's) FOUND in `V` at the budget `k`, and "found" holds
uniformly for `k ≥ k̂` because the instance of a `TAct`-theorem `∀¹ q` at `bnum k` costs
`K₀ + K₁·‖k‖ ≤ k` in EVERY model (`found_of_all_V`). So the guard is a `TAct`-theorem only in the
conditional form `∀¹ (k̂ ≤ #0 🡒 q)` (`tact_all_above_of_both`), and its instance at `k` is found within
`k` by ONE cut against `NumeralFacts.lenProvable_le_bnumT` (`found_of_all_above`, the
`Assembly/Family.exists_psiF_instance_length` route without Löb).

1. **The `k̂`-chain**: `found_of_all_V` (the V-generic `found_of_all`), `tact_all_above_of_both`,
   `found_of_all_above` (cost `K₀ + K₁·size k + K₂·size k²`, below `k` for large `k`).
2. **TitForTatBot in every model**: `TftV`, its transposition, the closed description triple
   `(cl TTft, cterm C, cterm D)` (TFT is canonical: `TftV < swapcode TftV` by the probe's constant), the
   probe lemmas `tft_C_of_probe_C_V`/`tftT_D_of_probe_D_V`, and the searchers' clauses in every frame
   (`SV_then_V`, `botSV_then_V`).
3. **The three TFT cells**, unconditional at the engine's pads: `khat_DupocBot_vs_TitForTatBot` `(C, C)`,
   `khat_JustBot_vs_TitForTatBot` `(C, C)` (on the engine's own `pcode (JustBot k)`),
   `khat_CIMCIC_vs_TitForTatBot` `(C, C)`.
4. **`CupodTroll7`** — CupodTroll on a CONSTANT seven-variable template (route (c), `Cells/JustSlot.lean`'s
   construction): `CupodTrollBot k := .search k (.eq .opp (CupodBot k)) (.const D) (.const C)` freezes the
   budget-carrying snapshot `CupodBot k` inside its `.eq` guard (§7 of the scope note). The six-variable base
   `eqTmpl` says "the program described by the opp-triple IS the program described by the me-triple";
   `GtmplT7 := (eqTmpl ⇜ ![TCu4, cl uCu, cl wCu, #1, #2, #3]) ⇜ ![#6, #3, #4, #5]` reads the snapshot's
   budget from the slot `#6` through Cupod's description tower `TS gCu 1`. Instance equation
   `guardCodeB_GtmplT7 : guardCodeB ⌜GtmplT7⌝ me opp k = guardCode ⌜eqTmpl⌝ (SV gCu 1 k) opp`, truth
   equation `eval_eqTmpl_V` ("`opp = SV gCu 1 k`"), the engine bridge `guardCodeB_GtmplT7_nat` (the same
   CODE as the engine's guard `guardCode (tcode (phiT k)) me opp`, through the typed equality
   `eqTmpl_subst_eq_tmpl_eq`), hence `evalGraph_CupodTroll7_iff` (the same play as `pcode (CupodTrollBot k)`
   in every frame at every fuel), and the description layer `TT/uT/wT`, `hX_troll7`/`hopp_troll7`.
5. **CupodTroll × Cupod `(D, D)`** (`outcome_CupodTrollBot_vs_CupodBot`): CupodTroll's guard against
   `Cupod k` is the true equation `SV gCu 1 k = SV gCu 1 k` in both readings (`tact_qTC`), found for all
   large `k` (`found_of_all`), so CupodTroll plays its then-branch D; Cupod's guard "CupodTroll plays D
   against me" is then TRUE above `k̂` in every model (`found_of_all_V`), found by the chain
   (`found_of_all_above`): `khat_CupodTrollBot_vs_CupodBot`.

Conventions: every threshold EXISTENTIAL; `simp` never sees a closed quote; `omega` is never asked about
`V`; `≤` at ℕ bridged by `le_def`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The `k̂`-chain -/

section chain

/-- **A `TAct`-theorem `∀¹ q` is found at every large budget, in EVERY model** (the V-generic
`found_of_all`): the proof of `∀¹ q` is a standard object (`exists_lenDerivable_V_of_proof`), its
instance at `bnum k` costs `N + 5·|q|·|bnum k| + 3·|q| + |bnum k| + 7` (`lenDerivable_instB_V'`), linear
in `‖k‖` (`termLen_bnum_le_V'`), below `k` above a standard threshold (`linear_size_le_eventually`). -/
theorem found_of_all_V {q : Semisentence LAct 1} (hq : TAct ⊢ ∀¹ q) :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
      (kHat : V) ≤ k → LenProvableV TAct k (instB (⌜q⌝ : V) k) := by
  obtain ⟨N, hN⟩ := exists_lenDerivable_V_of_proof (∀¹ q) hq
  set fq := flen (q : Semiproposition LAct 1) with hfq
  obtain ⟨kHat, hkHat⟩ := linear_size_le_eventually (N + 35 * fq + 3 * fq + 7 + 7)
  refine ⟨kHat + 2, fun V _ _ k hk ↦ ?_⟩
  have hk₀ : (kHat : V) ≤ k := le_trans (by push_cast; exact le_self_add) hk
  have hs1 : 1 ≤ ‖k‖ := by
    have h1 : (1 : V) ≤ k := le_trans (by push_cast; exact le_add_left one_le_two) hk
    have := length_monotone h1
    rwa [length_one] at this
  have h := hN V
  rw [quote_all_sentence] at h
  have h1 := lenDerivable_instB_V' (V := V) (k := k) (Sentence.quote_isSemiformul₁ q) h
  rw [formulaLen_quote_semisentence_V, ← hfq] at h1
  have ht : termLen LAct (bnum k) ≤ 7 * ‖k‖ := termLen_bnum_le_V' hs1
  have hpoly := hkHat V k hk₀
  refine (lenDerivable_iff_lenProvableV _ _).mp (lenDerivable_mono_V (le_trans ?_ hpoly) h1)
  have e1 : (N : V) ≤ N * ‖k‖ := le_mul_of_one_le_right (by simp) hs1
  have e2 : (5 : V) * ((fq : V) * termLen LAct (bnum k)) ≤ 35 * fq * ‖k‖ := by
    calc (5 : V) * ((fq : V) * termLen LAct (bnum k)) ≤ 5 * ((fq : V) * (7 * ‖k‖)) := by gcongr
      _ = 35 * fq * ‖k‖ := by ring
  have e3 : (3 : V) * (fq : V) ≤ 3 * fq * ‖k‖ := le_mul_of_one_le_right (by simp) hs1
  have e4 : (7 : V) ≤ 7 * ‖k‖ := le_mul_of_one_le_right (by simp) hs1
  calc (N : V) + 5 * ((fq : V) * termLen LAct (bnum k)) + 3 * (fq : V) + termLen LAct (bnum k) + 7
      ≤ N * ‖k‖ + 35 * fq * ‖k‖ + 3 * fq * ‖k‖ + 7 * ‖k‖ + 7 * ‖k‖ := by gcongr
    _ = ((N + 35 * fq + 3 * fq + 7 + 7 : ℕ) : V) * ‖k‖ := by push_cast; ring

/-- **A conditional `TAct`-theorem from truth above a standard threshold, in both readings**
(`pblt_uniformF`'s closing step, for an arbitrary `q`): `TAct ⊢ ∀¹ (k̂ ≤ #0 🡒 q)`. -/
theorem tact_all_above_of_both (q : Semisentence LAct 1) (kHat : ℕ)
    (hstd : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kHat : M) ≤ x →
      Semiformula.Eval (s := stdActV M) ![x] Empty.elim q)
    (hswap : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kHat : M) ≤ x →
      Semiformula.Eval (s := swapActS M) ![x] Empty.elim q) :
    TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q) := by
  refine tact_complete' _ fun M _ _ ↦ ?_
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  constructor
  · simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro x hx
    rw [← stdActV_eq_stdActS]
    exact hstd M x ((eval_leF_numeral_bvar _ stdActS_lMap_emb kHat x).mp hx)
  · simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro x hx
    exact hswap M x ((eval_leF_numeral_bvar _ swapActS_lMap_emb kHat x).mp hx)

/-- **The instance of a conditional `TAct`-theorem at `bnum k`, its antecedent cut away**
(`exists_psiF_instance_length` for an arbitrary consequent): cost `K₀ + K₁·size k + K₂·size k²`. -/
theorem exists_instance_length_above (q : Semisentence LAct 1) (kHat : ℕ)
    (hq : TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q)) :
    ∃ K₀ K₁ K₂ : ℕ, ∀ k : ℕ, kHat < k →
      LenProvable (fbound : ℕ → ℕ) (K₀ + K₁ * Nat.size k + K₂ * Nat.size k * Nat.size k) TAct
        (⌜(q ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct)⌝ : ℕ) := by
  obtain ⟨N₃, hN₃⟩ := lenProvable_of_provable hq
  obtain ⟨C₀, C₁, hle⟩ := lenProvable_le_bnumT kHat
  refine ⟨N₃ + 13 * flen (((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q : Semisentence LAct 1) : Semiproposition LAct 1)
      + 8 + C₀ + 20 * tlen (Rew.emb (↑kHat : ClosedSemiterm LAct 0) : SyntacticSemiterm LAct 0) + 50
      + 20 * flen (q : Semiproposition LAct 1) + 9,
    30 * flen (((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q : Semisentence LAct 1) : Semiproposition LAct 1)
      + 126 + 60 * flen (q : Semiproposition LAct 1),
    C₁, fun k hk ↦ ?_⟩
  have h1 := lenProvable_inst_size ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q) k hN₃
  have h2 := hle k (Nat.le_of_lt hk)
  set fχ := flen (((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q : Semisentence LAct 1) : Semiproposition LAct 1)
    with hfχ
  set fψ := flen (q : Semiproposition LAct 1) with hfψ
  set a := tlen (Rew.emb (↑kHat : ClosedSemiterm LAct 0) : SyntacticSemiterm LAct 0) with ha
  set t : ClosedSemiterm LAct 0 := Semiterm.lMap emb (bnumT k) with ht
  set s := Nat.size k with hs
  have hχt : flen ((((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q) ⇜ ![t] : Sentence LAct) : Proposition LAct)
      ≤ fχ * (6 * s + 2) := flen_subst_bnumT_le _ k
  have h1' : LenProvable (fbound : ℕ → ℕ) (N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8) TAct
      (⌜(((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q) ⇜ ![t] : Sentence LAct)⌝ : ℕ) :=
    lenProvable_fbound_mono (by omega) h1
  rw [substs_leF_imp] at h1'
  have h3 := lenProvable_mp h1' h2
  refine lenProvable_fbound_mono ?_ h3
  have hψt : flen ((q ⇜ ![t] : Sentence LAct) : Proposition LAct) ≤ fψ * (6 * s + 2) :=
    flen_subst_bnumT_le q k
  have hleF : flen ((leF (↑kHat) t : Sentence LAct) : Proposition LAct) ≤ 2 * a + 2 * (6 * s + 1) + 3 := by
    rw [flen_leF_sentence, ht, tlen_emb_lMap_bnumT]
    have : tlen (Rew.emb (bnumT k) : SyntacticSemiterm ℒₒᵣ 0) ≤ 6 * s + 1 := tlen_bnumT k
    omega
  calc _ ≤ N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8 + (C₀ + C₁ * s * s)
        + 10 * ((2 * a + 2 * (6 * s + 1) + 3) + fψ * (6 * s + 2)) + 9 := by gcongr
    _ = N₃ + 13 * fχ + 8 + C₀ + 20 * a + 50 + 20 * fψ + 9 + (30 * fχ + 126 + 60 * fψ) * s
        + C₁ * s * s := by ring

/-- **`found_of_all` with an antecedent — the `k̂`-chain**: a guard family that is the `bnum k`-instance
of a formula `q` provable in `TAct` for `k ≥ k̂` is found within the budget `k` for all large `k`
(the instance at `bnum k`, the antecedent discharged by `lenProvable_le_bnumT` through one
`Cut.lenProvable_mp`, the quadratic cost below `k` by `quadratic_le_cube` + `poly_size_le_eventually`). -/
theorem found_of_all_above {q : Semisentence LAct 1} (kHat : ℕ)
    (hq : TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q)) (G : ℕ → ℕ)
    (hG : ∀ k, G k = instB (⌜q⌝ : ℕ) k) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (G k) := by
  obtain ⟨K₀, K₁, K₂, hmeta⟩ := exists_instance_length_above q kHat hq
  obtain ⟨kHat₁, hkHat₁⟩ := poly_size_le_eventually 1 3
  refine ⟨kHat₁ + kHat + 2 ^ (K₀ + K₁ + K₂ + 1), fun k hk ↦ ?_⟩
  have h2pow : 2 ≤ 2 ^ (K₀ + K₁ + K₂ + 1) := Nat.le_self_pow (Nat.succ_ne_zero _) 2
  have h := hmeta k (by omega)
  have hsize : K₀ + K₁ + K₂ + 1 ≤ Nat.size k := Nat.lt_size.mpr (by omega)
  have hcube := quadratic_le_cube K₀ K₁ K₂ (Nat.size k) hsize
  have hpoly := hkHat₁ ℕ k (le_def.mpr (Or.inr (by rw [natCast_nat]; omega)))
  rw [natCast_nat, ← size_eq_length, one_mul] at hpoly
  have hpoly' : Nat.size k ^ 3 ≤ k := by
    rcases le_def.mp hpoly with h | h
    · exact Nat.le_of_eq h
    · exact Nat.le_of_lt h
  have hle : K₀ + K₁ * Nat.size k + K₂ * Nat.size k * Nat.size k ≤ k := by
    refine le_trans hcube (le_trans (le_of_eq ?_) hpoly')
    ring
  have h2 := lenProvable_fbound_mono hle h
  rw [← lenProvableV_nat] at h2
  have hq' : instB (⌜q⌝ : ℕ) k = ⌜(q ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) q k
    rwa [natCast_nat] at this
  rw [hG, hq']
  exact h2

end chain

/-! ### 2. TitForTatBot in every model, and the searchers' clauses in every frame -/

section tft

/-- **TitForTatBot's code, in every model**: `ite (sim opp (bot CooperateBot)) C (const C) (const D)`. -/
noncomputable def TftV : V := pIte (pSim pOpp (pBot (pConst 0))) 0 (pConst 0) (pConst 1)

/-- The transposed TitForTatBot: `ite (sim opp (bot DefectBot)) D (const D) (const C)`. -/
noncomputable def TftTV : V := pIte (pSim pOpp (pBot (pConst 1))) 1 (pConst 1) (pConst 0)

lemma pcode_TFT : pcode TitForTatBot = pIte (pSim pOpp (pBot (pConst 0))) 0 (pConst 0) (pConst 1) := by
  simp [TitForTatBot, CooperateBot, actCode]

lemma TftV_nat : TftV (V := ℕ) = pcode TitForTatBot := by rw [pcode_TFT]; rfl

lemma cast_Tft : ((pcode TitForTatBot : ℕ) : V) = TftV := by
  rw [pcode_TFT, cast_pIte, cast_pSim, cast_pOpp, cast_pBot, cast_pConst, cast_pConst]
  simp [TftV]

theorem swapcode_TftV : swapcode (TftV : V) = TftTV := by
  unfold TftV TftTV swapcode
  simp [relabelAct]

theorem swapcode_TftTV : swapcode (TftTV : V) = TftV := by
  rw [← swapcode_TftV, swapcode_swapcode]

/-- TFT is CANONICAL: its code is below its transposition's (the probe's constant decides). -/
theorem TftV_lt_TftTV : (TftV : V) < TftTV := by
  unfold TftV TftTV pIte pSim pBot pConst pOpp ppair
  norm_num

lemma dnum_TftV : dnum (TftV : V) = TftV :=
  dnum_of_lt (by rw [swapcode_TftV]; exact TftV_lt_TftTV)

lemma dU_TftV : dU (TftV : V) = csym 0 := by
  unfold dU; rw [swapcode_TftV, if_pos TftV_lt_TftTV]

lemma dW_TftV : dW (TftV : V) = csym 1 := by
  unfold dW; rw [swapcode_TftV, if_pos TftV_lt_TftTV]

/-- TFT's closed description term: the structural term of its code. -/
noncomputable def TTft : ClosedSemiterm LAct 0 := Semiterm.lMap emb (progTT (pcode TitForTatBot))

lemma lMap_swap_TTft : Semiterm.lMap swap TTft = TTft := term_lMap_swap_emb _

theorem val_TTft_V : TTft.val (s := stdActV V) ![] Empty.elim = TftV := by
  unfold TTft
  rw [Semiterm.val_lMap, stdActV_lMap_emb, val_progTT_V, cast_Tft]

theorem quote_emb_TTft : (⌜(Rew.emb TTft : SyntacticSemiterm LAct 0)⌝ : V) = progT TftV := by
  unfold TTft
  rw [term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def, quote_progTT, cast_Tft]

/-- The description hypotheses of the triple `(cl TTft, cterm C, cterm D)`. -/
lemma hX_tft (k : V) :
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb (cl TTft : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum TftV) := by
  rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_TTft, dnum_TftV]
lemma hU_tft : (⌜(cterm Act.C : ClosedSemiterm LAct 0)⌝ : V) = dU TftV := by rw [quote_cterm_C, dU_TftV]
lemma hW_tft : (⌜(cterm Act.D : ClosedSemiterm LAct 0)⌝ : V) = dW TftV := by rw [quote_cterm_D, dW_TftV]

/-- The values: the triple reconstructs TFT; the swapped triple its transposition. -/
lemma val_desc_tft (k : V) :
    relabel ((cterm Act.C : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cterm Act.D : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cl TTft : Semiterm LAct Empty 1).val (s := stdActV V) ![k] Empty.elim) = TftV := by
  rw [val_cl_V, val_TTft_V, val_cterm_C_V, val_cterm_D_V, relabel_zero_one]
lemma val_desc_tft_swap (k : V) :
    relabel ((cterm Act.D : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cterm Act.C : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cl TTft : Semiterm LAct Empty 1).val (s := stdActV V) ![k] Empty.elim) = TftTV := by
  rw [val_cl_V, val_TTft_V, val_cterm_C_V, val_cterm_D_V]
  exact swapcode_TftV

/-- **TFT cooperates with `x` when `x` cooperates with `.bot CooperateBot`, in every model** (fuel `+2`). -/
theorem tft_C_of_probe_C_V {x n : V} (h : EvalGraph n x (pBot (pConst 0)) x 0) :
    EvalGraph (n + 1 + 1) TftV x TftV 0 := by
  unfold TftV
  rw [EvalGraph.ite_iff]
  refine ⟨0, ?_, Or.inl ⟨rfl, EvalGraph.const_iff.mpr rfl⟩⟩
  rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
  exact h

/-- **The transposed TFT defects against `x` when `x` defects against `.bot DefectBot`** (fuel `+2`). -/
theorem tftT_D_of_probe_D_V {x n : V} (h : EvalGraph n x (pBot (pConst 1)) x 1) :
    EvalGraph (n + 1 + 1) TftTV x TftTV 1 := by
  unfold TftTV
  rw [EvalGraph.ite_iff]
  refine ⟨1, ?_, Or.inl ⟨rfl, EvalGraph.const_iff.mpr rfl⟩⟩
  rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
  exact h

/-- **The generic searcher's then-clause in ANY frame** (fuel 2): a proof of `guardCode ⌜g⌝ me opp`
within `k` makes `SV g a k` play `a`. -/
theorem SV_then_V (g : Semisentence LAct 6) (a : ℕ) (k me opp : V)
    (h : LenProvableV TAct k (guardCode (⌜g⌝ : V) me opp)) : EvalGraph 2 me opp (SV g a k) (a : V) := by
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) me opp (pSearch k (⌜g⌝ : V) (pConst (a : V)) (pConst ((1 - a : ℕ) : V))) (a : V)
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ g)]
  left
  refine ⟨h, ?_⟩
  rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]

/-- The bot-wrapped generic searcher's then-clause in any frame (fuel 3). -/
theorem botSV_then_V (g : Semisentence LAct 6) (a : ℕ) (k me opp : V)
    (h : LenProvableV TAct k (guardCode (⌜g⌝ : V) me opp)) : EvalGraph 3 me opp (pBot (SV g a k)) (a : V) := by
  rw [show (3 : V) = 2 + 1 from two_add_one_eq_three.symm, EvalGraph.bot_iff]
  exact SV_then_V g a k me opp h

end tft

/-! ### 3. The probes against `.bot CooperateBot`/`.bot DefectBot`, found in every model above `k̂` -/

section probes

/-- Dupoc's guard against `.bot CooperateBot`: "`.bot CooperateBot` plays C against Dupoc(k)". -/
noncomputable def qDuB0 : Semisentence LAct 1 :=
  qT gDu (TS gDu 0) (uS gDu 0) (wS gDu 0) (cl TB0) (cterm Act.C) (cterm Act.D)

theorem guardCode_DuB0 (k : V) :
    guardCode (⌜gDu⌝ : V) (SV gDu 0 k) (pBot (pConst 0)) = instB (⌜qDuB0⌝ : V) k :=
  guardCode_qT_eq_instB gDu k _ _ _ _ _ _ (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k)
    (hW_SV gDu 0 (Or.inl rfl) k) (hX_bot_zero k) hU_C_bot_zero hW_D_bot_zero

theorem tact_qDuB0 : TAct ⊢ ∀¹ qDuB0 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qDuB0, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (hme_SV gDu 0 (Or.inl rfl) x) (val_desc_bot_zero x),
      actCode_C_cast]
    exact bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qDuB0, eval_qT_swap, lMap_swap_gDu, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .D _ _ _ _ _ _ x (hme_SVT gDu 0 (Or.inl rfl) x) (val_desc_bot_one x),
      actCode_D_cast]
    exact bot_const_play_V _ _ _

/-- **Dupoc cooperates with `.bot CooperateBot` in every model, above a standard threshold** (fuel 2). -/
theorem dupoc_botCB_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (SV gDu 0 k) (pBot (pConst 0)) (SV gDu 0 k) 0 := by
  obtain ⟨kHat, h⟩ := found_of_all_V tact_qDuB0
  refine ⟨kHat, fun V _ _ k hk ↦ ?_⟩
  have := SV_then_V gDu 0 k (SV gDu 0 k) (pBot (pConst 0)) (by rw [guardCode_DuB0]; exact h V k hk)
  rwa [Nat.cast_zero] at this

/-- **Cupod defects against `.bot DefectBot` in every model, above a standard threshold** (fuel 2). -/
theorem cupod_botDB_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (SV gCu 1 k) (pBot (pConst 1)) (SV gCu 1 k) 1 := by
  obtain ⟨kHat, h⟩ := found_of_all_V tact_qCuB1
  refine ⟨kHat, fun V _ _ k hk ↦ ?_⟩
  have := SV_then_V gCu 1 k (SV gCu 1 k) (pBot (pConst 1)) (by rw [guardCode_CuB1]; exact h V k hk)
  rwa [Nat.cast_one] at this

/-- The bot-wrapped Dupoc's guard against `.bot CooperateBot` (Just's consulted guard there). -/
noncomputable def qJB0 : Semisentence LAct 1 :=
  qT gDu (TBS gDu 0) (uS gDu 0) (wS gDu 0) (cl TB0) (cterm Act.C) (cterm Act.D)

theorem guardCode_JB0 (k : V) :
    guardCode (⌜gDu⌝ : V) (pBot (SV gDu 0 k)) (pBot (pConst 0)) = instB (⌜qJB0⌝ : V) k :=
  guardCode_qT_eq_instB gDu k _ _ _ _ _ _ (termSubst_TBS gDu 0 (Or.inl rfl) k) (hU_botSV gDu 0 (Or.inl rfl) k)
    (hW_botSV gDu 0 (Or.inl rfl) k) (hX_bot_zero k) hU_C_bot_zero hW_D_bot_zero

theorem tact_qJB0 : TAct ⊢ ∀¹ qJB0 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qJB0, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (hme_botSV gDu 0 (Or.inl rfl) x) (val_desc_bot_zero x),
      actCode_C_cast]
    exact bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qJB0, eval_qT_swap, lMap_swap_gDu, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .D _ _ _ _ _ _ x (hme_botSVT gDu 0 (Or.inl rfl) x) (val_desc_bot_one x),
      actCode_D_cast]
    exact bot_const_play_V _ _ _

/-- The bot-wrapped Cupod's guard against `.bot DefectBot` (the τ-twin). -/
noncomputable def qJB1 : Semisentence LAct 1 :=
  qT gCu (TBS gCu 1) (uS gCu 1) (wS gCu 1) (cl TB0) (cterm Act.D) (cterm Act.C)

theorem guardCode_JB1 (k : V) :
    guardCode (⌜gCu⌝ : V) (pBot (SV gCu 1 k)) (pBot (pConst 1)) = instB (⌜qJB1⌝ : V) k :=
  guardCode_qT_eq_instB gCu k _ _ _ _ _ _ (termSubst_TBS gCu 1 (Or.inr rfl) k) (hU_botSV gCu 1 (Or.inr rfl) k)
    (hW_botSV gCu 1 (Or.inr rfl) k) (hX_bot_one k) hU_D_bot_one hW_C_bot_one

theorem tact_qJB1 : TAct ⊢ ∀¹ qJB1 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qJB1, eval_qT_plays_opp_self .D _ _ _ _ _ _ x (hme_botSV gCu 1 (Or.inr rfl) x) (val_desc_bot_one x),
      actCode_D_cast]
    exact bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qJB1, eval_qT_swap, lMap_swap_gCu, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .C _ _ _ _ _ _ x (hme_botSVT gCu 1 (Or.inr rfl) x) (val_desc_bot_zero x),
      actCode_C_cast]
    exact bot_const_play_V _ _ _

/-- **The bot-wrapped Dupoc cooperates with `.bot CooperateBot` in every model, above a threshold** (fuel 3). -/
theorem botDupoc_botCB_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 3 (pBot (SV gDu 0 k)) (pBot (pConst 0)) (pBot (SV gDu 0 k)) 0 := by
  obtain ⟨kHat, h⟩ := found_of_all_V tact_qJB0
  refine ⟨kHat, fun V _ _ k hk ↦ ?_⟩
  have := botSV_then_V gDu 0 k (pBot (SV gDu 0 k)) (pBot (pConst 0)) (by rw [guardCode_JB0]; exact h V k hk)
  rwa [Nat.cast_zero] at this

/-- **The bot-wrapped Cupod defects against `.bot DefectBot` in every model, above a threshold** (fuel 3). -/
theorem botCupod_botDB_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 3 (pBot (SV gCu 1 k)) (pBot (pConst 1)) (pBot (SV gCu 1 k)) 1 := by
  obtain ⟨kHat, h⟩ := found_of_all_V tact_qJB1
  refine ⟨kHat, fun V _ _ k hk ↦ ?_⟩
  have := botSV_then_V gCu 1 k (pBot (SV gCu 1 k)) (pBot (pConst 1)) (by rw [guardCode_JB1]; exact h V k hk)
  rwa [Nat.cast_one] at this

/-- The transposed CIMCIC's guard against `.bot DefectBot`. -/
noncomputable def qCiTB1 : Semisentence LAct 1 := qCTG (cl TB0) (cterm Act.D) (cterm Act.C)

theorem guardCode_CiTB1 (k : V) :
    guardCode (⌜tmplCT⌝ : V) (CimcicTV k) (pBot (pConst 1)) = instB (⌜qCiTB1⌝ : V) k := by
  have h := guardCode_CimcicTV_eq_instB k (cl TB0) (cterm Act.C) (cterm Act.D) (hX_bot_zero k) hU_C_bot_zero
    hW_D_bot_zero
  rw [swapcode_pBot, swapcode_pConst_zero, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D] at h
  exact h

theorem tact_qCiTB1 : TAct ⊢ ∀¹ qCiTB1 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCiTB1, eval_qCTG_iff_V x _ _ _ (val_desc_bot_one x)]
    exact fun _ ↦ bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCiTB1, eval_qCTG_swap_iff_V, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qCG_iff_V x _ _ _ (val_desc_bot_zero x)]
    exact fun _ ↦ bot_const_play_V _ _ _

/-- **CIMCIC cooperates with `.bot CooperateBot` in every model, above a threshold** (fuel 2). -/
theorem cimcic_botCB_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (CimcicV k) (pBot (pConst 0)) (CimcicV k) 0 := by
  obtain ⟨kHat, h⟩ := found_of_all_V tact_qCiB0
  exact ⟨kHat, fun V _ _ k hk ↦ cimcic_search_V k _ (by rw [guardCode_CiB0]; exact h V k hk)⟩

/-- **The transposed CIMCIC defects against `.bot DefectBot` in every model, above a threshold** (fuel 2). -/
theorem cimcicT_botDB_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (CimcicTV k) (pBot (pConst 1)) (CimcicTV k) 1 := by
  obtain ⟨kHat, h⟩ := found_of_all_V tact_qCiTB1
  exact ⟨kHat, fun V _ _ k hk ↦ cimcicT_search_V k _ (by rw [guardCode_CiTB1]; exact h V k hk)⟩

end probes

/-! ### 4. The three TFT cells -/

section tftCells

/-! #### DupocBot × TitForTatBot `(C, C)` -/

/-- Dupoc's guard against TFT: "TFT plays C against Dupoc(k)". -/
noncomputable def qDT : Semisentence LAct 1 :=
  qT gDu (TS gDu 0) (uS gDu 0) (wS gDu 0) (cl TTft) (cterm Act.C) (cterm Act.D)

theorem guardCode_DT (k : V) : guardCode (⌜gDu⌝ : V) (SV gDu 0 k) TftV = instB (⌜qDT⌝ : V) k :=
  guardCode_qT_eq_instB gDu k _ _ _ _ _ _ (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k)
    (hW_SV gDu 0 (Or.inl rfl) k) (hX_tft k) hU_tft hW_tft

/-- `qDT` is true in both readings above a standard threshold: TFT's probe of Dupoc against
`.bot CooperateBot` succeeds there (and Cupod's against `.bot DefectBot` in the swap reading). -/
theorem tact_qDT_above : ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 qDT) := by
  obtain ⟨k₁, h₁⟩ := dupoc_botCB_V
  obtain ⟨k₂, h₂⟩ := cupod_botDB_V
  refine ⟨k₁ + k₂, tact_all_above_of_both _ _ (fun M _ _ x hx ↦ ?_) (fun M _ _ x hx ↦ ?_)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qDT, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (hme_SV gDu 0 (Or.inl rfl) x) (val_desc_tft x),
      actCode_C_cast]
    exact ⟨_, tft_C_of_probe_C_V (h₁ M x (le_trans (by push_cast; exact le_self_add) hx))⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qDT, eval_qT_swap, lMap_swap_gDu, lMap_swap_cl, lMap_swap_TTft, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .D _ _ _ _ _ _ x (hme_SVT gDu 0 (Or.inl rfl) x) (val_desc_tft_swap x),
      actCode_D_cast, lMap_swap_gDu]
    exact ⟨_, tftT_D_of_probe_D_V (h₂ M x (le_trans (by push_cast; exact le_add_self) hx))⟩

/-- **`DupocBot × TitForTatBot = (C, C)`** (engine `outcome_DupocBot_vs_TitForTatBot`, pad 4), for all large
`k`, on the engine's own codes: Dupoc's guard "TFT cooperates with me" is true above `k̂` and found by the
`k̂`-chain; TFT's probe sees Dupoc cooperate with `.bot CooperateBot`. -/
theorem khat_DupocBot_vs_TitForTatBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 4 (pcode (DupocBot k)) (pcode TitForTatBot) (pcode (DupocBot k)) (actCode .C) ∧
      EvalGraph 4 (pcode TitForTatBot) (pcode (DupocBot k)) (pcode TitForTatBot) (actCode .C) := by
  obtain ⟨kHat, hq⟩ := tact_qDT_above
  obtain ⟨k₀, h⟩ := found_of_all_above kHat hq
    (fun k ↦ guardCode (tcode phiDu) (pcode (DupocBot k)) (pcode TitForTatBot))
    (fun k ↦ by rw [← TftV_nat, pcode_DupocBot_SV]; exact guardCode_DT (V := ℕ) k)
  obtain ⟨k₁, h₁⟩ := dupoc_botCB_V
  refine ⟨k₀ + k₁, fun k hk ↦ ⟨?_, ?_⟩⟩
  · have hg := h k (by omega)
    rw [pcode_DupocBot'] at hg ⊢
    refine EvalGraph.mono_le (n := 0 + 1 + 1) (by omega) ?_
    exact search_then phiDu hg (const_play _ _ _ _)
  · have hp := h₁ ℕ k (le_def.mpr (Or.inr (by rw [natCast_nat]; omega)))
    rw [← pcode_DupocBot_SV] at hp
    exact tft_C_of_probe_C hp

/-! #### JustBot × TitForTatBot `(C, C)` -/

/-- Just's guard against TFT: "TFT plays C against the frozen `.bot (DupocBot k)`". -/
noncomputable def qJT : Semisentence LAct 1 :=
  qT gDu (TBS gDu 0) (uS gDu 0) (wS gDu 0) (cl TTft) (cterm Act.C) (cterm Act.D)

theorem guardCode_JT (k : V) : guardCode (⌜gDu⌝ : V) (pBot (SV gDu 0 k)) TftV = instB (⌜qJT⌝ : V) k :=
  guardCode_qT_eq_instB gDu k _ _ _ _ _ _ (termSubst_TBS gDu 0 (Or.inl rfl) k) (hU_botSV gDu 0 (Or.inl rfl) k)
    (hW_botSV gDu 0 (Or.inl rfl) k) (hX_tft k) hU_tft hW_tft

/-- Just cooperates with `.bot CooperateBot` for all large `k`, on the engine's own code (the consulted guard is
the snapshot's, `guardCode_JustBot_eq`, the `bnum k`-instance of `qJB0`). -/
theorem just_botCB_found :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (pcode (JustBot k)) (pBot (pConst 0)) (pcode (JustBot k)) 0 := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qJB0
    (fun k ↦ guardCode (tcode (phiJ k)) (pcode (JustBot k)) (pBot (pConst 0)))
    (fun k ↦ by
      rw [← pcode_botCB, guardCode_JustBot_eq k proper_botCB, pcode_botCB, pcode_DupocBot_SV]
      exact guardCode_JB0 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hg := h k hk
  rw [pcode_JustBot] at hg ⊢
  exact search_then (phiJ k) hg (const_play _ _ _ _)

theorem tact_qJT_above : ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 qJT) := by
  obtain ⟨k₁, h₁⟩ := botDupoc_botCB_V
  obtain ⟨k₂, h₂⟩ := botCupod_botDB_V
  refine ⟨k₁ + k₂, tact_all_above_of_both _ _ (fun M _ _ x hx ↦ ?_) (fun M _ _ x hx ↦ ?_)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qJT, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (hme_botSV gDu 0 (Or.inl rfl) x) (val_desc_tft x),
      actCode_C_cast]
    exact ⟨_, tft_C_of_probe_C_V (h₁ M x (le_trans (by push_cast; exact le_self_add) hx))⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qJT, eval_qT_swap, lMap_swap_gDu, lMap_swap_cl, lMap_swap_TTft, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .D _ _ _ _ _ _ x (hme_botSVT gDu 0 (Or.inl rfl) x) (val_desc_tft_swap x),
      actCode_D_cast, lMap_swap_gDu]
    exact ⟨_, tftT_D_of_probe_D_V (h₂ M x (le_trans (by push_cast; exact le_add_self) hx))⟩

/-- **`JustBot × TitForTatBot = (C, C)`** (engine `outcome_JustBot_vs_TitForTatBot`, pad 5), for all large `k`,
on the engine's own `pcode (JustBot k)`: the consulted guard is Dupoc's in the snapshot's frame
(`guardCode_JustBot_eq`), true above `k̂` because TFT sees the frozen `.bot (DupocBot k)` cooperate with
`.bot CooperateBot`. -/
theorem khat_JustBot_vs_TitForTatBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 5 (pcode (JustBot k)) (pcode TitForTatBot) (pcode (JustBot k)) (actCode .C) ∧
      EvalGraph 5 (pcode TitForTatBot) (pcode (JustBot k)) (pcode TitForTatBot) (actCode .C) := by
  obtain ⟨kHat, hq⟩ := tact_qJT_above
  obtain ⟨k₀, h⟩ := found_of_all_above kHat hq
    (fun k ↦ guardCode (tcode (phiJ k)) (pcode (JustBot k)) (pcode TitForTatBot))
    (fun k ↦ by
      rw [guardCode_JustBot_eq k sfp_TitForTatBot.1, ← TftV_nat, pcode_DupocBot_SV]
      exact guardCode_JT (V := ℕ) k)
  obtain ⟨k₁, h₁⟩ := just_botCB_found
  refine ⟨k₀ + k₁, fun k hk ↦ ⟨?_, ?_⟩⟩
  · have hg := h k (by omega)
    rw [pcode_JustBot] at hg ⊢
    refine EvalGraph.mono_le (n := 0 + 1 + 1) (by omega) ?_
    exact search_then (phiJ k) hg (const_play _ _ _ _)
  · exact EvalGraph.mono_le (n := 2 + 1 + 1) (by omega) (tft_C_of_probe_C (h₁ k (by omega)))

/-! #### CIMCIC × TitForTatBot `(C, C)` -/

/-- CIMCIC's guard against TFT: "CIMCIC(k) plays C against TFT ⇒ TFT plays C against CIMCIC(k)". -/
noncomputable def qCT : Semisentence LAct 1 := qCG (cl TTft) (cterm Act.C) (cterm Act.D)

theorem guardCode_CT (k : V) : guardCode (⌜tmplC⌝ : V) (CimcicV k) TftV = instB (⌜qCT⌝ : V) k :=
  guardCode_CimcicV_eq_instB k (cl TTft) _ _ (hX_tft k) hU_tft hW_tft

theorem tact_qCT_above : ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 qCT) := by
  obtain ⟨k₁, h₁⟩ := cimcic_botCB_V
  obtain ⟨k₂, h₂⟩ := cimcicT_botDB_V
  refine ⟨k₁ + k₂, tact_all_above_of_both _ _ (fun M _ _ x hx ↦ ?_) (fun M _ _ x hx ↦ ?_)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCT, eval_qCG_iff_V x _ _ _ (val_desc_tft x)]
    exact fun _ ↦ ⟨_, tft_C_of_probe_C_V (h₁ M x (le_trans (by push_cast; exact le_self_add) hx))⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCT, eval_qCG_swap_iff_V, lMap_swap_cl, lMap_swap_TTft, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qCTG_iff_V x _ _ _ (val_desc_tft_swap x)]
    exact fun _ ↦ ⟨_, tftT_D_of_probe_D_V (h₂ M x (le_trans (by push_cast; exact le_add_self) hx))⟩

/-- **`CIMCIC × TitForTatBot = (C, C)`** (engine `llm_outcome_CIMCIC_vs_TitForTatBot`, pad 6), for all large `k`:
the consequent of CIMCIC's guard, "TFT cooperates with me", is true above `k̂` (TFT sees CIMCIC cooperate with
`.bot CooperateBot`), so the guard is found by the `k̂`-chain (the engine's `weakenImpl`). -/
theorem khat_CIMCIC_vs_TitForTatBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 6 (pcode (CIMCIC k)) (pcode TitForTatBot) (pcode (CIMCIC k)) (actCode .C) ∧
      EvalGraph 6 (pcode TitForTatBot) (pcode (CIMCIC k)) (pcode TitForTatBot) (actCode .C) := by
  obtain ⟨kHat, hq⟩ := tact_qCT_above
  obtain ⟨k₀, h⟩ := found_of_all_above kHat hq
    (fun k ↦ guardCode (⌜tmplC⌝ : ℕ) (Cimcic k) (pcode TitForTatBot))
    (fun k ↦ by rw [← TftV_nat]; exact guardCode_CT (V := ℕ) k)
  obtain ⟨k₁, h₁⟩ := cimcic_botCB_V
  refine ⟨k₀ + k₁, fun k hk ↦ ⟨?_, ?_⟩⟩
  · rw [pcode_CIMCIC]
    exact EvalGraph.mono_le (n := 2) (by omega) (cimcic_search_V (V := ℕ) k _ (h k (by omega)))
  · have hp := h₁ ℕ k (le_def.mpr (Or.inr (by rw [natCast_nat]; omega)))
    rw [pcode_CIMCIC]
    exact EvalGraph.mono_le (n := 2 + 1 + 1) (by omega) (tft_C_of_probe_C hp)

end tftCells

/-! ### 5. `CupodTroll7`: CupodTroll on a CONSTANT template with a budget slot -/

section trollTemplate

/-- **The six-variable base of the `.eq` guard**: "the program described by the opp-triple `(#3, #4, #5)`
IS the program described by the me-triple `(#0, #1, #2)`" — `tmpl (.eq .opp q)` with the frozen literal's
closed description (`closedDesc (pcode q)`) replaced by the me-triple's (`progAux .self _`). -/
noncomputable def eqTmpl : Semisentence LAct 6 :=
  ∃¹ (∃¹ (((descF #1 #5 #6 #7 : Semisentence LAct 7) ⇜ ![#1, #2, #3, #4, #5, #6, #7]) ⋏
    (((descF #1 #2 #3 #4 : Semisentence LAct 7) ⇜ ![#0, #2, #3, #4, #5, #6, #7]) ⋏
      Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#1, #0])))

/-- **The truth of `eqTmpl` at a frame, in every model**: the opp-triple and the me-triple describe the
same program. -/
theorem eval_eqTmpl_V (b : Fin 6 → V) :
    Semiformula.Eval (s := stdActV V) b Empty.elim eqTmpl ↔
      relabel (b 4) (b 5) (b 3) = relabel (b 1) (b 2) (b 0) := by
  unfold eqTmpl descF
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, stdActV_rel_eq, Function.comp_def,
    Matrix.cons_val, Semiterm.val_bvar]
  constructor
  · rintro ⟨x, y, ⟨d, rfl, rfl⟩, ⟨d', rfl, rfl⟩, h⟩
    exact h
  · intro h
    exact ⟨_, _, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, h⟩

/-- `eqTmpl` is τ-fixed. -/
lemma lMap_swap_eqTmpl : Semiformula.lMap swap eqTmpl = eqTmpl := by
  unfold eqTmpl
  simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst, lMap_swap_descF,
    Semiformula.lMap_rel, Semiterm.lMap_bvar]
  congr 3
  · congr 1; funext i; fin_cases i <;> rfl
  · congr 1
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1; funext i; fin_cases i <;> rfl

/-- `descF #1 #2 #3 #4 ⇜ w` is the closed description of `c` when `w` carries `c`'s description terms
in the me-slots (the `.self` case of `Code.progAux_subst`, without a frame). -/
lemma descF_self_subst {m : ℕ} (c : ℕ) (w w' : Fin 7 → Semiterm LAct Empty m) (h0 : w 0 = w' 0)
    (h1 : w 1 = cl (dnumT c)) (h2 : w 2 = cl (dUT c)) (h3 : w 3 = cl (dWT c)) :
    (descF #1 #2 #3 #4 : Semisentence LAct 7) ⇜ w = closedDesc c ⇜ w' := by
  rw [closedDesc_subst]
  unfold Rewriting.subst
  rw [rew_descF]
  show descF (Rew.bShift (w 0)) (Rew.bShift (w 1)) (Rew.bShift (w 2)) (Rew.bShift (w 3)) = _
  rw [h0, h1, h2, h3, rew_cl, rew_cl, rew_cl]

/-- `descF #1 #5 #6 #7 ⇜ w` depends only on the entries `0, 4, 5, 6` of `w`. -/
lemma descF_opp_subst {m : ℕ} (w w' : Fin 7 → Semiterm LAct Empty m) (h0 : w 0 = w' 0)
    (h4 : w 4 = w' 4) (h5 : w 5 = w' 5) (h6 : w 6 = w' 6) :
    (descF #1 #5 #6 #7 : Semisentence LAct 7) ⇜ w = (descF #1 #5 #6 #7 : Semisentence LAct 7) ⇜ w' := by
  unfold Rewriting.subst
  rw [rew_descF, rew_descF]
  show descF (Rew.bShift (w 0)) (Rew.bShift (w 4)) (Rew.bShift (w 5)) (Rew.bShift (w 6)) =
    descF (Rew.bShift (w' 0)) (Rew.bShift (w' 4)) (Rew.bShift (w' 5)) (Rew.bShift (w' 6))
  rw [h0, h4, h5, h6]

/-- **The typed bridge**: `eqTmpl` filled with the description of `pcode Q` in the me-slots and `opp`'s in the
opp-slots IS `tmpl (.eq .opp Q)` filled with ANY me-description and `opp`'s (the literal `Q` is closed, the
frame's `me` unused on both sides). -/
theorem eqTmpl_subst_eq_tmpl_eq (Q : PD.Prog) (me opp : ℕ) :
    (eqTmpl ⇜ (fun i ↦ (cl (descTerms (pcode Q) opp i) : Semiterm LAct Empty 6))) =
      tmpl (.eq .opp Q) ⇜ (fun i ↦ (cl (descTerms me opp i) : Semiterm LAct Empty 6)) := by
  rw [tmpl_eq]
  unfold eqTmpl progGraph
  rw [progAux_opp]
  simp only [Rewriting.app_exs, Rew.q_subst, LogicalConnective.HomClass.map_and, rew_subst_eq]
  congr 3
  · refine descF_opp_subst _ _ ?_ ?_ ?_ ?_
    · rfl
    all_goals (show Rew.bShift (Rew.bShift (cl _)) = Rew.bShift (Rew.bShift (cl _)); rfl)
  · congr 1
    · refine descF_self_subst (pcode Q) _ _ ?_ ?_ ?_ ?_
      · rfl
      all_goals (show Rew.bShift (Rew.bShift (cl _)) = _; rw [rew_cl, rew_cl]; try rfl)
    · rw [Semiformula.rew_rel, Semiformula.rew_rel]
      congr 1
      funext i
      fin_cases i <;> rfl

/-- `guardCode ⌜g⌝ me opp` at ℕ is the code of the guard sentence, for ANY six-variable template
(`Code.quote_trAt`'s argument). -/
theorem quote_subst_descTerms (g : Semisentence LAct 6) (me opp : ℕ) :
    (⌜(g ⇜ descTerms me opp : Sentence LAct)⌝ : ℕ) = guardCode (⌜g⌝ : ℕ) me opp := by
  unfold guardCode
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1
  exact semitermVec_val_descTerms _ _

/-- **The guard-code bridge at ℕ**: `eqTmpl` in the frame `(pcode Q, opp)` has the SAME code as the engine's
`.eq .opp Q` template in any frame `(me, opp)`. -/
theorem guardCode_eqTmpl_eq_tcode (Q : PD.Prog) (me opp : ℕ) :
    guardCode (⌜eqTmpl⌝ : ℕ) (pcode Q) opp = guardCode (tcode (.eq .opp Q)) me opp := by
  unfold tcode
  rw [← quote_subst_descTerms, ← quote_subst_descTerms, ← quote_subst_cl, ← quote_subst_cl,
    eqTmpl_subst_eq_tmpl_eq Q me opp]

/-! #### The seven-variable template -/

/-- Cupod's description tower with the budget as `#0`, cast into four variables. -/
noncomputable def TCu4 : Semiterm LAct Empty 4 := Rew.castLE (by norm_num) (TS gCu 1)

/-- "The program described by the triple `(#1, #2, #3)` is the Cupod of budget `#0` (described by
`(TS gCu 1 (#0), U, W)`)". -/
noncomputable def qE4 (U W : ClosedSemiterm LAct 0) : Semisentence LAct 4 :=
  eqTmpl ⇜ ![TCu4, cl U, cl W, #1, #2, #3]

/-- **The constant seven-variable template**: the frame's opp-triple in `#3 #4 #5`, the node budget in `#6`. -/
noncomputable def GtmplT7A (U W : ClosedSemiterm LAct 0) : Semisentence LAct 7 :=
  qE4 U W ⇜ ![#6, #3, #4, #5]

/-- **CupodTroll's template**: "the opponent IS `CupodBot #6`". -/
noncomputable def GtmplT7 : Semisentence LAct 7 := GtmplT7A (uS gCu 1) (wS gCu 1)

lemma GtmplT7_def : GtmplT7 = GtmplT7A (uS gCu 1) (wS gCu 1) := rfl

lemma lMap_swap_TCu4 : Semiterm.lMap swap TCu4 = TCu4 := by
  unfold TCu4
  change Semiterm.lMap swap (Rew.map (Fin.castLE _) id (TS gCu 1)) = Rew.map (Fin.castLE _) id (TS gCu 1)
  rw [Semiterm.lMap_map, lMap_swap_TS]

lemma lMap_swap_qE4 (U W : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (qE4 U W) = qE4 (Semiterm.lMap swap U) (Semiterm.lMap swap W) := by
  unfold qE4
  rw [Semiformula.lMap_subst, lMap_swap_eqTmpl]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_TCu4, lMap_swap_cl]

lemma lMap_swap_GtmplT7A (U W : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (GtmplT7A U W) = GtmplT7A (Semiterm.lMap swap U) (Semiterm.lMap swap W) := by
  unfold GtmplT7A
  rw [Semiformula.lMap_subst, lMap_swap_qE4]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The transposed re-valuation terms of Cupod (those of Dupoc, `swapcode (CupodBot k) = DupocBot k`). -/
noncomputable def uST : ClosedSemiterm LAct 0 := Semiterm.lMap swap (uS gCu 1)
noncomputable def wST : ClosedSemiterm LAct 0 := Semiterm.lMap swap (wS gCu 1)

lemma lMap_swap_GtmplT7 : Semiformula.lMap swap GtmplT7 = GtmplT7A uST wST := by
  rw [GtmplT7_def, lMap_swap_GtmplT7A]; rfl

/-! #### The codes -/

/-- The codes of `![TCu4, cl U, cl W, #1, #2, #3]`. -/
noncomputable def eVec4 (U W : ClosedSemiterm LAct 0) : V :=
  (⌜(Rew.emb TCu4 : SyntacticSemiterm LAct 4)⌝ : V) ∷
    ⌜(Rew.emb (cl U : Semiterm LAct Empty 4) : SyntacticSemiterm LAct 4)⌝ ∷
    ⌜(Rew.emb (cl W : Semiterm LAct Empty 4) : SyntacticSemiterm LAct 4)⌝ ∷
    ⌜(Rew.emb (#1 : Semiterm LAct Empty 4) : SyntacticSemiterm LAct 4)⌝ ∷
    ⌜(Rew.emb (#2 : Semiterm LAct Empty 4) : SyntacticSemiterm LAct 4)⌝ ∷
    ⌜(Rew.emb (#3 : Semiterm LAct Empty 4) : SyntacticSemiterm LAct 4)⌝ ∷ 0

theorem quote_GtmplT7A (U W : ClosedSemiterm LAct 0) :
    (⌜GtmplT7A U W⌝ : V) = subst LAct sVec7 (⌜qE4 U W⌝ : V) := by
  unfold GtmplT7A
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1

theorem quote_qE4 (U W : ClosedSemiterm LAct 0) :
    (⌜qE4 U W⌝ : V) = subst LAct (eVec4 U W) (⌜eqTmpl⌝ : V) := by
  unfold qE4
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1

lemma eVec4_semitermVec (U W : ClosedSemiterm LAct 0) : IsSemitermVec LAct 6 4 (eVec4 U W : V) := by
  rw [six_eq, eVec4]
  exact ((((((IsSemitermVec.nil 4).adjoin (semiterm_quote_emb₄ (#3 : Semiterm LAct Empty 4))).adjoin
    (semiterm_quote_emb₄ (#2 : Semiterm LAct Empty 4))).adjoin
    (semiterm_quote_emb₄ (#1 : Semiterm LAct Empty 4))).adjoin
    (semiterm_quote_emb₄ (cl W : Semiterm LAct Empty 4))).adjoin
    (semiterm_quote_emb₄ (cl U : Semiterm LAct Empty 4))).adjoin (semiterm_quote_emb₄ TCu4)

/-- Filling `![TCu4, cl U, cl W, #1, #2, #3]` with the budget vector gives the description vector of
`(SV gCu 1 k, opp)` up to the two closed entries. -/
theorem termSubstVec_eVec4 (U W : ClosedSemiterm LAct 0) (opp k : V) :
    termSubstVec LAct 6 (bVec4 opp k) (eVec4 U W) =
      progT (dnum (SV gCu 1 k)) ∷ (⌜(Rew.emb U : SyntacticSemiterm LAct 0)⌝ : V) ∷
        (⌜(Rew.emb W : SyntacticSemiterm LAct 0)⌝ : V) ∷ progT (dnum opp) ∷ dU opp ∷ dW opp ∷ 0 := by
  unfold eVec4 TCu4
  rw [quote_emb_castLE_V, show (cl U : Semiterm LAct Empty 4) = Rew.castLE (Nat.zero_le 4) U from rfl,
    show (cl W : Semiterm LAct Empty 4) = Rew.castLE (Nat.zero_le 4) W from rfl,
    quote_emb_castLE_V, quote_emb_castLE_V, quote_emb_bvar4_1, quote_emb_bvar4_2, quote_emb_bvar4_3]
  have hT : IsUTerm LAct (⌜(Rew.emb (TS gCu 1) : SyntacticSemiterm LAct 1)⌝ : V) := (semiterm_quote_emb₁ _).isUTerm
  have hU : IsUTerm LAct (⌜(Rew.emb U : SyntacticSemiterm LAct 0)⌝ : V) := (semiterm_quote_emb₀ _).isUTerm
  have hW : IsUTerm LAct (⌜(Rew.emb W : SyntacticSemiterm LAct 0)⌝ : V) := (semiterm_quote_emb₀ _).isUTerm
  have h1 : IsUTerm LAct (^#1 : V) := (IsSemiterm.bvar.mpr (by norm_num : (1 : V) < 4)).isUTerm
  have h2 : IsUTerm LAct (^#2 : V) := (IsSemiterm.bvar.mpr (by norm_num : (2 : V) < 4)).isUTerm
  have h3 : IsUTerm LAct (^#3 : V) := (IsSemiterm.bvar.mpr (by norm_num : (3 : V) < 4)).isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin h3
  have e2 := e1.adjoin h2
  have e3 := e2.adjoin h1
  have e4 := e3.adjoin hW
  have e5 := e4.adjoin hU
  rw [six_eq, termSubstVec_cons hT e5, termSubstVec_cons hU e4, termSubstVec_cons hW e3,
    termSubstVec_cons h1 e2, termSubstVec_cons h2 e1, termSubstVec_cons h3 e0, termSubstVec_nil,
    quote_emb_TS, termSubst_tower_of _ k _ _ _ (by unfold bVec4; rw [nth_adjoin_zero]),
    ← dnum_SV gCu 1 (Or.inr rfl) k,
    termSubst_closed _ (semiterm_quote_emb₀ _), termSubst_closed _ (semiterm_quote_emb₀ _),
    termSubst_bvar, termSubst_bvar, termSubst_bvar]
  unfold bVec4
  rw [show (3 : V) = 2 + 1 by norm_num, nth_adjoin_succ]
  simp only [nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]

/-- **The generic instance equation of the seven-variable template**. -/
theorem guardCodeB_GtmplT7A (U W : ClosedSemiterm LAct 0) (me opp k : V) :
    guardCodeB (⌜GtmplT7A U W⌝ : V) me opp k =
      subst LAct (progT (dnum (SV gCu 1 k)) ∷ (⌜(Rew.emb U : SyntacticSemiterm LAct 0)⌝ : V) ∷
        (⌜(Rew.emb W : SyntacticSemiterm LAct 0)⌝ : V) ∷ progT (dnum opp) ∷ dU opp ∷ dW opp ∷ 0)
        (⌜eqTmpl⌝ : V) := by
  unfold guardCodeB
  rw [quote_GtmplT7A, substs_substs (isSemiformula_quote₄ (qE4 U W)) (descVecB_semitermVec me opp k)
    sVec7_semitermVec, termSubstVec_sVec7, quote_qE4,
    substs_substs (isSemiformula_quote₆ eqTmpl) (bVec4_semitermVec opp k) (eVec4_semitermVec U W),
    termSubstVec_eVec4]

/-- **CupodTroll's instance equation**: in the frame `(me, opp)` the constant template filled with the node
budget `k` IS the guard of `eqTmpl` in the frame `(CupodBot k, opp)` — "`opp` is `CupodBot k`". -/
theorem guardCodeB_GtmplT7 (me opp k : V) :
    guardCodeB (⌜GtmplT7⌝ : V) me opp k = guardCode (⌜eqTmpl⌝ : V) (SV gCu 1 k) opp := by
  rw [GtmplT7_def, guardCodeB_GtmplT7A]
  have hu := hU_SV gCu 1 (Or.inr rfl) k
  have hw := hW_SV gCu 1 (Or.inr rfl) k
  rw [Semiterm.empty_quote_def] at hu hw
  rw [hu, hw]
  rfl

/-- **The transposed instance equation**: the transposed template gives `eqTmpl` in the frame `(DupocBot k, opp)`. -/
theorem guardCodeB_GtmplT7T (me opp k : V) :
    guardCodeB (⌜GtmplT7A uST wST⌝ : V) me opp k = guardCode (⌜eqTmpl⌝ : V) (SV gDu 0 k) opp := by
  have h := relabelTemplate_guardCodeB (isSemiformula_quote₇ GtmplT7) (swapcode me) (swapcode opp) k
  rw [swapcode_swapcode, swapcode_swapcode, relabelTemplate_quote_sentence₇_V, lMap_swap_GtmplT7,
    guardCodeB_GtmplT7] at h
  rw [← h]
  have hg : IsSemiformula LAct 6 (⌜eqTmpl⌝ : V) := isSemiformula_quote₆ eqTmpl
  rw [← gsubst_of_template hg, relabelTemplate_gsubst, swapcode_SV gCu 1 (Or.inr rfl), lMap_swap_gCu,
    swapcode_swapcode, relabelTemplate_quote_sentence₆_V, lMap_swap_eqTmpl, gsubst_of_template hg]

/-! #### The engine bridge at ℕ -/

/-- **`GtmplT7` consults the engine's guard**: at ℕ, in every frame, the constant template filled with the
node budget has the SAME code as the engine's `.eq .opp (CupodBot k)` template filled with the frame. -/
theorem guardCodeB_GtmplT7_nat (me opp k : ℕ) :
    guardCodeB (⌜GtmplT7⌝ : ℕ) me opp k = guardCode (tcode (phiT k)) me opp := by
  rw [guardCodeB_GtmplT7]
  have h := guardCode_eqTmpl_eq_tcode (CupodBot k) me opp
  rw [pcode_CupodBot_SV] at h
  exact h

end trollTemplate

/-! ### 6. `CupodTrollV7`: the searcher on the constant template -/

section troll7

/-- **CupodTroll on the constant template, in every model**: found ⇒ D, else C. -/
noncomputable def CupodTrollV7 (k : V) : V := pSearch k (⌜GtmplT7⌝ : V) (pConst 1) (pConst 0)

/-- The transposed searcher: "the opponent IS `DupocBot k`" ⇒ C, else D. -/
noncomputable def CupodTrollTV7 (k : V) : V := pSearch k (⌜GtmplT7A uST wST⌝ : V) (pConst 0) (pConst 1)

/-- **CupodTroll at ℕ on the constant template.** -/
noncomputable def CupodTroll7 (k : ℕ) : ℕ := CupodTrollV7 (V := ℕ) k

lemma CupodTrollV7_nat (k : ℕ) : CupodTrollV7 (V := ℕ) k = CupodTroll7 k := rfl

theorem swapcode_CupodTrollV7 (k : V) : swapcode (CupodTrollV7 k) = CupodTrollTV7 k := by
  unfold CupodTrollV7 CupodTrollTV7 swapcode
  rw [relabel_search, relabel_const, relabel_const, relabelTemplate_quote_sentence₇_V, lMap_swap_GtmplT7]
  simp [relabelAct]

theorem swapcode_CupodTrollTV7 (k : V) : swapcode (CupodTrollTV7 k) = CupodTrollV7 k := by
  rw [← swapcode_CupodTrollV7, swapcode_swapcode]

/-- **CupodTroll's then-clause in ANY frame** (fuel 2): a proof within `k` of "`opp` is `CupodBot k`" makes
`CupodTrollV7 k` DEFECT. -/
theorem troll7_then_V (k me opp : V) (h : LenProvableV TAct k (guardCode (⌜eqTmpl⌝ : V) (SV gCu 1 k) opp)) :
    EvalGraph 2 me opp (CupodTrollV7 k) 1 := by
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) me opp (pSearch k (⌜GtmplT7⌝ : V) (pConst 1) (pConst 0)) 1
  rw [EvalGraph.search_iff, guardCodeB_GtmplT7]
  left
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) me opp (pConst 1) 1 := EvalGraph.const_iff.mpr rfl
  rwa [zero_add] at e

/-- **CupodTroll's else-clause in any frame** (fuel 2): no proof ⇒ COOPERATE. -/
theorem troll7_else_V (k me opp : V) (h : ¬ LenProvableV TAct k (guardCode (⌜eqTmpl⌝ : V) (SV gCu 1 k) opp)) :
    EvalGraph 2 me opp (CupodTrollV7 k) 0 := by
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) me opp (pSearch k (⌜GtmplT7⌝ : V) (pConst 1) (pConst 0)) 0
  rw [EvalGraph.search_iff, guardCodeB_GtmplT7]
  right
  refine ⟨h, ?_⟩
  rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]

/-- **The transposed searcher's then-clause in any frame** (fuel 2): found ⇒ C. -/
theorem troll7T_then_V (k me opp : V) (h : LenProvableV TAct k (guardCode (⌜eqTmpl⌝ : V) (SV gDu 0 k) opp)) :
    EvalGraph 2 me opp (CupodTrollTV7 k) 0 := by
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) me opp (pSearch k (⌜GtmplT7A uST wST⌝ : V) (pConst 0) (pConst 1)) 0
  rw [EvalGraph.search_iff, guardCodeB_GtmplT7T]
  left
  refine ⟨h, ?_⟩
  rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]

/-- **`CupodTroll7 k` and the engine's `CupodTrollBot k` play identically**: in every frame, at every fuel,
the same results (the consulted guards have the same code, `guardCodeB_GtmplT7_nat`). -/
theorem evalGraph_CupodTroll7_iff (n me opp a k : ℕ) :
    EvalGraph n me opp (CupodTroll7 k) a ↔ EvalGraph n me opp (pcode (CupodTrollBot k)) a := by
  cases n with
  | zero => exact ⟨fun h ↦ absurd h EvalGraph.zero_iff, fun h ↦ absurd h EvalGraph.zero_iff⟩
  | succ n =>
    rw [pcode_CupodTrollBot]
    show EvalGraph (n + 1) me opp (pSearch k (⌜GtmplT7⌝ : ℕ) (pConst 1) (pConst 0)) a ↔ _
    rw [EvalGraph.search_iff, guardCodeB_GtmplT7_nat, EvalGraph.search_iff₆ (isSemiformula_tcode _)]

end troll7

/-! ### 7. The description layer of `CupodTrollV7 k` (`Cells/JustSlot.lean` §3 re-run) -/

section canonical

/-- The budget-independent inner part of CupodTroll's code. -/
noncomputable def innerT : ℕ := ppair (⌜GtmplT7⌝ : ℕ) (ppair (pConst 1) (pConst 0))

/-- The budget-independent inner part of the transposed searcher's code. -/
noncomputable def innerTT : ℕ := ppair (⌜GtmplT7A uST wST⌝ : ℕ) (ppair (pConst 0) (pConst 1))

lemma innerT_def : innerT = ppair (⌜GtmplT7⌝ : ℕ) (ppair (pConst 1) (pConst 0)) := rfl
lemma innerTT_def : innerTT = ppair (⌜GtmplT7A uST wST⌝ : ℕ) (ppair (pConst 0) (pConst 1)) := rfl

/- Closed constants built from the giant template: never to be evaluated. -/
attribute [irreducible] innerT innerTT

lemma cast_innerT : ((innerT : ℕ) : V) = ppair (⌜GtmplT7⌝ : V) (ppair (pConst 1) (pConst 0)) := by
  rw [innerT_def, cast_ppair, cast_ppair, cast_pConst, cast_pConst, coe_quote_sentence₇]
  push_cast
  rfl

lemma cast_innerTT : ((innerTT : ℕ) : V) = ppair (⌜GtmplT7A uST wST⌝ : V) (ppair (pConst 0) (pConst 1)) := by
  rw [innerTT_def, cast_ppair, cast_ppair, cast_pConst, cast_pConst, coe_quote_sentence₇]
  push_cast
  rfl

lemma CupodTrollV7_eq_inner (k : V) : CupodTrollV7 k = ppair 6 (ppair k (innerT : V)) + 1 := by
  rw [cast_innerT]; rfl
lemma CupodTrollTV7_eq_inner (k : V) : CupodTrollTV7 k = ppair 6 (ppair k (innerTT : V)) + 1 := by
  rw [cast_innerTT]; rfl

lemma CupodTrollV7_lt_CupodTrollTV7_iff (k : V) : CupodTrollV7 k < CupodTrollTV7 k ↔ innerT < innerTT := by
  rw [CupodTrollV7_eq_inner, CupodTrollTV7_eq_inner, pSearchInner_lt_iff, Nat.cast_lt]

lemma CupodTrollTV7_lt_CupodTrollV7_iff (k : V) : CupodTrollTV7 k < CupodTrollV7 k ↔ innerTT < innerT := by
  rw [CupodTrollV7_eq_inner, CupodTrollTV7_eq_inner, pSearchInner_lt_iff, Nat.cast_lt]

/-- The stored template of the canonical searcher. -/
noncomputable def gTd : ℕ := if innerT ≤ innerTT then (⌜GtmplT7⌝ : ℕ) else (⌜GtmplT7A uST wST⌝ : ℕ)
/-- Its then-branch. -/
noncomputable def pTd : ℕ := if innerT ≤ innerTT then pConst 1 else pConst 0
/-- Its else-branch. -/
noncomputable def qTd : ℕ := if innerT ≤ innerTT then pConst 0 else pConst 1
/-- The first re-valuation term of the description of `CupodTrollV7 k`. -/
noncomputable def uT : ClosedSemiterm LAct 0 :=
  if innerT < innerTT then cterm Act.C else if innerTT < innerT then cterm Act.D else numT 0
/-- The second re-valuation term of the description of `CupodTrollV7 k`. -/
noncomputable def wT : ClosedSemiterm LAct 0 :=
  if innerT < innerTT then cterm Act.D else if innerTT < innerT then cterm Act.C else numT 1

lemma CupodTrollV7_eq_cast (k : V) :
    CupodTrollV7 k = pSearch k ((⌜GtmplT7⌝ : ℕ) : V) ((pConst 1 : ℕ) : V) ((pConst 0 : ℕ) : V) := by
  unfold CupodTrollV7; rw [coe_quote_sentence₇, cast_pConst, cast_pConst]; push_cast; rfl

lemma CupodTrollTV7_eq_cast (k : V) :
    CupodTrollTV7 k = pSearch k ((⌜GtmplT7A uST wST⌝ : ℕ) : V) ((pConst 0 : ℕ) : V) ((pConst 1 : ℕ) : V) := by
  unfold CupodTrollTV7; rw [coe_quote_sentence₇, cast_pConst, cast_pConst]; push_cast; rfl

/-- **The canonical code of `CupodTrollV7 k` is a searcher with the (cast) `k`-independent inner triple.** -/
theorem dnum_CupodTrollV7 (k : V) : dnum (CupodTrollV7 k) = pSearch k (gTd : V) (pTd : V) (qTd : V) := by
  by_cases h : innerT ≤ innerTT
  · simp only [gTd, pTd, qTd, if_pos h]
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · rw [dnum_of_lt (by rw [swapcode_CupodTrollV7]; exact (CupodTrollV7_lt_CupodTrollTV7_iff k).mpr h')]
      exact CupodTrollV7_eq_cast k
    · rw [dnum_of_eq (by rw [swapcode_CupodTrollV7, CupodTrollV7_eq_inner, CupodTrollTV7_eq_inner, h'])]
      exact CupodTrollV7_eq_cast k
  · simp only [gTd, pTd, qTd, if_neg h]
    rw [dnum_of_gt (by rw [swapcode_CupodTrollV7]; exact (CupodTrollTV7_lt_CupodTrollV7_iff k).mpr (Nat.lt_of_not_le h)),
      swapcode_CupodTrollV7]
    exact CupodTrollTV7_eq_cast k

theorem dU_CupodTrollV7 (k : V) : dU (CupodTrollV7 k) = (⌜uT⌝ : V) := by
  unfold dU uT
  rw [swapcode_CupodTrollV7]
  by_cases h1 : innerT < innerTT
  · rw [if_pos ((CupodTrollV7_lt_CupodTrollTV7_iff k).mpr h1), if_pos h1, quote_cterm_C]
  · rw [if_neg (fun h ↦ h1 ((CupodTrollV7_lt_CupodTrollTV7_iff k).mp h)), if_neg h1]
    by_cases h2 : innerTT < innerT
    · rw [if_pos ((CupodTrollTV7_lt_CupodTrollV7_iff k).mpr h2), if_pos h2, quote_cterm_D]
    · rw [if_neg (fun h ↦ h2 ((CupodTrollTV7_lt_CupodTrollV7_iff k).mp h)), if_neg h2, quote_numT]
      simp

theorem dW_CupodTrollV7 (k : V) : dW (CupodTrollV7 k) = (⌜wT⌝ : V) := by
  unfold dW wT
  rw [swapcode_CupodTrollV7]
  by_cases h1 : innerT < innerTT
  · rw [if_pos ((CupodTrollV7_lt_CupodTrollTV7_iff k).mpr h1), if_pos h1, quote_cterm_D]
  · rw [if_neg (fun h ↦ h1 ((CupodTrollV7_lt_CupodTrollTV7_iff k).mp h)), if_neg h1]
    by_cases h2 : innerTT < innerT
    · rw [if_pos ((CupodTrollTV7_lt_CupodTrollV7_iff k).mpr h2), if_pos h2, quote_cterm_C]
    · rw [if_neg (fun h ↦ h2 ((CupodTrollTV7_lt_CupodTrollV7_iff k).mp h)), if_neg h2, quote_numT]
      simp

/-- The one-variable description term of CupodTroll, over `LAct`. -/
noncomputable def TT : Semiterm LAct Empty 1 := Semiterm.lMap emb (searchT1 gTd pTd qTd)

lemma lMap_swap_TT : Semiterm.lMap swap TT = TT := term_lMap_swap_emb _

/-- The code of `TT` (over `LAct`) is the `ℒₒᵣ` tower. -/
theorem quote_emb_TT :
    (⌜(Rew.emb TT : SyntacticSemiterm LAct 1)⌝ : V) =
    ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (gTd : V)) (ppairT (progT (pTd : V)) (progT (qTd : V))))) ^+ 𝟏 := by
  unfold TT
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, quote_emb_searchT1]

/-- **`TT` at the budget `k` denotes the canonical code of `CupodTrollV7 k`** (in `stdActV V`). -/
theorem val_TT_V (k : V) : TT.val (s := stdActV V) ![k] Empty.elim = dnum (CupodTrollV7 k) := by
  unfold TT
  rw [Semiterm.val_lMap, stdActV_lMap_emb, val_searchT1_V, dnum_CupodTrollV7]

/-- The `k`-independent re-valuation terms reconstruct `CupodTrollV7 k` from its canonical code. -/
theorem relabel_val_uT_wT_V (k : V) :
    relabel (uT.val (s := stdActV V) ![] Empty.elim) (wT.val (s := stdActV V) ![] Empty.elim)
      (dnum (CupodTrollV7 k)) = CupodTrollV7 k := by
  unfold uT wT
  by_cases h1 : innerT < innerTT
  · rw [if_pos h1, if_pos h1, val_cterm_C_V, val_cterm_D_V,
      dnum_of_lt (by rw [swapcode_CupodTrollV7]; exact (CupodTrollV7_lt_CupodTrollTV7_iff k).mpr h1), relabel_zero_one]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : innerTT < innerT
    · rw [if_pos h2, if_pos h2, val_cterm_D_V, val_cterm_C_V,
        dnum_of_gt (by rw [swapcode_CupodTrollV7]; exact (CupodTrollTV7_lt_CupodTrollV7_iff k).mpr h2)]
      exact swapcode_swapcode _
    · have h' : innerT = innerTT := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      rw [if_neg h2, if_neg h2, val_numT_V, val_numT_V, Nat.cast_zero, Nat.cast_one,
        dnum_of_eq (by rw [swapcode_CupodTrollV7, CupodTrollV7_eq_inner, CupodTrollTV7_eq_inner, h']), relabel_zero_one]

/-- The transposed re-valuation terms. -/
noncomputable def uTT : ClosedSemiterm LAct 0 := Semiterm.lMap swap uT
noncomputable def wTT : ClosedSemiterm LAct 0 := Semiterm.lMap swap wT

/-- The transposed descriptions reconstruct `CupodTrollTV7 k` from the canonical code of `CupodTrollV7 k`. -/
theorem relabel_val_uTT_wTT_V (k : V) :
    relabel (uTT.val (s := stdActV V) ![] Empty.elim) (wTT.val (s := stdActV V) ![] Empty.elim)
      (dnum (CupodTrollV7 k)) = CupodTrollTV7 k := by
  unfold uTT wTT uT wT
  by_cases h1 : innerT < innerTT
  · rw [if_pos h1, if_pos h1, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V,
      dnum_of_lt (by rw [swapcode_CupodTrollV7]; exact (CupodTrollV7_lt_CupodTrollTV7_iff k).mpr h1)]
    exact swapcode_CupodTrollV7 k
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : innerTT < innerT
    · rw [if_pos h2, if_pos h2, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
        dnum_of_gt (by rw [swapcode_CupodTrollV7]; exact (CupodTrollTV7_lt_CupodTrollV7_iff k).mpr h2),
        swapcode_CupodTrollV7, relabel_zero_one]
    · have h' : innerT = innerTT := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      rw [if_neg h2, if_neg h2, lMap_swap_numT, lMap_swap_numT, val_numT_V, val_numT_V, Nat.cast_zero,
        Nat.cast_one, dnum_of_eq (by rw [swapcode_CupodTrollV7, CupodTrollV7_eq_inner, CupodTrollTV7_eq_inner, h']),
        relabel_zero_one]
      have e : CupodTrollV7 k = CupodTrollTV7 k := by rw [CupodTrollV7_eq_inner, CupodTrollTV7_eq_inner, h']
      exact e

/-! #### The description hypotheses -/

/-- CupodTroll's own triple describes `CupodTrollV7 k` on codes. -/
lemma hX_troll7 (k : V) :
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb TT : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (CupodTrollV7 k)) := by
  rw [quote_emb_TT, termSubst_tower, dnum_CupodTrollV7]

lemma hU_troll7 (k : V) : (⌜uT⌝ : V) = dU (CupodTrollV7 k) := (dU_CupodTrollV7 k).symm
lemma hW_troll7 (k : V) : (⌜wT⌝ : V) = dW (CupodTrollV7 k) := (dW_CupodTrollV7 k).symm

/-- CupodTroll's own triple describes `CupodTrollV7 k` in `stdActV V`. -/
lemma hopp_troll7 (k : V) :
    relabel (uT.val (s := stdActV V) ![] Empty.elim) (wT.val (s := stdActV V) ![] Empty.elim)
      (TT.val (s := stdActV V) ![k] Empty.elim) = CupodTrollV7 k := by
  rw [val_TT_V]; exact relabel_val_uT_wT_V k

/-- The transposed triple describes `CupodTrollTV7 k` in `stdActV V`. -/
lemma hopp'_troll7 (k : V) :
    relabel ((Semiterm.lMap swap uT).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap wT).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap TT).val (s := stdActV V) ![k] Empty.elim) = CupodTrollTV7 k := by
  rw [lMap_swap_TT, val_TT_V]; exact relabel_val_uTT_wTT_V k

end canonical

end ArithS
