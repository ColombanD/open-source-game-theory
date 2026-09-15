import ArithS.Necessitation.IndRecRows

/-!
# ArithS.Necessitation.IndRec — case (ii) of the `axm` prologue: the induction-instance recognizer

`ProAxm.lean` discharges case (i) of the `axm` prologue (the finitely many standard axioms) and names case (ii)
— `p` an induction instance `IsSemiformula ℒₒᵣ 0 p ∧ InductionR (fun _ ↦ True) p`, possibly NONSTANDARD — as
the oracle `AxmIndOracle`. This file builds the object proof of `axchFact &ip` from the dossier of such a `p`,
in the vocabulary of `IndRecRows.lean` (`indRecL` and its predicates), PER MODEL (`∃ P`, as `proAxm_ok` and the
pin are), each pass an existence proof by `𝚺₁`-induction (on a counter, or structural on the code) rather than a
`Fixpoint` producer: the motives are `∃ P, HInv … P ∧ len P ≤ … ∧ neg (fact) ∈ finalCtx Γ P` with every free
index bounded, hence `𝚺₁`.

* §0 `HInv tbl E Γ P` — `ListOK tbl E 9 Γ P ∧ NoDrop' P ∧ HornOnly P ∧ shiftsV P = 0` (a shift-free Horn list),
  its algebra, the definability of the new fact codes.
* §1 the `qqAlls` walk: from the dossier of `qqAlls b m` at `&ip`, `allsFact &ip &(ip+m) (cTV m)` in `m + 1`
  steps (`qqAllsZero` at `b`, then `m` × `qqAllsSucc` along the dossier's `allFact`s).
* §2 the `≤` chain on chain numerals: `leFact (cTV a) (cTV (a + d))` in `d + 1` steps.
* §3 the `bs` pass: bottom-up over the dossier of an `ℒₒᵣ`-code, `bsTFact (cTV n) (cTV (termBV t)) &i`,
  `bsVFact …`, `bsFFact (cTV n) (cTV (bv r)) &i` — `ℒₒᵣ`-formation and the EXACT `bv` in one pass.
* §4 `fvSeq`, the substitution instances, the body, and the assembly `axmInd_ok` (see the closing docstring
  for what is delivered and what remains).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open PeanoMinus ISigma0 ISigma1
open LAct

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

/-- Sentinel: the generated table has its thirty-four rows. -/
example : indRecExtraRowCount = 34 := rfl

/-! ## 0. The shift-free Horn invariant and the fact codes -/

section hinv

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **A shift-free Horn list** applicable at cap `9` at `Γ`. -/
def HInv (tbl E Γ P : V) : Prop :=
  ListOK tbl E ((9 : ℕ) : V) Γ P ∧ NoDrop' P ∧ HornOnly P ∧ shiftsV P = 0

instance hInv_definable : 𝚫₁-Relation₄ (HInv : V → V → V → V → Prop) := by
  unfold HInv; definability

lemma HInv.nil (tbl E Γ : V) : HInv tbl E Γ 0 :=
  ⟨listOK_nil _ _ _ _, noDrop'_nil, hornOnly_nil, shiftsV_nil⟩

lemma HInv.append {tbl E Γ P₁ P₂ : V} (h₁ : HInv tbl E Γ P₁) (h₂ : HInv tbl E (finalCtx Γ P₁) P₂) :
    HInv tbl E Γ (appendV P₁ P₂) :=
  ⟨listOK_appendV h₁.1 h₂.1, noDrop'_appendV h₁.2.1 h₂.2.1, hornOnly_appendV h₁.2.2.1 h₂.2.2.1,
    by rw [shiftsV_appendV, h₁.2.2.2, h₂.2.2.2, add_zero]⟩

/-- One tag-`0` step at cap `8` (the `iok_`/`fok_` shape). -/
lemma HInv.single {tbl E Γ s : V} (h : StepOK tbl E ((8 : ℕ) : V) Γ s) (htag : sTag s = 0) :
    HInv tbl E Γ ?[s] :=
  ⟨listOK_single (h.mono (by exact_mod_cast (by decide : 8 ≤ 9))), noDrop'_single (Or.inl htag),
    hornOnly_single (Or.inl htag), shiftsV_single_tag0 htag⟩

/-- A step appended to a list. -/
lemma HInv.snoc {tbl E Γ P s : V} (hP : HInv tbl E Γ P) (h : StepOK tbl E ((8 : ℕ) : V) (finalCtx Γ P) s)
    (htag : sTag s = 0) : HInv tbl E Γ (appendV P ?[s]) :=
  hP.append (HInv.single h htag)

lemma HInv.mem {tbl E Γ P x : V} (h : HInv tbl E Γ P) (hx : x ∈ Γ) : x ∈ finalCtx Γ P :=
  mem_final0 h.2.1 h.2.2.2 hx

lemma HInv.isFormulaSet {tbl N E Γ P : V} (htbl : TableOK tbl N) (hΓ : IsFormulaSet LAct Γ) (h : HInv tbl E Γ P) :
    IsFormulaSet LAct (finalCtx Γ P) :=
  finalCtx_isFormulaSet 9 htbl hΓ h.1

lemma HInv.dossF {tbl E Γ P W n r i : V} (h : HInv tbl E Γ P) (hD : DossF W Γ n r i) : DossF W (finalCtx Γ P) n r i := by
  have := dossF_transport' h.2.1 hD
  rwa [h.2.2.2, add_zero] at this
lemma HInv.dossT {tbl E Γ P W n t i : V} (h : HInv tbl E Γ P) (hD : DossT W Γ n t i) : DossT W (finalCtx Γ P) n t i := by
  have := dossT_transport' h.2.1 hD
  rwa [h.2.2.2, add_zero] at this
lemma HInv.dossV {tbl E Γ P W n k v j i : V} (h : HInv tbl E Γ P) (hD : DossV W Γ n k v j i) :
    DossV W (finalCtx Γ P) n k v j i := by
  have := dossV_transport' h.2.1 hD
  rwa [h.2.2.2, add_zero] at this

lemma HInv.sizeOK {tbl E Γ P Q D : V} (h : HInv tbl E Γ P) : SizeOK Q D P := sizeOK_of_hornOnly h.2.2.1

/-! ### Context monotonicity of shift-free Horn lists (`Cert` Part 0's `ctxAfter_mono`/`ctxVec_mono`, lifted to `ListOK`) -/

lemma HornOK.mono_ctxI {tbl E M Γ Γ' s : V} (hsub : Γ ⊆ Γ') (h : HornOK tbl E M Γ s) : HornOK tbl E M Γ' s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun k hk ↦ hsub (h.2.2.2.2.2 k hk)⟩

/-- A Horn step stays applicable in a larger formula-set context. -/
lemma StepOK.mono_ctxI {tbl E M Γ Γ' s : V} (hΓ' : IsFormulaSet LAct Γ') (hsub : Γ ⊆ Γ')
    (htag : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2) (h : StepOK tbl E M Γ s) : StepOK tbl E M Γ' s := by
  obtain ⟨-, h⟩ := h
  refine ⟨hΓ', ?_⟩
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
  · exact Or.inl ⟨h1, h2.mono_ctxI hsub, h3⟩
  · exact Or.inr (Or.inl ⟨h1, h2.mono_ctxI hsub, h3⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2.mono_ctxI hsub, h3⟩))
  all_goals (rcases htag with h0 | h0 | h0 <;> rw [h0] at h1 <;> norm_num at h1)

lemma listOK_mono_auxI (M : ℕ) {tbl N E Γ Γ' S : V} (htbl : TableOK tbl N) (hΓ' : IsFormulaSet LAct Γ')
    (hS : HornOnly S) (hsub : Γ ⊆ Γ') (h : ListOK tbl E (M : V) Γ S) :
    ∀ j ≤ len S, (∀ i < j, StepOK tbl E (M : V) (ctxVec Γ' S).[i] S.[i]) ∧ IsFormulaSet LAct (ctxVec Γ' S).[j] := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    refine ⟨fun i hi ↦ by simp at hi, ?_⟩
    simpa using hΓ'
  | succ j ih =>
    intro hj
    have hj' : j < len S := lt_of_lt_of_le (lt_add_one j) hj
    obtain ⟨ih₁, ih₂⟩ := ih (le_of_lt hj')
    have hstep : StepOK tbl E (M : V) (ctxVec Γ' S).[j] S.[j] :=
      (h j hj').mono_ctxI ih₂ (ctxVec_mono (noDrop_of_hornOnly hS) hsub j (le_of_lt hj')) (hS j hj')
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with hlt | rfl
      · exact ih₁ i hlt
      · exact hstep
    · rw [nth_ctxVec_succ Γ' S hj']
      exact isFormulaSet_ctxAfter M htbl hstep

/-- **A shift-free Horn list transfers to any larger formula-set context.** -/
theorem HInv.mono_ctx {tbl N E Γ Γ' P : V} (htbl : TableOK tbl N) (hΓ' : IsFormulaSet LAct Γ') (hsub : Γ ⊆ Γ')
    (h : HInv tbl E Γ P) : HInv tbl E Γ' P :=
  ⟨fun i hi ↦ (listOK_mono_auxI 9 htbl hΓ' h.2.2.1 hsub h.1 (len P) le_rfl).1 i hi, h.2.1, h.2.2.1, h.2.2.2⟩

lemma HInv.finalCtx_mono {tbl E Γ Γ' P : V} (h : HInv tbl E Γ P) (hsub : Γ ⊆ Γ') : finalCtx Γ P ⊆ finalCtx Γ' P :=
  ArithS.finalCtx_mono (noDrop_of_hornOnly h.2.2.1) hsub

lemma len_single (s : V) : len (?[s] : V) = 1 := by simp

/-! ### Definability of the fact codes used in the motives -/

instance allsFact_definable : 𝚺₁-Function₃ (allsFact : V → V → V → V) := by
  have : (allsFact : V → V → V → V) = fun p b m ↦ subst LAct (p ∷ b ∷ m ∷ 0) Palls := rfl
  rw [this]; definability
instance bsTFact_definable : 𝚺₁-Function₃ (bsTFact : V → V → V → V) := by
  have : (bsTFact : V → V → V → V) = fun n m t ↦ subst LAct (n ∷ m ∷ t ∷ 0) PbsT := rfl
  rw [this]; definability
instance bsVFact_definable : 𝚺₁-Function₄ (bsVFact : V → V → V → V → V) := by
  have : (bsVFact : V → V → V → V → V) = fun n m k v ↦ subst LAct (n ∷ m ∷ k ∷ v ∷ 0) PbsV := rfl
  rw [this]; definability
instance bsFFact_definable : 𝚺₁-Function₃ (bsFFact : V → V → V → V) := by
  have : (bsFFact : V → V → V → V) = fun n m p ↦ subst LAct (n ∷ m ∷ p ∷ 0) PbsF := rfl
  rw [this]; definability
instance fvSeqFact_definable : 𝚺₁-Function₃ (fvSeqFact : V → V → V → V) := by
  have : (fvSeqFact : V → V → V → V) = fun w j m ↦ subst LAct (w ∷ j ∷ m ∷ 0) PfvSeq := rfl
  rw [this]; definability

/-- `2 * j + 1 ≤ E` from `2 * m + 1 ≤ E` and `j ≤ m`. -/
lemma cTV_cap {j m E : V} (hj : j ≤ m) (hE : 2 * m + 1 ≤ E) : termLen LAct (cTV j) ≤ E :=
  termLen_cTV_le (le_trans (add_le_add (mul_le_mul_of_nonneg_left hj zero_le) le_rfl) hE)

end hinv

/-! ## 1. The `qqAlls` walk -/

section qqAllsWalk

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The dossier of `qqAlls b m` at `&ip` holds the dossier of every `qqAlls b j` (`j + d = m`) at depth `d`,
offset `ip + d`. -/
lemma dossF_qqAlls {tbl N W Γ b m ip : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hb : IsSemiformula LAct m b) (hD : DossF W Γ 0 (qqAlls b m) ip) :
    ∀ d ≤ m, ∀ j, j + d = m → DossF W Γ d (qqAlls b j) (ip + d) := by
  intro d
  induction d using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _ j hj
    rw [add_zero] at hj
    subst hj
    simpa using hD
  | succ d ih =>
    intro hd j hj
    have hd' : d ≤ m := le_trans le_self_add hd
    have hj' : (j + 1) + d = m := by rw [← hj]; ring
    have h := ih hd' (j + 1) hj'
    rw [qqAlls_succ] at h
    have hbj : IsSemiformula LAct (d + 1) (qqAlls b j) := by
      have : IsSemiformula LAct ((d + 1) + j) b := by rw [show (d + 1) + j = m by rw [← hj]; ring]; exact hb
      exact this.qqAlls
    have := (dossF_all htbl hW hWp hbj h).2.2
    rwa [add_assoc] at this

/-- **The `qqAlls` walk**: from the dossier of `qqAlls b m` at `&ip`, a shift-free Horn list of length `≤ m + 1`
leaving `allsFact &ip &(ip + m) (cTV m)` (`p = qqAlls b m` at the eigenvariables of `p` and `b`). -/
theorem qqAllsWalk_ok {tbl N E Γ b m ip : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl)
    (hΓ : IsFormulaSet LAct Γ) (hb : IsSemiformula LAct m b) (hD : DossF walkPieces Γ 0 (qqAlls b m) ip)
    (hE : 2 * m + 1 ≤ E) (hEi : ip + m + 1 ≤ E) :
    ∃ P : V, HInv tbl E Γ P ∧ len P ≤ m + 1 ∧
      neg LAct (allsFact (^&ip) (^&(ip + m)) (cTV m)) ∈ finalCtx Γ P := by
  have hW := hT.walkTable
  have key : ∀ j ≤ m, ∀ a ≤ m, a + j = m → ∃ P : V, HInv tbl E Γ P ∧ len P ≤ j + 1 ∧
      neg LAct (allsFact (^&(ip + a)) (^&(ip + m)) (cTV j)) ∈ finalCtx Γ P := by
    intro j
    induction j using ISigma1.sigma1_succ_induction with
    | hP => definability
    | zero =>
      intro _ a _ ha
      rw [add_zero] at ha
      subst ha
      obtain ⟨hlen, hrow⟩ := hT.qqAllsZero
      have hw : IsSemiterm LAct 0 (^&(ip + a) : V) := by simp
      have hEw : termLen LAct (^&(ip + a) : V) ≤ E := termLen_fvar_le hEi
      obtain ⟨hok, htag, hctx⟩ := iok_qqAllsZero htbl rfl hlen hrow hΓ hw hEw
      refine ⟨_, HInv.single hok htag, by rw [len_single, zero_add], ?_⟩
      rw [finalCtx_single, hctx, cTV_zero]
      exact mem_insert_self'
    | succ j ih =>
      intro hj a ha hja
      have hj' : j ≤ m := le_trans le_self_add hj
      have ha1 : a + 1 ≤ m := by rw [← hja]; exact add_le_add le_rfl (le_add_self : 1 ≤ j + 1)
      obtain ⟨P₀, hP₀, hl₀, hf₀⟩ := ih hj' (a + 1) ha1 (by rw [← hja]; ring)
      -- the dossier's `allFact` at depth `a`
      have hDa := dossF_qqAlls htbl hW rfl hb hD a (le_trans le_self_add ha1) (j + 1) (by rw [← hja]; ring)
      rw [qqAlls_succ] at hDa
      have hbj : IsSemiformula LAct (a + 1) (qqAlls b j) := by
        have : IsSemiformula LAct ((a + 1) + j) b := by rw [show (a + 1) + j = m by rw [← hja]; ring]; exact hb
        exact this.qqAlls
      have hall := (dossF_all htbl hW rfl hbj hDa).1
      have hΓ₁ := hP₀.isFormulaSet htbl hΓ
      obtain ⟨hlen, hrow⟩ := hT.qqAllsSucc
      have hwm : IsSemiterm LAct 0 (cTV j) := cTV_semiterm_LAct 0 _
      have hEwm : termLen LAct (cTV j) ≤ E := cTV_cap hj' hE
      have hwb : IsSemiterm LAct 0 (^&(ip + m) : V) := by simp
      have hEwb : termLen LAct (^&(ip + m) : V) ≤ E := termLen_fvar_le hEi
      have hwp : IsSemiterm LAct 0 (^&(ip + (a + 1)) : V) := by simp
      have hEwp : termLen LAct (^&(ip + (a + 1)) : V) ≤ E :=
        termLen_fvar_le (le_trans (add_le_add (add_le_add le_rfl ha1) le_rfl) hEi)
      have hwpp : IsSemiterm LAct 0 (^&(ip + a) : V) := by simp
      have hEwpp : termLen LAct (^&(ip + a) : V) ≤ E :=
        termLen_fvar_le (le_trans (add_le_add (add_le_add le_rfl (le_trans le_self_add ha1)) le_rfl) hEi)
      have hall' : neg LAct (allFact (^&(ip + a)) (^&(ip + (a + 1)))) ∈ finalCtx Γ P₀ := by
        rw [← add_assoc]; exact hP₀.mem hall
      obtain ⟨hok, htag, hctx⟩ := iok_qqAllsSucc htbl rfl hlen hrow hΓ₁ hwm hEwm hwb hEwb hwp hEwp hwpp hEwpp hf₀ hall'
      refine ⟨_, hP₀.snoc hok htag, ?_, ?_⟩
      · rw [len_appendV, len_single]; exact add_le_add hl₀ le_rfl
      · rw [finalCtx_appendV_single, hctx, ← cTV_succ]
        exact mem_insert_self'
  obtain ⟨P, hP, hl, hf⟩ := key m le_rfl 0 zero_le (zero_add m)
  rw [add_zero] at hf
  exact ⟨P, hP, hl, hf⟩

end qqAllsWalk

/-! ## 2. The `≤` chain on chain numerals -/

section leChain

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `leFact (cTV a) (cTV (a + d))` in `d + 1` shift-free Horn steps (`leRefl`, then `d` × `leSuccR`). -/
theorem leChain_ok {tbl N E Γ a d : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl)
    (hΓ : IsFormulaSet LAct Γ) (hE : 2 * (a + d) + 1 ≤ E) :
    ∃ P : V, HInv tbl E Γ P ∧ len P ≤ d + 1 ∧ neg LAct (leFact (cTV a) (cTV (a + d))) ∈ finalCtx Γ P := by
  have hF := hT.proTable.frag1Table
  have hEa : termLen LAct (cTV a) ≤ E := cTV_cap le_self_add hE
  induction d using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero =>
    obtain ⟨hok, htag, hctx⟩ := fok_leRefl htbl hF rfl hΓ (cTV_semiterm_LAct 0 a) hEa
    refine ⟨_, HInv.single hok htag, by rw [len_single, zero_add], ?_⟩
    rw [finalCtx_single, hctx, add_zero]
    exact mem_insert_self'
  | succ d ih =>
    have hE' : 2 * (a + d) + 1 ≤ E :=
      le_trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl le_self_add) zero_le) le_rfl) hE
    obtain ⟨P₀, hP₀, hl₀, hf₀⟩ := ih hE'
    have hΓ₁ := hP₀.isFormulaSet htbl hΓ
    obtain ⟨hlen, hrow⟩ := hT.leSuccR
    obtain ⟨hok, htag, hctx⟩ := iok_leSuccR htbl rfl hlen hrow hΓ₁ (cTV_semiterm_LAct 0 a) hEa
      (cTV_semiterm_LAct 0 (a + d)) (cTV_cap (le_refl (a + d)) hE') hf₀
    refine ⟨_, hP₀.snoc hok htag, ?_, ?_⟩
    · rw [len_appendV, len_single]; exact add_le_add hl₀ le_rfl
    · rw [finalCtx_appendV_single, hctx, ← cTV_succ, ← add_assoc]
      exact mem_insert_self'

/-- The chain between two values `x ≤ y` (`y = x + (y - x)`). -/
theorem leChain_ok' {tbl N E Γ x y : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl)
    (hΓ : IsFormulaSet LAct Γ) (hxy : x ≤ y) (hE : 2 * y + 1 ≤ E) :
    ∃ P : V, HInv tbl E Γ P ∧ len P ≤ y + 1 ∧ neg LAct (leFact (cTV x) (cTV y)) ∈ finalCtx Γ P := by
  obtain ⟨d, rfl⟩ : ∃ d, y = x + d := ⟨y - x, (add_tsub_cancel_of_le hxy).symm⟩
  obtain ⟨P, hP, hl, hf⟩ := leChain_ok htbl hT hΓ hE
  exact ⟨P, hP, le_trans hl (add_le_add le_add_self le_rfl), hf⟩

end leChain

/-! ## 3. The `bs` pass: `ℒₒᵣ`-formation and the exact bound-variable count, bottom-up -/

section bsPass

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 3.1 Vector helpers -/

lemma isSemitermVec_takeLast_LOR {k n v : V} (hv : IsSemitermVec ℒₒᵣ k n v) :
    ∀ j ≤ k, IsSemitermVec ℒₒᵣ j n (takeLast v j) := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hj
    have hlt : k - (j + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have hjl : j < len v := by rw [hv.lh]; exact lt_of_lt_of_le (lt_add_one j) hj
    rw [takeLast_succ_of_lt hjl, hv.lh]
    exact IsSemitermVec.cons_iff.mpr ⟨hv.nth hlt, ih (le_trans le_self_add hj)⟩

lemma listMax_termBVVec_takeLast_le {k n v : V} (hv : IsSemitermVec ℒₒᵣ k n v) :
    ∀ j ≤ k, listMax (termBVVec ℒₒᵣ j (takeLast v j)) ≤ n := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    rw [takeLast_zero]
    unfold termBVVec
    rw [IsUTerm.BV.construction.resultVec_nil ℒₒᵣ ![]]
    simp
  | succ j ih =>
    intro hj
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hj
    have hlt : k - (j + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have hjl : j < len v := by rw [hv.lh]; exact lt_of_lt_of_le (lt_add_one j) hj
    have hw := isSemitermVec_takeLast_LOR hv j (le_trans le_self_add hj)
    rw [takeLast_succ_of_lt hjl, hv.lh, termBVVec_cons (hv.nth hlt).isUTerm hw.isUTermVec, listMax_adjoin]
    exact max_le (IsSemiterm.def.mp (hv.nth hlt)).2 (ih (le_trans le_self_add hj))

/-- The bound `descCountT + 1 ≤ 2 · termLen` of the term walk, standalone. -/
lemma descCountT_succ_le {tbl N n t : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (ht : IsSemiterm LAct n t) :
    descCountT walkPieces n t + 1 ≤ 2 * termLen LAct t :=
  (describeT_ok htbl hW ht (E := 2 * n + 2 * termLen LAct t + 8) le_rfl (Γ := 0) IsFormulaSet.empty).2.2.2.1

lemma descCountF_succ_le' {tbl N n r : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hr : IsSemiformula LAct n r) :
    descCountF walkPieces n r + 1 ≤ 2 * formulaLen LAct r :=
  (describeF_ok htbl hW hr (E := 2 * n + 2 * formulaLen LAct r + 8) le_rfl (Γ := 0) IsFormulaSet.empty).2.2.2.1

lemma cTV_one_eq : cTV (1 : V) = (𝟎 : V) ^+ 𝟏 := by rw [← zero_add (1 : V), cTV_succ, cTV_zero]
lemma cTV_two_eq : cTV (2 : V) = (𝟎 : V) ^+ 𝟏 ^+ 𝟏 := by
  rw [show (2 : V) = 0 + 1 + 1 by norm_num, cTV_succ, cTV_succ, cTV_zero]
lemma cT_two : (cT 2 : V) = (𝟎 : V) ^+ 𝟏 ^+ 𝟏 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, cT_succ, cT_one]

/-! ### 3.2 The closed symbol steps -/

/-- The closed `ℒₒᵣ` function-symbol fact `isFuncORFact (cTV k) (cTV f)`, one step. -/
lemma isFuncOR_step {tbl N E Γ k f : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hkf : (ℒₒᵣ).IsFunc k f) :
    ∃ P : V, HInv tbl E Γ P ∧ len P ≤ 1 ∧ neg LAct (isFuncORFact (cTV k) (cTV f)) ∈ finalCtx Γ P := by
  rcases isFunc_LOR_iff_V.mp hkf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hlen, hrow⟩ := hT.isFuncOR_zero
    obtain ⟨hok, htag, hctx⟩ := iok_isFuncOR_zero htbl rfl hlen hrow hΓ
    refine ⟨_, HInv.single hok htag, by rw [len_single], ?_⟩
    rw [finalCtx_single, hctx, cTV_zero]; exact mem_insert_self'
  · obtain ⟨hlen, hrow⟩ := hT.isFuncOR_one
    obtain ⟨hok, htag, hctx⟩ := iok_isFuncOR_one htbl rfl hlen hrow hΓ
    refine ⟨_, HInv.single hok htag, by rw [len_single], ?_⟩
    rw [finalCtx_single, hctx, cTV_zero, cTV_one_eq, ← cT_one]; exact mem_insert_self'
  · obtain ⟨hlen, hrow⟩ := hT.isFuncOR_add
    obtain ⟨hok, htag, hctx⟩ := iok_isFuncOR_add htbl rfl hlen hrow hΓ
    refine ⟨_, HInv.single hok htag, by rw [len_single], ?_⟩
    rw [finalCtx_single, hctx, cTV_zero, cTV_two_eq, ← cT_two]; exact mem_insert_self'
  · obtain ⟨hlen, hrow⟩ := hT.isFuncOR_mul
    obtain ⟨hok, htag, hctx⟩ := iok_isFuncOR_mul htbl rfl hlen hrow hΓ
    refine ⟨_, HInv.single hok htag, by rw [len_single], ?_⟩
    rw [finalCtx_single, hctx, cTV_one_eq, cTV_two_eq, ← cT_two, ← cT_one]; exact mem_insert_self'

/-- The closed `ℒₒᵣ` relation-symbol fact `isRelORFact (cTV k) (cTV R)`, one step. -/
lemma isRelOR_step {tbl N E Γ k R : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hkR : (ℒₒᵣ).IsRel k R) :
    ∃ P : V, HInv tbl E Γ P ∧ len P ≤ 1 ∧ neg LAct (isRelORFact (cTV k) (cTV R)) ∈ finalCtx Γ P := by
  rcases isRel_LOR_iff_V.mp hkR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hlen, hrow⟩ := hT.isRelOR_eq
    obtain ⟨hok, htag, hctx⟩ := iok_isRelOR_eq htbl rfl hlen hrow hΓ
    refine ⟨_, HInv.single hok htag, by rw [len_single], ?_⟩
    rw [finalCtx_single, hctx, cTV_zero, cTV_two_eq, ← cT_two]; exact mem_insert_self'
  · obtain ⟨hlen, hrow⟩ := hT.isRelOR_lt
    obtain ⟨hok, htag, hctx⟩ := iok_isRelOR_lt htbl rfl hlen hrow hΓ
    refine ⟨_, HInv.single hok htag, by rw [len_single], ?_⟩
    rw [finalCtx_single, hctx, cTV_one_eq, cTV_two_eq, ← cT_two, ← cT_one]; exact mem_insert_self'

/-! ### 3.3 Arithmetic of the length bounds -/

/-- `4a²c + b²c + c ≤ (2a + b)²c` for `1 ≤ a`, `1 ≤ b`. -/
lemma sq_bound_adj {a b c : V} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    4 * a * a * c + b * b * c + c ≤ (2 * a + b) * (2 * a + b) * c := by
  have h1 : c ≤ 4 * a * b * c := by
    calc c = 1 * 1 * c := by ring
      _ ≤ 4 * a * b * c := by
        refine mul_le_mul (mul_le_mul ?_ hb zero_le zero_le) le_rfl zero_le zero_le
        calc (1 : V) ≤ 4 := by norm_num
          _ = 4 * 1 := by ring
          _ ≤ 4 * a := mul_le_mul_of_nonneg_left ha zero_le
  calc 4 * a * a * c + b * b * c + c ≤ 4 * a * a * c + b * b * c + 4 * a * b * c := add_le_add le_rfl h1
    _ = (2 * a + b) * (2 * a + b) * c := by ring

/-- `(2S + 1)²c + 2 ≤ 4(S + 1)²c` for `1 ≤ c`. -/
lemma sq_bound_func {S c : V} (hc : 1 ≤ c) :
    (2 * S + 1) * (2 * S + 1) * c + 2 ≤ 4 * (S + 1) * (S + 1) * c := by
  have h2 : (2 : V) ≤ (4 * S + 3) * c := by
    calc (2 : V) = 2 * 1 := by ring
      _ ≤ (4 * S + 3) * c := mul_le_mul (le_trans (by norm_num) (le_add_self : (3 : V) ≤ 4 * S + 3)) hc zero_le zero_le
  calc (2 * S + 1) * (2 * S + 1) * c + 2 ≤ (2 * S + 1) * (2 * S + 1) * c + (4 * S + 3) * c := add_le_add le_rfl h2
    _ = 4 * (S + 1) * (S + 1) * c := by ring

/-- `4a²c + 4b²c + c ≤ 4(a + b + 1)²c`. -/
lemma sq_bound_bin {a b c : V} :
    4 * a * a * c + 4 * b * b * c + c ≤ 4 * (a + b + 1) * (a + b + 1) * c := by
  calc 4 * a * a * c + 4 * b * b * c + c ≤ 4 * a * a * c + 4 * b * b * c + c + (8 * a * b + 8 * a + 8 * b + 3) * c := le_self_add
    _ = 4 * (a + b + 1) * (a + b + 1) * c := by ring

/-- `4a²c + 1 ≤ 4(a + 1)²c` for `1 ≤ c`. -/
lemma sq_bound_un {a c : V} (hc : 1 ≤ c) : 4 * a * a * c + 1 ≤ 4 * (a + 1) * (a + 1) * c := by
  have h1 : (1 : V) ≤ (8 * a + 4) * c :=
    le_trans (by norm_num : (1 : V) ≤ 4) (le_trans (le_add_self : (4 : V) ≤ 8 * a + 4)
      (by calc 8 * a + 4 = (8 * a + 4) * 1 := by ring
            _ ≤ (8 * a + 4) * c := mul_le_mul_of_nonneg_left hc zero_le))
  calc 4 * a * a * c + 1 ≤ 4 * a * a * c + (8 * a + 4) * c := add_le_add le_rfl h1
    _ = 4 * (a + 1) * (a + 1) * c := by ring

/-- `1 ≤ 4a²c` for `1 ≤ a`, `1 ≤ c`; and `b + 2 ≤ 4a²c` when `b + 1 ≤ a`. -/
lemma one_le_sq4 {a c : V} (ha : 1 ≤ a) (hc : 1 ≤ c) : 1 ≤ 4 * a * a * c := by
  calc (1 : V) = 1 * 1 * 1 := by ring
    _ ≤ 4 * a * a * c := mul_le_mul (mul_le_mul (le_trans ha (by
        calc a = 1 * a := by ring
          _ ≤ 4 * a := mul_le_mul_of_nonneg_right (by norm_num) zero_le)) ha zero_le zero_le) hc zero_le zero_le

lemma succ_le_sq {a c : V} (ha : 1 ≤ a) (hc : 1 ≤ c) : a + 1 ≤ 4 * a * a * c := by
  calc a + 1 ≤ a + a := add_le_add le_rfl ha
    _ = 2 * a * 1 * 1 := by ring
    _ ≤ 4 * a * a * c := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (by norm_num) zero_le) ha zero_le zero_le) hc zero_le zero_le

/-! ### 3.4 Vectors, terms -/

/-- The entry invariant of the term pass (what the vector pass assumes of each entry). -/
def BsTInv (tbl E Γ B Bi n t : V) : Prop :=
  ∀ i ≤ Bi, i + 2 * termLen LAct t ≤ Bi → DossT walkPieces Γ n t i →
    ∃ P : V, HInv tbl E Γ P ∧ len P ≤ 4 * termLen LAct t * termLen LAct t * (B + 3) ∧
      neg LAct (bsTFact (cTV n) (cTV (termBV ℒₒᵣ t)) (^&i)) ∈ finalCtx Γ P

instance bsTInv_definable :
    𝚺₁.Definable (fun v : Fin 7 → V ↦ BsTInv (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := by
  unfold BsTInv; definability

set_option maxHeartbeats 1000000 in
/-- **The `bs` pass on the last `j` entries of a vector**, given the entries' term passes: from the dossier of the
last `j` entries of `v` at `&i` (`i + 2S + 1 ≤ Bi`, `S` the sum of their lengths), a shift-free Horn list of length
`≤ (2S + 1)²(B + 3)` leaving `bsVFact (cTV n) (cTV (listMax (termBVVec j (takeLast v j)))) (cTV j) (vRef i j)`. -/
theorem bsV_of_entries {tbl N E Γ B Bi n k v : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hnB : n ≤ B) (hE : 2 * B + 1 ≤ E) (hEi : Bi + 1 ≤ E)
    (hv : IsSemitermVec ℒₒᵣ k n v) (ih : ∀ a < k, BsTInv tbl E Γ B Bi n v.[a]) :
    ∀ j ≤ k, ∀ i ≤ Bi, i + 2 * listSum (termLenVec LAct j (takeLast v j)) + 1 ≤ Bi →
      DossV walkPieces Γ n k v j i →
      ∃ P : V, HInv tbl E Γ P ∧
        len P ≤ (2 * listSum (termLenVec LAct j (takeLast v j)) + 1) * (2 * listSum (termLenVec LAct j (takeLast v j)) + 1) * (B + 3) ∧
        neg LAct (bsVFact (cTV n) (cTV (listMax (termBVVec ℒₒᵣ j (takeLast v j)))) (cTV j) (vRef i j)) ∈ finalCtx Γ P := by
  have hW := hT.walkTable
  have hB3 : (1 : V) ≤ B + 3 := le_trans (by norm_num) le_add_self
  have hEn : termLen LAct (cTV n) ≤ E := cTV_cap hnB hE
  have hwn : IsSemiterm LAct 0 (cTV n) := cTV_semiterm_LAct 0 n
  have hvL : IsSemitermVec LAct k n v := IsSemitermVec.LAct_of_LOR hv
  have hlv : len v = k := hv.lh
  intro j
  induction j using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero =>
    intro _ i _ _ _
    obtain ⟨hlen, hrow⟩ := hT.bsVNil
    obtain ⟨hok, htag, hctx⟩ := iok_bsVNil htbl rfl hlen hrow hΓ hwn hEn
    have e0 : listSum (termLenVec LAct 0 (takeLast v 0)) = 0 := by rw [takeLast_zero, termLenVec_nil, listSum_nil]
    refine ⟨_, HInv.single hok htag, ?_, ?_⟩
    · rw [len_single, e0]
      calc (1 : V) = 1 * 1 * 1 := by ring
        _ ≤ (2 * 0 + 1) * (2 * 0 + 1) * (B + 3) :=
          mul_le_mul (mul_le_mul (le_of_eq (by ring)) (le_of_eq (by ring)) zero_le zero_le) hB3 zero_le zero_le
    · rw [finalCtx_single, hctx, takeLast_zero, vRef_zero, cTV_zero]
      unfold termBVVec
      rw [IsUTerm.BV.construction.resultVec_nil ℒₒᵣ ![], listMax_nil, cTV_zero]
      exact mem_insert_self'
  | succ j ihj =>
    intro hj i hi hib hDv
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hj
    have hlt : k - (j + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have hjl : j < len v := by rw [hlv]; exact lt_of_lt_of_le (lt_add_one j) hj
    have hj' : j ≤ k := le_trans le_self_add hj
    have ht : IsSemiterm ℒₒᵣ n v.[k - (j + 1)] := hv.nth hlt
    have htL : IsSemiterm LAct n v.[k - (j + 1)] := hvL.nth hlt
    have hw := isSemitermVec_takeLast_LOR hv j hj'
    have hwL : IsUTermVec LAct j (takeLast v j) := isUTermVec_takeLast hvL j hj'
    have htake : takeLast v (j + 1) = v.[k - (j + 1)] ∷ takeLast v j := by rw [takeLast_succ_of_lt hjl, hlv]
    have hSsucc : listSum (termLenVec LAct (j + 1) (takeLast v (j + 1))) =
        termLen LAct v.[k - (j + 1)] + listSum (termLenVec LAct j (takeLast v j)) := by
      rw [htake, termLenVec_cons htL.isUTerm hwL, listSum_adjoin]
    rw [hSsucc] at hib ⊢
    obtain ⟨hadj, _, hDt, hDtail⟩ := dossV_succ htbl hW rfl hvL hj hDv
    have hct2 : descCountT walkPieces n v.[k - (j + 1)] + 1 ≤ 2 * termLen LAct v.[k - (j + 1)] := descCountT_succ_le htbl hW htL
    have h1t : (1 : V) ≤ termLen LAct v.[k - (j + 1)] := one_le_termLen htL
    -- the entry at `i + 1`
    have hib_t : (i + 1) + 2 * termLen LAct v.[k - (j + 1)] ≤ Bi := by
      calc (i + 1) + 2 * termLen LAct v.[k - (j + 1)]
          = i + 2 * termLen LAct v.[k - (j + 1)] + 1 := by ring
        _ ≤ i + 2 * (termLen LAct v.[k - (j + 1)] + listSum (termLenVec LAct j (takeLast v j))) + 1 :=
            add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left le_self_add zero_le)) le_rfl
        _ ≤ Bi := hib
    have hi1 : i + 1 ≤ Bi := le_trans le_self_add hib_t
    obtain ⟨Pt, hPt, hlPt, hft⟩ := ih (k - (j + 1)) hlt (i + 1) hi1 hib_t hDt
    -- the tail at `i + 1 + ct`
    have hib_v : (i + 1 + descCountT walkPieces n v.[k - (j + 1)]) + 2 * listSum (termLenVec LAct j (takeLast v j)) + 1 ≤ Bi := by
      calc (i + 1 + descCountT walkPieces n v.[k - (j + 1)]) + 2 * listSum (termLenVec LAct j (takeLast v j)) + 1
          = i + (descCountT walkPieces n v.[k - (j + 1)] + 1) + 2 * listSum (termLenVec LAct j (takeLast v j)) + 1 := by ring
        _ ≤ i + 2 * termLen LAct v.[k - (j + 1)] + 2 * listSum (termLenVec LAct j (takeLast v j)) + 1 :=
            add_le_add (add_le_add (add_le_add le_rfl hct2) le_rfl) le_rfl
        _ = i + 2 * (termLen LAct v.[k - (j + 1)] + listSum (termLenVec LAct j (takeLast v j))) + 1 := by ring
        _ ≤ Bi := hib
    have hiv : i + 1 + descCountT walkPieces n v.[k - (j + 1)] ≤ Bi := le_trans le_self_add (le_trans le_self_add hib_v)
    obtain ⟨Pv, hPv₀, hlPv, hfv₀⟩ := ihj hj' _ hiv hib_v hDtail
    have hsub : Γ ⊆ finalCtx Γ Pt := fun x hx ↦ hPt.mem hx
    have hPv : HInv tbl E (finalCtx Γ Pt) Pv := hPv₀.mono_ctx htbl (hPt.isFormulaSet htbl hΓ) hsub
    have hfv := finalCtx_mono (noDrop_of_hornOnly hPv₀.2.2.1) hsub hfv₀
    have hPtv := hPt.append hPv
    have hΓ₂ := hPtv.isFormulaSet htbl hΓ
    -- the values and their caps
    have hmtn : termBV ℒₒᵣ v.[k - (j + 1)] ≤ n := (IsSemiterm.def.mp ht).2
    have hmvn : listMax (termBVVec ℒₒᵣ j (takeLast v j)) ≤ n := listMax_termBVVec_takeLast_le hv j hj'
    have hEmt : termLen LAct (cTV (termBV ℒₒᵣ v.[k - (j + 1)])) ≤ E := cTV_cap (le_trans hmtn hnB) hE
    have hEmv : termLen LAct (cTV (listMax (termBVVec ℒₒᵣ j (takeLast v j)))) ≤ E := cTV_cap (le_trans hmvn hnB) hE
    have hjS : j ≤ listSum (termLenVec LAct j (takeLast v j)) := by
      have := len_le_listSum_of_one_le (termLenVec LAct j (takeLast v j)) (fun m hm ↦ by
        rw [len_termLenVec hwL] at hm
        rw [nth_termLenVec hwL hm]
        exact one_le_termLen (IsSemiterm.LAct_of_LOR (hw.nth hm)))
      rwa [len_termLenVec hwL] at this
    have hEj : termLen LAct (cTV j) ≤ E := by
      refine cTV_cap hjS ?_
      calc 2 * listSum (termLenVec LAct j (takeLast v j)) + 1
          ≤ i + 2 * (termLen LAct v.[k - (j + 1)] + listSum (termLenVec LAct j (takeLast v j))) + 1 := by
            calc 2 * listSum (termLenVec LAct j (takeLast v j)) + 1
                ≤ 2 * listSum (termLenVec LAct j (takeLast v j)) + 1 + (i + 2 * termLen LAct v.[k - (j + 1)]) := le_self_add
              _ = i + 2 * (termLen LAct v.[k - (j + 1)] + listSum (termLenVec LAct j (takeLast v j))) + 1 := by ring
        _ ≤ Bi := hib
        _ ≤ E := le_trans le_self_add hEi
    have hEi1 : termLen LAct (^&(i + 1) : V) ≤ E := termLen_fvar_le (le_trans (add_le_add hi1 le_rfl) hEi)
    have hEi0 : termLen LAct (^&i : V) ≤ E := termLen_fvar_le (le_trans (add_le_add hi le_rfl) hEi)
    have hEr : termLen LAct (vRef (i + 1 + descCountT walkPieces n v.[k - (j + 1)]) j) ≤ E :=
      termLen_vRef_le (le_trans (add_le_add hiv le_rfl) hEi)
    -- the facts at the joint context
    have hft' : neg LAct (bsTFact (cTV n) (cTV (termBV ℒₒᵣ v.[k - (j + 1)])) (^&(i + 1))) ∈ finalCtx Γ (appendV Pt Pv) := by
      rw [finalCtx_appendV]; exact hPv.mem hft
    have hfv' : neg LAct (bsVFact (cTV n) (cTV (listMax (termBVVec ℒₒᵣ j (takeLast v j)))) (cTV j)
        (vRef (i + 1 + descCountT walkPieces n v.[k - (j + 1)]) j)) ∈ finalCtx Γ (appendV Pt Pv) := by
      rw [finalCtx_appendV]; exact hfv
    have hadj' : neg LAct (adjFact (^&i) (^&(i + 1)) (vRef (i + 1 + descCountT walkPieces n v.[k - (j + 1)]) j)) ∈
        finalCtx Γ (appendV Pt Pv) := hPtv.mem hadj
    have hlen2 : len (appendV Pt Pv) ≤
        4 * termLen LAct v.[k - (j + 1)] * termLen LAct v.[k - (j + 1)] * (B + 3) +
        (2 * listSum (termLenVec LAct j (takeLast v j)) + 1) * (2 * listSum (termLenVec LAct j (takeLast v j)) + 1) * (B + 3) := by
      rw [len_appendV]; exact add_le_add hlPt hlPv
    have hfinal : ∀ P₃ : V, HInv tbl E (finalCtx Γ (appendV Pt Pv)) P₃ → len P₃ ≤ B + 2 →
        ∀ s : V, StepOK tbl E ((8 : ℕ) : V) (finalCtx (finalCtx Γ (appendV Pt Pv)) P₃) s → sTag s = 0 →
        ∀ m : V, ctxAfter (finalCtx (finalCtx Γ (appendV Pt Pv)) P₃) s =
          insert (neg LAct (bsVFact (cTV n) (cTV m) (cTV j ^+ (𝟏 : V)) (^&i))) (finalCtx (finalCtx Γ (appendV Pt Pv)) P₃) →
        m = listMax (termBVVec ℒₒᵣ (j + 1) (takeLast v (j + 1))) →
        ∃ P : V, HInv tbl E Γ P ∧
          len P ≤ (2 * (termLen LAct v.[k - (j + 1)] + listSum (termLenVec LAct j (takeLast v j))) + 1) *
            (2 * (termLen LAct v.[k - (j + 1)] + listSum (termLenVec LAct j (takeLast v j))) + 1) * (B + 3) ∧
          neg LAct (bsVFact (cTV n) (cTV (listMax (termBVVec ℒₒᵣ (j + 1) (takeLast v (j + 1))))) (cTV (j + 1)) (vRef i (j + 1))) ∈
            finalCtx Γ P := by
      intro P₃ hP₃ hl₃ s hok htag m hctx hm
      have hok' : StepOK tbl E ((8 : ℕ) : V) (finalCtx Γ (appendV (appendV Pt Pv) P₃)) s := by
        rw [finalCtx_appendV]; exact hok
      refine ⟨_, (hPtv.append hP₃).snoc hok' htag, ?_, ?_⟩
      · rw [len_appendV, len_appendV, len_single]
        calc len (appendV Pt Pv) + len P₃ + 1 = len (appendV Pt Pv) + (len P₃ + 1) := by ring
          _ ≤ (4 * termLen LAct v.[k - (j + 1)] * termLen LAct v.[k - (j + 1)] * (B + 3) +
              (2 * listSum (termLenVec LAct j (takeLast v j)) + 1) * (2 * listSum (termLenVec LAct j (takeLast v j)) + 1) * (B + 3)) +
              (B + 3) := by
                refine add_le_add hlen2 ?_
                calc len P₃ + 1 ≤ B + 2 + 1 := add_le_add hl₃ le_rfl
                  _ = B + 3 := by ring
          _ ≤ (2 * termLen LAct v.[k - (j + 1)] + (2 * listSum (termLenVec LAct j (takeLast v j)) + 1)) *
              (2 * termLen LAct v.[k - (j + 1)] + (2 * listSum (termLenVec LAct j (takeLast v j)) + 1)) * (B + 3) :=
                sq_bound_adj h1t le_add_self
          _ = (2 * (termLen LAct v.[k - (j + 1)] + listSum (termLenVec LAct j (takeLast v j))) + 1) *
              (2 * (termLen LAct v.[k - (j + 1)] + listSum (termLenVec LAct j (takeLast v j))) + 1) * (B + 3) := by ring
      · rw [finalCtx_appendV_single, finalCtx_appendV, hctx, ← hm, ← cTV_succ, vRef_of_ne (ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_add_self))]
        exact mem_insert_self'
    have hmax : listMax (termBVVec ℒₒᵣ (j + 1) (takeLast v (j + 1))) =
        max (termBV ℒₒᵣ v.[k - (j + 1)]) (listMax (termBVVec ℒₒᵣ j (takeLast v j))) := by
      rw [htake, termBVVec_cons ht.isUTerm hw.isUTermVec, listMax_adjoin]
    rcases le_total (termBV ℒₒᵣ v.[k - (j + 1)]) (listMax (termBVVec ℒₒᵣ j (takeLast v j))) with hle | hle
    · obtain ⟨P₃, hP₃, hl₃, hf₃⟩ := leChain_ok' htbl hT hΓ₂ hle (le_trans (add_le_add (mul_le_mul_of_nonneg_left (le_trans hmvn hnB) zero_le) le_rfl) hE)
      have hΓ₃ := hP₃.isFormulaSet htbl hΓ₂
      obtain ⟨hlen, hrow⟩ := hT.bsVAdjL
      obtain ⟨hok, htag, hctx⟩ := iok_bsVAdjL htbl rfl hlen hrow hΓ₃ hwn hEn (cTV_semiterm_LAct 0 _) hEj
        (cTV_semiterm_LAct 0 _) hEmt (cTV_semiterm_LAct 0 _) hEmv (by simp) hEi1 (isSemiterm_vRef _ _) hEr (by simp) hEi0
        (hP₃.mem hft') (hP₃.mem hfv') (hP₃.mem hadj') hf₃
      exact hfinal P₃ hP₃ (le_trans hl₃ (add_le_add (le_trans hmvn hnB) (by norm_num))) _ hok htag _ hctx
        (by rw [hmax, max_eq_right hle])
    · obtain ⟨P₃, hP₃, hl₃, hf₃⟩ := leChain_ok' htbl hT hΓ₂ hle (le_trans (add_le_add (mul_le_mul_of_nonneg_left (le_trans hmtn hnB) zero_le) le_rfl) hE)
      have hΓ₃ := hP₃.isFormulaSet htbl hΓ₂
      obtain ⟨hlen, hrow⟩ := hT.bsVAdjR
      obtain ⟨hok, htag, hctx⟩ := iok_bsVAdjR htbl rfl hlen hrow hΓ₃ hwn hEn (cTV_semiterm_LAct 0 _) hEj
        (cTV_semiterm_LAct 0 _) hEmt (cTV_semiterm_LAct 0 _) hEmv (by simp) hEi1 (isSemiterm_vRef _ _) hEr (by simp) hEi0
        (hP₃.mem hft') (hP₃.mem hfv') (hP₃.mem hadj') hf₃
      exact hfinal P₃ hP₃ (le_trans hl₃ (add_le_add (le_trans hmtn hnB) (by norm_num))) _ hok htag _ hctx
        (by rw [hmax, max_eq_left hle])

/-- **The `bs` pass on terms**: from the dossier of an `ℒₒᵣ`-term `t` (bound `n ≤ B`) at `&i` (`i + 2|t| ≤ Bi`), a
shift-free Horn list of length `≤ 4|t|²(B + 3)` leaving `bsTFact (cTV n) (cTV (termBV t)) &i`. -/
theorem bsT_ok {tbl N E Γ B Bi n : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hnB : n ≤ B) (hE : 2 * B + 1 ≤ E) (hEi : Bi + 1 ≤ E) (hE8 : 8 ≤ E) :
    ∀ t, IsSemiterm ℒₒᵣ n t → BsTInv tbl E Γ B Bi n t := by
  have hW := hT.walkTable
  have hB3 : (1 : V) ≤ B + 3 := le_trans (by norm_num) le_add_self
  have hEn : termLen LAct (cTV n) ≤ E := cTV_cap hnB hE
  have hwn : IsSemiterm LAct 0 (cTV n) := cTV_semiterm_LAct 0 n
  refine IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_
  · definability
  · -- bound variables
    intro z hzn i hi hib hD
    obtain ⟨hbv, _⟩ := dossT_bvar htbl hW rfl hD
    have hEn1 : 2 * n + 1 ≤ E := le_trans (add_le_add (mul_le_mul_of_nonneg_left hnB zero_le) le_rfl) hE
    obtain ⟨hok₀, hnd₀, hsh₀, _, hlt₀⟩ := ltSteps_ok htbl hW rfl hzn hEn1 Γ hΓ
    have hP₀ : HInv tbl E Γ (ltSteps walkPieces n z) :=
      ⟨hok₀.mono (by exact_mod_cast (by decide : 8 ≤ 9)), hnd₀.noDrop', hornOnly_ltAux rfl n z z, hsh₀⟩
    have hΓ₁ := hP₀.isFormulaSet htbl hΓ
    obtain ⟨hlen, hrow⟩ := hT.bsBvar
    have hEi' : i + 1 ≤ E := le_trans (add_le_add hi le_rfl) hEi
    obtain ⟨hok, htag, hctx⟩ := iok_bsBvar htbl rfl hlen hrow hΓ₁ hwn hEn (cTV_semiterm_LAct 0 z)
      (cTV_cap (le_trans (le_of_lt hzn) hnB) hE) (by simp) (termLen_fvar_le hEi') hlt₀ (hP₀.mem hbv)
    refine ⟨_, hP₀.snoc hok htag, ?_, ?_⟩
    · rw [len_appendV, len_single, len_ltSteps, termLen_bvar]
      exact succ_le_sq (le_add_self : (1 : V) ≤ z + 1) hB3
    · rw [finalCtx_appendV_single, hctx, termBV_bvar, ← cTV_succ]
      exact mem_insert_self'
  · -- free variables
    intro x i hi hib hD
    obtain ⟨hfv, _⟩ := dossT_fvar htbl hW rfl hD
    obtain ⟨hlen, hrow⟩ := hT.bsFvar
    have hEi' : i + 1 ≤ E := le_trans (add_le_add hi le_rfl) hEi
    have hEx : termLen LAct (cTV x) ≤ E := by
      rw [termLen_cTV]
      rw [termLen_fvar] at hib
      calc 2 * x + 1 ≤ i + 2 * (x + 1) := by
            calc 2 * x + 1 ≤ 2 * x + 1 + (i + 1) := le_self_add
              _ = i + 2 * (x + 1) := by ring
        _ ≤ Bi := hib
        _ ≤ E := le_trans le_self_add hEi
    obtain ⟨hok, htag, hctx⟩ := iok_bsFvar htbl rfl hlen hrow hΓ hwn hEn (cTV_semiterm_LAct 0 x) hEx
      (by simp) (termLen_fvar_le hEi') hfv
    refine ⟨_, HInv.single hok htag, ?_, ?_⟩
    · rw [len_single, termLen_fvar]
      exact one_le_sq4 (le_add_self : (1 : V) ≤ x + 1) hB3
    · rw [finalCtx_single, hctx, termBV_fvar, cTV_zero]
      exact mem_insert_self'
  · -- function applications
    intro k f v hkf hv ih i hi hib hD
    have hvL : IsSemitermVec LAct k n v := IsSemitermVec.LAct_of_LOR hv
    have hkfL : LAct.IsFunc k f := isFunc_LAct_of_LOR hkf
    have hlv : len v = k := hv.lh
    have htk : takeLast v k = v := by conv_lhs => rw [← hlv]; exact takeLast_len_self v
    obtain ⟨hfunc, _, _, hDv⟩ := dossT_func htbl hW rfl hkfL hvL hD
    have hS : termLen LAct (^func k f v) = listSum (termLenVec LAct k v) + 1 := termLen_func hkfL hvL.isUTermVec
    rw [hS] at hib ⊢
    have hib_v : (i + 1) + 2 * listSum (termLenVec LAct k (takeLast v k)) + 1 ≤ Bi := by
      rw [htk]
      calc (i + 1) + 2 * listSum (termLenVec LAct k v) + 1 = i + 2 * (listSum (termLenVec LAct k v) + 1) := by ring
        _ ≤ Bi := hib
    have hi1 : i + 1 ≤ Bi := le_trans le_self_add (le_trans le_self_add hib_v)
    obtain ⟨Pv, hPv, hlPv, hfv⟩ := bsV_of_entries htbl hT hΓ hnB hE hEi hv ih k le_rfl (i + 1) hi1 hib_v hDv
    rw [htk] at hlPv hfv
    have hΓ₁ := hPv.isFormulaSet htbl hΓ
    obtain ⟨Pc, hPc, hlPc, hfc⟩ := isFuncOR_step (E := E) htbl hT hΓ₁ hkf
    have hPvc := hPv.append hPc
    have hΓ₂ := hPvc.isFormulaSet htbl hΓ
    -- caps
    have hkS : k ≤ listSum (termLenVec LAct k v) := by
      have := len_le_listSum_of_one_le (termLenVec LAct k v) (fun m hm ↦ by
        rw [len_termLenVec hvL.isUTermVec] at hm
        rw [nth_termLenVec hvL.isUTermVec hm]
        exact one_le_termLen (hvL.nth hm))
      rwa [len_termLenVec hvL.isUTermVec] at this
    have hEk : termLen LAct (cTV k) ≤ E := by
      refine cTV_cap hkS ?_
      calc 2 * listSum (termLenVec LAct k v) + 1 ≤ i + 2 * (listSum (termLenVec LAct k v) + 1) := by
            calc 2 * listSum (termLenVec LAct k v) + 1 ≤ 2 * listSum (termLenVec LAct k v) + 1 + (i + 1) := le_self_add
              _ = i + 2 * (listSum (termLenVec LAct k v) + 1) := by ring
        _ ≤ Bi := hib
        _ ≤ E := le_trans le_self_add hEi
    have hf1 : f ≤ 1 := by
      rcases isFunc_LOR_iff_V.mp hkf with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
    have hEf : termLen LAct (cTV f) ≤ E := cTV_cap hf1 (le_trans (by norm_num) hE8)
    have hm : listMax (termBVVec ℒₒᵣ k v) ≤ n := by
      have := listMax_termBVVec_takeLast_le hv k le_rfl; rwa [htk] at this
    have hEm : termLen LAct (cTV (listMax (termBVVec ℒₒᵣ k v))) ≤ E := cTV_cap (le_trans hm hnB) hE
    have hEr : termLen LAct (vRef (i + 1) k) ≤ E := termLen_vRef_le (le_trans (add_le_add hi1 le_rfl) hEi)
    have hEi0 : termLen LAct (^&i : V) ≤ E := termLen_fvar_le (le_trans (add_le_add hi le_rfl) hEi)
    obtain ⟨hlen, hrow⟩ := hT.bsFunc
    obtain ⟨hok, htag, hctx⟩ := iok_bsFunc htbl rfl hlen hrow hΓ₂ hwn hEn (cTV_semiterm_LAct 0 _) hEm
      (cTV_semiterm_LAct 0 k) hEk (cTV_semiterm_LAct 0 f) hEf (isSemiterm_vRef _ _) hEr (by simp) hEi0
      (by rw [finalCtx_appendV]; exact hfc) (by rw [finalCtx_appendV]; exact hPc.mem hfv) (hPvc.mem hfunc)
    refine ⟨_, hPvc.snoc hok htag, ?_, ?_⟩
    · rw [len_appendV, len_appendV, len_single]
      calc len Pv + len Pc + 1 ≤ (2 * listSum (termLenVec LAct k v) + 1) * (2 * listSum (termLenVec LAct k v) + 1) * (B + 3) + 1 + 1 :=
            add_le_add (add_le_add hlPv hlPc) le_rfl
        _ = (2 * listSum (termLenVec LAct k v) + 1) * (2 * listSum (termLenVec LAct k v) + 1) * (B + 3) + 2 := by ring
        _ ≤ 4 * (listSum (termLenVec LAct k v) + 1) * (listSum (termLenVec LAct k v) + 1) * (B + 3) := sq_bound_func hB3
    · rw [finalCtx_appendV_single, hctx, termBV_func hkf hv.isUTermVec]
      exact mem_insert_self'

end bsPass

end ArithS
