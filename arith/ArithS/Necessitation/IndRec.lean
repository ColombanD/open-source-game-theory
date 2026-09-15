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
* §4 `fvSeq` (`fvSeqFact (vRef i m) 𝟎 (cTV m)` along the walk of `fvarVec m`), `shift b = b` (`certShift` at the
  table, re-indexed), the `⟨#0 + 1⟩` iterate bounds.
* §5 the polynomial bookkeeping `gp Z k`, the lists WITH eigenvariables `WInv tbl E Γ P σ`; stage A (`stageA`): the
  five walks (`s = subst (fvarVec m) b`, `neg K`, `fvarVec m`, `⟨⌜0⌝⟩`, `⟨#0 + 1⟩`) and the three `certSubst`
  instances (the body at `fvarVec m`, and `neg K` at `𝟎` and at `#0 + 1`); stage B (`stageB`): the shift-free
  closing at stage A's context — the `qqAlls` walk, the `bs` pass on `b`, `shiftFact`, `fvSeqFact`, `negFact`, the
  identification of `K`'s two copies, `isC0Fact`/`isC1Fact`, then `bodyIntro`, `indBodyIntroL`, `indRecL`.
* §6 the producer `axmInd_ok` and the honest oracle `AxmIndOracle'` with `axmIndOracle_of`.

**What is delivered, and the honest variant (READ THIS).** The list `axmInd_ok` produces is NOT shift-free: the
recognizer needs the dossiers of `s`, `neg K` and three substitution vectors, which do not occur in the sequent's
layout, and `certSubst` itself introduces eigenvariables — so `shiftsV P = σ ≤ 100 Z³` and the fact is
`axchFact &(ip + σ)`, at `p`'s MOVED offset. `ProAxm.AxmIndOracle` (`NumInv`: `shiftsV P = 0`, standard `C : ℕ`)
and `Verify2`'s `AxmIndOracleC` are therefore NOT met by this construction, and for NONSTANDARD `p` no shift-free
list of standard length can meet them (the walks alone are `|p|` steps long). The consumer must be adjusted to
`AxmIndOracle'`: `shiftsV P ≤ C`, `len P ≤ C`, `SizeOK C C P`, fact at `&(memTop s p i + shiftsV P)`, with
`C = 4100 Z⁵`, `Z = i + 6D + 1 + D(D + 1)`, under `E ≥ 200 Z³` — every bound a polynomial in the sequent bound `D`
and the base offset `i` (degree 10 in `D`), `V`-valued. `vAxm_ok`'s node then reads the fact at the moved
offset exactly as `vAll_ok`/`vExs_ok` already do for their eigenvariable prologues.
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

/-! ### 3.5 Formulas -/

/-- The row step closing a binary node, abstracted over `⋏`/`⋎` and the two `≤` directions: from the two sub-passes
(`q` at `&(i+1)`, `p` at `&(i+cq+1)`), the shape fact and a chain, ONE step. -/
lemma bsBin_close {tbl N E Γ B Bi n i cq mp mq mr : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hnB : n ≤ B) (hE : 2 * B + 1 ≤ E) (hEi : Bi + 1 ≤ E) (hi : i ≤ Bi) (hcq : i + cq + 1 ≤ Bi)
    (hmp : mp ≤ n) (hmq : mq ≤ n) {Pq Pp : V} (hPq : HInv tbl E Γ Pq) (hPp : HInv tbl E Γ Pp)
    (hfq : neg LAct (bsFFact (cTV n) (cTV mq) (^&(i + 1))) ∈ finalCtx Γ Pq)
    (hfp : neg LAct (bsFFact (cTV n) (cTV mp) (^&(i + cq + 1))) ∈ finalCtx Γ Pp)
    (shape : V) (hshape : neg LAct shape ∈ Γ)
    (hstep : ∀ Γ' : V, IsFormulaSet LAct Γ' → neg LAct (bsFFact (cTV n) (cTV mp) (^&(i + cq + 1))) ∈ Γ' →
      neg LAct (bsFFact (cTV n) (cTV mq) (^&(i + 1))) ∈ Γ' → neg LAct shape ∈ Γ' →
      ((mp ≤ mq ∧ neg LAct (leFact (cTV mp) (cTV mq)) ∈ Γ') ∨ (mq ≤ mp ∧ neg LAct (leFact (cTV mq) (cTV mp)) ∈ Γ')) →
      ∃ s : V, StepOK tbl E ((8 : ℕ) : V) Γ' s ∧ sTag s = 0 ∧
        ctxAfter Γ' s = insert (neg LAct (bsFFact (cTV n) (cTV mr) (^&i))) Γ')
    (hmr : mr = max mp mq) :
    ∃ P : V, HInv tbl E Γ P ∧ len P ≤ len Pq + len Pp + (B + 3) ∧
      neg LAct (bsFFact (cTV n) (cTV mr) (^&i)) ∈ finalCtx Γ P := by
  have hsub : Γ ⊆ finalCtx Γ Pq := fun x hx ↦ hPq.mem hx
  have hPp' : HInv tbl E (finalCtx Γ Pq) Pp := hPp.mono_ctx htbl (hPq.isFormulaSet htbl hΓ) hsub
  have hfp' := hPp.finalCtx_mono hsub hfp
  have hPqp := hPq.append hPp'
  have hΓ₂ := hPqp.isFormulaSet htbl hΓ
  have hfq' : neg LAct (bsFFact (cTV n) (cTV mq) (^&(i + 1))) ∈ finalCtx Γ (appendV Pq Pp) := by
    rw [finalCtx_appendV]; exact hPp'.mem hfq
  have hfp'' : neg LAct (bsFFact (cTV n) (cTV mp) (^&(i + cq + 1))) ∈ finalCtx Γ (appendV Pq Pp) := by
    rw [finalCtx_appendV]; exact hfp'
  have hsh' : neg LAct shape ∈ finalCtx Γ (appendV Pq Pp) := hPqp.mem hshape
  have hfin : ∀ P₃ : V, HInv tbl E (finalCtx Γ (appendV Pq Pp)) P₃ → len P₃ ≤ B + 2 →
      ((mp ≤ mq ∧ neg LAct (leFact (cTV mp) (cTV mq)) ∈ finalCtx (finalCtx Γ (appendV Pq Pp)) P₃) ∨
       (mq ≤ mp ∧ neg LAct (leFact (cTV mq) (cTV mp)) ∈ finalCtx (finalCtx Γ (appendV Pq Pp)) P₃)) →
      ∃ P : V, HInv tbl E Γ P ∧ len P ≤ len Pq + len Pp + (B + 3) ∧
        neg LAct (bsFFact (cTV n) (cTV mr) (^&i)) ∈ finalCtx Γ P := by
    intro P₃ hP₃ hl₃ hle
    have hΓ₃ := hP₃.isFormulaSet htbl hΓ₂
    obtain ⟨s, hok, htag, hctx⟩ := hstep _ hΓ₃ (hP₃.mem hfp'') (hP₃.mem hfq') (hP₃.mem hsh') hle
    have hok' : StepOK tbl E ((8 : ℕ) : V) (finalCtx Γ (appendV (appendV Pq Pp) P₃)) s := by
      rw [finalCtx_appendV]; exact hok
    refine ⟨_, (hPqp.append hP₃).snoc hok' htag, ?_, ?_⟩
    · rw [len_appendV, len_appendV, len_appendV, len_single]
      calc len Pq + len Pp + len P₃ + 1 = len Pq + len Pp + (len P₃ + 1) := by ring
        _ ≤ len Pq + len Pp + (B + 2 + 1) := add_le_add le_rfl (add_le_add hl₃ le_rfl)
        _ = len Pq + len Pp + (B + 3) := by ring
    · rw [finalCtx_appendV_single, finalCtx_appendV, hctx]
      exact mem_insert_self'
  rcases le_total mp mq with hle | hle
  · obtain ⟨P₃, hP₃, hl₃, hf₃⟩ := leChain_ok' htbl hT hΓ₂ hle
      (le_trans (add_le_add (mul_le_mul_of_nonneg_left (le_trans hmq hnB) zero_le) le_rfl) hE)
    exact hfin P₃ hP₃ (le_trans hl₃ (add_le_add (le_trans hmq hnB) (by norm_num))) (Or.inl ⟨hle, hf₃⟩)
  · obtain ⟨P₃, hP₃, hl₃, hf₃⟩ := leChain_ok' htbl hT hΓ₂ hle
      (le_trans (add_le_add (mul_le_mul_of_nonneg_left (le_trans hmp hnB) zero_le) le_rfl) hE)
    exact hfin P₃ hP₃ (le_trans hl₃ (add_le_add (le_trans hmp hnB) (by norm_num))) (Or.inr ⟨hle, hf₃⟩)

/-- **The `bs` pass on formulas**: from the dossier of an `ℒₒᵣ`-formula `r` (bound `n`, `n + |r| ≤ B`) at `&i`
(`i + 2|r| ≤ Bi`), a shift-free Horn list of length `≤ 4|r|²(B + 3)` leaving `bsFFact (cTV n) (cTV (bv r)) &i`:
`ℒₒᵣ`-formation and the EXACT bound-variable count, established bottom-up. -/
theorem bsF_ok {tbl N E Γ B Bi : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hE : 2 * B + 1 ≤ E) (hEi : Bi + 1 ≤ E) (hE8 : 8 ≤ E) {n r : V} (hr : IsSemiformula ℒₒᵣ n r) :
    ∀ i ≤ Bi, i + 2 * formulaLen LAct r ≤ Bi → n + formulaLen LAct r ≤ B → DossF walkPieces Γ n r i →
      ∃ P : V, HInv tbl E Γ P ∧ len P ≤ 4 * formulaLen LAct r * formulaLen LAct r * (B + 3) ∧
        neg LAct (bsFFact (cTV n) (cTV (Bootstrapping.bv ℒₒᵣ r)) (^&i)) ∈ finalCtx Γ P := by
  have hW := hT.walkTable
  have hB3 : (1 : V) ≤ B + 3 := le_trans (by norm_num) le_add_self
  revert n r
  refine IsSemiformula.sigma1_structural_induction (L := ℒₒᵣ)
    (P := fun n r ↦ ∀ i ≤ Bi, i + 2 * formulaLen LAct r ≤ Bi → n + formulaLen LAct r ≤ B → DossF walkPieces Γ n r i →
      ∃ P : V, HInv tbl E Γ P ∧ len P ≤ 4 * formulaLen LAct r * formulaLen LAct r * (B + 3) ∧
        neg LAct (bsFFact (cTV n) (cTV (Bootstrapping.bv ℒₒᵣ r)) (^&i)) ∈ finalCtx Γ P)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · definability
  · -- rel
    intro n k R v hkR hv i hi hib hnB' hD
    have hnB : n ≤ B := le_trans le_self_add hnB'
    have hwn : IsSemiterm LAct 0 (cTV n) := cTV_semiterm_LAct 0 n
    have hEn : termLen LAct (cTV n) ≤ E := cTV_cap hnB hE
    have hvL : IsSemitermVec LAct k n v := IsSemitermVec.LAct_of_LOR hv
    have hkRL : LAct.IsRel k R := isRel_LAct_of_LOR hkR
    have hlv : len v = k := hv.lh
    have htk : takeLast v k = v := by conv_lhs => rw [← hlv]; exact takeLast_len_self v
    obtain ⟨hrel, _, _, hDv⟩ := dossF_rel htbl hW rfl hkRL hvL hD
    have hS : formulaLen LAct (^rel k R v) = listSum (termLenVec LAct k v) + 1 := formulaLen_rel hkRL hvL.isUTermVec
    rw [hS] at hib ⊢
    have hib_v : (i + 1) + 2 * listSum (termLenVec LAct k (takeLast v k)) + 1 ≤ Bi := by
      rw [htk]
      calc (i + 1) + 2 * listSum (termLenVec LAct k v) + 1 = i + 2 * (listSum (termLenVec LAct k v) + 1) := by ring
        _ ≤ Bi := hib
    have hi1 : i + 1 ≤ Bi := le_trans le_self_add (le_trans le_self_add hib_v)
    obtain ⟨Pv, hPv, hlPv, hfv⟩ := bsV_of_entries htbl hT hΓ hnB hE hEi hv
      (fun a ha ↦ bsT_ok htbl hT hΓ hnB hE hEi hE8 _ (hv.nth ha)) k le_rfl (i + 1) hi1 hib_v hDv
    rw [htk] at hlPv hfv
    have hΓ₁ := hPv.isFormulaSet htbl hΓ
    obtain ⟨Pc, hPc, hlPc, hfc⟩ := isRelOR_step (E := E) htbl hT hΓ₁ hkR
    have hPvc := hPv.append hPc
    have hΓ₂ := hPvc.isFormulaSet htbl hΓ
    have hk2 : k ≤ 2 := by rcases isRel_LOR_iff_V.mp hkR with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact le_rfl
    have hR1 : R ≤ 1 := by rcases isRel_LOR_iff_V.mp hkR with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
    have hEk : termLen LAct (cTV k) ≤ E := cTV_cap hk2 (le_trans (by norm_num) hE8)
    have hER : termLen LAct (cTV R) ≤ E := cTV_cap hR1 (le_trans (by norm_num) hE8)
    have hm : listMax (termBVVec ℒₒᵣ k v) ≤ n := by
      have := listMax_termBVVec_takeLast_le hv k le_rfl; rwa [htk] at this
    have hEm : termLen LAct (cTV (listMax (termBVVec ℒₒᵣ k v))) ≤ E := cTV_cap (le_trans hm hnB) hE
    have hEr : termLen LAct (vRef (i + 1) k) ≤ E := termLen_vRef_le (le_trans (add_le_add hi1 le_rfl) hEi)
    have hEi0 : termLen LAct (^&i : V) ≤ E := termLen_fvar_le (le_trans (add_le_add hi le_rfl) hEi)
    obtain ⟨hlen, hrow⟩ := hT.bsRel
    obtain ⟨hok, htag, hctx⟩ := iok_bsRel htbl rfl hlen hrow hΓ₂ hwn hEn (cTV_semiterm_LAct 0 _) hEm
      (cTV_semiterm_LAct 0 k) hEk (cTV_semiterm_LAct 0 R) hER (isSemiterm_vRef _ _) hEr (by simp) hEi0
      (by rw [finalCtx_appendV]; exact hfc) (by rw [finalCtx_appendV]; exact hPc.mem hfv) (hPvc.mem hrel)
    refine ⟨_, hPvc.snoc hok htag, ?_, ?_⟩
    · rw [len_appendV, len_appendV, len_single]
      calc len Pv + len Pc + 1 ≤ (2 * listSum (termLenVec LAct k v) + 1) * (2 * listSum (termLenVec LAct k v) + 1) * (B + 3) + 1 + 1 :=
            add_le_add (add_le_add hlPv hlPc) le_rfl
        _ = (2 * listSum (termLenVec LAct k v) + 1) * (2 * listSum (termLenVec LAct k v) + 1) * (B + 3) + 2 := by ring
        _ ≤ 4 * (listSum (termLenVec LAct k v) + 1) * (listSum (termLenVec LAct k v) + 1) * (B + 3) := sq_bound_func hB3
    · rw [finalCtx_appendV_single, hctx, bv_rel hkR hv.isUTermVec]
      exact mem_insert_self'
  · -- nrel
    intro n k R v hkR hv i hi hib hnB' hD
    have hnB : n ≤ B := le_trans le_self_add hnB'
    have hwn : IsSemiterm LAct 0 (cTV n) := cTV_semiterm_LAct 0 n
    have hEn : termLen LAct (cTV n) ≤ E := cTV_cap hnB hE
    have hvL : IsSemitermVec LAct k n v := IsSemitermVec.LAct_of_LOR hv
    have hkRL : LAct.IsRel k R := isRel_LAct_of_LOR hkR
    have hlv : len v = k := hv.lh
    have htk : takeLast v k = v := by conv_lhs => rw [← hlv]; exact takeLast_len_self v
    obtain ⟨hrel, _, _, hDv⟩ := dossF_nrel htbl hW rfl hkRL hvL hD
    have hS : formulaLen LAct (^nrel k R v) = listSum (termLenVec LAct k v) + 1 := formulaLen_nrel hkRL hvL.isUTermVec
    rw [hS] at hib ⊢
    have hib_v : (i + 1) + 2 * listSum (termLenVec LAct k (takeLast v k)) + 1 ≤ Bi := by
      rw [htk]
      calc (i + 1) + 2 * listSum (termLenVec LAct k v) + 1 = i + 2 * (listSum (termLenVec LAct k v) + 1) := by ring
        _ ≤ Bi := hib
    have hi1 : i + 1 ≤ Bi := le_trans le_self_add (le_trans le_self_add hib_v)
    obtain ⟨Pv, hPv, hlPv, hfv⟩ := bsV_of_entries htbl hT hΓ hnB hE hEi hv
      (fun a ha ↦ bsT_ok htbl hT hΓ hnB hE hEi hE8 _ (hv.nth ha)) k le_rfl (i + 1) hi1 hib_v hDv
    rw [htk] at hlPv hfv
    have hΓ₁ := hPv.isFormulaSet htbl hΓ
    obtain ⟨Pc, hPc, hlPc, hfc⟩ := isRelOR_step (E := E) htbl hT hΓ₁ hkR
    have hPvc := hPv.append hPc
    have hΓ₂ := hPvc.isFormulaSet htbl hΓ
    have hk2 : k ≤ 2 := by rcases isRel_LOR_iff_V.mp hkR with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact le_rfl
    have hR1 : R ≤ 1 := by rcases isRel_LOR_iff_V.mp hkR with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
    have hEk : termLen LAct (cTV k) ≤ E := cTV_cap hk2 (le_trans (by norm_num) hE8)
    have hER : termLen LAct (cTV R) ≤ E := cTV_cap hR1 (le_trans (by norm_num) hE8)
    have hm : listMax (termBVVec ℒₒᵣ k v) ≤ n := by
      have := listMax_termBVVec_takeLast_le hv k le_rfl; rwa [htk] at this
    have hEm : termLen LAct (cTV (listMax (termBVVec ℒₒᵣ k v))) ≤ E := cTV_cap (le_trans hm hnB) hE
    have hEr : termLen LAct (vRef (i + 1) k) ≤ E := termLen_vRef_le (le_trans (add_le_add hi1 le_rfl) hEi)
    have hEi0 : termLen LAct (^&i : V) ≤ E := termLen_fvar_le (le_trans (add_le_add hi le_rfl) hEi)
    obtain ⟨hlen, hrow⟩ := hT.bsNRel
    obtain ⟨hok, htag, hctx⟩ := iok_bsNRel htbl rfl hlen hrow hΓ₂ hwn hEn (cTV_semiterm_LAct 0 _) hEm
      (cTV_semiterm_LAct 0 k) hEk (cTV_semiterm_LAct 0 R) hER (isSemiterm_vRef _ _) hEr (by simp) hEi0
      (by rw [finalCtx_appendV]; exact hfc) (by rw [finalCtx_appendV]; exact hPc.mem hfv) (hPvc.mem hrel)
    refine ⟨_, hPvc.snoc hok htag, ?_, ?_⟩
    · rw [len_appendV, len_appendV, len_single]
      calc len Pv + len Pc + 1 ≤ (2 * listSum (termLenVec LAct k v) + 1) * (2 * listSum (termLenVec LAct k v) + 1) * (B + 3) + 1 + 1 :=
            add_le_add (add_le_add hlPv hlPc) le_rfl
        _ = (2 * listSum (termLenVec LAct k v) + 1) * (2 * listSum (termLenVec LAct k v) + 1) * (B + 3) + 2 := by ring
        _ ≤ 4 * (listSum (termLenVec LAct k v) + 1) * (listSum (termLenVec LAct k v) + 1) * (B + 3) := sq_bound_func hB3
    · rw [finalCtx_appendV_single, hctx, bv_nrel hkR hv.isUTermVec]
      exact mem_insert_self'
  · -- verum
    intro n i hi hib hnB' hD
    have hnB : n ≤ B := le_trans le_self_add hnB'
    obtain ⟨hv, _⟩ := dossF_verum htbl hW rfl hD
    obtain ⟨hlen, hrow⟩ := hT.bsVerum
    obtain ⟨hok, htag, hctx⟩ := iok_bsVerum htbl rfl hlen hrow hΓ (cTV_semiterm_LAct 0 n) (cTV_cap hnB hE)
      (by simp) (termLen_fvar_le (le_trans (add_le_add hi le_rfl) hEi)) hv
    refine ⟨_, HInv.single hok htag, ?_, ?_⟩
    · rw [len_single, formulaLen_verum]; exact one_le_sq4 le_rfl hB3
    · rw [finalCtx_single, hctx, bv_verum, cTV_zero]; exact mem_insert_self'
  · -- falsum
    intro n i hi hib hnB' hD
    have hnB : n ≤ B := le_trans le_self_add hnB'
    obtain ⟨hv, _⟩ := dossF_falsum htbl hW rfl hD
    obtain ⟨hlen, hrow⟩ := hT.bsFalsum
    obtain ⟨hok, htag, hctx⟩ := iok_bsFalsum htbl rfl hlen hrow hΓ (cTV_semiterm_LAct 0 n) (cTV_cap hnB hE)
      (by simp) (termLen_fvar_le (le_trans (add_le_add hi le_rfl) hEi)) hv
    refine ⟨_, HInv.single hok htag, ?_, ?_⟩
    · rw [len_single, formulaLen_falsum]; exact one_le_sq4 le_rfl hB3
    · rw [finalCtx_single, hctx, bv_falsum, cTV_zero]; exact mem_insert_self'
  · -- and
    intro n p q hp hq ihp ihq i hi hib hnB' hD
    have hnB : n ≤ B := le_trans le_self_add hnB'
    have hpL := IsSemiformula.LAct_of_LOR hp
    have hqL := IsSemiformula.LAct_of_LOR hq
    obtain ⟨hand, _, hDq, hDp⟩ := dossF_and htbl hW rfl hpL hqL hD
    have hlen : formulaLen LAct (p ^⋏ q) = formulaLen LAct p + formulaLen LAct q + 1 := formulaLen_and hpL.isUFormula hqL.isUFormula
    rw [hlen] at hib hnB' ⊢
    have hcq := descCountF_succ_le' htbl hW hqL
    have hib_q : (i + 1) + 2 * formulaLen LAct q ≤ Bi := by
      calc (i + 1) + 2 * formulaLen LAct q ≤ (i + 1) + 2 * formulaLen LAct q + 2 * formulaLen LAct p + 1 := le_trans le_self_add le_self_add
        _ = i + 2 * (formulaLen LAct p + formulaLen LAct q + 1) := by ring
        _ ≤ Bi := hib
    have hi1 : i + 1 ≤ Bi := le_trans le_self_add hib_q
    have hib_p : (i + descCountF walkPieces n q + 1) + 2 * formulaLen LAct p ≤ Bi := by
      calc (i + descCountF walkPieces n q + 1) + 2 * formulaLen LAct p
          = i + (descCountF walkPieces n q + 1) + 2 * formulaLen LAct p := by ring
        _ ≤ i + 2 * formulaLen LAct q + 2 * formulaLen LAct p := add_le_add (add_le_add le_rfl hcq) le_rfl
        _ ≤ i + 2 * formulaLen LAct q + 2 * formulaLen LAct p + 2 := le_self_add
        _ = i + 2 * (formulaLen LAct p + formulaLen LAct q + 1) := by ring
        _ ≤ Bi := hib
    have hicq : i + descCountF walkPieces n q + 1 ≤ Bi := le_trans le_self_add hib_p
    obtain ⟨Pq, hPq, hlq, hfq⟩ := ihq (i + 1) hi1 hib_q (le_trans (add_le_add le_rfl (le_trans le_add_self le_self_add)) hnB') hDq
    obtain ⟨Pp, hPp, hlp, hfp⟩ := ihp _ hicq hib_p (le_trans (add_le_add le_rfl (le_trans le_self_add le_self_add)) hnB') hDp
    have hwn : IsSemiterm LAct 0 (cTV n) := cTV_semiterm_LAct 0 n
    have hEn : termLen LAct (cTV n) ≤ E := cTV_cap hnB hE
    obtain ⟨P, hP, hl, hf⟩ := bsBin_close htbl hT hΓ hnB hE hEi hi hicq hp.bv_le hq.bv_le hPq hPp hfq hfp _ hand
      (fun Γ' hΓ' hfp' hfq' hsh' hle ↦ by
        have hEmp : termLen LAct (cTV (Bootstrapping.bv ℒₒᵣ p)) ≤ E := cTV_cap (le_trans hp.bv_le hnB) hE
        have hEmq : termLen LAct (cTV (Bootstrapping.bv ℒₒᵣ q)) ≤ E := cTV_cap (le_trans hq.bv_le hnB) hE
        have hEp : termLen LAct (^&(i + descCountF walkPieces n q + 1) : V) ≤ E := termLen_fvar_le (le_trans (add_le_add hicq le_rfl) hEi)
        have hEq : termLen LAct (^&(i + 1) : V) ≤ E := termLen_fvar_le (le_trans (add_le_add hi1 le_rfl) hEi)
        have hEi0 : termLen LAct (^&i : V) ≤ E := termLen_fvar_le (le_trans (add_le_add hi le_rfl) hEi)
        rcases hle with ⟨hle, hf⟩ | ⟨hle, hf⟩
        · obtain ⟨hlen, hrow⟩ := hT.bsAndL
          obtain ⟨hok, htag, hctx⟩ := iok_bsAndL htbl rfl hlen hrow hΓ' hwn hEn (cTV_semiterm_LAct 0 _) hEmp
            (cTV_semiterm_LAct 0 _) hEmq (by simp) hEp (by simp) hEq (by simp) hEi0 hfp' hfq' hsh' hf
          exact ⟨_, hok, htag, by rw [hctx, max_eq_right hle]⟩
        · obtain ⟨hlen, hrow⟩ := hT.bsAndR
          obtain ⟨hok, htag, hctx⟩ := iok_bsAndR htbl rfl hlen hrow hΓ' hwn hEn (cTV_semiterm_LAct 0 _) hEmp
            (cTV_semiterm_LAct 0 _) hEmq (by simp) hEp (by simp) hEq (by simp) hEi0 hfp' hfq' hsh' hf
          exact ⟨_, hok, htag, by rw [hctx, max_eq_left hle]⟩) rfl
    refine ⟨P, hP, ?_, ?_⟩
    · calc len P ≤ len Pq + len Pp + (B + 3) := hl
        _ ≤ 4 * formulaLen LAct q * formulaLen LAct q * (B + 3) + 4 * formulaLen LAct p * formulaLen LAct p * (B + 3) + (B + 3) :=
            add_le_add (add_le_add hlq hlp) le_rfl
        _ ≤ 4 * (formulaLen LAct q + formulaLen LAct p + 1) * (formulaLen LAct q + formulaLen LAct p + 1) * (B + 3) := sq_bound_bin
        _ = 4 * (formulaLen LAct p + formulaLen LAct q + 1) * (formulaLen LAct p + formulaLen LAct q + 1) * (B + 3) := by ring
    · rw [bv_and hp.isUFormula hq.isUFormula]; exact hf
  · -- or
    intro n p q hp hq ihp ihq i hi hib hnB' hD
    have hnB : n ≤ B := le_trans le_self_add hnB'
    have hpL := IsSemiformula.LAct_of_LOR hp
    have hqL := IsSemiformula.LAct_of_LOR hq
    obtain ⟨hor, _, hDq, hDp⟩ := dossF_or htbl hW rfl hpL hqL hD
    have hlen : formulaLen LAct (p ^⋎ q) = formulaLen LAct p + formulaLen LAct q + 1 := formulaLen_or hpL.isUFormula hqL.isUFormula
    rw [hlen] at hib hnB' ⊢
    have hcq := descCountF_succ_le' htbl hW hqL
    have hib_q : (i + 1) + 2 * formulaLen LAct q ≤ Bi := by
      calc (i + 1) + 2 * formulaLen LAct q ≤ (i + 1) + 2 * formulaLen LAct q + 2 * formulaLen LAct p + 1 := le_trans le_self_add le_self_add
        _ = i + 2 * (formulaLen LAct p + formulaLen LAct q + 1) := by ring
        _ ≤ Bi := hib
    have hi1 : i + 1 ≤ Bi := le_trans le_self_add hib_q
    have hib_p : (i + descCountF walkPieces n q + 1) + 2 * formulaLen LAct p ≤ Bi := by
      calc (i + descCountF walkPieces n q + 1) + 2 * formulaLen LAct p
          = i + (descCountF walkPieces n q + 1) + 2 * formulaLen LAct p := by ring
        _ ≤ i + 2 * formulaLen LAct q + 2 * formulaLen LAct p := add_le_add (add_le_add le_rfl hcq) le_rfl
        _ ≤ i + 2 * formulaLen LAct q + 2 * formulaLen LAct p + 2 := le_self_add
        _ = i + 2 * (formulaLen LAct p + formulaLen LAct q + 1) := by ring
        _ ≤ Bi := hib
    have hicq : i + descCountF walkPieces n q + 1 ≤ Bi := le_trans le_self_add hib_p
    obtain ⟨Pq, hPq, hlq, hfq⟩ := ihq (i + 1) hi1 hib_q (le_trans (add_le_add le_rfl (le_trans le_add_self le_self_add)) hnB') hDq
    obtain ⟨Pp, hPp, hlp, hfp⟩ := ihp _ hicq hib_p (le_trans (add_le_add le_rfl (le_trans le_self_add le_self_add)) hnB') hDp
    have hwn : IsSemiterm LAct 0 (cTV n) := cTV_semiterm_LAct 0 n
    have hEn : termLen LAct (cTV n) ≤ E := cTV_cap hnB hE
    obtain ⟨P, hP, hl, hf⟩ := bsBin_close htbl hT hΓ hnB hE hEi hi hicq hp.bv_le hq.bv_le hPq hPp hfq hfp _ hor
      (fun Γ' hΓ' hfp' hfq' hsh' hle ↦ by
        have hEmp : termLen LAct (cTV (Bootstrapping.bv ℒₒᵣ p)) ≤ E := cTV_cap (le_trans hp.bv_le hnB) hE
        have hEmq : termLen LAct (cTV (Bootstrapping.bv ℒₒᵣ q)) ≤ E := cTV_cap (le_trans hq.bv_le hnB) hE
        have hEp : termLen LAct (^&(i + descCountF walkPieces n q + 1) : V) ≤ E := termLen_fvar_le (le_trans (add_le_add hicq le_rfl) hEi)
        have hEq : termLen LAct (^&(i + 1) : V) ≤ E := termLen_fvar_le (le_trans (add_le_add hi1 le_rfl) hEi)
        have hEi0 : termLen LAct (^&i : V) ≤ E := termLen_fvar_le (le_trans (add_le_add hi le_rfl) hEi)
        rcases hle with ⟨hle, hf⟩ | ⟨hle, hf⟩
        · obtain ⟨hlen, hrow⟩ := hT.bsOrL
          obtain ⟨hok, htag, hctx⟩ := iok_bsOrL htbl rfl hlen hrow hΓ' hwn hEn (cTV_semiterm_LAct 0 _) hEmp
            (cTV_semiterm_LAct 0 _) hEmq (by simp) hEp (by simp) hEq (by simp) hEi0 hfp' hfq' hsh' hf
          exact ⟨_, hok, htag, by rw [hctx, max_eq_right hle]⟩
        · obtain ⟨hlen, hrow⟩ := hT.bsOrR
          obtain ⟨hok, htag, hctx⟩ := iok_bsOrR htbl rfl hlen hrow hΓ' hwn hEn (cTV_semiterm_LAct 0 _) hEmp
            (cTV_semiterm_LAct 0 _) hEmq (by simp) hEp (by simp) hEq (by simp) hEi0 hfp' hfq' hsh' hf
          exact ⟨_, hok, htag, by rw [hctx, max_eq_left hle]⟩) rfl
    refine ⟨P, hP, ?_, ?_⟩
    · calc len P ≤ len Pq + len Pp + (B + 3) := hl
        _ ≤ 4 * formulaLen LAct q * formulaLen LAct q * (B + 3) + 4 * formulaLen LAct p * formulaLen LAct p * (B + 3) + (B + 3) :=
            add_le_add (add_le_add hlq hlp) le_rfl
        _ ≤ 4 * (formulaLen LAct q + formulaLen LAct p + 1) * (formulaLen LAct q + formulaLen LAct p + 1) * (B + 3) := sq_bound_bin
        _ = 4 * (formulaLen LAct p + formulaLen LAct q + 1) * (formulaLen LAct p + formulaLen LAct q + 1) * (B + 3) := by ring
    · rw [bv_or hp.isUFormula hq.isUFormula]; exact hf
  · -- all
    intro n p hp ih i hi hib hnB' hD
    have hnB : n ≤ B := le_trans le_self_add hnB'
    have hpL := IsSemiformula.LAct_of_LOR hp
    obtain ⟨hall, _, hDp⟩ := dossF_all htbl hW rfl hpL hD
    have hlen : formulaLen LAct (^∀ p) = formulaLen LAct p + 1 := formulaLen_all hpL.isUFormula
    rw [hlen] at hib hnB' ⊢
    have hib_p : (i + 1) + 2 * formulaLen LAct p ≤ Bi := by
      calc (i + 1) + 2 * formulaLen LAct p ≤ (i + 1) + 2 * formulaLen LAct p + 1 := le_self_add
        _ = i + 2 * (formulaLen LAct p + 1) := by ring
        _ ≤ Bi := hib
    have hi1 : i + 1 ≤ Bi := le_trans le_self_add hib_p
    obtain ⟨Pp, hPp, hlp, hfp⟩ := ih (i + 1) hi1 hib_p (by rw [add_right_comm, add_assoc]; exact hnB') hDp
    have hΓ₁ := hPp.isFormulaSet htbl hΓ
    have hwn : IsSemiterm LAct 0 (cTV n) := cTV_semiterm_LAct 0 n
    have hEn : termLen LAct (cTV n) ≤ E := cTV_cap hnB hE
    have hEp : termLen LAct (^&(i + 1) : V) ≤ E := termLen_fvar_le (le_trans (add_le_add hi1 le_rfl) hEi)
    have hEi0 : termLen LAct (^&i : V) ≤ E := termLen_fvar_le (le_trans (add_le_add hi le_rfl) hEi)
    rw [cTV_succ] at hfp
    have hall' := hPp.mem hall
    rcases zero_or_succ (Bootstrapping.bv ℒₒᵣ p) with h0 | ⟨mp, hmp⟩
    · rw [h0, cTV_zero] at hfp
      obtain ⟨hlen, hrow⟩ := hT.bsAllZ
      obtain ⟨hok, htag, hctx⟩ := iok_bsAllZ htbl rfl hlen hrow hΓ₁ hwn hEn (by simp) hEp (by simp) hEi0 hfp hall'
      refine ⟨_, hPp.snoc hok htag, ?_, ?_⟩
      · rw [len_appendV, len_single]; exact le_trans (add_le_add hlp le_rfl) (sq_bound_un hB3)
      · rw [finalCtx_appendV_single, hctx, bv_all hp.isUFormula, h0, sub_spec_of_le zero_le, cTV_zero]
        exact mem_insert_self'
    · rw [hmp, cTV_succ] at hfp
      have hmpn : mp ≤ n := by
        have := hp.bv_le; rw [hmp] at this; exact le_of_add_le_add_right this
      obtain ⟨hlen, hrow⟩ := hT.bsAllS
      obtain ⟨hok, htag, hctx⟩ := iok_bsAllS htbl rfl hlen hrow hΓ₁ hwn hEn (cTV_semiterm_LAct 0 mp)
        (cTV_cap (le_trans hmpn hnB) hE) (by simp) hEp (by simp) hEi0 hfp hall'
      refine ⟨_, hPp.snoc hok htag, ?_, ?_⟩
      · rw [len_appendV, len_single]; exact le_trans (add_le_add hlp le_rfl) (sq_bound_un hB3)
      · rw [finalCtx_appendV_single, hctx, bv_all hp.isUFormula, hmp]
        simp only [add_tsub_cancel_right]
        exact mem_insert_self'
  · -- exs
    intro n p hp ih i hi hib hnB' hD
    have hnB : n ≤ B := le_trans le_self_add hnB'
    have hpL := IsSemiformula.LAct_of_LOR hp
    obtain ⟨hexs, _, hDp⟩ := dossF_exs htbl hW rfl hpL hD
    have hlen : formulaLen LAct (^∃ p) = formulaLen LAct p + 1 := formulaLen_exs hpL.isUFormula
    rw [hlen] at hib hnB' ⊢
    have hib_p : (i + 1) + 2 * formulaLen LAct p ≤ Bi := by
      calc (i + 1) + 2 * formulaLen LAct p ≤ (i + 1) + 2 * formulaLen LAct p + 1 := le_self_add
        _ = i + 2 * (formulaLen LAct p + 1) := by ring
        _ ≤ Bi := hib
    have hi1 : i + 1 ≤ Bi := le_trans le_self_add hib_p
    obtain ⟨Pp, hPp, hlp, hfp⟩ := ih (i + 1) hi1 hib_p (by rw [add_right_comm, add_assoc]; exact hnB') hDp
    have hΓ₁ := hPp.isFormulaSet htbl hΓ
    have hwn : IsSemiterm LAct 0 (cTV n) := cTV_semiterm_LAct 0 n
    have hEn : termLen LAct (cTV n) ≤ E := cTV_cap hnB hE
    have hEp : termLen LAct (^&(i + 1) : V) ≤ E := termLen_fvar_le (le_trans (add_le_add hi1 le_rfl) hEi)
    have hEi0 : termLen LAct (^&i : V) ≤ E := termLen_fvar_le (le_trans (add_le_add hi le_rfl) hEi)
    rw [cTV_succ] at hfp
    have hexs' := hPp.mem hexs
    rcases zero_or_succ (Bootstrapping.bv ℒₒᵣ p) with h0 | ⟨mp, hmp⟩
    · rw [h0, cTV_zero] at hfp
      obtain ⟨hlen, hrow⟩ := hT.bsExsZ
      obtain ⟨hok, htag, hctx⟩ := iok_bsExsZ htbl rfl hlen hrow hΓ₁ hwn hEn (by simp) hEp (by simp) hEi0 hfp hexs'
      refine ⟨_, hPp.snoc hok htag, ?_, ?_⟩
      · rw [len_appendV, len_single]; exact le_trans (add_le_add hlp le_rfl) (sq_bound_un hB3)
      · rw [finalCtx_appendV_single, hctx, bv_ex hp.isUFormula, h0, sub_spec_of_le zero_le, cTV_zero]
        exact mem_insert_self'
    · rw [hmp, cTV_succ] at hfp
      have hmpn : mp ≤ n := by
        have := hp.bv_le; rw [hmp] at this; exact le_of_add_le_add_right this
      obtain ⟨hlen, hrow⟩ := hT.bsExsS
      obtain ⟨hok, htag, hctx⟩ := iok_bsExsS htbl rfl hlen hrow hΓ₁ hwn hEn (cTV_semiterm_LAct 0 mp)
        (cTV_cap (le_trans hmpn hnB) hE) (by simp) hEp (by simp) hEi0 hfp hexs'
      refine ⟨_, hPp.snoc hok htag, ?_, ?_⟩
      · rw [len_appendV, len_single]; exact le_trans (add_le_add hlp le_rfl) (sq_bound_un hB3)
      · rw [finalCtx_appendV_single, hctx, bv_ex hp.isUFormula, hmp]
        simp only [add_tsub_cancel_right]
        exact mem_insert_self'


end bsPass

/-! ## 4. The substitution instances: the walks, `fvSeq`, the caps -/

section instances

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 4.1 The walk of a `k`-entry vector at bound `n` (`Prologue.vecWalk_ok`, generalized) -/

/-- The walk of the vector `v` (`k` entries at bound `n`): the vector object at `&0`. -/
noncomputable def vecWalkN (Ww n k v : V) : V := π₂ (descVecAux Ww n (descTVec Ww n k v) k)
noncomputable def vecCwN (Ww n k v : V) : V := π₁ (descVecAux Ww n (descTVec Ww n k v) k)

theorem vecWalkN_ok {tbl N n k v E Γ : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hv : IsSemitermVec LAct k n v)
    (hE : 2 * n + 2 * k + 2 * listSum (termLenVec LAct k v) + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (vecWalkN walkPieces n k v) ∧ NoDrop (vecWalkN walkPieces n k v) ∧
    HornOnly (vecWalkN walkPieces n k v) ∧ shiftsV (vecWalkN walkPieces n k v) = vecCwN walkPieces n k v ∧
    vecCwN walkPieces n k v ≤ 2 * listSum (termLenVec LAct k v) ∧
    len (vecWalkN walkPieces n k v) + 2 ≤ 12 * listSum (termLenVec LAct k v) + 4 ∧
    DossV walkPieces (finalCtx Γ (vecWalkN walkPieces n k v)) n k v k 0 := by
  have htl : takeLast v k = v := by have := takeLast_len_self v; rwa [hv.lh] at this
  obtain ⟨_, hcu, hVF⟩ := descVecAux_ok' htbl hW rfl hv hE k le_rfl
  rw [htl] at hcu
  obtain ⟨okU, ndU, shU, _⟩ := hVF Γ hΓ
  have hoU : HornOnly (vecWalkN walkPieces n k v) :=
    hornOnly_descVecAux rfl hv (fun i hi ↦ by have := hornOnly_describeT rfl n _ (hv.nth hi); rwa [describeT] at this) k le_rfl
  obtain ⟨_, hl⟩ := len_descVecAux_le hv (fun i hi ↦ len_describeT_le walkPieces n _ (hv.nth hi)) k le_rfl
  rw [htl] at hl
  exact ⟨okU, ndU, hoU, shU, hcu, hl, dossV_of_walk ndU⟩

/-! ### 4.2 The `fvSeq` pass over the walked `fvarVec q` -/

/-- **The `fvSeq` pass**: from the dossier of the last `j` entries of `fvarVec q` at `&i`, `fvSeqFact (vRef i j) (cTV a) (cTV q)`
(`a + j = q`) in `j + 1` shift-free Horn steps. -/
theorem fvSeq_ok {tbl N E Γ Bi q : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hE : 2 * q + 1 ≤ E) (hEi : Bi + 1 ≤ E) :
    ∀ j ≤ q, ∀ a ≤ q, a + j = q → ∀ i ≤ Bi, i + 2 * listSum (termLenVec LAct j (takeLast (Bootstrapping.fvarVec q) j)) + 1 ≤ Bi →
      DossV walkPieces Γ 0 q (Bootstrapping.fvarVec q) j i →
      ∃ P : V, HInv tbl E Γ P ∧ len P ≤ j + 1 ∧
        neg LAct (fvSeqFact (vRef i j) (cTV a) (cTV q)) ∈ finalCtx Γ P := by
  have hW := hT.walkTable
  have hvL : IsSemitermVec LAct q 0 (Bootstrapping.fvarVec q) := IsSemitermVec.LAct_of_LOR (fvarVec_isSemitermVec_LOR q)
  have hlv : len (Bootstrapping.fvarVec q) = q := Bootstrapping.len_fvarVec q
  have hEq : termLen LAct (cTV q) ≤ E := cTV_cap le_rfl hE
  intro j
  induction j using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero =>
    intro _ a _ ha i _ _ _
    rw [add_zero] at ha
    subst ha
    obtain ⟨hlen, hrow⟩ := hT.fvSeqNil
    obtain ⟨hok, htag, hctx⟩ := iok_fvSeqNil htbl rfl hlen hrow hΓ (cTV_semiterm_LAct 0 a) hEq
    refine ⟨_, HInv.single hok htag, by rw [len_single, zero_add], ?_⟩
    rw [finalCtx_single, hctx, vRef_zero]
    exact mem_insert_self'
  | succ j ih =>
    intro hj a ha hja i hi hib hDv
    have hj' : j ≤ q := le_trans le_self_add hj
    have ha1 : a + 1 ≤ q := by rw [← hja]; exact add_le_add le_rfl (le_add_self : 1 ≤ j + 1)
    have hk0 : (0 : V) < q := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hj
    have hlt : q - (j + 1) < q := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have hjl : j < len (Bootstrapping.fvarVec q) := by rw [hlv]; exact lt_of_lt_of_le (lt_add_one j) hj
    have hqa : q - (j + 1) = a := by rw [← hja]; exact add_tsub_cancel_right a (j + 1)
    have hent : (Bootstrapping.fvarVec q).[q - (j + 1)] = ^&a := by rw [Bootstrapping.nth_fvarVec q _ hlt, hqa]
    obtain ⟨hadj, _, hDt, hDtail⟩ := dossV_succ htbl hW rfl hvL hj hDv
    rw [hent] at hDt hadj hDtail
    obtain ⟨hfv, _⟩ := dossT_fvar htbl hW rfl hDt
    -- the offsets
    have htake : takeLast (Bootstrapping.fvarVec q) (j + 1) = ^&a ∷ takeLast (Bootstrapping.fvarVec q) j := by
      rw [takeLast_succ_of_lt hjl, hlv, hent]
    have hwL : IsUTermVec LAct j (takeLast (Bootstrapping.fvarVec q) j) := isUTermVec_takeLast hvL j hj'
    have hSsucc : listSum (termLenVec LAct (j + 1) (takeLast (Bootstrapping.fvarVec q) (j + 1))) =
        (a + 1) + listSum (termLenVec LAct j (takeLast (Bootstrapping.fvarVec q) j)) := by
      rw [htake, termLenVec_cons (by simp) hwL, listSum_adjoin, termLen_fvar]
    rw [hSsucc] at hib
    have hct := descCountT_succ_le htbl hW (t := (^&a : V)) (n := 0) (by simp)
    rw [termLen_fvar] at hct
    have hib_v : (i + 1 + descCountT walkPieces 0 (^&a)) + 2 * listSum (termLenVec LAct j (takeLast (Bootstrapping.fvarVec q) j)) + 1 ≤ Bi := by
      calc (i + 1 + descCountT walkPieces 0 (^&a)) + 2 * listSum (termLenVec LAct j (takeLast (Bootstrapping.fvarVec q) j)) + 1
          = i + (descCountT walkPieces 0 (^&a) + 1) + 2 * listSum (termLenVec LAct j (takeLast (Bootstrapping.fvarVec q) j)) + 1 := by ring
        _ ≤ i + 2 * (a + 1) + 2 * listSum (termLenVec LAct j (takeLast (Bootstrapping.fvarVec q) j)) + 1 :=
            add_le_add (add_le_add (add_le_add le_rfl hct) le_rfl) le_rfl
        _ = i + 2 * ((a + 1) + listSum (termLenVec LAct j (takeLast (Bootstrapping.fvarVec q) j))) + 1 := by ring
        _ ≤ Bi := hib
    have hiv : i + 1 + descCountT walkPieces 0 (^&a) ≤ Bi := le_trans le_self_add (le_trans le_self_add hib_v)
    have hi1 : i + 1 ≤ Bi := le_trans le_self_add hiv
    obtain ⟨P₀, hP₀, hl₀, hf₀⟩ := ih hj' (a + 1) ha1 (by rw [← hja]; ring) _ hiv hib_v hDtail
    have hΓ₁ := hP₀.isFormulaSet htbl hΓ
    obtain ⟨hlen, hrow⟩ := hT.fvSeqCons
    obtain ⟨hok, htag, hctx⟩ := iok_fvSeqCons htbl rfl hlen hrow hΓ₁ (cTV_semiterm_LAct 0 a) (cTV_cap (le_trans le_self_add ha1) hE)
      (cTV_semiterm_LAct 0 q) hEq (isSemiterm_vRef _ _) (termLen_vRef_le (le_trans (add_le_add hiv le_rfl) hEi))
      (by simp) (termLen_fvar_le (le_trans (add_le_add hi1 le_rfl) hEi)) (by simp) (termLen_fvar_le (le_trans (add_le_add hi le_rfl) hEi))
      (by rw [cTV_succ] at hf₀; exact hf₀) (hP₀.mem hfv) (hP₀.mem hadj)
    refine ⟨_, hP₀.snoc hok htag, ?_, ?_⟩
    · rw [len_appendV, len_single]; exact add_le_add hl₀ le_rfl
    · rw [finalCtx_appendV_single, hctx, vRef_of_ne (ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_add_self))]
      exact mem_insert_self'

/-! ### 4.3 The caps of the three substitution vectors -/

/-- `fvarVec q` is `SubstInv (q + 1)` (closed entries `&i`, `i + 1 ≤ q + 1`). -/
lemma substInv_fvarVec (q : V) : SubstInv LAct (q + 1) (Bootstrapping.fvarVec q) := by
  intro i hi
  rw [Bootstrapping.len_fvarVec] at hi
  rw [Bootstrapping.nth_fvarVec q i hi]
  exact Or.inr ⟨by simp, by rw [termLen_fvar]; exact add_le_add (le_of_lt hi) le_rfl⟩

/-- The sum of the entry lengths of `fvarVec q` is `≤ q * (q + 1)`. -/
lemma listSum_termLenVec_fvarVec_le (q : V) :
    listSum (termLenVec LAct q (Bootstrapping.fvarVec q)) ≤ q * (q + 1) := by
  have hvL : IsSemitermVec LAct q 0 (Bootstrapping.fvarVec q) := IsSemitermVec.LAct_of_LOR (fvarVec_isSemitermVec_LOR q)
  have hl : len (termLenVec LAct q (Bootstrapping.fvarVec q)) = q := len_termLenVec hvL.isUTermVec
  have := listSum_le_len_mul (M := q + 1) (termLenVec LAct q (Bootstrapping.fvarVec q)) (fun i hi ↦ by
    rw [hl] at hi
    rw [nth_termLenVec hvL.isUTermVec hi, Bootstrapping.nth_fvarVec q i hi, termLen_fvar]
    exact add_le_add (le_of_lt hi) le_rfl)
  rwa [hl] at this

/-- The step-case vector `⟨#0 + 1⟩` (bound `1`). -/
noncomputable def c1v : V := (^#(0 : V) ^+ (𝟏 : V)) ∷ 0

lemma isSemiterm_c1t : IsSemiterm LAct 1 (^#0 ^+ (𝟏 : V)) := by
  rw [isSemiterm_qqAdd_LAct_iff]; simp

lemma isSemitermVec_c1v : IsSemitermVec LAct 1 1 (c1v : V) := by
  unfold c1v
  rw [show (1 : V) = 0 + 1 by simp, IsSemitermVec.cons_iff]
  exact ⟨by rw [zero_add]; exact isSemiterm_c1t, IsSemitermVec.nil _⟩

lemma isC1_c1v : IsC1 (c1v : V) := by
  refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold c1v
  rw [qqAdd_eq, coe_one_eq]

/-- The `termBShift` of `#e + 1` is `#(e + 1) + 1`. -/
lemma termBShift_c1t (e : V) : termBShift LAct (^#e ^+ (𝟏 : V)) = ^#(e + 1) ^+ 𝟏 := by
  have h1 : IsUTermVec LAct 2 (?[^#e, (𝟏 : V)] : V) := by simp [qqOne_uterm_LAct]
  unfold qqAdd
  rw [termBShift_func (isFunc_LAct_addIndex) h1]
  congr 1
  refine nth_ext' 2 (len_termBShiftVec h1) (by rw [len_adjoin, len_adjoin, len_nil]; norm_num) fun i hi ↦ ?_
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · rw [nth_termBShiftVec h1 hi]; simp
  · rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · rw [nth_termBShiftVec h1 hi]; simp
      rw [qqOne_eq, termBShift_func isFunc_LAct_oneIndex (by simp), termBShiftVec_nil]
    · exfalso
      have : (2 : V) ≤ i + 1 + 1 := by
        calc (2 : V) = 0 + 1 + 1 := by norm_num
          _ ≤ i + 1 + 1 := add_le_add (add_le_add zero_le le_rfl) le_rfl
      exact absurd hi (not_lt.mpr this)

/-- The iterates of `⟨#0 + 1⟩`: `⟨#0, …, #(e-1), #e + 1⟩`. -/
lemma qVecIterV_c1v : ∀ e : V,
    (∀ i < e, (qVecIterV LAct c1v e).[i] = ^#i) ∧ (qVecIterV LAct c1v e).[e] = ^#e ^+ 𝟏 := by
  intro e
  induction e using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero =>
    refine ⟨fun i hi ↦ absurd hi (not_lt.mpr zero_le), ?_⟩
    rw [qVecIterV_zero]; simp [c1v]
  | succ e ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have hv : IsSemitermVec LAct (1 + e) (1 + e) (qVecIterV LAct c1v e) := isSemitermVec_qVecIterV isSemitermVec_c1v e
    have hlen : len (qVecIterV LAct c1v e) = 1 + e := hv.lh
    rw [qVecIterV_succ]
    unfold qVec
    rw [hlen]
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · rcases zero_or_succ i with rfl | ⟨i, rfl⟩
      · simp
      · rw [nth_adjoin_succ, nth_termBShiftVec hv.isUTermVec (by rw [add_comm]; exact lt_of_lt_of_le (lt_of_add_lt_add_right hi) le_self_add)]
        rw [ih₁ i (lt_of_add_lt_add_right hi), termBShift_bvar]
    · rw [nth_adjoin_succ, nth_termBShiftVec hv.isUTermVec (by rw [add_comm]; exact lt_add_one e), ih₂, termBShift_c1t]

/-- Every entry of the `e`-th iterate of `⟨#0 + 1⟩` has length `≤ e + 3`. -/
lemma termLen_qVecIterV_c1v_le (e : V) : ∀ i < 1 + e, termLen LAct (qVecIterV LAct c1v e).[i] ≤ e + 3 := by
  intro i hi
  obtain ⟨ih₁, ih₂⟩ := qVecIterV_c1v e
  rcases lt_or_eq_of_le (lt_succ_iff_le.mp (by rw [add_comm] at hi; exact hi)) with hlt | rfl
  · rw [ih₁ i hlt, termLen_bvar]
    exact le_trans (add_le_add (le_of_lt hlt) le_rfl) (add_le_add le_rfl (by norm_num))
  · rw [ih₂, termLen_qqAdd isFunc_LAct_addIndex (by simp) qqOne_uterm_LAct, termLen_bvar, termLen_qqOne isFunc_LAct_oneIndex]
    exact le_of_eq (by ring)

lemma listSum_qVecIterV_c1v_le (e : V) :
    listSum (termLenVec LAct (1 + e) (qVecIterV LAct c1v e)) ≤ (1 + e) * (e + 3) := by
  have hv : IsSemitermVec LAct (1 + e) (1 + e) (qVecIterV LAct c1v e) := isSemitermVec_qVecIterV isSemitermVec_c1v e
  have hl : len (termLenVec LAct (1 + e) (qVecIterV LAct c1v e)) = 1 + e := len_termLenVec hv.isUTermVec
  have := listSum_le_len_mul (M := e + 3) (termLenVec LAct (1 + e) (qVecIterV LAct c1v e)) (fun i hi ↦ by
    rw [hl] at hi
    rw [nth_termLenVec hv.isUTermVec hi]
    exact termLen_qVecIterV_c1v_le e i hi)
  rwa [hl] at this

/-- The walk-length cap of `certSubst` at `⟨#0 + 1⟩` (`len_qWalkP_le`, with the bespoke sum bound). -/
lemma len_qWalkP_c1v_le (Wd e : V) :
    len (π₂ (qWalkP Wd (1 + e) (1 + e) (qVecIterV LAct c1v e))) + 2 ≤ 12 * ((1 + e + 1) * (e + 1 + 3)) + 4 := by
  have hv : IsSemitermVec LAct (1 + e + 1) (1 + e + 1) (qVecIterV LAct c1v (e + 1)) := by
    have := isSemitermVec_qVecIterV isSemitermVec_c1v (e + 1); rwa [← add_assoc] at this
  have htl : takeLast (qVecIterV LAct c1v (e + 1)) (1 + e + 1) = qVecIterV LAct c1v (e + 1) := by
    rw [← hv.lh]; exact takeLast_len_self _
  obtain ⟨_, hl⟩ := len_descVecAux_le hv (fun i hi ↦ len_describeT_le Wd _ _ (hv.nth hi)) (1 + e + 1) le_rfl
  rw [htl] at hl
  unfold qWalkP
  rw [← qVecIterV_succ]
  refine le_trans hl ?_
  have := listSum_qVecIterV_c1v_le (e + 1)
  rw [← add_assoc] at this
  exact add_le_add (mul_le_mul_of_nonneg_left this zero_le) (le_refl _)

/-! ### 4.4 `certShift` on a shift-invariant formula (`shift b = b`) -/

/-- `shiftFact &ib &ib` from the dossier of a shift-invariant `b` (bound `q`) at `&ib`: `certShift` re-indexed to the table. -/
theorem shiftSelf_ok {tbl N E Γ q b ib : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hb : IsSemiformula LAct q b) (hsh : shift LAct b = b) (hD : DossF walkPieces Γ q b ib)
    (hE : 2 * q + 2 * formulaLen LAct b + 8 ≤ E) (hEi : ib + 2 * formulaLen LAct b + 1 ≤ E) :
    ∃ P : V, HInv tbl E Γ P ∧ len P ≤ 12 * formulaLen LAct b ∧ neg LAct (shiftFact (^&ib) (^&ib)) ∈ finalCtx Γ P := by
  have hC := hT.proTable.certTable
  have hDj : DossF walkPieces Γ q (shift LAct b) ib := by rw [hsh]; exact hD
  obtain ⟨hok, hnd, hho, hs, hf⟩ := certShift_ok (tbl := certView tbl) (N := N) (Wd := walkPieces) (W := certPieces)
    (hT.proTable.tableOK_certView htbl) hC rfl rfl hb hE hEi hEi hΓ hD hDj
  refine ⟨reidxL (certShift certPieces q b ib ib),
    ⟨(listOK_reidxL hT.proTable hok).mono (by exact_mod_cast (by decide : 8 ≤ 9)), noDrop'_reidxL hnd.noDrop',
      hornOnly_reidxL hho, by rw [shiftsV_reidxL, hs]⟩, ?_, ?_⟩
  · rw [len_reidxL]; exact le_trans le_self_add (len_certShift_le hb)
  · rw [finalCtx_reidxL]; exact hf

end instances

/-! ## 5. The assembly -/

section assembly

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 5.0 Powers of the size bound, the shifted-list invariant, the semantic shape of the body -/

/-- `gp G n = G^n` (repeated multiplication, `ℕ`-indexed). -/
noncomputable def gp (G : V) : ℕ → V
  | 0 => 1
  | n + 1 => gp G n * G

@[simp] lemma gp_zero (G : V) : gp G 0 = 1 := rfl
@[simp] lemma gp_succ (G : V) (n : ℕ) : gp G (n + 1) = gp G n * G := rfl

lemma one_le_gp {G : V} (hG : 1 ≤ G) : ∀ n : ℕ, 1 ≤ gp G n
  | 0 => le_rfl
  | n + 1 => by
    rw [gp_succ]
    calc (1 : V) = 1 * 1 := by ring
      _ ≤ gp G n * G := mul_le_mul (one_le_gp hG n) hG zero_le zero_le

lemma gp_le_gp_succ {G : V} (hG : 1 ≤ G) (n : ℕ) : gp G n ≤ gp G (n + 1) := by
  rw [gp_succ]
  calc gp G n = gp G n * 1 := by ring
    _ ≤ gp G n * G := mul_le_mul_of_nonneg_left hG zero_le

lemma gp_mono {G : V} (hG : 1 ≤ G) {a b : ℕ} (h : a ≤ b) : gp G a ≤ gp G b := by
  induction b with
  | zero => rw [Nat.le_zero.mp h]
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · exact le_trans (ih (Nat.lt_succ_iff.mp hlt)) (gp_le_gp_succ hG b)
    · rw [Nat.le_antisymm h hge]

lemma gp_add (G : V) (a : ℕ) : ∀ b : ℕ, gp G (a + b) = gp G a * gp G b
  | 0 => by simp
  | b + 1 => by rw [← Nat.add_assoc, gp_succ, gp_add G a b, gp_succ]; ring

lemma le_gp_one (G : V) : G = gp G 1 := by simp

/-- A list with eigenvariables: applicable at cap `9`, cut-admitting, Horn-only, with `σ` shifts. -/
def WInv (tbl E Γ P σ : V) : Prop :=
  ListOK tbl E ((9 : ℕ) : V) Γ P ∧ NoDrop' P ∧ HornOnly P ∧ shiftsV P = σ

lemma WInv.append {tbl E Γ P₁ P₂ σ₁ σ₂ : V} (h₁ : WInv tbl E Γ P₁ σ₁) (h₂ : WInv tbl E (finalCtx Γ P₁) P₂ σ₂) :
    WInv tbl E Γ (appendV P₁ P₂) (σ₁ + σ₂) :=
  ⟨listOK_appendV h₁.1 h₂.1, noDrop'_appendV h₁.2.1 h₂.2.1, hornOnly_appendV h₁.2.2.1 h₂.2.2.1,
    by rw [shiftsV_appendV, h₁.2.2.2, h₂.2.2.2]⟩

lemma WInv.isFormulaSet {tbl N E Γ P σ : V} (htbl : TableOK tbl N) (hΓ : IsFormulaSet LAct Γ) (h : WInv tbl E Γ P σ) :
    IsFormulaSet LAct (finalCtx Γ P) :=
  finalCtx_isFormulaSet 9 htbl hΓ h.1

lemma WInv.dossF {tbl E Γ P σ W n r i : V} (h : WInv tbl E Γ P σ) (hD : DossF W Γ n r i) :
    DossF W (finalCtx Γ P) n r (i + σ) := by
  have := dossF_transport' h.2.1 hD; rwa [h.2.2.2] at this
lemma WInv.dossV {tbl E Γ P σ W n k v j i : V} (h : WInv tbl E Γ P σ) (hD : DossV W Γ n k v j i) :
    DossV W (finalCtx Γ P) n k v j (i + σ) := by
  have := dossV_transport' h.2.1 hD; rwa [h.2.2.2] at this
lemma WInv.substFact {tbl E Γ P σ y w p : V} (h : WInv tbl E Γ P σ) (hy : IsSemiterm LAct 0 y) (hw : IsSemiterm LAct 0 w)
    (hp : IsSemiterm LAct 0 p) (hx : neg LAct (substFact y w p) ∈ Γ) :
    neg LAct (substFact (termShiftIterV y σ) (termShiftIterV w σ) (termShiftIterV p σ)) ∈ finalCtx Γ P := by
  have := mem_finalCtx_of_mem' h.2.1 hx
  rwa [h.2.2.2, shiftIterV_neg (isFormula_substFact hy hw hp), shiftIterV_substFact hy hw hp] at this
lemma HInv.winv {tbl E Γ P : V} (h : HInv tbl E Γ P) : WInv tbl E Γ P 0 := h

/-- The walk of a formula as a `WInv` list. -/
lemma walkF_winv {tbl N E Γ n r : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hr : IsSemiformula LAct n r)
    (hE : 2 * n + 2 * formulaLen LAct r + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) :
    WInv tbl E Γ (describeF walkPieces n r) (descCountF walkPieces n r) ∧
    descCountF walkPieces n r + 1 ≤ 2 * formulaLen LAct r ∧ len (describeF walkPieces n r) ≤ 12 * formulaLen LAct r ∧
    DossF walkPieces (finalCtx Γ (describeF walkPieces n r)) n r 0 := by
  obtain ⟨hok, hnd, hsh, hc, _⟩ := describeF_ok htbl hW hr hE hΓ
  exact ⟨⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), hnd.noDrop', hornOnly_describeF rfl hr, hsh⟩, hc,
    le_trans le_self_add (len_describeF_le walkPieces hr), dossF_of_walk hnd⟩

/-- The walk of a vector as a `WInv` list. -/
lemma walkV_winv {tbl N E Γ n k v : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hv : IsSemitermVec LAct k n v)
    (hE : 2 * n + 2 * k + 2 * listSum (termLenVec LAct k v) + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) :
    WInv tbl E Γ (vecWalkN walkPieces n k v) (vecCwN walkPieces n k v) ∧
    vecCwN walkPieces n k v ≤ 2 * listSum (termLenVec LAct k v) ∧
    len (vecWalkN walkPieces n k v) ≤ 12 * listSum (termLenVec LAct k v) + 4 ∧
    DossV walkPieces (finalCtx Γ (vecWalkN walkPieces n k v)) n k v k 0 := by
  obtain ⟨hok, hnd, hho, hsh, hc, hl, hD⟩ := vecWalkN_ok htbl hW hv hE hΓ
  exact ⟨⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), hnd.noDrop', hho, hsh⟩, hc, le_trans le_self_add hl, hD⟩

/-- The base-case vector `⟨⌜0⌝⟩` as a `V`-code. -/
noncomputable def c0v : V := (^func 0 0 0 : V) ∷ 0

lemma isC0_c0v : IsC0 (c0v : V) := ⟨_, rfl, rfl⟩
lemma c0t_eq : (^func 0 0 0 : V) = 𝟎 := coe_zero_eq.symm
lemma isSemiterm_c0t : IsSemiterm LAct 0 (^func 0 0 0 : V) := by rw [c0t_eq]; exact isSemiterm_qqZero_LAct 0
lemma termLen_c0t : termLen LAct (^func 0 0 0 : V) = 1 := by rw [c0t_eq]; exact termLen_qqZero isFunc_LAct_zeroIndex
lemma isSemitermVec_c0v : IsSemitermVec LAct 1 0 (c0v : V) := by
  unfold c0v; rw [show (1 : V) = 0 + 1 by simp, IsSemitermVec.cons_iff]
  exact ⟨isSemiterm_c0t, IsSemitermVec.nil _⟩
lemma termLen_c1t : termLen LAct (^#(0 : V) ^+ (𝟏 : V)) = 3 := by
  rw [termLen_qqAdd isFunc_LAct_addIndex (by simp) qqOne_uterm_LAct, termLen_bvar, termLen_qqOne isFunc_LAct_oneIndex]
  ring

/-- **The shape of the induction body in the `LAct` vocabulary**: for an `ℒₒᵣ`-1-formula `K`,
`indBodyVal K = x ⋎ ((∃ (K ⋏ ns)) ⋎ (∀ K))` with `x = subst c0v (neg K)`, `ns = subst c1v (neg K)`. -/
theorem indBodyVal_shape {K : V} (hK : IsSemiformula ℒₒᵣ 1 K) :
    indBodyVal K = subst LAct c0v (neg LAct K) ^⋎ ((^∃ (K ^⋏ subst LAct c1v (neg LAct K))) ^⋎ ^∀ K) := by
  have hc0O := isC0_isSemitermVec (isC0_c0v (V := V))
  have hc1O := isC1_isSemitermVec (isC1_c1v (V := V))
  have hx : subst LAct c0v (neg LAct K) = neg ℒₒᵣ (subst ℒₒᵣ c0v K) := by
    rw [substs_neg (IsSemiformula.LAct_of_LOR hK) (IsSemitermVec.LAct_of_LOR hc0O), subst_LAct_eq hK.isUFormula hc0O.isUTermVec,
      neg_LAct_eq (IsSemiformula.subst hK hc0O).isUFormula]
  have hns : subst LAct c1v (neg LAct K) = neg ℒₒᵣ (subst ℒₒᵣ c1v K) := by
    rw [substs_neg (IsSemiformula.LAct_of_LOR hK) (IsSemitermVec.LAct_of_LOR hc1O), subst_LAct_eq hK.isUFormula hc1O.isUTermVec,
      neg_LAct_eq (IsSemiformula.subst hK hc1O).isUFormula]
  rw [hx, hns]
  unfold indBodyVal
  rw [← isC0_val (isC0_c0v (V := V)), ← isC1_val (isC1_c1v (V := V))]
  simp only [Bootstrapping.imp]
  have hs1K : IsUFormula ℒₒᵣ (subst ℒₒᵣ c1v K) := (IsSemiformula.subst hK hc1O).isUFormula
  have hor : IsUFormula ℒₒᵣ (neg ℒₒᵣ K ^⋎ subst ℒₒᵣ c1v K) := by simp [hK.isUFormula.neg, hs1K]
  rw [neg_all hor, neg_or hK.isUFormula.neg hs1K, IsUFormula.neg_neg hK.isUFormula]

/-- `formulaLen (qqAlls b m) = formulaLen b + m`. -/
lemma formulaLen_qqAlls {b : V} (hb : IsUFormula LAct b) : ∀ m : V, formulaLen LAct (qqAlls b m) = formulaLen LAct b + m := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [qqAlls_succ, formulaLen_all (isUFormula_qqAlls.mpr hb), ih, add_assoc]

end assembly

/-! ### 5.1 The three `certSubst` instances (re-indexed to the table) -/

section substInst

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `certSubst` re-indexed to a `ProTable`, as a `WInv` list. -/
lemma certSubst_winv {tbl N E Γ n m w iw r i j Q L : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (hw : IsSemitermVec LAct n m w) (hr : IsSemiformula LAct n r) (hPre : SubFPre E Q n m w r i j iw Γ)
    (hL : ∀ e ≤ formulaLen LAct r, len (π₂ (qWalkP walkPieces (m + e) (n + e) (qVecIterV LAct w e))) ≤ L)
    (hDi : DossF walkPieces Γ n r i) (hDj : DossF walkPieces Γ m (subst LAct w r) j) (hDw : DossV walkPieces Γ m n w n iw) :
    ∃ S sh : V, WInv tbl E Γ S sh ∧ sh ≤ 2 * Q * formulaLen LAct r ∧ len S ≤ sfK L Q * formulaLen LAct r ∧
      neg LAct (substFact (^&(j + sh)) (vRef (iw + sh) n) (^&(i + sh))) ∈ finalCtx Γ S := by
  obtain ⟨hok, hnd, hho, hsh, hlen, hf⟩ := certSubst_ok (tbl := certView tbl) (N := N) (Wd := walkPieces) (W := certPieces)
    (hP.tableOK_certView htbl) hP.certTable rfl rfl hw hr hPre hL hDi hDj hDw
  refine ⟨reidxL (certSubst certPieces walkPieces n m w iw r i j), shiftsV (certSubst certPieces walkPieces n m w iw r i j),
    ⟨listOK_reidxL hP hok, noDrop'_reidxL hnd, hornOnly_reidxL hho, shiftsV_reidxL _⟩, hsh, ?_, ?_⟩
  · rw [len_reidxL]; exact hlen
  · rw [finalCtx_reidxL]; exact hf

/-- **The instance `s = subst (fvarVec m) b`** (`Q₆ = (m + |b|)(m + |b| + m + 1)`). -/
theorem substInst_fv {tbl N E Γ m b i j iw : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hb : IsSemiformula LAct m b)
    (hE1 : 2 * formulaLen LAct b + 2 * (m + formulaLen LAct b) + 2 * ((m + formulaLen LAct b) * (m + formulaLen LAct b + (m + 1))) + 9 ≤ E)
    (hE3 : 2 * m + 2 * formulaLen LAct b + 8 ≤ E)
    (hE4 : i + 2 * formulaLen LAct b * ((m + formulaLen LAct b) * (m + formulaLen LAct b + (m + 1)) + 1) + 1 ≤ E)
    (hE5 : j + 2 * formulaLen LAct (subst LAct (Bootstrapping.fvarVec m) b) +
      2 * ((m + formulaLen LAct b) * (m + formulaLen LAct b + (m + 1))) * formulaLen LAct b + 1 ≤ E)
    (hE6 : iw + 2 * ((m + formulaLen LAct b) * (m + formulaLen LAct b + (m + 1))) * (formulaLen LAct b + 1) + 2 ≤ E)
    (hDi : DossF walkPieces Γ m b i) (hDj : DossF walkPieces Γ 0 (subst LAct (Bootstrapping.fvarVec m) b) j)
    (hDw : DossV walkPieces Γ 0 m (Bootstrapping.fvarVec m) m iw) :
    ∃ S sh : V, WInv tbl E Γ S sh ∧ sh ≤ 2 * ((m + formulaLen LAct b) * (m + formulaLen LAct b + (m + 1))) * formulaLen LAct b ∧
      len S ≤ sfK (12 * ((m + formulaLen LAct b + 1) * (m + formulaLen LAct b + 1 + (m + 1))) + 2)
        ((m + formulaLen LAct b) * (m + formulaLen LAct b + (m + 1))) * formulaLen LAct b ∧
      neg LAct (substFact (^&(j + sh)) (vRef (iw + sh) m) (^&(i + sh))) ∈ finalCtx Γ S := by
  have hw : IsSemitermVec LAct m 0 (Bootstrapping.fvarVec m) := IsSemitermVec.LAct_of_LOR (fvarVec_isSemitermVec_LOR m)
  have hinv := substInv_fvarVec (V := V) m
  have hcap := listSum_termLenVec_qVecIterV_cap (D := formulaLen LAct b) hw hinv
  have hPre : SubFPre E ((m + formulaLen LAct b) * (m + formulaLen LAct b + (m + 1))) m 0 (Bootstrapping.fvarVec m) b i j iw Γ := by
    refine ⟨fun e he ↦ ?_, hcap, hE3, hE4, hE5, hE6, hΓ⟩
    calc 2 * (0 + e) + 2 * (m + e) + 2 * listSum (termLenVec LAct (m + e) (qVecIterV LAct (Bootstrapping.fvarVec m) e)) + 9
        ≤ 2 * (0 + formulaLen LAct b) + 2 * (m + formulaLen LAct b) +
          2 * ((m + formulaLen LAct b) * (m + formulaLen LAct b + (m + 1))) + 9 :=
          add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl he) zero_le)
            (mul_le_mul_of_nonneg_left (add_le_add le_rfl he) zero_le)) (mul_le_mul_of_nonneg_left (hcap e he) zero_le)) le_rfl
      _ = 2 * formulaLen LAct b + 2 * (m + formulaLen LAct b) + 2 * ((m + formulaLen LAct b) * (m + formulaLen LAct b + (m + 1))) + 9 := by ring
      _ ≤ E := hE1
  exact certSubst_winv htbl hT.proTable hw hb hPre (len_qWalkP_cap (Wd := walkPieces) hw hinv) hDi hDj hDw

/-- **The instance `x = subst ⟨⌜0⌝⟩ (neg K)`** (`Q₇ = (1 + |nk|)(1 + |nk| + 1)`). -/
theorem substInst_c0 {tbl N E Γ nk i j iw : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hnk : IsSemiformula LAct 1 nk)
    (hE1 : 4 * formulaLen LAct nk + 2 * ((1 + formulaLen LAct nk) * (1 + formulaLen LAct nk + 1)) + 11 ≤ E)
    (hE4 : i + 2 * formulaLen LAct nk * ((1 + formulaLen LAct nk) * (1 + formulaLen LAct nk + 1) + 1) + 1 ≤ E)
    (hE5 : j + 2 * formulaLen LAct (subst LAct c0v nk) +
      2 * ((1 + formulaLen LAct nk) * (1 + formulaLen LAct nk + 1)) * formulaLen LAct nk + 1 ≤ E)
    (hE6 : iw + 2 * ((1 + formulaLen LAct nk) * (1 + formulaLen LAct nk + 1)) * (formulaLen LAct nk + 1) + 2 ≤ E)
    (hDi : DossF walkPieces Γ 1 nk i) (hDj : DossF walkPieces Γ 0 (subst LAct c0v nk) j)
    (hDw : DossV walkPieces Γ 0 1 c0v 1 iw) :
    ∃ S sh : V, WInv tbl E Γ S sh ∧ sh ≤ 2 * ((1 + formulaLen LAct nk) * (1 + formulaLen LAct nk + 1)) * formulaLen LAct nk ∧
      len S ≤ sfK (12 * ((1 + formulaLen LAct nk + 1) * (1 + formulaLen LAct nk + 1 + 1)) + 2)
        ((1 + formulaLen LAct nk) * (1 + formulaLen LAct nk + 1)) * formulaLen LAct nk ∧
      neg LAct (substFact (^&(j + sh)) (^&(iw + sh)) (^&(i + sh))) ∈ finalCtx Γ S := by
  have ht : IsSemiterm LAct 0 (^func 0 0 0 : V) := isSemiterm_c0t
  have hB : termLen LAct (^func 0 0 0 : V) ≤ 1 := le_of_eq termLen_c0t
  have hPre : SubFPre E ((1 + formulaLen LAct nk) * (1 + formulaLen LAct nk + 1)) 1 0 ((^func 0 0 0 : V) ∷ 0) nk i j iw Γ :=
    subFPre_single ht hB hE1 hE4 hE5 hE6 hΓ
  have hL := qWalkP_single_cap (Wd := walkPieces) (t := (^func 0 0 0 : V)) (B := 1) (r := nk) ht hB
  obtain ⟨S, sh, hS, hsh, hl, hf⟩ := certSubst_winv htbl hT.proTable isSemitermVec_c0v hnk hPre hL hDi hDj hDw
  refine ⟨S, sh, hS, hsh, hl, ?_⟩
  rwa [vRef_of_ne _root_.one_ne_zero] at hf

/-- **The instance `ns = subst ⟨#0 + 1⟩ (neg K)`** (`Q₈ = (1 + |nk|)(|nk| + 3)`, the bespoke caps of §4.3). -/
theorem substInst_c1 {tbl N E Γ nk i j iw : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hnk : IsSemiformula LAct 1 nk)
    (hE1 : 4 * (1 + formulaLen LAct nk) + 2 * ((1 + formulaLen LAct nk) * (formulaLen LAct nk + 3)) + 9 ≤ E)
    (hE3 : 2 * 1 + 2 * formulaLen LAct nk + 8 ≤ E)
    (hE4 : i + 2 * formulaLen LAct nk * ((1 + formulaLen LAct nk) * (formulaLen LAct nk + 3) + 1) + 1 ≤ E)
    (hE5 : j + 2 * formulaLen LAct (subst LAct c1v nk) +
      2 * ((1 + formulaLen LAct nk) * (formulaLen LAct nk + 3)) * formulaLen LAct nk + 1 ≤ E)
    (hE6 : iw + 2 * ((1 + formulaLen LAct nk) * (formulaLen LAct nk + 3)) * (formulaLen LAct nk + 1) + 2 ≤ E)
    (hDi : DossF walkPieces Γ 1 nk i) (hDj : DossF walkPieces Γ 1 (subst LAct c1v nk) j)
    (hDw : DossV walkPieces Γ 1 1 c1v 1 iw) :
    ∃ S sh : V, WInv tbl E Γ S sh ∧ sh ≤ 2 * ((1 + formulaLen LAct nk) * (formulaLen LAct nk + 3)) * formulaLen LAct nk ∧
      len S ≤ sfK (12 * ((1 + formulaLen LAct nk + 1) * (formulaLen LAct nk + 1 + 3)) + 4)
        ((1 + formulaLen LAct nk) * (formulaLen LAct nk + 3)) * formulaLen LAct nk ∧
      neg LAct (substFact (^&(j + sh)) (^&(iw + sh)) (^&(i + sh))) ∈ finalCtx Γ S := by
  have hcap : ∀ e ≤ formulaLen LAct nk, listSum (termLenVec LAct (1 + e) (qVecIterV LAct c1v e)) ≤
      (1 + formulaLen LAct nk) * (formulaLen LAct nk + 3) := fun e he ↦
    le_trans (listSum_qVecIterV_c1v_le e) (mul_le_mul (add_le_add le_rfl he) (add_le_add he le_rfl) zero_le zero_le)
  have hPre : SubFPre E ((1 + formulaLen LAct nk) * (formulaLen LAct nk + 3)) 1 1 c1v nk i j iw Γ := by
    refine ⟨fun e he ↦ ?_, hcap, hE3, hE4, hE5, hE6, hΓ⟩
    calc 2 * (1 + e) + 2 * (1 + e) + 2 * listSum (termLenVec LAct (1 + e) (qVecIterV LAct c1v e)) + 9
        ≤ 2 * (1 + formulaLen LAct nk) + 2 * (1 + formulaLen LAct nk) +
          2 * ((1 + formulaLen LAct nk) * (formulaLen LAct nk + 3)) + 9 :=
          add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl he) zero_le)
            (mul_le_mul_of_nonneg_left (add_le_add le_rfl he) zero_le)) (mul_le_mul_of_nonneg_left (hcap e he) zero_le)) le_rfl
      _ = 4 * (1 + formulaLen LAct nk) + 2 * ((1 + formulaLen LAct nk) * (formulaLen LAct nk + 3)) + 9 := by ring
      _ ≤ E := hE1
  have hL : ∀ e ≤ formulaLen LAct nk, len (π₂ (qWalkP walkPieces (1 + e) (1 + e) (qVecIterV LAct c1v e))) ≤
      12 * ((1 + formulaLen LAct nk + 1) * (formulaLen LAct nk + 1 + 3)) + 4 := fun e he ↦ by
    have h1 := len_qWalkP_c1v_le walkPieces e
    have h2 : 12 * ((1 + e + 1) * (e + 1 + 3)) + 4 ≤ 12 * ((1 + formulaLen LAct nk + 1) * (formulaLen LAct nk + 1 + 3)) + 4 :=
      add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul (add_le_add (add_le_add le_rfl he) le_rfl)
        (add_le_add (add_le_add he le_rfl) le_rfl) zero_le zero_le) zero_le) le_rfl
    exact le_trans le_self_add (le_trans h1 h2)
  obtain ⟨S, sh, hS, hsh, hl, hf⟩ := certSubst_winv htbl hT.proTable isSemitermVec_c1v hnk hPre hL hDi hDj hDw
  refine ⟨S, sh, hS, hsh, hl, ?_⟩
  rwa [vRef_of_ne _root_.one_ne_zero] at hf

end substInst

/-! ### 5.2 The five walks: `s`, `neg K`, `fvarVec m`, `⟨⌜0⌝⟩`, `⟨#0 + 1⟩` -/

section walks

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma listSum_termLenVec_c0v : listSum (termLenVec LAct 1 (c0v : V)) = 1 := by
  have := listSum_termLenVec_single (V := V) isSemiterm_c0t
  rw [termLen_c0t] at this; exact this

lemma listSum_termLenVec_c1v : listSum (termLenVec LAct 1 (c1v : V)) = 3 := by
  have := termLenVec_cons (L := LAct) (k := (0 : V)) (t := (^#(0 : V) ^+ (𝟏 : V))) (ts := 0) isSemiterm_c1t.isUTerm (by simp)
  rw [zero_add] at this
  unfold c1v
  rw [this, listSum_adjoin, termLenVec_nil, listSum_nil, termLen_c1t, add_zero]

/-- **The five walks**, one `WInv` list: the dossiers of `s` (bound `0`), `neg K` (bound `1`), `fvarVec m`, `⟨⌜0⌝⟩` and
`⟨#0 + 1⟩` (bound `1`) at the returned offsets, `p`'s dossier moved by the total `A` of the eigenvariable counts. -/
theorem stageWalks {tbl N E Γ p ip s nk m : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hsL : IsSemiformula LAct 0 s) (hnkL : IsSemiformula LAct 1 nk)
    (hE : 2 * formulaLen LAct s + 2 * formulaLen LAct nk + 2 * m + 2 * (m * (m + 1)) + 20 ≤ E)
    (hD : DossF walkPieces Γ 0 p ip) :
    ∃ L A js ink iw iw0 : V, WInv tbl E Γ L A ∧
      A ≤ 2 * formulaLen LAct s + 2 * formulaLen LAct nk + 2 * (m * (m + 1)) + 8 ∧
      len L ≤ 12 * formulaLen LAct s + 12 * formulaLen LAct nk + 12 * (m * (m + 1)) + 60 ∧
      js ≤ A ∧ ink ≤ A ∧ iw ≤ A ∧ iw0 ≤ A ∧
      DossF walkPieces (finalCtx Γ L) 0 p (ip + A) ∧ DossF walkPieces (finalCtx Γ L) 0 s js ∧
      DossF walkPieces (finalCtx Γ L) 1 nk ink ∧ DossV walkPieces (finalCtx Γ L) 0 m (Bootstrapping.fvarVec m) m iw ∧
      DossV walkPieces (finalCtx Γ L) 0 1 c0v 1 iw0 ∧ DossV walkPieces (finalCtx Γ L) 1 1 c1v 1 0 := by
  have hW := hT.walkTable
  have hfv : IsSemitermVec LAct m 0 (Bootstrapping.fvarVec m) := IsSemitermVec.LAct_of_LOR (fvarVec_isSemitermVec_LOR m)
  have hSfv := listSum_termLenVec_fvarVec_le (V := V) m
  -- 1. the walk of `s`
  have hE1 : 2 * 0 + 2 * formulaLen LAct s + 8 ≤ E := by
    calc 2 * 0 + 2 * formulaLen LAct s + 8 ≤ 2 * 0 + 2 * formulaLen LAct s + 8 + (2 * formulaLen LAct nk + 2 * m + 2 * (m * (m + 1)) + 12) := le_self_add
      _ = 2 * formulaLen LAct s + 2 * formulaLen LAct nk + 2 * m + 2 * (m * (m + 1)) + 20 := by ring
      _ ≤ E := hE
  obtain ⟨h1, hc1, hl1, hD1s⟩ := walkF_winv htbl hW hsL hE1 hΓ
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ (describeF walkPieces 0 s) := ⟨_, rfl⟩
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact h1.isFormulaSet htbl hΓ
  have hD1p : DossF walkPieces Γ₁ 0 p (ip + descCountF walkPieces 0 s) := by rw [hΓ₁]; exact h1.dossF hD
  rw [← hΓ₁] at hD1s
  -- 2. the walk of `neg K`
  have hE2 : 2 * 1 + 2 * formulaLen LAct nk + 8 ≤ E := by
    calc 2 * 1 + 2 * formulaLen LAct nk + 8 ≤ 2 * 1 + 2 * formulaLen LAct nk + 8 + (2 * formulaLen LAct s + 2 * m + 2 * (m * (m + 1)) + 10) := le_self_add
      _ = 2 * formulaLen LAct s + 2 * formulaLen LAct nk + 2 * m + 2 * (m * (m + 1)) + 20 := by ring
      _ ≤ E := hE
  obtain ⟨h2, hc2, hl2, hD2k⟩ := walkF_winv htbl hW hnkL hE2 hΓ₁f
  obtain ⟨Γ₂, hΓ₂⟩ : ∃ Γ', Γ' = finalCtx Γ₁ (describeF walkPieces 1 nk) := ⟨_, rfl⟩
  have hΓ₂f : IsFormulaSet LAct Γ₂ := by rw [hΓ₂]; exact h2.isFormulaSet htbl hΓ₁f
  have hD2p := h2.dossF hD1p
  have hD2s := h2.dossF hD1s
  rw [← hΓ₂] at hD2p hD2s hD2k
  -- 3. the walk of `fvarVec m`
  have hE3 : 2 * 0 + 2 * m + 2 * listSum (termLenVec LAct m (Bootstrapping.fvarVec m)) + 8 ≤ E := by
    calc 2 * 0 + 2 * m + 2 * listSum (termLenVec LAct m (Bootstrapping.fvarVec m)) + 8
        ≤ 2 * 0 + 2 * m + 2 * (m * (m + 1)) + 8 := add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hSfv zero_le)) le_rfl
      _ ≤ 2 * 0 + 2 * m + 2 * (m * (m + 1)) + 8 + (2 * formulaLen LAct s + 2 * formulaLen LAct nk + 12) := le_self_add
      _ = 2 * formulaLen LAct s + 2 * formulaLen LAct nk + 2 * m + 2 * (m * (m + 1)) + 20 := by ring
      _ ≤ E := hE
  obtain ⟨h3, hc3, hl3, hD3w⟩ := walkV_winv htbl hW hfv hE3 hΓ₂f
  obtain ⟨Γ₃, hΓ₃⟩ : ∃ Γ', Γ' = finalCtx Γ₂ (vecWalkN walkPieces 0 m (Bootstrapping.fvarVec m)) := ⟨_, rfl⟩
  have hΓ₃f : IsFormulaSet LAct Γ₃ := by rw [hΓ₃]; exact h3.isFormulaSet htbl hΓ₂f
  have hD3p := h3.dossF hD2p
  have hD3s := h3.dossF hD2s
  have hD3k := h3.dossF hD2k
  rw [← hΓ₃] at hD3p hD3s hD3k hD3w
  -- 4. the walk of `⟨⌜0⌝⟩`
  have hE4 : 2 * 0 + 2 * 1 + 2 * listSum (termLenVec LAct 1 (c0v : V)) + 8 ≤ E := by
    rw [listSum_termLenVec_c0v]
    calc (2 * 0 + 2 * 1 + 2 * 1 + 8 : V) = 12 := by norm_num
      _ ≤ 12 + (2 * formulaLen LAct s + 2 * formulaLen LAct nk + 2 * m + 2 * (m * (m + 1)) + 8) := le_self_add
      _ = 2 * formulaLen LAct s + 2 * formulaLen LAct nk + 2 * m + 2 * (m * (m + 1)) + 20 := by ring
      _ ≤ E := hE
  obtain ⟨h4, hc4, hl4, hD4w0⟩ := walkV_winv htbl hW isSemitermVec_c0v hE4 hΓ₃f
  rw [listSum_termLenVec_c0v] at hc4 hl4
  obtain ⟨Γ₄, hΓ₄⟩ : ∃ Γ', Γ' = finalCtx Γ₃ (vecWalkN walkPieces 0 1 c0v) := ⟨_, rfl⟩
  have hΓ₄f : IsFormulaSet LAct Γ₄ := by rw [hΓ₄]; exact h4.isFormulaSet htbl hΓ₃f
  have hD4p := h4.dossF hD3p
  have hD4s := h4.dossF hD3s
  have hD4k := h4.dossF hD3k
  have hD4w := h4.dossV hD3w
  rw [← hΓ₄] at hD4p hD4s hD4k hD4w hD4w0
  -- 5. the walk of `⟨#0 + 1⟩`
  have hE5 : 2 * 1 + 2 * 1 + 2 * listSum (termLenVec LAct 1 (c1v : V)) + 8 ≤ E := by
    rw [listSum_termLenVec_c1v]
    calc (2 * 1 + 2 * 1 + 2 * 3 + 8 : V) = 18 := by norm_num
      _ ≤ 18 + (2 * formulaLen LAct s + 2 * formulaLen LAct nk + 2 * m + 2 * (m * (m + 1)) + 2) := le_self_add
      _ = 2 * formulaLen LAct s + 2 * formulaLen LAct nk + 2 * m + 2 * (m * (m + 1)) + 20 := by ring
      _ ≤ E := hE
  obtain ⟨h5, hc5, hl5, hD5w1⟩ := walkV_winv htbl hW isSemitermVec_c1v hE5 hΓ₄f
  rw [listSum_termLenVec_c1v] at hc5 hl5
  obtain ⟨Γ₅, hΓ₅⟩ : ∃ Γ', Γ' = finalCtx Γ₄ (vecWalkN walkPieces 1 1 c1v) := ⟨_, rfl⟩
  have hD5p := h5.dossF hD4p
  have hD5s := h5.dossF hD4s
  have hD5k := h5.dossF hD4k
  have hD5w := h5.dossV hD4w
  have hD5w0 := h5.dossV hD4w0
  rw [← hΓ₅] at hD5p hD5s hD5k hD5w hD5w0 hD5w1
  -- the composite
  have hL : WInv tbl E Γ (appendV (describeF walkPieces 0 s) (appendV (describeF walkPieces 1 nk)
      (appendV (vecWalkN walkPieces 0 m (Bootstrapping.fvarVec m)) (appendV (vecWalkN walkPieces 0 1 c0v) (vecWalkN walkPieces 1 1 c1v)))))
      (descCountF walkPieces 0 s + (descCountF walkPieces 1 nk + (vecCwN walkPieces 0 m (Bootstrapping.fvarVec m) +
        (vecCwN walkPieces 0 1 c0v + vecCwN walkPieces 1 1 c1v)))) := by
    refine h1.append ?_
    rw [← hΓ₁]
    refine h2.append ?_
    rw [← hΓ₂]
    refine h3.append ?_
    rw [← hΓ₃]
    refine h4.append ?_
    rw [← hΓ₄]
    exact h5
  have hctx : finalCtx Γ (appendV (describeF walkPieces 0 s) (appendV (describeF walkPieces 1 nk)
      (appendV (vecWalkN walkPieces 0 m (Bootstrapping.fvarVec m)) (appendV (vecWalkN walkPieces 0 1 c0v) (vecWalkN walkPieces 1 1 c1v))))) = Γ₅ := by
    rw [finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, ← hΓ₁, ← hΓ₂, ← hΓ₃, ← hΓ₄, ← hΓ₅]
  have hc1' : descCountF walkPieces 0 s ≤ 2 * formulaLen LAct s := le_trans le_self_add hc1
  have hc2' : descCountF walkPieces 1 nk ≤ 2 * formulaLen LAct nk := le_trans le_self_add hc2
  have hc3' : vecCwN walkPieces 0 m (Bootstrapping.fvarVec m) ≤ 2 * (m * (m + 1)) := le_trans hc3 (mul_le_mul_of_nonneg_left hSfv zero_le)
  refine ⟨_, _, descCountF walkPieces 1 nk + (vecCwN walkPieces 0 m (Bootstrapping.fvarVec m) + (vecCwN walkPieces 0 1 c0v + vecCwN walkPieces 1 1 c1v)),
    vecCwN walkPieces 0 m (Bootstrapping.fvarVec m) + (vecCwN walkPieces 0 1 c0v + vecCwN walkPieces 1 1 c1v),
    vecCwN walkPieces 0 1 c0v + vecCwN walkPieces 1 1 c1v, vecCwN walkPieces 1 1 c1v, hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc descCountF walkPieces 0 s + (descCountF walkPieces 1 nk + (vecCwN walkPieces 0 m (Bootstrapping.fvarVec m) +
        (vecCwN walkPieces 0 1 c0v + vecCwN walkPieces 1 1 c1v)))
        ≤ 2 * formulaLen LAct s + (2 * formulaLen LAct nk + (2 * (m * (m + 1)) + (2 * 1 + 2 * 3))) :=
          add_le_add hc1' (add_le_add hc2' (add_le_add hc3' (add_le_add hc4 hc5)))
      _ = 2 * formulaLen LAct s + 2 * formulaLen LAct nk + 2 * (m * (m + 1)) + 8 := by ring
  · rw [len_appendV, len_appendV, len_appendV, len_appendV]
    calc len (describeF walkPieces 0 s) + (len (describeF walkPieces 1 nk) + (len (vecWalkN walkPieces 0 m (Bootstrapping.fvarVec m)) +
        (len (vecWalkN walkPieces 0 1 c0v) + len (vecWalkN walkPieces 1 1 c1v))))
        ≤ 12 * formulaLen LAct s + (12 * formulaLen LAct nk + ((12 * (m * (m + 1)) + 4) + ((12 * 1 + 4) + (12 * 3 + 4)))) :=
          add_le_add hl1 (add_le_add hl2 (add_le_add (le_trans hl3 (add_le_add (mul_le_mul_of_nonneg_left hSfv zero_le) le_rfl))
            (add_le_add hl4 hl5)))
      _ = 12 * formulaLen LAct s + 12 * formulaLen LAct nk + 12 * (m * (m + 1)) + 60 := by ring
  · exact le_add_self
  · exact le_trans le_add_self le_add_self
  · exact le_trans le_add_self (le_trans le_add_self le_add_self)
  · exact le_trans le_add_self (le_trans le_add_self (le_trans le_add_self le_add_self))
  · rw [hctx]
    have := hD5p
    rwa [show ip + descCountF walkPieces 0 s + descCountF walkPieces 1 nk + vecCwN walkPieces 0 m (Bootstrapping.fvarVec m) +
      vecCwN walkPieces 0 1 c0v + vecCwN walkPieces 1 1 c1v = ip + (descCountF walkPieces 0 s + (descCountF walkPieces 1 nk +
      (vecCwN walkPieces 0 m (Bootstrapping.fvarVec m) + (vecCwN walkPieces 0 1 c0v + vecCwN walkPieces 1 1 c1v)))) by ring] at this
  · rw [hctx]
    have := hD5s
    rwa [show 0 + descCountF walkPieces 1 nk + vecCwN walkPieces 0 m (Bootstrapping.fvarVec m) + vecCwN walkPieces 0 1 c0v +
      vecCwN walkPieces 1 1 c1v = descCountF walkPieces 1 nk + (vecCwN walkPieces 0 m (Bootstrapping.fvarVec m) +
      (vecCwN walkPieces 0 1 c0v + vecCwN walkPieces 1 1 c1v)) by ring] at this
  · rw [hctx]
    have := hD5k
    rwa [show 0 + vecCwN walkPieces 0 m (Bootstrapping.fvarVec m) + vecCwN walkPieces 0 1 c0v + vecCwN walkPieces 1 1 c1v =
      vecCwN walkPieces 0 m (Bootstrapping.fvarVec m) + (vecCwN walkPieces 0 1 c0v + vecCwN walkPieces 1 1 c1v) by ring] at this
  · rw [hctx]
    have := hD5w
    rwa [zero_add] at this
  · rw [hctx]
    have := hD5w0
    rwa [zero_add] at this
  · rw [hctx]; exact hD5w1

end walks

/-! ### 5.3 The body's dossier and the size-bound helpers -/

section bodyDoss

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The pieces of the body `indBodyVal K` in the `LAct` vocabulary. -/
noncomputable def xK (K : V) : V := subst LAct c0v (neg LAct K)
noncomputable def nsK (K : V) : V := subst LAct c1v (neg LAct K)
noncomputable def n1K (K : V) : V := K ^⋏ nsK K
noncomputable def zK (K : V) : V := ^∀ K
noncomputable def yK (K : V) : V := (^∃ n1K K) ^⋎ zK K

lemma indBodyVal_eq_yK {K : V} (hK : IsSemiformula ℒₒᵣ 1 K) : indBodyVal K = xK K ^⋎ yK K := by
  rw [indBodyVal_shape hK]; rfl

lemma nkL_of {K : V} (hK : IsSemiformula ℒₒᵣ 1 K) : IsSemiformula LAct 1 (neg LAct K) := by
  rw [neg_LAct_eq hK.isUFormula]; exact IsSemiformula.LAct_of_LOR hK.neg
lemma xK_isSemiformula {K : V} (hK : IsSemiformula ℒₒᵣ 1 K) : IsSemiformula LAct 0 (xK K) :=
  IsSemiformula.subst (nkL_of hK) isSemitermVec_c0v
lemma nsK_isSemiformula {K : V} (hK : IsSemiformula ℒₒᵣ 1 K) : IsSemiformula LAct 1 (nsK K) :=
  IsSemiformula.subst (nkL_of hK) isSemitermVec_c1v
lemma n1K_isSemiformula {K : V} (hK : IsSemiformula ℒₒᵣ 1 K) : IsSemiformula LAct 1 (n1K K) :=
  IsSemiformula.and.mpr ⟨IsSemiformula.LAct_of_LOR hK, nsK_isSemiformula hK⟩
lemma zK_isSemiformula {K : V} (hK : IsSemiformula ℒₒᵣ 1 K) : IsSemiformula LAct 0 (zK K) :=
  IsSemiformula.all.mpr (by rw [zero_add]; exact IsSemiformula.LAct_of_LOR hK)
lemma yK_isSemiformula {K : V} (hK : IsSemiformula ℒₒᵣ 1 K) : IsSemiformula LAct 0 (yK K) :=
  IsSemiformula.or.mpr ⟨IsSemiformula.exs.mpr (by rw [zero_add]; exact n1K_isSemiformula hK), zK_isSemiformula hK⟩
lemma indBodyVal_isSemiformula {K : V} (hK : IsSemiformula ℒₒᵣ 1 K) : IsSemiformula LAct 0 (indBodyVal K) := by
  rw [indBodyVal_eq_yK hK]; exact IsSemiformula.or.mpr ⟨xK_isSemiformula hK, yK_isSemiformula hK⟩

/-- The lengths of the pieces are bounded by the body's. -/
lemma formulaLen_pieces_le {K : V} (hK : IsSemiformula ℒₒᵣ 1 K) :
    formulaLen LAct (xK K) ≤ formulaLen LAct (indBodyVal K) ∧ formulaLen LAct (yK K) ≤ formulaLen LAct (indBodyVal K) ∧
    formulaLen LAct (zK K) ≤ formulaLen LAct (indBodyVal K) ∧ formulaLen LAct (nsK K) ≤ formulaLen LAct (indBodyVal K) ∧
    formulaLen LAct K ≤ formulaLen LAct (indBodyVal K) := by
  have hx := xK_isSemiformula hK
  have hy := yK_isSemiformula hK
  have hz := zK_isSemiformula hK
  have hn1 := n1K_isSemiformula hK
  have hns := nsK_isSemiformula hK
  have hKL := IsSemiformula.LAct_of_LOR hK
  have e1 : formulaLen LAct (indBodyVal K) = formulaLen LAct (xK K) + formulaLen LAct (yK K) + 1 := by
    rw [indBodyVal_eq_yK hK]; exact formulaLen_or hx.isUFormula hy.isUFormula
  have e2 : formulaLen LAct (yK K) = formulaLen LAct (^∃ n1K K) + formulaLen LAct (zK K) + 1 :=
    formulaLen_or (IsSemiformula.exs.mpr (by rw [zero_add]; exact hn1)).isUFormula hz.isUFormula
  have e3 : formulaLen LAct (^∃ n1K K) = formulaLen LAct (n1K K) + 1 := formulaLen_exs hn1.isUFormula
  have e4 : formulaLen LAct (n1K K) = formulaLen LAct K + formulaLen LAct (nsK K) + 1 := formulaLen_and hKL.isUFormula hns.isUFormula
  have e5 : formulaLen LAct (zK K) = formulaLen LAct K + 1 := formulaLen_all hKL.isUFormula
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; exact le_trans le_self_add le_self_add
  · rw [e1]; exact le_trans le_add_self le_self_add
  · rw [e1, e2]; exact le_trans le_add_self (le_trans le_self_add (le_trans le_add_self le_self_add))
  · rw [e1, e2, e3, e4]
    have h : formulaLen LAct (nsK K) ≤ formulaLen LAct K + formulaLen LAct (nsK K) + 1 + 1 + formulaLen LAct (zK K) + 1 :=
      le_trans le_add_self (le_trans le_self_add (le_trans le_self_add (le_trans le_self_add le_self_add)))
    exact le_trans h (le_trans le_add_self le_self_add)
  · rw [e1, e2, e3, e4]
    have h : formulaLen LAct K ≤ formulaLen LAct K + formulaLen LAct (nsK K) + 1 + 1 + formulaLen LAct (zK K) + 1 :=
      le_trans le_self_add (le_trans le_self_add (le_trans le_self_add (le_trans le_self_add le_self_add)))
    exact le_trans h (le_trans le_add_self le_self_add)

/-- **The body's dossier, decomposed**: from the dossier of `indBodyVal K` at `&js` (bound `0`), the five shape facts and
the sub-dossiers of `x`, `ns`, and the two copies of `K` at their walk offsets. -/
theorem bodyDoss {tbl N Γ K js : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hK : IsSemiformula ℒₒᵣ 1 K)
    (hD : DossF walkPieces Γ 0 (indBodyVal K) js) :
    neg LAct (orFact (^&js) (^&(js + descCountF walkPieces 0 (yK K) + 1)) (^&(js + 1))) ∈ Γ ∧
    neg LAct (orFact (^&(js + 1)) (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1)) (^&(js + 1 + 1))) ∈ Γ ∧
    neg LAct (exsFact (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1)) (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1))) ∈ Γ ∧
    neg LAct (andFact (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1))
      (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + descCountF walkPieces 1 (nsK K) + 1))
      (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + 1))) ∈ Γ ∧
    neg LAct (allFact (^&(js + 1 + 1)) (^&(js + 1 + 1 + 1))) ∈ Γ ∧
    DossF walkPieces Γ 0 (xK K) (js + descCountF walkPieces 0 (yK K) + 1) ∧
    DossF walkPieces Γ 1 (nsK K) (js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + 1) ∧
    DossF walkPieces Γ 1 K (js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + descCountF walkPieces 1 (nsK K) + 1) ∧
    DossF walkPieces Γ 1 K (js + 1 + 1 + 1) := by
  have hx := xK_isSemiformula hK
  have hy := yK_isSemiformula hK
  have hz := zK_isSemiformula hK
  have hn1 := n1K_isSemiformula hK
  have hns := nsK_isSemiformula hK
  have hKL := IsSemiformula.LAct_of_LOR hK
  have hu : IsSemiformula LAct 0 (^∃ n1K K) := IsSemiformula.exs.mpr (by rw [zero_add]; exact hn1)
  rw [indBodyVal_eq_yK hK] at hD
  obtain ⟨h1, _, hDy, hDx⟩ := dossF_or htbl hW rfl hx hy hD
  have hDy' : DossF walkPieces Γ 0 ((^∃ n1K K) ^⋎ zK K) (js + 1) := hDy
  obtain ⟨h2, _, hDz, hDu⟩ := dossF_or htbl hW rfl hu hz hDy'
  obtain ⟨h3, _, hDn1⟩ := dossF_exs htbl hW rfl (by rw [zero_add]; exact hn1) hDu
  rw [zero_add] at hDn1
  have hDn1' : DossF walkPieces Γ 1 (K ^⋏ nsK K) (js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1) := hDn1
  obtain ⟨h4, _, hDns, hDK1⟩ := dossF_and htbl hW rfl hKL hns hDn1'
  have hDz' : DossF walkPieces Γ 0 (^∀ K) (js + 1 + 1) := hDz
  obtain ⟨h5, _, hDK2⟩ := dossF_all htbl hW rfl (by rw [zero_add]; exact hKL) hDz'
  rw [zero_add] at hDK2
  exact ⟨h1, h2, h3, h4, h5, hDx, hDns, hDK1, hDK2⟩

/-! ### The size-bound helpers (`gp Z k`) -/

lemma le_gp_of_le {Z a : V} {c : V} {k : ℕ} (hZ : 1 ≤ Z) (ha : a ≤ c * gp Z k) {k' : ℕ} (hk : k ≤ k') : a ≤ c * gp Z k' :=
  le_trans ha (mul_le_mul_of_nonneg_left (gp_mono hZ hk) zero_le)

lemma add_gp_le {Z a b c₁ c₂ : V} {i j k : ℕ} (hZ : 1 ≤ Z) (ha : a ≤ c₁ * gp Z i) (hb : b ≤ c₂ * gp Z j) (hi : i ≤ k) (hj : j ≤ k) :
    a + b ≤ (c₁ + c₂) * gp Z k := by
  calc a + b ≤ c₁ * gp Z k + c₂ * gp Z k := add_le_add (le_gp_of_le hZ ha hi) (le_gp_of_le hZ hb hj)
    _ = (c₁ + c₂) * gp Z k := by ring

lemma mul_gp_le {Z a b c₁ c₂ : V} {i j : ℕ} (ha : a ≤ c₁ * gp Z i) (hb : b ≤ c₂ * gp Z j) :
    a * b ≤ (c₁ * c₂) * gp Z (i + j) := by
  calc a * b ≤ (c₁ * gp Z i) * (c₂ * gp Z j) := mul_le_mul ha hb zero_le zero_le
    _ = (c₁ * c₂) * gp Z (i + j) := by rw [gp_add]; ring

lemma const_gp_le {Z : V} (c : V) (hZ : 1 ≤ Z) (k : ℕ) : c ≤ c * gp Z k := by
  calc c = c * 1 := by ring
    _ ≤ c * gp Z k := mul_le_mul_of_nonneg_left (one_le_gp hZ k) zero_le

lemma atom_gp_le {Z a : V} (ha : a ≤ Z) : a ≤ 1 * gp Z 1 := by rw [one_mul]; simpa using ha

lemma coef_gp_le {Z a c c' : V} {k : ℕ} (ha : a ≤ c * gp Z k) (hc : c ≤ c') : a ≤ c' * gp Z k :=
  le_trans ha (mul_le_mul_of_nonneg_right hc zero_le)

end bodyDoss

/-! ### 5.4 Stage A: the walks and the three substitution instances, with the size bounds -/

section stageA

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma cmul_gp_le {Z a c' : V} {k : ℕ} (c : V) (ha : a ≤ c' * gp Z k) : c * a ≤ (c * c') * gp Z k := by
  calc c * a ≤ c * (c' * gp Z k) := mul_le_mul_of_nonneg_left ha zero_le
    _ = (c * c') * gp Z k := by ring

lemma gp_final {Z a c c' : V} {k k' : ℕ} (hZ : 1 ≤ Z) (ha : a ≤ c * gp Z k) (hk : k ≤ k') (hc : c ≤ c') : a ≤ c' * gp Z k' :=
  le_trans (le_gp_of_le hZ ha hk) (mul_le_mul_of_nonneg_right hc zero_le)

/-- **Stage A**: from the dossier of `p = qqAlls b m` at `&ip`, ONE list with eigenvariables (`σ` shifts) holding the
dossiers of `s = indBodyVal K`, `neg K`, `fvarVec m`, `⟨⌜0⌝⟩`, `⟨#0 + 1⟩` and the three substitution facts
`s = subst (fvarVec m) b`, `x = subst ⟨⌜0⌝⟩ (neg K)`, `ns = subst ⟨#0 + 1⟩ (neg K)`; every size polynomial in the
bound `Z ≥ ip, m, |b|, |s|, |K|`. -/
theorem stageA {tbl N E Γ p ip b m K Z : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hZ : 1 ≤ Z) (hb : IsSemiformula LAct m b) (hK : IsSemiformula ℒₒᵣ 1 K) (hp : p = qqAlls b m)
    (hs : subst LAct (Bootstrapping.fvarVec m) b = indBodyVal K)
    (hip : ip ≤ Z) (hm : m ≤ Z) (hLb : formulaLen LAct b ≤ Z) (hLs : formulaLen LAct (indBodyVal K) ≤ Z)
    (hLk : formulaLen LAct K ≤ Z) (hE : 200 * gp Z 3 ≤ E) (hD : DossF walkPieces Γ 0 p ip) :
    ∃ L σ js ink iw iw0 iw1 : V, WInv tbl E Γ L σ ∧ σ ≤ 100 * gp Z 3 ∧ len L ≤ 4000 * gp Z 5 ∧
      js ≤ σ ∧ ink ≤ σ ∧ iw ≤ σ ∧ iw0 ≤ σ ∧ iw1 ≤ σ ∧
      DossF walkPieces (finalCtx Γ L) 0 p (ip + σ) ∧ DossF walkPieces (finalCtx Γ L) 0 (indBodyVal K) js ∧
      DossF walkPieces (finalCtx Γ L) 1 (neg LAct K) ink ∧
      DossV walkPieces (finalCtx Γ L) 0 m (Bootstrapping.fvarVec m) m iw ∧
      DossV walkPieces (finalCtx Γ L) 0 1 c0v 1 iw0 ∧ DossV walkPieces (finalCtx Γ L) 1 1 c1v 1 iw1 ∧
      neg LAct (substFact (^&js) (vRef iw m) (^&(ip + σ + m))) ∈ finalCtx Γ L ∧
      neg LAct (substFact (^&(js + descCountF walkPieces 0 (yK K) + 1)) (^&iw0) (^&ink)) ∈ finalCtx Γ L ∧
      neg LAct (substFact (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + 1)) (^&iw1) (^&ink)) ∈ finalCtx Γ L := by
  have hW := hT.walkTable
  have hKL := IsSemiformula.LAct_of_LOR hK
  have hnkL := nkL_of hK
  have hsL := indBodyVal_isSemiformula hK
  have hLnk : formulaLen LAct (neg LAct K) = formulaLen LAct K := formulaLen_neg hKL.isUFormula
  obtain ⟨hLx, hLy, hLz, hLns, hLK⟩ := formulaLen_pieces_le hK
  -- the atoms in the `gp Z k` form
  have hZ1 : (1 : V) ≤ 1 * gp Z 1 := by rw [one_mul]; exact one_le_gp hZ 1
  have hm' := atom_gp_le hm
  have hLb' := atom_gp_le hLb
  have hLs' := atom_gp_le hLs
  have hLk' := atom_gp_le hLk
  have hip' := atom_gp_le hip
  have hLnk' : formulaLen LAct (neg LAct K) ≤ 1 * gp Z 1 := by rw [hLnk]; exact hLk'
  have hLx' : formulaLen LAct (xK K) ≤ 1 * gp Z 1 := atom_gp_le (le_trans hLx hLs)
  have hLns' : formulaLen LAct (nsK K) ≤ 1 * gp Z 1 := atom_gp_le (le_trans hLns hLs)
  have hLy' : formulaLen LAct (yK K) ≤ 1 * gp Z 1 := atom_gp_le (le_trans hLy hLs)
  have hLz' : formulaLen LAct (zK K) ≤ 1 * gp Z 1 := atom_gp_le (le_trans hLz hLs)
  -- the quadratic quantities
  have hmLb : m + formulaLen LAct b ≤ (1 + 1) * gp Z 1 := add_gp_le hZ hm' hLb' le_rfl le_rfl
  have hQ6 : (m + formulaLen LAct b) * (m + formulaLen LAct b + (m + 1)) ≤ ((1 + 1) * (1 + 1 + (1 + 1))) * gp Z 2 :=
    mul_gp_le hmLb (add_gp_le hZ hmLb (add_gp_le hZ hm' hZ1 le_rfl le_rfl) le_rfl le_rfl)
  have hQ6' : (m + formulaLen LAct b) * (m + formulaLen LAct b + (m + 1)) ≤ 8 * gp Z 2 := gp_final hZ hQ6 le_rfl (by norm_num)
  have h1Lk : 1 + formulaLen LAct K ≤ (1 + 1) * gp Z 1 := add_gp_le hZ hZ1 hLk' le_rfl le_rfl
  have hQ7' : (1 + formulaLen LAct K) * (1 + formulaLen LAct K + 1) ≤ 6 * gp Z 2 :=
    gp_final hZ (mul_gp_le h1Lk (add_gp_le hZ h1Lk hZ1 le_rfl le_rfl)) le_rfl (by norm_num)
  have hQ8' : (1 + formulaLen LAct K) * (formulaLen LAct K + 3) ≤ 8 * gp Z 2 :=
    gp_final hZ (mul_gp_le h1Lk (add_gp_le hZ hLk' (const_gp_le (3 : V) hZ 1) le_rfl le_rfl)) le_rfl (by norm_num)
  have hmm : m * (m + 1) ≤ 2 * gp Z 2 :=
    gp_final hZ (mul_gp_le hm' (add_gp_le hZ hm' hZ1 le_rfl le_rfl)) le_rfl (by norm_num)
  -- Stage 1–5: the walks
  have hEw : 2 * formulaLen LAct (indBodyVal K) + 2 * formulaLen LAct (neg LAct K) + 2 * m + 2 * (m * (m + 1)) + 20 ≤ E := by
    refine le_trans ?_ hE
    exact gp_final hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ (cmul_gp_le 2 hLs') (cmul_gp_le 2 hLnk') le_rfl le_rfl)
      (cmul_gp_le 2 hm') le_rfl le_rfl) (cmul_gp_le 2 hmm) (by norm_num) le_rfl) (const_gp_le (20 : V) hZ 2) le_rfl le_rfl)
      (by norm_num) (by norm_num)
  obtain ⟨L₀, A, js₅, ink₅, iw₅, iw0₅, hL₀, hA, hlen₀, hjs₅, hink₅, hiw₅, hiw0₅, hD5p, hD5s, hD5k, hD5w, hD5w0, hD5w1⟩ :=
    stageWalks htbl hT hΓ hsL hnkL (m := m) hEw hD
  obtain ⟨Γ₅, hΓ₅⟩ : ∃ Γ', Γ' = finalCtx Γ L₀ := ⟨_, rfl⟩
  have hΓ₅f : IsFormulaSet LAct Γ₅ := by rw [hΓ₅]; exact hL₀.isFormulaSet htbl hΓ
  rw [← hΓ₅] at hD5p hD5s hD5k hD5w hD5w0 hD5w1
  have hAZ : A ≤ 16 * gp Z 2 := by
    refine le_trans hA ?_
    exact gp_final hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ (cmul_gp_le 2 hLs') (cmul_gp_le 2 hLnk') le_rfl le_rfl)
      (cmul_gp_le 2 hmm) (by norm_num) le_rfl) (const_gp_le (8 : V) hZ 2) le_rfl le_rfl) le_rfl (by norm_num)
  have hlen₀Z : len L₀ ≤ 108 * gp Z 2 := by
    refine le_trans hlen₀ ?_
    exact gp_final hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ (cmul_gp_le 12 hLs') (cmul_gp_le 12 hLnk') le_rfl le_rfl)
      (cmul_gp_le 12 hmm) (by norm_num) le_rfl) (const_gp_le (60 : V) hZ 2) le_rfl le_rfl) le_rfl (by norm_num)
  -- the dossier of `b` inside `p`'s
  have hD5b : DossF walkPieces Γ₅ m b (ip + A + m) := by
    have := dossF_qqAlls htbl hW rfl hb (by rw [← hp]; exact hD5p) m le_rfl 0 (zero_add m)
    rwa [qqAlls_zero] at this
  -- Stage 6: `s = subst (fvarVec m) b`
  have hDs' : DossF walkPieces Γ₅ 0 (subst LAct (Bootstrapping.fvarVec m) b) js₅ := by rw [hs]; exact hD5s
  have hcapA : ip + A + m ≤ 18 * gp Z 2 :=
    gp_final hZ (add_gp_le hZ (add_gp_le hZ hip' hAZ (by norm_num) le_rfl) hm' le_rfl (by norm_num)) le_rfl (by norm_num)
  have hjs₅Z : js₅ ≤ 16 * gp Z 2 := le_trans hjs₅ hAZ
  have hink₅Z : ink₅ ≤ 16 * gp Z 2 := le_trans hink₅ hAZ
  have hiw₅Z : iw₅ ≤ 16 * gp Z 2 := le_trans hiw₅ hAZ
  have hiw0₅Z : iw0₅ ≤ 16 * gp Z 2 := le_trans hiw0₅ hAZ
  have hLsub : formulaLen LAct (subst LAct (Bootstrapping.fvarVec m) b) ≤ 1 * gp Z 1 := by rw [hs]; exact hLs'
  obtain ⟨S₆, sh6, hS₆, hsh6, hl6, hf6⟩ := substInst_fv (i := ip + A + m) (j := js₅) (iw := iw₅) htbl hT hΓ₅f hb
    (le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ (cmul_gp_le 2 hLb') (cmul_gp_le 2 hmLb) le_rfl le_rfl)
      (cmul_gp_le 2 hQ6') (by norm_num) le_rfl) (const_gp_le (9 : V) hZ 2) le_rfl le_rfl) (by norm_num) (by norm_num)) hE)
    (le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ (cmul_gp_le 2 hm') (cmul_gp_le 2 hLb') le_rfl le_rfl)
      (const_gp_le (8 : V) hZ 1) le_rfl le_rfl) (by norm_num) (by norm_num)) hE)
    (le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ hcapA
      (mul_gp_le (cmul_gp_le 2 hLb') (add_gp_le hZ hQ6' (const_gp_le (1 : V) hZ 2) le_rfl le_rfl)) (by norm_num) le_rfl)
      (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)) hE)
    (le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ hjs₅Z (cmul_gp_le 2 hLsub) le_rfl (by norm_num))
      (mul_gp_le (cmul_gp_le 2 hQ6') hLb') (by norm_num) le_rfl) (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)) hE)
    (le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ hiw₅Z
      (mul_gp_le (cmul_gp_le 2 hQ6') (add_gp_le hZ hLb' hZ1 le_rfl le_rfl)) (by norm_num) le_rfl)
      (const_gp_le (2 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)) hE)
    hD5b hDs' hD5w
  obtain ⟨Γ₆, hΓ₆⟩ : ∃ Γ', Γ' = finalCtx Γ₅ S₆ := ⟨_, rfl⟩
  have hΓ₆f : IsFormulaSet LAct Γ₆ := by rw [hΓ₆]; exact hS₆.isFormulaSet htbl hΓ₅f
  have hD6p := hS₆.dossF hD5p
  have hD6s := hS₆.dossF hD5s
  have hD6k := hS₆.dossF hD5k
  have hD6w := hS₆.dossV hD5w
  have hD6w0 := hS₆.dossV hD5w0
  have hD6w1 := hS₆.dossV hD5w1
  rw [← hΓ₆] at hD6p hD6s hD6k hD6w hD6w0 hD6w1 hf6
  have hsh6Z : sh6 ≤ 16 * gp Z 3 := le_trans hsh6 (gp_final hZ (mul_gp_le (cmul_gp_le 2 hQ6') hLb') le_rfl (by norm_num))
  have hl6Z : len S₆ ≤ 1200 * gp Z 5 := by
    refine le_trans hl6 ?_
    unfold sfK
    have hL6 : 12 * ((m + formulaLen LAct b + 1) * (m + formulaLen LAct b + 1 + (m + 1))) + 2 ≤ 200 * gp Z 2 := by
      have h1 : m + formulaLen LAct b + 1 ≤ (1 + 1 + 1) * gp Z 1 := add_gp_le hZ hmLb hZ1 le_rfl le_rfl
      have h2 : m + formulaLen LAct b + 1 + (m + 1) ≤ (1 + 1 + 1 + (1 + 1)) * gp Z 1 :=
        add_gp_le hZ h1 (add_gp_le hZ hm' hZ1 le_rfl le_rfl) le_rfl le_rfl
      exact gp_final hZ (add_gp_le hZ (cmul_gp_le 12 (mul_gp_le h1 h2)) (const_gp_le (2 : V) hZ 2) le_rfl le_rfl) le_rfl (by norm_num)
    have hQ61 : (m + formulaLen LAct b) * (m + formulaLen LAct b + (m + 1)) + 1 ≤ (8 + 1) * gp Z 2 :=
      add_gp_le hZ hQ6' (const_gp_le (1 : V) hZ 2) le_rfl le_rfl
    have hsf : 12 * ((m + formulaLen LAct b) * (m + formulaLen LAct b + (m + 1))) *
        ((m + formulaLen LAct b) * (m + formulaLen LAct b + (m + 1)) + 1) ≤ (12 * 8 * (8 + 1)) * gp Z 4 :=
      mul_gp_le (cmul_gp_le 12 hQ6') hQ61
    have := mul_gp_le (add_gp_le hZ (add_gp_le hZ (cmul_gp_le 12 hQ61) (add_gp_le hZ hL6 hsf (by norm_num) le_rfl)
      (by norm_num) le_rfl) (const_gp_le (10 : V) hZ 4) le_rfl le_rfl) hLb'
    exact le_trans (le_of_eq (by ring)) (gp_final hZ this le_rfl (by norm_num))
  -- Stage 7: `x = subst ⟨⌜0⌝⟩ (neg K)`
  obtain ⟨_, _, _, _, _, hD6x, _, _, _⟩ := bodyDoss htbl hW hK hD6s
  have hcy : descCountF walkPieces 0 (yK K) ≤ 2 * gp Z 1 := by
    have := descCountF_succ_le' htbl hW (yK_isSemiformula hK)
    exact gp_final hZ (le_trans (le_trans le_self_add this) (cmul_gp_le 2 hLy')) le_rfl (by norm_num)
  have hcz : descCountF walkPieces 0 (zK K) ≤ 2 * gp Z 1 := by
    have := descCountF_succ_le' htbl hW (zK_isSemiformula hK)
    exact gp_final hZ (le_trans (le_trans le_self_add this) (cmul_gp_le 2 hLz')) le_rfl (by norm_num)
  have hjs₆ : js₅ + sh6 ≤ 32 * gp Z 3 := gp_final hZ (add_gp_le hZ hjs₅Z hsh6Z (by norm_num) le_rfl) le_rfl (by norm_num)
  have hink₆ : ink₅ + sh6 ≤ 32 * gp Z 3 := gp_final hZ (add_gp_le hZ hink₅Z hsh6Z (by norm_num) le_rfl) le_rfl (by norm_num)
  have hiw0₆ : iw0₅ + sh6 ≤ 32 * gp Z 3 := gp_final hZ (add_gp_le hZ hiw0₅Z hsh6Z (by norm_num) le_rfl) le_rfl (by norm_num)
  have hix₆ : js₅ + sh6 + descCountF walkPieces 0 (yK K) + 1 ≤ 35 * gp Z 3 :=
    gp_final hZ (add_gp_le hZ (add_gp_le hZ hjs₆ hcy le_rfl (by norm_num)) (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)
  have hD6x' : DossF walkPieces Γ₆ 0 (subst LAct c0v (neg LAct K)) (js₅ + sh6 + descCountF walkPieces 0 (yK K) + 1) := hD6x
  obtain ⟨S₇, sh7, hS₇, hsh7, hl7, hf7⟩ := substInst_c0 (E := E) (i := ink₅ + sh6) (j := js₅ + sh6 + descCountF walkPieces 0 (yK K) + 1)
    (iw := iw0₅ + sh6) htbl hT hΓ₆f hnkL
    (by
      rw [hLnk]
      exact le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ (cmul_gp_le 4 hLk') (cmul_gp_le 2 hQ7') (by norm_num) le_rfl)
        (const_gp_le (11 : V) hZ 2) le_rfl le_rfl) (by norm_num) (by norm_num)) hE)
    (by
      rw [hLnk]
      exact le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ hink₆
        (mul_gp_le (cmul_gp_le 2 hLk') (add_gp_le hZ hQ7' (const_gp_le (1 : V) hZ 2) le_rfl le_rfl)) le_rfl le_rfl)
        (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)) hE)
    (by
      rw [hLnk]
      have hLx'' : formulaLen LAct (subst LAct c0v (neg LAct K)) ≤ 1 * gp Z 1 := hLx'
      exact le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ hix₆ (cmul_gp_le 2 hLx'') le_rfl (by norm_num))
        (mul_gp_le (cmul_gp_le 2 hQ7') hLk') le_rfl le_rfl) (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)) hE)
    (by
      rw [hLnk]
      exact le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ hiw0₆
        (mul_gp_le (cmul_gp_le 2 hQ7') (add_gp_le hZ hLk' hZ1 le_rfl le_rfl)) le_rfl le_rfl)
        (const_gp_le (2 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)) hE)
    hD6k hD6x' hD6w0
  obtain ⟨Γ₇, hΓ₇⟩ : ∃ Γ', Γ' = finalCtx Γ₆ S₇ := ⟨_, rfl⟩
  have hΓ₇f : IsFormulaSet LAct Γ₇ := by rw [hΓ₇]; exact hS₇.isFormulaSet htbl hΓ₆f
  have hD7p := hS₇.dossF hD6p
  have hD7s := hS₇.dossF hD6s
  have hD7k := hS₇.dossF hD6k
  have hD7w := hS₇.dossV hD6w
  have hD7w0 := hS₇.dossV hD6w0
  have hD7w1 := hS₇.dossV hD6w1
  have hf6₇ := hS₇.substFact (by simp) (isSemiterm_vRef _ _) (by simp) hf6
  rw [termShiftIterV_fvar, termShiftIterV_vRef, termShiftIterV_fvar] at hf6₇
  rw [← hΓ₇] at hD7p hD7s hD7k hD7w hD7w0 hD7w1 hf6₇ hf7
  rw [hLnk] at hsh7 hl7
  have hsh7Z : sh7 ≤ 12 * gp Z 3 := le_trans hsh7 (gp_final hZ (mul_gp_le (cmul_gp_le 2 hQ7') hLk') le_rfl (by norm_num))
  have hl7Z : len S₇ ≤ 744 * gp Z 5 := by
    refine le_trans hl7 ?_
    unfold sfK
    have hL7 : 12 * ((1 + formulaLen LAct K + 1) * (1 + formulaLen LAct K + 1 + 1)) + 2 ≤ 146 * gp Z 2 := by
      have h1 : 1 + formulaLen LAct K + 1 ≤ (1 + 1 + 1) * gp Z 1 := add_gp_le hZ h1Lk hZ1 le_rfl le_rfl
      have h2 : 1 + formulaLen LAct K + 1 + 1 ≤ (1 + 1 + 1 + 1) * gp Z 1 := add_gp_le hZ h1 hZ1 le_rfl le_rfl
      exact gp_final hZ (add_gp_le hZ (cmul_gp_le 12 (mul_gp_le h1 h2)) (const_gp_le (2 : V) hZ 2) le_rfl le_rfl) le_rfl (by norm_num)
    have hQ71 : (1 + formulaLen LAct K) * (1 + formulaLen LAct K + 1) + 1 ≤ (6 + 1) * gp Z 2 :=
      add_gp_le hZ hQ7' (const_gp_le (1 : V) hZ 2) le_rfl le_rfl
    have hsf : 12 * ((1 + formulaLen LAct K) * (1 + formulaLen LAct K + 1)) *
        ((1 + formulaLen LAct K) * (1 + formulaLen LAct K + 1) + 1) ≤ (12 * 6 * (6 + 1)) * gp Z 4 :=
      mul_gp_le (cmul_gp_le 12 hQ7') hQ71
    have := mul_gp_le (add_gp_le hZ (add_gp_le hZ (cmul_gp_le 12 hQ71) (add_gp_le hZ hL7 hsf (by norm_num) le_rfl)
      (by norm_num) le_rfl) (const_gp_le (10 : V) hZ 4) le_rfl le_rfl) hLk'
    exact le_trans (le_of_eq (by ring)) (gp_final hZ this le_rfl (by norm_num))
  -- Stage 8: `ns = subst ⟨#0 + 1⟩ (neg K)`
  obtain ⟨_, _, _, _, _, _, hD7ns, _, _⟩ := bodyDoss htbl hW hK hD7s
  have hjs₇ : js₅ + sh6 + sh7 ≤ 44 * gp Z 3 := gp_final hZ (add_gp_le hZ hjs₆ hsh7Z le_rfl le_rfl) le_rfl (by norm_num)
  have hink₇ : ink₅ + sh6 + sh7 ≤ 44 * gp Z 3 := gp_final hZ (add_gp_le hZ hink₆ hsh7Z le_rfl le_rfl) le_rfl (by norm_num)
  have hiw1₇ : 0 + sh6 + sh7 ≤ 28 * gp Z 3 :=
    gp_final hZ (add_gp_le hZ (add_gp_le hZ (const_gp_le (0 : V) hZ 3) hsh6Z le_rfl le_rfl) hsh7Z le_rfl le_rfl) le_rfl (by norm_num)
  have hins₇ : js₅ + sh6 + sh7 + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + 1 ≤ 50 * gp Z 3 :=
    gp_final hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ hjs₇ (const_gp_le (1 : V) hZ 3) le_rfl le_rfl)
      hcz le_rfl (by norm_num)) (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) (const_gp_le (1 : V) hZ 3) le_rfl le_rfl)
      (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)
  have hD7ns' : DossF walkPieces Γ₇ 1 (subst LAct c1v (neg LAct K))
      (js₅ + sh6 + sh7 + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + 1) := hD7ns
  obtain ⟨S₈, sh8, hS₈, hsh8, hl8, hf8⟩ := substInst_c1 (E := E) (i := ink₅ + sh6 + sh7)
    (j := js₅ + sh6 + sh7 + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + 1) (iw := 0 + sh6 + sh7) htbl hT hΓ₇f hnkL
    (by
      rw [hLnk]
      exact le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ (cmul_gp_le 4 h1Lk) (cmul_gp_le 2 hQ8') (by norm_num) le_rfl)
        (const_gp_le (9 : V) hZ 2) le_rfl le_rfl) (by norm_num) (by norm_num)) hE)
    (by
      rw [hLnk]
      exact le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ (const_gp_le (2 * 1 : V) hZ 1) (cmul_gp_le 2 hLk') le_rfl le_rfl)
        (const_gp_le (8 : V) hZ 1) le_rfl le_rfl) (by norm_num) (by norm_num)) hE)
    (by
      rw [hLnk]
      exact le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ hink₇
        (mul_gp_le (cmul_gp_le 2 hLk') (add_gp_le hZ hQ8' (const_gp_le (1 : V) hZ 2) le_rfl le_rfl)) le_rfl le_rfl)
        (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)) hE)
    (by
      rw [hLnk]
      have hLns'' : formulaLen LAct (subst LAct c1v (neg LAct K)) ≤ 1 * gp Z 1 := hLns'
      exact le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ hins₇ (cmul_gp_le 2 hLns'') le_rfl (by norm_num))
        (mul_gp_le (cmul_gp_le 2 hQ8') hLk') le_rfl le_rfl) (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)) hE)
    (by
      rw [hLnk]
      exact le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ hiw1₇
        (mul_gp_le (cmul_gp_le 2 hQ8') (add_gp_le hZ hLk' hZ1 le_rfl le_rfl)) le_rfl le_rfl)
        (const_gp_le (2 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)) hE)
    hD7k hD7ns' hD7w1
  obtain ⟨Γ₈, hΓ₈⟩ : ∃ Γ', Γ' = finalCtx Γ₇ S₈ := ⟨_, rfl⟩
  have hD8p := hS₈.dossF hD7p
  have hD8s := hS₈.dossF hD7s
  have hD8k := hS₈.dossF hD7k
  have hD8w := hS₈.dossV hD7w
  have hD8w0 := hS₈.dossV hD7w0
  have hD8w1 := hS₈.dossV hD7w1
  have hf6₈ := hS₈.substFact (by simp) (isSemiterm_vRef _ _) (by simp) hf6₇
  rw [termShiftIterV_fvar, termShiftIterV_vRef, termShiftIterV_fvar] at hf6₈
  have hf7₈ := hS₈.substFact (by simp) (by simp) (by simp) hf7
  rw [termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar] at hf7₈
  rw [← hΓ₈] at hD8p hD8s hD8k hD8w hD8w0 hD8w1 hf6₈ hf7₈ hf8
  rw [hLnk] at hsh8 hl8
  have hsh8Z : sh8 ≤ 16 * gp Z 3 := le_trans hsh8 (gp_final hZ (mul_gp_le (cmul_gp_le 2 hQ8') hLk') le_rfl (by norm_num))
  have hl8Z : len S₈ ≤ 1166 * gp Z 5 := by
    refine le_trans hl8 ?_
    unfold sfK
    have hL8 : 12 * ((1 + formulaLen LAct K + 1) * (formulaLen LAct K + 1 + 3)) + 4 ≤ 184 * gp Z 2 := by
      have h1 : 1 + formulaLen LAct K + 1 ≤ (1 + 1 + 1) * gp Z 1 := add_gp_le hZ h1Lk hZ1 le_rfl le_rfl
      have h2 : formulaLen LAct K + 1 + 3 ≤ (1 + 1 + 3) * gp Z 1 :=
        add_gp_le hZ (add_gp_le hZ hLk' hZ1 le_rfl le_rfl) (const_gp_le (3 : V) hZ 1) le_rfl le_rfl
      exact gp_final hZ (add_gp_le hZ (cmul_gp_le 12 (mul_gp_le h1 h2)) (const_gp_le (4 : V) hZ 2) le_rfl le_rfl) le_rfl (by norm_num)
    have hQ81 : (1 + formulaLen LAct K) * (formulaLen LAct K + 3) + 1 ≤ (8 + 1) * gp Z 2 :=
      add_gp_le hZ hQ8' (const_gp_le (1 : V) hZ 2) le_rfl le_rfl
    have hsf : 12 * ((1 + formulaLen LAct K) * (formulaLen LAct K + 3)) *
        ((1 + formulaLen LAct K) * (formulaLen LAct K + 3) + 1) ≤ (12 * 8 * (8 + 1)) * gp Z 4 :=
      mul_gp_le (cmul_gp_le 12 hQ8') hQ81
    have := mul_gp_le (add_gp_le hZ (add_gp_le hZ (cmul_gp_le 12 hQ81) (add_gp_le hZ hL8 hsf (by norm_num) le_rfl)
      (by norm_num) le_rfl) (const_gp_le (10 : V) hZ 4) le_rfl le_rfl) hLk'
    exact le_trans (le_of_eq (by ring)) (gp_final hZ this le_rfl (by norm_num))
  -- the composite list
  have hL : WInv tbl E Γ (appendV L₀ (appendV S₆ (appendV S₇ S₈))) (A + (sh6 + (sh7 + sh8))) := by
    refine hL₀.append ?_
    rw [← hΓ₅]
    refine hS₆.append ?_
    rw [← hΓ₆]
    refine hS₇.append ?_
    rw [← hΓ₇]
    exact hS₈
  have hctx : finalCtx Γ (appendV L₀ (appendV S₆ (appendV S₇ S₈))) = Γ₈ := by
    rw [finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, ← hΓ₅, ← hΓ₆, ← hΓ₇, ← hΓ₈]
  have hσ : A + (sh6 + (sh7 + sh8)) ≤ 100 * gp Z 3 :=
    gp_final hZ (add_gp_le hZ hAZ (add_gp_le hZ hsh6Z (add_gp_le hZ hsh7Z hsh8Z le_rfl le_rfl) le_rfl le_rfl) (by norm_num) le_rfl)
      le_rfl (by norm_num)
  refine ⟨_, A + (sh6 + (sh7 + sh8)), js₅ + sh6 + sh7 + sh8, ink₅ + sh6 + sh7 + sh8, iw₅ + sh6 + sh7 + sh8, iw0₅ + sh6 + sh7 + sh8,
    0 + sh6 + sh7 + sh8, hL, hσ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [len_appendV, len_appendV, len_appendV]
    exact gp_final hZ (add_gp_le hZ hlen₀Z (add_gp_le hZ hl6Z (add_gp_le hZ hl7Z hl8Z le_rfl le_rfl) le_rfl le_rfl) (by norm_num) le_rfl)
      le_rfl (by norm_num)
  · calc js₅ + sh6 + sh7 + sh8 ≤ A + sh6 + sh7 + sh8 := add_le_add (add_le_add (add_le_add hjs₅ le_rfl) le_rfl) le_rfl
      _ = A + (sh6 + (sh7 + sh8)) := by ring
  · calc ink₅ + sh6 + sh7 + sh8 ≤ A + sh6 + sh7 + sh8 := add_le_add (add_le_add (add_le_add hink₅ le_rfl) le_rfl) le_rfl
      _ = A + (sh6 + (sh7 + sh8)) := by ring
  · calc iw₅ + sh6 + sh7 + sh8 ≤ A + sh6 + sh7 + sh8 := add_le_add (add_le_add (add_le_add hiw₅ le_rfl) le_rfl) le_rfl
      _ = A + (sh6 + (sh7 + sh8)) := by ring
  · calc iw0₅ + sh6 + sh7 + sh8 ≤ A + sh6 + sh7 + sh8 := add_le_add (add_le_add (add_le_add hiw0₅ le_rfl) le_rfl) le_rfl
      _ = A + (sh6 + (sh7 + sh8)) := by ring
  · calc 0 + sh6 + sh7 + sh8 ≤ A + sh6 + sh7 + sh8 := add_le_add (add_le_add (add_le_add zero_le le_rfl) le_rfl) le_rfl
      _ = A + (sh6 + (sh7 + sh8)) := by ring
  · rw [hctx]
    have e : ip + A + sh6 + sh7 + sh8 = ip + (A + (sh6 + (sh7 + sh8))) := by ring
    rw [e] at hD8p; exact hD8p
  · rw [hctx]; exact hD8s
  · rw [hctx]; exact hD8k
  · rw [hctx]; exact hD8w
  · rw [hctx]; exact hD8w0
  · rw [hctx]; exact hD8w1
  · rw [hctx]
    have e : ip + A + m + sh6 + sh7 + sh8 = ip + (A + (sh6 + (sh7 + sh8))) + m := by ring
    rw [e] at hf6₈; exact hf6₈
  · rw [hctx]
    have e : js₅ + sh6 + descCountF walkPieces 0 (yK K) + 1 + sh7 + sh8 = js₅ + sh6 + sh7 + sh8 + descCountF walkPieces 0 (yK K) + 1 := by ring
    rw [e] at hf7₈; exact hf7₈
  · rw [hctx]
    have e : js₅ + sh6 + sh7 + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + 1 + sh8 =
        js₅ + sh6 + sh7 + sh8 + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + 1 := by ring
    rw [e] at hf8; exact hf8

end stageA


/-! ### 5.5 Stage B: the shift-free closing — `qqAlls`, `bs`, `shift`, `fvSeq`, `neg`, the identification, the rows -/

section stageB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `certNeg` re-indexed to the table, as an `HInv` list: `negFact &j &i` from the dossiers of `r` (at `&i`) and `neg r` (at `&j`). -/
theorem negInst_ok {tbl N E Γ n r i j : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hr : IsSemiformula LAct n r) (hE : 2 * n + 2 * formulaLen LAct r + 8 ≤ E) (hEi : i + 2 * formulaLen LAct r + 1 ≤ E)
    (hEj : j + 2 * formulaLen LAct r + 1 ≤ E) (hDi : DossF walkPieces Γ n r i) (hDj : DossF walkPieces Γ n (neg LAct r) j) :
    ∃ P : V, HInv tbl E Γ P ∧ len P ≤ 12 * formulaLen LAct r ∧ neg LAct (negFact (^&j) (^&i)) ∈ finalCtx Γ P := by
  obtain ⟨hok, hnd, hho, hs, hf⟩ := certNeg_ok (tbl := certView tbl) (N := N) (Wd := walkPieces) (W := certPieces)
    (hT.proTable.tableOK_certView htbl) hT.proTable.certTable rfl rfl hr hE hEi hEj hΓ hDi hDj
  refine ⟨reidxL (certNeg certPieces n r i j),
    ⟨(listOK_reidxL hT.proTable hok).mono (by exact_mod_cast (by decide : 8 ≤ 9)), noDrop'_reidxL hnd.noDrop',
      hornOnly_reidxL hho, by rw [shiftsV_reidxL, hs]⟩, ?_, ?_⟩
  · rw [len_reidxL]; exact le_trans le_self_add (len_certNeg_le hr)
  · rw [finalCtx_reidxL]; exact hf

/-- `eqSteps` as an `HInv` list: `eqFactB &i &j` from two dossiers of `r`. -/
theorem eqInst_ok {tbl N E Γ n r i j : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hr : IsSemiformula LAct n r) (hE : 2 * (n + formulaLen LAct r) + 12 ≤ E) (hEi : i + 2 * formulaLen LAct r + 1 ≤ E)
    (hEj : j + 2 * formulaLen LAct r + 1 ≤ E) (hDi : DossF walkPieces Γ n r i) (hDj : DossF walkPieces Γ n r j) :
    ∃ P : V, HInv tbl E Γ P ∧ len P ≤ 4 * formulaLen LAct r + 1 ∧ neg LAct (eqFactB (^&i) (^&j)) ∈ finalCtx Γ P := by
  have hW := hT.walkTable
  have hc : eqCount r ≤ 2 * formulaLen LAct r := by
    rw [eqCount_eq_descCountF walkPieces hr]; exact le_trans le_self_add (descCountF_succ_le' htbl hW hr)
  obtain ⟨hok, hnd, hho, hs, hl, hf⟩ := eqSteps_ok htbl hT.layoutTable rfl rfl hr hE
    (le_trans (add_le_add (add_le_add le_rfl hc) le_rfl) hEi) (le_trans (add_le_add (add_le_add le_rfl hc) le_rfl) hEj) hΓ
    (dossierAt_of_dossF htbl hW rfl hr hDi) (dossierAt_of_dossF htbl hW rfl hr hDj)
  refine ⟨_, ⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), hnd.noDrop', hho, hs⟩, ?_, hf⟩
  calc len (eqSteps layoutPieces i j r) ≤ 2 * eqCount r + 1 := hl
    _ ≤ 2 * (2 * formulaLen LAct r) + 1 := add_le_add (mul_le_mul_of_nonneg_left hc zero_le) le_rfl
    _ = 4 * formulaLen LAct r + 1 := by ring

/-- The `isC0Fact &iw0` step from the vector dossier of `⟨⌜0⌝⟩` at `&iw0`. -/
theorem c0Intro_ok {tbl N E Γ iw0 : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hE : iw0 + 2 ≤ E) (hD : DossV walkPieces Γ 0 1 c0v 1 iw0) :
    ∃ P : V, HInv tbl E Γ P ∧ len P ≤ 1 ∧ neg LAct (isC0Fact (^&iw0)) ∈ finalCtx Γ P := by
  have hW := hT.walkTable
  have hD' : DossV walkPieces Γ 0 1 c0v (0 + 1) iw0 := by rwa [zero_add]
  obtain ⟨hadj, _, hDt, _⟩ := dossV_succ htbl hW rfl isSemitermVec_c0v (by rw [zero_add]) hD'
  have hnth : (c0v : V).[1 - (0 + 1)] = ^func 0 0 0 := by rw [zero_add, tsub_self]; unfold c0v; exact nth_adjoin_zero _ _
  rw [hnth] at hDt hadj
  rw [vRef_zero] at hadj
  obtain ⟨hfunc, _, _, _⟩ := dossT_func htbl hW rfl (k := 0) (f := 0) (v := 0) isFunc_LAct_zeroIndex (IsSemitermVec.nil _) hDt
  rw [cTV_zero, vRef_zero] at hfunc
  obtain ⟨hlen, hrow⟩ := hT.c0Intro
  obtain ⟨hok, htag, hctx⟩ := iok_c0Intro htbl rfl hlen hrow hΓ (by simp) (termLen_fvar_le (le_trans (le_of_eq (by ring)) hE)) (by simp)
    (termLen_fvar_le (le_trans (add_le_add le_rfl (by norm_num)) hE)) hfunc hadj
  refine ⟨_, HInv.single hok htag, by rw [len_single], ?_⟩
  rw [finalCtx_single, hctx]; exact mem_insert_self'

/-- The `isC1Fact &iw1` step from the vector dossier of `⟨#0 + 1⟩` at `&iw1` (bound `1`). -/
theorem c1Intro_ok {tbl N E Γ iw1 : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hE : iw1 + 8 ≤ E) (hD : DossV walkPieces Γ 1 1 c1v 1 iw1) :
    ∃ P : V, HInv tbl E Γ P ∧ len P ≤ 1 ∧ neg LAct (isC1Fact (^&iw1)) ∈ finalCtx Γ P := by
  have hW := hT.walkTable
  have hD' : DossV walkPieces Γ 1 1 c1v (0 + 1) iw1 := by rwa [zero_add]
  obtain ⟨hadj, _, hDt, _⟩ := dossV_succ htbl hW rfl isSemitermVec_c1v (by rw [zero_add]) hD'
  have hnth : (c1v : V).[1 - (0 + 1)] = ^#(0 : V) ^+ (𝟏 : V) := by rw [zero_add, tsub_self]; unfold c1v; exact nth_adjoin_zero _ _
  rw [hnth] at hDt hadj
  rw [vRef_zero] at hadj
  have hv2 : IsSemitermVec LAct 2 1 (?[^#(0 : V), (𝟏 : V)] : V) := by
    rw [show (2 : V) = 0 + 1 + 1 by norm_num, IsSemitermVec.cons_iff, IsSemitermVec.cons_iff]
    exact ⟨by simp, isSemiterm_qqOne_LAct 1, IsSemitermVec.nil _⟩
  have hDt' : DossT walkPieces Γ 1 (^func 2 (addIndex : V) ?[^#(0 : V), (𝟏 : V)]) (iw1 + 1) := by unfold qqAdd at hDt; exact hDt
  obtain ⟨hfunc, _, _, hDv2⟩ := dossT_func htbl hW rfl isFunc_LAct_addIndex hv2 hDt'
  rw [coe_addIndex_eq, cTV_zero, cTV_two_eq, ← cT_two, vRef_of_ne (by norm_num : (2 : V) ≠ 0)] at hfunc
  -- the two entries: `#0` then `𝟏`
  have hDv2' : DossV walkPieces Γ 1 2 ?[^#(0 : V), (𝟏 : V)] (1 + 1) (iw1 + 1 + 1) := by
    rw [one_add_one_eq_two]; exact hDv2
  obtain ⟨hadj2, _, hDx, hDv1⟩ := dossV_succ htbl hW rfl hv2 (by rw [one_add_one_eq_two]) hDv2'
  have hn0 : (?[^#(0 : V), (𝟏 : V)] : V).[2 - (1 + 1)] = ^#0 := by rw [one_add_one_eq_two, tsub_self]; simp
  rw [hn0] at hDx hadj2 hDv1
  rw [vRef_of_ne _root_.one_ne_zero] at hadj2
  obtain ⟨hbvar, _⟩ := dossT_bvar htbl hW rfl hDx
  rw [cTV_zero] at hbvar
  have hDv1' : DossV walkPieces Γ 1 2 ?[^#(0 : V), (𝟏 : V)] (0 + 1) (iw1 + 1 + 1 + 1 + descCountT walkPieces 1 (^#0)) := by
    rw [zero_add]; exact hDv1
  obtain ⟨hadj1, _, hDo, _⟩ := dossV_succ htbl hW rfl hv2 (by rw [zero_add]; norm_num) hDv1'
  have hn1 : (?[^#(0 : V), (𝟏 : V)] : V).[2 - (0 + 1)] = 𝟏 := by
    rw [zero_add, show (2 : V) = 1 + 1 by norm_num, add_tsub_cancel_right]; simp
  rw [hn1] at hDo hadj1
  rw [vRef_zero] at hadj1
  have hDo' : DossT walkPieces Γ 1 (^func 0 (oneIndex : V) 0) (iw1 + 1 + 1 + 1 + descCountT walkPieces 1 (^#0) + 1) := by
    rw [← qqOne_eq]; exact hDo
  obtain ⟨hfunc1, _, _, _⟩ := dossT_func htbl hW rfl isFunc_LAct_oneIndex (IsSemitermVec.nil _) hDo'
  rw [coe_oneIndex_eq, cTV_zero, cTV_one_eq, ← cT_one, vRef_zero] at hfunc1
  rw [descCountT_bvar] at hadj2 hadj1 hfunc1
  -- the step
  have hct : iw1 + 1 + 1 + 1 + 1 + 1 + 1 ≤ E := le_trans (le_of_eq (by ring)) (le_trans (add_le_add le_rfl (by norm_num : (6 : V) ≤ 8)) hE)
  have hE1 : iw1 + 1 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hE
  have hE2 : iw1 + 1 + 1 ≤ E := le_trans (le_of_eq (by ring)) (le_trans (add_le_add le_rfl (by norm_num : (2 : V) ≤ 8)) hE)
  have hE3 : iw1 + 1 + 1 + 1 ≤ E := le_trans (le_of_eq (by ring)) (le_trans (add_le_add le_rfl (by norm_num : (3 : V) ≤ 8)) hE)
  have hE4 : iw1 + 1 + 1 + 1 + 1 ≤ E := le_trans (le_of_eq (by ring)) (le_trans (add_le_add le_rfl (by norm_num : (4 : V) ≤ 8)) hE)
  have hE5 : iw1 + 1 + 1 + 1 + 1 + 1 ≤ E := le_trans (le_of_eq (by ring)) (le_trans (add_le_add le_rfl (by norm_num : (5 : V) ≤ 8)) hE)
  obtain ⟨hlen, hrow⟩ := hT.c1Intro
  obtain ⟨hok, htag, hctx⟩ := iok_c1Intro htbl rfl hlen hrow hΓ (by simp) (termLen_fvar_le hct) (by simp) (termLen_fvar_le hE5)
    (by simp) (termLen_fvar_le hE4) (by simp) (termLen_fvar_le hE3) (by simp) (termLen_fvar_le hE2) (by simp) (termLen_fvar_le hE1)
    hfunc1 hadj1 hbvar hadj2 hfunc hadj
  refine ⟨_, HInv.single hok htag, by rw [len_single], ?_⟩
  rw [finalCtx_single, hctx]; exact mem_insert_self'

end stageB

/-! ### 5.6 Stage B: the composition -/

section stageBmain

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- One tag-`0` step at cap `9`. -/
lemma HInv.single9 {tbl E Γ s : V} (h : StepOK tbl E ((9 : ℕ) : V) Γ s) (htag : sTag s = 0) :
    HInv tbl E Γ ?[s] :=
  ⟨listOK_single h, noDrop'_single (Or.inl htag), hornOnly_single (Or.inl htag), shiftsV_single_tag0 htag⟩
lemma HInv.snoc9 {tbl E Γ P s : V} (hP : HInv tbl E Γ P) (h : StepOK tbl E ((9 : ℕ) : V) (finalCtx Γ P) s)
    (htag : sTag s = 0) : HInv tbl E Γ (appendV P ?[s]) :=
  hP.append (HInv.single9 h htag)
lemma HInv.mem_app' {tbl E Γ P L P' x : V} (hP' : P' = appendV P L) (hL : HInv tbl E (finalCtx Γ P) L)
    (hx : x ∈ finalCtx Γ P) : x ∈ finalCtx Γ P' := by subst hP'; rw [finalCtx_appendV]; exact hL.mem hx
lemma HInv.new_app' {tbl E Γ P L P' x : V} (hP' : P' = appendV P L) (_ : HInv tbl E (finalCtx Γ P) L)
    (hx : x ∈ finalCtx (finalCtx Γ P) L) : x ∈ finalCtx Γ P' := by subst hP'; rw [finalCtx_appendV]; exact hx
lemma HInv.mem_app {tbl E Γ P L x : V} (hL : HInv tbl E (finalCtx Γ P) L) (hx : x ∈ finalCtx Γ P) :
    x ∈ finalCtx Γ (appendV P L) := by rw [finalCtx_appendV]; exact hL.mem hx
lemma HInv.new_app {tbl E Γ P L x : V} (_ : HInv tbl E (finalCtx Γ P) L) (hx : x ∈ finalCtx (finalCtx Γ P) L) :
    x ∈ finalCtx Γ (appendV P L) := by rw [finalCtx_appendV]; exact hx
lemma HInv.dossF_app {tbl E Γ P L W n r i : V} (hL : HInv tbl E (finalCtx Γ P) L) (hD : DossF W (finalCtx Γ P) n r i) :
    DossF W (finalCtx Γ (appendV P L)) n r i := by rw [finalCtx_appendV]; exact hL.dossF hD
lemma HInv.dossV_app {tbl E Γ P L W n k v j i : V} (hL : HInv tbl E (finalCtx Γ P) L) (hD : DossV W (finalCtx Γ P) n k v j i) :
    DossV W (finalCtx Γ (appendV P L)) n k v j i := by rw [finalCtx_appendV]; exact hL.dossV hD

set_option maxHeartbeats 4000000 in
/-- **Stage B**: at the context of stage A, the shift-free closing: the `qqAlls` walk, the `bs` pass, the shift and
`fvSeq` certificates, `neg K`, the identification of the two copies of `K`, the four packaging rows and the
recognizer — `axchFact &ip'`. -/
theorem stageB {tbl N E Γ p ip' b m K Z js ink iw iw0 iw1 : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl)
    (hΓ : IsFormulaSet LAct Γ) (hZ : 1 ≤ Z)
    (hb : IsSemiformula ℒₒᵣ m b) (hK : IsSemiformula ℒₒᵣ 1 K) (hp : p = qqAlls b m) (hbv : Bootstrapping.bv ℒₒᵣ b = m)
    (hsh : shift LAct b = b)
    (hm : m ≤ Z) (hLb : formulaLen LAct b ≤ Z) (hLs : formulaLen LAct (indBodyVal K) ≤ Z) (hLk : formulaLen LAct K ≤ Z)
    (hip : ip' ≤ 101 * gp Z 3) (hjs : js ≤ 100 * gp Z 3) (hink : ink ≤ 100 * gp Z 3) (hiw : iw ≤ 100 * gp Z 3)
    (hiw0 : iw0 ≤ 100 * gp Z 3) (hiw1 : iw1 ≤ 100 * gp Z 3) (hE : 200 * gp Z 3 ≤ E)
    (hDp : DossF walkPieces Γ 0 p ip') (hDs : DossF walkPieces Γ 0 (indBodyVal K) js)
    (hDk : DossF walkPieces Γ 1 (neg LAct K) ink) (hDw : DossV walkPieces Γ 0 m (Bootstrapping.fvarVec m) m iw)
    (hDw0 : DossV walkPieces Γ 0 1 c0v 1 iw0) (hDw1 : DossV walkPieces Γ 1 1 c1v 1 iw1)
    (hf6 : neg LAct (substFact (^&js) (vRef iw m) (^&(ip' + m))) ∈ Γ)
    (hf7 : neg LAct (substFact (^&(js + descCountF walkPieces 0 (yK K) + 1)) (^&iw0) (^&ink)) ∈ Γ)
    (hf8 : neg LAct (substFact (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + 1)) (^&iw1) (^&ink)) ∈ Γ) :
    ∃ P : V, HInv tbl E Γ P ∧ len P ≤ 100 * gp Z 3 ∧ neg LAct (axchFact (^&ip')) ∈ finalCtx Γ P := by
  have hW := hT.walkTable
  have hbL := IsSemiformula.LAct_of_LOR hb
  have hKL := IsSemiformula.LAct_of_LOR hK
  have hnkL := nkL_of hK
  have hLnk : formulaLen LAct (neg LAct K) = formulaLen LAct K := formulaLen_neg hKL.isUFormula
  obtain ⟨hLx, hLy, hLz, hLns, hLK⟩ := formulaLen_pieces_le hK
  -- the atoms
  have hZ1 : (1 : V) ≤ 1 * gp Z 1 := by rw [one_mul]; exact one_le_gp hZ 1
  have hm' := atom_gp_le hm
  have hLb' := atom_gp_le hLb
  have hLk' := atom_gp_le hLk
  have hcy : descCountF walkPieces 0 (yK K) ≤ 2 * gp Z 1 := by
    have := descCountF_succ_le' htbl hW (yK_isSemiformula hK)
    exact gp_final hZ (le_trans (le_trans le_self_add this) (cmul_gp_le 2 (atom_gp_le (le_trans hLy hLs)))) le_rfl (by norm_num)
  have hcz : descCountF walkPieces 0 (zK K) ≤ 2 * gp Z 1 := by
    have := descCountF_succ_le' htbl hW (zK_isSemiformula hK)
    exact gp_final hZ (le_trans (le_trans le_self_add this) (cmul_gp_le 2 (atom_gp_le (le_trans hLz hLs)))) le_rfl (by norm_num)
  have hcns : descCountF walkPieces 1 (nsK K) ≤ 2 * gp Z 1 := by
    have := descCountF_succ_le' htbl hW (nsK_isSemiformula hK)
    exact gp_final hZ (le_trans (le_trans le_self_add this) (cmul_gp_le 2 (atom_gp_le (le_trans hLns hLs)))) le_rfl (by norm_num)
  have hbig : ∀ (x : V) (c : V), x ≤ c * gp Z 3 → c ≤ 150 → x + 1 ≤ E := fun x c hx hc ↦
    le_trans (gp_final hZ (add_gp_le hZ hx (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by
      exact le_trans (add_le_add hc le_rfl) (by norm_num : (150 : V) + 1 ≤ 200))) hE
  have hE8 : (8 : V) ≤ E := le_trans (gp_final hZ (const_gp_le (8 : V) hZ 3) le_rfl (by norm_num)) hE
  -- the offsets inside `s`
  obtain ⟨hor1, hor2, hexs, hand, hall, _, _, hDK1, hDK2⟩ := bodyDoss htbl hW hK hDs
  have hix : js + descCountF walkPieces 0 (yK K) + 1 ≤ 104 * gp Z 3 :=
    gp_final hZ (add_gp_le hZ (add_gp_le hZ hjs hcy le_rfl (by norm_num)) (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)
  have hiu : js + 1 + descCountF walkPieces 0 (zK K) + 1 ≤ 105 * gp Z 3 :=
    gp_final hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ hjs (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) hcz le_rfl (by norm_num))
      (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)
  have hin1 : js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 ≤ 106 * gp Z 3 :=
    gp_final hZ (add_gp_le hZ hiu (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)
  have hins : js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + 1 ≤ 107 * gp Z 3 :=
    gp_final hZ (add_gp_le hZ hin1 (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)
  have hiK1 : js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + descCountF walkPieces 1 (nsK K) + 1 ≤ 110 * gp Z 3 :=
    gp_final hZ (add_gp_le hZ (add_gp_le hZ hin1 hcns le_rfl (by norm_num)) (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)
  have hiK2 : js + 1 + 1 + 1 ≤ 103 * gp Z 3 :=
    gp_final hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ hjs (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) (const_gp_le (1 : V) hZ 3) le_rfl le_rfl)
      (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)
  have hiy : js + 1 ≤ 101 * gp Z 3 := gp_final hZ (add_gp_le hZ hjs (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)
  have hiz : js + 1 + 1 ≤ 102 * gp Z 3 := gp_final hZ (add_gp_le hZ hiy (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)
  have hib : ip' + m ≤ 102 * gp Z 3 := gp_final hZ (add_gp_le hZ hip hm' le_rfl (by norm_num)) le_rfl (by norm_num)
  have hEm : termLen LAct (cTV m) ≤ E := cTV_cap le_rfl (hbig _ _ (gp_final hZ (cmul_gp_le 2 hm') (by norm_num) le_rfl) (by norm_num))
  -- B1. the `qqAlls` walk
  have hDp' : DossF walkPieces Γ 0 (qqAlls b m) ip' := by rw [← hp]; exact hDp
  obtain ⟨L1, hL1, hl1, hf1⟩ := qqAllsWalk_ok htbl hT hΓ hbL hDp'
    (hbig _ _ (gp_final hZ (cmul_gp_le 2 hm') (by norm_num) le_rfl) (by norm_num)) (hbig _ _ hib (by norm_num))
  obtain ⟨P₁, hP₁⟩ : ∃ P', P' = L1 := ⟨_, rfl⟩
  rw [← hP₁] at hL1 hl1 hf1
  have hΓ₁ := hL1.isFormulaSet htbl hΓ
  -- B2. the `bs` pass on `b`
  have hDb₁ : DossF walkPieces (finalCtx Γ P₁) m b (ip' + m) := by
    have := dossF_qqAlls htbl hW rfl hbL (hL1.dossF hDp') m le_rfl 0 (zero_add m)
    rwa [qqAlls_zero] at this
  have hBi : ip' + m + 2 * formulaLen LAct b ≤ 104 * gp Z 3 :=
    gp_final hZ (add_gp_le hZ hib (cmul_gp_le 2 hLb') le_rfl (by norm_num)) le_rfl (by norm_num)
  obtain ⟨L2, hL2, hl2, hf2⟩ := bsF_ok (B := m + formulaLen LAct b) (Bi := ip' + m + 2 * formulaLen LAct b) htbl hT hΓ₁
    (hbig _ _ (gp_final hZ (cmul_gp_le 2 (add_gp_le hZ hm' hLb' le_rfl le_rfl)) (by norm_num) le_rfl) (by norm_num)) (hbig _ _ hBi (by norm_num)) hE8 hb
    (ip' + m) le_self_add le_rfl le_rfl hDb₁
  rw [hbv] at hf2
  obtain ⟨P₂, hP₂⟩ : ∃ P', P' = appendV P₁ L2 := ⟨_, rfl⟩
  have hP₂i : HInv tbl E Γ P₂ := by rw [hP₂]; exact hL1.append hL2
  have hf2' : neg LAct (bsFFact (cTV m) (cTV m) (^&(ip' + m))) ∈ finalCtx Γ P₂ := by rw [hP₂]; exact hL2.new_app hf2
  have hf1' : neg LAct (allsFact (^&ip') (^&(ip' + m)) (cTV m)) ∈ finalCtx Γ P₂ := by rw [hP₂]; exact hL2.mem_app hf1
  have hΓ₂ := hP₂i.isFormulaSet htbl hΓ
  -- B3. `shift b = b`
  have hDb₂ : DossF walkPieces (finalCtx Γ P₂) m b (ip' + m) := by
    rw [hP₂, finalCtx_appendV]; exact hL2.dossF hDb₁
  obtain ⟨L3, hL3, hl3, hf3⟩ := shiftSelf_ok htbl hT hΓ₂ hbL hsh hDb₂
    (le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ (cmul_gp_le 2 hm') (cmul_gp_le 2 hLb') le_rfl le_rfl)
      (const_gp_le (8 : V) hZ 1) le_rfl le_rfl) (by norm_num) (by norm_num)) hE) (hbig _ _ hBi (by norm_num))
  obtain ⟨P₃, hP₃⟩ : ∃ P', P' = appendV P₂ L3 := ⟨_, rfl⟩
  have hP₃i : HInv tbl E Γ P₃ := by rw [hP₃]; exact hP₂i.append hL3
  have hf3' : neg LAct (shiftFact (^&(ip' + m)) (^&(ip' + m))) ∈ finalCtx Γ P₃ := by rw [hP₃]; exact hL3.new_app hf3
  have hf2'' := show neg LAct (bsFFact (cTV m) (cTV m) (^&(ip' + m))) ∈ finalCtx Γ P₃ by rw [hP₃]; exact hL3.mem_app hf2'
  have hf1'' := show neg LAct (allsFact (^&ip') (^&(ip' + m)) (cTV m)) ∈ finalCtx Γ P₃ by rw [hP₃]; exact hL3.mem_app hf1'
  have hΓ₃ := hP₃i.isFormulaSet htbl hΓ
  -- B4. `fvSeq`
  have hDw₃ : DossV walkPieces (finalCtx Γ P₃) 0 m (Bootstrapping.fvarVec m) m iw := hP₃i.dossV hDw
  have hmm : m * (m + 1) ≤ 2 * gp Z 2 := gp_final hZ (mul_gp_le hm' (add_gp_le hZ hm' hZ1 le_rfl le_rfl)) le_rfl (by norm_num)
  have htk : takeLast (Bootstrapping.fvarVec m) m = Bootstrapping.fvarVec m := by
    have := takeLast_len_self (Bootstrapping.fvarVec m); rwa [Bootstrapping.len_fvarVec] at this
  have hBi' : iw + 2 * (m * (m + 1)) + 1 ≤ 105 * gp Z 3 :=
    gp_final hZ (add_gp_le hZ (add_gp_le hZ hiw (cmul_gp_le 2 hmm) le_rfl (by norm_num)) (const_gp_le (1 : V) hZ 3) le_rfl le_rfl)
      le_rfl (by norm_num)
  obtain ⟨L4, hL4, hl4, hf4⟩ := fvSeq_ok (Bi := iw + 2 * (m * (m + 1)) + 1) htbl hT hΓ₃
    (hbig _ _ (gp_final hZ (cmul_gp_le 2 hm') (by norm_num) le_rfl) (by norm_num)) (hbig _ _ hBi' (by norm_num)) m le_rfl 0 zero_le (zero_add m) iw
    (le_trans le_self_add (le_trans le_self_add le_rfl))
    (by rw [htk]; exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left (listSum_termLenVec_fvarVec_le m) zero_le)) le_rfl) hDw₃
  rw [cTV_zero] at hf4
  obtain ⟨P₄, hP₄⟩ : ∃ P', P' = appendV P₃ L4 := ⟨_, rfl⟩
  have hP₄i : HInv tbl E Γ P₄ := by rw [hP₄]; exact hP₃i.append hL4
  have hΓ₄ := hP₄i.isFormulaSet htbl hΓ
  -- B5. `neg K`
  have hDK1₄ : DossF walkPieces (finalCtx Γ P₄) 1 K _ := hP₄i.dossF hDK1
  have hDk₄ : DossF walkPieces (finalCtx Γ P₄) 1 (neg LAct K) ink := hP₄i.dossF hDk
  have hEk1 : 2 * 1 + 2 * formulaLen LAct K + 8 ≤ E :=
    le_trans (gp_final hZ (add_gp_le hZ (add_gp_le hZ (const_gp_le (2 * 1 : V) hZ 1) (cmul_gp_le 2 hLk') le_rfl le_rfl)
      (const_gp_le (8 : V) hZ 1) le_rfl le_rfl) (by norm_num) (by norm_num)) hE
  obtain ⟨L5, hL5, hl5, hf5⟩ := negInst_ok htbl hT hΓ₄ hKL hEk1
    (hbig _ _ (gp_final hZ (add_gp_le hZ hiK1 (cmul_gp_le 2 hLk') le_rfl (by norm_num)) le_rfl le_rfl) (by norm_num))
    (hbig _ _ (gp_final hZ (add_gp_le hZ hink (cmul_gp_le 2 hLk') le_rfl (by norm_num)) le_rfl le_rfl) (by norm_num)) hDK1₄ hDk₄
  obtain ⟨P₅, hP₅⟩ : ∃ P', P' = appendV P₄ L5 := ⟨_, rfl⟩
  have hP₅i : HInv tbl E Γ P₅ := by rw [hP₅]; exact hP₄i.append hL5
  have hΓ₅ := hP₅i.isFormulaSet htbl hΓ
  -- B6. the identification of the two copies of `K`
  have hDK1₅ : DossF walkPieces (finalCtx Γ P₅) 1 K _ := hP₅i.dossF hDK1
  have hDK2₅ : DossF walkPieces (finalCtx Γ P₅) 1 K _ := hP₅i.dossF hDK2
  obtain ⟨L6, hL6, hl6, hf6'⟩ := eqInst_ok htbl hT hΓ₅ hKL
    (le_trans (gp_final hZ (add_gp_le hZ (cmul_gp_le 2 (add_gp_le hZ hZ1 hLk' le_rfl le_rfl)) (const_gp_le (12 : V) hZ 1) le_rfl le_rfl)
      (by norm_num) (by norm_num)) hE)
    (hbig _ _ (gp_final hZ (add_gp_le hZ hiK2 (cmul_gp_le 2 hLk') le_rfl (by norm_num)) le_rfl le_rfl) (by norm_num))
    (hbig _ _ (gp_final hZ (add_gp_le hZ hiK1 (cmul_gp_le 2 hLk') le_rfl (by norm_num)) le_rfl le_rfl) (by norm_num)) hDK2₅ hDK1₅
  obtain ⟨P₆, hP₆⟩ : ∃ P', P' = appendV P₅ L6 := ⟨_, rfl⟩
  have hP₆i : HInv tbl E Γ P₆ := by rw [hP₆]; exact hP₅i.append hL6
  have hΓ₆ := hP₆i.isFormulaSet htbl hΓ
  -- B7, B8. the constant vectors
  obtain ⟨L7, hL7, hl7, hf7'⟩ := c0Intro_ok htbl hT hΓ₆ (le_trans (le_of_eq (by ring)) (hbig _ _ (gp_final hZ (add_gp_le hZ hiw0 (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl le_rfl) (by norm_num))) (hP₆i.dossV hDw0)
  obtain ⟨P₇, hP₇⟩ : ∃ P', P' = appendV P₆ L7 := ⟨_, rfl⟩
  have hP₇i : HInv tbl E Γ P₇ := by rw [hP₇]; exact hP₆i.append hL7
  have hΓ₇ := hP₇i.isFormulaSet htbl hΓ
  obtain ⟨L8, hL8, hl8, hf8'⟩ := c1Intro_ok htbl hT hΓ₇ (le_trans (le_of_eq (by ring)) (hbig _ _ (gp_final hZ (add_gp_le hZ hiw1 (const_gp_le (7 : V) hZ 3) le_rfl le_rfl) le_rfl le_rfl) (by norm_num))) (hP₇i.dossV hDw1)
  obtain ⟨P₈, hP₈⟩ : ∃ P', P' = appendV P₇ L8 := ⟨_, rfl⟩
  have hP₈i : HInv tbl E Γ P₈ := by rw [hP₈]; exact hP₇i.append hL8
  have hΓ₈ := hP₈i.isFormulaSet htbl hΓ
  -- all the facts at `P₈`
  have mem₈ : ∀ x : V, x ∈ Γ → x ∈ finalCtx Γ P₈ := fun x hx ↦ hP₈i.mem hx
  have mem₈₃ : ∀ x : V, x ∈ finalCtx Γ P₃ → x ∈ finalCtx Γ P₈ := fun x hx ↦
    hL8.mem_app' hP₈ (hL7.mem_app' hP₇ (hL6.mem_app' hP₆ (hL5.mem_app' hP₅ (hL4.mem_app' hP₄ hx))))
  have g1 := mem₈₃ _ hf1''
  have g2 := mem₈₃ _ hf2''
  have g3 := mem₈₃ _ hf3'
  have g4 : neg LAct (fvSeqFact (vRef iw m) (𝟎 : V) (cTV m)) ∈ finalCtx Γ P₈ := by
    exact hL8.mem_app' hP₈ (hL7.mem_app' hP₇ (hL6.mem_app' hP₆ (hL5.mem_app' hP₅ (hL4.new_app' hP₄ hf4))))
  have g5 : neg LAct (negFact (^&ink) (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + descCountF walkPieces 1 (nsK K) + 1))) ∈
      finalCtx Γ P₈ := by
    exact hL8.mem_app' hP₈ (hL7.mem_app' hP₇ (hL6.mem_app' hP₆ (hL5.new_app' hP₅ hf5)))
  have g6 : neg LAct (eqFactB (^&(js + 1 + 1 + 1)) (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + descCountF walkPieces 1 (nsK K) + 1))) ∈
      finalCtx Γ P₈ := by
    exact hL8.mem_app' hP₈ (hL7.mem_app' hP₇ (hL6.new_app' hP₆ hf6'))
  have g7 : neg LAct (isC0Fact (^&iw0)) ∈ finalCtx Γ P₈ := hL8.mem_app' hP₈ (hL7.new_app' hP₇ hf7')
  have g8 : neg LAct (isC1Fact (^&iw1)) ∈ finalCtx Γ P₈ := hL8.new_app' hP₈ hf8'
  -- the witnesses' caps
  have cJs : termLen LAct (^&js : V) ≤ E := termLen_fvar_le (hbig _ _ (gp_final hZ hjs le_rfl le_rfl) (by norm_num))
  have cIx : termLen LAct (^&(js + descCountF walkPieces 0 (yK K) + 1) : V) ≤ E := termLen_fvar_le (hbig _ _ (gp_final hZ hix le_rfl le_rfl) (by norm_num))
  have cIy : termLen LAct (^&(js + 1) : V) ≤ E := termLen_fvar_le (hbig _ _ (gp_final hZ hiy le_rfl le_rfl) (by norm_num))
  have cIu : termLen LAct (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1) : V) ≤ E := termLen_fvar_le (hbig _ _ (gp_final hZ hiu le_rfl le_rfl) (by norm_num))
  have cIz : termLen LAct (^&(js + 1 + 1) : V) ≤ E := termLen_fvar_le (hbig _ _ (gp_final hZ hiz le_rfl le_rfl) (by norm_num))
  have cIn1 : termLen LAct (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1) : V) ≤ E := termLen_fvar_le (hbig _ _ (gp_final hZ hin1 le_rfl le_rfl) (by norm_num))
  have cIK1 : termLen LAct (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + descCountF walkPieces 1 (nsK K) + 1) : V) ≤ E :=
    termLen_fvar_le (hbig _ _ (gp_final hZ hiK1 le_rfl le_rfl) (by norm_num))
  have cIns : termLen LAct (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + 1) : V) ≤ E := termLen_fvar_le (hbig _ _ (gp_final hZ hins le_rfl le_rfl) (by norm_num))
  have cIK2 : termLen LAct (^&(js + 1 + 1 + 1) : V) ≤ E := termLen_fvar_le (hbig _ _ (gp_final hZ hiK2 le_rfl le_rfl) (by norm_num))
  have cInk : termLen LAct (^&ink : V) ≤ E := termLen_fvar_le (hbig _ _ (gp_final hZ hink le_rfl le_rfl) (by norm_num))
  have cIw0 : termLen LAct (^&iw0 : V) ≤ E := termLen_fvar_le (hbig _ _ (gp_final hZ hiw0 le_rfl le_rfl) (by norm_num))
  have cIw1 : termLen LAct (^&iw1 : V) ≤ E := termLen_fvar_le (hbig _ _ (gp_final hZ hiw1 le_rfl le_rfl) (by norm_num))
  have cIw : termLen LAct (vRef iw m) ≤ E := termLen_vRef_le (hbig _ _ (gp_final hZ hiw le_rfl le_rfl) (by norm_num))
  have cIp : termLen LAct (^&ip' : V) ≤ E := termLen_fvar_le (hbig _ _ (gp_final hZ hip le_rfl le_rfl) (by norm_num))
  have cIb : termLen LAct (^&(ip' + m) : V) ≤ E := termLen_fvar_le (hbig _ _ (gp_final hZ hib le_rfl le_rfl) (by norm_num))
  -- B9. `bodyIntro`
  obtain ⟨hlen9, hrow9⟩ := hT.bodyIntro
  obtain ⟨hok9, htag9, hctx9⟩ := iok_bodyIntro htbl rfl hlen9 hrow9 hΓ₈ (by simp) cIK2 (by simp) cIns (by simp) cIK1 (by simp) cIn1
    (by simp) cIz (by simp) cIu (by simp) cIy (by simp) cIx (by simp) cJs
    (mem₈ _ hor1) (mem₈ _ hor2) (mem₈ _ hexs) (mem₈ _ hand) (mem₈ _ hall) g6
  obtain ⟨P₉, hP₉⟩ : ∃ P', P' = appendV P₈ ?[mkStep indRecPieces ((iIdx_bodyIntro : ℕ) : V)
    ?[^&(js + 1 + 1 + 1), ^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + 1),
      ^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + descCountF walkPieces 1 (nsK K) + 1),
      ^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1), ^&(js + 1 + 1), ^&(js + 1 + descCountF walkPieces 0 (zK K) + 1),
      ^&(js + 1), ^&(js + descCountF walkPieces 0 (yK K) + 1), ^&js]] := ⟨_, rfl⟩
  have hP₉i : HInv tbl E Γ P₉ := by rw [hP₉]; exact hP₈i.snoc9 hok9 htag9
  have hΓ₉ := hP₉i.isFormulaSet htbl hΓ
  have g9 : neg LAct (bodyShapeFact (^&js) (^&(js + descCountF walkPieces 0 (yK K) + 1))
      (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + 1))
      (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + descCountF walkPieces 1 (nsK K) + 1))) ∈ finalCtx Γ P₉ := by
    rw [hP₉, finalCtx_appendV_single, hctx9]; exact mem_insert_self'
  have mem₉ : ∀ x : V, x ∈ finalCtx Γ P₈ → x ∈ finalCtx Γ P₉ := fun x hx ↦ by
    rw [hP₉, finalCtx_appendV_single, hctx9]; exact mem_insert_of_mem' hx
  -- B10. `indBodyIntroL`
  obtain ⟨hlen10, hrow10⟩ := hT.indBodyIntroL
  obtain ⟨hok10, htag10, hctx10⟩ := iok_indBodyIntroL htbl rfl hlen10 hrow10 hΓ₉ (by simp) cIw1 (by simp) cIw0 (by simp) cInk
    (by simp) cIns (by simp) cIx (by simp) cIK1 (by simp) cJs g9 (mem₉ _ g5) (mem₉ _ g7) (mem₉ _ (mem₈ _ hf7)) (mem₉ _ g8) (mem₉ _ (mem₈ _ hf8))
  obtain ⟨P₁₀, hP₁₀⟩ : ∃ P', P' = appendV P₉ ?[mkStep indRecPieces ((iIdx_indBodyIntroL : ℕ) : V)
    ?[^&iw1, ^&iw0, ^&ink, ^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + 1), ^&(js + descCountF walkPieces 0 (yK K) + 1),
      ^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + descCountF walkPieces 1 (nsK K) + 1), ^&js]] := ⟨_, rfl⟩
  have hP₁₀i : HInv tbl E Γ P₁₀ := by rw [hP₁₀]; exact hP₉i.snoc hok10 htag10
  have hΓ₁₀ := hP₁₀i.isFormulaSet htbl hΓ
  have g10 : neg LAct (indBodyLFact (^&js) (^&(js + 1 + descCountF walkPieces 0 (zK K) + 1 + 1 + descCountF walkPieces 1 (nsK K) + 1))) ∈
      finalCtx Γ P₁₀ := by
    rw [hP₁₀, finalCtx_appendV_single, hctx10]; exact mem_insert_self'
  have mem₁₀ : ∀ x : V, x ∈ finalCtx Γ P₉ → x ∈ finalCtx Γ P₁₀ := fun x hx ↦ by
    rw [hP₁₀, finalCtx_appendV_single, hctx10]; exact mem_insert_of_mem' hx
  -- B11. `indRecL`
  obtain ⟨hlen11, hrow11⟩ := hT.indRecL
  obtain ⟨hok11, htag11, hctx11⟩ := iok_indRecL htbl rfl hlen11 hrow11 hΓ₁₀ (by simp) cIp (cTV_semiterm_LAct 0 m) hEm (by simp) cIb
    (isSemiterm_vRef _ _) cIw (by simp) cJs (by simp) cIK1
    (mem₁₀ _ (mem₉ _ g1)) (mem₁₀ _ (mem₉ _ g2)) (mem₁₀ _ (mem₉ _ g3)) (mem₁₀ _ (mem₉ _ g4)) (mem₁₀ _ (mem₉ _ (mem₈ _ hf6))) g10
  refine ⟨_, hP₁₀i.snoc hok11 htag11, ?_, ?_⟩
  · -- the length
    have hl : len P₈ ≤ 60 * gp Z 3 := by
      rw [hP₈, hP₇, hP₆, hP₅, hP₄, hP₃, hP₂]
      rw [len_appendV, len_appendV, len_appendV, len_appendV, len_appendV, len_appendV, len_appendV]
      have hB3 : m + formulaLen LAct b + 3 ≤ 5 * gp Z 1 :=
        gp_final hZ (add_gp_le hZ (add_gp_le hZ hm' hLb' le_rfl le_rfl) (const_gp_le (3 : V) hZ 1) le_rfl le_rfl) le_rfl (by norm_num)
      have hl2' : len L2 ≤ 20 * gp Z 3 :=
        le_trans hl2 (gp_final hZ (mul_gp_le (mul_gp_le (cmul_gp_le 4 hLb') hLb') hB3) le_rfl (by norm_num))
      have hl1' : len P₁ ≤ 2 * gp Z 1 := le_trans hl1 (gp_final hZ (add_gp_le hZ hm' hZ1 le_rfl le_rfl) le_rfl (by norm_num))
      have hl3' : len L3 ≤ 12 * gp Z 1 := le_trans hl3 (gp_final hZ (cmul_gp_le 12 hLb') le_rfl (by norm_num))
      have hl4' : len L4 ≤ 2 * gp Z 1 := le_trans hl4 (gp_final hZ (add_gp_le hZ hm' hZ1 le_rfl le_rfl) le_rfl (by norm_num))
      have hl5' : len L5 ≤ 12 * gp Z 1 := le_trans hl5 (gp_final hZ (cmul_gp_le 12 hLk') le_rfl (by norm_num))
      have hl6' : len L6 ≤ 5 * gp Z 1 := le_trans hl6 (gp_final hZ (add_gp_le hZ (cmul_gp_le 4 hLk') hZ1 le_rfl le_rfl) le_rfl (by norm_num))
      have hl7' : len L7 ≤ 1 * gp Z 1 := le_trans hl7 (const_gp_le 1 hZ 1)
      have hl8' : len L8 ≤ 1 * gp Z 1 := le_trans hl8 (const_gp_le 1 hZ 1)
      exact gp_final hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ hl1' hl2'
        (by norm_num) le_rfl) hl3' le_rfl (by norm_num)) hl4' le_rfl (by norm_num)) hl5' le_rfl (by norm_num)) hl6' le_rfl (by norm_num))
        hl7' le_rfl (by norm_num)) hl8' le_rfl (by norm_num)) le_rfl (by norm_num)
    rw [len_appendV, len_single, hP₁₀, len_appendV, len_single, hP₉, len_appendV, len_single]
    exact gp_final hZ (add_gp_le hZ (add_gp_le hZ (add_gp_le hZ hl (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) (const_gp_le (1 : V) hZ 3) le_rfl le_rfl)
      (const_gp_le (1 : V) hZ 3) le_rfl le_rfl) le_rfl (by norm_num)
  · rw [finalCtx_appendV_single, hctx11]; exact mem_insert_self'

end stageBmain

/-! ## 6. The producer: `axmInd_ok`, and the honest oracle `AxmIndOracle'` -/

section producer

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option maxHeartbeats 1000000 in
/-- **The per-model producer** (task item 5, the honest variant): from the dossier of `p` at `ip` — `p` an
induction instance in the sense of `InductionR (fun _ ↦ True)`, possibly NONSTANDARD — one list `P`, applicable at
cap `9`, `NoDrop'`, Horn-only (so `SizeOK` for free), WITH eigenvariables (`shiftsV P ≤ 100 Z³`), of length
`≤ 4100 Z⁵`, leaving `axchFact &(ip + shiftsV P)` — the fact at `p`'s MOVED offset. `Z` bounds `ip` and
`|p|(|p| + 1)`; `E ≥ 200 Z³`. -/
theorem axmInd_ok {tbl N E Γ p ip Z : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hΓ : IsFormulaSet LAct Γ)
    (hZ : 1 ≤ Z) (hI : InductionR (fun _ ↦ True) p)
    (hip : ip ≤ Z) (hpZ : formulaLen LAct p * (formulaLen LAct p + 1) ≤ Z) (hE : 200 * gp Z 3 ≤ E)
    (hD : DossF walkPieces Γ 0 p ip) :
    ∃ P : V, ListOK tbl E ((9 : ℕ) : V) Γ P ∧ NoDrop' P ∧ HornOnly P ∧ shiftsV P ≤ 100 * gp Z 3 ∧
      len P ≤ 4100 * gp Z 5 ∧ neg LAct (axchFact (^&(ip + shiftsV P))) ∈ finalCtx Γ P := by
  obtain ⟨m, _, b, _, hp, hub, hsh, hbv, K, _, hK, _, hs⟩ := hI
  have hbO : IsSemiformula ℒₒᵣ m b := ⟨hub, le_of_eq hbv⟩
  have hbL := IsSemiformula.LAct_of_LOR hbO
  have hshL : shift LAct b = b := by rw [shift_LAct_eq hub]; exact hsh
  have hw : IsSemitermVec LAct m 0 (Bootstrapping.fvarVec m) :=
    IsSemitermVec.LAct_of_LOR (fvarVec_isSemitermVec_LOR m)
  have hsL : subst LAct (Bootstrapping.fvarVec m) b = indBodyVal K := by
    rw [subst_LAct_eq hub (fvarVec_isSemitermVec_LOR m).isUTermVec]; exact hs
  -- sizes
  have hLp : formulaLen LAct p = formulaLen LAct b + m := by rw [hp]; exact formulaLen_qqAlls hbL.isUFormula m
  have hpp : formulaLen LAct p ≤ formulaLen LAct p * (formulaLen LAct p + 1) :=
    le_trans (le_add_self : formulaLen LAct p ≤ formulaLen LAct p * formulaLen LAct p + formulaLen LAct p) (le_of_eq (by ring))
  have hpZ' : formulaLen LAct p ≤ Z := le_trans hpp hpZ
  have hLb : formulaLen LAct b ≤ Z := le_trans (le_trans le_self_add (le_of_eq hLp.symm)) hpZ'
  have hm : m ≤ Z := le_trans (le_trans le_add_self (le_of_eq hLp.symm)) hpZ'
  have hLs : formulaLen LAct (indBodyVal K) ≤ Z := by
    rw [← hsL]
    refine le_trans (formulaLen_subst_le (B := m + 1) le_add_self hbL 0 _ hw (substInv_fvarVec m)) (le_trans ?_ hpZ)
    exact mul_le_mul (le_trans le_self_add (le_of_eq hLp.symm)) (add_le_add (le_trans le_add_self (le_of_eq hLp.symm)) le_rfl)
      zero_le zero_le
  have hLk : formulaLen LAct K ≤ Z := le_trans (formulaLen_pieces_le hK).2.2.2.2 hLs
  -- stage A
  obtain ⟨L, σ, js, ink, iw, iw0, iw1, hL, hσ, hlen, hjs, hink, hiw, hiw0, hiw1, hDp, hDs, hDk, hDw, hDw0, hDw1, hf6, hf7, hf8⟩ :=
    stageA htbl hT hΓ hZ hbL hK hp hsL hip hm hLb hLs hLk hE hD
  -- stage B
  have hip' : ip + σ ≤ 101 * gp Z 3 :=
    gp_final hZ (add_gp_le hZ (atom_gp_le hip) hσ (by norm_num) le_rfl) le_rfl (by norm_num)
  obtain ⟨P, hP, hlP, hfact⟩ := stageB htbl hT (hL.isFormulaSet htbl hΓ) hZ hbO hK hp hbv hshL hm hLb hLs hLk hip'
    (le_trans hjs hσ) (le_trans hink hσ) (le_trans hiw hσ) (le_trans hiw0 hσ) (le_trans hiw1 hσ) hE
    hDp hDs hDk hDw hDw0 hDw1 hf6 hf7 hf8
  have hLP : WInv tbl E Γ (appendV L P) (σ + 0) := hL.append hP.winv
  have hsh' : shiftsV (appendV L P) = σ := by rw [hLP.2.2.2, add_zero]
  refine ⟨appendV L P, hLP.1, hLP.2.1, hLP.2.2.1, by rw [hsh']; exact hσ, ?_, ?_⟩
  · rw [len_appendV]
    exact gp_final hZ (add_gp_le hZ hlen hlP le_rfl (by norm_num)) le_rfl (by norm_num)
  · rw [hsh', finalCtx_appendV]; exact hfact

/-- **The honest oracle** (`ProAxm.AxmIndOracle` with eigenvariables): for every induction-instance member `p` of
`s`, a cap-`9`, `NoDrop'`, Horn-only list with `shiftsV P ≤ C`, `len P ≤ C`, `SizeOK C C P`, leaving
`axchFact &(memTop s p i + shiftsV P)` — the fact at the MOVED offset of `p`'s dossier. `C : V` (the bound is a
polynomial in the sequent bound `D` and `i`, hence nonstandard when they are). -/
def AxmIndOracle' (tbl E Wc T Γ s i C : V) : Prop :=
  ∀ p ∈ s, IsSemiformula ℒₒᵣ 0 p → InductionR (fun _ ↦ True) p →
    ∃ P : V, ListOK tbl E ((9 : ℕ) : V) Γ P ∧ NoDrop' P ∧ HornOnly P ∧ shiftsV P ≤ C ∧ len P ≤ C ∧
      SizeOK C C P ∧ neg LAct (axchFact (^&(memTop walkPieces Wc T s p i + shiftsV P))) ∈ finalCtx Γ P

/-- **`AxmIndOracle'` is DISCHARGED**: at the layout of `s` at `i` with `setLen s ≤ D`, with `Z := i + 6D + 1 + D(D+1)`
and `E ≥ 200 Z³`, the honest oracle holds with `C = 4100 Z⁵`. -/
theorem axmIndOracle_of {tbl N Wc T s D E Γ i : V} (htbl : TableOK tbl N) (hT : IndRecTable tbl) (hWc : Wc = certPieces)
    (hs : IsFormulaSet LAct s) (hsD : setLen LAct s ≤ D) (hΓ : IsFormulaSet LAct Γ)
    (hLay : Layout walkPieces Wc T Γ s i) (hE : 200 * gp (i + 6 * D + 1 + D * (D + 1)) 3 ≤ E) :
    AxmIndOracle' tbl E Wc T Γ s i (4100 * gp (i + 6 * D + 1 + D * (D + 1)) 5) := by
  intro p hp _ hI
  have hZ : (1 : V) ≤ i + 6 * D + 1 + D * (D + 1) := le_trans le_add_self le_self_add
  have hip : memTop walkPieces Wc T s p i ≤ i + 6 * D + 1 + D * (D + 1) :=
    le_trans (memTop_le htbl hT.walkTable hWc T hs hp hsD) le_self_add
  have hpD : formulaLen LAct p ≤ D := le_trans (formulaLen_le_setLen_of_mem hp) hsD
  have hpZ : formulaLen LAct p * (formulaLen LAct p + 1) ≤ i + 6 * D + 1 + D * (D + 1) :=
    le_trans (mul_le_mul hpD (add_le_add hpD le_rfl) zero_le zero_le) le_add_self
  obtain ⟨P, h1, h2, h3, h4, h5, h6⟩ := axmInd_ok htbl hT hΓ hZ hI hip hpZ hE (hLay.member hp).1
  exact ⟨P, h1, h2, h3, le_trans h4 (gp_final hZ le_rfl (by norm_num) (by norm_num)), h5, sizeOK_of_hornOnly h3, h6⟩

end producer

end ArithS
