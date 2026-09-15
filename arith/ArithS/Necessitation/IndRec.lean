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

end ArithS
