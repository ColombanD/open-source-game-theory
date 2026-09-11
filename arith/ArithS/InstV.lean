import ArithS.CutV
import ArithS.Bnum

/-!
# ArithS.InstV — the `bnum`-instance operator, the parametric box, and Quantifier Distribution on codes

M4 items U1 and U3 of `Research/Notes/M4_BOUNDED_HBL/BRIEF.md` §3, V-generic (every model of
`IΣ₁`), on Foundation's formula/derivation CODES.

* **U1.** `instB n k := subst LAct (bnum k ∷ 0) n` — the formula code `n` (one free variable
  `#0`) with the BINARY numeral of `k` substituted (Foundation's `substs1 LAct (bnum k) n`);
  its Σ₁ graph `instBGraph`, the `IsSemiformula` transport `isSemiformula_instB`, and the meta
  code equation `quote_instB : instB ⌜φ⌝ k = ⌜φ ⇜ ![lMap emb (bnumT k)]⌝` (the `quote_trAt`
  route of `ArithS.Code`), and the LENGTH bound `formulaLen_instB_le : |instB n k| ≤ |n| · |bnum k|`
  (from `formulaLen_subst_le`, `|p[w]| ≤ |p| · B` for vectors whose entries are identity
  variables or closed terms of length `≤ B` — the invariant `SubstInv`, preserved by `qVec`
  because the bound shift fixes closed terms, `termBShift_eq_self_of_closed`; a Π₁ structural
  induction on formula codes over a Π₁ induction on term codes and a vector induction for
  `listSum`). `bewB a n k := LenDerivable TAct a (instB n k)` is the parametric box "`□_a` of
  the `k`-instance of `n`", with its Σ₁ semisentence `bewBDef`.
* **U3 — Property 2 (Quantifier Distribution) with `dlen` accounting.** `instCode χ t d` is
  the derivation code of `{χ[t]}` from `d : {∀χ}`: cut on `∀χ` against `{∃∼χ, χ[t]}`, which
  `exsIntro` introduces at the term `t` from the closed leaf `{∼χ[t], ∃∼χ, χ[t]}`
  (`substs_neg` turns `(∼χ)[t]` into `∼(χ[t])`, `neg_all` turns `∼∀χ` into `∃∼χ`). Its
  `Proof` is `instCode_proof`; its length is EXACT (`dlen_instCode`, by the `DlenGraph.*_iff`
  inversion clauses) and bounded by `dlen d + 5|χ[t]| + 3|χ| + |t| + 7` (`dlen_instCode_le`).
  The theorems: `lenDerivable_inst_V` (any term, any Δ₁ theory), `lenDerivable_instB_V`
  (`t = bnum k` at `TAct`; `lenDerivable_instB_V'` with the instance length eliminated:
  `N + 5|χ|·|bnum k| + 3|χ| + |bnum k| + 7`; `bewB_of_all` in the box vocabulary), the meta twin `lenProvable_inst` at `V = ℕ` (the final meta step
  of PBLT — instantiate the uniform proof at `k`, cost `O(|χ[bnum k]| + size k)`), and the
  single-sentence form `instSentence` proved by `IΣ₁`/`PA`/`TAct` (`complete`).

Constants: `c₀ = 7`; the instance formula is charged `5×`, the template `3×`, the term `1×`
(the sequents `{χ[t]}`, `{∀χ, χ[t]}`, `{∃∼χ, χ[t]}`, `{∼χ[t], ∃∼χ, χ[t]}`, each node charging
its whole conclusion). The bound is stated in `|χ[t]|`, `|χ|`, `|t|` separately: `|χ| ≤ |χ[t]|`
and `|t| ≤ |χ[t]|` hold only when `#0` occurs in `χ`, so no single-quantity form is sharp.

Imports only `ArithS.CutV` and `ArithS.Bnum`; the `ℒₒᵣ → LAct` term-code transport of
`ArithS.Subst` is therefore re-proved here under the `InstV` namespace (four lines each).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### `ℒₒᵣ` term codes are `LAct` term codes (`LAct` keeps the `ℒₒᵣ` symbol codes) -/

namespace InstV

lemma isFunc_LOR {k f : V} : (ℒₒᵣ).IsFunc k f ↔
    (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1) := by
  rw [isFunc_def (L := ℒₒᵣ), func_def_LOR]; simp

lemma isFunc_LAct_of_LOR {k f : V} (h : (ℒₒᵣ).IsFunc k f) : LAct.IsFunc k f := by
  rw [isFunc_LAct]
  rcases isFunc_LOR.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))

lemma isSemiterm_LAct_of_LOR {n t : V} (ht : IsSemiterm ℒₒᵣ n t) : IsSemiterm LAct n t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hf hv ih
    rw [IsSemiterm.func]
    exact ⟨isFunc_LAct_of_LOR hf, IsSemitermVec.iff.mpr ⟨hv.lh, ih⟩⟩

end InstV

/-- The binary numeral is a closed `LAct` term code. -/
lemma bnum_term_LAct (k : V) : IsTerm LAct (bnum k) := InstV.isSemiterm_LAct_of_LOR (bnum_semiterm 0 k)

/-! ### U1 — the `bnum`-instance operator -/

/-- The formula code `n` (one free variable `#0`) with the binary numeral of `k` substituted:
`instB n k = substs1 LAct (bnum k) n` (definitionally). -/
noncomputable def instB (n k : V) : V := subst LAct (bnum k ∷ 0) n

lemma instB_eq_substs1 (n k : V) : instB n k = substs1 LAct (bnum k) n := rfl

/-- The Σ₁ graph of `instB` (`y n k`): the numeral, the one-entry vector, the substitution. -/
noncomputable def instBGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y n k. ∃ t, !bnumGraph t k ∧ ∃ v, !adjoinDef v t 0 ∧ !(substsGraph LAct) y v n”

instance instB.defined : 𝚺₁-Function₂ (instB : V → V → V) via instBGraph := .mk fun v ↦ by
  simp [instBGraph, instB]

instance instB.definable : 𝚺₁-Function₂ (instB : V → V → V) := instB.defined.to_definable

instance instB.definable' : Γ-[m + 1]-Function₂ (instB : V → V → V) := instB.definable.of_sigmaOne

/-- The `k`-instance of a one-variable formula code is a sentence code. -/
lemma isSemiformula_instB {n : V} (hn : IsSemiformula LAct 1 n) (k : V) :
    IsSemiformula LAct 0 (instB n k) :=
  IsSemiformula.substs1 (bnum_term_LAct k) hn

/-! #### The meta code equation -/

section quote

lemma term_emb_lMap_emb' (t : ClosedSemiterm ℒₒᵣ 0) :
    (Rew.emb (Semiterm.lMap emb t) : SyntacticSemiterm LAct 0) = Semiterm.lMap emb (Rew.emb t) := by
  induction t with
  | bvar x => rfl
  | fvar x => exact x.elim
  | func f v ih => simp [Rew.func, Semiterm.lMap_func, Function.comp_def, ih]

/-- The `LAct` code of the binary numeral term (embedded along `emb`) is `bnum k`. -/
lemma quote_lMap_bnumT (k : ℕ) :
    (⌜(Semiterm.lMap emb (bnumT k) : ClosedSemiterm LAct 0)⌝ : V) = bnum (k : V) := by
  rw [Semiterm.empty_quote_def, term_emb_lMap_emb', quote_term_lMap_emb, ← Semiterm.empty_quote_def,
    quote_bnumT]

lemma typed_val_emb' (t : ClosedSemiterm LAct 0) :
    ((⌜(Rew.emb t : SyntacticSemiterm LAct 0)⌝ : Bootstrapping.Semiterm V LAct 0)).val = (⌜t⌝ : V) := rfl

/-- **The code equation**: `instB ⌜φ⌝ k` is the code of `φ` with the binary numeral term
of `k` substituted. -/
theorem quote_instB (φ : Semisentence LAct 1) (k : ℕ) :
    instB (⌜φ⌝ : V) (k : V) = ⌜(φ ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct)⌝ := by
  unfold instB
  conv_rhs =>
    rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
      Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
      ← Sentence.quote_def]
  congr 1
  have hv : (fun i ↦ (⌜(Rew.emb (![Semiterm.lMap emb (bnumT k)] i) : SyntacticSemiterm LAct 0)⌝ :
      Bootstrapping.Semiterm V LAct 0)) =
      ![⌜(Rew.emb (Semiterm.lMap emb (bnumT k)) : SyntacticSemiterm LAct 0)⌝] := by
    funext i; fin_cases i; rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil, typed_val_emb', quote_lMap_bnumT]

end quote

/-! ### U1 — the parametric box -/

/-- The parametric box: `□_a` of the `k`-instance of the formula code `n`
(`LenDerivable` — no code bound). -/
def bewB (a n k : V) : Prop := LenDerivable TAct a (instB n k)

/-- `bewB` as a Σ₁ semisentence (`a n k`). -/
noncomputable def bewBDef : 𝚺₁.Semisentence 3 := .mkSigma
  “a n k. ∃ g, !instBGraph g n k ∧ !(lenDerivableDef TAct) a g”

instance bewB.defined : 𝚺₁-Relation₃[V] bewB via bewBDef := .mk fun v ↦ by
  simp [bewBDef, bewB, (LenDerivable.defined (V := V) TAct).iff]

instance bewB.definable : 𝚺₁-Relation₃[V] bewB := bewB.defined.to_definable

/-! ### U1 — the length of a substitution instance, inside `V`

`|p[w]| ≤ |p| · B` whenever every entry of `w` is either the identity variable `#i` or a CLOSED
term of length `≤ B ≥ 1` (`SubstInv`): a bound variable `#i` is charged `i + 1 ≤ (i + 1)·B`, a
closed entry `≤ B`, and closed entries are fixed by the bound shift, so the invariant passes
through `qVec` under quantifiers. For `instB n k` this gives `|instB n k| ≤ |n| · |bnum k|`. -/

section length

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- Every entry of the vector `w` is the identity variable or a closed term of length `≤ B`. -/
def SubstInv (L : Language) [L.Encodable] [L.LORDefinable] (B w : V) : Prop :=
  ∀ i < len w, w.[i] = ^#i ∨ (IsSemiterm L 0 w.[i] ∧ termLen L w.[i] ≤ B)

instance substInv_definable : Γ-[m + 1]-Relation[V] (SubstInv L) := by
  unfold SubstInv; definability

/-- A term code has at least one symbol. -/
lemma one_le_termLen {n t : V} (ht : IsSemiterm L n t) : 1 ≤ termLen L t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z _; simp
  · intro x; simp
  · intro k f v hf hv _
    rw [termLen_func hf hv.isUTerm]; exact le_add_self

/-- The bound shift fixes closed term codes. -/
lemma termBShift_eq_self_of_closed {t : V} (ht : IsSemiterm L 0 t) : termBShift L t = t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; exact absurd hz (by simp)
  · intro x; simp
  · intro k f v hf hv ih
    rw [termBShift_func hf hv.isUTerm]
    congr 1
    refine nth_ext' k (len_termBShiftVec hv.isUTerm) hv.lh fun i hi ↦ ?_
    rw [nth_termBShiftVec hv.isUTerm hi, ih i hi]

/-- The invariant passes through `qVec` (the vector under one more quantifier). -/
lemma substInv_qVec {B n m w : V} (hw : IsSemitermVec L n m w) (h : SubstInv L B w) :
    SubstInv L B (qVec L w) := by
  intro i hi
  rw [len_qVec hw.isUTerm] at hi
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩
  · left; simp [qVec]
  · have hj : j < n := lt_of_add_lt_add_right hi
    have hjw : j < len w := by rw [hw.lh]; exact hj
    have e : (qVec L w).[j + 1] = termBShift L w.[j] := by
      simp only [qVec, nth_adjoin_succ]
      rw [hw.lh, nth_termBShiftVec hw.isUTerm hj]
    rw [e]
    rcases h j hjw with hb | ⟨hc, hl⟩
    · left; rw [hb, termBShift_bvar]
    · right; rw [termBShift_eq_self_of_closed hc]; exact ⟨hc, hl⟩

/-- The one-entry vector of a closed term of length `≤ B` satisfies the invariant. -/
lemma substInv_single {B t : V} (ht : IsSemiterm L 0 t) (hB : termLen L t ≤ B) :
    SubstInv L B (t ∷ 0) := by
  intro i hi
  have h0 : i = 0 := by
    rw [len_adjoin, len_nil] at hi
    exact nonpos_iff_eq_zero.mp (lt_succ_iff_le.mp hi)
  subst h0
  right; simp [ht, hB]

/-- Entry-wise `a.[i] ≤ b.[i] · B` gives `Σ a ≤ (Σ b) · B`. -/
lemma listSum_le_mul {B a : V} :
    ∀ b : V, len a = len b → (∀ i < len a, a.[i] ≤ b.[i] * B) → listSum a ≤ listSum b * B := by
  induction a using adjoin_ISigma1.pi1_succ_induction with
  | hP => definability
  | nil => intro b _ _; simp
  | adjoin x a ih =>
    intro b hl h
    rcases nil_or_adjoin b with rfl | ⟨y, b', rfl⟩
    · simp at hl
    · rw [len_adjoin, len_adjoin] at hl
      have hl' : len a = len b' := by simpa using hl
      have h0 : x ≤ y * B := by simpa using h 0 (by simp)
      have hrest : ∀ i < len a, a.[i] ≤ b'.[i] * B := fun i hi ↦ by
        simpa using h (i + 1) (by rw [len_adjoin]; simpa using hi)
      rw [listSum_adjoin, listSum_adjoin, add_mul]
      exact add_le_add h0 (ih b' hl' hrest)

/-- The term-level bound: `|s[w]| ≤ |s| · B` under the invariant. -/
lemma termLen_termSubst_le {B n : V} (hB : 1 ≤ B) {s : V} (hs : IsSemiterm L n s) :
    ∀ m w : V, IsSemitermVec L n m w → SubstInv L B w →
      termLen L (termSubst L w s) ≤ termLen L s * B := by
  apply IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_ s hs
  · definability
  · intro z hz m w hw hinv
    rw [termSubst_bvar, termLen_bvar]
    have hzw : z < len w := by rw [hw.lh]; exact hz
    rcases hinv z hzw with hb | ⟨_, hl⟩
    · rw [hb, termLen_bvar]; exact le_mul_of_one_le_right (by simp) hB
    · exact le_trans hl (le_mul_of_one_le_left (by simp) (by simp))
  · intro x m w _ _
    rw [termSubst_fvar, termLen_fvar]; exact le_mul_of_one_le_right (by simp) hB
  · intro k f v hf hv ih m w hw hinv
    have hv' : IsUTermVec L k (termSubstVec L k w v) := (hw.termSubstVec hv).isUTerm
    rw [termSubst_func hf hv.isUTerm, termLen_func hf hv', termLen_func hf hv.isUTerm, add_mul, one_mul]
    refine add_le_add ?_ hB
    refine listSum_le_mul _ (by rw [len_termLenVec hv', len_termLenVec hv.isUTerm]) fun i hi ↦ ?_
    rw [len_termLenVec hv'] at hi
    rw [nth_termLenVec hv' hi, nth_termLenVec hv.isUTerm hi, nth_termSubstVec hv.isUTerm hi]
    exact ih i hi m w hw hinv

/-- The formula-level bound: `|p[w]| ≤ |p| · B` under the invariant. -/
lemma formulaLen_subst_le {B : V} (hB : 1 ≤ B) {n p : V} (hp : IsSemiformula L n p) :
    ∀ m w : V, IsSemitermVec L n m w → SubstInv L B w →
      formulaLen L (subst L w p) ≤ formulaLen L p * B := by
  apply IsSemiformula.pi1_structural_induction
    (P := fun n p ↦ ∀ m w : V, IsSemitermVec L n m w → SubstInv L B w →
      formulaLen L (subst L w p) ≤ formulaLen L p * B) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k r v hr hv m w hw hinv
    have hv' : IsUTermVec L k (termSubstVec L k w v) := (hw.termSubstVec hv).isUTerm
    rw [substs_rel hr hv.isUTerm, formulaLen_rel hr hv', formulaLen_rel hr hv.isUTerm, add_mul, one_mul]
    refine add_le_add ?_ hB
    refine listSum_le_mul _ (by rw [len_termLenVec hv', len_termLenVec hv.isUTerm]) fun i hi ↦ ?_
    rw [len_termLenVec hv'] at hi
    rw [nth_termLenVec hv' hi, nth_termLenVec hv.isUTerm hi, nth_termSubstVec hv.isUTerm hi]
    exact termLen_termSubst_le hB (hv.nth hi) m w hw hinv
  · intro n k r v hr hv m w hw hinv
    have hv' : IsUTermVec L k (termSubstVec L k w v) := (hw.termSubstVec hv).isUTerm
    rw [substs_nrel hr hv.isUTerm, formulaLen_nrel hr hv', formulaLen_nrel hr hv.isUTerm, add_mul, one_mul]
    refine add_le_add ?_ hB
    refine listSum_le_mul _ (by rw [len_termLenVec hv', len_termLenVec hv.isUTerm]) fun i hi ↦ ?_
    rw [len_termLenVec hv'] at hi
    rw [nth_termLenVec hv' hi, nth_termLenVec hv.isUTerm hi, nth_termSubstVec hv.isUTerm hi]
    exact termLen_termSubst_le hB (hv.nth hi) m w hw hinv
  · intro n m w _ _; simp [hB]
  · intro n m w _ _; simp [hB]
  · intro n p q hp hq ihp ihq m w hw hinv
    rw [substs_and hp.isUFormula hq.isUFormula,
      formulaLen_and (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      formulaLen_and hp.isUFormula hq.isUFormula, add_mul, add_mul, one_mul]
    exact add_le_add (add_le_add (ihp m w hw hinv) (ihq m w hw hinv)) hB
  · intro n p q hp hq ihp ihq m w hw hinv
    rw [substs_or hp.isUFormula hq.isUFormula,
      formulaLen_or (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      formulaLen_or hp.isUFormula hq.isUFormula, add_mul, add_mul, one_mul]
    exact add_le_add (add_le_add (ihp m w hw hinv) (ihq m w hw hinv)) hB
  · intro n p hp ih m w hw hinv
    rw [substs_all hp.isUFormula, formulaLen_all (hp.subst hw.qVec).isUFormula,
      formulaLen_all hp.isUFormula, add_mul, one_mul]
    exact add_le_add (ih (m + 1) (qVec L w) hw.qVec (substInv_qVec hw hinv)) hB
  · intro n p hp ih m w hw hinv
    rw [substs_ex hp.isUFormula, formulaLen_exs (hp.subst hw.qVec).isUFormula,
      formulaLen_exs hp.isUFormula, add_mul, one_mul]
    exact add_le_add (ih (m + 1) (qVec L w) hw.qVec (substInv_qVec hw hinv)) hB

end length

/-- **The length of the `bnum k`-instance**: `|instB n k| ≤ |n| · |bnum k|`. -/
theorem formulaLen_instB_le {n : V} (hn : IsSemiformula LAct 1 n) (k : V) :
    formulaLen LAct (instB n k) ≤ formulaLen LAct n * termLen LAct (bnum k) :=
  formulaLen_subst_le (one_le_termLen (bnum_term_LAct k)) hn 0 (bnum k ∷ 0)
    (by simp [bnum_term_LAct k]) (substInv_single (bnum_term_LAct k) (le_refl _))

/-! ### U3 — Quantifier Distribution on codes -/

section inst

variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

lemma substs1_neg_code {χ t : V} (hχ : IsSemiformula L 1 χ) (ht : IsTerm L t) :
    substs1 L t (neg L χ) = neg L (substs1 L t χ) :=
  substs_neg (m := 0) hχ (by simp [ht])

variable (L)

/-- The derivation code of `{χ[t]}` from `d : {∀χ}`: weaken `d` to `{∀χ, χ[t]}`; introduce
`∼∀χ = ∃∼χ` at the term `t` (`exsIntro`) from the closed leaf `{∼χ[t], ∃∼χ, χ[t]}`; cut on
`∀χ`. -/
noncomputable def instCode (χ t d : V) : V :=
  cutRule {substs1 L t χ} (^∀ χ)
    (wkRule (insert (^∀ χ) {substs1 L t χ}) d)
    (exsIntro (insert (^∃ neg L χ) {substs1 L t χ}) (neg L χ) t
      (axL (insert (substs1 L t (neg L χ)) (insert (^∃ neg L χ) {substs1 L t χ})) (substs1 L t χ)))

variable {L}

/-- The instance code is a `T`-proof of `χ[t]`. -/
theorem instCode_proof {χ t d : V} (hχ : IsSemiformula L 1 χ) (ht : IsTerm L t)
    (hd : Proof T d (^∀ χ)) : Proof T (instCode L χ t d) (substs1 L t χ) := by
  have hχt : IsFormula L (substs1 L t χ) := hχ.substs1 ht
  have hneg : substs1 L t (neg L χ) = neg L (substs1 L t χ) := substs1_neg_code hχ ht
  have e₁ : DerivationOf T (wkRule (insert (^∀ χ) {substs1 L t χ}) d) (insert (^∀ χ) {substs1 L t χ}) :=
    ⟨by simp, Derivation.wkRule (by simp [hχ, hχt]) (fun x hx ↦ by simp [mem_singleton_iff.mp hx]) hd⟩
  have e₃ : DerivationOf T
      (axL (insert (substs1 L t (neg L χ)) (insert (^∃ neg L χ) {substs1 L t χ})) (substs1 L t χ))
      (insert (substs1 L t (neg L χ)) (insert (^∃ neg L χ) {substs1 L t χ})) :=
    ⟨by simp, Derivation.axL (by rw [hneg]; simp [hχ, hχt]) (by simp) (by rw [hneg]; simp)⟩
  have e₂ : DerivationOf T
      (exsIntro (insert (^∃ neg L χ) {substs1 L t χ}) (neg L χ) t
        (axL (insert (substs1 L t (neg L χ)) (insert (^∃ neg L χ) {substs1 L t χ})) (substs1 L t χ)))
      (insert (^∃ neg L χ) {substs1 L t χ}) :=
    ⟨by simp, Derivation.exsIntro (by simp) ht e₃⟩
  refine ⟨by simp [instCode], Derivation.cutRule e₁ ?_⟩
  rw [neg_all hχ.isUFormula]
  exact e₂

/-- The exact length of the instance code, node by node. -/
theorem dlen_instCode {χ t d : V} (hχ : IsSemiformula L 1 χ) (ht : IsTerm L t)
    (hd : Proof T d (^∀ χ)) :
    dlen T (instCode L χ t d) =
      setLen L ({substs1 L t χ} : V)
      + (setLen L (insert (^∀ χ) {substs1 L t χ}) + dlen T d + 1)
      + (setLen L (insert (^∃ neg L χ) {substs1 L t χ}) + termLen L t
          + (setLen L (insert (substs1 L t (neg L χ)) (insert (^∃ neg L χ) {substs1 L t χ})) + 1) + 1)
      + 1 := by
  apply dlen_eq_of_graph (instCode_proof hχ ht hd).2
  unfold instCode
  refine DlenGraph.cutRule_iff.mpr ⟨_, _, DlenGraph.wkRule_iff.mpr ⟨_, dlen_graph hd.2, rfl⟩, ?_, rfl⟩
  exact DlenGraph.exsIntro_iff.mpr ⟨_, DlenGraph.axL_iff.mpr rfl, rfl⟩

/-- **Quantifier Distribution on codes, sharp**:
`dlen (instCode) ≤ dlen d + 5|χ[t]| + 3|χ| + |t| + 7`. -/
theorem dlen_instCode_le {χ t d : V} (hχ : IsSemiformula L 1 χ) (ht : IsTerm L t)
    (hd : Proof T d (^∀ χ)) :
    dlen T (instCode L χ t d) ≤
      dlen T d + 5 * formulaLen L (substs1 L t χ) + 3 * formulaLen L χ + termLen L t + 7 := by
  have hχ' := hχ.isUFormula
  have hχt : IsFormula L (substs1 L t χ) := hχ.substs1 ht
  have hneg : substs1 L t (neg L χ) = neg L (substs1 L t χ) := substs1_neg_code hχ ht
  set A := formulaLen L (substs1 L t χ) with hA
  set B := formulaLen L χ with hB
  have h₁ : setLen L (insert (^∀ χ) ({substs1 L t χ} : V)) ≤ A + B + 1 := by
    have := setLen_insert_le (L := L) (^∀ χ) {substs1 L t χ}
    rw [setLen_singleton, formulaLen_all hχ'] at this
    exact le_trans this (le_of_eq (by ring))
  have h₂ : setLen L (insert (^∃ neg L χ) ({substs1 L t χ} : V)) ≤ A + B + 1 := by
    have := setLen_insert_le (L := L) (^∃ neg L χ) {substs1 L t χ}
    rw [setLen_singleton, formulaLen_exs hχ'.neg, formulaLen_neg hχ'] at this
    exact le_trans this (le_of_eq (by ring))
  have h₃ : setLen L (insert (substs1 L t (neg L χ)) (insert (^∃ neg L χ) ({substs1 L t χ} : V)))
      ≤ 2 * A + B + 1 := by
    refine le_trans (setLen_insert_le _ _) ?_
    rw [hneg, formulaLen_neg hχt.isUFormula]
    exact le_trans (add_le_add h₂ (le_refl _)) (le_of_eq (by ring))
  rw [dlen_instCode hχ ht hd, setLen_singleton]
  calc A
      + (setLen L (insert (^∀ χ) {substs1 L t χ}) + dlen T d + 1)
      + (setLen L (insert (^∃ neg L χ) {substs1 L t χ}) + termLen L t
          + (setLen L (insert (substs1 L t (neg L χ)) (insert (^∃ neg L χ) {substs1 L t χ})) + 1) + 1)
      + 1
      ≤ A + ((A + B + 1) + dlen T d + 1)
      + ((A + B + 1) + termLen L t + ((2 * A + B + 1) + 1) + 1) + 1 := by gcongr
    _ = dlen T d + 5 * A + 3 * B + termLen L t + 7 := by ring

/-- **Property 2 (Quantifier Distribution) on codes, any Δ₁ theory, any closed term code**:
from a proof code of `∀χ` of length `≤ N`, a proof code of `χ[t]` of length
`≤ N + 5|χ[t]| + 3|χ| + |t| + 7`. -/
theorem lenDerivable_inst_V {N χ t : V} (hχ : IsSemiformula L 1 χ) (ht : IsTerm L t)
    (h : LenDerivable T N (^∀ χ)) :
    LenDerivable T (N + 5 * formulaLen L (substs1 L t χ) + 3 * formulaLen L χ + termLen L t + 7)
      (substs1 L t χ) := by
  obtain ⟨d, hd, hN⟩ := h
  refine ⟨instCode L χ t d, instCode_proof hχ ht hd, ?_⟩
  refine le_trans (dlen_instCode_le hχ ht hd) ?_
  gcongr

end inst

/-- **Property 2 at `TAct` for the binary numeral**: from a proof code of `∀χ` of length
`≤ N`, a proof code of the `bnum k`-instance of length
`≤ N + 5|instB χ k| + 3|χ| + |bnum k| + 7`. -/
theorem lenDerivable_instB_V {N χ k : V} (hχ : IsSemiformula LAct 1 χ)
    (h : LenDerivable TAct N (^∀ χ)) :
    LenDerivable TAct
      (N + 5 * formulaLen LAct (instB χ k) + 3 * formulaLen LAct χ + termLen LAct (bnum k) + 7)
      (instB χ k) :=
  lenDerivable_inst_V hχ (bnum_term_LAct k) h

/-- **Property 2 at `TAct`, in the template's length only** (`|instB χ k| ≤ |χ| · |bnum k|`,
`formulaLen_instB_le`): cost `N + 5|χ|·|bnum k| + 3|χ| + |bnum k| + 7`. -/
theorem lenDerivable_instB_V' {N χ k : V} (hχ : IsSemiformula LAct 1 χ)
    (h : LenDerivable TAct N (^∀ χ)) :
    LenDerivable TAct
      (N + 5 * (formulaLen LAct χ * termLen LAct (bnum k)) + 3 * formulaLen LAct χ
        + termLen LAct (bnum k) + 7)
      (instB χ k) :=
  lenDerivable_mono_V (by gcongr; exact formulaLen_instB_le hχ k) (lenDerivable_instB_V hχ h)

/-- The same, in the `bewB` vocabulary. -/
theorem bewB_of_all {N χ k : V} (hχ : IsSemiformula LAct 1 χ) (h : LenDerivable TAct N (^∀ χ)) :
    bewB (N + 5 * formulaLen LAct (instB χ k) + 3 * formulaLen LAct χ + termLen LAct (bnum k) + 7) χ k :=
  lenDerivable_instB_V hχ h

/-! ### The meta twin at `V = ℕ` — the final meta step of PBLT -/

section nat

/-- The code of the universal closure of a one-variable semisentence. -/
lemma quote_all_sentence (χ : Semisentence LAct 1) :
    (⌜(∀¹ χ : Sentence LAct)⌝ : V) = ^∀ (⌜χ⌝ : V) := by
  simp [Sentence.quote_def]

lemma isSemiformula_quote_one (χ : Semisentence LAct 1) : IsSemiformula LAct 1 (⌜χ⌝ : ℕ) := by
  rw [Sentence.quote_def]
  simp

lemma formulaLen_quote_sentence (σ : Sentence LAct) :
    formulaLen LAct (⌜σ⌝ : ℕ) = flen (σ : Proposition LAct) := by
  rw [Sentence.quote_def, formulaLen_quote]; simp

lemma formulaLen_quote_semisentence (χ : Semisentence LAct 1) :
    formulaLen LAct (⌜χ⌝ : ℕ) = flen (χ : Semiproposition LAct 1) := by
  rw [Sentence.quote_def, formulaLen_quote]; simp

/-- The `LAct` symbol count of `bnum k` is the meta length of the binary numeral term. -/
lemma termLen_bnum_nat (k : ℕ) :
    termLen LAct (bnum k : ℕ) = tlen (Rew.emb (bnumT k) : SyntacticSemiterm ℒₒᵣ 0) := by
  have h := quote_lMap_bnumT (V := ℕ) k
  rw [natCast_nat] at h
  rw [← h, Semiterm.empty_quote_def, termLen_quote, term_emb_lMap_emb', tlen_lMap]; simp

/-- **Property 2 (Quantifier Distribution), meta form, at `TAct`**: a `□_N` proof of `∀¹ χ`
yields a `□_{N + 5|χ[bnum k]| + 3|χ| + |bnum k| + 7}` proof of the instance
`χ ⇜ ![lMap emb (bnumT k)]` — the final meta step of PBLT (instantiate the uniform proof at
`k`). Proved through `lenDerivable_instB_V` at `V = ℕ`, `quote_instB`, and properness at `ℕ`
(`properV_nat_TAct`). -/
theorem lenProvable_inst (χ : Semisentence LAct 1) (k : ℕ) {N : ℕ}
    (h : LenProvable (fbound : ℕ → ℕ) N TAct (⌜(∀¹ χ : Sentence LAct)⌝ : ℕ)) :
    LenProvable (fbound : ℕ → ℕ)
      (N + 5 * flen ((χ ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct) : Proposition LAct)
        + 3 * flen (χ : Semiproposition LAct 1)
        + tlen (Rew.emb (bnumT k) : SyntacticSemiterm ℒₒᵣ 0) + 7)
      TAct (⌜(χ ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct)⌝ : ℕ) := by
  obtain ⟨d, _, hd, hk⟩ := h
  have e : ∀ n : ℕ, (ORingStructure.numeral n : ℕ) = n := fun n ↦ by simp
  rw [e] at hk
  rw [quote_all_sentence] at hd
  obtain ⟨d', hd', hk'⟩ :=
    lenDerivable_instB_V (V := ℕ) (k := k) (isSemiformula_quote_one χ) ⟨d, hd, hk⟩
  have hq : instB (⌜χ⌝ : ℕ) k = ⌜(χ ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) χ k
    rwa [natCast_nat] at this
  rw [hq] at hd' hk'
  rw [formulaLen_quote_sentence, formulaLen_quote_semisentence, termLen_bnum_nat] at hk'
  refine ⟨d', ?_, hd', ?_⟩
  · rw [e]; exact properV_nat_TAct _ d' _ hd' hk'
  · rw [e]; exact hk'

/-- The same with the numeral's length bounded by its bit length (`tlen_bnumT`):
cost `N + 5|χ[bnum k]| + 3|χ| + 6·size k + 8`. -/
theorem lenProvable_inst_size (χ : Semisentence LAct 1) (k : ℕ) {N : ℕ}
    (h : LenProvable (fbound : ℕ → ℕ) N TAct (⌜(∀¹ χ : Sentence LAct)⌝ : ℕ)) :
    LenProvable (fbound : ℕ → ℕ)
      (N + 5 * flen ((χ ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct) : Proposition LAct)
        + 3 * flen (χ : Semiproposition LAct 1) + 6 * Nat.size k + 8)
      TAct (⌜(χ ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct)⌝ : ℕ) :=
  lenProvable_fbound_mono (by have := tlen_bnumT k; omega) (lenProvable_inst χ k h)

end nat

/-! ### Quantifier Distribution as ONE arithmetic sentence, provable in `IΣ₁` (hence in `PA`) -/

section sentence

/-- **Quantifier Distribution on codes as a single `ℒₒᵣ`-sentence**: "for all `N x k`, if `x`
is a one-variable formula code and `∀x` has a `TAct`-proof of length `≤ N`, then the
`bnum k`-instance of `x` has one of length `≤ N + 5|x[bnum k]| + 3|x| + |bnum k| + 7`." -/
noncomputable def instSentence : ArithmeticSentence :=
  “∀ N x k, !(isSemiformula LAct).pi 1 x →
    ∀ u, !qqAllDef u x → !(lenDerivableDef TAct) N u →
    ∀ y, !instBGraph y x k → ∀ ly, !(formulaLenGraph LAct) ly y →
    ∀ lx, !(formulaLenGraph LAct) lx x →
    ∀ t, !bnumGraph t k → ∀ lt, !(termLenGraph LAct) lt t →
    !(lenDerivableDef TAct) (N + 5 * ly + 3 * lx + lt + 7) y”

lemma models_instSentence :
    V↓[ℒₒᵣ] ⊧ instSentence ↔
    ∀ N x k : V, IsSemiformula LAct 1 x →
      LenDerivable TAct N (^∀ x) →
      LenDerivable TAct (N + 5 * formulaLen LAct (instB x k) + 3 * formulaLen LAct x
        + termLen LAct (bnum k) + 7) (instB x k) := by
  simp [instSentence, models_iff, (IsSemiformula.defined (V := V) (L := LAct)).proper.iff',
    formulaLen.defined.iff, termLen.defined.iff, instB.defined.iff, bnum.defined.iff,
    (LenDerivable.defined (V := V) TAct).iff, numeral_eq_natCast]

/-- **`IΣ₁` proves Quantifier Distribution on codes.** -/
theorem isigma1_proves_instSentence : 𝗜𝚺₁ ⊢ instSentence :=
  complete 𝗜𝚺₁ _ fun (_ : Type) _ _ ↦ models_instSentence.mpr fun _ _ _ hx h ↦
    lenDerivable_instB_V hx h

/-- **`PA` proves Quantifier Distribution on codes.** -/
theorem pa_proves_instSentence : 𝗣𝗔 ⊢ instSentence :=
  complete 𝗣𝗔 _ fun (V : Type) _ _ ↦
    haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    models_instSentence.mpr fun _ _ _ hx h ↦ lenDerivable_instB_V hx h

/-- **`TAct` proves Quantifier Distribution on codes** (embedded along `emb`). -/
theorem tact_proves_instSentence : TAct ⊢ Semiformula.lMap LAct.emb instSentence := by
  refine Theory.Proof.complete fun (s : Struc.{0} LAct) hs ↦ ?_
  have hPA : s ⊧* Theory.lMap LAct.emb 𝗣𝗔 :=
    Semantics.ModelsSet.of_subset hs (fun x hx ↦ Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx))
  exact lMap_models_lMap (Theory.Proof.sound pa_proves_instSentence) hPA

end sentence

end ArithS
