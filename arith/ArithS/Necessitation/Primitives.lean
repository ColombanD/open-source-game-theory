import ArithS.InstV
import ArithS.ProperV

/-!
# ArithS.Necessitation.Primitives — the two moves of the verification proof, on derivation codes

`Research/Notes/M4_BOUNDED_HBL/DESIGN_inner_necessitation.md` §3.1 names the TWO primitive moves
of the inner verification proof (one-sided LK on codes; sequents are finite bit-SETS of formula
codes; hypotheses live in a sequent as their negations):

* **`useLemmaCode` — use a stored universal lemma at witnesses.** From a stored proof code
  `dΛ` of `Λ = ∀^m B` (`allsIter m B`, `= qqAlls B m` by `qqAlls_natCast`), witness term codes
  `e₁ … e_m` (closed) and a continuation `d` deriving the goal `Γ` under the hypothesis
  `B[ē]` (`d : insert (neg (instOuter es B)) Γ`), a derivation code of `Γ`:
  `cutRule Γ Λ (wkRule (insert Λ Γ) dΛ) (exsChainCode es (neg B) Γ d)`, where the second
  premise `insert (neg Λ) Γ = insert (∃^m (neg B)) Γ` (`neg_allsIter`) is closed by `m`
  `exsIntro`s at `e₁, …, e_m` (`exsChainCode`), outermost quantifier first, down to `d`
  weakened once. Foundation's `exsIntro` keeps the principal formula in the sequent, so the
  contexts ACCUMULATE along the chain (`m + 1` sequents, the `j`-th of size
  `≤ |Γ| + (j + 1)·F`), which is where the `(m + 1)²` in the bound comes from.
  `instOuter es B` is the iterated outermost-first instantiation (`subOuter`: substitute
  the outermost bound variable `#n` of an `(n + 1)`-semiformula, `subst (qVecIter n (e ∷ (0 : V)))`);
  `isInstOf_instOuter` shows it is ONE simultaneous substitution of `B` by identity-or-closed
  entries (`IsInstOf`, the invariant carried along the chain, composed by `substs_substs`), so
  `|B[ē]| ≤ |B|·E` (`formulaLen_instOuter_le`), not `|B|·E^m`.
* **`elimExistsCode` — eliminate an existential with a fresh eigenvariable.** From `D`
  deriving `insert (∃ P) Δ` (`Δ ⊆ Γ`) and a continuation `d` deriving
  `insert (neg (free P)) (setShift Γ)` — the goal under the hypothesis `P(&0)`, every free
  variable of `Γ` shifted — a derivation code of `Γ`:
  `cutRule Γ (∃ P) (wkRule (insert (∃ P) Γ) D) (allIntro (insert (∀ neg P) Γ) (neg P) (wkRule … d))`
  (`neg_ex`, `free_neg`). The shift charges every free-variable occurrence one more symbol
  (`termLen_fvar` is unary), so `|shift p| ≤ 2|p|` and `setLen (setShift Γ) ≤ 2·setLen Γ`
  are the honest bounds (`formulaLen_shift_le`, `setLen_setShift_le`).
* **`wkDropCode`** — drop facts: one `wkRule`.

Every `dlen` bound is proved EXACTLY through the `DlenGraph.*_iff` inversion clauses
(`ArithS.DerivationLength`) as in `ArithS.CutV`, then loosened. Meta `m : ℕ` (the library
lemmas have at most ~8 variables); witnesses are a `List V`, outermost quantifier first.
V-generic (every model of `IΣ₁`), any Δ₁ theory.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ### Iterated quantifiers on codes, meta-indexed -/

/-- `exsIter n q = ^∃ … ^∃ q` (`n` existential quantifiers). -/
noncomputable def exsIter : ℕ → V → V
  | 0, q => q
  | n + 1, q => ^∃ (exsIter n q)

/-- `allsIter n q = ^∀ … ^∀ q` (`n` universal quantifiers); `= qqAlls q n` (`qqAlls_natCast`). -/
noncomputable def allsIter : ℕ → V → V
  | 0, q => q
  | n + 1, q => ^∀ (allsIter n q)

@[simp] lemma exsIter_zero (q : V) : exsIter 0 q = q := rfl
@[simp] lemma exsIter_succ (n : ℕ) (q : V) : exsIter (n + 1) q = ^∃ (exsIter n q) := rfl
@[simp] lemma allsIter_zero (q : V) : allsIter 0 q = q := rfl
@[simp] lemma allsIter_succ (n : ℕ) (q : V) : allsIter (n + 1) q = ^∀ (allsIter n q) := rfl

/-- Foundation's `qqAlls` at a standard index is `allsIter`. -/
lemma qqAlls_natCast (q : V) (m : ℕ) : qqAlls q (m : V) = allsIter m q := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.cast_succ, qqAlls_succ, ih, allsIter_succ]

@[simp] lemma isUFormula_exsIter {n : ℕ} {q : V} : IsUFormula L (exsIter n q) ↔ IsUFormula L q := by
  induction n with
  | zero => simp
  | succ n ih => rw [exsIter_succ, IsUFormula.ex, ih]

@[simp] lemma isUFormula_allsIter {n : ℕ} {q : V} : IsUFormula L (allsIter n q) ↔ IsUFormula L q := by
  induction n with
  | zero => simp
  | succ n ih => rw [allsIter_succ, IsUFormula.all, ih]

lemma isSemiformula_exsIter {k : ℕ} : ∀ {n q : V}, IsSemiformula L (n + (k : V)) q →
    IsSemiformula L n (exsIter k q) := by
  induction k with
  | zero => intro n q h; simpa using h
  | succ k ih =>
    intro n q h
    rw [exsIter_succ, IsSemiformula.exs]
    exact ih (by rw [Nat.cast_succ, ← add_assoc, add_right_comm] at h; exact h)

lemma isSemiformula_allsIter {k : ℕ} : ∀ {n q : V}, IsSemiformula L (n + (k : V)) q →
    IsSemiformula L n (allsIter k q) := by
  induction k with
  | zero => intro n q h; simpa using h
  | succ k ih =>
    intro n q h
    rw [allsIter_succ, IsSemiformula.all]
    exact ih (by rw [Nat.cast_succ, ← add_assoc, add_right_comm] at h; exact h)

lemma isFormula_exsIter {k : ℕ} {q : V} (h : IsSemiformula L (k : V) q) :
    IsFormula L (exsIter k q) :=
  isSemiformula_exsIter (by simpa using h)

lemma isFormula_allsIter {k : ℕ} {q : V} (h : IsSemiformula L (k : V) q) :
    IsFormula L (allsIter k q) :=
  isSemiformula_allsIter (by simpa using h)

/-- `∼(∀^n q) = ∃^n (∼q)` on codes. -/
lemma neg_allsIter {n : ℕ} {q : V} (hq : IsUFormula L q) :
    neg L (allsIter n q) = exsIter n (neg L q) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [allsIter_succ, neg_all (isUFormula_allsIter.mpr hq), ih, exsIter_succ]

/-- `∼(∃^n q) = ∀^n (∼q)` on codes. -/
lemma neg_exsIter {n : ℕ} {q : V} (hq : IsUFormula L q) :
    neg L (exsIter n q) = allsIter n (neg L q) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [exsIter_succ, neg_ex (isUFormula_exsIter.mpr hq), ih, allsIter_succ]

lemma formulaLen_exsIter {n : ℕ} {q : V} (hq : IsUFormula L q) :
    formulaLen L (exsIter n q) = formulaLen L q + (n : V) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [exsIter_succ, formulaLen_exs (isUFormula_exsIter.mpr hq), ih, Nat.cast_succ, add_assoc]

lemma formulaLen_allsIter {n : ℕ} {q : V} (hq : IsUFormula L q) :
    formulaLen L (allsIter n q) = formulaLen L q + (n : V) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [allsIter_succ, formulaLen_all (isUFormula_allsIter.mpr hq), ih, Nat.cast_succ, add_assoc]

/-! ### Substitution under `n` quantifiers: `qVecIter`, `subOuter`, `instOuter` -/

variable (L) in
/-- The substitution vector `w` pushed under `n` quantifiers: `qVecIter (n + 1) w = qVecIter n (qVec w)`. -/
noncomputable def qVecIter : ℕ → V → V
  | 0, w => w
  | n + 1, w => qVecIter n (qVec L w)

@[simp] lemma qVecIter_zero (w : V) : qVecIter L 0 w = w := rfl
@[simp] lemma qVecIter_succ (n : ℕ) (w : V) : qVecIter L (n + 1) w = qVecIter L n (qVec L w) := rfl

/-- `subst w (∃^n q) = ∃^n (subst (qVecIter n w) q)`. -/
lemma subst_exsIter {n : ℕ} {q : V} (hq : IsUFormula L q) :
    ∀ w : V, subst L w (exsIter n q) = exsIter n (subst L (qVecIter L n w) q) := by
  induction n with
  | zero => intro w; rfl
  | succ n ih =>
    intro w
    rw [exsIter_succ, substs_ex (isUFormula_exsIter.mpr hq), ih, qVecIter_succ, exsIter_succ]

lemma isSemitermVec_qVecIter {n : ℕ} : ∀ {k m w : V}, IsSemitermVec L k m w →
    IsSemitermVec L (k + (n : V)) (m + (n : V)) (qVecIter L n w) := by
  induction n with
  | zero => intro k m w h; simpa using h
  | succ n ih =>
    intro k m w h
    have h' := ih h.qVec
    rw [qVecIter_succ, Nat.cast_succ, ← add_assoc, ← add_assoc]
    rwa [add_right_comm k 1, add_right_comm m 1] at h'

lemma substInv_qVecIter {n : ℕ} : ∀ {E k m w : V}, IsSemitermVec L k m w → SubstInv L E w →
    SubstInv L E (qVecIter L n w) := by
  induction n with
  | zero => intro E k m w _ h; simpa using h
  | succ n ih =>
    intro E k m w hw h
    rw [qVecIter_succ]
    exact ih hw.qVec (substInv_qVec hw h)

variable (L) in
/-- Substitute the closed term `e` for the OUTERMOST bound variable `#n` of the
`(n + 1)`-semiformula `q` (the variable bound by the outermost of `n + 1` quantifiers):
`subOuter n e q = subst ?[#0, …, #(n-1), e] q`. -/
noncomputable def subOuter (n : ℕ) (e q : V) : V := subst L (qVecIter L n (e ∷ (0 : V))) q

lemma isSemitermVec_qVecIter_single {n : ℕ} {e : V} (he : IsTerm L e) :
    IsSemitermVec L ((n : V) + 1) (n : V) (qVecIter L n (e ∷ (0 : V))) := by
  have h : IsSemitermVec L 1 0 (e ∷ (0 : V)) := by simp [he]
  have h' := isSemitermVec_qVecIter (n := n) h
  rwa [add_comm, zero_add] at h'

lemma isSemiformula_subOuter {n : ℕ} {e q : V} (hq : IsSemiformula L ((n : V) + 1) q)
    (he : IsTerm L e) : IsSemiformula L (n : V) (subOuter L n e q) :=
  hq.subst (isSemitermVec_qVecIter_single he)

/-- `substs1 e (∃^n q) = ∃^n (subOuter n e q)` — one `exsIntro` step on the chain. -/
lemma substs1_exsIter {n : ℕ} {q : V} (hq : IsUFormula L q) (e : V) :
    substs1 L e (exsIter n q) = exsIter n (subOuter L n e q) :=
  subst_exsIter hq (e ∷ (0 : V))

lemma subOuter_neg {n : ℕ} {e q : V} (hq : IsSemiformula L ((n : V) + 1) q) (he : IsTerm L e) :
    subOuter L n e (neg L q) = neg L (subOuter L n e q) :=
  substs_neg hq (isSemitermVec_qVecIter_single he)

variable (L) in
/-- Instantiate `∀^m B` at the witnesses `es = [e₁, …, e_m]`, outermost quantifier first:
`instOuter [] B = B`, `instOuter (e :: es) B = instOuter es (subOuter es.length e B)`.
Extensionally ONE simultaneous substitution `subst ?[e_m, …, e₁] B` (`isInstOf_instOuter`). -/
noncomputable def instOuter : List V → V → V
  | [], q => q
  | e :: es, q => instOuter es (subOuter L es.length e q)

@[simp] lemma instOuter_nil (q : V) : instOuter L [] q = q := rfl
@[simp] lemma instOuter_cons (e : V) (es : List V) (q : V) :
    instOuter L (e :: es) q = instOuter L es (subOuter L es.length e q) := rfl

lemma isFormula_instOuter : ∀ (es : List V) {q : V}, IsSemiformula L (es.length : V) q →
    (∀ e ∈ es, IsTerm L e) → IsFormula L (instOuter L es q) := by
  intro es
  induction es with
  | nil => intro q hq _; simpa using hq
  | cons e es ih =>
    intro q hq hes
    rw [instOuter_cons]
    refine ih (isSemiformula_subOuter (by simpa [Nat.cast_succ] using hq) (hes e (by simp))) ?_
    exact fun e' he' ↦ hes e' (by simp [he'])

lemma instOuter_neg : ∀ (es : List V) {q : V}, IsSemiformula L (es.length : V) q →
    (∀ e ∈ es, IsTerm L e) → instOuter L es (neg L q) = neg L (instOuter L es q) := by
  intro es
  induction es with
  | nil => intro q _ _; rfl
  | cons e es ih =>
    intro q hq hes
    have hq' : IsSemiformula L ((es.length : V) + 1) q := by simpa [Nat.cast_succ] using hq
    rw [instOuter_cons, instOuter_cons, subOuter_neg hq' (hes e (by simp))]
    exact ih (isSemiformula_subOuter hq' (hes e (by simp))) (fun e' he' ↦ hes e' (by simp [he']))

/-! ### The chain invariant: every partial instance is ONE simultaneous substitution -/

/-- A closed term is fixed by `termSubst`. -/
lemma termSubst_eq_self_of_closed {w t : V} (ht : IsSemiterm L 0 t) : termSubst L w t = t :=
  termSubst_eq_self ht (fun _ hi ↦ absurd hi (by simp))

/-- The invariant passes through composition: `termSubstVec k w v` (entrywise `termSubst w`)
has identity-or-closed entries when both `w` and `v` do. -/
lemma substInv_termSubstVec {E k n m w v : V} (hw : IsSemitermVec L n m w)
    (hv : IsSemitermVec L k n v) (hiw : SubstInv L E w) (hiv : SubstInv L E v) :
    SubstInv L E (termSubstVec L k w v) := by
  intro i hi
  rw [len_termSubstVec hv.isUTerm] at hi
  rw [nth_termSubstVec hv.isUTerm hi]
  rcases hiv i (by rw [hv.lh]; exact hi) with hb | ⟨hc, hl⟩
  · rw [hb, termSubst_bvar]
    have hin : i < n := by
      have := hv.nth hi
      rw [hb] at this
      exact IsSemiterm.bvar.mp this
    exact hiw i (by rw [hw.lh]; exact hin)
  · right
    rw [termSubst_eq_self_of_closed hc]
    exact ⟨hc, hl⟩

variable (L) in
/-- `q` is the `m`-semiformula `B` under a simultaneous substitution into an `n`-semiformula
whose entries are identity variables or closed terms of length `≤ E` — or `B` itself
(`n = m`). The invariant of the instantiation chain (`isInstOf_subOuter`). -/
def IsInstOf (E : V) (m : ℕ) (B : V) (n : ℕ) (q : V) : Prop :=
  (n = m ∧ q = B) ∨
    ∃ W, IsSemitermVec L (m : V) (n : V) W ∧ SubstInv L E W ∧ q = subst L W B

lemma isInstOf_self (E : V) (m : ℕ) (B : V) : IsInstOf L E m B m B := Or.inl ⟨rfl, rfl⟩

/-- One outermost instantiation preserves the invariant (`substs_substs` composes the vectors). -/
lemma isInstOf_subOuter {E : V} {m : ℕ} {B : V} (hB : IsSemiformula L (m : V) B) {n : ℕ}
    {q e : V} (he : IsTerm L e) (hle : termLen L e ≤ E) (h : IsInstOf L E m B (n + 1) q) :
    IsInstOf L E m B n (subOuter L n e q) := by
  have hV : IsSemitermVec L ((n : V) + 1) (n : V) (qVecIter L n (e ∷ (0 : V))) :=
    isSemitermVec_qVecIter_single he
  have hVinv : SubstInv L E (qVecIter L n (e ∷ (0 : V))) :=
    substInv_qVecIter (show IsSemitermVec L 1 0 (e ∷ (0 : V)) by simp [he]) (substInv_single he hle)
  rcases h with ⟨rfl, rfl⟩ | ⟨W, hW, hWinv, rfl⟩
  · right
    refine ⟨qVecIter L n (e ∷ (0 : V)), ?_, hVinv, rfl⟩
    simpa [Nat.cast_succ] using hV
  · right
    have hW' : IsSemitermVec L (m : V) ((n : V) + 1) W := by simpa [Nat.cast_succ] using hW
    refine ⟨termSubstVec L (m : V) (qVecIter L n (e ∷ (0 : V))) W, hV.termSubstVec hW',
      substInv_termSubstVec hV hW' hVinv hWinv, ?_⟩
    exact substs_substs hB hV hW'

/-- The length of every partial instance: `|q| ≤ |B|·E`. -/
lemma formulaLen_le_of_isInstOf {E : V} (hE : 1 ≤ E) {m : ℕ} {B : V}
    (hB : IsSemiformula L (m : V) B) {n : ℕ} {q : V} (h : IsInstOf L E m B n q) :
    formulaLen L q ≤ formulaLen L B * E := by
  rcases h with ⟨_, rfl⟩ | ⟨W, hW, hWinv, rfl⟩
  · exact le_mul_of_one_le_right (by simp) hE
  · exact formulaLen_subst_le hE hB _ W hW hWinv

/-- `instOuter es B` is a single simultaneous substitution of the witnesses (identity-or-closed
entries of length `≤ E`) — hence `|instOuter es B| ≤ |B|·E`, NOT `|B|·E^m`. -/
lemma isInstOf_instOuter {E : V} {m : ℕ} {B : V} (hB : IsSemiformula L (m : V) B) :
    ∀ (es : List V) {n : ℕ} {q : V}, (∀ e ∈ es, IsTerm L e ∧ termLen L e ≤ E) → n = es.length →
    IsInstOf L E m B n q → IsInstOf L E m B 0 (instOuter L es q) := by
  intro es
  induction es with
  | nil => intro n q _ hn h; subst hn; simpa using h
  | cons e es ih =>
    intro n q hes hn h
    subst hn
    rw [instOuter_cons]
    exact ih (fun e' he' ↦ hes e' (by simp [he'])) rfl
      (isInstOf_subOuter hB (hes e (by simp)).1 (hes e (by simp)).2 h)

theorem formulaLen_instOuter_le {E : V} (hE : 1 ≤ E) (es : List V) {B : V}
    (hB : IsSemiformula L (es.length : V) B) (hes : ∀ e ∈ es, IsTerm L e ∧ termLen L e ≤ E) :
    formulaLen L (instOuter L es B) ≤ formulaLen L B * E :=
  formulaLen_le_of_isInstOf hE hB (isInstOf_instOuter hB es hes rfl (isInstOf_self E _ B))

/-! ### Primitive 1 — the `exsIntro` chain and `useLemmaCode` -/

section chain

variable {T : Theory L} [T.Δ₁]

lemma subset_insert_of_subset {a b : V} (x : V) (h : a ⊆ b) : a ⊆ insert x b :=
  fun _ hi ↦ mem_bitInsert_iff.mpr (Or.inr (h hi))

lemma one_le_two' : (1 : V) ≤ 2 := by rw [← one_add_one_eq_two]; exact le_self_add

variable (L) in
/-- The chain of `es.length` `exsIntro`s closing `insert (∃^m q) Γ` at the witnesses
`es = [e₁, …, e_m]` (outermost quantifier first), down to the continuation `d` (a derivation of
`insert (instOuter es q) Γ₀`, `Γ₀ ⊆ Γ`) weakened once. Each `exsIntro` keeps its principal
formula, so the `j`-th sequent is `Γ` plus the `j + 1` chain formulas `∃^{m-i} q_i`. -/
noncomputable def exsChainCode : List V → V → V → V → V
  | [], q, Γ, d => wkRule (insert q Γ) d
  | e :: es, q, Γ, d =>
    exsIntro (insert (exsIter (es.length + 1) q) Γ) (exsIter es.length q) e
      (exsChainCode es (subOuter L es.length e q) (insert (exsIter (es.length + 1) q) Γ) d)

@[simp] lemma exsChainCode_nil (q Γ d : V) : exsChainCode L [] q Γ d = wkRule (insert q Γ) d := rfl

@[simp] lemma exsChainCode_cons (e : V) (es : List V) (q Γ d : V) :
    exsChainCode L (e :: es) q Γ d =
      exsIntro (insert (exsIter (es.length + 1) q) Γ) (exsIter es.length q) e
        (exsChainCode L es (subOuter L es.length e q) (insert (exsIter (es.length + 1) q) Γ) d) := rfl

/-- The chain derives `insert (∃^m q) Γ` from a derivation of `insert (instOuter es q) Γ₀`. -/
theorem exsChainCode_proof : ∀ (es : List V) {q Γ Γ₀ d : V},
    IsSemiformula L (es.length : V) q → (∀ e ∈ es, IsTerm L e) → IsFormulaSet L Γ → Γ₀ ⊆ Γ →
    DerivationOf T d (insert (instOuter L es q) Γ₀) →
    DerivationOf T (exsChainCode L es q Γ d) (insert (exsIter es.length q) Γ) := by
  intro es
  induction es with
  | nil =>
    intro q Γ Γ₀ d hq _ hΓ hsub hd
    have hq0 : IsFormula L q := by simpa using hq
    exact ⟨by simp, Derivation.wkRule (by simp [hq0, hΓ])
      (insert_subset_insert_of_subset q hsub) hd⟩
  | cons e es ih =>
    intro q Γ Γ₀ d hq hes hΓ hsub hd
    have hq' : IsSemiformula L ((es.length : V) + 1) q := by simpa [Nat.cast_succ] using hq
    have he : IsTerm L e := hes e (by simp)
    have hS : IsFormulaSet L (insert (exsIter (es.length + 1) q) Γ) :=
      IsFormulaSet.insert_iff.mpr ⟨isFormula_exsIter (k := es.length + 1) (by simpa using hq), hΓ⟩
    have hrec := ih (isSemiformula_subOuter hq' he) (fun e' he' ↦ hes e' (by simp [he'])) hS
      (subset_insert_of_subset _ hsub) hd
    refine ⟨by simp, Derivation.exsIntro (by simp) he ?_⟩
    rw [substs1_exsIter hq'.isUFormula]
    exact hrec

/-- **The length of the chain**: with `F ≥ |B|·E + m` a bound on every chain formula (`|q_j| + (m − j)`)
and `G ≥ |Γ|`, `dlen ≤ dlen d + (m + 1)(G + 1) + (m + 1)²·F + m·E`. The `(m + 1)²` is the
accumulation of the principal formulas (§3.1 of the design note). -/
theorem dlen_exsChainCode_le {E F : V} (hE : 1 ≤ E) {m : ℕ} {B : V}
    (hB : IsSemiformula L (m : V) B) :
    ∀ (es : List V) {q Γ Γ₀ d G : V},
    IsSemiformula L (es.length : V) q → (∀ e ∈ es, IsTerm L e ∧ termLen L e ≤ E) →
    IsFormulaSet L Γ → Γ₀ ⊆ Γ → DerivationOf T d (insert (instOuter L es q) Γ₀) →
    IsInstOf L E m B es.length q → formulaLen L B * E + (es.length : V) ≤ F → setLen L Γ ≤ G →
    dlen T (exsChainCode L es q Γ d) ≤
      dlen T d + ((es.length : V) + 1) * (G + 1)
        + ((es.length : V) + 1) * ((es.length : V) + 1) * F + (es.length : V) * E := by
  intro es
  induction es with
  | nil =>
    intro q Γ Γ₀ d G hq _ hΓ hsub hd hinst hF hG
    have hq0 : IsFormula L q := by simpa using hq
    have hpf := exsChainCode_proof (T := T) [] hq (by simp) hΓ hsub hd
    have hlen : dlen T (exsChainCode L [] q Γ d) = setLen L (insert q Γ) + dlen T d + 1 :=
      dlen_eq_of_graph hpf.2 (DlenGraph.wkRule_iff.mpr ⟨_, dlen_graph hd.2, rfl⟩)
    have hqF : formulaLen L q ≤ F :=
      le_trans (formulaLen_le_of_isInstOf hE hB hinst) (le_trans le_self_add hF)
    have h1 : setLen L (insert q Γ) ≤ G + F :=
      le_trans (setLen_insert_le _ _) (add_le_add hG hqF)
    rw [hlen]
    refine le_trans (b := G + F + dlen T d + 1) (add_le_add (add_le_add h1 (le_refl _)) (le_refl _))
      (le_of_eq ?_)
    simp only [List.length_nil, Nat.cast_zero]
    ring
  | cons e es ih =>
    intro q Γ Γ₀ d G hq hes hΓ hsub hd hinst hF hG
    have hq' : IsSemiformula L ((es.length : V) + 1) q := by simpa [Nat.cast_succ] using hq
    have he : IsTerm L e := (hes e (by simp)).1
    have hle : termLen L e ≤ E := (hes e (by simp)).2
    have hS : IsFormulaSet L (insert (exsIter (es.length + 1) q) Γ) :=
      IsFormulaSet.insert_iff.mpr ⟨isFormula_exsIter (k := es.length + 1) (by simpa using hq), hΓ⟩
    have hes' : ∀ e' ∈ es, IsTerm L e' ∧ termLen L e' ≤ E := fun e' he' ↦ hes e' (by simp [he'])
    have hrec := exsChainCode_proof (T := T) es (isSemiformula_subOuter hq' he) (fun e' he' ↦ (hes' e' he').1)
      hS (subset_insert_of_subset _ hsub) hd
    have hpf := exsChainCode_proof (T := T) (e :: es) hq (fun e' he' ↦ (hes e' he').1) hΓ hsub hd
    have hlen : dlen T (exsChainCode L (e :: es) q Γ d) =
        setLen L (insert (exsIter (es.length + 1) q) Γ) + termLen L e
          + dlen T (exsChainCode L es (subOuter L es.length e q) (insert (exsIter (es.length + 1) q) Γ) d) + 1 :=
      dlen_eq_of_graph hpf.2 (DlenGraph.exsIntro_iff.mpr ⟨_, dlen_graph hrec.2, rfl⟩)
    have hF₁ : formulaLen L B * E + ((es.length + 1 : ℕ) : V) ≤ F := by
      simpa only [List.length_cons] using hF
    have hF' : formulaLen L B * E + (es.length : V) ≤ F :=
      le_trans (add_le_add (le_refl _) (by rw [Nat.cast_succ]; exact le_self_add)) hF₁
    have hchainF : formulaLen L (exsIter (es.length + 1) q) ≤ F := by
      rw [formulaLen_exsIter hq'.isUFormula]
      exact le_trans (add_le_add (formulaLen_le_of_isInstOf hE hB hinst) (le_refl _)) hF₁
    have hS_le : setLen L (insert (exsIter (es.length + 1) q) Γ) ≤ G + F :=
      le_trans (setLen_insert_le _ _) (add_le_add hG hchainF)
    have hIH := ih (isSemiformula_subOuter hq' he) hes' hS (subset_insert_of_subset _ hsub) hd
      (isInstOf_subOuter hB he hle hinst) hF' hS_le
    rw [hlen]
    refine le_trans (add_le_add (add_le_add (add_le_add hS_le hle) hIH) (le_refl 1)) ?_
    refine le_trans (le_self_add (b := ((es.length : V) + 1) * F)) (le_of_eq ?_)
    simp only [List.length_cons, Nat.cast_succ]
    ring

variable (L) in
/-- **Use a stored universal lemma at witnesses.** `Λ = ∀^m B` (`allsIter m B`), `dΛ` a stored
proof code of `Λ`, `es = [e₁, …, e_m]` closed witness codes, `d` a derivation of the goal `Γ`
under the hypothesis `B[ē]` (`insert (neg (instOuter es B)) Γ`): cut on `Λ`, premise (a) the
stored proof weakened to `insert Λ Γ`, premise (b) `insert (neg Λ) Γ = insert (∃^m (neg B)) Γ`
closed by the `exsIntro` chain. -/
noncomputable def useLemmaCode (Γ : V) (es : List V) (B dΛ d : V) : V :=
  cutRule Γ (allsIter es.length B)
    (wkRule (insert (allsIter es.length B) Γ) dΛ)
    (exsChainCode L es (neg L B) Γ d)

/-- `useLemmaCode` derives `Γ`. -/
theorem useLemmaCode_proof {Γ Γ₀ : V} {es : List V} {B dΛ d : V}
    (hB : IsSemiformula L (es.length : V) B) (hes : ∀ e ∈ es, IsTerm L e)
    (hΓ : IsFormulaSet L Γ) (hsub : Γ₀ ⊆ Γ)
    (hΛ : Proof T dΛ (allsIter es.length B))
    (hd : DerivationOf T d (insert (neg L (instOuter L es B)) Γ₀)) :
    DerivationOf T (useLemmaCode L Γ es B dΛ d) Γ := by
  have hΛf : IsFormula L (allsIter es.length B) := isFormula_allsIter hB
  have e₁ : DerivationOf T (wkRule (insert (allsIter es.length B) Γ) dΛ)
      (insert (allsIter es.length B) Γ) :=
    ⟨by simp, Derivation.wkRule (by simp [hΛf, hΓ]) (fun x hx ↦ by simp [mem_singleton_iff.mp hx]) hΛ⟩
  have e₂ : DerivationOf T (exsChainCode L es (neg L B) Γ d) (insert (exsIter es.length (neg L B)) Γ) :=
    exsChainCode_proof es (by simpa using hB) hes hΓ hsub (by rw [instOuter_neg es hB hes]; exact hd)
  refine ⟨by simp [useLemmaCode], Derivation.cutRule e₁ ?_⟩
  rw [neg_allsIter hB.isUFormula]
  exact e₂

/-- The exact length of `useLemmaCode`: the root, the weakened stored proof, the chain. -/
theorem dlen_useLemmaCode {Γ Γ₀ : V} {es : List V} {B dΛ d : V}
    (hB : IsSemiformula L (es.length : V) B) (hes : ∀ e ∈ es, IsTerm L e)
    (hΓ : IsFormulaSet L Γ) (hsub : Γ₀ ⊆ Γ)
    (hΛ : Proof T dΛ (allsIter es.length B))
    (hd : DerivationOf T d (insert (neg L (instOuter L es B)) Γ₀)) :
    dlen T (useLemmaCode L Γ es B dΛ d) =
      setLen L Γ + (setLen L (insert (allsIter es.length B) Γ) + dlen T dΛ + 1)
        + dlen T (exsChainCode L es (neg L B) Γ d) + 1 := by
  have e₂ : DerivationOf T (exsChainCode L es (neg L B) Γ d) (insert (exsIter es.length (neg L B)) Γ) :=
    exsChainCode_proof es (by simpa using hB) hes hΓ hsub (by rw [instOuter_neg es hB hes]; exact hd)
  apply dlen_eq_of_graph (useLemmaCode_proof hB hes hΓ hsub hΛ hd).2
  unfold useLemmaCode
  exact DlenGraph.cutRule_iff.mpr ⟨_, _, DlenGraph.wkRule_iff.mpr ⟨_, dlen_graph hΛ.2, rfl⟩,
    dlen_graph e₂.2, rfl⟩

/-- **The bound for `useLemmaCode`** (`m = es.length`, `E ≥ 1` bounds every witness length,
`F ≥ |B|·E + m`):
`dlen ≤ dlen dΛ + dlen d + (m + 3)·|Γ| + |Λ| + (m + 1)²·F + m·E + m + 3`. -/
theorem dlen_useLemmaCode_le {E F : V} (hE : 1 ≤ E) {Γ Γ₀ : V} {es : List V} {B dΛ d : V}
    (hB : IsSemiformula L (es.length : V) B) (hes : ∀ e ∈ es, IsTerm L e ∧ termLen L e ≤ E)
    (hΓ : IsFormulaSet L Γ) (hsub : Γ₀ ⊆ Γ)
    (hΛ : Proof T dΛ (allsIter es.length B))
    (hd : DerivationOf T d (insert (neg L (instOuter L es B)) Γ₀))
    (hF : formulaLen L B * E + (es.length : V) ≤ F) :
    dlen T (useLemmaCode L Γ es B dΛ d) ≤
      dlen T dΛ + dlen T d + ((es.length : V) + 3) * setLen L Γ + formulaLen L (allsIter es.length B)
        + ((es.length : V) + 1) * ((es.length : V) + 1) * F + (es.length : V) * E
        + (es.length : V) + 3 := by
  have hes₁ : ∀ e ∈ es, IsTerm L e := fun e he ↦ (hes e he).1
  have hnB : IsSemiformula L (es.length : V) (neg L B) := by simpa using hB
  have hchain := dlen_exsChainCode_le (T := T) hE hnB es hnB hes hΓ hsub
    (by rw [instOuter_neg es hB hes₁]; exact hd) (isInstOf_self E _ _)
    (by simpa only [formulaLen_neg hB.isUFormula] using hF) (le_refl (setLen L Γ))
  rw [dlen_useLemmaCode hB hes₁ hΓ hsub hΛ hd]
  have hΛΓ : setLen L (insert (allsIter es.length B) Γ) ≤
      setLen L Γ + formulaLen L (allsIter es.length B) := setLen_insert_le _ _
  refine le_trans (add_le_add (add_le_add
    (add_le_add (le_refl _) (add_le_add (add_le_add hΛΓ (le_refl _)) (le_refl 1))) hchain) (le_refl 1))
    (le_of_eq ?_)
  ring

/-- The bound with `F := |B|·E + m` substituted and `|Λ| = |B| + m`:
`dlen ≤ dlen dΛ + dlen d + (m + 3)·|Γ| + (m + 1)²·(|B|·E + m) + |B| + m·E + 2m + 3`. -/
theorem dlen_useLemmaCode_le' {E : V} (hE : 1 ≤ E) {Γ Γ₀ : V} {es : List V} {B dΛ d : V}
    (hB : IsSemiformula L (es.length : V) B) (hes : ∀ e ∈ es, IsTerm L e ∧ termLen L e ≤ E)
    (hΓ : IsFormulaSet L Γ) (hsub : Γ₀ ⊆ Γ)
    (hΛ : Proof T dΛ (allsIter es.length B))
    (hd : DerivationOf T d (insert (neg L (instOuter L es B)) Γ₀)) :
    dlen T (useLemmaCode L Γ es B dΛ d) ≤
      dlen T dΛ + dlen T d + ((es.length : V) + 3) * setLen L Γ
        + ((es.length : V) + 1) * ((es.length : V) + 1) * (formulaLen L B * E + (es.length : V))
        + formulaLen L B + (es.length : V) * E + 2 * (es.length : V) + 3 := by
  refine le_trans (dlen_useLemmaCode_le hE hB hes hΓ hsub hΛ hd (le_refl _)) (le_of_eq ?_)
  rw [formulaLen_allsIter hB.isUFormula]
  ring

end chain

/-! ### Lengths under `shift` and `free` (free-variable indices are charged unary) -/

section shiftLen

lemma listSum_termLenVec_termShiftVec_le {k n v : V} (hv : IsSemitermVec L k n v)
    (ih : ∀ i < k, termLen L (termShift L v.[i]) ≤ 2 * termLen L v.[i]) :
    listSum (termLenVec L k (termShiftVec L k v)) ≤ 2 * listSum (termLenVec L k v) := by
  have hv' : IsUTermVec L k (termShiftVec L k v) := hv.termShiftVec.isUTerm
  have := listSum_le_mul (B := 2) (a := termLenVec L k (termShiftVec L k v)) (termLenVec L k v)
    (by rw [len_termLenVec hv', len_termLenVec hv.isUTerm]) (fun i hi ↦ by
      rw [len_termLenVec hv'] at hi
      rw [nth_termLenVec hv' hi, nth_termLenVec hv.isUTerm hi, nth_termShiftVec hv.isUTerm hi, mul_comm]
      exact ih i hi)
  rw [mul_comm] at this
  exact this

/-- `|termShift t| ≤ 2|t|` (each free variable `&x` becomes `&(x + 1)`, one more symbol). -/
lemma termLen_termShift_le {n t : V} (ht : IsSemiterm L n t) :
    termLen L (termShift L t) ≤ 2 * termLen L t := by
  apply IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z _
    rw [termShift_bvar, termLen_bvar]
    exact le_mul_of_one_le_left (by simp) one_le_two'
  · intro x
    rw [termShift_fvar, termLen_fvar, termLen_fvar]
    calc x + 1 + 1 ≤ (x + 1) + (x + 1) := add_le_add (le_refl _) le_add_self
      _ = 2 * (x + 1) := by ring
  · intro k f v hf hv ih
    have hv' : IsUTermVec L k (termShiftVec L k v) := hv.termShiftVec.isUTerm
    rw [termShift_func hf hv.isUTerm, termLen_func hf hv', termLen_func hf hv.isUTerm, mul_add, mul_one]
    exact add_le_add (listSum_termLenVec_termShiftVec_le hv ih) one_le_two'

/-- `|shift p| ≤ 2|p|`. -/
lemma formulaLen_shift_le {n p : V} (hp : IsSemiformula L n p) :
    formulaLen L (shift L p) ≤ 2 * formulaLen L p := by
  apply IsSemiformula.sigma1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv
    rw [shift_rel hR hv.isUTerm, formulaLen_rel hR hv.termShiftVec.isUTerm,
      formulaLen_rel hR hv.isUTerm, mul_add, mul_one]
    exact add_le_add (listSum_termLenVec_termShiftVec_le hv fun i hi ↦ termLen_termShift_le (hv.nth hi))
      one_le_two'
  · intro n k R v hR hv
    rw [shift_nrel hR hv.isUTerm, formulaLen_nrel hR hv.termShiftVec.isUTerm,
      formulaLen_nrel hR hv.isUTerm, mul_add, mul_one]
    exact add_le_add (listSum_termLenVec_termShiftVec_le hv fun i hi ↦ termLen_termShift_le (hv.nth hi))
      one_le_two'
  · intro n; rw [shift_verum, formulaLen_verum, mul_one]; exact one_le_two'
  · intro n; rw [shift_falsum, formulaLen_falsum, mul_one]; exact one_le_two'
  · intro n p q hp hq ihp ihq
    rw [shift_and hp.isUFormula hq.isUFormula, formulaLen_and hp.shift.isUFormula hq.shift.isUFormula,
      formulaLen_and hp.isUFormula hq.isUFormula]
    calc _ ≤ 2 * formulaLen L p + 2 * formulaLen L q + 2 := add_le_add (add_le_add ihp ihq) one_le_two'
      _ = 2 * (formulaLen L p + formulaLen L q + 1) := by ring
  · intro n p q hp hq ihp ihq
    rw [shift_or hp.isUFormula hq.isUFormula, formulaLen_or hp.shift.isUFormula hq.shift.isUFormula,
      formulaLen_or hp.isUFormula hq.isUFormula]
    calc _ ≤ 2 * formulaLen L p + 2 * formulaLen L q + 2 := add_le_add (add_le_add ihp ihq) one_le_two'
      _ = 2 * (formulaLen L p + formulaLen L q + 1) := by ring
  · intro n p hp ih
    rw [shift_all hp.isUFormula, formulaLen_all hp.shift.isUFormula, formulaLen_all hp.isUFormula]
    calc _ ≤ 2 * formulaLen L p + 2 := add_le_add ih one_le_two'
      _ = 2 * (formulaLen L p + 1) := by ring
  · intro n p hp ih
    rw [shift_exs hp.isUFormula, formulaLen_exs hp.shift.isUFormula, formulaLen_exs hp.isUFormula]
    calc _ ≤ 2 * formulaLen L p + 2 := add_le_add ih one_le_two'
      _ = 2 * (formulaLen L p + 1) := by ring

/-- `|free p| ≤ 2|p|` (`free p = (shift p)[#0 := &0]`, a one-symbol term for a one-symbol variable). -/
lemma formulaLen_free_le {p : V} (hp : IsSemiformula L 1 p) :
    formulaLen L (free L p) ≤ 2 * formulaLen L p := by
  have h1 : formulaLen L (subst L (^&0 ∷ (0 : V)) (shift L p)) ≤ formulaLen L (shift L p) * 1 :=
    formulaLen_subst_le (le_refl 1) hp.shift 0 (^&0 ∷ (0 : V)) (by simp)
      (substInv_single (by simp) (by simp))
  rw [mul_one] at h1
  exact le_trans h1 (formulaLen_shift_le hp)

/-- `setLen (setShift s) ≤ 2·setLen s` for a set of formulas (`insert` induction on the bit-set). -/
lemma setLen_setShift_le {s : V} (hs : IsFormulaSet L s) :
    setLen L (setShift L s) ≤ 2 * setLen L s := by
  refine insert_induction_piOne (P := fun s ↦ IsFormulaSet L s → setLen L (setShift L s) ≤ 2 * setLen L s)
    ?_ ?_ ?_ s hs
  · definability
  · intro _; simp
  · intro a s ha ih hs
    have hs' : IsFormulaSet L s := (IsFormulaSet.insert_iff.mp hs).2
    have ha' : IsFormula L a := (IsFormulaSet.insert_iff.mp hs).1
    rw [mem_setShift_insert, setLen_insert_of_not_mem_V ha, mul_add]
    exact le_trans (setLen_insert_le _ _) (add_le_add (ih hs') (formulaLen_shift_le ha'))

/-- `free (∼p) = ∼(free p)`. -/
lemma free_neg {p : V} (hp : IsSemiformula L 1 p) : free L (neg L p) = neg L (free L p) := by
  unfold free
  rw [shift_neg hp, substs1_neg_code hp.shift (by simp)]

end shiftLen

/-! ### Primitive 2 — `elimExistsCode`, and `wkDropCode` -/

section elim

variable {T : Theory L} [T.Δ₁]

variable (L) in
/-- **Eliminate an existential with a fresh eigenvariable.** From `D` deriving `insert (∃ P) Δ`
(`Δ ⊆ Γ`) and a continuation `d` deriving `insert (neg (free P)) (setShift Γ)` — the goal under
the hypothesis `P(&0)`, every free variable of `Γ` shifted — a derivation of `Γ`: cut on `∃ P`;
premise (a) `D` weakened; premise (b) `insert (∀ ∼P) Γ` by `allIntro`, whose premise
`insert (free (∼P)) (setShift (insert (∀ ∼P) Γ))` is `d` weakened (`free_neg`). -/
noncomputable def elimExistsCode (Γ P D d : V) : V :=
  cutRule Γ (^∃ P)
    (wkRule (insert (^∃ P) Γ) D)
    (allIntro (insert (^∀ neg L P) Γ) (neg L P)
      (wkRule (insert (free L (neg L P)) (setShift L (insert (^∀ neg L P) Γ))) d))

/-- `elimExistsCode` derives `Γ`. -/
theorem elimExistsCode_proof {Γ Δ P D d : V} (hP : IsSemiformula L 1 P) (hΓ : IsFormulaSet L Γ)
    (hΔ : Δ ⊆ Γ) (hD : DerivationOf T D (insert (^∃ P) Δ))
    (hd : DerivationOf T d (insert (neg L (free L P)) (setShift L Γ))) :
    DerivationOf T (elimExistsCode L Γ P D d) Γ := by
  have hE : IsFormula L (^∃ P) := by simp [hP]
  have hA : IsFormula L (^∀ neg L P) := by simp [hP]
  have e₁ : DerivationOf T (wkRule (insert (^∃ P) Γ) D) (insert (^∃ P) Γ) :=
    ⟨by simp, Derivation.wkRule (by simp [hE, hΓ]) (insert_subset_insert_of_subset _ hΔ) hD⟩
  have e₃ : DerivationOf T (wkRule (insert (free L (neg L P)) (setShift L (insert (^∀ neg L P) Γ))) d)
      (insert (free L (neg L P)) (setShift L (insert (^∀ neg L P) Γ))) := by
    refine ⟨by simp, Derivation.wkRule ?_ ?_ hd⟩
    · simp [hP, hΓ]
    · rw [free_neg hP, mem_setShift_insert]
      exact insert_subset_insert_of_subset _ (subset_insert_of_subset _ (subset_refl _))
  have e₂ : DerivationOf T (allIntro (insert (^∀ neg L P) Γ) (neg L P)
      (wkRule (insert (free L (neg L P)) (setShift L (insert (^∀ neg L P) Γ))) d))
      (insert (^∀ neg L P) Γ) :=
    ⟨by simp, Derivation.allIntro (by simp) e₃⟩
  refine ⟨by simp [elimExistsCode], Derivation.cutRule e₁ ?_⟩
  rw [neg_ex hP.isUFormula]
  exact e₂

/-- The exact length of `elimExistsCode`, node by node. -/
theorem dlen_elimExistsCode {Γ Δ P D d : V} (hP : IsSemiformula L 1 P) (hΓ : IsFormulaSet L Γ)
    (hΔ : Δ ⊆ Γ) (hD : DerivationOf T D (insert (^∃ P) Δ))
    (hd : DerivationOf T d (insert (neg L (free L P)) (setShift L Γ))) :
    dlen T (elimExistsCode L Γ P D d) =
      setLen L Γ + (setLen L (insert (^∃ P) Γ) + dlen T D + 1)
      + (setLen L (insert (^∀ neg L P) Γ)
          + (setLen L (insert (free L (neg L P)) (setShift L (insert (^∀ neg L P) Γ))) + dlen T d + 1)
          + 1)
      + 1 := by
  apply dlen_eq_of_graph (elimExistsCode_proof hP hΓ hΔ hD hd).2
  unfold elimExistsCode
  refine DlenGraph.cutRule_iff.mpr ⟨_, _, DlenGraph.wkRule_iff.mpr ⟨_, dlen_graph hD.2, rfl⟩, ?_, rfl⟩
  exact DlenGraph.allIntro_iff.mpr ⟨_, DlenGraph.wkRule_iff.mpr ⟨_, dlen_graph hd.2, rfl⟩, rfl⟩

/-- **The bound for `elimExistsCode`**, with the shifted context explicit:
`dlen ≤ dlen D + dlen d + 3·|Γ| + |setShift Γ| + 6|P| + 8`. -/
theorem dlen_elimExistsCode_le {Γ Δ P D d : V} (hP : IsSemiformula L 1 P) (hΓ : IsFormulaSet L Γ)
    (hΔ : Δ ⊆ Γ) (hD : DerivationOf T D (insert (^∃ P) Δ))
    (hd : DerivationOf T d (insert (neg L (free L P)) (setShift L Γ))) :
    dlen T (elimExistsCode L Γ P D d) ≤
      dlen T D + dlen T d + 3 * setLen L Γ + setLen L (setShift L Γ) + 6 * formulaLen L P + 8 := by
  have hP' := hP.isUFormula
  have hA : IsSemiformula L 0 (^∀ neg L P) := by simp [hP]
  have h₁ : setLen L (insert (^∃ P) Γ) ≤ setLen L Γ + (formulaLen L P + 1) := by
    have := setLen_insert_le (L := L) (^∃ P) Γ
    rwa [formulaLen_exs hP'] at this
  have h₂ : setLen L (insert (^∀ neg L P) Γ) ≤ setLen L Γ + (formulaLen L P + 1) := by
    have := setLen_insert_le (L := L) (^∀ neg L P) Γ
    rwa [formulaLen_all hP'.neg, formulaLen_neg hP'] at this
  have hsh : formulaLen L (shift L (^∀ neg L P)) ≤ 2 * (formulaLen L P + 1) := by
    have := formulaLen_shift_le hA
    rwa [formulaLen_all hP'.neg, formulaLen_neg hP'] at this
  have hfr : formulaLen L (free L (neg L P)) ≤ 2 * formulaLen L P := by
    rw [free_neg hP, formulaLen_neg hP.free.isUFormula]
    exact formulaLen_free_le hP
  have h₃ : setLen L (insert (free L (neg L P)) (setShift L (insert (^∀ neg L P) Γ))) ≤
      setLen L (setShift L Γ) + 2 * (formulaLen L P + 1) + 2 * formulaLen L P := by
    rw [mem_setShift_insert]
    calc setLen L (insert (free L (neg L P)) (insert (shift L (^∀ neg L P)) (setShift L Γ)))
        ≤ setLen L (insert (shift L (^∀ neg L P)) (setShift L Γ)) + formulaLen L (free L (neg L P)) :=
          setLen_insert_le _ _
      _ ≤ (setLen L (setShift L Γ) + formulaLen L (shift L (^∀ neg L P))) + formulaLen L (free L (neg L P)) :=
          add_le_add (setLen_insert_le _ _) (le_refl _)
      _ ≤ setLen L (setShift L Γ) + 2 * (formulaLen L P + 1) + 2 * formulaLen L P :=
          add_le_add (add_le_add (le_refl _) hsh) hfr
  rw [dlen_elimExistsCode hP hΓ hΔ hD hd]
  calc setLen L Γ + (setLen L (insert (^∃ P) Γ) + dlen T D + 1)
      + (setLen L (insert (^∀ neg L P) Γ)
          + (setLen L (insert (free L (neg L P)) (setShift L (insert (^∀ neg L P) Γ))) + dlen T d + 1)
          + 1)
      + 1
      ≤ setLen L Γ + ((setLen L Γ + (formulaLen L P + 1)) + dlen T D + 1)
      + ((setLen L Γ + (formulaLen L P + 1))
          + ((setLen L (setShift L Γ) + 2 * (formulaLen L P + 1) + 2 * formulaLen L P) + dlen T d + 1)
          + 1)
      + 1 := by gcongr
    _ = dlen T D + dlen T d + 3 * setLen L Γ + setLen L (setShift L Γ) + 6 * formulaLen L P + 8 := by ring

/-- The bound with the shift absorbed (`setLen_setShift_le`):
`dlen ≤ dlen D + dlen d + 5·|Γ| + 6|P| + 8`. -/
theorem dlen_elimExistsCode_le' {Γ Δ P D d : V} (hP : IsSemiformula L 1 P) (hΓ : IsFormulaSet L Γ)
    (hΔ : Δ ⊆ Γ) (hD : DerivationOf T D (insert (^∃ P) Δ))
    (hd : DerivationOf T d (insert (neg L (free L P)) (setShift L Γ))) :
    dlen T (elimExistsCode L Γ P D d) ≤
      dlen T D + dlen T d + 5 * setLen L Γ + 6 * formulaLen L P + 8 := by
  refine le_trans (dlen_elimExistsCode_le hP hΓ hΔ hD hd) ?_
  have := setLen_setShift_le hΓ
  calc dlen T D + dlen T d + 3 * setLen L Γ + setLen L (setShift L Γ) + 6 * formulaLen L P + 8
      ≤ dlen T D + dlen T d + 3 * setLen L Γ + 2 * setLen L Γ + 6 * formulaLen L P + 8 := by gcongr
    _ = dlen T D + dlen T d + 5 * setLen L Γ + 6 * formulaLen L P + 8 := by ring

/-- **Drop facts**: one weakening. -/
noncomputable def wkDropCode (Γ d : V) : V := wkRule Γ d

theorem wkDropCode_proof {Γ Γ' d : V} (hΓ : IsFormulaSet L Γ) (h : Γ' ⊆ Γ)
    (hd : DerivationOf T d Γ') : DerivationOf T (wkDropCode Γ d) Γ :=
  ⟨by simp [wkDropCode], Derivation.wkRule hΓ h hd⟩

theorem dlen_wkDropCode {Γ Γ' d : V} (hΓ : IsFormulaSet L Γ) (h : Γ' ⊆ Γ)
    (hd : DerivationOf T d Γ') : dlen T (wkDropCode Γ d) = setLen L Γ + dlen T d + 1 :=
  dlen_eq_of_graph (wkDropCode_proof hΓ h hd).2 (DlenGraph.wkRule_iff.mpr ⟨_, dlen_graph hd.2, rfl⟩)

theorem dlen_wkDropCode_le {Γ Γ' d : V} (hΓ : IsFormulaSet L Γ) (h : Γ' ⊆ Γ)
    (hd : DerivationOf T d Γ') : dlen T (wkDropCode Γ d) ≤ dlen T d + setLen L Γ + 1 := by
  rw [dlen_wkDropCode hΓ h hd, add_comm (setLen L Γ)]

end elim

end ArithS
