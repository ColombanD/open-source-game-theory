import ArithS.RedCell
import ArithS.ProofLength

/-!
# ArithS.Fit — the guard sentence FITS inside its own budget (Critch's assumption (b))

Critch fixes his proof system `S` only up to four assumptions (Appendix B of `critch22`);
assumption **(b)** is that `S` "writes `k` in `O(lg k)` characters". Under Foundation's
UNARY numerals this failed so badly that the bounded proof search of every agent was
vacuous — the retired `Vacuity.lean` (commit 470ee43) PROVED it: a search node
`pSearch k g p q` stores its budget `k` in its own pair-code, so the canonical numeral by
which the guard sentence names the searcher is `≥ k`; unary numerals cost `~ 2n` symbols;
every instance of the template is longer than that numeral; a derivation is at least as
long as its conclusion; hence `search_never_found`: the guard is never found at ANY budget,
`Dupoc k` always defects and `Cupod k` always cooperates, against EVERY opponent, and the
red cell held for a reason unrelated to symmetry.

Since the descriptions are BINARY numeral terms (`ArithS.Bnum`, `ArithS.Guard`), this file
proves the POSITIVE result that (b) demands, with explicit (ugly, but explicit) constants:

* `flen_subst_le`: a substitution instance `φ ⇜ w` of a template is at most `flen φ` times
  the total length of the substituted closed terms (plus one) — via `flen_rew_le`, a bound
  for every rewriter whose bound-variable images are variable-free or bare bound variables
  (the invariant that survives `Rew.q` under a quantifier);
* `exists_guard_const`: `∃ c, flen (guardSentenceA a me opp) ≤ 10c + 6c · (size (dnum me) +
  size (dnum opp))` for the actions `a ≤ 1`, with `c = cG 0 + cG 1`, `cG a = flen (GtmplA a)`
  the symbol counts of the two closed template instances, packaged existentially
  (`flen_guardSentence_le'` is the per-instance form);
* `size_dnum_Dupoc_le`: `size (dnum (Dupoc k)) ≤ 4 · size k + (4 · size cP + 26)`, by the
  Cantor-pairing bound `⟪a, b⟫ ≤ (a + b + 1)²` (`cP = ⟪⌜GtmplA 0⌝, pConst 0, pConst 1⟫` is
  the constant part of the searcher's code);
* **`guard_fits`**: `∃ K, ∀ k ≥ K, ∀ a ≤ 1, flen (guardSentenceA a (Dupoc k) (Cupod k)) ≤ k`
  (and `guard_fits'` with the roles swapped) — for all large budgets the searcher's own
  guard sentence fits inside its budget: the model is no longer degenerate, and whether the
  guard is actually PROVABLE within `k` becomes a genuine question (T3's).
-/

/-!
## Proof-craft note (2026-09-10)
The first version of this file hung for hours: a theorem stated with closed constants
(`10 * cG₀`, `Nat.size cP`) forced Lean's `Nat` defeq machinery to try to EVALUATE
`cG₀ = flen Gtmpl` and `cP = ⟪⌜Gtmpl⌝, …⟫` on the giant template term. The cure is
structural: the constants are packaged EXISTENTIALLY (`exists_guard_const`,
`exists_size_const`) and every arithmetic step is over variables. `Vacuity.lean`
(commit 470ee43) is retired because its theorems are false for the binary descriptions.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct


/-! ### 1. Length of a substitution instance -/

section rewriter

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- The term has no bound variable. -/
def BvFree {ξ : Type*} {n : ℕ} : Semiterm L ξ n → Prop
  | #_ => False
  | &_ => True
  | .func _ v => ∀ i, BvFree (v i)

@[simp] lemma bvFree_bvar {ξ : Type*} {n : ℕ} (x : Fin n) : ¬ BvFree (#x : Semiterm L ξ n) := by
  simp [BvFree]
@[simp] lemma bvFree_fvar {ξ : Type*} {n : ℕ} (x : ξ) : BvFree (&x : Semiterm L ξ n) := by
  simp [BvFree]
@[simp] lemma bvFree_func {ξ : Type*} {n k : ℕ} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    BvFree (Semiterm.func f v) ↔ ∀ i, BvFree (v i) := by simp [BvFree]

lemma BvFree.bShift {n : ℕ} : ∀ {t : SyntacticSemiterm L n}, BvFree t → BvFree (Rew.bShift t)
  | #x, h => absurd h (bvFree_bvar x)
  | &x, _ => by rw [Rew.bShift_fvar]; exact bvFree_fvar x
  | .func f v, h => by
    rw [Rew.func, bvFree_func]
    exact fun i ↦ BvFree.bShift ((bvFree_func f v).mp h i)

lemma tlen_bShift_of_bvFree {n : ℕ} :
    ∀ {t : SyntacticSemiterm L n}, BvFree t → tlen (Rew.bShift t) = tlen t
  | #x, h => absurd h (bvFree_bvar x)
  | &x, _ => by rw [Rew.bShift_fvar]; rfl
  | .func f v, h => by
    rw [Rew.func, tlen_func, tlen_func]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ tlen_bShift_of_bvFree ((bvFree_func f v).mp h i)

/-- The embedding of a closed term has no bound variable. -/
lemma bvFree_emb : ∀ t : ClosedSemiterm L 0, BvFree (Rew.emb t : SyntacticSemiterm L 0)
  | #x => x.elim0
  | &x => x.elim
  | .func f v => by
    rw [Rew.func, bvFree_func]
    exact fun i ↦ bvFree_emb (v i)

/-- `ω` sends every bound variable either to a variable-free term of length `≤ B` or to a
bound variable of index at most its own, and fixes the free variables. This is the invariant
`Rew.q` preserves under a quantifier. -/
def RewBounded {n m : ℕ} (B : ℕ) (ω : Rew L ℕ n ℕ m) : Prop :=
  (∀ i : Fin n, (BvFree (ω #i) ∧ tlen (ω #i) ≤ B) ∨ (∃ j : Fin m, ω #i = #j ∧ (j : ℕ) ≤ i)) ∧
  (∀ x : ℕ, ω &x = &x)

lemma RewBounded.q {n m B : ℕ} {ω : Rew L ℕ n ℕ m} (h : RewBounded B ω) : RewBounded B ω.q := by
  refine ⟨fun i ↦ ?_, fun x ↦ by rw [Rew.q_fvar, h.2, Rew.bShift_fvar]⟩
  cases i using Fin.cases with
  | zero => exact Or.inr ⟨0, Rew.q_bvar_zero ω, le_rfl⟩
  | succ i =>
    rw [Rew.q_bvar_succ]
    rcases h.1 i with ⟨hf, hl⟩ | ⟨j, hj, hle⟩
    · exact Or.inl ⟨hf.bShift, by rw [tlen_bShift_of_bvFree hf]; exact hl⟩
    · exact Or.inr ⟨j.succ, by rw [hj, Rew.bShift_bvar],
        by rw [Fin.val_succ, Fin.val_succ]; exact Nat.succ_le_succ hle⟩

/-- A bounded rewriter at most multiplies the length of a term by `B`. -/
lemma tlen_rew_le {n m B : ℕ} (hB : 1 ≤ B) {ω : Rew L ℕ n ℕ m} (h : RewBounded B ω) :
    ∀ t : SyntacticSemiterm L n, tlen (ω t) ≤ tlen t * B
  | #i => by
    rcases h.1 i with ⟨_, hl⟩ | ⟨j, hj, hle⟩
    · rw [tlen_bvar]; exact le_trans hl (Nat.le_mul_of_pos_left B (Nat.succ_pos _))
    · rw [hj, tlen_bvar, tlen_bvar]
      exact le_trans (Nat.succ_le_succ hle) (Nat.le_mul_of_pos_right _ hB)
  | &x => by rw [h.2, tlen_fvar]; exact Nat.le_mul_of_pos_right _ hB
  | .func f v => by
    rw [Rew.func, tlen_func, tlen_func, add_mul, one_mul, Finset.sum_mul]
    exact Nat.add_le_add (Finset.sum_le_sum fun i _ ↦ tlen_rew_le hB h (v i)) hB

/-- A bounded rewriter at most multiplies the length of a formula by `B`. -/
theorem flen_rew_le {B : ℕ} (hB : 1 ≤ B) {n : ℕ} (φ : Semiproposition L n) :
    ∀ {m : ℕ} (ω : Rew L ℕ n ℕ m), RewBounded B ω → flen (ω ▹ φ) ≤ flen φ * B := by
  induction φ with
  | verum =>
    intro m ω _
    show flen (ω ▹ (⊤ : Semiproposition L _)) ≤ flen (⊤ : Semiproposition L _) * B
    rw [LogicalConnective.HomClass.map_top, flen_verum, flen_verum, one_mul]
    exact hB
  | falsum =>
    intro m ω _
    show flen (ω ▹ (⊥ : Semiproposition L _)) ≤ flen (⊥ : Semiproposition L _) * B
    rw [LogicalConnective.HomClass.map_bot, flen_falsum, flen_falsum, one_mul]
    exact hB
  | rel R v =>
    intro m ω h
    rw [Semiformula.rew_rel, flen_rel, flen_rel, add_mul, one_mul, Finset.sum_mul]
    exact Nat.add_le_add (Finset.sum_le_sum fun i _ ↦ tlen_rew_le hB h (v i)) hB
  | nrel R v =>
    intro m ω h
    rw [Semiformula.rew_nrel, flen_nrel, flen_nrel, add_mul, one_mul, Finset.sum_mul]
    exact Nat.add_le_add (Finset.sum_le_sum fun i _ ↦ tlen_rew_le hB h (v i)) hB
  | and φ ψ ihφ ihψ =>
    intro m ω h
    show flen (ω ▹ (φ ⋏ ψ)) ≤ flen (φ ⋏ ψ) * B
    rw [LogicalConnective.HomClass.map_and, flen_and, flen_and, add_mul, add_mul, one_mul]
    have h1 := ihφ ω h
    have h2 := ihψ ω h
    omega
  | or φ ψ ihφ ihψ =>
    intro m ω h
    show flen (ω ▹ (φ ⋎ ψ)) ≤ flen (φ ⋎ ψ) * B
    rw [LogicalConnective.HomClass.map_or, flen_or, flen_or, add_mul, add_mul, one_mul]
    have h1 := ihφ ω h
    have h2 := ihψ ω h
    omega
  | all φ ih =>
    intro m ω h
    show flen (ω ▹ (∀¹ φ)) ≤ flen (∀¹ φ) * B
    rw [Rewriting.app_all, flen_all, flen_all, add_mul, one_mul]
    have h1 := ih ω.q h.q
    omega
  | exs φ ih =>
    intro m ω h
    show flen (ω ▹ (∃¹ φ)) ≤ flen (∃¹ φ) * B
    rw [Rewriting.app_exs, flen_exs, flen_exs, add_mul, one_mul]
    have h1 := ih ω.q h.q
    omega

/-- A substitution of closed terms is bounded by their total length (plus one). -/
lemma rewBounded_subst {k : ℕ} (w : Fin k → ClosedSemiterm L 0) :
    RewBounded (∑ i, tlen (Rew.emb (w i) : SyntacticSemiterm L 0) + 1)
      (Rew.subst fun i ↦ (Rew.emb (w i) : SyntacticSemiterm L 0)) := by
  refine ⟨fun i ↦ Or.inl ⟨?_, ?_⟩, fun x ↦ Rew.subst_fvar _ x⟩
  · rw [Rew.subst_bvar]; exact bvFree_emb (w i)
  · rw [Rew.subst_bvar]
    exact le_trans
      (Finset.single_le_sum (f := fun i ↦ tlen (Rew.emb (w i) : SyntacticSemiterm L 0))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i))
      (Nat.le_succ _)

/-- **Length of a substitution instance**: at most the template's length times the total
length of the substituted closed terms (plus one). -/
theorem flen_subst_le {k : ℕ} (φ : Semisentence L k) (w : Fin k → ClosedSemiterm L 0) :
    flen (Rewriting.emb (φ ⇜ w) : Proposition L) ≤
    flen (Rewriting.emb φ : Semiproposition L k) *
      (∑ i, tlen (Rew.emb (w i) : SyntacticSemiterm L 0) + 1) := by
  rw [Semiformula.coe_subst_eq_subst_coe]
  exact flen_rew_le (Nat.succ_pos _) _ _ (rewBounded_subst w)

end rewriter

/-! ### 2. The lengths of the description terms -/

section descriptions

lemma tlen_emb_lMap_emb (t : ClosedSemiterm ℒₒᵣ 0) :
    tlen (Rew.emb (Semiterm.lMap emb t) : SyntacticSemiterm LAct 0) =
    tlen (Rew.emb t : SyntacticSemiterm ℒₒᵣ 0) := by
  rw [term_emb_lMap_emb, tlen_lMap]

/-- The binary canonical numeral of `x` costs `O(size (dnum x))` symbols. -/
lemma tlen_emb_dnumT (x : ℕ) :
    tlen (Rew.emb (dnumT x) : SyntacticSemiterm LAct 0) ≤ 6 * Nat.size (dnum x) + 1 := by
  unfold dnumT
  rw [tlen_emb_lMap_emb]
  exact tlen_bnumT _

lemma tlen_emb_cterm (a : Act) :
    tlen (Rew.emb (cterm a : ClosedSemiterm LAct 0) : SyntacticSemiterm LAct 0) = 1 := by
  simp [cterm, Rew.func]

lemma numeral_operator_add_two {m : ℕ} (k : ℕ) :
    ((Semiterm.Operator.numeral ℒₒᵣ (k + 2)).operator ![] : SyntacticSemiterm ℒₒᵣ m) =
    Semiterm.Operator.Add.add.operator
      ![(Semiterm.Operator.numeral ℒₒᵣ (k + 1)).operator ![], (Semiterm.Operator.One.one).operator ![]] := by
  rw [Semiterm.Operator.numeral_add_two, Semiterm.Operator.operator_comp]
  congr 1
  funext i; fin_cases i <;> rfl

/-- The unary numeral `k` has at most `2k + 1` symbols. -/
lemma tlen_numeral_operator_le {m : ℕ} :
    ∀ k : ℕ, tlen ((Semiterm.Operator.numeral ℒₒᵣ k).operator ![] : SyntacticSemiterm ℒₒᵣ m) ≤ 2 * k + 1
  | 0 => by rw [Semiterm.Operator.numeral_zero, tlen_zero_operator]
  | 1 => by rw [Semiterm.Operator.numeral_one, tlen_one_operator]; omega
  | k + 2 => by
    rw [numeral_operator_add_two, tlen_add_operator]
    have := tlen_numeral_operator_le (m := m) (k + 1)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, tlen_one_operator]
    omega

lemma tlen_emb_numT_le (k : ℕ) : tlen (Rew.emb (numT k) : SyntacticSemiterm LAct 0) ≤ 2 * k + 1 := by
  unfold numT
  rw [tlen_emb_lMap_emb]
  have e : (Rew.emb (↑k : ClosedSemiterm ℒₒᵣ 0) : SyntacticSemiterm ℒₒᵣ 0) = ↑k := by simp
  rw [e]
  exact tlen_numeral_operator_le k

lemma tlen_emb_numT_zero : tlen (Rew.emb (numT 0) : SyntacticSemiterm LAct 0) = 1 := by
  unfold numT
  rw [tlen_emb_lMap_emb]
  exact tlen_emb_closed_zero

lemma tlen_emb_numT_one : tlen (Rew.emb (numT 1) : SyntacticSemiterm LAct 0) = 1 := by
  unfold numT
  rw [tlen_emb_lMap_emb]
  exact tlen_emb_closed_one

lemma tlen_emb_dUT (x : ℕ) : tlen (Rew.emb (dUT x) : SyntacticSemiterm LAct 0) ≤ 1 := by
  unfold dUT
  split_ifs
  · rw [tlen_emb_cterm]
  · rw [tlen_emb_cterm]
  · rw [tlen_emb_numT_zero]

lemma tlen_emb_dWT (x : ℕ) : tlen (Rew.emb (dWT x) : SyntacticSemiterm LAct 0) ≤ 1 := by
  unfold dWT
  split_ifs
  · rw [tlen_emb_cterm]
  · rw [tlen_emb_cterm]
  · rw [tlen_emb_numT_one]

lemma tlen_emb_actT (a : ℕ) : tlen (Rew.emb (actT a) : SyntacticSemiterm LAct 0) ≤ 2 * a + 1 := by
  unfold actT
  split_ifs
  · rw [tlen_emb_cterm]; omega
  · rw [tlen_emb_cterm]; omega
  · exact tlen_emb_numT_le a

/-- The total length of the six description terms. -/
theorem sum_tlen_descTerms_le (me opp : ℕ) :
    ∑ i, tlen (Rew.emb (descTerms me opp i) : SyntacticSemiterm LAct 0) ≤
    6 * (Nat.size (dnum me) + Nat.size (dnum opp)) + 6 := by
  have h0 := tlen_emb_dnumT me
  have h1 := tlen_emb_dUT me
  have h2 := tlen_emb_dWT me
  have h3 := tlen_emb_dnumT opp
  have h4 := tlen_emb_dUT opp
  have h5 := tlen_emb_dWT opp
  simp only [descTerms, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero]
  omega

end descriptions

/-! ### 3. The guard sentence is `O(size (dnum me) + size (dnum opp))` -/

/-- `cG a`: the symbol count of the closed template instance `GtmplA a`. -/
noncomputable def cG (a : ℕ) : ℕ := flen (Rewriting.emb (GtmplA a) : Semiproposition LAct 6)

/-- The per-instance bound. -/
theorem flen_guardSentence_le' (me opp a : ℕ) :
    flen (Rewriting.emb (guardSentenceA a me opp) : Proposition LAct) ≤
    cG a * (6 * (Nat.size (dnum me) + Nat.size (dnum opp)) + 7) :=
  le_trans (flen_subst_le (GtmplA a) (descTerms me opp))
    (Nat.mul_le_mul_left _ (by have := sum_tlen_descTerms_le me opp; omega))

/- `cG a` is a closed natural number built from the giant template; Lean's `Nat`-literal
defeq machinery would otherwise try to EVALUATE it (whnf of `flen` on the template) during
unification. From here on it is an atom. -/
attribute [irreducible] cG

/-- Abstract arithmetic behind `exists_guard_const`, over variables only. -/
lemma guard_bound_arith (c₀ c s : ℕ) (hc : c₀ ≤ c) :
    c₀ * (6 * s + 7) ≤ 10 * c + 6 * c * s := by
  calc c₀ * (6 * s + 7) ≤ c * (6 * s + 7) := Nat.mul_le_mul_right _ hc
    _ ≤ c * (6 * s + 10) := Nat.mul_le_mul_left _ (by omega)
    _ = 10 * c + 6 * c * s := by ring

/-- **The guard bound, with its constant packaged existentially**: for the actions `a ∈ {0, 1}`
the guard sentence of `me` against `opp` has at most `10c + 6c · (size (dnum me) + size (dnum opp))`
symbols, for the constant `c = cG 0 + cG 1` (the symbol counts of the two template instances).
The constant is never written into a closed arithmetic expression: Lean's `Nat` defeq machinery
would try to evaluate it (that is what `flen (GtmplA a)` on the giant template does), so every
later argument takes `c` as a variable from this statement. -/
theorem exists_guard_const : ∃ c : ℕ, ∀ me opp a : ℕ, a ≤ 1 →
    flen (Rewriting.emb (guardSentenceA a me opp) : Proposition LAct) ≤
    10 * c + 6 * c * (Nat.size (dnum me) + Nat.size (dnum opp)) :=
  ⟨cG 0 + cG 1, fun me opp a ha ↦ by
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl
    · exact le_trans (flen_guardSentence_le' me opp 0)
        (guard_bound_arith (cG 0) (cG 0 + cG 1) _ (Nat.le_add_right _ _))
    · exact le_trans (flen_guardSentence_le' me opp 1)
        (guard_bound_arith (cG 1) (cG 0 + cG 1) _ (Nat.le_add_left _ _))⟩

/-! ### 4. The bit length of a searcher's code is `O(size k)` -/

section size

lemma pair_le_sq (a b : ℕ) : ⟪a, b⟫ ≤ (a + b + 1) * (a + b + 1) := by
  unfold pair
  split_ifs with h
  · show b * b + a ≤ (a + b + 1) * (a + b + 1)
    nlinarith
  · show a * a + a + b ≤ (a + b + 1) * (a + b + 1)
    nlinarith

lemma size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, Nat.pow_add]
  calc a * b ≤ a * 2 ^ Nat.size b := Nat.mul_le_mul_left a (Nat.le_of_lt (Nat.lt_size_self b))
    _ < 2 ^ Nat.size a * 2 ^ Nat.size b :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (Nat.two_pow_pos _)

lemma size_add_le (a b : ℕ) : Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  rw [Nat.size_le, Nat.pow_succ, Nat.pow_add]
  calc a + b < 2 ^ Nat.size a + 2 ^ Nat.size b := Nat.add_lt_add (Nat.lt_size_self a) (Nat.lt_size_self b)
    _ ≤ 2 ^ Nat.size a * 2 ^ Nat.size b + 2 ^ Nat.size a * 2 ^ Nat.size b :=
        Nat.add_le_add (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
          (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
    _ = 2 ^ Nat.size a * 2 ^ Nat.size b * 2 := by ring

lemma size_succ_le (a : ℕ) : Nat.size (a + 1) ≤ Nat.size a + 2 := by
  have := size_add_le a 1
  rw [Nat.size_one] at this
  omega

/-- Cantor pairing at most doubles the bit length (plus a constant). -/
lemma size_pair_le (a b : ℕ) : Nat.size ⟪a, b⟫ ≤ 2 * (Nat.size a + Nat.size b) + 6 := by
  have h := Nat.size_le_size (pair_le_sq a b)
  have h1 := size_mul_le (a + b + 1) (a + b + 1)
  have h2 := size_add_le (a + b) 1
  have h3 := size_add_le a b
  rw [Nat.size_one] at h2
  omega

/-- The constant part of a searcher's code: `⟪⌜GtmplA 0⌝, pConst 0, pConst 1⟫`. -/
noncomputable def cP : ℕ := ⟪(⌜GtmplA 0⌝ : ℕ), pConst 0, pConst 1⟫

lemma Dupoc_eq (k : ℕ) : Dupoc k = ⟪6, k, cP⟫ + 1 := rfl

/- Same reason as for `cG₀`: never let `Nat.size cP` be evaluated. -/
attribute [irreducible] cP

/-- The canonical numeral of the orbit is at most the code. -/
lemma dnum_le_self (x : ℕ) : dnum x ≤ x := by
  rcases lt_trichotomy x (swapcode x) with h | h | h
  · exact le_of_eq (dnum_of_lt h)
  · exact le_of_eq (dnum_of_eq h)
  · rw [dnum_of_gt h]; exact Nat.le_of_lt h

theorem size_Dupoc_le (k : ℕ) : Nat.size (Dupoc k) ≤ 4 * Nat.size k + (4 * Nat.size cP + 26) := by
  rw [Dupoc_eq]
  have h1 := size_succ_le ⟪6, k, cP⟫
  have h2 := size_pair_le 6 ⟪k, cP⟫
  have h3 := size_pair_le k cP
  have h6 : Nat.size 6 ≤ 3 := Nat.size_le.mpr (by norm_num)
  omega

/-- **The description of `Dupoc k` has bit length `O(size k)`**: `A = 4`, `B = 4 · size cP + 26`. -/
theorem size_dnum_Dupoc_le (k : ℕ) :
    Nat.size (dnum (Dupoc k)) ≤ 4 * Nat.size k + (4 * Nat.size cP + 26) :=
  le_trans (Nat.size_le_size (dnum_le_self _)) (size_Dupoc_le k)

theorem size_dnum_Cupod_le (k : ℕ) :
    Nat.size (dnum (Cupod k)) ≤ 4 * Nat.size k + (4 * Nat.size cP + 26) := by
  rw [← swapcode_Dupoc, dnum_swapcode]
  exact size_dnum_Dupoc_le k

/-- The pairing constant of the searchers' codes, packaged existentially (same reason as
`exists_guard_const`: `Nat.size cP` must never sit inside a closed arithmetic term). -/
theorem exists_size_const : ∃ P : ℕ, ∀ k : ℕ,
    Nat.size (dnum (Dupoc k)) ≤ 4 * Nat.size k + P ∧ Nat.size (dnum (Cupod k)) ≤ 4 * Nat.size k + P :=
  ⟨4 * Nat.size cP + 26, fun k ↦ ⟨size_dnum_Dupoc_le k, size_dnum_Cupod_le k⟩⟩

end size

/-! ### 5. The guard fits: `C₀ + C₁ · size k ≤ k` for all large `k` -/

section fits

lemma mul_le_two_pow_pred (M : ℕ) : ∀ s, 2 * M + 2 ≤ s → M * s ≤ 2 ^ (s - 1) := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
    have h : M + 1 ≤ 2 ^ M := Nat.lt_two_pow_self
    have h2 : (M + 1) * (M + 1) ≤ 2 ^ M * 2 ^ M := Nat.mul_le_mul h h
    have e : 2 * M + 2 - 1 = M + M + 1 := by omega
    rw [e, Nat.pow_succ, Nat.pow_add]
    nlinarith
  | succ s hs ih =>
    have hM : M ≤ 2 ^ (s - 1) :=
      le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have e : s + 1 - 1 = (s - 1) + 1 := by omega
    rw [e, Nat.pow_succ]
    nlinarith

/-- A linear function of the bit length is eventually below the identity. -/
lemma exists_linear_size_le (C₀ C₁ : ℕ) : ∃ K, ∀ k ≥ K, C₀ + C₁ * Nat.size k ≤ k := by
  refine ⟨2 ^ (2 * (C₀ + C₁) + 2), fun k hk ↦ ?_⟩
  have hs : 2 * (C₀ + C₁) + 2 < Nat.size k := Nat.lt_size.mpr hk
  have h1 : (C₀ + C₁) * Nat.size k ≤ 2 ^ (Nat.size k - 1) := mul_le_two_pow_pred _ _ (by omega)
  have h2 : 2 ^ (Nat.size k - 1) ≤ k := Nat.lt_size.mp (by omega)
  have h3 : C₀ + C₁ * Nat.size k ≤ (C₀ + C₁) * Nat.size k := by
    rw [add_mul]
    exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ (by omega)) _
  omega

/-- **The guard fits inside the budget**: for all large `k`, the guard sentence that `Dupoc k`
searches for against `Cupod k` ("`Cupod k` plays `a` against me") has at most `k` symbols —
Critch's assumption (b) holds for the binary descriptions. The threshold `K` depends only on
the fixed template. -/
theorem guard_fits :
    ∃ K, ∀ k ≥ K, ∀ a ≤ 1,
      flen (Rewriting.emb (guardSentenceA a (Dupoc k) (Cupod k)) : Proposition LAct) ≤ k := by
  obtain ⟨c, hc⟩ := exists_guard_const
  obtain ⟨P, hP⟩ := exists_size_const
  obtain ⟨K, hK⟩ := exists_linear_size_le (10 * c + 12 * c * P) (48 * c)
  refine ⟨K, fun k hk a ha ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hP k
  have h5 : 6 * c * (Nat.size (dnum (Dupoc k)) + Nat.size (dnum (Cupod k))) ≤
      6 * c * (8 * Nat.size k + 2 * P) := Nat.mul_le_mul_left _ (by omega)
  calc flen (Rewriting.emb (guardSentenceA a (Dupoc k) (Cupod k)) : Proposition LAct)
      ≤ 10 * c + 6 * c * (Nat.size (dnum (Dupoc k)) + Nat.size (dnum (Cupod k))) := hc _ _ a ha
    _ ≤ 10 * c + 6 * c * (8 * Nat.size k + 2 * P) := Nat.add_le_add_left h5 _
    _ = 10 * c + 12 * c * P + 48 * c * Nat.size k := by ring
    _ ≤ k := hK k hk

/-- The same with the roles swapped: `Cupod k`'s guard against `Dupoc k` fits. -/
theorem guard_fits' :
    ∃ K, ∀ k ≥ K, ∀ a ≤ 1,
      flen (Rewriting.emb (guardSentenceA a (Cupod k) (Dupoc k)) : Proposition LAct) ≤ k := by
  obtain ⟨c, hc⟩ := exists_guard_const
  obtain ⟨P, hP⟩ := exists_size_const
  obtain ⟨K, hK⟩ := exists_linear_size_le (10 * c + 12 * c * P) (48 * c)
  refine ⟨K, fun k hk a ha ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hP k
  have h5 : 6 * c * (Nat.size (dnum (Cupod k)) + Nat.size (dnum (Dupoc k))) ≤
      6 * c * (8 * Nat.size k + 2 * P) := Nat.mul_le_mul_left _ (by omega)
  calc flen (Rewriting.emb (guardSentenceA a (Cupod k) (Dupoc k)) : Proposition LAct)
      ≤ 10 * c + 6 * c * (Nat.size (dnum (Cupod k)) + Nat.size (dnum (Dupoc k))) := hc _ _ a ha
    _ ≤ 10 * c + 6 * c * (8 * Nat.size k + 2 * P) := Nat.add_le_add_left h5 _
    _ = 10 * c + 12 * c * P + 48 * c * Nat.size k := by ring
    _ ≤ k := hK k hk

end fits

end ArithS
