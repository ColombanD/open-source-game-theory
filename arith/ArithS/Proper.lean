import ArithS.MetaLength
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# ArithS.Proper — properness: a derivation of length `k` has code below a tower in `k`

Meta-level (`V = ℕ`) numeric estimate on Foundation's coding (roadmap M1, last item).
Codes are built by `Nat.pair` (`⟪a, b⟫ = Nat.pair a b` on ℕ, `< (max a b + 1)^2`) and,
for sequents, by bit-sets `∑ 2^⌜φ⌝`. Two towers absorb these:

* `E s = 2^(2^s)`: closed under pairing at the cost of two levels
  (`a, b ≤ E s → ⟪a, b⟫ + 1 ≤ E (s + 2)`); bounds term and formula codes by `E (8·len)`.
* `F s = 2^(2^(2^s))`: same closure, and `2^(E s + 1) ≤ F (s + 1)` absorbs one bit-set;
  bounds sequent codes by `F (8·sqlen + 1)` and derivation codes by `F (12·mlen)`.

Hence `Proper` holds for `f k := F (12 k)`, which is Σ₁-definable via three `Exp.exp`s.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping

/-! ### The towers -/

def E (s : ℕ) : ℕ := 2 ^ (2 ^ s)
def F (s : ℕ) : ℕ := 2 ^ (2 ^ (2 ^ s))

lemma E_pos (s : ℕ) : 0 < E s := by unfold E; positivity
lemma two_le_E (s : ℕ) : 2 ≤ E s := by
  unfold E
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ s) := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_two_pow)
lemma E_mono {s t : ℕ} (h : s ≤ t) : E s ≤ E t :=
  Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)
lemma E_add_two (s : ℕ) : E (s + 2) = E s ^ 4 := by
  unfold E; rw [← pow_mul]; congr 1; rw [pow_add]; ring
lemma le_E (s : ℕ) : s ≤ E s := by
  unfold E
  exact le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_right (by norm_num) (Nat.lt_two_pow_self).le)

lemma F_pos (s : ℕ) : 0 < F s := by unfold F; positivity
lemma two_le_F (s : ℕ) : 2 ≤ F s := by
  unfold F
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ (2 ^ s)) := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_two_pow)
lemma F_mono {s t : ℕ} (h : s ≤ t) : F s ≤ F t :=
  Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) h))
lemma E_le_F (s : ℕ) : E s ≤ F s :=
  Nat.pow_le_pow_right (by norm_num) (Nat.lt_two_pow_self).le
lemma F_add_two (s : ℕ) : F s ^ 4 ≤ F (s + 2) := by
  unfold F
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  calc 2 ^ (2 ^ s) * 4 = 2 ^ (2 ^ s + 2) := by rw [pow_add]; norm_num
    _ ≤ 2 ^ (2 ^ (s + 2)) := Nat.pow_le_pow_right (by norm_num) (by
        rw [pow_add]; have := Nat.one_le_two_pow (n := s); omega)

/-- `(x + 1)^2 + 1 ≤ x^4` for `x ≥ 2`. -/
private lemma sq_succ_succ_le_pow_four {x : ℕ} (hx : 2 ≤ x) : (x + 1) ^ 2 + 1 ≤ x ^ 4 := by
  nlinarith [Nat.pow_le_pow_left hx 2, Nat.pow_le_pow_left hx 3]

/-- Pairing costs two tower levels. -/
lemma pair_E {a b s : ℕ} (ha : a ≤ E s) (hb : b ≤ E s) : Nat.pair a b + 1 ≤ E (s + 2) := by
  have h1 : Nat.pair a b < (E s + 1) ^ 2 :=
    lt_of_lt_of_le (Nat.pair_lt_max_add_one_sq a b)
      (Nat.pow_le_pow_left (by omega) 2 |> fun h ↦ by
        have : max a b + 1 ≤ E s + 1 := by omega
        exact Nat.pow_le_pow_left this 2)
  rw [E_add_two]
  have := sq_succ_succ_le_pow_four (two_le_E s)
  omega

lemma pair_F {a b s : ℕ} (ha : a ≤ F s) (hb : b ≤ F s) : Nat.pair a b + 1 ≤ F (s + 2) := by
  have h1 : Nat.pair a b < (F s + 1) ^ 2 :=
    lt_of_lt_of_le (Nat.pair_lt_max_add_one_sq a b) (by
        have : max a b + 1 ≤ F s + 1 := by omega
        exact Nat.pow_le_pow_left this 2)
  have h2 := sq_succ_succ_le_pow_four (two_le_F s)
  have h3 := F_add_two s
  omega

/-- One bit-set level: `2^(E s + 1) ≤ F (s + 1)`. -/
lemma two_pow_E_succ_le_F (s : ℕ) : 2 ^ (E s + 1) ≤ F (s + 1) := by
  unfold F E
  apply Nat.pow_le_pow_right (by norm_num)
  rw [pow_succ, pow_mul]
  have h : 2 ^ 2 ^ s + 1 ≤ (2 ^ 2 ^ s) ^ 2 := by
    have : 2 ≤ 2 ^ 2 ^ s := two_le_E s
    nlinarith
  exact h

/-! ### Term codes -/

section terms

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- `Nat.pair` on codes is Foundation's `⟪·,·⟫` at `V = ℕ`. -/
lemma nat_pair_eq' (a b : ℕ) : (⟪a, b⟫ : ℕ) = Nat.pair a b := nat_pair_eq b a

lemma pair_E' {a b s : ℕ} (ha : a ≤ E s) (hb : b ≤ E s) : (⟪a, b⟫ : ℕ) + 1 ≤ E (s + 2) := by
  rw [nat_pair_eq']; exact pair_E ha hb

lemma pair_E_le {a b s : ℕ} (ha : a ≤ E s) (hb : b ≤ E s) : (⟪a, b⟫ : ℕ) ≤ E (s + 2) :=
  le_trans (Nat.le_succ _) (pair_E' ha hb)

/-- A vector of `k` codes each `≤ E s` has code `≤ E (s + 2 k)`. -/
lemma vec_E {k : ℕ} {s : ℕ} (w : Fin k → ℕ) (hw : ∀ i, w i ≤ E s) :
    matrixToVec w ≤ E (s + 2 * k) := by
  induction k with
  | zero => simp [matrixToVec]
  | succ k ih =>
    change (w 0 ∷ matrixToVec (Matrix.vecTail w)) ≤ E (s + 2 * (k + 1))
    rw [adjoin_def]
    have h1 : w 0 ≤ E (s + 2 * k) := le_trans (hw 0) (E_mono (by omega))
    have h2 : matrixToVec (Matrix.vecTail w) ≤ E (s + 2 * k) :=
      ih _ (fun i ↦ hw i.succ)
    have := pair_E' h1 h2
    calc (⟪w 0, matrixToVec (Matrix.vecTail w)⟫ : ℕ) + 1 ≤ E (s + 2 * k + 2) := this
      _ = E (s + 2 * (k + 1)) := by ring_nf

end terms

/-! ### Term codes are bounded by `E (8 · tlen)` -/

section termBound

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- The largest of `k ≥ 1` positive numbers plus `k - 1` is at most their sum. -/
lemma sup_add_pred_card_le_sum {k : ℕ} (g : Fin (k + 1) → ℕ) (hg : ∀ i, 1 ≤ g i) :
    Finset.univ.sup g + k ≤ ∑ i, g i := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty g
  rw [← Finset.add_sum_erase Finset.univ g (Finset.mem_univ i₀), ← hi₀]
  have hcard : (Finset.univ.erase i₀).card = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
  have : (Finset.univ.erase i₀).card • 1 ≤ ∑ i ∈ Finset.univ.erase i₀, g i :=
    Finset.card_nsmul_le_sum _ _ _ (fun i _ ↦ hg i)
  rw [hcard, smul_eq_mul, mul_one] at this
  omega

lemma tlen_pos {n : ℕ} (t : SyntacticSemiterm L n) : 1 ≤ tlen t := by
  cases t <;> simp [tlen]

/-- Symbol codes bounded by `8` (true of `LAct`: the largest is `3`). -/
def SmallCodes (L : Language) [L.Encodable] : Prop :=
  ∀ {k : ℕ} (f : L.Func k), Encodable.encode f ≤ 8

lemma eight_le_E {s : ℕ} (h : 2 ≤ s) : 8 ≤ E s :=
  le_trans (by decide : 8 ≤ E 2) (E_mono h)

lemma quote_bvar_eq {n : ℕ} (x : Fin n) :
    (⌜(#x : SyntacticSemiterm L n)⌝ : ℕ) = ⟪0, (x : ℕ)⟫ + 1 := by
  rw [Semiterm.quote_bvar]; simp [qqBvar]
lemma quote_fvar_eq {n : ℕ} (x : ℕ) : (⌜(&x : SyntacticSemiterm L n)⌝ : ℕ) = ⟪1, x⟫ + 1 := by
  rw [Semiterm.quote_fvar]; simp [qqFvar]
lemma quote_func_eq {n k : ℕ} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜Semiterm.func f v⌝ : ℕ) =
      ⟪2, ⟪(k : ℕ), ⟪Encodable.encode f, matrixToVec fun i ↦ (⌜v i⌝ : ℕ)⟫⟫⟫ + 1 := by
  rw [Semiterm.quote_func, quote_func_def]
  unfold qqFunc SemitermVec.val
  simp
  rfl

/-- The code of a term is bounded by a tower in its symbol count. -/
theorem quote_term_le (hL : SmallCodes L) {n : ℕ} (t : SyntacticSemiterm L n) :
    (⌜t⌝ : ℕ) ≤ E (8 * tlen t) := by
  induction t with
  | bvar x =>
    rw [quote_bvar_eq, tlen_bvar]
    have := pair_E' (s := 8 * (x : ℕ) + 6) (a := 0) (b := (x : ℕ)) (Nat.zero_le _)
      (le_trans (by omega) (le_E _))
    rwa [show 8 * (x : ℕ) + 6 + 2 = 8 * ((x : ℕ) + 1) by ring] at this
  | fvar x =>
    rw [quote_fvar_eq, tlen_fvar]
    have := pair_E' (s := 8 * x + 6) (a := 1) (b := x)
      (le_trans (by omega) (le_E _)) (le_trans (by omega) (le_E _))
    rwa [show 8 * x + 6 + 2 = 8 * (x + 1) by ring] at this
  | @func k f v ih =>
    rw [quote_func_eq, tlen_func]
    cases k with
    | zero =>
      have hf : Encodable.encode f ≤ E 2 := le_trans (hL f) (by decide)
      have h1 : (⟪Encodable.encode f, matrixToVec fun i : Fin 0 ↦ (⌜v i⌝ : ℕ)⟫ : ℕ) ≤ E 4 :=
        pair_E_le hf (by simp [matrixToVec])
      have h2 : (⟪(0 : ℕ), ⟪Encodable.encode f, matrixToVec fun i : Fin 0 ↦ (⌜v i⌝ : ℕ)⟫⟫ : ℕ) ≤ E 6 :=
        pair_E_le (Nat.zero_le _) h1
      have h3 := pair_E' (a := 2) (le_trans (by decide) (two_le_E 6)) h2
      simpa using h3
    | succ k =>
      set M := Finset.univ.sup (fun i ↦ tlen (v i)) with hM
      set S := ∑ i, tlen (v i) with hS
      have hMS : M + k ≤ S := sup_add_pred_card_le_sum _ (fun i ↦ tlen_pos _)
      -- every argument code is below `E (8 M)`
      have hv : ∀ i, (⌜v i⌝ : ℕ) ≤ E (8 * M) := fun i ↦
        le_trans (ih i) (E_mono (by
          have := Finset.le_sup (f := fun i ↦ tlen (v i)) (Finset.mem_univ i)
          omega))
      have hvec : matrixToVec (fun i ↦ (⌜v i⌝ : ℕ)) ≤ E (8 * M + 2 * (k + 1)) := vec_E _ hv
      have hs₀ : 2 ≤ 8 * M + 2 * (k + 1) := by omega
      have hf : Encodable.encode f ≤ E (8 * M + 2 * (k + 1)) := le_trans (hL f) (eight_le_E hs₀)
      have h1 := pair_E_le hf hvec
      have hk : (k + 1 : ℕ) ≤ E (8 * M + 2 * (k + 1) + 2) := le_trans (by omega) (le_E _)
      have h2 := pair_E_le hk h1
      have h3 := pair_E' (a := 2) (le_trans (by decide) (two_le_E _)) h2
      refine le_trans h3 (E_mono ?_)
      omega

end termBound

/-! ### Formula codes are bounded by `E (8 · flen)` -/

section formulaBound

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- Relation-symbol codes bounded by `8` (true of `LAct`: the largest is `1`). -/
def SmallRelCodes (L : Language) [L.Encodable] : Prop :=
  ∀ {k : ℕ} (r : L.Rel k), Encodable.encode r ≤ 8

lemma flen_pos {n : ℕ} (φ : Semiproposition L n) : 1 ≤ flen φ := by
  cases φ <;> simp [flen]

lemma quote_rel_eq {n k : ℕ} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜Semiformula.rel R v⌝ : ℕ) =
      ⟪0, ⟪(k : ℕ), ⟪Encodable.encode R, matrixToVec fun i ↦ (⌜v i⌝ : ℕ)⟫⟫⟫ + 1 := by
  rw [Semiformula.quote_rel, quote_rel_def]
  unfold qqRel SemitermVec.val
  simp
  rfl

lemma quote_nrel_eq {n k : ℕ} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜Semiformula.nrel R v⌝ : ℕ) =
      ⟪1, ⟪(k : ℕ), ⟪Encodable.encode R, matrixToVec fun i ↦ (⌜v i⌝ : ℕ)⟫⟫⟫ + 1 := by
  rw [Semiformula.quote_nrel, quote_rel_def]
  unfold qqNRel SemitermVec.val
  simp
  rfl

/-- The relation-node chain: arguments below `E (8 M)`, `k ≥ 1` args, tag `t ≤ 2`. -/
private lemma rel_chain {t k M S : ℕ} (ht : t ≤ 2) (hMS : M + k ≤ S) {r vec : ℕ}
    (hr : r ≤ 8) (hvec : vec ≤ E (8 * M + 2 * (k + 1))) :
    (⟪t, ⟪(k + 1 : ℕ), ⟪r, vec⟫⟫⟫ : ℕ) + 1 ≤ E (8 * (S + 1)) := by
  have hs₀ : 2 ≤ 8 * M + 2 * (k + 1) := by omega
  have hr' : r ≤ E (8 * M + 2 * (k + 1)) := le_trans hr (eight_le_E hs₀)
  have h1 := pair_E_le hr' hvec
  have hk : (k + 1 : ℕ) ≤ E (8 * M + 2 * (k + 1) + 2) := le_trans (by omega) (le_E _)
  have h2 := pair_E_le hk h1
  have h3 := pair_E' (a := t) (le_trans (by omega) (le_trans (by decide : 2 ≤ E 0) (E_mono (Nat.zero_le _)))) h2
  exact le_trans h3 (E_mono (by omega))

private lemma rel_chain₀ {t : ℕ} (ht : t ≤ 2) {r : ℕ} (hr : r ≤ 8) :
    (⟪t, ⟪(0 : ℕ), ⟪r, (0 : ℕ)⟫⟫⟫ : ℕ) + 1 ≤ E 8 := by
  have hr' : r ≤ E 2 := le_trans hr (by decide)
  have h1 : (⟪r, (0 : ℕ)⟫ : ℕ) ≤ E 4 := pair_E_le hr' (Nat.zero_le _)
  have h2 : (⟪(0 : ℕ), ⟪r, (0 : ℕ)⟫⟫ : ℕ) ≤ E 6 := pair_E_le (Nat.zero_le _) h1
  exact pair_E' (a := t) (le_trans (by omega) (two_le_E 6)) h2

theorem quote_formula_le (hL : SmallCodes L) (hR : SmallRelCodes L) {n : ℕ}
    (φ : Semiproposition L n) : (⌜φ⌝ : ℕ) ≤ E (8 * flen φ) := by
  induction φ with
  | @rel n k R v =>
    rw [quote_rel_eq]
    simp only [flen]
    cases k with
    | zero =>
      have : matrixToVec (fun i : Fin 0 ↦ (⌜v i⌝ : ℕ)) = 0 := by simp [matrixToVec]
      rw [this]; simpa using rel_chain₀ (by norm_num) (hR R)
    | succ k =>
      set M := Finset.univ.sup (fun i ↦ tlen (v i)) with hM
      have hMS : M + k ≤ ∑ i, tlen (v i) := sup_add_pred_card_le_sum _ (fun i ↦ tlen_pos _)
      have hv : ∀ i, (⌜v i⌝ : ℕ) ≤ E (8 * M) := fun i ↦
        le_trans (quote_term_le hL (v i)) (E_mono (by
          have := Finset.le_sup (f := fun i ↦ tlen (v i)) (Finset.mem_univ i)
          omega))
      exact rel_chain (by norm_num) hMS (hR R) (vec_E _ hv)
  | @nrel n k R v =>
    rw [quote_nrel_eq]
    simp only [flen]
    cases k with
    | zero =>
      have : matrixToVec (fun i : Fin 0 ↦ (⌜v i⌝ : ℕ)) = 0 := by simp [matrixToVec]
      rw [this]; simpa using rel_chain₀ (by norm_num) (hR R)
    | succ k =>
      set M := Finset.univ.sup (fun i ↦ tlen (v i)) with hM
      have hMS : M + k ≤ ∑ i, tlen (v i) := sup_add_pred_card_le_sum _ (fun i ↦ tlen_pos _)
      have hv : ∀ i, (⌜v i⌝ : ℕ) ≤ E (8 * M) := fun i ↦
        le_trans (quote_term_le hL (v i)) (E_mono (by
          have := Finset.le_sup (f := fun i ↦ tlen (v i)) (Finset.mem_univ i)
          omega))
      exact rel_chain (by norm_num) hMS (hR R) (vec_E _ hv)
  | verum =>
    change (⌜(⊤ : Semiproposition L _)⌝ : ℕ) ≤ E (8 * 1)
    rw [Semiformula.quote_verum]
    unfold qqVerum
    exact pair_E' (s := 6) (le_trans (by omega) (two_le_E 6)) (Nat.zero_le _)
  | falsum =>
    change (⌜(⊥ : Semiproposition L _)⌝ : ℕ) ≤ E (8 * 1)
    rw [Semiformula.quote_falsum]
    unfold qqFalsum
    exact pair_E' (s := 6) (le_trans (by omega) (le_E 6)) (Nat.zero_le _)
  | and φ ψ ihφ ihψ =>
    change (⌜φ ⋏ ψ⌝ : ℕ) ≤ E (8 * (flen φ + flen ψ + 1))
    rw [Semiformula.quote_and]
    unfold qqAnd
    have h1 := pair_E_le (le_trans ihφ (E_mono (by omega : 8 * flen φ ≤ 8 * (flen φ + flen ψ))))
      (le_trans ihψ (E_mono (by omega : 8 * flen ψ ≤ 8 * (flen φ + flen ψ))))
    have h2 := pair_E' (a := 4) (le_trans (by have := flen_pos φ; omega) (le_E _)) h1
    exact le_trans h2 (E_mono (by omega))
  | or φ ψ ihφ ihψ =>
    change (⌜φ ⋎ ψ⌝ : ℕ) ≤ E (8 * (flen φ + flen ψ + 1))
    rw [Semiformula.quote_or]
    unfold qqOr
    have h1 := pair_E_le (le_trans ihφ (E_mono (by omega : 8 * flen φ ≤ 8 * (flen φ + flen ψ))))
      (le_trans ihψ (E_mono (by omega : 8 * flen ψ ≤ 8 * (flen φ + flen ψ))))
    have h2 := pair_E' (a := 5) (le_trans (by have := flen_pos φ; omega) (le_E _)) h1
    exact le_trans h2 (E_mono (by omega))
  | all φ ih =>
    change (⌜∀¹ φ⌝ : ℕ) ≤ E (8 * (flen φ + 1))
    rw [Semiformula.quote_all]
    unfold qqAll
    have h := pair_E' (a := 6) (le_trans (by have := flen_pos φ; omega) (le_E _)) ih
    exact le_trans h (E_mono (by omega))
  | exs φ ih =>
    change (⌜∃¹ φ⌝ : ℕ) ≤ E (8 * (flen φ + 1))
    rw [Semiformula.quote_ex]
    unfold qqExs
    have h := pair_E' (a := 7) (le_trans (by have := flen_pos φ; omega) (le_E _)) ih
    exact le_trans h (E_mono (by omega))

end formulaBound

end ArithS
