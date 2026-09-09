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

end ArithS
