import PrisonersDilemma.Program
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace PD

/-!
# Size lemmas (character-faithful arithmetic)

The one arithmetic lemma the budget-faithful Löb chain needs: a linear function
of `Nat.log2 k` is eventually dominated by `k`. This is what lets the
source-transparency derivation (size `C · log2 k + D`) fit within search budget
`k` for large `k` — i.e. it is the constructive content of PBLT's
`f(k) ≻ O(lg k)` hypothesis. See `ProofLengthRoadmap.md`.

Used by the four Löb premises in `Theorems/CupodBot.lean` and
`Theorems/DupocBot.lean` (`linear_log2_add_le 5 33` for self-play,
`linear_log2_add_le 3 25` for the MirrorBot legs). Those premises compute the
*exact* derivation size inline (`simp [Derivation.size, …]; omega`), so no
per-rule size-bound API is needed here.

Key Mathlib primitives used:
* `Nat.log2_eq_log_two : Nat.log2 n = Nat.log 2 n`
* `Nat.pow_log_le_self 2 (h : n ≠ 0) : 2^(Nat.log 2 n) ≤ n`
* `Nat.le_log2 (h : n ≠ 0) : k ≤ Nat.log2 n ↔ 2^k ≤ n`
-/

-- Helper: 2*m + 1 ≤ 2^m for m ≥ 4
private lemma aux_2m_le_pow (m : Nat) (hm : m ≥ 4) : 2*m + 1 ≤ 2^m := by
  induction m with
  | zero => omega
  | succ k ih =>
    by_cases hk : k ≥ 4
    · have ihk := ih hk
      have : 2^(k+1) = 2 * 2^k := by ring
      linarith
    · have : k = 3 := by omega
      subst this; norm_num

-- Helper: 2^n ≥ n^2 for n ≥ 4
private lemma aux_pow_ge_sq (n : Nat) (hn : n ≥ 4) : n^2 ≤ 2^n := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : m ≥ 4
    · have ihm := ih hm
      have hm2 : 2*m + 1 ≤ 2^m := aux_2m_le_pow m hm
      have hpow : 2^(m+1) = 2 * 2^m := by ring
      rw [hpow]; nlinarith [sq_nonneg m]
    · have : m = 3 := by omega
      subst this; norm_num

-- Helper: A*n + B ≤ 2^n for n ≥ 2*A, n ≥ 2*B, n ≥ 4
private lemma aux_linear_le_pow (A B n : Nat)
    (hA : 2*A ≤ n) (hB : 2*B ≤ n) (h4 : 4 ≤ n) : A * n + B ≤ 2^n := by
  have hpow := aux_pow_ge_sq n h4
  nlinarith [Nat.mul_le_mul_right n hA, sq_nonneg n]

/-- For fixed `A` and `B`, `A * Nat.log2 k + B ≤ k` holds for all sufficiently
    large `k` (specifically, all `k ≥ 2^(max(2*A, 2*B, 4))`).

    This is the general form needed for the Löb-chain size bounds: the
    `searchBranch` derivation has size `C * log2 k + D` for constants `C, D`
    depending on the bot's structure, and we need this to fit within budget `k`.
    The proof uses `A * n + B ≤ 2^n` (for `n ≥ max(2A, 2B, 4)`, via `n^2 ≤ 2^n`)
    together with `2^(log2 k) ≤ k`. -/
theorem linear_log2_add_le (A B : Nat) : ∃ K : Nat, ∀ k : Nat, k ≥ K → A * Nat.log2 k + B ≤ k := by
  refine ⟨2 ^ (max (2*A) (max (2*B) 4)), fun k hk => ?_⟩
  have hk0 : k ≠ 0 := by
    intro heq; subst heq; simp at hk
  have hlog_ge : max (2*A) (max (2*B) 4) ≤ Nat.log2 k := (Nat.le_log2 hk0).mpr hk
  have hpow_le : 2^(Nat.log2 k) ≤ k := by
    rw [Nat.log2_eq_log_two]; exact Nat.pow_log_le_self 2 hk0
  linarith [aux_linear_le_pow A B (Nat.log2 k)
    (le_trans (Nat.le_max_left _ _) hlog_ge)
    (le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hlog_ge)
    (le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hlog_ge)]

end PD
