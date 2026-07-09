import PrisonersDilemma.Program
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Base/Asymptotics — the numeral/log₂ arithmetic layer

Pure `Nat` facts about `Nat.log2` (the numeral-cost function `numCost k = log2 k + 1`):
the linear-vs-log threshold lemma `linear_log2_add_le` (absorbed from the former
`SizeLemmas.lean`), monotonicity, `log2 k ≤ k`, and the staggering bounds
`log2 (2k+64) ≤ log2 k + 8` / `log2 (4k+100) ≤ log2 k + 9` used by the `pblt_engine`
instantiations. No proof theory here — only arithmetic.
-/

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

namespace PD.BaseTheorems

/-- `Nat.log2` is monotone (companion to `c_guard_mono`; used by the `pblt_engine`
    instantiations to bound the chain's box-subscript numerals by `log2 k`). -/
theorem log2_mono {a b : Nat} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  simp only [Nat.log2_eq_log_two]; exact Nat.log_mono_right h


/-- `log2 k ≤ k` (tiny helper for staggering arithmetic). -/
theorem log2_le_self (k : Nat) : Nat.log2 k ≤ k := by
  simp only [Nat.log2_eq_log_two]
  exact Nat.log_le_self 2 k

/-- The staggering function `2k + 64` costs at most 8 extra characters in its numeral. -/
theorem log2_stagger_le (k : Nat) : Nat.log2 (2 * k + 64) ≤ Nat.log2 k + 8 := by
  have h1 : k < 2 ^ (Nat.log2 k + 1) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Nat.two_pow_pos _
    · rw [Nat.log2_eq_log_two]
      exact Nat.lt_pow_succ_log_self (by norm_num) k
  have h2 : (2:Nat) ^ (Nat.log2 k + 9) = 2 ^ (Nat.log2 k + 1) * 256 := by
    rw [show Nat.log2 k + 9 = (Nat.log2 k + 1) + 8 from rfl, pow_add]
    norm_num
  have h3 : 2 * k + 64 < 2 ^ (Nat.log2 k + 9) := by
    have hp : 1 ≤ (2:Nat) ^ (Nat.log2 k + 1) := Nat.one_le_two_pow
    omega
  have := (Nat.log2_lt (by omega)).2 h3
  omega

/-- The wider staggering function `4k + 100` costs at most 9 extra numeral characters. -/
theorem log2_stagger4_le (k : Nat) : Nat.log2 (4 * k + 100) ≤ Nat.log2 k + 9 := by
  have h1 : k < 2 ^ (Nat.log2 k + 1) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Nat.two_pow_pos _
    · rw [Nat.log2_eq_log_two]
      exact Nat.lt_pow_succ_log_self (by norm_num) k
  have h2 : (2:Nat) ^ (Nat.log2 k + 10) = 2 ^ (Nat.log2 k + 1) * 512 := by
    rw [show Nat.log2 k + 10 = (Nat.log2 k + 1) + 9 from rfl, pow_add]
    norm_num
  have h3 : 4 * k + 100 < 2 ^ (Nat.log2 k + 10) := by
    have hp : 1 ≤ (2:Nat) ^ (Nat.log2 k + 1) := Nat.one_le_two_pow
    omega
  have := (Nat.log2_lt (by omega)).2 h3
  omega

end PD.BaseTheorems
