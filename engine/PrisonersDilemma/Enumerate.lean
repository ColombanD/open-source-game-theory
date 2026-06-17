import PrisonersDilemma.Program
import Mathlib.Data.Nat.Log

/-!
# Bounded enumeration of `Prog` and `Formula`

`progsOfSizeLE n` / `formulasOfSizeLE n` creates a list of every program / formula of `size ≤ n`.
Completeness (`prog_mem_ofSizeLE` / `formula_mem_ofSizeLE`): a term of `size ≤ n` is
in the list. This is the finite universe `U_k` over which the decision procedure
(`Checker.lean`) saturates the cut rules — it is what turns "is there a derivation
with cut formulas of size ≤ k" into a finite search.

The only non-structural piece is the `Nat` index carried by `.search` / `.box`, whose
size contribution is `Nat.log2 k + 1`. All indices with `Nat.log2 k + 1 ≤ b` satisfy
`k < 2^b`, so they are enumerated by `List.range (2 ^ b)` (`natsOfLog2CostLE`). The
`2^b` blowup is irrelevant to correctness (this file is only used in completeness
*proofs*, never run); see `Checker.lean` for the runtime story.
-/

namespace PD

-- Since .search and .box carry a Nat index k, we need to enumerate all possible indices
-- k whose size contribution `Nat.log2 k + 1` fits the budget b.
/-- All naturals whose numeral-cost `Nat.log2 k + 1` fits budget `b`: exactly the
    naturals `< 2 ^ b`. -/
def natsOfLog2CostLE (b : Nat) : List Nat := List.range (2 ^ b)

-- The following lemma is used in the completeness proofs to show that any index k
-- whose size contribution `Nat.log2 k + 1` fits the budget b is indeed enumerated by `natsOfLog2CostLE b`.
theorem nat_mem_natsOfLog2CostLE {k b : Nat} (h : Nat.log2 k + 1 ≤ b) :
    k ∈ natsOfLog2CostLE b := by
  unfold natsOfLog2CostLE
  rw [List.mem_range]
  -- `Nat.log2 k < b`, and `Nat.log2 k < b → k < 2 ^ b`.
  have hlt : Nat.log2 k < b := by omega
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; exact Nat.two_pow_pos b
  · -- `k < 2 ^ (Nat.log2 k + 1) ≤ 2 ^ b`
    have hk1 : k < 2 ^ (Nat.log2 k + 1) := by
      have := Nat.lt_log2_self (n := k)
      simpa [Nat.log2] using this
    exact lt_of_lt_of_le hk1 (Nat.pow_le_pow_right (by decide) hlt)

-- Enumerate programs and formulas of `size ≤ n`, by structural recursion on the
-- size budget `n`. Children of a term of size `≤ n+1` have size `≤ n`.
-- Builds the actual list of terms, not just a proof of existence.
mutual
  def progsOfSizeLE : Nat → List Prog
    | 0 => []
    | n + 1 =>
      let ps := progsOfSizeLE n
      let fs := formulasOfSizeLE n
      let idxs := natsOfLog2CostLE (n + 1)
      -- leaves
      [.const .C, .const .D, .self, .opp]
      -- one-child / multi-child nodes (children drawn from size-≤ n lists)
      ++ (ps.map .bot)
      ++ (ps.flatMap fun p => ps.map fun q => .sim p q)
      ++ (ps.flatMap fun b => ps.flatMap fun p => ps.flatMap fun q =>
            [Prog.ite b .C p q, Prog.ite b .D p q])
      ++ (idxs.flatMap fun k => fs.flatMap fun φ => ps.flatMap fun p => ps.map fun q =>
            Prog.search k φ p q)

  def formulasOfSizeLE : Nat → List Formula
    | 0 => []
    | n + 1 =>
      let ps := progsOfSizeLE n
      let fs := formulasOfSizeLE n
      let idxs := natsOfLog2CostLE (n + 1)
      (ps.flatMap fun p => ps.flatMap fun q => [Formula.plays p q .C, Formula.plays p q .D])
      ++ (fs.flatMap fun φ => fs.map fun ψ => Formula.impl φ ψ)
      ++ (fs.map Formula.neg)
      ++ (idxs.flatMap fun k => fs.map fun φ => Formula.box k φ)
      ++ (ps.flatMap fun p => ps.map fun q => Formula.eq p q)
end

private theorem prog_size_pos (p : Prog) : 1 ≤ p.size := by cases p <;> simp [Prog.size]
private theorem formula_size_pos (φ : Formula) : 1 ≤ φ.size := by cases φ <;> simp [Formula.size]

-- Guarantee that the enumerations are complete: any term of size ≤ n is in the list.
mutual
  theorem prog_mem_ofSizeLE {n : Nat} {p : Prog} (h : p.size ≤ n) : p ∈ progsOfSizeLE n := by
    cases n with
    | zero => exact absurd h (by have := prog_size_pos p; omega)
    | succ n =>
      have IHp : ∀ {q : Prog}, q.size ≤ n → q ∈ progsOfSizeLE n := fun hq => prog_mem_ofSizeLE hq
      have IHf : ∀ {ψ : Formula}, ψ.size ≤ n → ψ ∈ formulasOfSizeLE n := fun hψ => formula_mem_ofSizeLE hψ
      unfold progsOfSizeLE
      simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap]
      cases p with
      | const a => cases a <;> simp
      | self => simp
      | opp => simp
      | bot q =>
          have hq : q.size ≤ n := by simp only [Prog.size] at h; omega
          have := IHp hq; simp_all
      | sim p q =>
          have hp : p.size ≤ n := by simp only [Prog.size] at h; omega
          have hq : q.size ≤ n := by simp only [Prog.size] at h; omega
          have h1 := IHp hp; have h2 := IHp hq; simp_all
      | ite b a p q =>
          have hb : b.size ≤ n := by simp only [Prog.size] at h; omega
          have hp : p.size ≤ n := by simp only [Prog.size] at h; omega
          have hq : q.size ≤ n := by simp only [Prog.size] at h; omega
          have h1 := IHp hb; have h2 := IHp hp; have h3 := IHp hq
          cases a
          · exact Or.inl (Or.inr ⟨b, h1, p, h2, q, h3, Or.inl rfl⟩)
          · exact Or.inl (Or.inr ⟨b, h1, p, h2, q, h3, Or.inr (Or.inl rfl)⟩)
      | search k φ p q =>
          have hk : Nat.log2 k + 1 ≤ n + 1 := by simp only [Prog.size] at h; omega
          have hφ : φ.size ≤ n := by simp only [Prog.size] at h; omega
          have hp : p.size ≤ n := by simp only [Prog.size] at h; omega
          have hq : q.size ≤ n := by simp only [Prog.size] at h; omega
          have h0 := nat_mem_natsOfLog2CostLE hk
          have h1 := IHf hφ; have h2 := IHp hp; have h3 := IHp hq
          exact Or.inr ⟨k, h0, φ, h1, p, h2, q, h3, rfl⟩

  theorem formula_mem_ofSizeLE {n : Nat} {φ : Formula} (h : φ.size ≤ n) : φ ∈ formulasOfSizeLE n := by
    cases n with
    | zero => exact absurd h (by have := formula_size_pos φ; omega)
    | succ n =>
      have IHp : ∀ {q : Prog}, q.size ≤ n → q ∈ progsOfSizeLE n := fun hq => prog_mem_ofSizeLE hq
      have IHf : ∀ {ψ : Formula}, ψ.size ≤ n → ψ ∈ formulasOfSizeLE n := fun hψ => formula_mem_ofSizeLE hψ
      unfold formulasOfSizeLE
      simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap]
      cases φ with
      | plays p q a =>
          have hp : p.size ≤ n := by simp only [Formula.size] at h; omega
          have hq : q.size ≤ n := by simp only [Formula.size] at h; omega
          have h1 := IHp hp; have h2 := IHp hq; cases a <;> simp_all
      | impl φ ψ =>
          have hφ : φ.size ≤ n := by simp only [Formula.size] at h; omega
          have hψ : ψ.size ≤ n := by simp only [Formula.size] at h; omega
          have h1 := IHf hφ; have h2 := IHf hψ; simp_all
      | neg φ =>
          have hφ : φ.size ≤ n := by simp only [Formula.size] at h; omega
          have := IHf hφ; simp_all
      | box k φ =>
          have hk : Nat.log2 k + 1 ≤ n + 1 := by simp only [Formula.size] at h; omega
          have hφ : φ.size ≤ n := by simp only [Formula.size] at h; omega
          have h0 := nat_mem_natsOfLog2CostLE hk
          have h1 := IHf hφ; simp_all
      | eq p q =>
          have hp : p.size ≤ n := by simp only [Formula.size] at h; omega
          have hq : q.size ≤ n := by simp only [Formula.size] at h; omega
          have h1 := IHp hp; have h2 := IHp hq; simp_all
end

end PD
