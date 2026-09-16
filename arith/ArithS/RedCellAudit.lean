import ArithS.RedCell
import ArithS.Fit

/-!
# ArithS.RedCellAudit — the red cell's meaning, pinned

Companion to `Research/Notes/RED_CELL_AUDIT.md`. Nothing here is new mathematics: each theorem
restates, in the smallest possible form, one thing the reader must be able to check about
`red_cell` without reading the package — that the result is not vacuous, not fuel-dependent,
not an artefact of an under-determined evaluator, and that its NEGATION is refutable (the
negative control). If a definition in the trusted base were wrong in the usual ways (actions
swapped, template misread, evaluator clause off by one), one of these would fail to compile.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic
open LAct

/-! ### 1. The result, stated once more in words

`EvalGraph n me opp p a` reads "with fuel `n`, the program `p` run by `me` against `opp` returns
the action `a`", actions `0 = C`, `1 = D`. -/

/-- Dupoc returns D against Cupod, and Cupod returns C against Dupoc, at every shared budget. -/
theorem red_cell_words (k : ℕ) :
    EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 1 ∧ EvalGraph 2 (Cupod k) (Dupoc k) (Cupod k) 0 :=
  red_cell k

/-! ### 2. Negative controls — the opposite outcomes are REFUTABLE, not merely unproved -/

/-- Dupoc does NOT cooperate with Cupod, at any fuel. -/
theorem dupoc_not_coop (k n : ℕ) : ¬ EvalGraph n (Dupoc k) (Cupod k) (Dupoc k) 0 := fun h ↦ by
  have := EvalGraph.unique' h (red_cell k).1
  exact absurd this (by decide)

/-- Cupod does NOT defect against Dupoc, at any fuel. -/
theorem cupod_not_defect (k n : ℕ) : ¬ EvalGraph n (Cupod k) (Dupoc k) (Cupod k) 1 := fun h ↦ by
  have := EvalGraph.unique' h (red_cell k).2
  exact absurd this (by decide)

/-! ### 3. Determinism — the evaluator returns at most one action, so "returns D" excludes "returns C" -/

theorem red_cell_deterministic (k n : ℕ) {a b : ℕ}
    (ha : EvalGraph n (Dupoc k) (Cupod k) (Dupoc k) a) (hb : EvalGraph n (Cupod k) (Dupoc k) (Cupod k) b) :
    a = 1 ∧ b = 0 :=
  red_cell_unique k n ha hb

/-! ### 4. Fuel-independence — more fuel never changes the answer -/

theorem red_cell_any_fuel (k n : ℕ) (hn : 2 ≤ n) :
    EvalGraph n (Dupoc k) (Cupod k) (Dupoc k) 1 ∧ EvalGraph n (Cupod k) (Dupoc k) (Cupod k) 0 :=
  ⟨EvalGraph.mono_le hn (red_cell k).1, EvalGraph.mono_le hn (red_cell k).2⟩

/-! ### 5. The guard means what it says — a provable guard is a TRUE statement about a run

If Dupoc's guard ("Cupod plays C against me") had a proof of length `≤ k`, then Cupod really
would return C against Dupoc. This is the truth equation the whole argument turns on. -/

theorem guard_is_about_the_run (k : ℕ)
    (h : LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) (Cupod k))) :
    ∃ n, EvalGraph n (Cupod k) (Dupoc k) (Cupod k) 0 :=
  evalGraph_of_guard h

/-! ### 6. Why both guards fail — the two bots are each other's C/D mirror image

Dupoc's guard is provable iff Cupod's is (`guard_Dupoc_iff_guard_Cupod`); if either were,
Dupoc would both cooperate (its search fired) and defect (Cupod's guard says so): contradiction. -/

theorem guards_both_fail (k : ℕ) :
    ¬ LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) (Cupod k)) ∧
    ¬ LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : ℕ) (Cupod k) (Dupoc k)) := by
  have hD : ¬ LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) (Cupod k)) := fun hD ↦ by
    obtain ⟨n, hn⟩ := evalGraph_of_guard ((guard_Dupoc_iff_guard_Cupod k).mp hD)
    have hcoop : EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 0 := by
      show EvalGraph (1 + 1) (Dupoc k) (Cupod k) (pSearch k (⌜GtmplA 0⌝ : ℕ) (pConst 0) (pConst 1)) 0
      rw [EvalGraph.search_iff]
      exact Or.inl ⟨hD, (EvalGraph.const_iff (n := 0)).mpr rfl⟩
    exact dupoc_not_coop k 2 hcoop
  exact ⟨hD, fun h ↦ hD ((guard_Dupoc_iff_guard_Cupod k).mpr h)⟩

/-! ### 7. Non-vacuity — the searches are real: from some budget on, the guard sentence FITS

Without this, "the guard is unprovable at budget `k`" could hold merely because the guard is
longer than `k` characters. `guard_fits` says that from some `K` on it is not. -/

theorem search_is_real :
    ∃ K, ∀ k ≥ K, ∀ a ≤ 1,
      flen (Rewriting.emb (guardSentenceA a (Dupoc k) (Cupod k)) : Proposition LAct) ≤ k :=
  guard_fits

/-! ### 8. Census -/

#print axioms red_cell_words
#print axioms dupoc_not_coop
#print axioms cupod_not_defect
#print axioms guards_both_fail
#print axioms search_is_real

end ArithS
