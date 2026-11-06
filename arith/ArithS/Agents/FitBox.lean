import ArithS.Bridge.Neg
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot

/-!
# ArithS.FitBox — Critch's assumption (b) for guards that contain BOXES

`ArithS.Fit` proved assumption (b) (Appendix B of `critch22`: "`S` writes `k` in `O(lg k)`
characters") for the box-free searchers: their guard sentences have `O(size k)` symbols and fit
inside the budget `k` for all large `k`. This file settles the box-carrying guards — the
first zoo member is `LegibleBot kOut kIn = .search kOut (.box kIn (I play C)) C D`
(`Bots/LlmGenerations/LegibleBot.lean`) — and the answer splits in two.

## The positive half: the TEMPLATE of a box is short

`template (.box k ψ)` (`ArithS.Code`) writes the budget as the binary numeral TERM `numTB k`
(`termLenMeta ≤ 6 · size k + 1`, `ArithS.BinNumeral`) inside `lenProvG ⇜ ![cl (numTB k), #0]`; the other
three conjuncts do not depend on `k`. Hence (§6):

* `formulaLenMeta_emb_template_box_le : formulaLenMeta (emb (template (.box k ψ))) ≤ cBox ψ + 6 · cL · size k`, with
  `cL = formulaLenMeta (emb lenProvG)` and `cBox ψ` the symbol counts of the fixed conjuncts, packaged as
  irreducible constants (never evaluated: see the proof-craft note);
* `exists_formulaLenMeta_template_box_const ψ : ∃ c₀ c₁, ∀ k, formulaLenMeta (emb (template (.box k ψ))) ≤ c₀ + c₁ · size k`;
* `BudgetLinear F` (constants, `fun k ↦ .box k ψ`, `.impl`, `.neg`) and
  `exists_formulaLenMeta_template_const : BudgetLinear F → ∃ c₀ c₁, ∀ k, formulaLenMeta (emb (template (F k))) ≤ c₀ + c₁ · size k`.
  A box NESTED inside a box is not budget-linear: the inner formula's budget sits inside the
  code constant `numTB (templateCode ψ)` of the outer template, and codes are what the negative half is
  about.

## The negative half (the finding): the CODE of a binary numeral is exponential

Assumption (b) is about the symbols the proof system writes, and the guard sentence of a
searcher `me` names `me` by the canonical numeral of ITS OWN CODE: `sentenceAt me opp φ` contains
`canonicalMeta (progCode me) = lMap emb (codeTermMeta (canonical (progCode me)))`, whose length is at least the bit length of
`progCode me` (`size_le_termLenMeta_codeTermMeta`, `ArithS.CodeTerm`). For the box-free `Dupoc k` this is harmless:
`pSearch k g p q` stores `k` as a DATA field (a number of `size k` bits), so
`size (progCode (Dupoc k)) = O(size k)` (`size_canonical_Dupoc_le`). A box-carrying searcher stores
`templateCode (.box k ψ) = ⌜template (.box k ψ)⌝`, and that template contains the numeral TERM `numTB k`,
whose code `binNumeral k` is built by Cantor pairing along the bits of `k`:
`binNumeral (2m) = 𝟐 ^* binNumeral m = ^func 2 mulIndex ?[𝟐, binNumeral m]`, and the innermost pair
`⟪binNumeral m, 0⟫ = (binNumeral m)² + binNumeral m` SQUARES the code at every level. So

* `two_pow_succ_le_binNumeral : 2 ^ (n + 1) ≤ binNumeral n` and `size_binNumeral_ge : n + 2 ≤ Nat.size (binNumeral n)`:
  **the Cantor-pair code of the binary numeral of `n` has more than `n` bits — as many as a
  unary numeral has symbols.** (The true growth is much faster, `≳ n⁵`, since three more pairs
  wrap the vector; the square alone is what the induction needs.)

The rest of the file threads this through the translation, with `HasBox k φ` ("`□_k` occurs
at a Boolean position of `φ`", `.impl`/`.neg` closed) as the hypothesis:

* `fOcc_lenBox`: the budget variable `#0` OCCURS in `lenBox`'s Σ₁ definition — in
  the atom `n ≤ k` bounding the proof length. This is a SYNTACTIC proof: `simp only
  [sigma_mkDelta, val_mkSigma]` exposes the connective skeleton of the DSL formula while every
  `!p …` substitution stays opaque, and `FOcc` (§2) descends `∃¹`/`⋏`/`bexsLT` to the `≤` atom;
  no giant formula is ever unfolded (13 s, measured);
* `le_quote_rew_formula` (§2): if `#i` occurs in `φ` then `⌜ω #i⌝ ≤ ⌜ω ▹ φ⌝` (codes are
  monotone along the syntax tree: `le_qqFunc`, `le_qqRel`, …, `quote_le_quote_bShift`);
* `binNumeral_le_templateCode : HasBox k φ → binNumeral k ≤ templateCode φ` and `binNumeral_le_revalueTemplate_templateCode` (the
  code-level transposition `transposeCode` relabels the action constants only, the numeral survives —
  `lMap_swap_numTB`); then `binNumeral_le_canonical_progCode_search : binNumeral k ≤ canonical (progCode (.search k' φ p q))`
  (both the code and its transposition are `≥ binNumeral k`, so is their `min`) and
  `size_canonical_progCode_search_ge : k + 2 ≤ size (canonical (progCode (.search k' φ p q)))`;
* `size_canonical_le_formulaLenMeta_sentenceAt_hasBox : HasBox k φ → size (canonical (progCode me)) + 1 ≤ formulaLenMeta (emb (sentenceAt me opp φ))`
  (every box translation writes the `me`-description, §5);
* **`box_guard_never_fits : HasBox k φ → ∀ k' p q opp, k < formulaLenMeta (emb (sentenceAt (.search k' φ p q) opp φ))`**,
  `not_box_guard_fits`, and the zoo instances `legibleBot_guard_never_fits` /
  `legibleBot_staggered_guard_never_fits` (`kIn < formulaLenMeta (guard of LegibleBot kOut kIn)` for EVERY
  `kOut`): under the present coding, a searcher whose guard mentions `□_k` can never find its
  guard within `k` — not because of Löb, but because the sentence it searches for is longer
  than `k`. This is the exact analogue of the retired `Vacuity.lean` obstruction (unary
  numerals, commit 470ee43), one level up: binary numeral TERMS are short, their CODES are not.

## The design fix (described, deliberately NOT implemented here)

The budget must not be written as a numeral term inside a stored template; two repairs:

1. **Box budgets as node DATA.** Make the box template a SEVEN-variable formula with the box
   budget as the extra variable (`lenProvG ⇜ ![#6, #0]` instead of `![cl (numTB k), #0]`), and
   let the search node's own `k` (already a data field of `pSearch`) be substituted by
   `descriptions` at evaluation time, exactly as the players' descriptions are. The stored template
   then does not mention `k` at all, its code is a constant, `size (progCode (me k)) = O(size k)`
   as for `Dupoc`, and `guard_fits` goes through verbatim. Nested boxes need the same treatment
   recursively (a per-node budget vector).
2. **Balanced numeral terms.** Write `n = a·b + c` with `a, b ≈ √n` and recurse: depth
   `O(log log n)`, so the Cantor code is polylogarithmic in `n` (Foundation has `sqrt` in
   `ISigma0`). This keeps `numTB` inside the template but changes `binNumeral`/`binNumeralMeta` and every
   length lemma of `ArithS.BinNumeral`.

Route 1 is the faithful one (Critch's search node is "a proof of `φ` at budget `k`", with `k`
a parameter of the node, not a character of `φ`); route 2 is a coding trick.

## Proof-craft note — three ways this file hung for hours

1. A `le_trans ?_ (…)` chain with placeholders against a goal of the form `⌜…⌝ ≤ ^∃ (^∃ (… ^⋏ …))`
   made unification unfold `qqAnd`/`qqExs` down to `pair` and its `if` while trying to match
   mismatched shapes. Cure: the helpers `le_boxShapeCode`/`le_boxShapeCode_neg` state the exact
   syntactic shape, and every closed `⟪…⟫` bound is a named lemma over variables (`npair_le_*`).
2. `exact h` where `h : binNumeral k ≤ ⌜Rew.emb ▹ (lenProvG ⇜ w)⌝` was elaborated separately and the
   goal came out of `simp`: the two quotes differ only in the representation of the bound-variable
   index (`9` vs `6 + 1 + 1 + 1` from the quantifier nesting) and `isDefEq` fell back to unfolding
   the QUOTE of the giant `lenProvG`. Cure: every shape lemma finishes by replaying the tactic
   script on ITS OWN goal (`binNumeral_le_quote_emb_subst`'s script), lemma arguments are left to
   unification (`refine … _ ?_`), and cross-lemma `exact`s only ever meet two source-elaborated
   statements.
3. `unfold cBox`/`show`/`delta` on the constant `cBox ψ = … + 6`: any `whnf` of a closed `Nat`
   expression makes Lean EVALUATE the symbol counts of the giant conjuncts (Fit.lean's note,
   now with the tactic list). Cure: `rw [cBox, cL]` and an arithmetic lemma over variables
   applied by unification (`arith_le`).
Bisection by truncation (`#exit`) with `timeout` located each of the three within minutes;
the file checks in ~3 s once every step is goal-directed.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

/-! ### 0. Foundation's order on `ℕ` vs `Nat.le` -/

section order

lemma nle_of_fle {a b : ℕ} (h : a = b ∨ a < b) : a ≤ b := by omega
lemma fle_of_nle {a b : ℕ} (h : a ≤ b) : a = b ∨ a < b := by omega

lemma npair_le_left (a b : ℕ) : a ≤ ⟪a, b⟫ := nle_of_fle (le_def.mp (le_pair_left a b))
lemma npair_le_right (a b : ℕ) : b ≤ ⟪a, b⟫ := nle_of_fle (le_def.mp (le_pair_right a b))
lemma npair_le_pair {a₁ a₂ b₁ b₂ : ℕ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) : ⟪a₁, b₁⟫ ≤ ⟪a₂, b₂⟫ :=
  nle_of_fle (le_def.mp (pair_le_pair (le_def.mpr (fle_of_nle ha)) (le_def.mpr (fle_of_nle hb))))

/-- The polynomial pairing of PROGRAM codes (`ArithS.Prog`), read with `Nat.le`. -/
lemma nppair_le_left (a b : ℕ) : a ≤ ppair a b := by
  show a ≤ (a + b) * (a + b) + b
  exact Nat.le_trans (Nat.le_add_right a b) (Nat.le_trans (Nat.le_mul_self _) (Nat.le_add_right _ _))
lemma nppair_le_right (a b : ℕ) : b ≤ ppair a b := by
  show b ≤ (a + b) * (a + b) + b
  exact Nat.le_add_left b _

lemma le_matrixToVec : ∀ {k : ℕ} (v : Fin k → ℕ) (j : Fin k), v j ≤ matrixToVec v
  | 0, _, j => j.elim0
  | k + 1, v, j => by
    rw [matrixToVec_succ, adjoin_def]
    cases j using Fin.cases with
    | zero => exact le_trans (npair_le_left (v 0) (matrixToVec (Matrix.vecTail v))) (Nat.le_succ _)
    | succ j =>
      have h1 := le_matrixToVec (Matrix.vecTail v) j
      have h2 := npair_le_right (Matrix.vecHead v) (matrixToVec (Matrix.vecTail v))
      exact le_trans h1 (by omega)

lemma matrixToVec_mono : ∀ {k : ℕ} {v w : Fin k → ℕ}, (∀ i, v i ≤ w i) → matrixToVec v ≤ matrixToVec w
  | 0, _, _, _ => le_rfl
  | k + 1, v, w, h => by
    rw [matrixToVec_succ, matrixToVec_succ, adjoin_def, adjoin_def]
    show ⟪v 0, matrixToVec (Matrix.vecTail v)⟫ + 1 ≤ ⟪w 0, matrixToVec (Matrix.vecTail w)⟫ + 1
    have := npair_le_pair (h 0)
      (matrixToVec_mono (v := Matrix.vecTail v) (w := Matrix.vecTail w) (fun i ↦ h i.succ))
    omega

end order

/-! ### 1. The code of a binary numeral is exponential in its bit length -/

section binNumeralSize

open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

lemma pair_zero_right (a : ℕ) : ⟪a, 0⟫ = a * a + a := by
  unfold pair
  rw [if_neg (Nat.not_lt_zero a)]
  rfl

lemma sq_le_qqMul (x y : ℕ) : y * y ≤ x ^* y := by
  unfold qqMul qqFunc
  show y * y ≤ ⟪2, 2, mulIndex, x ∷ y ∷ 0⟫ + 1
  have h1 : y * y ≤ x ∷ y ∷ 0 := by
    rw [adjoin_def, adjoin_def, pair_zero_right]
    have := npair_le_right x (y * y + y + 1)
    omega
  exact le_trans h1 (le_trans (npair_le_right _ _)
    (le_trans (npair_le_right _ _) (le_trans (npair_le_right _ _) (Nat.le_succ _))))

lemma le_qqAdd_left (x y : ℕ) : x ≤ x ^+ y := by
  unfold qqAdd qqFunc
  show x ≤ ⟪2, 2, addIndex, x ∷ y ∷ 0⟫ + 1
  have h1 : x ≤ x ∷ y ∷ 0 := by
    rw [adjoin_def]
    have := npair_le_left x (y ∷ 0)
    omega
  exact le_trans h1 (le_trans (npair_le_right _ _)
    (le_trans (npair_le_right _ _) (le_trans (npair_le_right _ _) (Nat.le_succ _))))

lemma two_le_qqZero : 2 ≤ (𝟎 : ℕ) := by
  unfold Arithmetic.zero qqFuncN
  have := Nat.left_le_pair 2 (Nat.pair 0 (Nat.pair zeroIndex 0))
  omega

lemma four_le_qqOne : 4 ≤ (𝟏 : ℕ) := by
  unfold Arithmetic.one qqFuncN
  have h : ∀ z, 6 ≤ Nat.pair 2 z := fun z ↦ by
    unfold Nat.pair
    split_ifs with h
    · nlinarith
    · omega
  have := h (Nat.pair 0 (Nat.pair oneIndex 0))
  omega

/-- **The code of a binary numeral is exponential in its value's bit length**: `2^(n+1) ≤ binNumeral n`. -/
theorem two_pow_succ_le_binNumeral : ∀ n : ℕ, 2 ^ (n + 1) ≤ binNumeral (n : ℕ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | k
    · rw [binNumeral_zero]; exact two_le_qqZero
    · show 2 ^ (1 + 1) ≤ binNumeral (1 : ℕ)
      rw [binNumeral_one]; exact four_le_qqOne
    · obtain ⟨m, hm1, hm⟩ : ∃ m, 1 ≤ m ∧ (k + 2 = 2 * m ∨ k + 2 = 2 * m + 1) :=
        ⟨(k + 2) / 2, by omega, by omega⟩
      have ihm := ih m (by omega)
      have hsq : 2 ^ (2 * m + 2) ≤ binNumeral (m : ℕ) * binNumeral (m : ℕ) := by
        rw [show 2 * m + 2 = (m + 1) + (m + 1) by ring, Nat.pow_add]
        exact Nat.mul_le_mul ihm ihm
      rcases hm with hm | hm
      · have e : binNumeral (2 * m : ℕ) = 𝟐 ^* binNumeral (m : ℕ) := binNumeral_two_mul (le_def.mpr (fle_of_nle hm1))
        rw [hm, e]
        exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (le_trans hsq (sq_le_qqMul _ _))
      · have e : binNumeral (2 * m + 1 : ℕ) = (𝟐 ^* binNumeral (m : ℕ)) ^+ 𝟏 :=
          binNumeral_two_mul_add_one (le_def.mpr (fle_of_nle hm1))
        rw [hm, e]
        exact le_trans hsq (le_trans (sq_le_qqMul _ _) (le_qqAdd_left _ _))

/-- The bit length of the code of the binary numeral of `n` is at least `n + 2`. -/
theorem size_binNumeral_ge (n : ℕ) : n + 2 ≤ Nat.size (binNumeral (n : ℕ)) :=
  Nat.lt_size.mpr (two_pow_succ_le_binNumeral n)

end binNumeralSize

/-! ### 2. Occurrence of a bound variable, and the code of anything it is replaced by -/

section occurs

variable {L : Language}

/-- The bound variable `#i` occurs in the term. -/
def TOcc {ξ : Type*} {n : ℕ} (i : Fin n) : Semiterm L ξ n → Prop
  | #j => j = i
  | &_ => False
  | .func _ v => ∃ j, TOcc i (v j)

/-- The bound variable `#i` occurs in the formula. -/
def FOcc {ξ : Type*} : {n : ℕ} → Fin n → Semiformula L ξ n → Prop
  | _, i, .rel _ v => ∃ j, TOcc i (v j)
  | _, i, .nrel _ v => ∃ j, TOcc i (v j)
  | _, _, .verum => False
  | _, _, .falsum => False
  | _, i, .and φ ψ => FOcc i φ ∨ FOcc i ψ
  | _, i, .or φ ψ => FOcc i φ ∨ FOcc i ψ
  | _, i, .all φ => FOcc i.succ φ
  | _, i, .exs φ => FOcc i.succ φ

variable [L.Encodable] [L.LORDefinable]

/-- The code of a component of a vector is at most the code of the vector. -/
lemma le_semitermVec_val {k n : ℕ} (v : SemitermVec ℕ L k n) (j : Fin k) : (v j).val ≤ v.val :=
  le_matrixToVec (fun i ↦ (v i).val) j

lemma le_qqFunc (k f v : ℕ) : v ≤ ^func k f v := by
  unfold qqFunc
  exact le_trans (npair_le_right _ _) (le_trans (npair_le_right _ _) (le_trans (npair_le_right _ _) (Nat.le_succ _)))

lemma le_qqRel (k R v : ℕ) : v ≤ ^rel k R v := by
  unfold qqRel
  exact le_trans (npair_le_right _ _) (le_trans (npair_le_right _ _) (le_trans (npair_le_right _ _) (Nat.le_succ _)))

lemma le_qqNRel (k R v : ℕ) : v ≤ ^nrel k R v := by
  unfold qqNRel
  exact le_trans (npair_le_right _ _) (le_trans (npair_le_right _ _) (le_trans (npair_le_right _ _) (Nat.le_succ _)))

lemma le_qqAnd_left (p q : ℕ) : p ≤ p ^⋏ q := by
  unfold qqAnd
  exact le_trans (npair_le_left _ _) (le_trans (npair_le_right _ _) (Nat.le_succ _))
lemma le_qqAnd_right (p q : ℕ) : q ≤ p ^⋏ q := by
  unfold qqAnd
  exact le_trans (npair_le_right _ _) (le_trans (npair_le_right _ _) (Nat.le_succ _))
lemma le_qqOr_left (p q : ℕ) : p ≤ p ^⋎ q := by
  unfold qqOr
  exact le_trans (npair_le_left _ _) (le_trans (npair_le_right _ _) (Nat.le_succ _))
lemma le_qqOr_right (p q : ℕ) : q ≤ p ^⋎ q := by
  unfold qqOr
  exact le_trans (npair_le_right _ _) (le_trans (npair_le_right _ _) (Nat.le_succ _))
lemma le_qqAll (p : ℕ) : p ≤ ^∀ p := by
  unfold qqAll
  exact le_trans (npair_le_right _ _) (Nat.le_succ _)
lemma le_qqExs (p : ℕ) : p ≤ ^∃ p := by
  unfold qqExs
  exact le_trans (npair_le_right _ _) (Nat.le_succ _)

/-- A component of a function application has a smaller code. -/
lemma quote_le_quote_func {n k : ℕ} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) (j : Fin k) :
    (⌜v j⌝ : ℕ) ≤ ⌜Semiterm.func f v⌝ := by
  rw [Semiterm.quote_func]
  exact le_trans (le_semitermVec_val (fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm ℕ L n)) j) (le_qqFunc _ _ _)

/-- `bShift` does not decrease codes. -/
lemma quote_le_quote_bShift {n : ℕ} : ∀ t : SyntacticSemiterm L n, (⌜t⌝ : ℕ) ≤ ⌜Rew.bShift t⌝
  | #x => by
    rw [Rew.bShift_bvar, Semiterm.quote_bvar, Semiterm.quote_bvar]
    unfold qqBvar
    rw [natCast_nat, natCast_nat, Fin.val_succ]
    have := npair_le_pair (le_refl 0) (Nat.le_succ (x : ℕ))
    simp only [Nat.succ_eq_add_one] at this ⊢
    omega
  | &x => le_of_eq (by rw [Rew.bShift_fvar, Semiterm.quote_fvar, Semiterm.quote_fvar])
  | .func f v => by
    rw [Rew.func, Semiterm.quote_func, Semiterm.quote_func]
    unfold qqFunc
    have : (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm ℕ L n)) ≤
        SemitermVec.val fun i ↦ (⌜(⇑Rew.bShift ∘ v) i⌝ : Bootstrapping.Semiterm ℕ L (n + 1)) :=
      matrixToVec_mono (fun i ↦ quote_le_quote_bShift (v i))
    have h := npair_le_pair (le_refl (⌜f⌝ : ℕ)) this
    exact Nat.add_le_add_right (npair_le_pair (le_refl 2) (npair_le_pair (le_refl _) h)) 1

/-- **Occurrence bounds the code**: if `#i` occurs in `t` then the code of `ω t` is at least the
code of `ω #i`. -/
lemma le_quote_rew_term {ξ : Type*} {n m : ℕ} (ω : Rew L ξ n ℕ m) (i : Fin n) (C : ℕ) (hC : C ≤ ⌜ω #i⌝) :
    ∀ t : Semiterm L ξ n, TOcc i t → C ≤ ⌜ω t⌝
  | #j, h => by
    have : j = i := h
    subst this; exact hC
  | &x, h => h.elim
  | .func f v, h => by
    obtain ⟨j, hj⟩ := h
    rw [Rew.func]
    exact le_trans (le_quote_rew_term ω i C hC (v j) hj) (quote_le_quote_func f (fun i ↦ ω (v i)) j)

lemma le_quote_rew_formula {ξ : Type*} {n : ℕ} (φ : Semiformula L ξ n) :
    ∀ {m : ℕ} (ω : Rew L ξ n ℕ m) (i : Fin n) (C : ℕ), C ≤ ⌜ω #i⌝ → FOcc i φ → C ≤ ⌜ω ▹ φ⌝ := by
  induction φ with
  | rel R v =>
    intro m ω i C hC h
    obtain ⟨j, hj⟩ := h
    rw [Semiformula.rew_rel, Semiformula.quote_rel]
    exact le_trans (le_quote_rew_term ω i C hC (v j) hj)
      (le_trans (le_semitermVec_val (fun i ↦ (⌜ω (v i)⌝ : Bootstrapping.Semiterm ℕ L m)) j) (le_qqRel _ _ _))
  | nrel R v =>
    intro m ω i C hC h
    obtain ⟨j, hj⟩ := h
    rw [Semiformula.rew_nrel, Semiformula.quote_nrel]
    exact le_trans (le_quote_rew_term ω i C hC (v j) hj)
      (le_trans (le_semitermVec_val (fun i ↦ (⌜ω (v i)⌝ : Bootstrapping.Semiterm ℕ L m)) j) (le_qqNRel _ _ _))
  | verum => intro _ _ _ _ _ h; exact h.elim
  | falsum => intro _ _ _ _ _ h; exact h.elim
  | and φ ψ ihφ ihψ =>
    intro m ω i C hC h
    show C ≤ ⌜ω ▹ (φ ⋏ ψ)⌝
    rw [LogicalConnective.HomClass.map_and, Semiformula.quote_and]
    rcases h with h | h
    · exact le_trans (ihφ ω i C hC h) (le_qqAnd_left _ _)
    · exact le_trans (ihψ ω i C hC h) (le_qqAnd_right _ _)
  | or φ ψ ihφ ihψ =>
    intro m ω i C hC h
    show C ≤ ⌜ω ▹ (φ ⋎ ψ)⌝
    rw [LogicalConnective.HomClass.map_or, Semiformula.quote_or]
    rcases h with h | h
    · exact le_trans (ihφ ω i C hC h) (le_qqOr_left _ _)
    · exact le_trans (ihψ ω i C hC h) (le_qqOr_right _ _)
  | all φ ih =>
    intro m ω i C hC h
    show C ≤ ⌜ω ▹ (∀¹ φ)⌝
    rw [Rewriting.app_all, Semiformula.quote_all]
    have hC' : C ≤ ⌜ω.q #(i.succ)⌝ := by
      rw [Rew.q_bvar_succ]; exact le_trans hC (quote_le_quote_bShift _)
    exact le_trans (ih ω.q i.succ C hC' h) (le_qqAll _)
  | exs φ ih =>
    intro m ω i C hC h
    show C ≤ ⌜ω ▹ (∃¹ φ)⌝
    rw [Rewriting.app_exs, Semiformula.quote_ex]
    have hC' : C ≤ ⌜ω.q #(i.succ)⌝ := by
      rw [Rew.q_bvar_succ]; exact le_trans hC (quote_le_quote_bShift _)
    exact le_trans (ih ω.q i.succ C hC' h) (le_qqExs _)

end occurs

/-! ### 3. The budget variable occurs in `lenProvG`; the template of a box carries `binNumeral k` -/

section boxCode

variable {L : Language}

@[simp] lemma FOcc_exs {ξ : Type*} {n : ℕ} (i : Fin n) (φ : Semiformula L ξ (n + 1)) :
    FOcc i (∃¹ φ) ↔ FOcc i.succ φ := Iff.rfl
@[simp] lemma FOcc_all {ξ : Type*} {n : ℕ} (i : Fin n) (φ : Semiformula L ξ (n + 1)) :
    FOcc i (∀¹ φ) ↔ FOcc i.succ φ := Iff.rfl
@[simp] lemma FOcc_and {ξ : Type*} {n : ℕ} (i : Fin n) (φ ψ : Semiformula L ξ n) :
    FOcc i (φ ⋏ ψ) ↔ FOcc i φ ∨ FOcc i ψ := Iff.rfl
@[simp] lemma FOcc_or {ξ : Type*} {n : ℕ} (i : Fin n) (φ ψ : Semiformula L ξ n) :
    FOcc i (φ ⋎ ψ) ↔ FOcc i φ ∨ FOcc i ψ := Iff.rfl
@[simp] lemma FOcc_rel {ξ : Type*} {n k : ℕ} (i : Fin n) (R : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    FOcc i (Semiformula.rel R v) ↔ ∃ j, TOcc i (v j) := Iff.rfl

/-- Occurrence is invariant under negation. -/
lemma FOcc_neg {ξ : Type*} : ∀ {n : ℕ} (i : Fin n) (φ : Semiformula L ξ n), FOcc i (∼φ) ↔ FOcc i φ
  | _, _, .rel _ _ => Iff.rfl
  | _, _, .nrel _ _ => Iff.rfl
  | _, _, .verum => Iff.rfl
  | _, _, .falsum => Iff.rfl
  | _, i, .and φ ψ => or_congr (FOcc_neg i φ) (FOcc_neg i ψ)
  | _, i, .or φ ψ => or_congr (FOcc_neg i φ) (FOcc_neg i ψ)
  | _, i, .all φ => FOcc_neg i.succ φ
  | _, i, .exs φ => FOcc_neg i.succ φ

/-- Occurrence is preserved by a language map. -/
lemma TOcc_lMap {L₁ L₂ : Language} (Φ : L₁ →ᵥ L₂) {ξ : Type*} {n : ℕ} (i : Fin n) :
    ∀ t : Semiterm L₁ ξ n, TOcc i t → TOcc i (Semiterm.lMap Φ t)
  | #j, h => by rw [Semiterm.lMap_bvar]; exact h
  | &x, h => h.elim
  | .func f v, h => by
    obtain ⟨j, hj⟩ := h
    rw [Semiterm.lMap_func]
    exact ⟨j, TOcc_lMap Φ i (v j) hj⟩

lemma FOcc_lMap {L₁ L₂ : Language} (Φ : L₁ →ᵥ L₂) {ξ : Type*} :
    ∀ {n : ℕ} (i : Fin n) (φ : Semiformula L₁ ξ n), FOcc i φ → FOcc i (Semiformula.lMap Φ φ)
  | _, i, .rel R v, h => by
    obtain ⟨j, hj⟩ := h
    rw [Semiformula.lMap_rel]
    exact ⟨j, TOcc_lMap Φ i (v j) hj⟩
  | _, i, .nrel R v, h => by
    obtain ⟨j, hj⟩ := h
    rw [Semiformula.lMap_nrel]
    exact ⟨j, TOcc_lMap Φ i (v j) hj⟩
  | _, _, .verum, h => h.elim
  | _, _, .falsum, h => h.elim
  | _, i, .and φ ψ, h => by
    show FOcc i (Semiformula.lMap Φ (φ ⋏ ψ))
    rw [LogicalConnective.HomClass.map_and, FOcc_and]
    exact h.imp (FOcc_lMap Φ i φ) (FOcc_lMap Φ i ψ)
  | _, i, .or φ ψ, h => by
    show FOcc i (Semiformula.lMap Φ (φ ⋎ ψ))
    rw [LogicalConnective.HomClass.map_or, FOcc_or]
    exact h.imp (FOcc_lMap Φ i φ) (FOcc_lMap Φ i ψ)
  | _, i, .all φ, h => by
    show FOcc i (Semiformula.lMap Φ (∀¹ φ))
    rw [Semiformula.lMap_all, FOcc_all]
    exact FOcc_lMap Φ i.succ φ h
  | _, i, .exs φ, h => by
    show FOcc i (Semiformula.lMap Φ (∃¹ φ))
    rw [Semiformula.lMap_exs, FOcc_exs]
    exact FOcc_lMap Φ i.succ φ h

/-- **The budget variable occurs in the provability predicate**: `k` (the first variable of
`lenBox T`) is written in the atom `n ≤ k` that bounds the proof length. -/
lemma fOcc_lenBox : FOcc (0 : Fin 2) ((lenBox TAct).sigma.val) := by
  unfold lenBox
  simp only [HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma]
  rw [FOcc_exs, FOcc_and]
  refine Or.inr ?_
  unfold Semiformula.bexsLT bexs
  rw [FOcc_exs, FOcc_and]
  refine Or.inr ?_
  rw [FOcc_and]
  refine Or.inr ?_
  rw [FOcc_exs, FOcc_and]
  refine Or.inr ?_
  rw [Semiformula.Operator.le_def, FOcc_or]
  exact Or.inl ⟨1, rfl⟩

lemma fOcc_lenProvG : FOcc (0 : Fin 2) lenProvG := FOcc_lMap emb _ _ fOcc_lenBox

-- `quote_numTB` lives in `Agents/Code.lean` since 2026-10-01.

/-- The budget-carrying conjunct of a box template carries the code `binNumeral k`, for any
substitution vector whose first entry is the numeral. NOTE: this lemma is never applied
across a `simp`-produced goal — its tactic script is replayed inside each shape lemma below;
checking a separately elaborated quote of the giant `lenProvG` against a `simp`-produced
goal makes `isDefEq` unfold the quote (the second hang of this file, proof-craft note). -/
lemma binNumeral_le_quote_emb_subst (k : ℕ) {n : ℕ} (σ : Semisentence LAct 2) (hσ : FOcc 0 σ)
    (w : Fin 2 → Semiterm LAct Empty n) (hw : w 0 = cl (numTB k)) :
    binNumeral k ≤ (⌜(Rew.emb ▹ (σ ⇜ w) : Semiproposition LAct n)⌝ : ℕ) := by
  unfold Rewriting.subst
  rw [← TransitiveRewriting.comp_app]
  refine le_quote_rew_formula σ _ 0 (binNumeral k) ?_ hσ
  rw [Rew.comp_app, Rew.subst_bvar, hw, quote_emb_cl, ← Semiterm.empty_quote_def, quote_numTB]

/-- The code shape of a box template, with the conjuncts abstracted: the last conjunct's code
is below the whole. Stated in the exact syntactic form so that no unification ever unfolds
`qqAnd`/`qqExs` (down to `pair` and its `if`) — the first hang of this file. -/
lemma le_boxShapeCode (a b c d : ℕ) : d ≤ ^∃ (^∃ (a ^⋏ (b ^⋏ ^∃ (c ^⋏ d)))) :=
  le_trans (le_qqAnd_right c d) (le_trans (le_qqExs (c ^⋏ d))
    (le_trans (le_qqAnd_right b (^∃ (c ^⋏ d))) (le_trans (le_qqAnd_right a (b ^⋏ ^∃ (c ^⋏ d)))
      (le_trans (le_qqExs (a ^⋏ (b ^⋏ ^∃ (c ^⋏ d)))) (le_qqExs (^∃ (a ^⋏ (b ^⋏ ^∃ (c ^⋏ d)))))))))

lemma le_boxShapeCode_neg (a b c d : ℕ) : d ≤ ^∀ (^∀ (a ^⋎ (b ^⋎ ^∀ (c ^⋎ d)))) :=
  le_trans (le_qqOr_right c d) (le_trans (le_qqAll (c ^⋎ d))
    (le_trans (le_qqOr_right b (^∀ (c ^⋎ d))) (le_trans (le_qqOr_right a (b ^⋎ ^∀ (c ^⋎ d)))
      (le_trans (le_qqAll (a ^⋎ (b ^⋎ ^∀ (c ^⋎ d)))) (le_qqAll (^∀ (a ^⋎ (b ^⋎ ^∀ (c ^⋎ d)))))))))

/-- **The shape of `template (.box k ψ)` carries `binNumeral k`**: whatever the fixed conjuncts `A B C`
and the vector `w` (first entry the numeral) are, the code is at least `binNumeral k`. -/
lemma binNumeral_le_quote_boxShape (k : ℕ) {w : Fin 2 → Semiterm LAct Empty 9} (hw : w 0 = cl (numTB k))
    (A B : Semisentence LAct 8) (C : Semisentence LAct 9) :
    binNumeral k ≤ (⌜((∃¹ (∃¹ (A ⋏ (B ⋏ (∃¹ (C ⋏ (lenProvG ⇜ w))))))) : Semisentence LAct 6)⌝ : ℕ) := by
  rw [Sentence.quote_def]
  simp only [Rewriting.emb, Rewriting.app_exs, Rew.q_emb, LogicalConnective.HomClass.map_and,
    Semiformula.quote_ex, Semiformula.quote_and]
  refine le_trans ?_ (le_boxShapeCode _ _ _ _)
  unfold Rewriting.subst
  rw [← TransitiveRewriting.comp_app]
  refine le_quote_rew_formula lenProvG _ 0 (binNumeral k) ?_ fOcc_lenProvG
  rw [Rew.comp_app, Rew.subst_bvar, hw, quote_emb_cl, ← Semiterm.empty_quote_def, quote_numTB]

/-- The negated shape (`∼` pushed through the connectives). -/
lemma binNumeral_le_quote_allShape (k : ℕ) {w : Fin 2 → Semiterm LAct Empty 9} (hw : w 0 = cl (numTB k))
    (A B : Semisentence LAct 8) (C : Semisentence LAct 9) :
    binNumeral k ≤ (⌜((∀¹ (∀¹ (A ⋎ (B ⋎ (∀¹ (C ⋎ ((∼lenProvG) ⇜ w))))))) : Semisentence LAct 6)⌝ : ℕ) := by
  rw [Sentence.quote_def]
  simp only [Rewriting.emb, Rewriting.app_all, Rew.q_emb, LogicalConnective.HomClass.map_or,
    Semiformula.quote_all, Semiformula.quote_or]
  refine le_trans ?_ (le_boxShapeCode_neg _ _ _ _)
  unfold Rewriting.subst
  rw [← TransitiveRewriting.comp_app]
  refine le_quote_rew_formula (∼lenProvG) _ 0 (binNumeral k) ?_ ((FOcc_neg _ _).mpr fOcc_lenProvG)
  rw [Rew.comp_app, Rew.subst_bvar, hw, quote_emb_cl, ← Semiterm.empty_quote_def, quote_numTB]

lemma neg_boxShape (A B : Semisentence LAct 8) (C D : Semisentence LAct 9) :
    ((∼ (∃¹ (∃¹ (A ⋏ (B ⋏ (∃¹ (C ⋏ D))))))) : Semisentence LAct 6) =
    ∀¹ (∀¹ (∼A ⋎ (∼B ⋎ (∀¹ (∼C ⋎ ∼D))))) := rfl

lemma neg_subst {n : ℕ} (σ : Semisentence LAct 2) (w : Fin 2 → Semiterm LAct Empty n) :
    ((∼(σ ⇜ w)) : Semisentence LAct n) = (∼σ) ⇜ w := by
  unfold Rewriting.subst
  rw [LogicalConnective.HomClass.map_neg]

lemma binNumeral_le_quote_boxShape_neg (k : ℕ) {w : Fin 2 → Semiterm LAct Empty 9} (hw : w 0 = cl (numTB k))
    (A B : Semisentence LAct 8) (C : Semisentence LAct 9) :
    binNumeral k ≤ (⌜((∼ (∃¹ (∃¹ (A ⋏ (B ⋏ (∃¹ (C ⋏ (lenProvG ⇜ w)))))))) : Semisentence LAct 6)⌝ : ℕ) := by
  rw [neg_boxShape, neg_subst]
  exact binNumeral_le_quote_allShape k hw _ _ _

lemma lMap_swap_numTB (c : ℕ) : Semiterm.lMap swap (numTB c) = numTB c := term_lMap_swap_emb _

lemma lMap_swap_neg_lenProvG : Semiformula.lMap swap (∼lenProvG) = ∼lenProvG := by
  rw [LogicalConnective.HomClass.map_neg, lMap_swap_lenProvG]

/-- The transposed shape: `swap` fixes the numeral, so the bound survives `lMap swap`. -/
lemma binNumeral_le_quote_boxShape_swap (k : ℕ) {w : Fin 2 → Semiterm LAct Empty 9} (hw : w 0 = cl (numTB k))
    (A B : Semisentence LAct 8) (C : Semisentence LAct 9) :
    binNumeral k ≤ (⌜(Semiformula.lMap swap ((∃¹ (∃¹ (A ⋏ (B ⋏ (∃¹ (C ⋏ (lenProvG ⇜ w))))))) : Semisentence LAct 6))⌝ : ℕ) := by
  simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
    lMap_swap_lenProvG]
  rw [Sentence.quote_def]
  simp only [Rewriting.emb, Rewriting.app_exs, Rew.q_emb, LogicalConnective.HomClass.map_and,
    Semiformula.quote_ex, Semiformula.quote_and]
  refine le_trans ?_ (le_boxShapeCode _ _ _ _)
  unfold Rewriting.subst
  rw [← TransitiveRewriting.comp_app]
  refine le_quote_rew_formula lenProvG _ 0 (binNumeral k) ?_ fOcc_lenProvG
  rw [Rew.comp_app, Rew.subst_bvar]
  show binNumeral k ≤ ⌜Rew.emb (Semiterm.lMap swap (w 0))⌝
  rw [hw, lMap_swap_cl, lMap_swap_numTB, quote_emb_cl, ← Semiterm.empty_quote_def, quote_numTB]

lemma binNumeral_le_quote_boxShape_swap_neg (k : ℕ) {w : Fin 2 → Semiterm LAct Empty 9} (hw : w 0 = cl (numTB k))
    (A B : Semisentence LAct 8) (C : Semisentence LAct 9) :
    binNumeral k ≤ (⌜((∼ (Semiformula.lMap swap ((∃¹ (∃¹ (A ⋏ (B ⋏ (∃¹ (C ⋏ (lenProvG ⇜ w))))))) : Semisentence LAct 6))) : Semisentence LAct 6)⌝ : ℕ) := by
  rw [← LogicalConnective.HomClass.map_neg, neg_boxShape, neg_subst]
  simp only [Semiformula.lMap_all, LogicalConnective.HomClass.map_or, Semiformula.lMap_subst,
    lMap_swap_neg_lenProvG]
  rw [Sentence.quote_def]
  simp only [Rewriting.emb, Rewriting.app_all, Rew.q_emb, LogicalConnective.HomClass.map_or,
    Semiformula.quote_all, Semiformula.quote_or]
  refine le_trans ?_ (le_boxShapeCode_neg _ _ _ _)
  unfold Rewriting.subst
  rw [← TransitiveRewriting.comp_app]
  refine le_quote_rew_formula (∼lenProvG) _ 0 (binNumeral k) ?_ ((FOcc_neg _ _).mpr fOcc_lenProvG)
  rw [Rew.comp_app, Rew.subst_bvar]
  show binNumeral k ≤ ⌜Rew.emb (Semiterm.lMap swap (w 0))⌝
  rw [hw, lMap_swap_cl, lMap_swap_numTB, quote_emb_cl, ← Semiterm.empty_quote_def, quote_numTB]

end boxCode

/-! ### 4. Formulas with a box at budget `k`: their template codes are `≥ binNumeral k` -/

section hasBox

/-- `HasBox k φ`: `φ` contains `□_k` at a Boolean position (under `.impl`/`.neg` only; a box
NESTED inside another box is not counted — it sits inside a code constant, see the docstring). -/
inductive HasBox (k : ℕ) : PD.Formula → Prop
  | box (ψ : PD.Formula) : HasBox k (.box k ψ)
  | implL {φ} (ψ : PD.Formula) : HasBox k φ → HasBox k (.impl φ ψ)
  | implR (φ : PD.Formula) {ψ} : HasBox k ψ → HasBox k (.impl φ ψ)
  | neg {φ} : HasBox k φ → HasBox k (.neg φ)

/-- `c` is below the code of `σ` and of `∼σ` (the pair is what survives `.impl`/`.neg`). -/
def GoodCode (c : ℕ) (σ : Semisentence LAct 6) : Prop := c ≤ (⌜σ⌝ : ℕ) ∧ c ≤ (⌜(∼σ : Semisentence LAct 6)⌝ : ℕ)

lemma tilde_tilde (σ : Semisentence LAct 6) : ∼∼σ = σ := Semiformula.neg_neg σ

lemma quote_or_sentence (σ τ : Semisentence LAct 6) : (⌜(σ ⋎ τ : Semisentence LAct 6)⌝ : ℕ) = ⌜σ⌝ ^⋎ ⌜τ⌝ := by
  rw [Sentence.quote_def, Sentence.quote_def, Sentence.quote_def, LogicalConnective.HomClass.map_or,
    Semiformula.quote_or]

lemma quote_and_sentence (σ τ : Semisentence LAct 6) : (⌜(σ ⋏ τ : Semisentence LAct 6)⌝ : ℕ) = ⌜σ⌝ ^⋏ ⌜τ⌝ := by
  rw [Sentence.quote_def, Sentence.quote_def, Sentence.quote_def, LogicalConnective.HomClass.map_and,
    Semiformula.quote_and]

lemma GoodCode.impl_left {c : ℕ} {σ : Semisentence LAct 6} (h : GoodCode c σ) (τ : Semisentence LAct 6) :
    GoodCode c (σ 🡒 τ) := by
  refine ⟨?_, ?_⟩
  · rw [Semiformula.imp_eq, quote_or_sentence]
    exact le_trans h.2 (le_qqOr_left _ _)
  · rw [Semiformula.imp_eq, show (∼(∼σ ⋎ τ) : Semisentence LAct 6) = σ ⋏ ∼τ by
      rw [LogicalConnective.DeMorgan.or, tilde_tilde], quote_and_sentence]
    exact le_trans h.1 (le_qqAnd_left _ _)

lemma GoodCode.impl_right {c : ℕ} (σ : Semisentence LAct 6) {τ : Semisentence LAct 6} (h : GoodCode c τ) :
    GoodCode c (σ 🡒 τ) := by
  refine ⟨?_, ?_⟩
  · rw [Semiformula.imp_eq, quote_or_sentence]
    exact le_trans h.1 (le_qqOr_right _ _)
  · rw [Semiformula.imp_eq, show (∼(∼σ ⋎ τ) : Semisentence LAct 6) = σ ⋏ ∼τ by
      rw [LogicalConnective.DeMorgan.or, tilde_tilde], quote_and_sentence]
    exact le_trans h.2 (le_qqAnd_right _ _)

lemma GoodCode.neg {c : ℕ} {σ : Semisentence LAct 6} (h : GoodCode c σ) : GoodCode c (∼σ) :=
  ⟨h.2, by rw [tilde_tilde]; exact h.1⟩

/-- On the template of a `.box k ψ`. -/
lemma goodCode_template_box (k : ℕ) (ψ : PD.Formula) : GoodCode (binNumeral k) (template (.box k ψ)) := by
  rw [template_box]
  exact ⟨binNumeral_le_quote_boxShape k rfl _ _ _, binNumeral_le_quote_boxShape_neg k rfl _ _ _⟩

/-- On the transposed template of a `.box k ψ` (the numeral is `swap`-invariant). -/
lemma goodCode_lMap_swap_template_box (k : ℕ) (ψ : PD.Formula) :
    GoodCode (binNumeral k) (Semiformula.lMap swap (template (.box k ψ))) := by
  rw [template_box]
  exact ⟨binNumeral_le_quote_boxShape_swap k rfl _ _ _, binNumeral_le_quote_boxShape_swap_neg k rfl _ _ _⟩

theorem goodCode_template {k : ℕ} : ∀ {φ : PD.Formula}, HasBox k φ → GoodCode (binNumeral k) (template φ)
  | _, .box ψ => goodCode_template_box k ψ
  | _, .implL ψ h => by rw [template_impl]; exact (goodCode_template h).impl_left _
  | _, .implR φ h => by rw [template_impl]; exact (goodCode_template h).impl_right _
  | _, .neg h => by rw [template_neg]; exact (goodCode_template h).neg

theorem goodCode_lMap_swap_template {k : ℕ} : ∀ {φ : PD.Formula}, HasBox k φ →
    GoodCode (binNumeral k) (Semiformula.lMap swap (template φ))
  | _, .box ψ => goodCode_lMap_swap_template_box k ψ
  | _, .implL ψ h => by
    rw [template_impl, LogicalConnective.HomClass.map_imply]; exact (goodCode_lMap_swap_template h).impl_left _
  | _, .implR φ h => by
    rw [template_impl, LogicalConnective.HomClass.map_imply]; exact (goodCode_lMap_swap_template h).impl_right _
  | _, .neg h => by
    rw [template_neg, LogicalConnective.HomClass.map_neg]; exact (goodCode_lMap_swap_template h).neg

/-- **The template code of a box-carrying formula is at least `binNumeral k`.** -/
theorem binNumeral_le_templateCode {k : ℕ} {φ : PD.Formula} (h : HasBox k φ) (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    binNumeral k ≤ templateCode φ := by
  rw [templateCode_eq_quote_template φ hφ]
  exact (goodCode_template h).1

/-- … and so is its code-level transposition. -/
theorem binNumeral_le_revalueTemplate_templateCode {k : ℕ} {φ : PD.Formula} (h : HasBox k φ)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) :
    binNumeral k ≤ revalueTemplate 1 0 (templateCode φ) := by
  rw [templateCode_eq_quote_template φ hφ, revalueTemplate_quote_sentence]
  exact (goodCode_lMap_swap_template h).1

/-! #### The searcher's code and canonical numeral -/

lemma le_pSearch (k g p q : ℕ) : g ≤ pSearch k g p q := by
  unfold pSearch
  exact le_trans (nppair_le_left _ _) (le_trans (nppair_le_right _ _)
    (le_trans (nppair_le_right _ _) (Nat.le_succ _)))

/-- A searcher on a box-carrying guard has code `≥ binNumeral k`. -/
theorem binNumeral_le_progCode_search {k : ℕ} {φ : PD.Formula} (h : HasBox k φ) (k' : ℕ) (p q : PD.Prog)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) (hφ' : noBudgetSnapshotF φ = true := by noSnap_tac) :
    binNumeral k ≤ progCode (.search k' φ p q) := by
  rw [progCode_search_noSnap _ _ _ _ hφ']
  exact le_trans (binNumeral_le_templateCode h) (le_pSearch _ _ _ _)

theorem binNumeral_le_transposeCode_progCode_search {k : ℕ} {φ : PD.Formula} (h : HasBox k φ) (k' : ℕ) (p q : PD.Prog)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) (hφ' : noBudgetSnapshotF φ = true := by noSnap_tac) :
    binNumeral k ≤ transposeCode (progCode (.search k' φ p q)) := by
  rw [progCode_search_noSnap _ _ _ _ hφ', transposeCode, revalue_search]
  exact le_trans (binNumeral_le_revalueTemplate_templateCode h) (le_pSearch _ _ _ _)

/-- The canonical numeral (`min` of the code and its transposition) is still `≥ binNumeral k`. -/
theorem binNumeral_le_canonical_progCode_search {k : ℕ} {φ : PD.Formula} (h : HasBox k φ) (k' : ℕ) (p q : PD.Prog)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) (hφ' : noBudgetSnapshotF φ = true := by noSnap_tac) :
    binNumeral k ≤ canonical (progCode (.search k' φ p q)) := by
  unfold canonical
  split_ifs
  · exact binNumeral_le_progCode_search h k' p q hφ hφ'
  · exact binNumeral_le_transposeCode_progCode_search h k' p q hφ hφ'

/-- **The description of a box-carrying searcher has bit length `> k`** — Critch's (b) fails
for it regardless of how the numeral is written. (A box body is stored unabstracted, so the guard's own
`noBudgetSnapshotF` is what the searcher's code needs: it holds for every `.box`-headed guard.) -/
theorem size_canonical_progCode_search_ge {k : ℕ} {φ : PD.Formula} (h : HasBox k φ) (k' : ℕ) (p q : PD.Prog)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) (hφ' : noBudgetSnapshotF φ = true := by noSnap_tac) :
    k + 2 ≤ Nat.size (canonical (progCode (.search k' φ p q))) :=
  le_trans (size_binNumeral_ge k) (Nat.size_le_size (binNumeral_le_canonical_progCode_search h k' p q hφ hφ'))

end hasBox

/-! ### 5. The guard sentence of a box-carrying searcher is longer than its budget -/

section guardLength

variable {L : Language}

lemma emb_bShift {n : ℕ} : ∀ t : Semiterm LAct Empty n,
    (Rew.emb (Rew.bShift t) : SyntacticSemiterm LAct (n + 1)) = Rew.bShift (Rew.emb t)
  | #x => rfl
  | &x => x.elim
  | .func f v => by
    rw [Rew.func, Rew.func, Rew.func, Rew.func]
    congr 1
    funext i
    exact emb_bShift (v i)

/-- The `me`-description slot of a box template, after the players' descriptions are filled in:
three `bShift`s of the closed numeral. -/
lemma termLenMeta_emb_bShift3_canonicalMeta (x : ℕ) :
    termLenMeta (Rew.emb (Rew.bShift (Rew.bShift (Rew.bShift (canonicalMeta x)))) : SyntacticSemiterm LAct 3) =
    termLenMeta (Rew.emb (canonicalMeta x) : SyntacticSemiterm LAct 0) := by
  rw [emb_bShift, emb_bShift, emb_bShift, termLenMeta_bShift_of_bvFree (bvFree_emb _).bShift.bShift,
    termLenMeta_bShift_of_bvFree (bvFree_emb _).bShift, termLenMeta_bShift_of_bvFree (bvFree_emb _)]

/-- **A box translation writes the description of `me`**: the sentence `sentenceAt me opp (.box k ψ)`
is longer than the bit length of the canonical numeral of `progCode me`. -/
theorem size_canonical_le_formulaLenMeta_sentenceAt_box (me opp : PD.Prog) (k : ℕ) (ψ : PD.Formula) :
    Nat.size (canonical (progCode me)) + 1 ≤ formulaLenMeta (Rewriting.emb (sentenceAt me opp (.box k ψ)) : Proposition LAct) := by
  unfold sentenceAt
  rw [template_box, progAux_self, progAux_opp]
  simp only [Rewriting.subst, Rewriting.emb, Rewriting.app_exs, Rew.q_emb, LogicalConnective.HomClass.map_and,
    rew_descF, formulaLenMeta_exs, formulaLenMeta_and]
  refine le_trans ?_ (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ 1)
    (le_trans (Nat.le_add_right _ 1) (Nat.le_add_right _ 1))))
  refine le_trans ?_ (formulaLenMeta_emb_descF_ge _ _ _ _)
  show Nat.size (canonical (progCode me)) + 1 ≤
    termLenMeta (Rew.emb (Rew.bShift (Rew.bShift (Rew.bShift (canonicalMeta (progCode me))))) : SyntacticSemiterm LAct 3) + 1
  rw [termLenMeta_emb_bShift3_canonicalMeta]
  unfold canonicalMeta
  rw [termLenMeta_emb_lMap_emb]
  exact Nat.succ_le_succ (size_le_termLenMeta_codeTermMeta _)

lemma formulaLenMeta_emb_sentenceAt_impl (me opp : PD.Prog) (φ ψ : PD.Formula) :
    formulaLenMeta (Rewriting.emb (sentenceAt me opp (.impl φ ψ)) : Proposition LAct) =
    formulaLenMeta (Rewriting.emb (sentenceAt me opp φ) : Proposition LAct) + formulaLenMeta (Rewriting.emb (sentenceAt me opp ψ) : Proposition LAct) + 1 := by
  unfold sentenceAt
  rw [template_impl]
  unfold Rewriting.subst Rewriting.emb
  rw [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_imply, formulaLenMeta_imply]

lemma formulaLenMeta_emb_sentenceAt_neg (me opp : PD.Prog) (φ : PD.Formula) :
    formulaLenMeta (Rewriting.emb (sentenceAt me opp (.neg φ)) : Proposition LAct) =
    formulaLenMeta (Rewriting.emb (sentenceAt me opp φ) : Proposition LAct) := by
  unfold sentenceAt
  rw [template_neg]
  unfold Rewriting.subst Rewriting.emb
  rw [LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_neg, formulaLenMeta_neg]

/-- The description of `me` is written by the translation of every box-carrying formula. -/
theorem size_canonical_le_formulaLenMeta_sentenceAt_hasBox (me opp : PD.Prog) {k : ℕ} :
    ∀ {φ : PD.Formula}, HasBox k φ →
      Nat.size (canonical (progCode me)) + 1 ≤ formulaLenMeta (Rewriting.emb (sentenceAt me opp φ) : Proposition LAct)
  | _, .box ψ => size_canonical_le_formulaLenMeta_sentenceAt_box me opp k ψ
  | _, .implL ψ h => by
    rw [formulaLenMeta_emb_sentenceAt_impl]
    have := size_canonical_le_formulaLenMeta_sentenceAt_hasBox me opp h
    omega
  | _, .implR φ h => by
    rw [formulaLenMeta_emb_sentenceAt_impl]
    have := size_canonical_le_formulaLenMeta_sentenceAt_hasBox me opp h
    omega
  | _, .neg h => by
    rw [formulaLenMeta_emb_sentenceAt_neg]
    exact size_canonical_le_formulaLenMeta_sentenceAt_hasBox me opp h

/-- **The obstruction (Critch's (b) fails for box-carrying guards under Cantor-pair codes).**
A searcher `.search k' φ p q` whose guard `φ` mentions `□_k` — at ANY search budget `k'`, against
ANY opponent — has a guard sentence of more than `k` symbols: `sentenceAt me opp φ` writes the
canonical numeral of `progCode me`, `progCode me` stores `templateCode φ = ⌜template φ⌝`, the template writes
the budget as the binary numeral term `numTB k` whose CODE `binNumeral k` is `≥ 2^(k+1)`, and a
binary numeral of a number is at least as long as that number's bit length. -/
theorem box_guard_never_fits {k : ℕ} {φ : PD.Formula} (h : HasBox k φ) (k' : ℕ) (p q opp : PD.Prog)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) (hφ' : noBudgetSnapshotF φ = true := by noSnap_tac) :
    k < formulaLenMeta (Rewriting.emb (sentenceAt (.search k' φ p q) opp φ) : Proposition LAct) := by
  have h1 := size_canonical_le_formulaLenMeta_sentenceAt_hasBox (.search k' φ p q) opp h
  have h2 := size_canonical_progCode_search_ge h k' p q hφ hφ'
  omega

/-- In particular the guard of the SAME-budget searcher never fits, at any budget — the
negation of the `guard_fits` statement of `ArithS.Fit` for this searcher. -/
theorem not_box_guard_fits {k : ℕ} {φ : PD.Formula} (h : HasBox k φ) (k' : ℕ) (p q opp : PD.Prog)
    (hφ : noSelfIdxF φ = true := by noSelfIdx_tac) (hφ' : noBudgetSnapshotF φ = true := by noSnap_tac) :
    ¬ formulaLenMeta (Rewriting.emb (sentenceAt (.search k' φ p q) opp φ) : Proposition LAct) ≤ k :=
  Nat.not_le.mpr (box_guard_never_fits h k' p q opp hφ hφ')

/-- The zoo instance: `LegibleBot k k = .search k (□_k (I play C)) C D`. Its guard sentence
against any opponent has more than `k` symbols, so its search can never succeed. -/
theorem legibleBot_guard_never_fits (k : ℕ) (opp : PD.Prog) :
    k < formulaLenMeta (Rewriting.emb (sentenceAt (PD.Bots.LegibleBot k k) opp (.box k (.plays .self .opp .C))) :
      Proposition LAct) :=
  box_guard_never_fits (.box _) k _ _ opp

/-- Even the STAGGERED LegibleBot cannot fit its inner budget: the guard is longer than `kIn`
whatever the outer budget `kOut` is. -/
theorem legibleBot_staggered_guard_never_fits (kOut kIn : ℕ) (opp : PD.Prog) :
    kIn < formulaLenMeta (Rewriting.emb (sentenceAt (PD.Bots.LegibleBot kOut kIn) opp (.box kIn (.plays .self .opp .C))) :
      Proposition LAct) :=
  box_guard_never_fits (.box _) kOut _ _ opp

end guardLength

/-! ### 6. The positive side: the TEMPLATE of a box is `O(size k)` symbols -/

section templateLength

/-- The four conjuncts of `template (.box k ψ)`, named so that their symbol counts can be packaged
without ever being evaluated. -/
noncomputable def boxA : Semisentence LAct 8 := progAux .self 0 ⇜ ![#1, #2, #3, #4, #5, #6, #7]
noncomputable def boxB : Semisentence LAct 8 := progAux .opp 0 ⇜ ![#0, #2, #3, #4, #5, #6, #7]
noncomputable def boxC (ψ : PD.Formula) : Semisentence LAct 9 := guardCodeG ⇜ ![#0, cl (numTB (templateCode ψ)), #2, #1]

lemma template_box_eq (k : ℕ) (ψ : PD.Formula) :
    template (.box k ψ) = ∃¹ (∃¹ (boxA ⋏ (boxB ⋏ (∃¹ (boxC ψ ⋏ (lenProvG ⇜ ![cl (numTB k), #0])))))) :=
  template_box k ψ

lemma bvFree_emb_cl {n : ℕ} : ∀ t : ClosedSemiterm LAct 0, BvFree (Rew.emb (cl t) : SyntacticSemiterm LAct n)
  | #x => x.elim0
  | &x => x.elim
  | .func f v => by
    show BvFree (Rew.emb (Rew.castLE _ (Semiterm.func f v)) : SyntacticSemiterm LAct n)
    rw [Rew.func, Rew.func, bvFree_func]
    exact fun i ↦ bvFree_emb_cl (v i)

lemma termLenMeta_emb_numTB (c : ℕ) : termLenMeta (Rew.emb (numTB c) : SyntacticSemiterm LAct 0) ≤ 6 * Nat.size c + 1 := by
  unfold numTB
  rw [termLenMeta_emb_lMap_emb]
  exact termLenMeta_binNumeralMeta c

lemma emb_comp_subst {n : ℕ} (w : Fin 2 → Semiterm LAct Empty n) :
    (Rew.emb : Rew LAct Empty n ℕ n).comp (Rew.subst w) =
    (Rew.subst fun i ↦ (Rew.emb (w i) : SyntacticSemiterm LAct n)).comp Rew.emb := by
  ext x
  · simp [Rew.comp_app]
  · exact x.elim

/-- The substitution of `w` into a two-variable template, with `w 0` variable-free of length
`≤ t` and `w 1` a bound variable of index `≤ 1`, is at most `t + 1` times longer. -/
lemma formulaLenMeta_emb_subst2_le {n : ℕ} (σ : Semisentence LAct 2) (w : Fin 2 → Semiterm LAct Empty n) (t : ℕ)
    (hw0 : BvFree (Rew.emb (w 0) : SyntacticSemiterm LAct n) ∧ termLenMeta (Rew.emb (w 0) : SyntacticSemiterm LAct n) ≤ t)
    (hw1 : ∃ j : Fin n, w 1 = #j ∧ (j : ℕ) ≤ 1) :
    formulaLenMeta (Rew.emb ▹ (σ ⇜ w) : Semiproposition LAct n) ≤ formulaLenMeta (Rew.emb ▹ σ : Semiproposition LAct 2) * (t + 1) := by
  unfold Rewriting.subst
  rw [← TransitiveRewriting.comp_app, emb_comp_subst, TransitiveRewriting.comp_app]
  refine formulaLenMeta_rew_le (Nat.succ_pos t) _ _ ⟨fun i ↦ ?_, fun x ↦ Rew.subst_fvar _ x⟩
  rw [Rew.subst_bvar]
  match i with
  | 0 => exact Or.inl ⟨hw0.1, le_trans hw0.2 (Nat.le_succ _)⟩
  | 1 =>
    obtain ⟨j, hj, hle⟩ := hw1
    exact Or.inr ⟨j, by rw [hj, Rew.emb_bvar], hle⟩

lemma shape_le {a b c x y : ℕ} (h : x ≤ y) :
    a + (b + (c + x + 1 + 1) + 1) + 1 + 1 + 1 ≤ a + b + c + y + 6 := by omega

/-- The symbol count of the box shape, with the conjuncts abstracted. -/
lemma formulaLenMeta_emb_boxShape_le (A B : Semisentence LAct 8) (C : Semisentence LAct 9)
    (w : Fin 2 → Semiterm LAct Empty 9) (t : ℕ)
    (hw0 : BvFree (Rew.emb (w 0) : SyntacticSemiterm LAct 9) ∧ termLenMeta (Rew.emb (w 0) : SyntacticSemiterm LAct 9) ≤ t)
    (hw1 : ∃ j : Fin 9, w 1 = #j ∧ (j : ℕ) ≤ 1) :
    formulaLenMeta (Rewriting.emb ((∃¹ (∃¹ (A ⋏ (B ⋏ (∃¹ (C ⋏ (lenProvG ⇜ w))))))) : Semisentence LAct 6) : Semiproposition LAct 6) ≤
    formulaLenMeta (Rewriting.emb A : Semiproposition LAct 8) + formulaLenMeta (Rewriting.emb B : Semiproposition LAct 8) +
      formulaLenMeta (Rewriting.emb C : Semiproposition LAct 9) + formulaLenMeta (Rewriting.emb lenProvG : Semiproposition LAct 2) * (t + 1) + 6 := by
  simp only [Rewriting.emb, Rewriting.app_exs, Rew.q_emb, LogicalConnective.HomClass.map_and, formulaLenMeta_exs, formulaLenMeta_and]
  refine shape_le ?_
  exact formulaLenMeta_emb_subst2_le lenProvG w t hw0 hw1

/-- The symbol counts of the fixed conjuncts and of the provability predicate, packaged as
irreducible constants (never evaluated: `Fit.lean`'s proof-craft note). -/
noncomputable def cL : ℕ := formulaLenMeta (Rewriting.emb lenProvG : Semiproposition LAct 2)
noncomputable def cBox (ψ : PD.Formula) : ℕ :=
  formulaLenMeta (Rewriting.emb boxA : Semiproposition LAct 8) + formulaLenMeta (Rewriting.emb boxB : Semiproposition LAct 8) +
    formulaLenMeta (Rewriting.emb (boxC ψ) : Semiproposition LAct 9) + 2 * cL + 6

lemma arith_le (a b c L s : ℕ) : a + b + c + L * (6 * s + 1 + 1) + 6 ≤ a + b + c + 2 * L + 6 + 6 * L * s := by
  have e : L * (6 * s + 1 + 1) = 6 * L * s + 2 * L := by ring
  omega

/-- **The template of `□_k ψ` is `O(size k)` symbols**: `cBox ψ + 6 · cL · size k`. (Proof craft:
`cBox` is opened with `rw`, never with `unfold`/`show`/`delta` — any `whnf` of a closed `Nat`
expression `… + 6` makes Lean evaluate the symbol counts of the giant conjuncts.) -/
theorem formulaLenMeta_emb_template_box_le (k : ℕ) (ψ : PD.Formula) :
    formulaLenMeta (Rewriting.emb (template (.box k ψ)) : Semiproposition LAct 6) ≤ cBox ψ + 6 * cL * Nat.size k := by
  rw [template_box_eq]
  refine le_trans (formulaLenMeta_emb_boxShape_le _ _ _ _ (6 * Nat.size k + 1) ⟨bvFree_emb_cl _, ?_⟩ ⟨0, rfl, by omega⟩) ?_
  · show termLenMeta (Rew.emb (cl (numTB k)) : SyntacticSemiterm LAct 9) ≤ 6 * Nat.size k + 1
    rw [termLenMeta_emb_cl]; exact termLenMeta_emb_numTB k
  · rw [cBox, cL]
    exact arith_le _ _ _ _ _

attribute [irreducible] cL cBox

/-- The existential form asked for: constants depending only on `ψ`. -/
theorem exists_formulaLenMeta_template_box_const (ψ : PD.Formula) : ∃ c₀ c₁ : ℕ, ∀ k,
    formulaLenMeta (Rewriting.emb (template (.box k ψ)) : Semiproposition LAct 6) ≤ c₀ + c₁ * Nat.size k :=
  ⟨cBox ψ, 6 * cL, fun k ↦ formulaLenMeta_emb_template_box_le k ψ⟩

/-- A budget-parametric formula family whose only dependence on the budget is through
OUTERMOST box budgets equal to the budget itself (a box nested inside a box sits inside a
code constant and is NOT linear — see the module docstring). -/
inductive BudgetLinear : (ℕ → PD.Formula) → Prop
  | const (φ : PD.Formula) : BudgetLinear (fun _ ↦ φ)
  | box (ψ : PD.Formula) : BudgetLinear (fun k ↦ .box k ψ)
  | impl {F G} : BudgetLinear F → BudgetLinear G → BudgetLinear (fun k ↦ .impl (F k) (G k))
  | neg {F} : BudgetLinear F → BudgetLinear (fun k ↦ .neg (F k))

lemma formulaLenMeta_emb_template_impl (φ ψ : PD.Formula) :
    formulaLenMeta (Rewriting.emb (template (.impl φ ψ)) : Semiproposition LAct 6) =
    formulaLenMeta (Rewriting.emb (template φ) : Semiproposition LAct 6) + formulaLenMeta (Rewriting.emb (template ψ) : Semiproposition LAct 6) + 1 := by
  rw [template_impl]
  unfold Rewriting.emb
  rw [LogicalConnective.HomClass.map_imply, formulaLenMeta_imply]

lemma formulaLenMeta_emb_template_neg (φ : PD.Formula) :
    formulaLenMeta (Rewriting.emb (template (.neg φ)) : Semiproposition LAct 6) = formulaLenMeta (Rewriting.emb (template φ) : Semiproposition LAct 6) := by
  rw [template_neg]
  unfold Rewriting.emb
  rw [LogicalConnective.HomClass.map_neg, formulaLenMeta_neg]

/-- **Critch's (b) for the TEMPLATES of budget-linear families**: `c₀ + c₁ · size k`. -/
theorem exists_formulaLenMeta_template_const {F : ℕ → PD.Formula} (h : BudgetLinear F) :
    ∃ c₀ c₁ : ℕ, ∀ k, formulaLenMeta (Rewriting.emb (template (F k)) : Semiproposition LAct 6) ≤ c₀ + c₁ * Nat.size k := by
  induction h with
  | const φ =>
    exact ⟨formulaLenMeta (Rewriting.emb (template φ) : Semiproposition LAct 6), 0, fun k ↦ by
      rw [Nat.zero_mul, Nat.add_zero]⟩
  | box ψ => exact exists_formulaLenMeta_template_box_const ψ
  | impl _ _ ihF ihG =>
    obtain ⟨a₀, a₁, ha⟩ := ihF
    obtain ⟨b₀, b₁, hb⟩ := ihG
    refine ⟨a₀ + b₀ + 1, a₁ + b₁, fun k ↦ ?_⟩
    rw [formulaLenMeta_emb_template_impl]
    have h1 := ha k
    have h2 := hb k
    have e : (a₁ + b₁) * Nat.size k = a₁ * Nat.size k + b₁ * Nat.size k := Nat.add_mul _ _ _
    omega
  | neg _ ih =>
    obtain ⟨a₀, a₁, ha⟩ := ih
    exact ⟨a₀, a₁, fun k ↦ by rw [formulaLenMeta_emb_template_neg]; exact ha k⟩

/-- The instance the zoo needs: `□_k (I play C)` (LegibleBot's guard) and, more generally, the
budget-linear families over it. -/
theorem exists_formulaLenMeta_template_legible_const : ∃ c₀ c₁ : ℕ, ∀ k,
    formulaLenMeta (Rewriting.emb (template (.box k (.plays .self .opp .C))) : Semiproposition LAct 6) ≤ c₀ + c₁ * Nat.size k :=
  exists_formulaLenMeta_template_box_const _

end templateLength

#print axioms two_pow_succ_le_binNumeral
#print axioms size_binNumeral_ge
#print axioms fOcc_lenBox
#print axioms binNumeral_le_templateCode
#print axioms size_canonical_progCode_search_ge
#print axioms box_guard_never_fits
#print axioms legibleBot_guard_never_fits
#print axioms exists_formulaLenMeta_template_box_const
#print axioms exists_formulaLenMeta_template_const

end ArithS
