import PrisonersDilemma.Base.Soundness

/-!
# Base/Exclusion — structural exclusion: what `S` can NOT conclude

The positive layers certify plays; this file starts the NEGATIVE direction, needed by
the honest outcome theorems for the floor-killed pairs (the tombstones in
`Theorems/DupocBot.lean` / `Theorems/LlmGenerations/PrudentBot.lean`): `¬Provable k φ`
facts for TRUE formulas, where soundness gives nothing and only cost accounting can
close the guard.

Contents:
* `Formula.size_pos` — every formula costs at least one character.
* `rightTail` — the final consequent of a right-nested implication chain (the spine
  tail; `modusPonens`/`app` peel it, `hypSyll`/`implTrans`/`impS2` preserve it).
* `ReadableMe` — the five player shapes whose plays the `Derivation` source-transparency
  bridge can conclude.
* `Derivation.tail_plays_readable` — THE CENSUS: if a `Derivation`'s conclusion has a
  plays-atom spine tail, the player is one of the readable shapes. Contrapositive: a
  bot whose source is not bridge-readable (e.g. DBot — an `.ite` with a `.const`
  then-branch) has NO `Derivation` route to any formula ending in its play atoms,
  which closes the `struct` entry point of `Provable` in one stroke.

Consumers combine the census with a budget strong-induction over `Provable` (the
`app`/`weakenImpl`/`implTrans`/`diagF`/`impS2` regress descends because transcript
cumulativity makes every premise budget strictly smaller) and kill the `atom` entry by
the `search_f` floor arithmetic — blueprint: `no_provable_DBot_C_tail` in
`Theorems/DupocBot.lean`.
-/

open Classical

open PD
namespace PD.BaseTheorems

/-- Every formula costs at least one character. -/
theorem _root_.PD.Formula.size_pos : ∀ φ : Formula, 1 ≤ φ.size := by
  intro φ; cases φ <;> simp only [Formula.size] <;> omega

/-- The final consequent of a right-nested implication chain — the "spine tail".
    `rightTail (φ₁ → (φ₂ → … → ψ))` is `ψ` for non-`.impl` `ψ`. -/
def rightTail : Formula → Formula
  | .impl _ ψ => rightTail ψ
  | φ => φ

@[simp] theorem rightTail_impl (φ ψ : Formula) :
    rightTail (.impl φ ψ) = rightTail ψ := rfl
@[simp] theorem rightTail_plays (p q : Prog) (a : Action) :
    rightTail (.plays p q a) = .plays p q a := rfl
@[simp] theorem rightTail_neg (φ : Formula) : rightTail (.neg φ) = .neg φ := rfl
@[simp] theorem rightTail_box (n : Nat) (φ : Formula) :
    rightTail (.box n φ) = .box n φ := rfl
@[simp] theorem rightTail_eq (p q : Prog) : rightTail (.eq p q) = .eq p q := rfl
@[simp] theorem rightTail_diag (g : Nat) (φ : Formula) :
    rightTail (.diag g φ) = .diag g φ := rfl

/-- The five player shapes whose plays the source-transparency bridge rules can
    conclude (`searchBranch`, `simStep`, `botSimStep`, `botSearchStep`,
    `iteBranchSearch_t` — one disjunct each, in that order). A player of any OTHER
    shape has no `Derivation` route to its play atoms (`tail_plays_readable`). -/
def ReadableMe (me : Prog) : Prop :=
  (∃ k ψ a b, me = .search k ψ (.const a) (.const b)) ∨
  (∃ p q, me = .sim p q) ∨
  (∃ p q, me = .bot (.sim p q)) ∨
  (∃ k ψ a b, me = .bot (.search k ψ (.const a) (.const b))) ∨
  (∃ z a' k ψ c0 c1 q,
    me = .ite (.sim .opp (.bot z)) a' (.search k ψ (.const c0) (.const c1)) q)

/-- **The Derivation census**: if a `Derivation`'s conclusion has a plays-atom spine
    tail, the player is bridge-readable. Induction: the logical core (`modusPonens`,
    `hypSyll`) preserves the spine tail; each bridge rule's tail names its own (readable)
    `me`; `eqRefl`/`eqNeg` have non-plays tails. -/
theorem tail_plays_readable :
    ∀ {φ : Formula}, Derivation φ →
      ∀ {me oppo : Prog} {a : Action},
        rightTail φ = .plays me oppo a → ReadableMe me := by
  intro φ d
  induction d with
  | modusPonens φ ψ d1 d2 ih1 ih2 =>
      intro me oppo a h
      exact ih1 (by simpa using h)
  | hypSyll φ ψ χ d1 d2 ih1 ih2 =>
      intro me oppo a h
      exact ih2 (by simpa using h)
  | searchBranch k ψ a b me' oppo' hme =>
      intro me oppo a' h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inl ⟨k, ψ, _, _, hme⟩
  | simStep me' p q oppo' a hme =>
      intro me oppo a' h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inl ⟨p, q, hme⟩)
  | botSimStep me' p q oppo' a hme =>
      intro me oppo a' h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inl ⟨p, q, hme⟩))
  | botSearchStep k ψ a b me' oppo' hme =>
      intro me oppo a' h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, ψ, _, _, hme⟩)))
  | iteBranchSearch_t k z a' c0 c1 ψ q me' oppo' hme =>
      intro me oppo a'' h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨z, a', k, ψ, c0, c1, q, hme⟩)))
  | eqRefl p =>
      intro me oppo a h
      simp at h
  | eqNeg p q hne =>
      intro me oppo a h
      simp at h

end PD.BaseTheorems
