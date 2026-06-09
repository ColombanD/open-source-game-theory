import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms


open Classical

open PD
open PD.Axioms
namespace PD.BaseTheorems

/-- The bridge `proofSearch ↔ Provable` is now a theorem, not an axiom. -/
theorem proofSearch_spec (k : Nat) (φ : Formula) :
    proofSearch k φ = true ↔ Provable k φ := by
  unfold proofSearch; exact decide_eq_true_iff

-- Soundness of the structural rules. Each `Derivation` yields a true
-- formula. The interesting cases (`searchBranch`, `simStep`) are exactly the
-- semantic content the old transparency axioms asserted for free.
--
-- Declared as `_root_.PD.Derivation.sound` (absolute name) so it lands in
-- the `PD.Derivation` namespace and dot notation `d.sound` on a
-- `d : PD.Derivation φ` resolves it — rather than being prefixed by the
-- ambient `PD.BaseTheorems` namespace.
theorem _root_.PD.Derivation.sound : ∀ {φ}, Derivation φ → φ.interp := by
  intro φ d
  induction d with
  | searchBranch k ψ a b me opponent hme =>
      -- `me` is a `.search` node; a provable guard makes `eval` take the
      -- `.const a` branch, so `me` plays `a` against `opponent`.
      subst hme
      intro hguard
      have hps : proofSearch k (ψ.subst (.search k ψ (.const a) (.const b)) opponent) = true :=
        (proofSearch_spec _ _).2 hguard
      exact ⟨2, by simp only [play, eval, hps, if_true]⟩
  | simStep me p q opponent a hme =>
      -- `me` is a `.sim` node; by the `.sim` eval rule, `me` plays `a` iff its
      -- closed body `p'` plays `a` against `q'`.
      subst hme
      intro h
      obtain ⟨n, hn⟩ := h
      exact ⟨n + 1, by show eval (n+1) (.sim p q) opponent (.sim p q) = some a
                       simp only [eval]; exact hn⟩
  | hypSyll φ ψ χ _ _ ih1 ih2 =>
      exact fun h => ih2 (ih1 h)

/-- A derivation of size `m` witnesses `proofSearch m φ = true` (structural
    disjunct of `Provable`). -/
theorem derives {φ : Formula} (d : Derivation φ) : ∃ m, proofSearch m φ = true :=
  ⟨d.size, (proofSearch_spec _ _).2 (Or.inl ⟨d, Nat.le_refl _⟩)⟩

/--
S can read source code: if an agent `me` is literally
`.search k ψ (.const a) (.const b)`, then S proves
`□_k ψ' → me plays a against opponent`, where `ψ' = ψ.subst me opponent`.

Was an axiom; now a theorem, witnessed by `Derivation.searchBranch`.
-/
theorem proof_system_verifies_search_branch :
    ∀ (k : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog),
      me = .search k ψ (.const a) (.const b) →
      ∃ m, proofSearch m
        (.impl (.box k (ψ.subst me opponent)) (.plays me opponent a)) = true :=
  fun k ψ a b me opponent hme => derives (.searchBranch k ψ a b me opponent hme)

/--
S can read `.sim` nodes: if `me = .sim p q`, then S proves
`(p' plays a vs q') → (me plays a vs opponent)`.

Was an axiom; now a theorem, witnessed by `Derivation.simStep`.
-/
theorem proof_system_verifies_sim :
    ∀ (me p q opponent : Prog) (a : Action),
      me = .sim p q →
      ∃ m, proofSearch m
        (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
               (.plays me opponent a)) = true :=
  fun me p q opponent a hme => derives (.simStep me p q opponent a hme)


-- Soundness of bounded proof search. Either the formula is provable by the
-- structural `Derivation` rules (→ `Derivation.sound`), or it is an atomic σ₁
-- fact (→ `AtomProvable_sound`).
theorem proofSearch_sound :
  ∀ k φ, proofSearch k φ = true → φ.interp := by
  intro k φ hk
  rcases (proofSearch_spec k φ).1 hk with ⟨d, _⟩ | hatom
  · exact d.sound
  · exact AtomProvable_sound φ hatom

/-- Completeness of bounded proof search for atomic plays-formulas, via the
    σ₁ atom-completeness axiom. Any budget works (`AtomProvable` is
    budget-independent); pick `0`. -/
theorem proofSearch_complete_plays :
∀ p q a, (∃ n, play n p q = some a) → ∃ k, proofSearch k (.plays p q a) = true := by
  intro p q a h
  exact ⟨0, (proofSearch_spec 0 (.plays p q a)).2 (Or.inr (atom_complete p q a h))⟩

-- Monotonicity in proof-search budget: the structural disjunct relaxes its size
-- bound, and the `AtomProvable` disjunct is budget-independent — so both carry
-- over to any larger budget.
theorem proofSearch_monotone :
  ∀ k₁ k₂ φ, k₁ ≤ k₂ → proofSearch k₁ φ = true → proofSearch k₂ φ = true := by
  intro k₁ k₂ φ hk h1
  rcases (proofSearch_spec k₁ φ).1 h1 with ⟨d, hd⟩ | hatom
  · exact (proofSearch_spec k₂ φ).2 (Or.inl ⟨d, Nat.le_trans hd hk⟩)
  · exact (proofSearch_spec k₂ φ).2 (Or.inr hatom)

end PD.BaseTheorems
