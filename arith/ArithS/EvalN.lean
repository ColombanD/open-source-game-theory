import ArithS.Eval

/-!
# ArithS.EvalN — the evaluator on `ℕ`: inversion, determinism, fuel monotonicity

Facts about `EvalGraph` at `V = ℕ`, by ordinary induction on the fuel (no definability
side conditions). `evalN` packages the graph as a partial function `Option ℕ`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open LAct

section inversion

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch

lemma EvalGraph.zero_iff {me opp p a : V} : ¬EvalGraph 0 me opp p a := by
  rw [EvalGraph.case_iff]
  rintro ⟨n', h, _⟩
  exact zero_ne_add_one n' h

lemma EvalGraph.const_iff {n me opp a a' : V} :
    EvalGraph (n + 1) me opp (pConst a) a' ↔ a' = a := by
  rw [EvalGraph.case_iff]; simp [eq_comm]

lemma EvalGraph.self_iff {n me opp a : V} :
    EvalGraph (n + 1) me opp pSelf a ↔ EvalGraph n me opp me a := by
  rw [EvalGraph.case_iff]; simp

lemma EvalGraph.opp_iff {n me opp a : V} :
    EvalGraph (n + 1) me opp pOpp a ↔ EvalGraph n me opp opp a := by
  rw [EvalGraph.case_iff]; simp

lemma EvalGraph.bot_iff {n me opp p a : V} :
    EvalGraph (n + 1) me opp (pBot p) a ↔ EvalGraph n me opp p a := by
  rw [EvalGraph.case_iff]; simp

lemma EvalGraph.sim_iff {n me opp p q a : V} :
    EvalGraph (n + 1) me opp (pSim p q) a ↔
    EvalGraph n (psubst me opp p) (psubst me opp q) (psubst me opp p) a := by
  rw [EvalGraph.case_iff]; simp

lemma EvalGraph.ite_iff {n me opp b a' p q a : V} :
    EvalGraph (n + 1) me opp (pIte b a' p q) a ↔
    ∃ r, EvalGraph n me opp b r ∧
      ((r = a' ∧ EvalGraph n me opp p a) ∨ (r ≠ a' ∧ EvalGraph n me opp q a)) := by
  rw [EvalGraph.case_iff]; simp

lemma EvalGraph.search_iff {n me opp k g p q a : V} :
    EvalGraph (n + 1) me opp (pSearch k g p q) a ↔
    ((LenProvableV TAct k (guardCode g me opp) ∧ EvalGraph n me opp p a) ∨
     (¬LenProvableV TAct k (guardCode g me opp) ∧ EvalGraph n me opp q a)) := by
  rw [EvalGraph.case_iff]; simp

end inversion

/-! ### On `ℕ`: determinism and fuel monotonicity -/

section nat

/-- The evaluator is deterministic. -/
theorem EvalGraph.unique (n : ℕ) : ∀ me opp p a₁ a₂ : ℕ,
    EvalGraph n me opp p a₁ → EvalGraph n me opp p a₂ → a₁ = a₂ := by
  induction n with
  | zero => intro me opp p a₁ a₂ h; exact absurd h EvalGraph.zero_iff
  | succ n ih =>
    intro me opp p a₁ a₂ h₁ h₂
    by_cases hp : IsShape p
    · rcases hp with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a', p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · rw [EvalGraph.const_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [EvalGraph.self_iff] at h₁ h₂; exact ih _ _ _ _ _ h₁ h₂
      · rw [EvalGraph.opp_iff] at h₁ h₂; exact ih _ _ _ _ _ h₁ h₂
      · rw [EvalGraph.bot_iff] at h₁ h₂; exact ih _ _ _ _ _ h₁ h₂
      · rw [EvalGraph.sim_iff] at h₁ h₂; exact ih _ _ _ _ _ h₁ h₂
      · rcases EvalGraph.ite_iff.mp h₁ with ⟨r₁, hb₁, hc₁⟩
        rcases EvalGraph.ite_iff.mp h₂ with ⟨r₂, hb₂, hc₂⟩
        have hr : r₁ = r₂ := ih _ _ _ _ _ hb₁ hb₂
        subst hr
        rcases hc₁ with ⟨e₁, h₁'⟩ | ⟨e₁, h₁'⟩ <;> rcases hc₂ with ⟨e₂, h₂'⟩ | ⟨e₂, h₂'⟩
        · exact ih _ _ _ _ _ h₁' h₂'
        · exact absurd e₁ e₂
        · exact absurd e₂ e₁
        · exact ih _ _ _ _ _ h₁' h₂'
      · rcases EvalGraph.search_iff.mp h₁ with ⟨e₁, h₁'⟩ | ⟨e₁, h₁'⟩ <;>
          rcases EvalGraph.search_iff.mp h₂ with ⟨e₂, h₂'⟩ | ⟨e₂, h₂'⟩
        · exact ih _ _ _ _ _ h₁' h₂'
        · exact absurd e₁ e₂
        · exact absurd e₂ e₁
        · exact ih _ _ _ _ _ h₁' h₂'
    · exfalso
      rcases EvalGraph.case_iff.mp h₁ with ⟨n', _, (h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨p', h, _⟩ |
        ⟨p', q, h, _⟩ | ⟨b, a', p', q, r, h, _⟩ | ⟨k, g, p', q, h, _⟩)⟩
      · exact hp (Or.inl ⟨_, h⟩)
      · exact hp (Or.inr (Or.inl h))
      · exact hp (Or.inr (Or.inr (Or.inl h)))
      · exact hp (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, h⟩))))
      · exact hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, h⟩)))))
      · exact hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, h⟩))))))
      · exact hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, h⟩))))))

/-- More fuel never changes a result. -/
theorem EvalGraph.mono (n : ℕ) : ∀ me opp p a : ℕ, EvalGraph n me opp p a → EvalGraph (n + 1) me opp p a := by
  induction n with
  | zero => intro me opp p a h; exact absurd h EvalGraph.zero_iff
  | succ n ih =>
    intro me opp p a h
    rcases EvalGraph.case_iff.mp h with ⟨n', hn, H⟩
    have hn' : n' = n := by omega
    rw [hn'] at H
    rw [EvalGraph.case_iff]
    refine ⟨n + 1, rfl, ?_⟩
    rcases H with h | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨p', h, hc⟩ | ⟨p', q, h, hc⟩ |
      ⟨b, a', p', q, r, h, hb, hpq⟩ | ⟨k, g, p', q, h, hpq⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h, ih _ _ _ _ hc⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h, ih _ _ _ _ hc⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p', h, ih _ _ _ _ hc⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p', q, h, ih _ _ _ _ hc⟩))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a', p', q, r, h, ih _ _ _ _ hb, ?_⟩)))))
      rcases hpq with ⟨e, hc⟩ | ⟨e, hc⟩
      · exact Or.inl ⟨e, ih _ _ _ _ hc⟩
      · exact Or.inr ⟨e, ih _ _ _ _ hc⟩
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, g, p', q, h, ?_⟩)))))
      rcases hpq with ⟨e, hc⟩ | ⟨e, hc⟩
      · exact Or.inl ⟨e, ih _ _ _ _ hc⟩
      · exact Or.inr ⟨e, ih _ _ _ _ hc⟩

theorem EvalGraph.mono_le {n n' me opp p a : ℕ} (h : n ≤ n') (e : EvalGraph n me opp p a) :
    EvalGraph n' me opp p a := by
  induction h with
  | refl => exact e
  | step _ ih => exact EvalGraph.mono _ _ _ _ _ ih

/-- Results at any two fuels agree. -/
theorem EvalGraph.unique' {n n' me opp p a a' : ℕ}
    (h : EvalGraph n me opp p a) (h' : EvalGraph n' me opp p a') : a = a' :=
  EvalGraph.unique (max n n') me opp p a a' (EvalGraph.mono_le (le_max_left _ _) h)
    (EvalGraph.mono_le (le_max_right _ _) h')

end nat

end ArithS
