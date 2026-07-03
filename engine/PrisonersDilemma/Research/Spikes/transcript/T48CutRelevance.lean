import PrisonersDilemma.Decidability.T42ProvableB
import PrisonersDilemma.Decidability.T31EngineDecider

/-!
# T4.8 spike — cut relevance, C0: the mechanical foundations.

`Research/Notes/CUT_RELEVANCE.md` milestone C0. The LITERAL half of the conjecture is
locally free: every gated premise position is size-paid at its own judgment, so its
literals are `< 2^(local budget)`:

  * `maxLitP_lt_two_pow_size` / `maxLitF_lt_two_pow_size` — a formula's literals are
    exponentially bounded by its character size (each literal pays its `log2` in the size);
  * `cut_lit_bound` — the cut formula of any `implTrans`/`app`/`impS2` premise
    `Provable a (.impl A ψ)` has `maxLitF ψ < 2^a` (and `maxLitF A < 2^a`);
  * `box_lit_bound` — `axK`'s enumerated premise `.box a (.impl ψ α)` has `a < 2^m`;
  * `diag_lit_bound` — `diagF/B`'s enumerated premise `.impl (.box fb t) t` has `fb < 2^m`.

What this does NOT give (the note, §1): the uniform stratum bound — cut ATOMS are
size-exempt and can smuggle programs whose literals escalate the cite-chain budgets inside
one derivation. The uniform bound must be STRUCTURAL: the antecedent-provenance dichotomy
(note §2–3), milestones C1–C5.
-/

namespace PD.T48
open PD PD.T31 PD.T42

/-! ## 1. Literals are exponentially size-bounded. -/

mutual
  theorem maxLitP_lt_two_pow_size : ∀ p : Prog, maxLitP p < 2 ^ p.size := by
    intro p
    cases p with
    | const a =>
        simp only [maxLitP, Prog.size]
        exact Nat.two_pow_pos 1
    | self =>
        simp only [maxLitP, Prog.size]
        exact Nat.two_pow_pos 1
    | opp =>
        simp only [maxLitP, Prog.size]
        exact Nat.two_pow_pos 1
    | bot p =>
        have h := maxLitP_lt_two_pow_size p
        have hm : (2:Nat) ^ p.size ≤ 2 ^ (Prog.bot p).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Prog.size]; omega)
        simp only [maxLitP]
        omega
    | sim p₁ p₂ =>
        have h₁ := maxLitP_lt_two_pow_size p₁
        have h₂ := maxLitP_lt_two_pow_size p₂
        have hm₁ : (2:Nat) ^ p₁.size ≤ 2 ^ (Prog.sim p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Prog.size]; omega)
        have hm₂ : (2:Nat) ^ p₂.size ≤ 2 ^ (Prog.sim p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Prog.size]; omega)
        simp only [maxLitP]
        omega
    | ite b a p₁ p₂ =>
        have h₀ := maxLitP_lt_two_pow_size b
        have h₁ := maxLitP_lt_two_pow_size p₁
        have h₂ := maxLitP_lt_two_pow_size p₂
        have hm₀ : (2:Nat) ^ b.size ≤ 2 ^ (Prog.ite b a p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Prog.size]; omega)
        have hm₁ : (2:Nat) ^ p₁.size ≤ 2 ^ (Prog.ite b a p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Prog.size]; omega)
        have hm₂ : (2:Nat) ^ p₂.size ≤ 2 ^ (Prog.ite b a p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Prog.size]; omega)
        simp only [maxLitP]
        omega
    | search k φ p₁ p₂ =>
        have hk : k < 2 ^ (Prog.search k φ p₁ p₂).size :=
          lt_two_pow_of_log2_lt (by simp only [Prog.size]; omega)
        have h₀ := maxLitF_lt_two_pow_size φ
        have h₁ := maxLitP_lt_two_pow_size p₁
        have h₂ := maxLitP_lt_two_pow_size p₂
        have hm₀ : (2:Nat) ^ φ.size ≤ 2 ^ (Prog.search k φ p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Prog.size]; omega)
        have hm₁ : (2:Nat) ^ p₁.size ≤ 2 ^ (Prog.search k φ p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Prog.size]; omega)
        have hm₂ : (2:Nat) ^ p₂.size ≤ 2 ^ (Prog.search k φ p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Prog.size]; omega)
        simp only [maxLitP]
        omega

  theorem maxLitF_lt_two_pow_size : ∀ φ : Formula, maxLitF φ < 2 ^ φ.size := by
    intro φ
    cases φ with
    | plays p₁ p₂ a =>
        have h₁ := maxLitP_lt_two_pow_size p₁
        have h₂ := maxLitP_lt_two_pow_size p₂
        have hm₁ : (2:Nat) ^ p₁.size ≤ 2 ^ (Formula.plays p₁ p₂ a).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Formula.size]; omega)
        have hm₂ : (2:Nat) ^ p₂.size ≤ 2 ^ (Formula.plays p₁ p₂ a).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Formula.size]; omega)
        simp only [maxLitF]
        omega
    | impl φ ψ =>
        have h₁ := maxLitF_lt_two_pow_size φ
        have h₂ := maxLitF_lt_two_pow_size ψ
        have hm₁ : (2:Nat) ^ φ.size ≤ 2 ^ (Formula.impl φ ψ).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Formula.size]; omega)
        have hm₂ : (2:Nat) ^ ψ.size ≤ 2 ^ (Formula.impl φ ψ).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Formula.size]; omega)
        simp only [maxLitF]
        omega
    | neg φ =>
        have h₁ := maxLitF_lt_two_pow_size φ
        have hm₁ : (2:Nat) ^ φ.size ≤ 2 ^ (Formula.neg φ).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Formula.size]; omega)
        simp only [maxLitF]
        omega
    | box n φ =>
        have hn : n < 2 ^ (Formula.box n φ).size :=
          lt_two_pow_of_log2_lt (by simp only [Formula.size]; omega)
        have h₁ := maxLitF_lt_two_pow_size φ
        have hm₁ : (2:Nat) ^ φ.size ≤ 2 ^ (Formula.box n φ).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Formula.size]; omega)
        simp only [maxLitF]
        omega
    | eq p₁ p₂ =>
        have h₁ := maxLitP_lt_two_pow_size p₁
        have h₂ := maxLitP_lt_two_pow_size p₂
        have hm₁ : (2:Nat) ^ p₁.size ≤ 2 ^ (Formula.eq p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Formula.size]; omega)
        have hm₂ : (2:Nat) ^ p₂.size ≤ 2 ^ (Formula.eq p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Formula.size]; omega)
        simp only [maxLitF]
        omega
    | diag g φ =>
        have hg : g < 2 ^ (Formula.diag g φ).size :=
          lt_two_pow_of_log2_lt (by simp only [Formula.size]; omega)
        have h₁ := maxLitF_lt_two_pow_size φ
        have hm₁ : (2:Nat) ^ φ.size ≤ 2 ^ (Formula.diag g φ).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [Formula.size]; omega)
        simp only [maxLitF]
        omega
end

/-! ## 2. Every gated premise position is literal-bounded at its own judgment. -/

/-- The cut formula of any `implTrans`/`app`/`impS2` premise is exponentially
    literal-bounded by the premise's budget (both components). -/
theorem cut_lit_bound {a : Nat} {A ψ : Formula} (h : Provable a (.impl A ψ)) :
    maxLitF A < 2 ^ a ∧ maxLitF ψ < 2 ^ a := by
  have hsz := provable_impl_size h
  have hA := maxLitF_lt_two_pow_size A
  have hψ := maxLitF_lt_two_pow_size ψ
  have hmA : (2:Nat) ^ A.size ≤ 2 ^ a :=
    Nat.pow_le_pow_right (by omega) (by simp only [Formula.size] at hsz; omega)
  have hmψ : (2:Nat) ^ ψ.size ≤ 2 ^ a :=
    Nat.pow_le_pow_right (by omega) (by simp only [Formula.size] at hsz; omega)
  omega

/-- `axK`'s enumerated premise `.box a (.impl ψ α)` is subscript-bounded at its own
    judgment: boxes are non-atoms, hence size-paid. -/
theorem box_lit_bound {m a : Nat} {ψ : Formula} (h : Provable m (.box a ψ)) :
    a < 2 ^ m ∧ maxLitF ψ < 2 ^ m := by
  have hsz : (Formula.box a ψ).size ≤ m := by
    rcases provable_size_or_atom h with hsz | hatom
    · exact hsz
    · cases hatom
  have hψ := maxLitF_lt_two_pow_size ψ
  have hmψ : (2:Nat) ^ ψ.size ≤ 2 ^ m :=
    Nat.pow_le_pow_right (by omega) (by simp only [Formula.size] at hsz; omega)
  refine ⟨lt_two_pow_of_log2_lt ?_, by omega⟩
  simp only [Formula.size] at hsz
  omega

/-- `diagF/B`'s enumerated premise `.impl (.box fb t) t` is Löb-budget-bounded at its own
    judgment. -/
theorem diag_lit_bound {m fb : Nat} {t : Formula}
    (h : Provable m (.impl (.box fb t) t)) : fb < 2 ^ m := by
  have hsz := provable_impl_size h
  refine lt_two_pow_of_log2_lt ?_
  simp only [Formula.size] at hsz
  omega

/-- The judgment-local summary: at budget `m`, EVERY gated premise position of the
    `modestGate`/`litGate` rules carries literals `< 2^m`. (The uniform stratum bound —
    across the cite-escalating sub-judgments of one derivation — is exactly what the
    antecedent-provenance program (CUT_RELEVANCE.md §2–3) must supply.) -/
theorem local_lit_bound {m : Nat} {B : Formula} (h : Provable m B) :
    maxLitF B < 2 ^ m ∨ ∃ p q a, B = .plays p q a := by
  rcases provable_size_or_atom h with hsz | hatom
  · left
    have hB := maxLitF_lt_two_pow_size B
    have := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) hsz
    omega
  · right
    cases hatom with
    | mk cert hle => exact ⟨_, _, _, rfl⟩

end PD.T48
