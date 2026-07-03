import PrisonersDilemma.Decidability.T42ProvableB
import PrisonersDilemma.Decidability.T31EngineDecider
import PrisonersDilemma.Decidability.T46LogicSpace

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

/-! ## 3. C1 — the Derivation layer has no free antecedents.

The invariant is stated over the POSITIVE IMPLICATION SPINE (`PosImpl φ B C`: the pair
`.impl B C` occurs along φ's chain of consequents). This makes `modusPonens` free — the
conclusion's spine embeds in the impl-premise's spine — and `hypSyll` a transitivity step.
`DAnt B C` enumerates the census (CUT_RELEVANCE.md §2) for the Type layer: one constructor
per transparency shape, plus transitivity. -/

/-- `.impl B C` occurs in positive position (along the consequent chain) of the formula. -/
inductive PosImpl : Formula → Formula → Formula → Prop where
  | head {B C : Formula} : PosImpl (.impl B C) B C
  | tail {X C' B C : Formula} : PosImpl C' B C → PosImpl (.impl X C') B C

/-- The Derivation layer's legitimate-antecedent relation: transparency shapes (each
    conclusion-determined via its `hme`-equation) closed under transitivity. -/
inductive DAnt : Formula → Formula → Prop where
  | searchBr {k : Nat} {ψ : Formula} {a b : Action} {me opponent : Prog}
      (hme : me = .search k ψ (.const a) (.const b)) :
      DAnt (.box k (ψ.subst me opponent)) (.plays me opponent a)
  | botSearchSt {k : Nat} {ψ : Formula} {a b : Action} {me opponent : Prog}
      (hme : me = .bot (.search k ψ (.const a) (.const b))) :
      DAnt (.box k (ψ.subst me opponent)) (.plays me opponent a)
  | simSt {me p q opponent : Prog} {a : Action} (hme : me = .sim p q) :
      DAnt (.plays (p.subst me opponent) (q.subst me opponent) a) (.plays me opponent a)
  | botSimSt {me p q opponent : Prog} {a : Action} (hme : me = .bot (.sim p q)) :
      DAnt (.plays (p.subst me opponent) (q.subst me opponent) a) (.plays me opponent a)
  | iteBr₁ {k : Nat} {z : Prog} {a' c0 c1 : Action} {ψ : Formula} {q me opponent : Prog}
      (hme : me = .ite (.sim .opp (.bot z)) a'
        (.search k ψ (.const c0) (.const c1)) q) :
      DAnt (.plays opponent (.bot z) a')
        (.impl (.box k (ψ.subst me opponent)) (.plays me opponent c0))
  | iteBr₂ {k : Nat} {z : Prog} {a' c0 c1 : Action} {ψ : Formula} {q me opponent : Prog}
      (hme : me = .ite (.sim .opp (.bot z)) a'
        (.search k ψ (.const c0) (.const c1)) q) :
      DAnt (.box k (ψ.subst me opponent)) (.plays me opponent c0)
  | trans {B D C : Formula} : DAnt B D → DAnt D C → DAnt B C

/-- **C1**: every positive-position implication of a `Derivation`-derivable formula has a
    census-legitimate antecedent. `modusPonens` needs NO analysis of its cut (the
    conclusion's spine embeds in the impl-premise's); `hypSyll` is `DAnt.trans`. -/
theorem derivation_posImpl_ant : ∀ {φ : Formula}, Derivation φ →
    ∀ {B C : Formula}, PosImpl φ B C → DAnt B C := by
  intro φ d
  induction d with
  | modusPonens φ' ψ d₁ d₂ ih₁ ih₂ =>
      intro B C hp
      exact ih₁ (.tail hp)
  | hypSyll φ' ψ' χ' d₁ d₂ ih₁ ih₂ =>
      intro B C hp
      cases hp with
      | head => exact .trans (ih₁ .head) (ih₂ .head)
      | tail hp' => exact ih₂ (.tail hp')
  | searchBranch k ψ a b me opponent hme =>
      intro B C hp
      cases hp with
      | head => exact .searchBr hme
      | tail hp' => cases hp'
  | simStep me p q opponent a hme =>
      intro B C hp
      cases hp with
      | head => exact .simSt hme
      | tail hp' => cases hp'
  | botSimStep me p q opponent a hme =>
      intro B C hp
      cases hp with
      | head => exact .botSimSt hme
      | tail hp' => cases hp'
  | botSearchStep k ψ a b me opponent hme =>
      intro B C hp
      cases hp with
      | head => exact .botSearchSt hme
      | tail hp' => cases hp'
  | iteBranchSearch_t k z a' c0 c1 ψ q me opponent hme =>
      intro B C hp
      cases hp with
      | head => exact .iteBr₁ hme
      | tail hp' =>
          cases hp' with
          | head => exact .iteBr₂ hme
          | tail hp'' => cases hp''
  | eqRefl p =>
      intro B C hp
      cases hp
  | eqNeg p q hne =>
      intro B C hp
      cases hp

/-- The top-level corollary: `Derivation (.impl B C)` forces a census antecedent. -/
theorem derivation_impl_ant {B C : Formula} (d : Derivation (.impl B C)) : DAnt B C :=
  derivation_posImpl_ant d .head

/-! ## 4. Provenance payoff: Derivation antecedents never increase literals. -/

open PD.T46 in
/-- Every census step is literal-nonincreasing — antecedents are built from the
    consequent's own programs and their source guards (via `maxLitF_subst`), so the
    Derivation layer cannot smuggle exotic literals into negative positions. -/
theorem DAnt_lit : ∀ {B C : Formula}, DAnt B C → maxLitF B ≤ maxLitF C := by
  intro B C h
  induction h with
  | @searchBr k ψ a b me opponent hme =>
      have hs := maxLitF_subst me opponent ψ
      subst hme
      simp only [maxLitF, maxLitP] at *
      omega
  | @botSearchSt k ψ a b me opponent hme =>
      have hs := maxLitF_subst me opponent ψ
      subst hme
      simp only [maxLitF, maxLitP] at *
      omega
  | @simSt me p q opponent a hme =>
      have hp := maxLitP_subst me opponent p
      have hq := maxLitP_subst me opponent q
      subst hme
      simp only [maxLitF, maxLitP] at *
      omega
  | @botSimSt me p q opponent a hme =>
      have hp := maxLitP_subst me opponent p
      have hq := maxLitP_subst me opponent q
      subst hme
      simp only [maxLitF, maxLitP] at *
      omega
  | @iteBr₁ k z a' c0 c1 ψ q me opponent hme =>
      subst hme
      simp only [maxLitF, maxLitP] at *
      omega
  | @iteBr₂ k z a' c0 c1 ψ q me opponent hme =>
      have hs := maxLitF_subst me opponent ψ
      subst hme
      simp only [maxLitF, maxLitP] at *
      omega
  | trans h₁ h₂ ih₁ ih₂ => omega

/-- Combining C0 + C1: a `struct`-entry at budget `k` has all its positive-position
    antecedents literal-bounded by the conclusion — which is itself `< 2^k`. The Type
    layer is fully tame; the residue of the conjecture is the `Provable` layer's chains
    and its size-exempt cut atoms (CUT_RELEVANCE.md C2–C4). -/
theorem struct_ant_lit {k : Nat} {φ B C : Formula}
    (h : ∃ d : Derivation φ, d.size ≤ k) (hp : PosImpl φ B C) :
    maxLitF B < 2 ^ k := by
  obtain ⟨d, hsz⟩ := h
  have h₁ := DAnt_lit (derivation_posImpl_ant d hp)
  have h₂ : maxLitF C ≤ maxLitF φ ∧ maxLitF B ≤ maxLitF φ := by
    clear h₁ hsz d
    induction hp with
    | head => simp only [maxLitF]; omega
    | tail hp' ih => simp only [maxLitF]; omega
  have h₃ := maxLitF_lt_two_pow_size φ
  have h₄ : φ.size ≤ k := Nat.le_trans d.concl_size_le hsz
  have h₅ := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) h₄
  omega

end PD.T48
