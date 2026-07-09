import PrisonersDilemma.Decidability.T42ProvableB
import PrisonersDilemma.Decidability.T31EngineDecider
import PrisonersDilemma.Decidability.T46LogicSpace

/-!
# Cut relevance I — literal bounds and the antecedent census.

Foundations consumed by the whole T48–T54 arc (research history:
`Research/Notes/CUT_RELEVANCE.md`):

  * **Literal bounds**: every gated premise position is size-paid at its own
    judgment, so its literals are `< 2^(local budget)` — `maxLitF_lt_two_pow_size`,
    `cut_lit_bound`, `box_lit_bound`, `diag_lit_bound`, `local_lit_bound`.
  * **The antecedent census** (`DAnt`, `derivation_impl_ant`, `DAnt_lit`): every
    positive-position implication a `Derivation` proves has a census-legitimate
    antecedent — the Type layer has no free hypotheses.
  * **Shape facts**: `derivation_shape`, `derivation_no_box`, `box_inversion`,
    the split literals (`maxSLitF`) and the gate-bound arithmetic.
-/

namespace PD.T48
open PD PD.T31 PD.T42

/-! ## 1. Literals are exponentially size-bounded. -/

mutual
  theorem maxLitP_lt_two_pow_size : ∀ p : Prog, maxLitP p < 2 ^ p.size := by
    intro p
    cases p with
    | const a =>
        simp only [numCost, maxLitP, Prog.size]
        exact Nat.two_pow_pos 1
    | self =>
        simp only [numCost, maxLitP, Prog.size]
        exact Nat.two_pow_pos 1
    | opp =>
        simp only [numCost, maxLitP, Prog.size]
        exact Nat.two_pow_pos 1
    | bot p =>
        have h := maxLitP_lt_two_pow_size p
        have hm : (2:Nat) ^ p.size ≤ 2 ^ (Prog.bot p).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        simp only [maxLitP]
        omega
    | sim p₁ p₂ =>
        have h₁ := maxLitP_lt_two_pow_size p₁
        have h₂ := maxLitP_lt_two_pow_size p₂
        have hm₁ : (2:Nat) ^ p₁.size ≤ 2 ^ (Prog.sim p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        have hm₂ : (2:Nat) ^ p₂.size ≤ 2 ^ (Prog.sim p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        simp only [maxLitP]
        omega
    | ite b a p₁ p₂ =>
        have h₀ := maxLitP_lt_two_pow_size b
        have h₁ := maxLitP_lt_two_pow_size p₁
        have h₂ := maxLitP_lt_two_pow_size p₂
        have hm₀ : (2:Nat) ^ b.size ≤ 2 ^ (Prog.ite b a p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        have hm₁ : (2:Nat) ^ p₁.size ≤ 2 ^ (Prog.ite b a p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        have hm₂ : (2:Nat) ^ p₂.size ≤ 2 ^ (Prog.ite b a p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        simp only [maxLitP]
        omega
    | search k φ p₁ p₂ =>
        have hk : k < 2 ^ (Prog.search k φ p₁ p₂).size :=
          lt_two_pow_of_log2_lt (by simp only [numCost, Prog.size]; omega)
        have h₀ := maxLitF_lt_two_pow_size φ
        have h₁ := maxLitP_lt_two_pow_size p₁
        have h₂ := maxLitP_lt_two_pow_size p₂
        have hm₀ : (2:Nat) ^ φ.size ≤ 2 ^ (Prog.search k φ p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        have hm₁ : (2:Nat) ^ p₁.size ≤ 2 ^ (Prog.search k φ p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        have hm₂ : (2:Nat) ^ p₂.size ≤ 2 ^ (Prog.search k φ p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        simp only [maxLitP]
        omega

  theorem maxLitF_lt_two_pow_size : ∀ φ : Formula, maxLitF φ < 2 ^ φ.size := by
    intro φ
    cases φ with
    | plays p₁ p₂ a =>
        have h₁ := maxLitP_lt_two_pow_size p₁
        have h₂ := maxLitP_lt_two_pow_size p₂
        have hm₁ : (2:Nat) ^ p₁.size ≤ 2 ^ (Formula.plays p₁ p₂ a).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        have hm₂ : (2:Nat) ^ p₂.size ≤ 2 ^ (Formula.plays p₁ p₂ a).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        simp only [maxLitF]
        omega
    | impl φ ψ =>
        have h₁ := maxLitF_lt_two_pow_size φ
        have h₂ := maxLitF_lt_two_pow_size ψ
        have hm₁ : (2:Nat) ^ φ.size ≤ 2 ^ (Formula.impl φ ψ).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        have hm₂ : (2:Nat) ^ ψ.size ≤ 2 ^ (Formula.impl φ ψ).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        simp only [maxLitF]
        omega
    | neg φ =>
        have h₁ := maxLitF_lt_two_pow_size φ
        have hm₁ : (2:Nat) ^ φ.size ≤ 2 ^ (Formula.neg φ).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        simp only [maxLitF]
        omega
    | box n φ =>
        have hn : n < 2 ^ (Formula.box n φ).size :=
          lt_two_pow_of_log2_lt (by simp only [numCost, Formula.size]; omega)
        have h₁ := maxLitF_lt_two_pow_size φ
        have hm₁ : (2:Nat) ^ φ.size ≤ 2 ^ (Formula.box n φ).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        simp only [maxLitF]
        omega
    | eq p₁ p₂ =>
        have h₁ := maxLitP_lt_two_pow_size p₁
        have h₂ := maxLitP_lt_two_pow_size p₂
        have hm₁ : (2:Nat) ^ p₁.size ≤ 2 ^ (Formula.eq p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        have hm₂ : (2:Nat) ^ p₂.size ≤ 2 ^ (Formula.eq p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        simp only [maxLitF]
        omega
    | diag g φ =>
        have hg : g < 2 ^ (Formula.diag g φ).size :=
          lt_two_pow_of_log2_lt (by simp only [numCost, Formula.size]; omega)
        have h₁ := maxLitF_lt_two_pow_size φ
        have hm₁ : (2:Nat) ^ φ.size ≤ 2 ^ (Formula.diag g φ).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
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
    Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size] at hsz; omega)
  have hmψ : (2:Nat) ^ ψ.size ≤ 2 ^ a :=
    Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size] at hsz; omega)
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
    Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size] at hsz; omega)
  refine ⟨lt_two_pow_of_log2_lt ?_, by omega⟩
  simp only [numCost, Formula.size] at hsz
  omega

/-- `diagF/B`'s enumerated premise `.impl (.box fb t) t` is Löb-budget-bounded at its own
    judgment. -/
theorem diag_lit_bound {m fb : Nat} {t : Formula}
    (h : Provable m (.impl (.box fb t) t)) : fb < 2 ^ m := by
  have hsz := provable_impl_size h
  refine lt_two_pow_of_log2_lt ?_
  simp only [numCost, Formula.size] at hsz
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

/-! ## 5. C2 — the `Provable` layer's spine dichotomy.

The census relation `PAnt` for the `Provable` layer: C1's `DAnt` embedded, one constructor
per modal/transparency producer. Where pairwise information is genuinely insufficient the
constructor is honest about it: `imps2Ant` RECORDS the producing judgment (budget strictly
below — C3's tree-invariant unfolds it), and `axkPair` is shape-only (for a box-box pair
the antecedent's content is carried by the SIBLING judgment `.box a (.impl ψ α)` at the
consuming `app` — visible to the tree-invariant, not to the pair). The dichotomy: every
positive-spine pair of a derivable formula is census-legitimate OR the consequent is
provable outright within the same budget (weakening-degeneracy). -/

/-- The `Provable`-layer antecedent census. -/
inductive PAnt : Formula → Formula → Prop where
  | ofD {B C : Formula} : DAnt B C → PAnt B C
  | stsAnt {k₁ k₂ : Nat} {ψ₁ ψ₂ : Formula} {c0 c1 : Action} {q me opnt : Prog}
      (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) :
      PAnt (.box k₁ (ψ₁.subst me opnt)) (.plays me opnt c0)
  | atomBoxAnt {p q : Prog} {a : Action} {kBox : Nat} :
      PAnt (.plays p q a) (.box kBox (.plays p q a))
  | axkPair {b c : Nat} {ψ α : Formula} :
      PAnt (.box b ψ) (.box c α)
  | box4Ant {a b : Nat} {φ' : Formula} :
      PAnt (.box a φ') (.box b (.box a φ'))
  | boxMonoAnt {a b : Nat} {ψ : Formula} :
      PAnt (.box a ψ) (.box b ψ)
  | axkfAnt {a b c : Nat} {ψ α : Formula} :
      PAnt (.box a (.impl ψ α)) (.impl (.box b ψ) (.box c α))
  | diagFAnt {g : Nat} {tgt : Formula} :
      PAnt (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)
  | diagFInner {g : Nat} {tgt : Formula} :
      PAnt (.box g (.diag g tgt)) tgt
  | diagBAnt {g : Nat} {tgt : Formula} :
      PAnt (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)
  | imps2Ant {A ψ χ : Formula} {m₁ : Nat} :
      Provable m₁ (.impl A (.impl ψ χ)) → PAnt A χ
  | trans {B D C : Formula} : PAnt B D → PAnt D C → PAnt B C

set_option maxHeartbeats 1000000 in
/-- **C2**: every positive-spine implication pair of a `Provable`-derivable formula has a
    census-legitimate antecedent, or its consequent is provable outright within the same
    budget. `app` and `weakenImpl`'s tails ride the C1 spine-embedding; `implTrans` mixes
    census-transitivity with degeneracy-propagation (the `Provable.app` reassembly fits the
    original budget); `diagF`'s deep tail recurses through its Löb premise. -/
theorem provable_posImpl_ant : ∀ {m : Nat} {φ : Formula}, Provable m φ →
    ∀ {B C : Formula}, PosImpl φ B C →
      PAnt B C ∨ ∃ m', m' ≤ m ∧ Provable m' C := by
  intro m φ h
  refine Provable.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun m φ _ => ∀ {B C : Formula}, PosImpl φ B C →
      PAnt B C ∨ ∃ m', m' ≤ m ∧ Provable m' C)
    ?pConst ?pSelf ?pOpp ?pBot ?pSim ?pIte_t ?pIte_f ?pSearch_t ?pSearch_f ?pMk
    ?cStruct ?cAtom ?cWeaken ?cSTS ?cITrans ?cAtomBox ?cBoxIntro ?cApp ?cAxK ?cBox4
    ?cDiagF ?cDiagB ?cAxKf ?cImpS2 ?cBoxMono ?cAtomNeg h
  case pConst => intros; trivial
  case pSelf => intros; trivial
  case pOpp => intros; trivial
  case pBot => intros; trivial
  case pSim => intros; trivial
  case pIte_t => intros; trivial
  case pIte_f => intros; trivial
  case pSearch_t => intros; trivial
  case pSearch_f => intros; trivial
  case pMk => intros; trivial
  case cStruct =>
      intro φ0 k0 hd B C hp
      obtain ⟨d, _⟩ := hd
      exact Or.inl (.ofD (derivation_posImpl_ant d hp))
  case cAtom =>
      intro k0 φ0 hatom _ B C hp
      cases hatom with
      | mk cert hle => cases hp
  case cWeaken =>
      intro k A ψ m' hψ hle ih B C hp
      cases hp with
      | head => exact Or.inr ⟨m', by omega, hψ⟩
      | tail hp' =>
          rcases ih hp' with hl | ⟨m'', hm'', hC⟩
          · exact Or.inl hl
          · exact Or.inr ⟨m'', by omega, hC⟩
  case cSTS =>
      intro k k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opnt hme hprud hmk hle ih B C hp
      cases hp with
      | head => exact Or.inl (.stsAnt hme)
      | tail hp' => cases hp'
  case cITrans =>
      intro k A ψ χ a b h1 h2 hle ih1 ih2 B C hp
      cases hp with
      | head =>
          rcases ih2 .head with hl2 | ⟨m2', hm2', hC⟩
          · rcases ih1 .head with hl1 | ⟨m1', hm1', hψ⟩
            · exact Or.inl (.trans hl1 hl2)
            · refine Or.inr ⟨b + m1' + χ.size, ?_, ?_⟩
              · have hA := Formula.size_pos A
                simp only [numCost, Formula.size] at hle
                omega
              · exact Provable.app _ b m1' ψ χ h2 hψ (Nat.le_refl _)
          · exact Or.inr ⟨m2', by omega, hC⟩
      | tail hp' =>
          rcases ih2 (.tail hp') with hl | ⟨m'', hm'', hC⟩
          · exact Or.inl hl
          · exact Or.inr ⟨m'', by omega, hC⟩
  case cAtomBox =>
      intro k kBox p q a hatom hle _ B C hp
      cases hp with
      | head => exact Or.inl .atomBoxAnt
      | tail hp' => cases hp'
  case cBoxIntro =>
      intro kIn K A hprem hle ih B C hp
      cases hp
  case cApp =>
      intro k m₁ m₂ ψ α h1 h2 hle ih1 ih2 B C hp
      rcases ih1 (.tail hp) with hl | ⟨m'', hm'', hC⟩
      · exact Or.inl hl
      · refine Or.inr ⟨m'', ?_, hC⟩
        have hα := Formula.size_pos α
        omega
  case cAxK =>
      intro a b c m' K A α hprem hgate hle ih B C hp
      cases hp with
      | head => exact Or.inl .axkPair
      | tail hp' => cases hp'
  case cBox4 =>
      intro a b K A hgate hle B C hp
      cases hp with
      | head => exact Or.inl .box4Ant
      | tail hp' => cases hp'
  case cDiagF =>
      intro pm fb g K tgt hgate hle ih B C hp
      cases hp with
      | head => exact Or.inl .diagFAnt
      | tail hp' =>
          cases hp' with
          | head => exact Or.inl .diagFInner
          | tail hp'' =>
              rcases ih (.tail hp'') with hl | ⟨m'', hm'', hC⟩
              · exact Or.inl hl
              · exact Or.inr ⟨m'', by omega, hC⟩
  case cDiagB =>
      intro pm fb g K tgt hgate hle ih B C hp
      cases hp with
      | head => exact Or.inl .diagBAnt
      | tail hp' => cases hp'
  case cAxKf =>
      intro a b c K A α hgate hle B C hp
      cases hp with
      | head => exact Or.inl .axkfAnt
      | tail hp' =>
          cases hp' with
          | head => exact Or.inl .axkPair
          | tail hp'' => cases hp''
  case cImpS2 =>
      intro A ψ χ m₁ m₂ K h1 h2 hle ih1 ih2 B C hp
      cases hp with
      | head => exact Or.inl (.imps2Ant h1)
      | tail hp' =>
          rcases ih1 (.tail (.tail hp')) with hl | ⟨m'', hm'', hC⟩
          · exact Or.inl hl
          · refine Or.inr ⟨m'', ?_, hC⟩
            have hAC := Formula.size_pos (Formula.impl A χ)
            omega
  case cBoxMono =>
      intro a b K A hab hle B C hp
      cases hp with
      | head => exact Or.inl .boxMonoAnt
      | tail hp' => cases hp'
  case cAtomNeg =>
      intro k p q b aN m' hatom hne hle _ B C hp
      cases hp

/-- The top-level corollary: any derivable implication's antecedent is census-legitimate
    or the implication is weakening-degenerate. This is Lemma A's dichotomy at the head
    pair — the tool the C3 tree-invariant applies at every `app` site. -/
theorem provable_impl_ant {m : Nat} {B C : Formula} (h : Provable m (.impl B C)) :
    PAnt B C ∨ ∃ m', m' ≤ m ∧ Provable m' C :=
  provable_posImpl_ant h .head

/-! ## 6. C3a — shape lemmas and the box-inversion (the sibling-sourcing tools).

The system has NO reflection rule, and `Derivation` cannot conclude a box — so box CONTENTS
never become judgments. Box JUDGMENTS invert to exactly two sources: `boxIntro` (the content
WAS a judgment) or `app` (the spine). These are the tools the C3 master induction uses to
source the census holes (`axkPair`/`box4` pairs) from sibling judgments
(CUT_RELEVANCE.md §5). -/

/-- The formula's positive spine ends in a `.plays` atom. -/
inductive EndsInPlays : Formula → Prop where
  | plays {p q : Prog} {a : Action} : EndsInPlays (.plays p q a)
  | impl {X C : Formula} : EndsInPlays C → EndsInPlays (.impl X C)

/-- Every `Derivation`-derivable formula is a plays-ended implication chain or an
    equality shape: the Type layer concludes NO boxes, diags, or negated atoms. -/
theorem derivation_shape : ∀ {φ : Formula}, Derivation φ →
    EndsInPlays φ ∨ (∃ p, φ = .eq p p) ∨ (∃ p q, φ = .neg (.eq p q)) := by
  intro φ d
  induction d with
  | modusPonens φ' ψ d₁ d₂ ih₁ ih₂ =>
      rcases ih₁ with h | ⟨p, hp⟩ | ⟨p, q, hp⟩
      · cases h with
        | impl h' => exact Or.inl h'
      · cases hp
      · cases hp
  | hypSyll φ' ψ' χ' d₁ d₂ ih₁ ih₂ =>
      rcases ih₂ with h | ⟨p, hp⟩ | ⟨p, q, hp⟩
      · cases h with
        | impl h' => exact Or.inl (.impl h')
      · cases hp
      · cases hp
  | searchBranch k ψ a b me opponent hme => exact Or.inl (.impl .plays)
  | simStep me p q opponent a hme => exact Or.inl (.impl .plays)
  | botSimStep me p q opponent a hme => exact Or.inl (.impl .plays)
  | botSearchStep k ψ a b me opponent hme => exact Or.inl (.impl .plays)
  | iteBranchSearch_t k z a' c0 c1 ψ q me opponent hme =>
      exact Or.inl (.impl (.impl .plays))
  | eqRefl p => exact Or.inr (Or.inl ⟨p, rfl⟩)
  | eqNeg p q hne => exact Or.inr (Or.inr ⟨p, q, rfl⟩)

/-- The Type layer cannot conclude a box. -/
theorem derivation_no_box {b : Nat} {ψ : Formula} (d : Derivation (.box b ψ)) : False := by
  rcases derivation_shape d with h | ⟨p, hp⟩ | ⟨p, q, hp⟩
  · cases h
  · cases hp
  · cases hp

/-- Every judgment costs at least one character. -/
theorem provable_pos {m : Nat} {φ : Formula} (h : Provable m φ) : 1 ≤ m := by
  rcases provable_size_or_atom h with hsz | hatom
  · have := Formula.size_pos φ
    omega
  · exact atomProvable_pos hatom

/-- **Box-judgment inversion** (the sibling-sourcing tool): a derivable box comes from
    `boxIntro` — its content WAS a judgment, at a budget below the subscript — or from an
    `app` spine. No other rule concludes a box (the Type layer can't, atoms are `.plays`,
    everything else concludes impls/negs). -/
theorem box_inversion {m b : Nat} {ψ : Formula} (h : Provable m (.box b ψ)) :
    (∃ mIn, Provable mIn ψ ∧ mIn ≤ b ∧ b + (Formula.box b ψ).size ≤ m) ∨
    (∃ m₁ m₂ φ', Provable m₁ (.impl φ' (.box b ψ)) ∧ Provable m₂ φ' ∧
      m₁ + m₂ + (Formula.box b ψ).size ≤ m) := by
  cases h with
  | struct hd =>
      obtain ⟨d, _⟩ := hd
      exact (derivation_no_box d).elim
  | atom hatom => cases hatom
  | boxIntro =>
      -- index unification: the content's budget IS the subscript `b`
      rename_i hprem hle
      exact Or.inl ⟨b, hprem, Nat.le_refl _, hle⟩
  | app =>
      rename_i m₁ m₂ φ' h2 h1 hle
      exact Or.inr ⟨m₁, m₂, φ', h1, h2, hle⟩

/-! ## 7. C3b foundations — the SPLIT MEASURE `maxSLit`.

Cite targets are ONLY `.search` literals of programs; `.box`/`.diag` subscripts never
become budgets (boxes are never opened, §6). The master induction's tameness invariant
therefore tracks `maxSLitF` — search literals only — while subscripts stay size-paid and
gate-covered. The split lemma reassembles the full-literal gate bound from the two halves.
(CUT_RELEVANCE.md §5a′.) -/

mutual
  /-- The largest `.search` budget literal (subscripts of `.box`/`.diag` NOT counted). -/
  def maxSLitP : Prog → Nat
    | .const _ => 0
    | .self => 0
    | .opp => 0
    | .bot p => maxSLitP p
    | .sim p q => max (maxSLitP p) (maxSLitP q)
    | .ite b _ p q => max (maxSLitP b) (max (maxSLitP p) (maxSLitP q))
    | .search k φ p q => max k (max (maxSLitF φ) (max (maxSLitP p) (maxSLitP q)))

  def maxSLitF : Formula → Nat
    | .plays p q _ => max (maxSLitP p) (maxSLitP q)
    | .impl φ ψ => max (maxSLitF φ) (maxSLitF ψ)
    | .neg φ => maxSLitF φ
    | .box _ φ => maxSLitF φ
    | .eq p q => max (maxSLitP p) (maxSLitP q)
    | .diag _ φ => maxSLitF φ
end

/-! Substitution: search literals of an instance come from the parts. -/

mutual
  theorem maxSLitP_subst (u v : Prog) : ∀ (p : Prog),
      maxSLitP (p.subst u v) ≤ max (maxSLitP p) (max (maxSLitP u) (maxSLitP v)) := by
    intro p
    cases p with
    | const a => simp only [Prog.subst, maxSLitP]; omega
    | self => simp only [Prog.subst]; omega
    | opp => simp only [Prog.subst]; omega
    | bot p => simp only [Prog.subst]; omega
    | sim p₁ p₂ =>
        have h1 := maxSLitP_subst u v p₁
        have h2 := maxSLitP_subst u v p₂
        simp only [Prog.subst, maxSLitP] at *
        omega
    | ite b a p₁ p₂ =>
        have h1 := maxSLitP_subst u v b
        have h2 := maxSLitP_subst u v p₁
        have h3 := maxSLitP_subst u v p₂
        simp only [Prog.subst, maxSLitP] at *
        omega
    | search k φ p₁ p₂ =>
        have h1 := maxSLitF_subst u v φ
        have h2 := maxSLitP_subst u v p₁
        have h3 := maxSLitP_subst u v p₂
        simp only [Prog.subst, maxSLitP] at *
        omega

  theorem maxSLitF_subst (u v : Prog) : ∀ (φ : Formula),
      maxSLitF (φ.subst u v) ≤ max (maxSLitF φ) (max (maxSLitP u) (maxSLitP v)) := by
    intro φ
    cases φ with
    | plays p₁ p₂ a =>
        have h1 := maxSLitP_subst u v p₁
        have h2 := maxSLitP_subst u v p₂
        simp only [Formula.subst, maxSLitF] at *
        omega
    | impl φ ψ =>
        have h1 := maxSLitF_subst u v φ
        have h2 := maxSLitF_subst u v ψ
        simp only [Formula.subst, maxSLitF] at *
        omega
    | neg φ =>
        have h1 := maxSLitF_subst u v φ
        simp only [Formula.subst, maxSLitF] at *
        omega
    | box n φ =>
        have h1 := maxSLitF_subst u v φ
        simp only [Formula.subst, maxSLitF] at *
        omega
    | eq p₁ p₂ =>
        have h1 := maxSLitP_subst u v p₁
        simp only [Formula.subst, maxSLitF] at *
        omega
    | diag g φ => simp only [Formula.subst, maxSLitF]; omega
end

/-! The split lemma: full literals ≤ search literals + subscripts, and subscripts are
size-bounded — so `maxLitF φ ≤ maxSLitF φ + 2^|φ|`, which is what turns the tameness
invariant (`maxSLitF ≤ L`) plus local size-payment into the GATE bound
(`maxLitF ≤ L + 2^M ≤ 2^(M+2)`). -/

mutual
  theorem maxLitP_split : ∀ p : Prog, maxLitP p ≤ maxSLitP p + 2 ^ p.size := by
    intro p
    cases p with
    | const a => simp only [maxLitP, maxSLitP]; exact Nat.zero_le _
    | self => simp only [maxLitP, maxSLitP]; exact Nat.zero_le _
    | opp => simp only [maxLitP, maxSLitP]; exact Nat.zero_le _
    | bot p =>
        have h := maxLitP_split p
        have hm : (2:Nat) ^ p.size ≤ 2 ^ (Prog.bot p).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        simp only [maxLitP, maxSLitP]
        omega
    | sim p₁ p₂ =>
        have h1 := maxLitP_split p₁
        have h2 := maxLitP_split p₂
        have hm1 : (2:Nat) ^ p₁.size ≤ 2 ^ (Prog.sim p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        have hm2 : (2:Nat) ^ p₂.size ≤ 2 ^ (Prog.sim p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        simp only [maxLitP, maxSLitP]
        omega
    | ite b a p₁ p₂ =>
        have h0 := maxLitP_split b
        have h1 := maxLitP_split p₁
        have h2 := maxLitP_split p₂
        have hm0 : (2:Nat) ^ b.size ≤ 2 ^ (Prog.ite b a p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        have hm1 : (2:Nat) ^ p₁.size ≤ 2 ^ (Prog.ite b a p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        have hm2 : (2:Nat) ^ p₂.size ≤ 2 ^ (Prog.ite b a p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        simp only [maxLitP, maxSLitP]
        omega
    | search k φ p₁ p₂ =>
        have h0 := maxLitF_split φ
        have h1 := maxLitP_split p₁
        have h2 := maxLitP_split p₂
        have hm0 : (2:Nat) ^ φ.size ≤ 2 ^ (Prog.search k φ p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        have hm1 : (2:Nat) ^ p₁.size ≤ 2 ^ (Prog.search k φ p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        have hm2 : (2:Nat) ^ p₂.size ≤ 2 ^ (Prog.search k φ p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Prog.size]; omega)
        have hp := Nat.two_pow_pos (Prog.search k φ p₁ p₂).size
        simp only [maxLitP, maxSLitP]
        omega

  theorem maxLitF_split : ∀ φ : Formula, maxLitF φ ≤ maxSLitF φ + 2 ^ φ.size := by
    intro φ
    cases φ with
    | plays p₁ p₂ a =>
        have h1 := maxLitP_split p₁
        have h2 := maxLitP_split p₂
        have hm1 : (2:Nat) ^ p₁.size ≤ 2 ^ (Formula.plays p₁ p₂ a).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        have hm2 : (2:Nat) ^ p₂.size ≤ 2 ^ (Formula.plays p₁ p₂ a).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        simp only [maxLitF, maxSLitF]
        omega
    | impl φ ψ =>
        have h1 := maxLitF_split φ
        have h2 := maxLitF_split ψ
        have hm1 : (2:Nat) ^ φ.size ≤ 2 ^ (Formula.impl φ ψ).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        have hm2 : (2:Nat) ^ ψ.size ≤ 2 ^ (Formula.impl φ ψ).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        simp only [maxLitF, maxSLitF]
        omega
    | neg φ =>
        have h1 := maxLitF_split φ
        have hm1 : (2:Nat) ^ φ.size ≤ 2 ^ (Formula.neg φ).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        simp only [maxLitF, maxSLitF]
        omega
    | box n φ =>
        have hn : n < 2 ^ (Formula.box n φ).size :=
          lt_two_pow_of_log2_lt (by simp only [numCost, Formula.size]; omega)
        have h1 := maxLitF_split φ
        have hm1 : (2:Nat) ^ φ.size ≤ 2 ^ (Formula.box n φ).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        simp only [maxLitF, maxSLitF]
        omega
    | eq p₁ p₂ =>
        have h1 := maxLitP_split p₁
        have h2 := maxLitP_split p₂
        have hm1 : (2:Nat) ^ p₁.size ≤ 2 ^ (Formula.eq p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        have hm2 : (2:Nat) ^ p₂.size ≤ 2 ^ (Formula.eq p₁ p₂).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        simp only [maxLitF, maxSLitF]
        omega
    | diag g φ =>
        have hg : g < 2 ^ (Formula.diag g φ).size :=
          lt_two_pow_of_log2_lt (by simp only [numCost, Formula.size]; omega)
        have h1 := maxLitF_split φ
        have hm1 : (2:Nat) ^ φ.size ≤ 2 ^ (Formula.diag g φ).size :=
          Nat.pow_le_pow_right (by omega) (by simp only [numCost, Formula.size]; omega)
        simp only [maxLitF, maxSLitF]
        omega
end

/-- The gate bound the master induction's arms will use: a size-paid formula that is
    search-tame has ALL its literals under `2^(M+2)` (with `L ≤ M` and size ≤ budget
    ≤ M). -/
theorem gate_bound {L M m : Nat} {ψ : Formula} (hLM : L ≤ M) (hm : m ≤ M)
    (hsz : ψ.size ≤ m) (htame : maxSLitF ψ ≤ L) :
    maxLitF ψ ≤ 2 ^ (M + 2) := by
  have h1 := maxLitF_split ψ
  have h2 : (2:Nat) ^ ψ.size ≤ 2 ^ M :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (2:Nat) ^ M + 2 ^ M ≤ 2 ^ (M + 1) := by
    have : (2:Nat) ^ (M + 1) = 2 ^ M * 2 := Nat.pow_succ ..
    omega
  have h4 : (2:Nat) ^ (M + 1) ≤ 2 ^ (M + 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h5 : L ≤ 2 ^ M := by
    have := Nat.lt_two_pow_self (n := M)
    omega
  omega

/-! ## 8. [RETRACTED — see §9] the "tame trichotomy" over `PPair`.

**STATUS (2026-07-03, post-review): the theorem below is TRUE BUT VACUOUS** — its
`DboxMid`/`DboxPos` disjuncts do not mention the analyzed pair and are unconditionally
inhabited (`Tri_always`, §9), so `tame_trichotomy` follows in one line with no analysis.
The 26 arms are retained ONLY as a map of which cases can maintain which links. Original
(withdrawn) description follows.

Every positive pair (implication spines + one box-content descent) of a derivable formula
is: **D1** literal-nonincreasing (`Tame C → Tame B` — implicational, composes through the
chains), **D2** degenerate (consequent provable within budget), or one of THREE precisely
named box obstructions — **DboxAnt** (the pair's antecedent is a box: sibling-resolvable at
its discharge `app`), **DboxMid** (a box-antecedent pair recorded in some judgment: the
`implTrans`-through-box-middle kernel), **DboxPos** (a box-interior pair of some judgment:
content-judgment-resolvable). The obstruction disjuncts are SELF-CONTAINED (they mention
their own witnesses, not the ambient pair), so they pass through every composition
verbatim. This isolates the conjecture's residue to exactly the box-flavored positions the
sibling machinery (§6) is designed for. -/

/-- `.box j χ` occurs along the positive consequent chain. -/
inductive PosBox : Formula → Nat → Formula → Prop where
  | head {j : Nat} {χ : Formula} : PosBox (.box j χ) j χ
  | tail {X C' : Formula} {j : Nat} {χ : Formula} :
      PosBox C' j χ → PosBox (.impl X C') j χ

/-- Positive pairs at box-depth ≤ 1: implication-spine pairs, plus the spine pairs of one
    positive box's content (what `axK`-premise sourcing needs; deeper box interiors are
    never consumed — boxes are never opened). -/
def PPair (φ B C : Formula) : Prop :=
  PosImpl φ B C ∨ ∃ j χ, PosBox φ j χ ∧ PosImpl χ B C

theorem PPair_tail {X C' B C : Formula} (h : PPair C' B C) : PPair (.impl X C') B C := by
  rcases h with h | ⟨j, χ, pb, pi⟩
  · exact Or.inl (.tail h)
  · exact Or.inr ⟨j, χ, .tail pb, pi⟩

theorem PPair_tail_inv {X C' B C : Formula} (h : PPair (.impl X C') B C) :
    (B = X ∧ C = C') ∨ PPair C' B C := by
  rcases h with h | ⟨j, χ, pb, pi⟩
  · cases h with
    | head => exact Or.inl ⟨rfl, rfl⟩
    | tail h' => exact Or.inr (Or.inl h')
  · cases pb with
    | tail pb' => exact Or.inr (Or.inr ⟨j, χ, pb', pi⟩)

theorem PPair_box_inv {j₀ : Nat} {χ₀ B C : Formula} (h : PPair (.box j₀ χ₀) B C) :
    PosImpl χ₀ B C := by
  rcases h with h | ⟨j, χ, pb, pi⟩
  · cases h
  · cases pb with
    | head => exact pi

/-- Census steps never increase SEARCH literals (box/diag subscripts don't count). -/
theorem DAnt_slit : ∀ {B C : Formula}, DAnt B C → maxSLitF B ≤ maxSLitF C := by
  intro B C h
  induction h with
  | @searchBr k ψ a b me opponent hme =>
      have hs := maxSLitF_subst me opponent ψ
      subst hme
      simp only [maxSLitF, maxSLitP] at *
      omega
  | @botSearchSt k ψ a b me opponent hme =>
      have hs := maxSLitF_subst me opponent ψ
      subst hme
      simp only [maxSLitF, maxSLitP] at *
      omega
  | @simSt me p q opponent a hme =>
      have hp := maxSLitP_subst me opponent p
      have hq := maxSLitP_subst me opponent q
      subst hme
      simp only [maxSLitF, maxSLitP] at *
      omega
  | @botSimSt me p q opponent a hme =>
      have hp := maxSLitP_subst me opponent p
      have hq := maxSLitP_subst me opponent q
      subst hme
      simp only [maxSLitF, maxSLitP] at *
      omega
  | @iteBr₁ k z a' c0 c1 ψ q me opponent hme =>
      subst hme
      simp only [maxSLitF, maxSLitP] at *
      omega
  | @iteBr₂ k z a' c0 c1 ψ q me opponent hme =>
      have hs := maxSLitF_subst me opponent ψ
      subst hme
      simp only [maxSLitF, maxSLitP] at *
      omega
  | trans h₁ h₂ ih₁ ih₂ => omega

theorem endsInPlays_no_box : ∀ {φ : Formula} {j : Nat} {χ : Formula},
    EndsInPlays φ → PosBox φ j χ → False := by
  intro φ j χ he pb
  induction pb with
  | head => cases he
  | tail pb' ih =>
      cases he with
      | impl he' => exact ih he'

/-- The five-way answer. Obstruction disjuncts are self-contained (compose verbatim). -/
def Tri (L m : Nat) (B C : Formula) : Prop :=
  (maxSLitF C ≤ L → maxSLitF B ≤ L)
  ∨ (∃ b ψ₀, B = Formula.box b ψ₀)
  ∨ (∃ b ψ₀ m' X C', Provable m' X ∧ PPair X (.box b ψ₀) C')
  ∨ (∃ m' X j χ B' C', Provable m' X ∧ PosBox X j χ ∧ PosImpl χ B' C')
  ∨ (∃ m', m' ≤ m ∧ Provable m' C)

theorem Tri_mono {L m₁ m₂ : Nat} {B C : Formula} (h : m₁ ≤ m₂) (ht : Tri L m₁ B C) :
    Tri L m₂ B C := by
  rcases ht with h1 | h1 | h1 | h1 | ⟨m', hm', hC⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨m', by omega, hC⟩)))

set_option maxHeartbeats 2000000 in
/-- **C3b-i — the tame trichotomy**: every positive pair of a derivable judgment is
    literal-nonincreasing, degenerate within budget, or a precisely-named box obstruction. -/
theorem tame_trichotomy (L : Nat) : ∀ {m : Nat} {φ : Formula}, Provable m φ →
    ∀ {B C : Formula}, PPair φ B C → Tri L m B C := by
  intro m φ h
  refine Provable.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun m φ _ => ∀ {B C : Formula}, PPair φ B C → Tri L m B C)
    ?pConst ?pSelf ?pOpp ?pBot ?pSim ?pIte_t ?pIte_f ?pSearch_t ?pSearch_f ?pMk
    ?cStruct ?cAtom ?cWeaken ?cSTS ?cITrans ?cAtomBox ?cBoxIntro ?cApp ?cAxK ?cBox4
    ?cDiagF ?cDiagB ?cAxKf ?cImpS2 ?cBoxMono ?cAtomNeg h
  case pConst => intros; trivial
  case pSelf => intros; trivial
  case pOpp => intros; trivial
  case pBot => intros; trivial
  case pSim => intros; trivial
  case pIte_t => intros; trivial
  case pIte_f => intros; trivial
  case pSearch_t => intros; trivial
  case pSearch_f => intros; trivial
  case pMk => intros; trivial
  case cStruct =>
      intro φ0 k0 hd B C hp
      obtain ⟨d, _⟩ := hd
      rcases hp with hpi | ⟨j, χ, pb, pi⟩
      · exact Or.inl (fun hC =>
          Nat.le_trans (DAnt_slit (derivation_posImpl_ant d hpi)) hC)
      · rcases derivation_shape d with he | ⟨p, hp'⟩ | ⟨p, q, hp'⟩
        · exact absurd pb (fun pb => endsInPlays_no_box he pb)
        · subst hp'; cases pb
        · subst hp'; cases pb
  case cAtom =>
      intro k0 φ0 hatom _ B C hp
      cases hatom with
      | mk cert hle =>
          rcases hp with hpi | ⟨j, χ, pb, _⟩
          · cases hpi
          · cases pb
  case cWeaken =>
      intro k A ψ m' hψ hle ih B C hp
      rcases PPair_tail_inv hp with ⟨rfl, rfl⟩ | hp'
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨m', by omega, hψ⟩)))
      · exact Tri_mono (by omega) (ih hp')
  case cSTS =>
      intro k k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opnt hme hprud hmk hle ih B C hp
      rcases PPair_tail_inv hp with ⟨rfl, rfl⟩ | hp'
      · exact Or.inr (Or.inl ⟨k₁, _, rfl⟩)
      · rcases hp' with hpi | ⟨j, χ, pb, _⟩
        · cases hpi
        · cases pb
  case cITrans =>
      intro k A ψ χ' a b h1 h2 hle ih1 ih2 B C hp
      rcases PPair_tail_inv hp with ⟨rfl, rfl⟩ | hp'
      · -- head pair
        rcases ih2 (Or.inl .head) with d1₂ | ⟨b0, ψ₀, hψeq⟩ | dbm₂ | dbp₂ | ⟨m2', hm2', hC⟩
        · rcases ih1 (Or.inl .head) with d1₁ | dba₁ | dbm₁ | dbp₁ | ⟨m1', hm1', hψd⟩
          · exact Or.inl (fun hC => d1₁ (d1₂ hC))
          · exact Or.inr (Or.inl dba₁)
          · exact Or.inr (Or.inr (Or.inl dbm₁))
          · exact Or.inr (Or.inr (Or.inr (Or.inl dbp₁)))
          · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨b + m1' + C.size, ?_, ?_⟩)))
            · have hA := Formula.size_pos B
              simp only [numCost, Formula.size] at hle
              omega
            · exact Provable.app _ b m1' ψ C h2 hψd (Nat.le_refl _)
        · refine Or.inr (Or.inr (Or.inl ⟨b0, ψ₀, b, .impl ψ C, C, h2, ?_⟩))
          rw [hψeq] at *
          exact Or.inl .head
        · exact Or.inr (Or.inr (Or.inl dbm₂))
        · exact Or.inr (Or.inr (Or.inr (Or.inl dbp₂)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨m2', by omega, hC⟩)))
      · exact Tri_mono (by omega) (ih2 (PPair_tail hp'))
  case cAtomBox =>
      intro k kBox p q a hatom hle _ B C hp
      rcases PPair_tail_inv hp with ⟨rfl, rfl⟩ | hp'
      · exact Or.inl (fun hC => by simp only [maxSLitF] at hC ⊢; omega)
      · cases PPair_box_inv hp'
  case cBoxIntro =>
      intro kIn K A hprem hle ih B C hp
      have hpi := PPair_box_inv hp
      exact Tri_mono (by omega) (ih (Or.inl hpi))
  case cApp =>
      intro k m₁ m₂ ψ α h1 h2 hle ih1 ih2 B C hp
      have hα := Formula.size_pos α
      exact Tri_mono (by omega) (ih1 (PPair_tail hp))
  case cAxK =>
      intro a b c m' K A α hprem hgate hle ih B C hp
      rcases PPair_tail_inv hp with ⟨rfl, rfl⟩ | hp'
      · exact Or.inr (Or.inl ⟨b, A, rfl⟩)
      · have hpi := PPair_box_inv hp'
        exact Tri_mono (by omega) (ih (Or.inr ⟨a, .impl A α, .head, .tail hpi⟩))
  case cBox4 =>
      intro a b K A hgate hle B C hp
      rcases PPair_tail_inv hp with ⟨rfl, rfl⟩ | hp'
      · exact Or.inr (Or.inl ⟨a, A, rfl⟩)
      · cases PPair_box_inv hp'
  case cDiagF =>
      intro pm fb g K tgt hgate hle ih B C hp
      rcases PPair_tail_inv hp with ⟨rfl, rfl⟩ | hp'
      · exact Or.inl (fun hC => by simp only [maxSLitF] at hC ⊢; omega)
      · rcases PPair_tail_inv hp' with ⟨rfl, rfl⟩ | hp''
        · exact Or.inr (Or.inl ⟨g, _, rfl⟩)
        · exact Tri_mono (by omega) (ih (PPair_tail hp''))
  case cDiagB =>
      intro pm fb g K tgt hgate hle ih B C hp
      rcases PPair_tail_inv hp with ⟨rfl, rfl⟩ | hp'
      · exact Or.inl (fun hC => by simp only [maxSLitF] at hC ⊢; omega)
      · rcases hp' with hpi | ⟨j, χ, pb, _⟩
        · cases hpi
        · cases pb
  case cAxKf =>
      intro a b c K A α hgate hle B C hp
      rcases PPair_tail_inv hp with ⟨rfl, rfl⟩ | hp'
      · exact Or.inr (Or.inl ⟨a, _, rfl⟩)
      · rcases PPair_tail_inv hp' with ⟨rfl, rfl⟩ | hp''
        · exact Or.inr (Or.inl ⟨b, A, rfl⟩)
        · have hpi := PPair_box_inv hp''
          refine Or.inr (Or.inr (Or.inr (Or.inl
            ⟨K, .impl (.box a (.impl A α)) (.impl (.box b A) (.box c α)),
              c, α, B, C, Provable.axKf a b c K A α hgate hle,
              .tail (.tail .head), hpi⟩)))
  case cImpS2 =>
      intro A ψ χ' m₁ m₂ K h1 h2 hle ih1 ih2 B C hp
      rcases PPair_tail_inv hp with ⟨rfl, rfl⟩ | hp'
      · rcases ih1 (Or.inl (.tail .head)) with dt | ⟨b0, ψ₀, hψeq⟩ | dbm | dbp
          | ⟨mt', hmt', hC⟩
        · rcases ih1 (Or.inl .head) with d1₁ | dba₁ | dbm₁ | dbp₁ | ⟨m1', hm1', hd⟩
          · refine Or.inl (fun hC => d1₁ ?_)
            have := dt hC
            simp only [maxSLitF]
            omega
          · exact Or.inr (Or.inl dba₁)
          · exact Or.inr (Or.inr (Or.inl dbm₁))
          · exact Or.inr (Or.inr (Or.inr (Or.inl dbp₁)))
          · rcases ih2 (Or.inl .head) with d1h | dbah | dbmh | dbph | ⟨m2', hm2', hψd⟩
            · exact Or.inl (fun hC => d1h (dt hC))
            · exact Or.inr (Or.inl dbah)
            · exact Or.inr (Or.inr (Or.inl dbmh))
            · exact Or.inr (Or.inr (Or.inr (Or.inl dbph)))
            · refine Or.inr (Or.inr (Or.inr (Or.inr
                ⟨m1' + m2' + C.size, ?_, ?_⟩)))
              · have hA := Formula.size_pos B
                simp only [numCost, Formula.size] at hle
                omega
              · exact Provable.app _ m1' m2' ψ C hd hψd (Nat.le_refl _)
        · refine Or.inr (Or.inr (Or.inl ⟨b0, ψ₀, m₁, .impl B (.impl ψ C), C, h1, ?_⟩))
          rw [hψeq] at *
          exact Or.inl (.tail .head)
        · exact Or.inr (Or.inr (Or.inl dbm))
        · exact Or.inr (Or.inr (Or.inr (Or.inl dbp)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨mt', by omega, hC⟩)))
      · exact Tri_mono (by omega) (ih1 (PPair_tail (PPair_tail hp')))
  case cBoxMono =>
      intro a b K A hab hle B C hp
      rcases PPair_tail_inv hp with ⟨rfl, rfl⟩ | hp'
      · exact Or.inr (Or.inl ⟨a, A, rfl⟩)
      · have hpi := PPair_box_inv hp'
        refine Or.inr (Or.inr (Or.inr (Or.inl
          ⟨K, .impl (.box a A) (.box b A), b, A, B, C,
            Provable.boxMono a b K A hab hle, .tail .head, hpi⟩)))
  case cAtomNeg =>
      intro k p q b aN m' hatom hne hle _ B C hp
      rcases hp with hpi | ⟨j, χ, pb, _⟩
      · cases hpi
      · cases pb

/-- The judgment-head corollary — Lemma A's dichotomy in its final (maxSLit) form. -/
theorem tame_impl_trichotomy (L : Nat) {m : Nat} {B C : Formula}
    (h : Provable m (.impl B C)) : Tri L m B C :=
  tame_trichotomy L h (Or.inl .head)

/-! ## 9. RETRACTION of C3b-i — `Tri` is vacuous (machine-checked).

External review (2026-07-03) observed that `Tri`'s third and fourth disjuncts quantify
their witnesses fully existentially with NO occurrence of the analyzed pair `(B, C)`:
any provable judgment containing a box-flavored pair — one fixed `box4` instance —
witnesses them for EVERY input. The kernel confirms: `Tri_always` below holds with no
hypotheses, so `tame_trichotomy` (§8) carries no information beyond its own arms'
private bookkeeping. C3b-i is RETRACTED as a milestone.

THE LESSON (recorded in CUT_RELEVANCE.md §5c): when an induction's compositions only
close after UNLINKING an escape disjunct from the goal, the unlinking does not "isolate
the obstruction" — it makes the disjunct `True` and the theorem hollow. Composition
pressure is the signal that the pairwise judgment-local shape cannot carry the
information; the correct responses are to carry it (linked, with whatever context the
composition needs) or to handle those cases where the missing context (the sibling
judgment) is actually present — never to drop the link. The same softness, in milder
form, affects `PAnt.axkPair` (§5): `PAnt` is trivial on box-box pairs, and `trans` leaks
this to any pair whose path routes through boxes. -/

/-- One fixed `box4` witness inhabits the `DboxMid` disjunct — unrelated to any pair. -/
theorem dboxMid_always :
    ∃ b ψ₀ m' X C', Provable m' X ∧ PPair X (.box b ψ₀) C' := by
  refine ⟨0, .plays .self .opp .C, 1000, _,
    .box 1000 (.box 0 (.plays .self .opp .C)), ?_, Or.inl .head⟩
  exact Provable.box4 0 1000 1000 (.plays .self .opp .C) (by decide) (by decide)

/-- **`Tri` holds for every input whatsoever** — the vacuity, kernel-checked. -/
theorem Tri_always (L m : Nat) (B C : Formula) : Tri L m B C :=
  Or.inr (Or.inr (Or.inl dboxMid_always))

/-- The one-line derivation the review predicted: `tame_trichotomy` without induction. -/
theorem tame_trichotomy_vacuous (L : Nat) {m : Nat} {φ : Formula}
    (_ : Provable m φ) {B C : Formula} (_ : PPair φ B C) : Tri L m B C :=
  Tri_always L m B C

/-! ## 10. C3b-i′ — the LINKED diagnostic: two machine-checked FALSITY results.

Running the retraction's corrected course (§5c step 1) against the tight, linked targets
produced findings BEFORE the induction: the linked forms are not merely hard — at two
precisely-located position classes they are FALSE, so no amount of proof effort closes
them. This pins down exactly what information a correct formulation must carry.

**Finding 1 (`ppair_linked_false`)**: over full `PPair` (box-content descent included),
the linked trichotomy `D1 ∨ (B is a box) ∨ D2` is FALSE. Witness: `axKf` is a premise-free
axiom schema, so its consequent-box CONTENT `α` is arbitrary — put `α := .impl wild eqCD`
(a wild-slit antecedent and an unprovable consequent) inside and the content pair defeats
all three disjuncts. Consequence: box-content pairs can NEVER be covered by a
judgment-local lemma; contents must be sourced at CONSUMPTION (box judgments via
`box_inversion` — the §5 consumer-side design), and `PPair`'s boxT descent must go.

**Finding 2 (`spine_boxlinked_false`)**: even at SPINE level, the box-LINKED form
`D1 ∨ (B = □ψ₀ ∧ (Tame C → Tame ψ₀)) ∨ D2` is FALSE at GUARDED tail positions — the
`axKf` conclusion's tail pair `(□b wild, □c eqCD)` sits behind the undischarged antecedent
`□a(wild → eqCD)`, and before discharge nothing links its sides. Consequence: pairwise
judgment-local dichotomies are genuinely false below undischarged antecedents; the guard
CONTEXT (provability of the guarding antecedents) is necessary information, vindicating
the discharge-site (`app`-with-sibling) architecture of §5.

**The corrected foundation (C3b-ii′, for the next attack):**
  * motive = pairs WITH GUARD CONTEXT: `PosImplCtx φ Γ B C` collecting the antecedents `Γ`
    passed on the way to the pair; the dichotomy hypothesizes `∀ X ∈ Γ, ∃ mX, Provable mX X`
    (at discharge sites the siblings supply exactly this);
  * induction = BUDGET-STRONG-INDUCTION with inversion, NOT structural `rec`: the key
    observation is that pair-queries never cross cites (`searchThenSearch_t`'s and
    `search_t`'s cited premises contribute NO pairs to their conclusions' spines — checked
    rule-by-rule), so every pair-relevant premise is at a strictly smaller budget, and the
    opaque degenerate witnesses (the D2 wall of the merged-motive design) are covered by
    the same strong IH — no transform-carrying needed for the dichotomy itself;
  * kernel = `HBoxHead` (the box-chain grounding at HEAD positions only):
    `Provable m (.impl (.box b₀ ψ₀) C) → (Tame C → Tame ψ₀) ∨ (∃ m' ≤ m, Provable m' C)` —
    the head-level form dodges both falsity findings (heads are unguarded, and box
    contents at heads come from constrained producers: the census families, `axK`'s
    premise-constrained instances, chains, or discharged `axKf` — whose discharge sibling
    `□a(ψ₀ → α)` constrains the content). -/

/-- Distinct constant programs are never provably equal (soundness). -/
theorem eq_const_unprovable {m : Nat} :
    ¬ Provable m (.eq (.const .C) (.const .D)) := by
  intro h
  have h2 := PD.BaseTheorems.Provable_sound _ _ h
  simp only [Formula.interp] at h2
  exact absurd h2 (by decide)

/-- Nor is any box of that equality (soundness twice: `interp (.box c φ) = Provable c φ`). -/
theorem box_eq_unprovable {m c : Nat} :
    ¬ Provable m (.box c (.eq (.const .C) (.const .D))) := by
  intro h
  have h2 := PD.BaseTheorems.Provable_sound _ _ h
  simp only [Formula.interp] at h2
  exact eq_const_unprovable h2

/-- A formula with a nonzero search literal: `maxSLitF wildF = 1`. -/
def wildF : Formula :=
  .plays (.search 1 (.plays .self .self .C) (.const .C) (.const .C)) (.const .C) .C

/-- **Finding 1**: the linked trichotomy over full `PPair` is FALSE — `axKf`'s
    consequent-box content is arbitrary, so its content pairs defeat all disjuncts. -/
theorem ppair_linked_false :
    ∃ (L m : Nat) (φ B C : Formula), Provable m φ ∧ PPair φ B C ∧
      ¬ ((maxSLitF C ≤ L → maxSLitF B ≤ L)
         ∨ (∃ b ψ₀, B = Formula.box b ψ₀)
         ∨ (∃ m', m' ≤ m ∧ Provable m' C)) := by
  refine ⟨0, 1000, _, wildF, .eq (.const .C) (.const .D),
    Provable.axKf 0 0 1000 1000 (.plays (.const .C) (.const .C) .C)
      (.impl wildF (.eq (.const .C) (.const .D))) (by decide) (by decide),
    Or.inr ⟨1000, _, .tail (.tail .head), .head⟩, ?_⟩
  rintro (h1 | ⟨b, ψ₀, hB⟩ | ⟨m', _, hC⟩)
  · have := h1 (by decide)
    revert this
    decide
  · simp only [wildF] at hB
    cases hB
  · exact eq_const_unprovable hC

/-- **Finding 2**: even at SPINE level, the box-LINKED dichotomy is FALSE at guarded tail
    positions — before its antecedent is discharged, `axKf`'s tail pair has no link. -/
theorem spine_boxlinked_false :
    ∃ (L m : Nat) (φ B C : Formula), Provable m φ ∧ PosImpl φ B C ∧
      ¬ ((maxSLitF C ≤ L → maxSLitF B ≤ L)
         ∨ (∃ b ψ₀, B = Formula.box b ψ₀ ∧
              (maxSLitF C ≤ L → maxSLitF ψ₀ ≤ L))
         ∨ (∃ m', m' ≤ m ∧ Provable m' C)) := by
  refine ⟨0, 1000, _, .box 0 wildF, .box 1000 (.eq (.const .C) (.const .D)),
    Provable.axKf 0 0 1000 1000 wildF (.eq (.const .C) (.const .D))
      (by decide) (by decide),
    .tail .head, ?_⟩
  rintro (h1 | ⟨b, ψ₀, hB, hlink⟩ | ⟨m', _, hC⟩)
  · have := h1 (by decide)
    revert this
    decide
  · -- B = .box 0 wildF forces ψ₀ = wildF; the link then demands Tame wildF — false
    injection hB with hb hψ
    subst hψ
    have := hlink (by decide)
    revert this
    decide
  · exact box_eq_unprovable hC

/-! ## 11. C3b-ii′ probe — the kernel `HBoxHead` is ALSO FALSE (the third refutation).

Before building the guard-context dichotomy on §5d's foundation, the kernel got the same
adversarial probe that caught §9 and §10 — and it fails too. The counterexample is a
**dead implication**: a derivable judgment whose boxed antecedent is UNPROVABLE (so the
implication can never fire via `app`), assembled from four engine facts:

  * provable formulas carry arbitrary search literals (`eqRefl` on any program — `wildA`
    below is provable with `maxSLitF = 1`);
  * `weakenImpl` puts an ARBITRARY antecedent in front of a provable formula;
  * `boxIntro` + `axK` box the degenerate implication and distribute it, planting the
    arbitrary antecedent inside a boxed-antecedent implication;
  * `impS2` against a free `axKf` instance composes away the middle, leaving
    `deadJ : Provable 10000 (.impl (.box 300 ψ₀) (.box 1000 eqCD))`
    with `ψ₀` wild (slit 1), the consequent tame (slit 0) and UNPROVABLE.

`deadJ` defeats both of `HBoxHead`'s disjuncts at an UNGUARDED HEAD pair
(`hboxhead_false`), and since `maxSLitF (.box 300 ψ₀) = maxSLitF ψ₀`, the same judgment
refutes the head-level linked dichotomy outright (`head_dichotomy_false`). Combined with
§10: pairwise judgment-local dichotomies fail at EVERY position class — box content,
guarded tail, and now unguarded head. The judgment-local program is CLOSED.

What survives, again, is the conjecture: `deadJ` is dead weight — both its sides are
unprovable (`box_psi0_unprovable`, `box_eq_unprovable`), so no derivation of a provable
goal ever consumes it through `app`, and minimality should excise it. The analysis must
move from judgments to MINIMAL DERIVATION TREES of provable roots — see the note's §5e
for the fork this forces. -/

/-- The §5d kernel, as stated there: box-antecedent grounding at head positions. -/
def HBoxHead (L : Nat) : Prop :=
  ∀ m b₀ ψ₀ C, Provable m (.impl (.box b₀ ψ₀) C) →
    (maxSLitF C ≤ L → maxSLitF ψ₀ ≤ L) ∨ (∃ m', m' ≤ m ∧ Provable m' C)

/-- A program with a positive search subscript (never evaluated — pure literal weight). -/
def wildQ : Prog := .search 1 (.eq (.const .C) (.const .C)) (.const .C) (.const .C)

/-- Provable (by `eqRefl`) yet wild: `maxSLitF wildA = 1`. Provability does not bound
    search literals — the atom layer certifies reflexivity for ANY program. -/
def wildA : Formula := .eq wildQ wildQ

/-- The wild, semantically FALSE antecedent content: `wildA → (C = D)`. -/
def psi0 : Formula := .impl wildA (.eq (.const .C) (.const .D))

theorem wildA_provable : Provable 100 wildA :=
  .struct ⟨.eqRefl wildQ, by decide⟩

theorem psi0_unprovable {m : Nat} : ¬ Provable m psi0 := by
  intro h
  have h2 := PD.BaseTheorems.Provable_sound _ _ h
  simp only [psi0, Formula.interp] at h2
  exact absurd (h2 rfl) (by decide)

/-- `deadJ`'s antecedent never fires: the boxed content is unprovable. -/
theorem box_psi0_unprovable {m b : Nat} : ¬ Provable m (.box b psi0) := by
  intro h
  have h2 := PD.BaseTheorems.Provable_sound _ _ h
  simp only [Formula.interp] at h2
  exact psi0_unprovable h2

/-- The dead implication: derivable, wild boxed antecedent, tame unprovable consequent. -/
theorem deadJ :
    Provable 10000 (.impl (.box 300 psi0) (.box 1000 (.eq (.const .C) (.const .D)))) := by
  have h1 : Provable 200 (.impl psi0 wildA) :=
    .weakenImpl psi0 wildA 100 wildA_provable (by decide)
  have hbox : Provable 500 (.box 200 (.impl psi0 wildA)) :=
    .boxIntro 200 500 (.impl psi0 wildA) h1 (by decide)
  have h2 : Provable 2000 (.impl (.box 300 psi0) (.box 600 wildA)) :=
    .axK 200 300 600 500 2000 psi0 wildA hbox (by decide) (by decide)
  have h1' : Provable 3000
      (.impl (.box 300 psi0)
             (.impl (.box 600 wildA) (.box 1000 (.eq (.const .C) (.const .D))))) :=
    .axKf 300 600 1000 3000 wildA (.eq (.const .C) (.const .D)) (by decide) (by decide)
  exact .impS2 (.box 300 psi0) (.box 600 wildA)
    (.box 1000 (.eq (.const .C) (.const .D))) 3000 2000 10000 h1' h2 (by decide)

/-- **The third refutation**: the §5d kernel is false — at an unguarded head pair. -/
theorem hboxhead_false : ¬ HBoxHead 0 := by
  intro h
  rcases h 10000 300 psi0 (.box 1000 (.eq (.const .C) (.const .D))) deadJ with
    h1 | ⟨m', _, hC⟩
  · have := h1 (by decide)
    revert this
    decide
  · exact box_eq_unprovable hC

/-- The same judgment refutes the head-level linked dichotomy itself (`Γ = []`):
    with §10, pairwise dichotomies fail at every position class. -/
theorem head_dichotomy_false :
    ∃ (m : Nat) (B C : Formula), Provable m (.impl B C) ∧
      ¬ ((maxSLitF C ≤ 0 → maxSLitF B ≤ 0) ∨ (∃ m', m' ≤ m ∧ Provable m' C)) := by
  refine ⟨10000, .box 300 psi0, .box 1000 (.eq (.const .C) (.const .D)), deadJ, ?_⟩
  rintro (h1 | ⟨m', _, hC⟩)
  · have := h1 (by decide)
    revert this
    decide
  · exact box_eq_unprovable hC

end PD.T48
