import PrisonersDilemma.Decidability.T42ProvableB
import PrisonersDilemma.Decidability.T45CertReads

/-!
# T4.6 spike — the GLOBAL query universe (T4.4c part 2a).

`DECIDABILITY_ROADMAP.md` T4.4c part 2. The stabilization space for `stepB` (T4.4) is
`(budgets ≤ R) × (size-stratified, invariant-filtered formulas)`. This spike builds the
BUDGET and PROGRAM ingredients and proves the containment lemmas the checker-closure
(part 2b) consumes:

  * `maxLit` kit — literals never grow: subterms (`maxLitP_of_mem`/`maxLitF_of_mem`) and
    substitutions (`maxLitP_subst`/`maxLitF_subst`) stay under the parts' maxima.
  * **The budget ceiling is non-circular**: every read either strictly decreases the
    budget or jumps to a guard cite at a LITERAL — and literals come from the roots
    (`≤ L₀`) or from `modestGate`-gated cut material (`≤ N`). So `LU := max L₀ N` bounds
    every jump target, and `R := max k₀ LU` bounds every reachable budget.
  * **`allowedProgs`** — the global program universe: subterm closure of the roots,
    `.self`/`.opp`, and every closed modest literal-gated program of size `≤ R` (the
    possible cut-atom arguments). Subterm-CLOSED, all MODEST, all literals `≤ LU`.
  * **`GF`** — the global guard family: `guardU u v` over all pairs `u v ∈ allowedProgs`
    (T4.3's per-pair guard universes, glued). Finite; `.plays` args of members are again
    in `allowedProgs`; literals `≤ LU`.
  * **`certRead_budget` / `certRead_mem_GF`** — the T4.5 read interface, globalized:
    every oracle consultation of a certificate search rooted at an `allowedProgs` pair
    has budget `≤ max b LU` and formula in `GF` (or the `.neg` of a member).

Part 2b: the size-stratified formula space `SL`, the 16-checker in-space closure and
`stepB` congruence, the countP stabilization, and the `Decidable` payoff.
-/

namespace PD.T46
open PD PD.T31 PD.T42 PD.T43 PD.T45

/-! ## 1. Literals never grow: subterms and substitutions. -/

mutual
  theorem maxLitP_of_mem : ∀ (p q : Prog), q ∈ subsP p → maxLitP q ≤ maxLitP p := by
    intro p
    cases p with
    | const a =>
        intro q hq
        simp only [subsP, List.mem_singleton] at hq
        subst hq; exact Nat.le_refl _
    | self =>
        intro q hq
        simp only [subsP, List.mem_singleton] at hq
        subst hq; exact Nat.le_refl _
    | opp =>
        intro q hq
        simp only [subsP, List.mem_singleton] at hq
        subst hq; exact Nat.le_refl _
    | bot p =>
        intro q hq
        simp only [subsP, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact Nat.le_refl _
        · have := maxLitP_of_mem p q hq
          simp only [maxLitP]
          omega
    | sim p₁ p₂ =>
        intro q hq
        simp only [subsP, List.mem_cons, List.mem_append] at hq
        rcases hq with rfl | hq | hq
        · exact Nat.le_refl _
        · have := maxLitP_of_mem p₁ q hq
          simp only [maxLitP]; omega
        · have := maxLitP_of_mem p₂ q hq
          simp only [maxLitP]; omega
    | ite b a p₁ p₂ =>
        intro q hq
        simp only [subsP, List.mem_cons, List.mem_append] at hq
        rcases hq with rfl | (hq | hq) | hq
        · exact Nat.le_refl _
        · have := maxLitP_of_mem b q hq
          simp only [maxLitP]; omega
        · have := maxLitP_of_mem p₁ q hq
          simp only [maxLitP]; omega
        · have := maxLitP_of_mem p₂ q hq
          simp only [maxLitP]; omega
    | search k φ p₁ p₂ =>
        intro q hq
        simp only [subsP, List.mem_cons, List.mem_append] at hq
        rcases hq with rfl | (hq | hq) | hq
        · exact Nat.le_refl _
        · have := maxLitF_of_mem φ q hq
          simp only [maxLitP]; omega
        · have := maxLitP_of_mem p₁ q hq
          simp only [maxLitP]; omega
        · have := maxLitP_of_mem p₂ q hq
          simp only [maxLitP]; omega

  theorem maxLitF_of_mem : ∀ (φ : Formula) (q : Prog), q ∈ subsF φ → maxLitP q ≤ maxLitF φ := by
    intro φ
    cases φ with
    | plays p₁ p₂ a =>
        intro q hq
        simp only [subsF, List.mem_append] at hq
        rcases hq with hq | hq
        · have := maxLitP_of_mem p₁ q hq
          simp only [maxLitF]; omega
        · have := maxLitP_of_mem p₂ q hq
          simp only [maxLitF]; omega
    | impl φ ψ =>
        intro q hq
        simp only [subsF, List.mem_append] at hq
        rcases hq with hq | hq
        · have := maxLitF_of_mem φ q hq
          simp only [maxLitF]; omega
        · have := maxLitF_of_mem ψ q hq
          simp only [maxLitF]; omega
    | neg φ =>
        intro q hq
        have := maxLitF_of_mem φ q hq
        simp only [maxLitF]; omega
    | box n φ =>
        intro q hq
        have := maxLitF_of_mem φ q hq
        simp only [maxLitF]; omega
    | eq p₁ p₂ =>
        intro q hq
        simp only [subsF, List.mem_append] at hq
        rcases hq with hq | hq
        · have := maxLitP_of_mem p₁ q hq
          simp only [maxLitF]; omega
        · have := maxLitP_of_mem p₂ q hq
          simp only [maxLitF]; omega
    | diag g φ =>
        intro q hq
        have := maxLitF_of_mem φ q hq
        simp only [maxLitF]; omega
end

mutual
  theorem maxLitP_subst (u v : Prog) : ∀ (p : Prog),
      maxLitP (p.subst u v) ≤ max (maxLitP p) (max (maxLitP u) (maxLitP v)) := by
    intro p
    cases p with
    | const a => simp only [Prog.subst, maxLitP]; omega
    | self => simp only [Prog.subst]; omega
    | opp => simp only [Prog.subst]; omega
    | bot p => simp only [Prog.subst]; omega
    | sim p₁ p₂ =>
        have h1 := maxLitP_subst u v p₁
        have h2 := maxLitP_subst u v p₂
        simp only [Prog.subst, maxLitP] at *
        omega
    | ite b a p₁ p₂ =>
        have h1 := maxLitP_subst u v b
        have h2 := maxLitP_subst u v p₁
        have h3 := maxLitP_subst u v p₂
        simp only [Prog.subst, maxLitP] at *
        omega
    | search k φ p₁ p₂ =>
        have h1 := maxLitF_subst u v φ
        have h2 := maxLitP_subst u v p₁
        have h3 := maxLitP_subst u v p₂
        simp only [Prog.subst, maxLitP] at *
        omega

  theorem maxLitF_subst (u v : Prog) : ∀ (φ : Formula),
      maxLitF (φ.subst u v) ≤ max (maxLitF φ) (max (maxLitP u) (maxLitP v)) := by
    intro φ
    cases φ with
    | plays p₁ p₂ a =>
        have h1 := maxLitP_subst u v p₁
        have h2 := maxLitP_subst u v p₂
        simp only [Formula.subst, maxLitF] at *
        omega
    | impl φ ψ =>
        have h1 := maxLitF_subst u v φ
        have h2 := maxLitF_subst u v ψ
        simp only [Formula.subst, maxLitF] at *
        omega
    | neg φ =>
        have h1 := maxLitF_subst u v φ
        simp only [Formula.subst, maxLitF] at *
        omega
    | box n φ =>
        have h1 := maxLitF_subst u v φ
        simp only [Formula.subst, maxLitF] at *
        omega
    | eq p₁ p₂ =>
        have h1 := maxLitP_subst u v p₁
        simp only [Formula.subst, maxLitF] at *
        omega
    | diag g φ => simp only [Formula.subst]; omega
end

/-! ## 2. The global program universe and the guard family. -/

section Universe

variable (r₁ r₂ : Prog) (N R : Nat)

/-- The roots' literal ceiling. -/
def L₀ : Nat := max (maxLitP r₁) (maxLitP r₂)

/-- Every jump target: root literals or gated-cut literals. -/
def LU : Nat := max (L₀ r₁ r₂) N

/-- Generators of the global program universe: the roots, the placeholders, and every
    possible cut-atom argument (closed, modest, literal-gated, size `≤ R`). -/
def baseProgs : List Prog :=
  r₁ :: r₂ :: .self :: .opp ::
    (enumProg R).filter (fun p => closedP p && modestP p && decide (maxLitP p ≤ N))

/-- The global program universe: subterm closure of the generators. FINITE. -/
def allowedProgs : List Prog :=
  (baseProgs r₁ r₂ N R).flatMap subsP

theorem allowedProgs_subterm_closed {p : Prog} (hp : p ∈ allowedProgs r₁ r₂ N R)
    {q : Prog} (hq : q ∈ subsP p) : q ∈ allowedProgs r₁ r₂ N R := by
  simp only [allowedProgs, List.mem_flatMap] at hp ⊢
  obtain ⟨base, hbase, hpb⟩ := hp
  exact ⟨base, hbase, subsP_trans base p hpb q hq⟩

theorem allowedProgs_modest (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true) :
    ∀ {p : Prog}, p ∈ allowedProgs r₁ r₂ N R → modestP p = true := by
  intro p hp
  simp only [allowedProgs, List.mem_flatMap] at hp
  obtain ⟨base, hbase, hpb⟩ := hp
  have hbm : modestP base = true := by
    simp only [baseProgs, List.mem_cons, List.mem_filter, Bool.and_eq_true] at hbase
    rcases hbase with rfl | rfl | rfl | rfl | ⟨_, ⟨_, hm⟩, _⟩
    · exact h₁
    · exact h₂
    · rfl
    · rfl
    · exact hm
  exact modestP_of_mem base hbm p hpb

theorem allowedProgs_lit : ∀ {p : Prog}, p ∈ allowedProgs r₁ r₂ N R →
    maxLitP p ≤ LU r₁ r₂ N := by
  intro p hp
  simp only [allowedProgs, List.mem_flatMap] at hp
  obtain ⟨base, hbase, hpb⟩ := hp
  have hbl : maxLitP base ≤ LU r₁ r₂ N := by
    simp only [baseProgs, List.mem_cons, List.mem_filter, Bool.and_eq_true,
      decide_eq_true_eq] at hbase
    rcases hbase with rfl | rfl | rfl | rfl | ⟨_, _, hl⟩
    · simp only [LU, L₀]; omega
    · simp only [LU, L₀]; omega
    · simp only [maxLitP]; omega
    · simp only [maxLitP]; omega
    · simp only [LU]; omega
  exact Nat.le_trans (maxLitP_of_mem base p hpb) hbl

/-- The roots are in the universe. -/
theorem root₁_mem : r₁ ∈ allowedProgs r₁ r₂ N R := by
  simp only [allowedProgs, List.mem_flatMap]
  exact ⟨r₁, by simp [baseProgs], mem_subsP_self r₁⟩

theorem root₂_mem : r₂ ∈ allowedProgs r₁ r₂ N R := by
  simp only [allowedProgs, List.mem_flatMap]
  exact ⟨r₂, by simp [baseProgs], mem_subsP_self r₂⟩

/-- T4.3's per-pair players are in the universe (for universe pairs). -/
theorem players_mem {u v : Prog} (hu : u ∈ allowedProgs r₁ r₂ N R)
    (hv : v ∈ allowedProgs r₁ r₂ N R) :
    ∀ {p : Prog}, p ∈ players u v → p ∈ allowedProgs r₁ r₂ N R := by
  intro p hp
  simp only [players, List.mem_cons] at hp
  rcases hp with rfl | rfl | hp
  · exact hu
  · exact hv
  · have hmem := (List.mem_filter.mp hp).1
    simp only [certU, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact allowedProgs_subterm_closed r₁ r₂ N R hu hmem
    · exact allowedProgs_subterm_closed r₁ r₂ N R hv hmem

/-- Per-pair cert bodies are in the universe (for universe pairs). -/
theorem certU_mem {u v : Prog} (hu : u ∈ allowedProgs r₁ r₂ N R)
    (hv : v ∈ allowedProgs r₁ r₂ N R) :
    ∀ {p : Prog}, p ∈ certU u v → p ∈ allowedProgs r₁ r₂ N R := by
  intro p hp
  simp only [certU, List.mem_append] at hp
  rcases hp with hp | hp
  · exact allowedProgs_subterm_closed r₁ r₂ N R hu hp
  · exact allowedProgs_subterm_closed r₁ r₂ N R hv hp

/-- **The global guard family**: every pair's T4.3 guard universe, glued. FINITE. -/
def GF : List Formula :=
  (allowedProgs r₁ r₂ N R).flatMap fun u =>
    (allowedProgs r₁ r₂ N R).flatMap fun v => guardU u v

theorem mem_GF {u v : Prog} (hu : u ∈ allowedProgs r₁ r₂ N R)
    (hv : v ∈ allowedProgs r₁ r₂ N R) {ψ : Formula} (hψ : ψ ∈ guardU u v) :
    ψ ∈ GF r₁ r₂ N R := by
  simp only [GF, List.mem_flatMap]
  exact ⟨u, hu, v, hv, hψ⟩

/-- `.plays` arguments of guard-family members are again universe programs. -/
theorem GF_args (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true) :
    ∀ {ψ : Formula}, ψ ∈ GF r₁ r₂ N R →
    ∀ {P : Prog}, P ∈ playsArgsF ψ → P ∈ allowedProgs r₁ r₂ N R := by
  intro ψ hψ P hP
  simp only [GF, List.mem_flatMap] at hψ
  obtain ⟨u, hu, v, hv, hψ⟩ := hψ
  have hum := allowedProgs_modest r₁ r₂ N R h₁ h₂ hu
  have hvm := allowedProgs_modest r₁ r₂ N R h₁ h₂ hv
  have := guardU_args u v hum hvm hψ hP
  exact players_mem r₁ r₂ N R hu hv this

/-- Guard-family literals are bounded by the jump ceiling. -/
theorem GF_lit : ∀ {ψ : Formula}, ψ ∈ GF r₁ r₂ N R →
    maxLitF ψ ≤ LU r₁ r₂ N := by
  intro ψ hψ
  simp only [GF, List.mem_flatMap] at hψ
  obtain ⟨u, hu, v, hv, hψ⟩ := hψ
  simp only [guardU, List.mem_flatMap] at hψ
  obtain ⟨p, hp, hψ⟩ := hψ
  cases p with
  | search kg g pb qb =>
      simp only [List.mem_flatMap, List.mem_map] at hψ
      obtain ⟨u', hu', v', hv', rfl⟩ := hψ
      have hsub := maxLitF_subst u' v' g
      have hglit : maxLitF g ≤ LU r₁ r₂ N := by
        have hmem : Prog.search kg g pb qb ∈ allowedProgs r₁ r₂ N R :=
          certU_mem r₁ r₂ N R hu hv hp
        have := allowedProgs_lit r₁ r₂ N R hmem
        simp only [maxLitP] at this
        omega
      have hu'l : maxLitP u' ≤ LU r₁ r₂ N :=
        allowedProgs_lit r₁ r₂ N R (players_mem r₁ r₂ N R hu hv hu')
      have hv'l : maxLitP v' ≤ LU r₁ r₂ N :=
        allowedProgs_lit r₁ r₂ N R (players_mem r₁ r₂ N R hu hv hv')
      omega
  | const a => simp at hψ
  | self => simp at hψ
  | opp => simp at hψ
  | bot pb => simp at hψ
  | sim pb qb => simp at hψ
  | ite b a pb qb => simp at hψ

/-! ## 3. The T4.5 read interface, globalized. -/

/-- **Cert-read budget bound**: over universe triples, every oracle consultation is at
    budget `≤ max b LU` — refutation sweeps stay under the cert budget, guard cites are
    literals of universe programs. -/
theorem certRead_budget :
    ∀ {b : Nat} {me oppo body : Prog} {m : Nat} {ψ : Formula},
    CertRead b me oppo body m ψ →
    maxLitP me ≤ LU r₁ r₂ N → maxLitP oppo ≤ LU r₁ r₂ N →
    maxLitP body ≤ LU r₁ r₂ N →
    m ≤ max b (LU r₁ r₂ N) := by
  intro b me oppo body m ψ hr
  induction hr with
  | citeT =>
      intro _ _ hbody
      simp only [maxLitP] at hbody
      omega
  | citeF hm => intro _ _ _; omega
  | searchT _ ih =>
      intro hme hoppo hbody
      simp only [maxLitP] at hbody
      have := ih hme hoppo (by omega)
      omega
  | searchF hm' _ ih =>
      intro hme hoppo hbody
      simp only [maxLitP] at hbody
      have := ih hme hoppo (by omega)
      omega
  | selfR _ ih =>
      intro hme hoppo _
      have := ih hme hoppo hme
      omega
  | oppR _ ih =>
      intro hme hoppo _
      have := ih hme hoppo hoppo
      omega
  | botR _ ih =>
      intro hme hoppo hbody
      simp only [maxLitP] at hbody
      have := ih hme hoppo hbody
      omega
  | @simR _ me' oppo' p q _ _ _ ih =>
      intro hme hoppo hbody
      simp only [maxLitP] at hbody
      have hp := maxLitP_subst me' oppo' p
      have hq := maxLitP_subst me' oppo' q
      have := ih (by omega) (by omega) (by omega)
      omega
  | iteG hm' _ ih =>
      intro hme hoppo hbody
      simp only [maxLitP] at hbody
      have := ih hme hoppo (by omega)
      omega
  | iteP hm' _ ih =>
      intro hme hoppo hbody
      simp only [maxLitP] at hbody
      have := ih hme hoppo (by omega)
      omega
  | iteQ hm' _ ih =>
      intro hme hoppo hbody
      simp only [maxLitP] at hbody
      have := ih hme hoppo (by omega)
      omega

/-- **Cert-read formula containment, globalized**: over universe pairs, every consulted
    formula is a `GF` member or the `.neg` of one. -/
theorem certRead_mem_GF (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    {P Q : Prog} (hP : P ∈ allowedProgs r₁ r₂ N R) (hQ : Q ∈ allowedProgs r₁ r₂ N R)
    {b m : Nat} {ψ : Formula} (hr : CertRead b P Q P m ψ) :
    ψ ∈ GF r₁ r₂ N R ∨ ∃ ψ₀ ∈ GF r₁ r₂ N R, ψ = .neg ψ₀ := by
  have hPm := allowedProgs_modest r₁ r₂ N R h₁ h₂ hP
  have hQm := allowedProgs_modest r₁ r₂ N R h₁ h₂ hQ
  have := certRead_mem_guardU P Q hPm hQm hr
    (by simp [players]) (by simp [players])
    (players_subset_certU P Q (by simp [players]))
  rcases this with h | ⟨ψ₀, hψ₀, rfl⟩
  · exact Or.inl (mem_GF r₁ r₂ N R hP hQ h)
  · exact Or.inr ⟨ψ₀, mem_GF r₁ r₂ N R hP hQ hψ₀, rfl⟩

end Universe

end PD.T46
