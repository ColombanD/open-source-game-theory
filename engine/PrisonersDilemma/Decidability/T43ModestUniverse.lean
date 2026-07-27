import PrisonersDilemma.Program
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot

/-!
# T4.3 spike — the MODEST universe: the finite query space under substitution dynamics.

`DECIDABILITY_ROADMAP.md` T4.2 remaining pipeline (i). The T4.1a stabilization template
(`T4QueryBound.lean`) decides budget-jumping systems over a FINITE query space; the engine
obstacle to instantiating it on `ProvableB` (`T42PfB.lean`) is PROGRAM GROWTH: `eval`'s
`.sim` step and `.search` guard hop substitute the current players into subterms, and a
composite argument containing `.self` grows strictly under substitution — iterate and the
program universe is infinite.

**Modesty** is the syntactic condition that kills the growth: every position that
substitution can ever route a PLAYER through — `.sim` arguments and the program arguments of
`.plays` atoms in guard formulas — must be `.self`, `.opp`, or subst-FROZEN (`closedP`:
no exposed `.self`/`.opp`; a `.bot` body is frozen by `Prog.subst` itself). Then
substitution never manufactures a new program: `.sim` steps resolve their arguments to
`{me, oppo, the frozen argument}`, and a hopped guard's atoms resolve to the same. The whole
bot zoo is modest (examples at the bottom — `MirrorBot`, `DupocBot`, `PrudentBot`,
`PrudentBot2`, `JustBot`, …, all by `rfl`).

Shipped here (all by structural mutual recursion over `Prog`/`Formula`, no axioms beyond
the 3 standard):
  * `closedP`/`closedF` — subst-invariance; `substP_id`/`substF_id` (frozen ⇒ identity);
  * `modestP`/`modestF` — the modesty predicate (computable, `rfl`-checkable per bot);
  * `subsP`/`subsF` — the program subterm closure (descending through guard formulas),
    with `subsP_trans`/`subsF_trans` and `modestP_of_mem`/`modestF_of_mem`;
  * `playsArgsF` — the cert-relevant atom arguments of a formula (`.plays` only: `.eq`
    atoms never spawn evaluation queries), with `playsArgsF_subst`: the args of a
    substituted modest formula are `me`, `oppo`, or frozen args of the original;
  * the universe: `certU` (bodies) / `players` / `guardU` (hop formulas), all finite
    computable lists, and the STEP LEMMAS:
      - `step_sim`      — `.sim` steps keep players in `players`;
      - `step_search`   — guard hops land in `guardU`;
      - `guardU_args`   — `.plays` args of `guardU` members are in `players`
    i.e. **the modest query space is finite and closed under the evaluation dynamics** —
    exactly the `T4QueryBound` in-space closure, now for real engine programs.

What remains for pipeline (i), now mechanical in principle: the two-sided step operator for
`ProvableB` over `(budgets ≤ max k N) × (enumFormula-with-gate ∪ guardU-subformulas) ×
(players × players × certU)`, then the T4.1a lfp-stabilization verbatim. The budget side is
already covered by T4.2's literal gates (hop targets are source literals ≤ N).
-/

namespace PD.T43
open PD

/-! ## 1. Subst-invariance (`closedP`) and the frozen-identity lemmas. -/

mutual
  /-- No exposed `.self`/`.opp`: `Prog.subst` is the identity on these. NOTE `.bot p` is
      closed REGARDLESS of `p` — `subst` does not descend into a `.bot` (frozen reference);
      likewise `.diag` and the RHS of `.eq` on the formula side. -/
  def closedP : Prog → Bool
    | .const _ => true
    | .self => false
    | .opp => false
    | .bot _ => true
    | .sim p q => closedP p && closedP q
    | .ite b _ p q => closedP b && closedP p && closedP q
    | .search _ φ p q => closedF φ && closedP p && closedP q

  def closedF : Formula → Bool
    | .plays p q _ => closedP p && closedP q
    | .impl φ ψ => closedF φ && closedF ψ
    | .neg φ => closedF φ
    | .box _ φ => closedF φ
    | .eq p _ => closedP p
    | .diag _ _ => true
end

mutual
  theorem substP_id (m o : Prog) : ∀ (p : Prog), closedP p = true → p.subst m o = p := by
    intro p
    cases p with
    | const a => intro _; rfl
    | self => intro h; simp [closedP] at h
    | opp => intro h; simp [closedP] at h
    | bot p => intro _; rfl
    | sim p q =>
        intro h
        simp only [closedP, Bool.and_eq_true] at h
        show Prog.sim (p.subst m o) (q.subst m o) = Prog.sim p q
        rw [substP_id m o p h.1, substP_id m o q h.2]
    | ite b a p q =>
        intro h
        simp only [closedP, Bool.and_eq_true] at h
        show Prog.ite (b.subst m o) a (p.subst m o) (q.subst m o) = Prog.ite b a p q
        rw [substP_id m o b h.1.1, substP_id m o p h.1.2, substP_id m o q h.2]
    | search k φ p q =>
        intro h
        simp only [closedP, Bool.and_eq_true] at h
        show Prog.search k (φ.subst m o) (p.subst m o) (q.subst m o) = Prog.search k φ p q
        rw [substF_id m o φ h.1.1, substP_id m o p h.1.2, substP_id m o q h.2]

  theorem substF_id (m o : Prog) : ∀ (φ : Formula), closedF φ = true → φ.subst m o = φ := by
    intro φ
    cases φ with
    | plays p q a =>
        intro h
        simp only [closedF, Bool.and_eq_true] at h
        show Formula.plays (p.subst m o) (q.subst m o) a = Formula.plays p q a
        rw [substP_id m o p h.1, substP_id m o q h.2]
    | impl φ ψ =>
        intro h
        simp only [closedF, Bool.and_eq_true] at h
        show Formula.impl (φ.subst m o) (ψ.subst m o) = Formula.impl φ ψ
        rw [substF_id m o φ h.1, substF_id m o ψ h.2]
    | neg φ =>
        intro h
        simp only [closedF] at h
        show Formula.neg (φ.subst m o) = Formula.neg φ
        rw [substF_id m o φ h]
    | box n φ =>
        intro h
        simp only [closedF] at h
        show Formula.box n (φ.subst m o) = Formula.box n φ
        rw [substF_id m o φ h]
    | eq p q =>
        intro h
        simp only [closedF] at h
        show Formula.eq (p.subst m o) q = Formula.eq p q
        rw [substP_id m o p h]
    | diag g φ => intro _; rfl
end

/-! ## 2. Modesty. -/

/-- A substitution-position argument is admissible: it resolves under `subst` to a player
    or to itself. -/
def argOK (p : Prog) : Bool := p == .self || p == .opp || closedP p

theorem argOK_subst {p : Prog} (h : argOK p = true) (m o : Prog) :
    p.subst m o = m ∨ p.subst m o = o ∨ (p.subst m o = p ∧ closedP p = true) := by
  simp only [argOK, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨substP_id m o p h, h⟩)

mutual
  /-- Every substitution-reachable position is `argOK`: `.sim` arguments, and the `.plays`
      atom arguments of guard formulas. Everything else just recurses. -/
  def modestP : Prog → Bool
    | .const _ => true
    | .self => true
    | .opp => true
    | .bot p => modestP p
    | .sim p q => argOK p && argOK q && modestP p && modestP q
    | .ite b _ p q => modestP b && modestP p && modestP q
    | .search _ φ p q => modestF φ && modestP p && modestP q

  def modestF : Formula → Bool
    | .plays p q _ => argOK p && argOK q && modestP p && modestP q
    | .impl φ ψ => modestF φ && modestF ψ
    | .neg φ => modestF φ
    | .box _ φ => modestF φ
    | .eq p q => argOK p && modestP p && modestP q
    | .diag _ φ => modestF φ
end

/-! ## 3. The subterm closure (through guard formulas). -/

mutual
  def subsP : Prog → List Prog
    | .const a => [.const a]
    | .self => [.self]
    | .opp => [.opp]
    | .bot p => .bot p :: subsP p
    | .sim p q => .sim p q :: (subsP p ++ subsP q)
    | .ite b a p q => .ite b a p q :: (subsP b ++ subsP p ++ subsP q)
    | .search k φ p q => .search k φ p q :: (subsF φ ++ subsP p ++ subsP q)

  def subsF : Formula → List Prog
    | .plays p q _ => subsP p ++ subsP q
    | .impl φ ψ => subsF φ ++ subsF ψ
    | .neg φ => subsF φ
    | .box _ φ => subsF φ
    | .eq p q => subsP p ++ subsP q
    | .diag _ φ => subsF φ
end

theorem mem_subsP_self : ∀ p : Prog, p ∈ subsP p := by
  intro p; cases p <;> simp [subsP]

mutual
  theorem subsP_trans : ∀ (p q : Prog), q ∈ subsP p →
      ∀ (r : Prog), r ∈ subsP q → r ∈ subsP p := by
    intro p
    cases p with
    | const a =>
        intro q hq r hr
        simp only [subsP, List.mem_singleton] at hq
        subst hq; exact hr
    | self =>
        intro q hq r hr
        simp only [subsP, List.mem_singleton] at hq
        subst hq; exact hr
    | opp =>
        intro q hq r hr
        simp only [subsP, List.mem_singleton] at hq
        subst hq; exact hr
    | bot p =>
        intro q hq r hr
        simp only [subsP, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hr
        · exact List.mem_cons_of_mem _ (subsP_trans p q hq r hr)
    | sim p₁ p₂ =>
        intro q hq r hr
        simp only [subsP, List.mem_cons, List.mem_append] at hq
        rcases hq with rfl | hq | hq
        · exact hr
        · exact List.mem_cons_of_mem _
            (List.mem_append_left _ (subsP_trans p₁ q hq r hr))
        · exact List.mem_cons_of_mem _
            (List.mem_append_right _ (subsP_trans p₂ q hq r hr))
    | ite b a p₁ p₂ =>
        intro q hq r hr
        simp only [subsP, List.mem_cons, List.mem_append] at hq
        rcases hq with rfl | (hq | hq) | hq
        · exact hr
        · exact List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_append_left _ (subsP_trans b q hq r hr)))
        · exact List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_append_right _ (subsP_trans p₁ q hq r hr)))
        · exact List.mem_cons_of_mem _
            (List.mem_append_right _ (subsP_trans p₂ q hq r hr))
    | search k φ p₁ p₂ =>
        intro q hq r hr
        simp only [subsP, List.mem_cons, List.mem_append] at hq
        rcases hq with rfl | (hq | hq) | hq
        · exact hr
        · exact List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_append_left _ (subsF_trans φ q hq r hr)))
        · exact List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_append_right _ (subsP_trans p₁ q hq r hr)))
        · exact List.mem_cons_of_mem _
            (List.mem_append_right _ (subsP_trans p₂ q hq r hr))

  theorem subsF_trans : ∀ (φ : Formula) (q : Prog), q ∈ subsF φ →
      ∀ (r : Prog), r ∈ subsP q → r ∈ subsF φ := by
    intro φ
    cases φ with
    | plays p₁ p₂ a =>
        intro q hq r hr
        simp only [subsF, List.mem_append] at hq
        rcases hq with hq | hq
        · exact List.mem_append_left _ (subsP_trans p₁ q hq r hr)
        · exact List.mem_append_right _ (subsP_trans p₂ q hq r hr)
    | impl φ ψ =>
        intro q hq r hr
        simp only [subsF, List.mem_append] at hq
        rcases hq with hq | hq
        · exact List.mem_append_left _ (subsF_trans φ q hq r hr)
        · exact List.mem_append_right _ (subsF_trans ψ q hq r hr)
    | neg φ =>
        intro q hq r hr
        exact subsF_trans φ q hq r hr
    | box n φ =>
        intro q hq r hr
        exact subsF_trans φ q hq r hr
    | eq p₁ p₂ =>
        intro q hq r hr
        simp only [subsF, List.mem_append] at hq
        rcases hq with hq | hq
        · exact List.mem_append_left _ (subsP_trans p₁ q hq r hr)
        · exact List.mem_append_right _ (subsP_trans p₂ q hq r hr)
    | diag g φ =>
        intro q hq r hr
        exact subsF_trans φ q hq r hr
end

mutual
  theorem modestP_of_mem : ∀ (p : Prog), modestP p = true →
      ∀ (q : Prog), q ∈ subsP p → modestP q = true := by
    intro p
    cases p with
    | const a =>
        intro h q hq
        simp only [subsP, List.mem_singleton] at hq
        subst hq; exact h
    | self =>
        intro h q hq
        simp only [subsP, List.mem_singleton] at hq
        subst hq; exact h
    | opp =>
        intro h q hq
        simp only [subsP, List.mem_singleton] at hq
        subst hq; exact h
    | bot p =>
        intro h q hq
        simp only [modestP] at h
        simp only [subsP, List.mem_cons] at hq
        rcases hq with rfl | hq
        · simpa [modestP] using h
        · exact modestP_of_mem p h q hq
    | sim p₁ p₂ =>
        intro h q hq
        simp only [modestP, Bool.and_eq_true] at h
        simp only [subsP, List.mem_cons, List.mem_append] at hq
        rcases hq with rfl | hq | hq
        · simp only [modestP, Bool.and_eq_true]; exact h
        · exact modestP_of_mem p₁ h.1.2 q hq
        · exact modestP_of_mem p₂ h.2 q hq
    | ite b a p₁ p₂ =>
        intro h q hq
        simp only [modestP, Bool.and_eq_true] at h
        simp only [subsP, List.mem_cons, List.mem_append] at hq
        rcases hq with rfl | (hq | hq) | hq
        · simp only [modestP, Bool.and_eq_true]; exact h
        · exact modestP_of_mem b h.1.1 q hq
        · exact modestP_of_mem p₁ h.1.2 q hq
        · exact modestP_of_mem p₂ h.2 q hq
    | search k φ p₁ p₂ =>
        intro h q hq
        simp only [modestP, Bool.and_eq_true] at h
        simp only [subsP, List.mem_cons, List.mem_append] at hq
        rcases hq with rfl | (hq | hq) | hq
        · simp only [modestP, Bool.and_eq_true]; exact h
        · exact modestF_of_mem φ h.1.1 q hq
        · exact modestP_of_mem p₁ h.1.2 q hq
        · exact modestP_of_mem p₂ h.2 q hq

  theorem modestF_of_mem : ∀ (φ : Formula), modestF φ = true →
      ∀ (q : Prog), q ∈ subsF φ → modestP q = true := by
    intro φ
    cases φ with
    | plays p₁ p₂ a =>
        intro h q hq
        simp only [modestF, Bool.and_eq_true] at h
        simp only [subsF, List.mem_append] at hq
        rcases hq with hq | hq
        · exact modestP_of_mem p₁ h.1.2 q hq
        · exact modestP_of_mem p₂ h.2 q hq
    | impl φ ψ =>
        intro h q hq
        simp only [modestF, Bool.and_eq_true] at h
        simp only [subsF, List.mem_append] at hq
        rcases hq with hq | hq
        · exact modestF_of_mem φ h.1 q hq
        · exact modestF_of_mem ψ h.2 q hq
    | neg φ =>
        intro h q hq
        simp only [modestF] at h
        exact modestF_of_mem φ h q hq
    | box n φ =>
        intro h q hq
        simp only [modestF] at h
        exact modestF_of_mem φ h q hq
    | eq p₁ p₂ =>
        intro h q hq
        simp only [modestF, Bool.and_eq_true] at h
        simp only [subsF, List.mem_append] at hq
        rcases hq with hq | hq
        · exact modestP_of_mem p₁ h.1.2 q hq
        · exact modestP_of_mem p₂ h.2 q hq
    | diag g φ =>
        intro h q hq
        simp only [modestF] at h
        exact modestF_of_mem φ h q hq
end

/-! ## 4. The cert-relevant atom arguments and their behavior under substitution. -/

/-- The program arguments of `.plays` atoms — the positions that spawn evaluation (cert)
    queries. `.eq` atoms are handled by structural comparison (`eqRefl`/`eqNeg`), never
    evaluated, so they are NOT collected. -/
def playsArgsF : Formula → List Prog
  | .plays p q _ => [p, q]
  | .impl φ ψ => playsArgsF φ ++ playsArgsF ψ
  | .neg φ => playsArgsF φ
  | .box _ φ => playsArgsF φ
  | .eq _ _ => []
  | .diag _ _ => []   -- frozen under subst AND meta-only (never in bot source): not collected

theorem playsArgsF_subset_subsF : ∀ (φ : Formula) (P : Prog),
    P ∈ playsArgsF φ → P ∈ subsF φ := by
  intro φ
  refine Formula.rec (motive_1 := fun _ => True)
    (motive_2 := fun φ => ∀ P, P ∈ playsArgsF φ → P ∈ subsF φ)
    ?const ?self ?opp ?bot ?sim ?ite ?search ?plays ?impl ?neg ?box ?eq ?diag φ
  case const => intro _; trivial
  case self => trivial
  case opp => trivial
  case bot => intro _ _; trivial
  case sim => intro _ _ _ _; trivial
  case ite => intro _ _ _ _ _ _ _; trivial
  case search => intro _ _ _ _ _ _ _; trivial
  case plays =>
      intro p q a _ _ P hP
      simp only [playsArgsF, List.mem_cons,
        List.not_mem_nil, or_false] at hP
      simp only [subsF, List.mem_append]
      rcases hP with rfl | rfl
      · exact Or.inl (mem_subsP_self P)
      · exact Or.inr (mem_subsP_self P)
  case impl =>
      intro φ ψ ihφ ihψ P hP
      simp only [playsArgsF, List.mem_append] at hP
      simp only [subsF, List.mem_append]
      rcases hP with hP | hP
      · exact Or.inl (ihφ P hP)
      · exact Or.inr (ihψ P hP)
  case neg => intro φ ih P hP; exact ih P hP
  case box => intro n φ ih P hP; exact ih P hP
  case eq => intro p q _ _ P hP; simp [playsArgsF] at hP
  case diag => intro g φ _ P hP; simp [playsArgsF] at hP

/-- **Substituted modest atoms resolve to the players or to frozen originals.** -/
theorem playsArgsF_subst (m o : Prog) : ∀ (φ : Formula), modestF φ = true →
    ∀ (P : Prog), P ∈ playsArgsF (φ.subst m o) →
      P = m ∨ P = o ∨ (P ∈ playsArgsF φ ∧ closedP P = true) := by
  intro φ
  refine Formula.rec (motive_1 := fun _ => True)
    (motive_2 := fun φ => modestF φ = true → ∀ P, P ∈ playsArgsF (φ.subst m o) →
      P = m ∨ P = o ∨ (P ∈ playsArgsF φ ∧ closedP P = true))
    ?const ?self ?opp ?bot ?sim ?ite ?search ?plays ?impl ?neg ?box ?eq ?diag φ
  case const => intro _; trivial
  case self => trivial
  case opp => trivial
  case bot => intro _ _; trivial
  case sim => intro _ _ _ _; trivial
  case ite => intro _ _ _ _ _ _ _; trivial
  case search => intro _ _ _ _ _ _ _; trivial
  case plays =>
      intro p q a _ _ h P hP
      simp only [modestF, Bool.and_eq_true] at h
      simp only [Formula.subst, playsArgsF, List.mem_cons,
        List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · rcases argOK_subst h.1.1.1 m o with h' | h' | ⟨h', hc⟩
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · refine Or.inr (Or.inr ⟨?_, by rw [h']; exact hc⟩)
          rw [h']; simp [playsArgsF]
      · rcases argOK_subst h.1.1.2 m o with h' | h' | ⟨h', hc⟩
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · refine Or.inr (Or.inr ⟨?_, by rw [h']; exact hc⟩)
          rw [h']; simp [playsArgsF]
  case impl =>
      intro φ ψ ihφ ihψ h P hP
      simp only [modestF, Bool.and_eq_true] at h
      simp only [Formula.subst, playsArgsF, List.mem_append] at hP
      rcases hP with hP | hP
      · rcases ihφ h.1 P hP with h' | h' | ⟨h', hc⟩
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · refine Or.inr (Or.inr ⟨?_, hc⟩)
          simp only [playsArgsF, List.mem_append]
          exact Or.inl h'
      · rcases ihψ h.2 P hP with h' | h' | ⟨h', hc⟩
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · refine Or.inr (Or.inr ⟨?_, hc⟩)
          simp only [playsArgsF, List.mem_append]
          exact Or.inr h'
  case neg =>
      intro φ ih h P hP
      simp only [modestF] at h
      simp only [Formula.subst, playsArgsF] at hP
      exact ih h P hP
  case box =>
      intro n φ ih h P hP
      simp only [modestF] at h
      simp only [Formula.subst, playsArgsF] at hP
      exact ih h P hP
  case eq =>
      intro p q _ _ _ P hP
      simp only [Formula.subst, playsArgsF] at hP
      cases hP
  case diag =>
      intro g φ _ _ P hP
      simp only [Formula.subst, playsArgsF] at hP
      cases hP

/-! ## 5. The universe, and the step-closure lemmas. -/

section Universe

variable (r₁ r₂ : Prog)

/-- The body universe: subterm closure of both roots. Finite by construction. -/
def certU : List Prog := subsP r₁ ++ subsP r₂

/-- The player universe: the roots and every frozen subterm. -/
def players : List Prog := r₁ :: r₂ :: (certU r₁ r₂).filter closedP

/-- The hop-formula universe: every `.search` guard in the closure, substituted by every
    player pair. Finite by construction. -/
def guardU : List Formula :=
  (certU r₁ r₂).flatMap fun p =>
    match p with
    | .search _ g _ _ =>
        (players r₁ r₂).flatMap fun u => (players r₁ r₂).map fun v => g.subst u v
    | _ => []

theorem players_subset_certU : ∀ {p : Prog}, p ∈ players r₁ r₂ → p ∈ certU r₁ r₂ := by
  intro p hp
  simp only [players, List.mem_cons] at hp
  rcases hp with rfl | rfl | hp
  · exact List.mem_append_left _ (mem_subsP_self p)
  · exact List.mem_append_right _ (mem_subsP_self p)
  · exact (List.mem_filter.mp hp).1

theorem certU_trans : ∀ {p : Prog}, p ∈ certU r₁ r₂ →
    ∀ {q : Prog}, q ∈ subsP p → q ∈ certU r₁ r₂ := by
  intro p hp q hq
  simp only [certU, List.mem_append] at hp ⊢
  rcases hp with hp | hp
  · exact Or.inl (subsP_trans r₁ p hp q hq)
  · exact Or.inr (subsP_trans r₂ p hp q hq)

theorem certU_modest (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true) :
    ∀ {p : Prog}, p ∈ certU r₁ r₂ → modestP p = true := by
  intro p hp
  simp only [certU, List.mem_append] at hp
  rcases hp with hp | hp
  · exact modestP_of_mem r₁ h₁ p hp
  · exact modestP_of_mem r₂ h₂ p hp

/-- **Step lemma (`.sim`)**: for a modest universe, the substituted `.sim` arguments —
    `eval`'s new players AND new body — are again players. -/
theorem step_sim (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    {me oppo : Prog} (hme : me ∈ players r₁ r₂) (hoppo : oppo ∈ players r₁ r₂)
    {p q : Prog} (hbody : Prog.sim p q ∈ certU r₁ r₂) :
    p.subst me oppo ∈ players r₁ r₂ ∧ q.subst me oppo ∈ players r₁ r₂ := by
  have hmod : modestP (Prog.sim p q) = true := certU_modest r₁ r₂ h₁ h₂ hbody
  simp only [modestP, Bool.and_eq_true] at hmod
  have hsubp : p ∈ subsP (Prog.sim p q) := by
    simp [subsP, List.mem_cons, List.mem_append, mem_subsP_self p]
  have hsubq : q ∈ subsP (Prog.sim p q) := by
    simp [subsP, List.mem_cons, List.mem_append, mem_subsP_self q]
  constructor
  · rcases argOK_subst hmod.1.1.1 me oppo with h' | h' | ⟨h', hc⟩
    · rw [h']; exact hme
    · rw [h']; exact hoppo
    · rw [h']
      simp only [players, List.mem_cons]
      exact Or.inr (Or.inr (List.mem_filter.mpr ⟨certU_trans r₁ r₂ hbody hsubp, hc⟩))
  · rcases argOK_subst hmod.1.1.2 me oppo with h' | h' | ⟨h', hc⟩
    · rw [h']; exact hme
    · rw [h']; exact hoppo
    · rw [h']
      simp only [players, List.mem_cons]
      exact Or.inr (Or.inr (List.mem_filter.mpr ⟨certU_trans r₁ r₂ hbody hsubq, hc⟩))

/-- **Step lemma (`.search`)**: the hop formula lands in the finite guard universe. -/
theorem step_search {me oppo : Prog} (hme : me ∈ players r₁ r₂)
    (hoppo : oppo ∈ players r₁ r₂)
    {k : Nat} {g : Formula} {p q : Prog}
    (hbody : Prog.search k g p q ∈ certU r₁ r₂) :
    g.subst me oppo ∈ guardU r₁ r₂ := by
  simp only [guardU, List.mem_flatMap]
  refine ⟨Prog.search k g p q, hbody, ?_⟩
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨me, hme, oppo, hoppo, rfl⟩

/-- **Entry lemma**: the `.plays` arguments of any hop formula are players — so the cert
    queries a hop spawns stay inside `players × players × certU`. The space is CLOSED. -/
theorem guardU_args (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true) :
    ∀ {φ : Formula}, φ ∈ guardU r₁ r₂ →
    ∀ {P : Prog}, P ∈ playsArgsF φ → P ∈ players r₁ r₂ := by
  intro φ hφ P hP
  simp only [guardU, List.mem_flatMap] at hφ
  obtain ⟨p, hp, hφ⟩ := hφ
  cases p with
  | search k g pb qb =>
      simp only [List.mem_flatMap, List.mem_map] at hφ
      obtain ⟨u, hu, v, hv, rfl⟩ := hφ
      have hmod : modestP (Prog.search k g pb qb) = true := certU_modest r₁ r₂ h₁ h₂ hp
      simp only [modestP, Bool.and_eq_true] at hmod
      rcases playsArgsF_subst u v g hmod.1.1 P hP with rfl | rfl | ⟨hPg, hc⟩
      · exact hu
      · exact hv
      -- frozen original arg: it is a subterm of the guard, hence of the `.search`
      -- member, hence of a root — and closed, so a player.
      · have hPsub : P ∈ subsF g := playsArgsF_subset_subsF g P hPg
        have hPsearch : P ∈ subsP (Prog.search k g pb qb) := by
          simp only [subsP, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inl (Or.inl hPsub))
        simp only [players, List.mem_cons]
        exact Or.inr (Or.inr (List.mem_filter.mpr
          ⟨certU_trans r₁ r₂ hp hPsearch, hc⟩))
  | const a => simp at hφ
  | self => simp at hφ
  | opp => simp at hφ
  | bot pb => simp at hφ
  | sim pb qb => simp at hφ
  | ite b a pb qb => simp at hφ

end Universe

/-! ## 6. The whole zoo is modest (and so are the LLM generations). -/

open PD.Bots in
example : modestP CooperateBot = true := by rfl
open PD.Bots in
example : modestP DefectBot = true := by rfl
open PD.Bots in
example : modestP MirrorBot = true := by rfl
open PD.Bots in
example (k : Nat) : modestP (DupocBot k) = true := by rfl
open PD.Bots in
example (k : Nat) : modestP (CupodBot k) = true := by rfl
open PD.Bots in
example : modestP TitForTatBot = true := by rfl
open PD.Bots in
example (k : Nat) : modestP (PrudentBot k) = true := by rfl
open PD.Bots in
example (kOut kIn : Nat) : modestP (PrudentBot2 kOut kIn) = true := by rfl
open PD.Bots in
example (k : Nat) : modestP (JustBot k) = true := by rfl

end PD.T43
