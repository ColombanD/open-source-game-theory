import PrisonersDilemma.Research.Spikes.transcript.T52DecInst

/-! # T53 — STABILIZATION AT THE INSTANCE GATE: `Decidable (ProvableG (instGate P N))`.

T47's finite query space (`SL`/`InvP`/`ZS`) is GATE-FREE and reused verbatim; the
canonical pool is `players r₁ r₂ ⊆ AP`. New content: the instance read-classification
(`enumArg_mem_inst` — instance-gated cuts' args re-enter the universe: frames are
self/opp, closed-RAW-modest (the tightened `argOKP`), or players), then the `stepG`
congruence at `instOKb`, the countP stabilization, and the `Decidable` payoff. -/

namespace PD.T53
open PD PD.BaseTheorems PD.T31 PD.T42 PD.T43 PD.T44 PD.T45 PD.T46 PD.T47
open PD.T50 PD.T52

variable (r₁ r₂ : Prog) (N k₀ : Nat) (φ₀ : Formula)

/-- The canonical pool for the instance gate. -/
abbrev PP : List Prog := T43.players r₁ r₂

/-- Players live in the program universe. -/
theorem players_sub_AP : ∀ {p : Prog}, p ∈ PP r₁ r₂ → p ∈ AP r₁ r₂ N k₀ φ₀ := by
  intro p hp
  simp only [PP, T43.players, List.mem_cons] at hp
  rcases hp with rfl | rfl | hp
  · simp only [AP, allowedProgs, List.mem_flatMap]
    exact ⟨p, by simp [baseProgs], mem_subsP_self _⟩
  · simp only [AP, allowedProgs, List.mem_flatMap]
    exact ⟨p, by simp [baseProgs], mem_subsP_self _⟩
  · have hc := (List.mem_filter.mp hp).1
    simp only [T43.certU, List.mem_append] at hc
    simp only [AP, allowedProgs, List.mem_flatMap]
    rcases hc with hc | hc
    · exact ⟨r₁, by simp [baseProgs], hc⟩
    · exact ⟨r₂, by simp [baseProgs], hc⟩

/-- Atom args of instance-modest formulas are admissible and instance-modest. -/
theorem playsArgs_instModest (P : List Prog) : ∀ (φ : Formula),
    instModestF P φ = true →
    ∀ q ∈ playsArgsF φ, argOKP P q = true ∧ instModestP P q = true := by
  intro φ
  refine Formula.rec (motive_1 := fun _ => True)
    (motive_2 := fun φ => instModestF P φ = true →
      ∀ q ∈ playsArgsF φ, argOKP P q = true ∧ instModestP P q = true)
    ?const ?self ?opp ?bot ?sim ?ite ?search ?plays ?impl ?neg ?box ?eq ?diag φ
  case const => intro _; trivial
  case self => trivial
  case opp => trivial
  case bot => intro _ _; trivial
  case sim => intro _ _ _ _; trivial
  case ite => intro _ _ _ _ _ _ _; trivial
  case search => intro _ _ _ _ _ _ _; trivial
  case plays =>
      intro p q a _ _ h P' hP'
      simp only [instModestF, Bool.and_eq_true] at h
      simp only [playsArgsF, List.mem_cons, List.not_mem_nil, or_false] at hP'
      rcases hP' with rfl | rfl
      · exact ⟨h.1.1.1, h.1.2⟩
      · exact ⟨h.1.1.2, h.2⟩
  case impl =>
      intro φ ψ ihφ ihψ h P' hP'
      simp only [instModestF, Bool.and_eq_true] at h
      simp only [playsArgsF, List.mem_append] at hP'
      rcases hP' with hP' | hP'
      · exact ihφ h.1 P' hP'
      · exact ihψ h.2 P' hP'
  case neg => intro φ ih h P' hP'; exact ih h P' hP'
  case box => intro n φ ih h P' hP'; exact ih h P' hP'
  case eq =>
      intro p q _ _ h P' hP'
      simp [playsArgsF] at hP'
  case diag =>
      intro g φ ih h P' hP'
      simp [playsArgsF] at hP'

/-- **The instance read-classification**: every atom arg of an instance-gated enum
    formula is a universe program. -/
theorem enumArg_mem_inst {K : Nat} (hK : K ≤ RR r₁ r₂ N k₀ φ₀) {ψ' : Formula}
    (hmem : ψ' ∈ enumFormula K) (hgate : instOKb (PP r₁ r₂) N ψ' = true) :
    ∀ {q : Prog}, q ∈ playsArgsF ψ' → q ∈ AP r₁ r₂ N k₀ φ₀ := by
  intro q hq
  have hgate' := instOKb_iff.mp hgate
  obtain ⟨hargOK, hqmod⟩ := playsArgs_instModest (PP r₁ r₂) ψ' hgate'.2 q hq
  have hsubs : q ∈ subsF ψ' := playsArgsF_subset_subsF ψ' q hq
  simp only [argOKP, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hargOK
  rcases hargOK with ((rfl | rfl) | ⟨hclosed, hmodest⟩) | hmemP
  · simp only [AP, allowedProgs, List.mem_flatMap]
    exact ⟨.self, by simp [baseProgs], mem_subsP_self _⟩
  · simp only [AP, allowedProgs, List.mem_flatMap]
    exact ⟨.opp, by simp [baseProgs], mem_subsP_self _⟩
  · have hqsz : q.size ≤ SB r₁ r₂ N k₀ φ₀ := by
      have h1 := sizeF_of_mem ψ' q hsubs
      have h2 := le_EB hmem
      have h3 := EB_le_EBR r₁ r₂ N k₀ φ₀ hK
      simp only [SB]; omega
    have hqlit : maxLitP q ≤ N := by
      have h1 := maxLitF_of_mem ψ' q hsubs
      have h2 := hgate'.1
      omega
    simp only [AP, allowedProgs, List.mem_flatMap]
    refine ⟨q, ?_, mem_subsP_self q⟩
    simp only [baseProgs, List.mem_cons]
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(enum_complete _).1 q hqsz, ⟨hclosed, hmodest⟩, hqlit⟩
  · exact players_sub_AP r₁ r₂ N k₀ φ₀ (by simpa using hmemP)

end PD.T53
