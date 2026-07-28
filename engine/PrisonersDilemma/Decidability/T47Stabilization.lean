import PrisonersDilemma.Decidability.T44BoundedDecider
import PrisonersDilemma.Decidability.T46LogicSpace

/-!
# T4.7 spike — the STABILIZATION space (T4.4c part 2b, chunk 1: the space).

`DECIDABILITY_ROADMAP.md` T4.4c finale. Builds the finite query space `SL` for `stepB`'s
least-fixpoint stabilization:

  * `foldMax`/`le_foldMax` — fold-based size ceilings (no structural enumeration bounds
    needed: members of `enumFormula b` are bounded by the fold OVER THE LIST ITSELF,
    `EB b`);
  * `sizeP_of_mem`/`sizeF_of_mem` — subterm sizes never exceed the whole;
  * the ceilings: `LL` (literals), `RR` (budgets — non-circular, T4.6), `EBR` (enum
    member sizes across all budgets), `SB` (program universe ceiling);
  * the size stratification `ZS b := Z₀ + (RR − b) · (EBR + RR + 3)`: reads at strictly
    smaller budgets get enough headroom for one cut-composite (`≤ EBR + 2`) or one
    boxed premise (`≤ RR + 3`); the guard family `GFall` fits at EVERY budget (`≤ Z₀`);
  * the invariant `InvP` (atom args in the universe, literals `≤ LL`), the space list
    `SL`, and the read-classification lemmas (`GFall_mem_SL`, `enumArg_mem` — gated cut
    formulas' arguments re-enter the universe).

Chunks 2–3 (same file, appended): the 16-checker `stepB` congruence over `SL`, the countP
stabilization, and the `Decidable` payoff.
-/

namespace PD.T47
open PD PD.BaseTheorems PD.T31 PD.T42 PD.T43 PD.T44 PD.T45 PD.T46

/-! ## 1. Fold ceilings and subterm sizes. -/

def foldMax {α : Type} (f : α → Nat) (l : List α) : Nat :=
  l.foldr (fun x acc => max (f x) acc) 0

theorem le_foldMax {α : Type} (f : α → Nat) : ∀ {l : List α} {x : α}, x ∈ l →
    f x ≤ foldMax f l := by
  intro l
  induction l with
  | nil => intro x hx; cases hx
  | cons a t ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxt
      · simp only [foldMax, List.foldr]; omega
      · have := ih hxt
        simp only [foldMax, List.foldr] at this ⊢
        omega

mutual
  theorem sizeP_of_mem : ∀ (p q : Prog), q ∈ subsP p → q.size ≤ p.size := by
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
        · have := sizeP_of_mem p q hq
          simp only [Prog.size]; omega
    | sim p₁ p₂ =>
        intro q hq
        simp only [subsP, List.mem_cons, List.mem_append] at hq
        rcases hq with rfl | hq | hq
        · exact Nat.le_refl _
        · have := sizeP_of_mem p₁ q hq
          simp only [Prog.size]; omega
        · have := sizeP_of_mem p₂ q hq
          simp only [Prog.size]; omega
    | ite b a p₁ p₂ =>
        intro q hq
        simp only [subsP, List.mem_cons, List.mem_append] at hq
        rcases hq with rfl | (hq | hq) | hq
        · exact Nat.le_refl _
        · have := sizeP_of_mem b q hq
          simp only [Prog.size]; omega
        · have := sizeP_of_mem p₁ q hq
          simp only [Prog.size]; omega
        · have := sizeP_of_mem p₂ q hq
          simp only [Prog.size]; omega
    | search k φ p₁ p₂ =>
        intro q hq
        simp only [subsP, List.mem_cons, List.mem_append] at hq
        rcases hq with rfl | (hq | hq) | hq
        · exact Nat.le_refl _
        · have := sizeF_of_mem φ q hq
          simp only [numCost, Prog.size]; omega
        · have := sizeP_of_mem p₁ q hq
          simp only [numCost, Prog.size]; omega
        · have := sizeP_of_mem p₂ q hq
          simp only [numCost, Prog.size]; omega

  theorem sizeF_of_mem : ∀ (φ : Formula) (q : Prog), q ∈ subsF φ → q.size ≤ φ.size := by
    intro φ
    cases φ with
    | plays p₁ p₂ a =>
        intro q hq
        simp only [subsF, List.mem_append] at hq
        rcases hq with hq | hq
        · have := sizeP_of_mem p₁ q hq
          simp only [Formula.size]; omega
        · have := sizeP_of_mem p₂ q hq
          simp only [Formula.size]; omega
    | impl φ ψ =>
        intro q hq
        simp only [subsF, List.mem_append] at hq
        rcases hq with hq | hq
        · have := sizeF_of_mem φ q hq
          simp only [Formula.size]; omega
        · have := sizeF_of_mem ψ q hq
          simp only [Formula.size]; omega
    | neg φ =>
        intro q hq
        have := sizeF_of_mem φ q hq
        simp only [Formula.size]; omega
    | box n φ =>
        intro q hq
        have := sizeF_of_mem φ q hq
        simp only [numCost, Formula.size]; omega
    | eq p₁ p₂ =>
        intro q hq
        simp only [subsF, List.mem_append] at hq
        rcases hq with hq | hq
        · have := sizeP_of_mem p₁ q hq
          simp only [Formula.size]; omega
        · have := sizeP_of_mem p₂ q hq
          simp only [Formula.size]; omega
    | diag g φ =>
        intro q hq
        have := sizeF_of_mem φ q hq
        simp only [numCost, Formula.size]; omega
end

/-- Gated atoms' arguments are `argOK` and modest (recursive collection of `modestF`'s
    per-atom data). -/
theorem playsArgs_modest : ∀ (φ : Formula), modestF φ = true →
    ∀ P ∈ playsArgsF φ, argOK P = true ∧ modestP P = true := by
  intro φ
  refine Formula.rec (motive_1 := fun _ => True)
    (motive_2 := fun φ => modestF φ = true →
      ∀ P ∈ playsArgsF φ, argOK P = true ∧ modestP P = true)
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
      simp only [playsArgsF, List.mem_cons, List.not_mem_nil,
        or_false] at hP
      rcases hP with rfl | rfl
      · exact ⟨h.1.1.1, h.1.2⟩
      · exact ⟨h.1.1.2, h.2⟩
  case impl =>
      intro φ ψ ihφ ihψ h P hP
      simp only [modestF, Bool.and_eq_true] at h
      simp only [playsArgsF, List.mem_append] at hP
      rcases hP with hP | hP
      · exact ihφ h.1 P hP
      · exact ihψ h.2 P hP
  case neg =>
      intro φ ih h P hP
      simp only [modestF] at h
      exact ih h P hP
  case box =>
      intro n φ ih h P hP
      simp only [modestF] at h
      exact ih h P hP
  case eq => intro p q _ _ _ P hP; simp [playsArgsF] at hP
  case diag => intro g φ _ _ P hP; simp [playsArgsF] at hP

/-! ## 2. The ceilings and the space. -/

section Space

variable (r₁ r₂ : Prog) (N k₀ : Nat) (φ₀ : Formula)

/-- Literal ceiling: the root formula's and every jump target's. -/
def LL : Nat := max (maxLitF φ₀) (LU r₁ r₂ N)

/-- Budget ceiling: the root budget and every jump target (T4.6: non-circular). -/
def RR : Nat := max k₀ (LL r₁ r₂ N φ₀)

/-- Enum-member size ceiling at budget `b` — the fold over the list itself. -/
def EB (b : Nat) : Nat := foldMax Formula.size (enumFormula b)

theorem le_EB {b : Nat} {ψ : Formula} (h : ψ ∈ enumFormula b) : ψ.size ≤ EB b :=
  le_foldMax Formula.size h

/-- Enum-member size ceiling across all reachable budgets. -/
def EBR : Nat := foldMax EB (List.range (RR r₁ r₂ N k₀ φ₀ + 1))

theorem EB_le_EBR {K : Nat} (hK : K ≤ RR r₁ r₂ N k₀ φ₀) :
    EB K ≤ EBR r₁ r₂ N k₀ φ₀ :=
  le_foldMax EB (List.mem_range.mpr (by omega))

/-- Program-universe size ceiling (covers cut-atom arguments from any enum sweep). -/
def SB : Nat := max (RR r₁ r₂ N k₀ φ₀) (EBR r₁ r₂ N k₀ φ₀)

/-- The instantiated program universe and guard family (T4.6 at ceiling `SB`). -/
def AP : List Prog := allowedProgs r₁ r₂ N (SB r₁ r₂ N k₀ φ₀)

def GFall : List Formula :=
  GF r₁ r₂ N (SB r₁ r₂ N k₀ φ₀) ++ (GF r₁ r₂ N (SB r₁ r₂ N k₀ φ₀)).map .neg

/-- Base of the size stratification: the root and the whole guard family fit. -/
def Z₀ : Nat := max φ₀.size (foldMax Formula.size (GFall r₁ r₂ N k₀ φ₀)) + 1

/-- The stratification: reads at strictly smaller budgets get headroom for one
    cut-composite (`≤ EBR + 2`) or one boxed/diag premise (`≤ RR + 3`). -/
def ZS (b : Nat) : Nat :=
  Z₀ r₁ r₂ N k₀ φ₀ +
    (RR r₁ r₂ N k₀ φ₀ - b) * (EBR r₁ r₂ N k₀ φ₀ + RR r₁ r₂ N k₀ φ₀ + 3)

theorem ZS_anti {b b' : Nat} (h : b ≤ b') : ZS r₁ r₂ N k₀ φ₀ b' ≤ ZS r₁ r₂ N k₀ φ₀ b := by
  have := Nat.mul_le_mul_right (EBR r₁ r₂ N k₀ φ₀ + RR r₁ r₂ N k₀ φ₀ + 3)
    (show RR r₁ r₂ N k₀ φ₀ - b' ≤ RR r₁ r₂ N k₀ φ₀ - b by omega)
  simp only [ZS]; omega

theorem ZS_step {b b' : Nat} (h : b' < b) (hb : b ≤ RR r₁ r₂ N k₀ φ₀) :
    ZS r₁ r₂ N k₀ φ₀ b + EBR r₁ r₂ N k₀ φ₀ + RR r₁ r₂ N k₀ φ₀ + 3 ≤
      ZS r₁ r₂ N k₀ φ₀ b' := by
  have h1 : RR r₁ r₂ N k₀ φ₀ - b + 1 ≤ RR r₁ r₂ N k₀ φ₀ - b' := by omega
  have h2 := Nat.mul_le_mul_right (EBR r₁ r₂ N k₀ φ₀ + RR r₁ r₂ N k₀ φ₀ + 3) h1
  have h3 : (RR r₁ r₂ N k₀ φ₀ - b + 1) * (EBR r₁ r₂ N k₀ φ₀ + RR r₁ r₂ N k₀ φ₀ + 3) =
      (RR r₁ r₂ N k₀ φ₀ - b) * (EBR r₁ r₂ N k₀ φ₀ + RR r₁ r₂ N k₀ φ₀ + 3) +
      (EBR r₁ r₂ N k₀ φ₀ + RR r₁ r₂ N k₀ φ₀ + 3) :=
    Nat.succ_mul _ _
  simp only [ZS]
  omega

/-- The invariant: atom arguments live in the universe, literals under the ceiling. -/
def InvP (ψ : Formula) : Prop :=
  (∀ P ∈ playsArgsF ψ, P ∈ AP r₁ r₂ N k₀ φ₀) ∧ maxLitF ψ ≤ LL r₁ r₂ N φ₀

instance InvP_dec (ψ : Formula) : Decidable (InvP r₁ r₂ N k₀ φ₀ ψ) := by
  unfold InvP; infer_instance

/-- The finite query space. -/
def SL : List (Nat × Formula) :=
  (List.range (RR r₁ r₂ N k₀ φ₀ + 1)).flatMap fun b =>
    ((enumFormula (ZS r₁ r₂ N k₀ φ₀ b)).filter
      (fun ψ => decide (ψ.size ≤ ZS r₁ r₂ N k₀ φ₀ b) &&
        decide (InvP r₁ r₂ N k₀ φ₀ ψ))).map fun ψ => (b, ψ)

theorem mem_SL_intro {b : Nat} {ψ : Formula} (hb : b ≤ RR r₁ r₂ N k₀ φ₀)
    (hsz : ψ.size ≤ ZS r₁ r₂ N k₀ φ₀ b) (hInv : InvP r₁ r₂ N k₀ φ₀ ψ) :
    (b, ψ) ∈ SL r₁ r₂ N k₀ φ₀ := by
  simp only [SL, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨b, by omega, ψ, ⟨(enum_complete _).2 ψ hsz, by simp [hsz, hInv]⟩, rfl⟩

theorem mem_SL_elim {b : Nat} {ψ : Formula} (h : (b, ψ) ∈ SL r₁ r₂ N k₀ φ₀) :
    b ≤ RR r₁ r₂ N k₀ φ₀ ∧ ψ.size ≤ ZS r₁ r₂ N k₀ φ₀ b ∧ InvP r₁ r₂ N k₀ φ₀ ψ := by
  simp only [SL, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨b', hb', ψ', ⟨_, hsz, hinv⟩, heq⟩ := h
  injection heq with h1 h2
  subst h1; subst h2
  exact ⟨by omega, hsz, hinv⟩

/-! ## 3. Read classification: the guard family and gated cut material re-enter. -/

theorem GFall_size {ψ : Formula} (h : ψ ∈ GFall r₁ r₂ N k₀ φ₀) :
    ψ.size ≤ Z₀ r₁ r₂ N k₀ φ₀ := by
  have := le_foldMax Formula.size h
  simp only [Z₀]; omega

theorem GFall_Inv (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    {ψ : Formula} (h : ψ ∈ GFall r₁ r₂ N k₀ φ₀) : InvP r₁ r₂ N k₀ φ₀ ψ := by
  simp only [GFall, List.mem_append, List.mem_map] at h
  rcases h with h | ⟨ψ₀, hψ₀, rfl⟩
  · refine ⟨fun P hP => GF_args r₁ r₂ N _ h₁ h₂ h hP, ?_⟩
    have := GF_lit r₁ r₂ N (SB r₁ r₂ N k₀ φ₀) h
    simp only [LL]; omega
  · refine ⟨fun P hP => ?_, ?_⟩
    · simp only [playsArgsF] at hP
      exact GF_args r₁ r₂ N _ h₁ h₂ hψ₀ hP
    · have := GF_lit r₁ r₂ N (SB r₁ r₂ N k₀ φ₀) hψ₀
      simp only [maxLitF, LL]; omega

theorem GFall_mem_SL (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    {ψ : Formula} (h : ψ ∈ GFall r₁ r₂ N k₀ φ₀) {b : Nat}
    (hb : b ≤ RR r₁ r₂ N k₀ φ₀) : (b, ψ) ∈ SL r₁ r₂ N k₀ φ₀ := by
  refine mem_SL_intro r₁ r₂ N k₀ φ₀ hb ?_ (GFall_Inv r₁ r₂ N k₀ φ₀ h₁ h₂ h)
  have := GFall_size r₁ r₂ N k₀ φ₀ h
  simp only [ZS]; omega

/-- **Gated cut material re-enters the universe**: a `.plays` argument of a
    `cutOKb`-passing enum formula is a universe program. -/
theorem enumArg_mem {K : Nat} (hK : K ≤ RR r₁ r₂ N k₀ φ₀) {ψ' : Formula}
    (hmem : ψ' ∈ enumFormula K) (hgate : cutOKb N ψ' = true) :
    ∀ {P : Prog}, P ∈ playsArgsF ψ' → P ∈ AP r₁ r₂ N k₀ φ₀ := by
  intro P hP
  have hgate' := cutOKb_iff.mp hgate
  obtain ⟨hargOK, hPmod⟩ := playsArgs_modest ψ' hgate'.2 P hP
  have hsubs : P ∈ subsF ψ' := playsArgsF_subset_subsF ψ' P hP
  simp only [argOK, Bool.or_eq_true, beq_iff_eq] at hargOK
  rcases hargOK with (rfl | rfl) | hclosed
  · -- .self is a base generator
    simp only [AP, allowedProgs, List.mem_flatMap]
    exact ⟨.self, by simp [baseProgs], mem_subsP_self _⟩
  · simp only [AP, allowedProgs, List.mem_flatMap]
    exact ⟨.opp, by simp [baseProgs], mem_subsP_self _⟩
  · -- closed modest gated argument of bounded size: a base generator
    have hPsz : P.size ≤ SB r₁ r₂ N k₀ φ₀ := by
      have h1 := sizeF_of_mem ψ' P hsubs
      have h2 := le_EB hmem
      have h3 := EB_le_EBR r₁ r₂ N k₀ φ₀ hK
      simp only [SB]; omega
    have hPlit : maxLitP P ≤ N := by
      have h1 := maxLitF_of_mem ψ' P hsubs
      have h2 := hgate'.1
      omega
    simp only [AP, allowedProgs, List.mem_flatMap]
    refine ⟨P, ?_, mem_subsP_self P⟩
    simp only [baseProgs, List.mem_cons]
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(enum_complete _).1 P hPsz, ⟨hclosed, hPmod⟩, hPlit⟩

/-! ## 4. The congruence: `stepB` at an in-space query reads only in-space queries. -/

/-- Cert-layer reads are answered equally by space-agreeing approximations. -/
theorem cert_reads_ok (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    {S₁ S₂ : Nat → Formula → Bool}
    (hag : ∀ b ψ, b ≤ RR r₁ r₂ N k₀ φ₀ → ψ.size ≤ ZS r₁ r₂ N k₀ φ₀ b →
      InvP r₁ r₂ N k₀ φ₀ ψ → S₁ b ψ = S₂ b ψ)
    {p q : Prog} (hp : p ∈ AP r₁ r₂ N k₀ φ₀) (hq : q ∈ AP r₁ r₂ N k₀ φ₀)
    {b : Nat} (hb : b ≤ RR r₁ r₂ N k₀ φ₀) :
    ∀ m ψ, CertRead b p q p m ψ → S₁ m ψ = S₂ m ψ := by
  intro m ψ hr
  have hlp := allowedProgs_lit r₁ r₂ N (SB r₁ r₂ N k₀ φ₀) hp
  have hlq := allowedProgs_lit r₁ r₂ N (SB r₁ r₂ N k₀ φ₀) hq
  have hbud := certRead_budget r₁ r₂ N hr hlp hlq hlp
  have hLU : LU r₁ r₂ N ≤ RR r₁ r₂ N k₀ φ₀ := by
    simp only [RR, LL]; omega
  have hmR : m ≤ RR r₁ r₂ N k₀ φ₀ := by omega
  rcases certRead_mem_GF r₁ r₂ N (SB r₁ r₂ N k₀ φ₀) h₁ h₂ hp hq hr
    with hmem | ⟨ψ₀, hψ₀, rfl⟩
  · have hGF : ψ ∈ GFall r₁ r₂ N k₀ φ₀ := List.mem_append_left _ hmem
    refine hag m ψ hmR ?_ (GFall_Inv r₁ r₂ N k₀ φ₀ h₁ h₂ hGF)
    have := GFall_size r₁ r₂ N k₀ φ₀ hGF
    simp only [ZS]; omega
  · have hGF : Formula.neg ψ₀ ∈ GFall r₁ r₂ N k₀ φ₀ :=
      List.mem_append_right _ (List.mem_map.mpr ⟨ψ₀, hψ₀, rfl⟩)
    refine hag m _ hmR ?_ (GFall_Inv r₁ r₂ N k₀ φ₀ h₁ h₂ hGF)
    have := GFall_size r₁ r₂ N k₀ φ₀ hGF
    simp only [ZS]; omega

set_option maxHeartbeats 4000000 in
/-- **THE CONGRUENCE**: at an in-space query, `stepB` is determined by the approximation's
    values at in-space queries. -/
theorem stepB_congr (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    {S₁ S₂ : Nat → Formula → Bool}
    (hag : ∀ b ψ, b ≤ RR r₁ r₂ N k₀ φ₀ → ψ.size ≤ ZS r₁ r₂ N k₀ φ₀ b →
      InvP r₁ r₂ N k₀ φ₀ ψ → S₁ b ψ = S₂ b ψ)
    {K : Nat} {φ : Formula} (hK : K ≤ RR r₁ r₂ N k₀ φ₀)
    (hsz : φ.size ≤ ZS r₁ r₂ N k₀ φ₀ K) (hInv : InvP r₁ r₂ N k₀ φ₀ φ) :
    stepB N S₁ K φ = stepB N S₂ K φ := by
  obtain ⟨hargs, hlit⟩ := hInv
  have hN_LL : N ≤ LL r₁ r₂ N φ₀ := by simp only [LL, LU]; omega
  have hLL_RR : LL r₁ r₂ N φ₀ ≤ RR r₁ r₂ N k₀ φ₀ := by simp only [RR]; omega
  have h_cert : certOG S₁ (K+1) K φ = certOG S₂ (K+1) K φ := by
    unfold certOG
    split
    · rename_i p q a
      exact decCertG_congr (K+1) K p q p a
        (cert_reads_ok r₁ r₂ N k₀ φ₀ h₁ h₂ hag
          (hargs p (by simp [playsArgsF])) (hargs q (by simp [playsArgsF])) hK)
    · rfl
  have h_weaken : chkWeaken S₁ K φ = chkWeaken S₂ K φ := by
    unfold chkWeaken
    split
    · rename_i A B
      have hInvB : InvP r₁ r₂ N k₀ φ₀ B := by
        constructor
        · intro P hP
          exact hargs P (by simp only [playsArgsF, List.mem_append]; exact Or.inr hP)
        · simp only [maxLitF] at hlit; omega
      have hszB : B.size ≤ ZS r₁ r₂ N k₀ φ₀ (K - (Formula.impl A B).size) := by
        have hZ := ZS_anti r₁ r₂ N k₀ φ₀
          (show K - (Formula.impl A B).size ≤ K by omega)
        simp only [Formula.size] at hsz
        omega
      rw [hag (K - (Formula.impl A B).size) B (by omega) hszB hInvB]
      -- the contrapose leg: the un-negated implication is a SMALLER in-space query
      -- (negs are transparent to `playsArgsF` and `maxLitF`)
      congr 1
      split
      · rename_i B' A'
        have hInv' : InvP r₁ r₂ N k₀ φ₀ (.impl A' B') := by
          constructor
          · intro P hP
            refine hargs P ?_
            simp only [playsArgsF, List.mem_append] at hP ⊢
            tauto
          · simp only [maxLitF] at hlit ⊢; omega
        have hsz' : (Formula.impl A' B').size ≤
            ZS r₁ r₂ N k₀ φ₀ (K - (Formula.impl (.neg B') (.neg A')).size) := by
          have hZ := ZS_anti r₁ r₂ N k₀ φ₀
            (show K - (Formula.impl (.neg B') (.neg A')).size ≤ K by omega)
          have hs : (Formula.impl A' B').size ≤ (Formula.impl (.neg B') (.neg A')).size := by
            simp only [Formula.size]; omega
          omega
        rw [hag (K - (Formula.impl (.neg B') (.neg A')).size) (.impl A' B')
          (by omega) hsz' hInv']
      · rfl
    · rfl
  have h_STS : chkSTS S₁ K φ = chkSTS S₂ K φ := by
    unfold chkSTS
    split
    · rename_i k₁ ψ' k₁' ψ₁ k₂ ψ₂ c0' c1 q opnt c0
      have hme : (Prog.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q)
          ∈ AP r₁ r₂ N k₀ φ₀ := hargs _ (by simp [playsArgsF])
      have hopnt : opnt ∈ AP r₁ r₂ N k₀ φ₀ := hargs _ (by simp [playsArgsF])
      have hinner : (Prog.search k₂ ψ₂ (.const c0') (.const c1)) ∈
          certU (Prog.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt := by
        refine List.mem_append_left _ ?_
        simp [subsP]
      have hmeP : (Prog.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) ∈
          players (Prog.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt := by
        simp only [players, List.mem_cons]
        exact Or.inl trivial
      have hopntP : opnt ∈
          players (Prog.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt := by
        simp only [players, List.mem_cons]
        exact Or.inr (Or.inl trivial)
      have hread := step_search
        (Prog.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt
        hmeP hopntP hinner
      have hGF : (ψ₂.subst (Prog.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q)
          opnt) ∈ GFall r₁ r₂ N k₀ φ₀ :=
        List.mem_append_left _
          (mem_GF r₁ r₂ N (SB r₁ r₂ N k₀ φ₀) hme hopnt hread)
      have hk₂ : k₂ ≤ RR r₁ r₂ N k₀ φ₀ := by
        simp only [maxLitF, maxLitP] at hlit
        omega
      rw [hag k₂ _ hk₂
        (by have := GFall_size r₁ r₂ N k₀ φ₀ hGF; simp only [ZS]; omega)
        (GFall_Inv r₁ r₂ N k₀ φ₀ h₁ h₂ hGF)]
    · rfl
  have h_ITrans : chkITransB N S₁ K φ = chkITransB N S₂ K φ := by
    unfold chkITransB
    split
    · rename_i A C
      apply anyCongr; intro m₁ hm₁
      apply anyCongr; intro ψ' hψ'
      have hm₁K : m₁ < K := List.mem_range.mp hm₁
      cases hc : cutOKb N ψ' with
      | false => simp []
      | true =>
          have hψsz := le_EB hψ'
          have hEBR := EB_le_EBR r₁ r₂ N k₀ φ₀ hK
          have hstep := ZS_step r₁ r₂ N k₀ φ₀ hm₁K hK
          have hstep2 := ZS_step r₁ r₂ N k₀ φ₀
            (show K - (Formula.impl A C).size - m₁ < K by
              have := Formula.size_pos (Formula.impl A C); omega) hK
          have hInv1 : InvP r₁ r₂ N k₀ φ₀ (.impl A ψ') := by
            constructor
            · intro P hP
              simp only [playsArgsF, List.mem_append] at hP
              rcases hP with hP | hP
              · exact hargs P (by simp only [playsArgsF, List.mem_append]; exact Or.inl hP)
              · exact enumArg_mem r₁ r₂ N k₀ φ₀ hK hψ' hc hP
            · have := (cutOKb_iff.mp hc).1
              simp only [maxLitF] at hlit ⊢
              omega
          have hInv2 : InvP r₁ r₂ N k₀ φ₀ (.impl ψ' C) := by
            constructor
            · intro P hP
              simp only [playsArgsF, List.mem_append] at hP
              rcases hP with hP | hP
              · exact enumArg_mem r₁ r₂ N k₀ φ₀ hK hψ' hc hP
              · exact hargs P (by simp only [playsArgsF, List.mem_append]; exact Or.inr hP)
            · have := (cutOKb_iff.mp hc).1
              simp only [maxLitF] at hlit ⊢
              omega
          have hsz1 : (Formula.impl A ψ').size ≤ ZS r₁ r₂ N k₀ φ₀ m₁ := by
            simp only [Formula.size] at hsz ⊢
            omega
          have hsz2 : (Formula.impl ψ' C).size ≤
              ZS r₁ r₂ N k₀ φ₀ (K - (Formula.impl A C).size - m₁) := by
            simp only [Formula.size] at hsz hstep2 ⊢
            omega
          rw [hag m₁ _ (by omega) hsz1 hInv1,
            hag (K - (Formula.impl A C).size - m₁) _ (by omega) hsz2 hInv2]
    · rfl
  have h_AtomBox : chkAtomBox (fun m ψ => certOG S₁ (m+1) m ψ) K φ =
      chkAtomBox (fun m ψ => certOG S₂ (m+1) m ψ) K φ := by
    unfold chkAtomBox
    split
    · rename_i p q a kB p' q' a'
      have hkB : kB ≤ RR r₁ r₂ N k₀ φ₀ := by
        simp only [maxLitF] at hlit
        omega
      have hOG := certOG_congr (kB+1) kB
        (cert_reads_ok r₁ r₂ N k₀ φ₀ h₁ h₂ hag
          (hargs p (by simp [playsArgsF])) (hargs q (by simp [playsArgsF])) hkB)
        (a := a)
      have hOG' : (fun m ψ => certOG S₁ (m+1) m ψ) kB (Formula.plays p q a) =
          (fun m ψ => certOG S₂ (m+1) m ψ) kB (Formula.plays p q a) := hOG
      rw [hOG']
    · rfl
  have h_BoxIntro : chkBoxIntroE S₁ K φ = chkBoxIntroE S₂ K φ := by
    unfold chkBoxIntroE
    split
    · rename_i kIn ψ
      cases hg : decide (kIn + (Formula.box kIn ψ).size ≤ K) with
      | false => simp []
      | true =>
          have hgle := of_decide_eq_true hg
          have hkK : kIn < K := by
            have := Formula.size_pos ψ
            simp only [numCost, Formula.size] at hgle
            omega
          have hstep := ZS_step r₁ r₂ N k₀ φ₀ hkK hK
          have hszψ : ψ.size ≤ ZS r₁ r₂ N k₀ φ₀ kIn := by
            simp only [numCost, Formula.size] at hsz
            omega
          have hInvψ : InvP r₁ r₂ N k₀ φ₀ ψ := by
            constructor
            · intro P hP
              exact hargs P (by simp only [playsArgsF]; exact hP)
            · simp only [maxLitF] at hlit; omega
          rw [hag kIn ψ (by omega) hszψ hInvψ]
    · rfl
  have h_AppE : chkAppEB N S₁ K φ = chkAppEB N S₂ K φ := by
    unfold chkAppEB
    apply anyCongr; intro m₁ hm₁
    apply anyCongr; intro ψ' hψ'
    have hm₁K : m₁ < K := List.mem_range.mp hm₁
    cases hc : cutOKb N ψ' with
    | false => simp []
    | true =>
        have hψsz := le_EB hψ'
        have hEBR := EB_le_EBR r₁ r₂ N k₀ φ₀ hK
        have hstep := ZS_step r₁ r₂ N k₀ φ₀ hm₁K hK
        have hstep2 := ZS_step r₁ r₂ N k₀ φ₀
          (show K - φ.size - m₁ < K by
            have := Formula.size_pos φ; omega) hK
        have hInvC : InvP r₁ r₂ N k₀ φ₀ ψ' := by
          constructor
          · intro P hP
            exact enumArg_mem r₁ r₂ N k₀ φ₀ hK hψ' hc hP
          · have := (cutOKb_iff.mp hc).1
            omega
        have hInv1 : InvP r₁ r₂ N k₀ φ₀ (.impl ψ' φ) := by
          constructor
          · intro P hP
            simp only [playsArgsF, List.mem_append] at hP
            rcases hP with hP | hP
            · exact enumArg_mem r₁ r₂ N k₀ φ₀ hK hψ' hc hP
            · exact hargs P hP
          · have := (cutOKb_iff.mp hc).1
            simp only [maxLitF]
            omega
        have hsz1 : (Formula.impl ψ' φ).size ≤ ZS r₁ r₂ N k₀ φ₀ m₁ := by
          simp only [Formula.size]
          omega
        have hsz2 : ψ'.size ≤ ZS r₁ r₂ N k₀ φ₀ (K - φ.size - m₁) := by
          omega
        rw [hag m₁ _ (by omega) hsz1 hInv1,
          hag (K - φ.size - m₁) _ (by omega) hsz2 hInvC]
  have h_AxK : chkAxKB N S₁ K φ = chkAxKB N S₂ K φ := by
    unfold chkAxKB
    split
    · rename_i b ψ c α
      cases hgate : decide ((Formula.impl (.box b ψ) (.box c α)).size ≤ K) with
      | false => simp []
      | true =>
          have hgle := of_decide_eq_true hgate
          simp only [Bool.true_and]
          apply anyCongr; intro a ha
          cases hc : cutOKb N (.box a (.impl ψ α)) with
          | false => simp []
          | true =>
              have hcut := cutOKb_iff.mp hc
              have haN : a ≤ N := by
                have := hcut.1
                simp only [maxLitF] at this
                omega
              have hKpos : K - (Formula.impl (.box b ψ) (.box c α)).size < K := by
                have := Formula.size_pos (Formula.impl (.box b ψ) (.box c α))
                omega
              have hstep := ZS_step r₁ r₂ N k₀ φ₀ hKpos hK
              have hlog : Nat.log2 a ≤ RR r₁ r₂ N k₀ φ₀ := by
                have hl1 := log2_mono haN
                have hl2 := log2_le_self N
                omega
              have hszr : (Formula.box a (Formula.impl ψ α)).size ≤
                  ZS r₁ r₂ N k₀ φ₀ (K - (Formula.impl (.box b ψ) (.box c α)).size) := by
                simp only [numCost, Formula.size] at hsz hstep ⊢
                omega
              have hInvr : InvP r₁ r₂ N k₀ φ₀ (.box a (.impl ψ α)) := by
                constructor
                · intro P hP
                  simp only [playsArgsF, List.mem_append] at hP
                  refine hargs P ?_
                  simp only [playsArgsF, List.mem_append]
                  exact hP
                · have := hcut.1
                  simp only [maxLitF] at hlit ⊢
                  omega
              rw [hag (K - (Formula.impl (.box b ψ) (.box c α)).size) _ (by omega)
                hszr hInvr]
    · rfl
  have h_DiagF : chkDiagFEB N S₁ K φ = chkDiagFEB N S₂ K φ := by
    unfold chkDiagFEB
    split
    · rename_i g t g' g'' t' t''
      cases ht1 : (t == t') with
      | false => simp
      | true =>
          cases ht2 : (t == t'') with
          | false => simp
          | true =>
              have het1 := eq_of_beq ht1
              have het2 := eq_of_beq ht2
              subst het1
              subst het2
              cases hgate : decide ((Formula.impl (.diag g t)
                  (.impl (.box g (.diag g t)) t)).size ≤ K) with
              | false => simp
              | true =>
                  have hgle := of_decide_eq_true hgate
                  congr 1
                  apply anyCongr; intro fb hfb
                  cases hc : cutOKb N (.impl (.box fb t) t) with
                  | false => simp []
                  | true =>
                      have hcut := cutOKb_iff.mp hc
                      have hfbN : fb ≤ N := by
                        have := hcut.1
                        simp only [maxLitF] at this
                        omega
                      have hKpos : K - (Formula.impl (.diag g t)
                          (.impl (.box g (.diag g t)) t)).size < K := by
                        have := Formula.size_pos (Formula.impl (.diag g t)
                          (.impl (.box g (.diag g t)) t))
                        omega
                      have hstep := ZS_step r₁ r₂ N k₀ φ₀ hKpos hK
                      have hlog : Nat.log2 fb ≤ RR r₁ r₂ N k₀ φ₀ := by
                        have hl1 := log2_mono hfbN
                        have hl2 := log2_le_self N
                        omega
                      have hszr : (Formula.impl (.box fb t) t).size ≤
                          ZS r₁ r₂ N k₀ φ₀ (K - (Formula.impl (.diag g t)
                            (.impl (.box g (.diag g t)) t)).size) := by
                        simp only [numCost, Formula.size] at hsz hstep ⊢
                        omega
                      have hInvr : InvP r₁ r₂ N k₀ φ₀ (.impl (.box fb t) t) := by
                        constructor
                        · intro P hP
                          refine hargs P ?_
                          simp only [playsArgsF, List.mem_append, List.not_mem_nil,
                            false_or] at hP ⊢
                          rcases hP with hP | hP
                          · exact hP
                          · exact hP
                        · have := hcut.1
                          simp only [maxLitF] at hlit ⊢
                          omega
                      rw [hag (K - (Formula.impl (.diag g t)
                        (.impl (.box g (.diag g t)) t)).size) _ (by omega) hszr hInvr]
    · rfl
  have h_DiagB : chkDiagBEB N S₁ K φ = chkDiagBEB N S₂ K φ := by
    unfold chkDiagBEB
    split
    · rename_i g g' t t' g'' t''
      cases ht1 : (t == t') with
      | false => simp
      | true =>
          cases ht2 : (t == t'') with
          | false => simp
          | true =>
              have het1 := eq_of_beq ht1
              have het2 := eq_of_beq ht2
              subst het1
              subst het2
              cases hgate : decide ((Formula.impl (.impl (.box g (.diag g t)) t)
                  (.diag g t)).size ≤ K) with
              | false => simp
              | true =>
                  have hgle := of_decide_eq_true hgate
                  congr 1
                  apply anyCongr; intro fb hfb
                  cases hc : cutOKb N (.impl (.box fb t) t) with
                  | false => simp []
                  | true =>
                      have hcut := cutOKb_iff.mp hc
                      have hfbN : fb ≤ N := by
                        have := hcut.1
                        simp only [maxLitF] at this
                        omega
                      have hKpos : K - (Formula.impl (.impl (.box g (.diag g t)) t)
                          (.diag g t)).size < K := by
                        have := Formula.size_pos (Formula.impl
                          (.impl (.box g (.diag g t)) t) (.diag g t))
                        omega
                      have hstep := ZS_step r₁ r₂ N k₀ φ₀ hKpos hK
                      have hlog : Nat.log2 fb ≤ RR r₁ r₂ N k₀ φ₀ := by
                        have hl1 := log2_mono hfbN
                        have hl2 := log2_le_self N
                        omega
                      have hszr : (Formula.impl (.box fb t) t).size ≤
                          ZS r₁ r₂ N k₀ φ₀ (K - (Formula.impl
                            (.impl (.box g (.diag g t)) t) (.diag g t)).size) := by
                        simp only [numCost, Formula.size] at hsz hstep ⊢
                        omega
                      have hInvr : InvP r₁ r₂ N k₀ φ₀ (.impl (.box fb t) t) := by
                        constructor
                        · intro P hP
                          refine hargs P ?_
                          simp only [playsArgsF, List.mem_append, List.not_mem_nil,
                            false_or, or_false] at hP ⊢
                          rcases hP with hP | hP
                          · exact hP
                          · exact hP
                        · have := hcut.1
                          simp only [maxLitF] at hlit ⊢
                          omega
                      rw [hag (K - (Formula.impl (.impl (.box g (.diag g t)) t)
                        (.diag g t)).size) _ (by omega) hszr hInvr]
    · rfl
  have h_ImpS2 : chkImpS2EB N S₁ K φ = chkImpS2EB N S₂ K φ := by
    unfold chkImpS2EB
    split
    · rename_i A C
      apply anyCongr; intro m₁ hm₁
      apply anyCongr; intro ψ' hψ'
      have hm₁K : m₁ < K := List.mem_range.mp hm₁
      cases hc : cutOKb N ψ' with
      | false => simp []
      | true =>
          have hψsz := le_EB hψ'
          have hEBR := EB_le_EBR r₁ r₂ N k₀ φ₀ hK
          have hstep := ZS_step r₁ r₂ N k₀ φ₀ hm₁K hK
          have hstep2 := ZS_step r₁ r₂ N k₀ φ₀
            (show K - (Formula.impl A C).size - m₁ < K by
              have := Formula.size_pos (Formula.impl A C); omega) hK
          have hInv1 : InvP r₁ r₂ N k₀ φ₀ (.impl A (.impl ψ' C)) := by
            constructor
            · intro P hP
              simp only [playsArgsF, List.mem_append] at hP
              rcases hP with hP | hP | hP
              · exact hargs P (by simp only [playsArgsF, List.mem_append]; exact Or.inl hP)
              · exact enumArg_mem r₁ r₂ N k₀ φ₀ hK hψ' hc hP
              · exact hargs P (by simp only [playsArgsF, List.mem_append]; exact Or.inr hP)
            · have := (cutOKb_iff.mp hc).1
              simp only [maxLitF] at hlit ⊢
              omega
          have hInv2 : InvP r₁ r₂ N k₀ φ₀ (.impl A ψ') := by
            constructor
            · intro P hP
              simp only [playsArgsF, List.mem_append] at hP
              rcases hP with hP | hP
              · exact hargs P (by simp only [playsArgsF, List.mem_append]; exact Or.inl hP)
              · exact enumArg_mem r₁ r₂ N k₀ φ₀ hK hψ' hc hP
            · have := (cutOKb_iff.mp hc).1
              simp only [maxLitF] at hlit ⊢
              omega
          have hsz1 : (Formula.impl A (.impl ψ' C)).size ≤ ZS r₁ r₂ N k₀ φ₀ m₁ := by
            simp only [Formula.size] at hsz ⊢
            omega
          have hsz2 : (Formula.impl A ψ').size ≤
              ZS r₁ r₂ N k₀ φ₀ (K - (Formula.impl A C).size - m₁) := by
            simp only [Formula.size] at hsz hstep2 ⊢
            omega
          rw [hag m₁ _ (by omega) hsz1 hInv1,
            hag (K - (Formula.impl A C).size - m₁) _ (by omega) hsz2 hInv2]
    · rfl
  have h_AtomNeg : chkAtomNeg (fun m ψ => certOG S₁ (m+1) m ψ) K φ =
      chkAtomNeg (fun m ψ => certOG S₂ (m+1) m ψ) K φ := by
    unfold chkAtomNeg
    split
    · rename_i p q aN
      have hpin : p ∈ AP r₁ r₂ N k₀ φ₀ := hargs p (by simp [playsArgsF])
      have hqin : q ∈ AP r₁ r₂ N k₀ φ₀ := hargs q (by simp [playsArgsF])
      have hb : K - (Formula.neg (.plays p q aN)).size ≤ RR r₁ r₂ N k₀ φ₀ := by omega
      have hOC := certOG_congr ((K - (Formula.neg (.plays p q aN)).size) + 1)
        (K - (Formula.neg (.plays p q aN)).size)
        (cert_reads_ok r₁ r₂ N k₀ φ₀ h₁ h₂ hag hpin hqin hb) (a := Action.C)
      have hOD := certOG_congr ((K - (Formula.neg (.plays p q aN)).size) + 1)
        (K - (Formula.neg (.plays p q aN)).size)
        (cert_reads_ok r₁ r₂ N k₀ φ₀ h₁ h₂ hag hpin hqin hb) (a := Action.D)
      have hOC' : (fun m ψ => certOG S₁ (m+1) m ψ)
          (K - (Formula.neg (.plays p q aN)).size) (Formula.plays p q .C) =
          (fun m ψ => certOG S₂ (m+1) m ψ)
          (K - (Formula.neg (.plays p q aN)).size) (Formula.plays p q .C) := hOC
      have hOD' : (fun m ψ => certOG S₁ (m+1) m ψ)
          (K - (Formula.neg (.plays p q aN)).size) (Formula.plays p q .D) =
          (fun m ψ => certOG S₂ (m+1) m ψ)
          (K - (Formula.neg (.plays p q aN)).size) (Formula.plays p q .D) := hOD
      rw [hOC', hOD']
    · rfl
  unfold stepB
  rw [h_cert, h_weaken, h_STS, h_ITrans, h_AtomBox, h_BoxIntro, h_AppE, h_AxK,
    h_DiagF, h_DiagB, h_ImpS2, h_AtomNeg]

/-! ## 5. The countP kit (T4.1a verbatim). -/

theorem countP_le {α : Type} {f g : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, f x = true → g x = true) → l.countP f ≤ l.countP g := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      rw [List.countP_cons, List.countP_cons]
      have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      by_cases hfa : f a = true
      · have := h a (List.mem_cons_self ..) hfa
        simp [hfa, this]; omega
      · simp only [Bool.not_eq_true] at hfa
        simp [hfa]; omega

theorem countP_lt {α : Type} {f g : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, f x = true → g x = true) →
      ∀ x ∈ l, f x = false → g x = true → l.countP f < l.countP g := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons a t ih =>
      intro h x hx hfx hgx
      rw [List.countP_cons, List.countP_cons]
      rcases List.mem_cons.mp hx with rfl | hxt
      · have ht := countP_le (fun y hy => h y (List.mem_cons_of_mem _ hy))
        simp [hfx, hgx]; omega
      · have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hxt hfx hgx
        by_cases hfa : f a = true
        · have := h a (List.mem_cons_self ..) hfa
          simp [hfa, this]; omega
        · simp only [Bool.not_eq_true] at hfa
          by_cases hga : g a = true <;> simp [hfa, hga] <;> omega

theorem countP_le_len {α : Type} (f : α → Bool) : ∀ l : List α, l.countP f ≤ l.length := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.countP_cons, List.length_cons]
      by_cases hfa : f a = true
      · simp [hfa]; omega
      · simp only [Bool.not_eq_true] at hfa
        simp [hfa]; omega

/-! ## 6. Stabilization (the T4.1a template over `SL`). -/

/-- Two consecutive iterates agree on the space. -/
def Agree (n : Nat) : Prop :=
  ∀ q ∈ SL r₁ r₂ N k₀ φ₀, decB N n q.1 q.2 = decB N (n+1) q.1 q.2

theorem agree_succ (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    {n : Nat} (h : Agree r₁ r₂ N k₀ φ₀ n) : Agree r₁ r₂ N k₀ φ₀ (n+1) := by
  intro q hq
  obtain ⟨b, ψ⟩ := q
  obtain ⟨hb, hsz, hInv⟩ := mem_SL_elim r₁ r₂ N k₀ φ₀ hq
  show decB N (n+1) b ψ = decB N (n+2) b ψ
  show stepB N (decB N n) b ψ = stepB N (decB N (n+1)) b ψ
  refine stepB_congr r₁ r₂ N k₀ φ₀ h₁ h₂ ?_ hb hsz hInv
  intro b' ψ' hb' hsz' hInv'
  exact h (b', ψ') (mem_SL_intro r₁ r₂ N k₀ φ₀ hb' hsz' hInv')

theorem agree_ge (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    {n : Nat} (h : Agree r₁ r₂ N k₀ φ₀ n) :
    ∀ m, n ≤ m → ∀ q ∈ SL r₁ r₂ N k₀ φ₀,
      decB N m q.1 q.2 = decB N n q.1 q.2 := by
  intro m
  induction m with
  | zero =>
      intro hm q _
      have : n = 0 := by omega
      subst this; rfl
  | succ m ih =>
      intro hm q hq
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · have hAm : Agree r₁ r₂ N k₀ φ₀ m := by
          have haux : ∀ j, n + j ≤ m → Agree r₁ r₂ N k₀ φ₀ (n + j) := by
            intro j
            induction j with
            | zero => intro _; simpa using h
            | succ j ihj =>
                intro hj
                have := ihj (by omega)
                exact agree_succ r₁ r₂ N k₀ φ₀ h₁ h₂ this
          have hnm : n ≤ m := by omega
          have h4 := haux (m - n) (by omega)
          have heq : n + (m - n) = m := by omega
          rw [heq] at h4
          exact h4
        have e1 : decB N (m + 1) q.1 q.2 = decB N m q.1 q.2 :=
          (hAm q hq).symm
        rw [e1, ih (by omega) q hq]
      · have : n = m + 1 := by omega
        subst this; rfl

theorem exists_agree (_ : modestP r₁ = true) (_ : modestP r₂ = true) :
    ∃ n, n ≤ (SL r₁ r₂ N k₀ φ₀).length ∧ Agree r₁ r₂ N k₀ φ₀ n := by
  apply Classical.byContradiction
  intro hcon
  have hall : ∀ j, j ≤ (SL r₁ r₂ N k₀ φ₀).length → ¬ Agree r₁ r₂ N k₀ φ₀ j := by
    intro j hj hag
    exact hcon ⟨j, hj, hag⟩
  have hstrict : ∀ j, j ≤ (SL r₁ r₂ N k₀ φ₀).length →
      (SL r₁ r₂ N k₀ φ₀).countP (fun q => decB N j q.1 q.2) <
      (SL r₁ r₂ N k₀ φ₀).countP (fun q => decB N (j+1) q.1 q.2) := by
    intro j hj
    have hnag := hall j hj
    have hex : ∃ q, q ∈ SL r₁ r₂ N k₀ φ₀ ∧
        decB N j q.1 q.2 ≠ decB N (j+1) q.1 q.2 := by
      apply Classical.byContradiction
      intro hno
      exact hnag (fun q hq => Classical.byContradiction (fun hne => hno ⟨q, hq, hne⟩))
    obtain ⟨q, hq, hne⟩ := hex
    have hmono : ∀ x ∈ SL r₁ r₂ N k₀ φ₀,
        decB N j x.1 x.2 = true → decB N (j+1) x.1 x.2 = true :=
      fun x _ hx => decB_mono N j (j+1) (by omega) _ _ hx
    have hfj : decB N j q.1 q.2 = false := by
      cases hj' : decB N j q.1 q.2 with
      | false => rfl
      | true =>
          have h2 := decB_mono N j (j+1) (by omega) _ _ hj'
          rw [hj', h2] at hne
          exact absurd rfl hne
    have hgj : decB N (j+1) q.1 q.2 = true := by
      cases hj'' : decB N (j+1) q.1 q.2 with
      | true => rfl
      | false =>
          rw [hfj, hj''] at hne
          exact absurd rfl hne
    exact countP_lt hmono q hq hfj hgj
  have hge : ∀ j, j ≤ (SL r₁ r₂ N k₀ φ₀).length + 1 →
      j ≤ (SL r₁ r₂ N k₀ φ₀).countP (fun q => decB N j q.1 q.2) := by
    intro j
    induction j with
    | zero => intro _; omega
    | succ j ih =>
        intro hj
        have hx1 := ih (by omega)
        have hx2 := hstrict j (by omega)
        omega
  have hx1 := hge ((SL r₁ r₂ N k₀ φ₀).length + 1) (Nat.le_refl _)
  have hx2 := countP_le_len
    (fun q => decB N ((SL r₁ r₂ N k₀ φ₀).length + 1) q.1 q.2) (SL r₁ r₂ N k₀ φ₀)
  omega

/-- Any ∃-fuel hit at an in-space query is already a hit at fuel `|SL|`. -/
theorem decB_bound (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    {n b : Nat} {ψ : Formula} (hb : b ≤ RR r₁ r₂ N k₀ φ₀)
    (hsz : ψ.size ≤ ZS r₁ r₂ N k₀ φ₀ b) (hInv : InvP r₁ r₂ N k₀ φ₀ ψ)
    (h : decB N n b ψ = true) : decB N (SL r₁ r₂ N k₀ φ₀).length b ψ = true := by
  obtain ⟨j, hjle, hag⟩ := exists_agree r₁ r₂ N k₀ φ₀ h₁ h₂
  have hqmem : (b, ψ) ∈ SL r₁ r₂ N k₀ φ₀ := mem_SL_intro r₁ r₂ N k₀ φ₀ hb hsz hInv
  rcases Nat.le_total n (SL r₁ r₂ N k₀ φ₀).length with hle | hge
  · exact decB_mono N n _ hle _ _ h
  · have e1 := agree_ge r₁ r₂ N k₀ φ₀ h₁ h₂ hag n (by omega) (b, ψ) hqmem
    have e2 := agree_ge r₁ r₂ N k₀ φ₀ h₁ h₂ hag (SL r₁ r₂ N k₀ φ₀).length
      (by omega) (b, ψ) hqmem
    simp only at e1 e2
    rw [e2, ← e1]
    exact h

/-! ## 7. THE PAYOFF — the modest stratum is DECIDABLE over the zoo universe. -/

/-- **DECIDABILITY of the modest stratum**, with the computable fuel bound `|SL|`. The only
    substantive hypotheses: the roots are modest (the whole zoo is, T4.3) and the root
    formula's `.plays` arguments live in the universe (automatic for `guardU` members —
    i.e. for every bot-guard instance — via `GF_args`). -/
theorem PfG_iff_decB_bound (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    (hargs₀ : ∀ P ∈ playsArgsF φ₀, P ∈ AP r₁ r₂ N k₀ φ₀) :
    PfG (modestGate N) k₀ φ₀ ↔
      decB N (SL r₁ r₂ N k₀ φ₀).length k₀ φ₀ = true := by
  have hk : k₀ ≤ RR r₁ r₂ N k₀ φ₀ := by simp only [RR]; omega
  have hsz : φ₀.size ≤ ZS r₁ r₂ N k₀ φ₀ k₀ := by
    simp only [ZS, Z₀]; omega
  have hInv : InvP r₁ r₂ N k₀ φ₀ φ₀ := ⟨hargs₀, by simp only [LL]; omega⟩
  constructor
  · intro h
    obtain ⟨F, hF⟩ := decB_complete N h k₀ (Nat.le_refl _)
    exact decB_bound r₁ r₂ N k₀ φ₀ h₁ h₂ hk hsz hInv hF
  · intro h
    exact decB_sound N _ k₀ φ₀ h

/-- The `Decidable` instance — bounded provability over the modest stratum is decided by
    a terminating computation. -/
def decidePfG (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    (hargs₀ : ∀ P ∈ playsArgsF φ₀, P ∈ AP r₁ r₂ N k₀ φ₀) :
    Decidable (PfG (modestGate N) k₀ φ₀) :=
  if h : decB N (SL r₁ r₂ N k₀ φ₀).length k₀ φ₀ = true then
    .isTrue ((PfG_iff_decB_bound r₁ r₂ N k₀ φ₀ h₁ h₂ hargs₀).mpr h)
  else
    .isFalse (fun hg => h ((PfG_iff_decB_bound r₁ r₂ N k₀ φ₀ h₁ h₂ hargs₀).mp hg))

end Space

end PD.T47
