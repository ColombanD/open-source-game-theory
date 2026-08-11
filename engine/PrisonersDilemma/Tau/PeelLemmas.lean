import PrisonersDilemma.Tau.Defs
import PrisonersDilemma.Base.Soundness

/-!
# Tau/PeelLemmas — the α-quantification workhorses

Two lemmas turn "the oracle bits of the guards" into "the play of the compiled tau
player", once and for all guard lists:

* `eval_tsearch_of_bits` — the `tsearch` peel: the node plays its then-branch exactly
  when the FIRED MASS (`GuardList.massWhere` over the closed guards' oracle bits)
  reaches the threshold. Linear induction over the guard list — this is Route B's
  payoff over the 2^n decision-tree case split.
* `eval_iteTree_of_vals` — the behavioral twin for `iteTree` (TauTFTSim): same
  statement with action-valued sim guards (`simMass`) instead of provability bits.

Plus the σ-player wrappers (`tau_play_C`/`tau_play_D`) and the fuel-alignment
packaging `outcome_of_ex_plays`.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- Unfolding helper: a firing head guard contributes its weight. -/
theorem massWhere_cons_true {f : Formula → Bool} {w : Nat} {φ : Formula}
    {rest : GuardList} (h : f φ = true) :
    GuardList.massWhere f (.cons w φ rest) = w + rest.massWhere f := by
  simp [GuardList.massWhere, h]

/-- Unfolding helper: a failing head guard contributes nothing. -/
theorem massWhere_cons_false {f : Formula → Bool} {w : Nat} {φ : Formula}
    {rest : GuardList} (h : f φ = false) :
    GuardList.massWhere f (.cons w φ rest) = rest.massWhere f := by
  simp [GuardList.massWhere, h]

/-- **The peel workhorse.** If the branch selected by comparing θ against the fired
    mass evaluates to `a`, so does the `tsearch` node. Guards are consulted in list
    order at budget `k`, closed against the current frame. -/
theorem eval_tsearch_of_bits (me opponent p q : Prog) (k : Nat) (a : Action) :
    ∀ (gs : GuardList) (θ : Nat),
      (∃ N, eval N me opponent
          (if θ ≤ gs.massWhere (fun ψ => proofSearch k (ψ.subst me opponent))
           then p else q) = some a) →
      ∃ N, eval N me opponent (.tsearch k gs θ p q) = some a
  -- (equation-style recursion: the tactic `induction` refuses the mutually
  -- inductive `GuardList`; structural recursion on it is fine)
  | .nil, θ, h => by
      simp only [GuardList.massWhere] at h
      by_cases hθ : θ = 0
      · subst hθ
        rw [if_pos (Nat.le_refl 0)] at h
        obtain ⟨N, hN⟩ := h
        exact ⟨N + 1, by rw [eval_tsearch_zero N]; exact hN⟩
      · rw [if_neg (by omega)] at h
        obtain ⟨N, hN⟩ := h
        exact ⟨N + 1, by rw [eval_tsearch_nil N hθ]; exact hN⟩
  | .cons w φ rest, θ, h => by
      by_cases hθ : θ = 0
      · subst hθ
        rw [if_pos (Nat.zero_le _)] at h
        obtain ⟨N, hN⟩ := h
        exact ⟨N + 1, by rw [eval_tsearch_zero N]; exact hN⟩
      · cases hg : proofSearch k (φ.subst me opponent) with
        | true =>
            have hiff :
                (θ ≤ GuardList.massWhere (fun ψ => proofSearch k (ψ.subst me opponent))
                  (.cons w φ rest))
                ↔ θ - w ≤ rest.massWhere (fun ψ => proofSearch k (ψ.subst me opponent)) := by
              rw [massWhere_cons_true
                (f := fun ψ => proofSearch k (ψ.subst me opponent)) hg]
              omega
            rw [if_congr hiff rfl rfl] at h
            obtain ⟨N, hN⟩ := eval_tsearch_of_bits me opponent p q k a rest (θ - w) h
            exact ⟨N + 1, by rw [eval_tsearch_cons_t N hθ hg]; exact hN⟩
        | false =>
            have hiff :
                (θ ≤ GuardList.massWhere (fun ψ => proofSearch k (ψ.subst me opponent))
                  (.cons w φ rest))
                ↔ θ ≤ rest.massWhere (fun ψ => proofSearch k (ψ.subst me opponent)) := by
              rw [massWhere_cons_false
                (f := fun ψ => proofSearch k (ψ.subst me opponent)) hg]
            rw [if_congr hiff rfl rfl] at h
            obtain ⟨N, hN⟩ := eval_tsearch_of_bits me opponent p q k a rest θ h
            exact ⟨N + 1, by rw [eval_tsearch_cons_f N hθ hg]; exact hN⟩
termination_by structural gs _ _ => gs

/-- σ-player wrapper, cooperative regime: the fired mass reaches θ, so the player
    (const branches) plays C — against EVERY opponent. -/
theorem tau_play_C {k θ : Nat} {gs : GuardList} (opponent : Prog)
    (hcond : θ ≤ gs.massWhere
      (fun ψ => proofSearch k
        (ψ.subst (.tsearch k gs θ (.const .C) (.const .D)) opponent))) :
    ∃ N, play N (.tsearch k gs θ (.const .C) (.const .D)) opponent = some .C :=
  eval_tsearch_of_bits _ opponent (.const .C) (.const .D) k .C gs θ
    ⟨1, by rw [if_pos hcond]; rfl⟩

/-- σ-player wrapper, defect regime: the fired mass misses θ. -/
theorem tau_play_D {k θ : Nat} {gs : GuardList} (opponent : Prog)
    (hcond : ¬ θ ≤ gs.massWhere
      (fun ψ => proofSearch k
        (ψ.subst (.tsearch k gs θ (.const .C) (.const .D)) opponent))) :
    ∃ N, play N (.tsearch k gs θ (.const .C) (.const .D)) opponent = some .D :=
  eval_tsearch_of_bits _ opponent (.const .C) (.const .D) k .D gs θ
    ⟨1, by rw [if_neg hcond]; rfl⟩

/-- Package two existential plays into an existential outcome (fuel aligned by
    monotonicity). -/
theorem outcome_of_ex_plays {A B : Prog} {a b : Action}
    (hA : ∃ N, play N A B = some a) (hB : ∃ N, play N B A = some b) :
    ∃ N, outcome N A B = some (a, b) := by
  obtain ⟨N₁, h₁⟩ := hA
  obtain ⟨N₂, h₂⟩ := hB
  refine ⟨max N₁ N₂, ?_⟩
  have h₁' : play (max N₁ N₂) A B = some a := eval_mono_le h₁ _ (Nat.le_max_left _ _)
  have h₂' : play (max N₁ N₂) B A = some b := eval_mono_le h₂ _ (Nat.le_max_right _ _)
  simp [outcome, h₁', h₂']

/-! ## The behavioral twin (TauTFTSim's `iteTree`) -/

/-- Fired mass of weighted action-guards under a valuation of the guard programs. -/
def simMass (val : Prog → Action) : List (Nat × Prog) → Nat
  | [] => 0
  | (w, g) :: rest => (if val g == Action.C then w else 0) + simMass val rest

/-- **The ite-tree workhorse**: if every guard in `L` evaluates (at some fuel) to its
    valuation, the tree plays C exactly when the C-mass reaches θ. -/
theorem eval_iteTree_of_vals (me opponent : Prog) (val : Prog → Action) :
    ∀ (L : List (Nat × Prog)) (θ : Nat),
      (∀ wg ∈ L, ∃ N, eval N me opponent wg.2 = some (val wg.2)) →
      ∃ N, eval N me opponent (iteTree L θ)
        = some (if θ ≤ simMass val L then Action.C else Action.D) := by
  intro L
  induction L with
  | nil =>
      intro θ _
      cases θ with
      | zero => exact ⟨1, by simp [iteTree, simMass, eval]⟩
      | succ m => exact ⟨1, by simp [iteTree, simMass, eval]⟩
  | cons wg rest ih =>
      obtain ⟨w, g⟩ := wg
      intro θ hvals
      cases θ with
      | zero => exact ⟨1, by simp [iteTree, simMass, eval]⟩
      | succ m =>
          obtain ⟨Ng, hNg⟩ := hvals (w, g) (List.mem_cons_self ..)
          have hrest : ∀ wg ∈ rest, ∃ N, eval N me opponent wg.2 = some (val wg.2) :=
            fun wg hm => hvals wg (List.mem_cons_of_mem _ hm)
          cases hv : val g with
          | C =>
              rw [hv] at hNg
              obtain ⟨Nb, hNb⟩ := ih (m + 1 - w) hrest
              refine ⟨max Ng Nb + 1, ?_⟩
              show eval (max Ng Nb + 1) me opponent
                (.ite g Action.C (iteTree rest (m + 1 - w)) (iteTree rest (m + 1)))
                = _
              rw [eval, eval_mono_le hNg _ (Nat.le_max_left _ _)]
              simp only [bind, Option.bind, BEq.beq]
              rw [eval_mono_le hNb _ (Nat.le_max_right _ _)]
              have hiff : (m + 1 - w ≤ simMass val rest)
                  ↔ (m + 1 ≤ simMass val ((w, g) :: rest)) := by
                have hw : (if (Action.C == Action.C) = true then w else 0) = w :=
                  if_pos rfl
                simp only [simMass, hv, hw]
                omega
              rw [if_congr hiff rfl rfl]
              exact if_pos rfl
          | D =>
              rw [hv] at hNg
              obtain ⟨Nb, hNb⟩ := ih (m + 1) hrest
              refine ⟨max Ng Nb + 1, ?_⟩
              show eval (max Ng Nb + 1) me opponent
                (.ite g Action.C (iteTree rest (m + 1 - w)) (iteTree rest (m + 1)))
                = _
              rw [eval, eval_mono_le hNg _ (Nat.le_max_left _ _)]
              simp only [bind, Option.bind, BEq.beq]
              rw [eval_mono_le hNb _ (Nat.le_max_right _ _)]
              have hiff : (m + 1 ≤ simMass val rest)
                  ↔ (m + 1 ≤ simMass val ((w, g) :: rest)) := by
                have hw : (if (Action.D == Action.C) = true then w else 0) = 0 :=
                  if_neg (by decide)
                simp only [simMass, hv, hw]
                omega
              rw [if_congr hiff rfl rfl]
              exact if_neg (by decide)

end PD.Tau
