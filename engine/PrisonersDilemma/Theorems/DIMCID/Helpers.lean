import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems

/-!
# Theorems/DIMCID/Helpers — DIMCID's trust floor, generic in the opponent

DIMCID's `C` is its ELSE-slot (it fires `D` when it can prove "my cooperating
would be met with defection"), so any certificate of that cooperation must cross
`search_f` and pay the full failed budget. Structural — no hypothesis about the
guard, and the opponent is arbitrary.

The twin of `no_provable_CupodBot_C_tail` (`Theorems/CupodBot/Helpers`), at the
opposite polarity: predicted by the tau layer's alignment rule, transplanted to
the base shape (2026-08-21).
-/

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- No proof of ≤ k characters concludes any formula whose guarded spine tail is
    "DIMCID plays C against O": `search_t` concludes the then-constant `.D`
    (action mismatch), `search_f` pays the floor. -/
theorem no_provable_DIMCID_C_tail (k : Nat) (O : Prog) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (DIMCID k) O .C) φ → False := by
  intro K φ hp hK ht
  refine no_provable_tailToS_floor k (· = .plays (DIMCID k) O .C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 ht)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · intro K' hK' φ' hφ'
    cases hφ'
    intro hA
    cases hA with
    | mk hpp hn =>
      unfold DIMCID at hpp
      cases hpp with
      | search_t hProv hbr => cases hbr
      | search_f hneg hbr => simp only [c_node] at hn; omega
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    unfold DIMCID at hme
    injection hme with e1 e2 e3 e4
    simp at e3
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3
    subst h1
    unfold DIMCID at hme; simp at hme
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3
    subst h1
    unfold DIMCID at hme; simp at hme
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3
    subst h1
    unfold DIMCID at hme; simp at hme
  · intro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3
    unfold DIMCID at h1; simp at h1
  · intro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3
    subst h1
    unfold DIMCID at hme; simp at hme
  · intro me oppo c hS L hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    cases L with
    | nil => unfold DIMCID at hme; simp [searchPlug] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        unfold DIMCID at hme
        simp only [searchPlug, Prog.search.injEq] at hme
        have hcontra := hme.2.2.1
        rw [searchPlug_eq_ctxPlug tl (.const .C)] at hcontra
        exact const_ne_ctxPlug (by decide) _ hcontra
  · intro me oppo c hS hd L hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    exfalso
    cases hd with
    | searchL g ψ e =>
        unfold DIMCID at hme
        simp only [ctxPlug, Prog.search.injEq] at hme
        have hcontra := hme.2.2.1
        exact const_ne_ctxPlug (by decide) L hcontra
    | iteL z aT other => unfold DIMCID at hme; simp [ctxPlug] at hme
  · -- polarity plug: DIMCID's C IS its else-slot — the matching `elseL`
    -- decomposition pays DIMCID's own floor `k`; the `thenL` route dead-ends
    intro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases hd with
    | thenL g ψ e =>
        simp only [plug2, DIMCID, Prog.search.injEq] at hme
        obtain ⟨-, -, hplug, -⟩ := hme
        exfalso
        cases L with
        | nil => simp [plug2] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [plug2] at hplug
    | elseL g P' Q' c' q =>
        simp only [plug2, DIMCID, Prog.search.injEq] at hme
        obtain ⟨rfl, -, -, -⟩ := hme
        simp only [layersCost, layerCost, c_node]
        omega
  · intro me oppo c hS defs i _ _ _ hme _
    injection hS with h1 h2 h3
    subst h1
    unfold DIMCID at hme; simp at hme
  · -- hbotsysrun: the `.sys` RUN twin, same shape kill
    intro me oppo c hS defs i _ _ _ hme _
    injection hS with h1 h2 h3
    subst h1
    unfold DIMCID at hme; simp at hme

end PD.Theorems
