import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.Helpers

open PD
open PD.Axioms
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

def antOK : Formula → Prop
  | .box _ _    => True
  | .plays _ _ _ => True
  | _           => False

def Pinv : Formula → Prop
  | .impl φ ψ    => antOK φ ∨ Pinv ψ
  | .box _ _     => False
  | .plays _ _ _ => False
  | _            => True

theorem antOK_not_Pinv {φ : Formula} (h : antOK φ) (h2 : Pinv φ) : False := by
  cases φ <;> simp_all [antOK, Pinv]

theorem deriv_Pinv : ∀ {φ}, Derivation φ → Pinv φ := by
  intro φ d
  induction d with
  | modusPonens φ ψ _ _ ih1 ih2 =>
      have ih1' : antOK φ ∨ Pinv ψ := ih1
      rcases ih1' with hant | hpsi
      · exact (antOK_not_Pinv hant ih2).elim
      · exact hpsi
  | hypSyll φ ψ χ _ _ ih1 ih2 =>
      have ih1' : antOK φ ∨ Pinv ψ := ih1
      have ih2' : antOK ψ ∨ Pinv χ := ih2
      show antOK φ ∨ Pinv χ
      rcases ih1' with hφ | hψ
      · exact Or.inl hφ
      · rcases ih2' with hψ2 | hχ
        · exact (antOK_not_Pinv hψ2 hψ).elim
        · exact Or.inr hχ
  | searchBranch k ψ a b me opponent hme => simp [Pinv, antOK]
  | simStep me p q opponent a hme => simp [Pinv, antOK]
  | botSimStep me p q opponent a hme => simp [Pinv, antOK]
  | iteBranchSearch_t k z a' c0 c1 ψ q me opponent hme => simp [Pinv, antOK]
  | eqRefl p => simp [Pinv]

theorem noAtom_CupodC (k m : Nat) :
    ¬ AtomProvable m (.plays (CupodBot k) (PrudentBot k) .C) := by
  rintro ⟨cert, _⟩
  unfold CupodBot at cert
  cases cert with
  | search_t hg hp => cases hp

theorem noAtom_PrudentD (k m : Nat) :
    ¬ AtomProvable m (.plays (PrudentBot k) (CupodBot k) .D) := by
  rintro ⟨cert, _⟩
  unfold PrudentBot at cert
  cases cert with
  | search_t hg hp =>
      cases hp with
      | search_t hg2 hp2 => cases hp2

theorem notProvable_CupodC (k m : Nat) :
    ¬ Provable m (.plays (CupodBot k) (PrudentBot k) .C) := by
  intro h
  cases h with
  | struct hd => obtain ⟨d, _⟩ := hd; have := deriv_Pinv d; simp [Pinv] at this
  | atom ha => exact noAtom_CupodC k m ha

theorem notProvable_PrudentD (k m : Nat) :
    ¬ Provable m (.plays (PrudentBot k) (CupodBot k) .D) := by
  intro h
  cases h with
  | struct hd => obtain ⟨d, _⟩ := hd; have := deriv_Pinv d; simp [Pinv] at this
  | atom ha => exact noAtom_PrudentD k m ha

theorem ps_false_CupodC (k : Nat) :
    proofSearch k (.plays (CupodBot k) (PrudentBot k) .C) = false := by
  cases hps : proofSearch k (.plays (CupodBot k) (PrudentBot k) .C) with
  | true => exact absurd ((proofSearch_spec _ _).1 hps) (notProvable_CupodC k k)
  | false => rfl

theorem ps_false_PrudentD (k : Nat) :
    proofSearch k (.plays (PrudentBot k) (CupodBot k) .D) = false := by
  cases hps : proofSearch k (.plays (PrudentBot k) (CupodBot k) .D) with
  | true => exact absurd ((proofSearch_spec _ _).1 hps) (notProvable_PrudentD k k)
  | false => rfl

theorem prudent_defects_vs_Cupod (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) (CupodBot k) = some .D := by
  have hf := ps_false_CupodC k
  show eval (fuel + 2) (PrudentBot k) (CupodBot k) (PrudentBot k) = some .D
  unfold PrudentBot at hf ⊢
  simp [eval, Prog.subst, Formula.subst, hf]

theorem cupod_coops_vs_Prudent (k fuel : Nat) :
    play (fuel + 2) (CupodBot k) (PrudentBot k) = some .C := by
  have hg := ps_false_PrudentD k
  show eval (fuel + 2) (CupodBot k) (PrudentBot k) (CupodBot k) = some .C
  unfold CupodBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

theorem llm_outcome_PrudentBot_vs_CupodBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) (CupodBot k) = some (.D, .C) := by
  refine ⟨0, fun k _ => ⟨2, ?_⟩⟩
  have hA : play 2 (PrudentBot k) (CupodBot k) = some .D := by
    simpa using prudent_defects_vs_Cupod k 0
  have hB : play 2 (CupodBot k) (PrudentBot k) = some .C := by
    simpa using cupod_coops_vs_Prudent k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
