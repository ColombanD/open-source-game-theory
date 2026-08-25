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
  -- An instance of the bare else-floor edition `no_provable_searcherElse_tail`
  -- (2026-08-25; formerly a 95-line hand-rolled kernel instantiation — the SAME
  -- census the tau layer's `.bot`/`.sys` editions run, one library for both).
  intro K φ hp hK ht
  exact no_provable_searcherElse_tail k (.impl (.plays .self .opp .C) (.plays .opp .self .D)) .D .C (by decide) O K φ hp hK
    (by simpa only [DIMCID] using ht)

end PD.Theorems
