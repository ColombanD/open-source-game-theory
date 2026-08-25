import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Theorems.CupodBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! ### The red cell — Dupoc × Cupod, resolved by the τ-transposition (2026-08-20)

The matchup Critch–Dennis–Russell 2022 leave open (the tau/EGT layer had to
stipulate it). Theorem 1.14 of `latex/Cupod_vs_Dupco_proof.tex`: Cupod is the
τ̂-transpose of Dupoc (`Base/Transpose`), so their substituted guards are each
other's τ-images and `□_k ρ₁ ⟺ □_k ρ₂` at the SAME budget (`Pf.transpose`).
If either held, Dupoc's play would be both `C` (its guard fires) and `D` (the
τ-image is sound) — `eval` determinism refutes it. Both guards fail at every
budget, both bots fall through to their defaults: `(D, C)`, for EVERY `k`,
same budget on both sides. Machinery: `Theorems/DupocBot/Helpers.lean`
(`not_Pf_dupoc_guard` and friends). No floor census, no exclusion machinery —
and the negative half is robust to ANY τ-symmetric extension of `S`, since it
uses only soundness + τ-closure, never the constructor list. -/

/-- **The red cell** — `outcome(Dupoc(k), Cupod(k)) = (D, C)` at every budget
    `k` (same on both sides) and every sufficient fuel: the searcher defects,
    the cooperator cooperates — the symmetric guard pair annihilates itself
    (paper Thm 1.14; the `(C, D)` orientation is derived by the matrix loader). -/
@[outcome]
theorem outcome_DupocBot_vs_CupodBot :
    OutcomeSpec .universal 2
      DupocBot CupodBot (some (.D, .C)) := by
  intro k fuel
  have hA := DupocBot_plays_D_vs_CupodBot k fuel
  have hB := CupodBot_plays_C_vs_DupocBot k fuel
  simp [outcome, hA, hB]

/-- The mirror orientation, for the record (the app's matrix loader derives it
    by swapping — deliberately an `example`, not a scanned second theorem). -/
example (k fuel : Nat) :
    outcome (fuel + 2) (CupodBot k) (DupocBot k) = some (.C, .D) := by
  have hA := CupodBot_plays_C_vs_DupocBot k fuel
  have hB := DupocBot_plays_D_vs_CupodBot k fuel
  simp [outcome, hA, hB]

/-! ### Audit cross-checks (ported from the promotion audit, 2026-08-19)

Kernel-computed Def-1.11 checks, the k = 0 edge (the τ-argument needs no
largeness assumption, unlike the Löb results), and the DIFFERENTIAL TEST:
`Pf.transpose` maps the two INDEPENDENTLY hand-proven Löb premises
(`dupoc_loeb_premise` ⟷ `cupod_loeb_premise`) onto each other at the same
`5·log2 k + 33` transcript — two unrelated proof routes converging, and a
standing corroboration that τ̂ preserves proof length exactly. -/

example : (DupocBot 7).transpose = CupodBot 7 := by decide
example : ((DupocBot 7).transpose).transpose = DupocBot 7 := by decide
example : (Formula.plays (CupodBot 7) (DupocBot 7) .C).transpose
    = .plays (DupocBot 7) (CupodBot 7) .D := by decide

example : outcome 2 (DupocBot 0) (CupodBot 0) = some (.D, .C) :=
  outcome_DupocBot_vs_CupodBot 0 0

/-- Dupoc's Löb premise transposes to EXACTLY Cupod's (statement of
    `cupod_loeb_premise`), same transcript budget. -/
example (k : Nat) :
    Pf (5 * Nat.log2 k + 33)
      (.impl (.box k (.plays (CupodBot k) (CupodBot k) .D))
             (.plays (CupodBot k) (CupodBot k) .D)) := by
  have h := Pf.transpose (dupoc_loeb_premise k)
  simpa [Formula.transpose, Action.swap, transpose_DupocBot] using h

/-- And back: Cupod's premise transposes to Dupoc's. -/
example (k : Nat) :
    Pf (5 * Nat.log2 k + 33)
      (.impl (.box k (.plays (DupocBot k) (DupocBot k) .C))
             (.plays (DupocBot k) (DupocBot k) .C)) := by
  have h := Pf.transpose (cupod_loeb_premise k)
  simpa [Formula.transpose, Action.swap, transpose_CupodBot] using h

end PD.Theorems
