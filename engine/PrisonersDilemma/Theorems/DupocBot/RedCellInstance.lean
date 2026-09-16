import PrisonersDilemma.Base.RedCellFramework
import PrisonersDilemma.Base.Transpose
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.DupocBot.Helpers

/-!
# `Theorems/DupocBot/RedCellInstance` — the red cell through the abstract framework, in `S`

`Base/RedCellFramework.lean` proves `(Dupoc, Cupod) = (D, C)` once, over a hypothesis
package. This file instantiates the package with the engine: sentences are `Formula`,
bounded derivability is `Pf`, the transposition is `Formula.transpose` (an involution,
`Pf.transpose` is its same-budget closure), the plays are `play`, the two guards are
the substituted `.search` guards of `DupocBot k`/`CupodBot k`, and soundness /
determinism are `Pf_sound` / `play_unique`. `red_cell_engine` is then one application
of the abstract theorem — the SAME argument `outcome_DupocBot_vs_CupodBot` makes by
hand, now shared with the arithmetized instance (`arith/ArithS/RedCellInstance.lean`).
-/

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- Dupoc's guard fires: `⊢_k "Cupod plays C vs Dupoc"` makes Dupoc play `C` (fuel 2). -/
theorem DupocBot_fires_vs_CupodBot (k : Nat)
    (h : Pf k (.plays (CupodBot k) (DupocBot k) .C)) :
    play 2 (DupocBot k) (CupodBot k) = some .C := by
  have hps : proofSearch k (.plays (CupodBot k) (DupocBot k) .C) = true :=
    (proofSearch_spec _ _).2 h
  show eval 2 (DupocBot k) (CupodBot k) (DupocBot k) = some .C
  unfold DupocBot at hps ⊢
  simp [eval, Prog.subst, Formula.subst, hps]

/-- Dupoc's else-branch: no derivation of its guard makes Dupoc play `D` (fuel 2). -/
theorem DupocBot_else_vs_CupodBot (k : Nat)
    (h : ¬ Pf k (.plays (CupodBot k) (DupocBot k) .C)) :
    play 2 (DupocBot k) (CupodBot k) = some .D := by
  have hps : proofSearch k (.plays (CupodBot k) (DupocBot k) .C) = false := by
    cases hh : proofSearch k (.plays (CupodBot k) (DupocBot k) .C) with
    | true => exact absurd ((proofSearch_spec _ _).1 hh) h
    | false => rfl
  show eval 2 (DupocBot k) (CupodBot k) (DupocBot k) = some .D
  unfold DupocBot at hps ⊢
  simp [eval, Prog.subst, Formula.subst, hps]

/-- Cupod's guard fires: `⊢_k "Dupoc plays D vs Cupod"` makes Cupod play `D` (fuel 2). -/
theorem CupodBot_fires_vs_DupocBot (k : Nat)
    (h : Pf k (.plays (DupocBot k) (CupodBot k) .D)) :
    play 2 (CupodBot k) (DupocBot k) = some .D := by
  have hps : proofSearch k (.plays (DupocBot k) (CupodBot k) .D) = true :=
    (proofSearch_spec _ _).2 h
  show eval 2 (CupodBot k) (DupocBot k) (CupodBot k) = some .D
  unfold CupodBot at hps ⊢
  simp [eval, Prog.subst, Formula.subst, hps]

/-- Cupod's else-branch: no derivation of its guard makes Cupod play `C` (fuel 2). -/
theorem CupodBot_else_vs_DupocBot (k : Nat)
    (h : ¬ Pf k (.plays (DupocBot k) (CupodBot k) .D)) :
    play 2 (CupodBot k) (DupocBot k) = some .C := by
  have hps : proofSearch k (.plays (DupocBot k) (CupodBot k) .D) = false := by
    cases hh : proofSearch k (.plays (DupocBot k) (CupodBot k) .D) with
    | true => exact absurd ((proofSearch_spec _ _).1 hh) h
    | false => rfl
  show eval 2 (CupodBot k) (DupocBot k) (CupodBot k) = some .C
  unfold CupodBot at hps ⊢
  simp [eval, Prog.subst, Formula.subst, hps]

/-- **The engine instance** of the red-cell package: `Pf` over `Formula`, transposed
    by `Formula.transpose`, played by `play`. -/
noncomputable def pfRedCell : RedCellFramework where
  Act := Action
  C := .C
  D := .D
  hCD := by decide
  Sent := Formula
  Prov := Pf
  τ := Formula.transpose
  τ_invol := Formula.transpose_transpose
  prov_swap := fun _ _ h => Pf.transpose h
  playA := fun k a => ∃ n, play n (DupocBot k) (CupodBot k) = some a
  playB := fun k b => ∃ n, play n (CupodBot k) (DupocBot k) = some b
  ρ₁ := fun k => .plays (CupodBot k) (DupocBot k) .C
  ρ₂ := fun k => .plays (DupocBot k) (CupodBot k) .D
  mirror := rho1_transpose
  fireA := fun k h => ⟨2, DupocBot_fires_vs_CupodBot k h⟩
  elseA := fun k h => ⟨2, DupocBot_else_vs_CupodBot k h⟩
  fireB := fun k h => ⟨2, CupodBot_fires_vs_DupocBot k h⟩
  elseB := fun k h => ⟨2, CupodBot_else_vs_DupocBot k h⟩
  sound₂ := fun k h => by simpa [Formula.interp] using Pf_sound _ _ h
  detA := fun _ _ _ ⟨_, hn⟩ ⟨_, hm⟩ => play_unique hn hm
  detB := fun _ _ _ ⟨_, hn⟩ ⟨_, hm⟩ => play_unique hn hm

/-- **The red cell in `S`, via the framework**: at every shared budget `k`, Dupoc plays
    `D` and Cupod plays `C` at some fuel. -/
theorem red_cell_engine (k : Nat) :
    (∃ n, play n (DupocBot k) (CupodBot k) = some .D) ∧
    (∃ n, play n (CupodBot k) (DupocBot k) = some .C) :=
  pfRedCell.red_cell k

/-- The framework's negative half is the engine's `not_Pf_dupoc_guard`/`not_Pf_cupod_guard`. -/
example (k : Nat) :
    ¬ Pf k (.plays (CupodBot k) (DupocBot k) .C) ∧ ¬ Pf k (.plays (DupocBot k) (CupodBot k) .D) :=
  pfRedCell.guards_fail k

/-- Agreement with the hand-proven cell: the framework's fuel witness is lifted to the
    literal pad `2` of `outcome_DupocBot_vs_CupodBot` by fuel determinism. -/
example (k : Nat) : ∀ fuel, play (fuel + 2) (DupocBot k) (CupodBot k) = some .D :=
  play_at_of_ex (red_cell_engine k).1 ⟨_, DupocBot_plays_D_vs_CupodBot k 0⟩

example (k : Nat) : ∀ fuel, play (fuel + 2) (CupodBot k) (DupocBot k) = some .C :=
  play_at_of_ex (red_cell_engine k).2 ⟨_, CupodBot_plays_C_vs_DupocBot k 0⟩

end PD.Theorems
