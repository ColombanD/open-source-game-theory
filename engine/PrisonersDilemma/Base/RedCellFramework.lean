/-!
# `Base/RedCellFramework` — the red cell, once, over a hypothesis package

`Dupoc` (cooperate iff I can prove you cooperate with me, else defect) against `Cupod`
(defect iff I can prove you defect against me, else cooperate) at a SHARED budget is
`(D, C)`, and the argument needs only: the C/D transposition `τ` is an involution on
sentences, derivations transpose at the SAME budget (exact search symmetry), and
provable guards are true (soundness) — nothing about the rules. This file states it
ONCE over the abstract package `RedCellFramework` (the note's (H0)–(H6)), instantiated
by the engine's `S` (`Theorems/DupocBot/RedCellInstance.lean`) and by PA-`S'`
(`arith/ArithS/RedCellInstance.lean`). The §6.1 table is split into named theorems:
symmetry alone excludes `(C, C)`/`(D, D)`, soundness excludes `(C, D)`, `(D, C)` remains.
Imports nothing; every theorem is axiom-free.
-/

namespace PD

/-- The red-cell hypothesis package (the note's (H0)–(H6), abstracted). -/
structure RedCellFramework where
  Act : Type
  C : Act
  D : Act
  hCD : C ≠ D
  Sent : Type
  /-- bounded derivability `□_k` -/
  Prov : Nat → Sent → Prop
  /-- the C/D transposition on sentences -/
  τ : Sent → Sent
  τ_invol : ∀ φ, τ (τ φ) = φ
  /-- (H1)+(H5): length-preserving transposition of proofs -/
  prov_swap : ∀ k φ, Prov k φ → Prov k (τ φ)
  /-- the two plays of the match at budget `k` (Dupoc's action, Cupod's action) -/
  playA : Nat → Act → Prop
  playB : Nat → Act → Prop
  /-- the two guard sentences: `ρ₁ k` = "Cupod k plays C against Dupoc k",
      `ρ₂ k` = "Dupoc k plays D against Cupod k" -/
  ρ₁ : Nat → Sent
  ρ₂ : Nat → Sent
  /-- (H3)+(H4)+(H6a): mirroring -/
  mirror : ∀ k, τ (ρ₁ k) = ρ₂ k
  /-- (H6b): Dupoc fires on its guard, defaults to D -/
  fireA : ∀ k, Prov k (ρ₁ k) → playA k C
  elseA : ∀ k, ¬ Prov k (ρ₁ k) → playA k D
  /-- (H6c): Cupod fires on its guard, defaults to C -/
  fireB : ∀ k, Prov k (ρ₂ k) → playB k D
  elseB : ∀ k, ¬ Prov k (ρ₂ k) → playB k C
  /-- (H2)+(H4): soundness at the one instance the argument needs — a provable `ρ₂` is TRUE -/
  sound₂ : ∀ k, Prov k (ρ₂ k) → playA k D
  /-- determinism of the two plays (the note folds both into (H0)'s "the evaluator is
      a function"; `detB` is what lets symmetry ALONE read Cupod's play back into its
      guard, so the §6.1 table splits cleanly) -/
  detA : ∀ k a a', playA k a → playA k a' → a = a'
  detB : ∀ k b b', playB k b → playB k b' → b = b'

namespace RedCellFramework

variable (F : RedCellFramework)

/-- `τ (ρ₂ k) = ρ₁ k` — from `mirror` and the involution. -/
theorem mirror' (k : Nat) : F.τ (F.ρ₂ k) = F.ρ₁ k := by
  rw [← F.mirror k, F.τ_invol]

/-- **Exact search symmetry** (uses `prov_swap`, `mirror`, `τ_invol` only): the two
    guards are derivable together or not at all, at the SAME budget. -/
theorem search_symmetry (k : Nat) : F.Prov k (F.ρ₁ k) ↔ F.Prov k (F.ρ₂ k) :=
  ⟨fun h => F.mirror k ▸ F.prov_swap k _ h,
   fun h => F.mirror' k ▸ F.prov_swap k _ h⟩

/-- Reading the plays back into the guards (determinism + the fire/else clauses). -/
theorem not_prov₂_of_playB_C (k : Nat) (hB : F.playB k F.C) : ¬ F.Prov k (F.ρ₂ k) :=
  fun h₂ => F.hCD (F.detB k _ _ hB (F.fireB k h₂))

theorem not_prov₁_of_playA_D (k : Nat) (hA : F.playA k F.D) : ¬ F.Prov k (F.ρ₁ k) :=
  fun h₁ => F.hCD (F.detA k _ _ (F.fireA k h₁) hA)

theorem prov₁_stable_of_playA_C (k : Nat) (hA : F.playA k F.C) : ¬ ¬ F.Prov k (F.ρ₁ k) :=
  fun h₁ => F.hCD (F.detA k _ _ hA (F.elseA k h₁))

theorem prov₂_stable_of_playB_D (k : Nat) (hB : F.playB k F.D) : ¬ ¬ F.Prov k (F.ρ₂ k) :=
  fun h₂ => F.hCD (F.detB k _ _ (F.elseB k h₂) hB)

/-- **`(C, C)` is excluded by symmetry alone** (`search_symmetry`, `elseA`, `fireB`,
    `detA`, `detB`, `hCD`; NO soundness): Cupod plays `C` only when its guard fails
    (`fireB` + `detB`), so by symmetry Dupoc's fails too and Dupoc plays `D`
    (`elseA`), not `C` (`detA`). Axiom-free. -/
theorem not_CC (k : Nat) : ¬ (F.playA k F.C ∧ F.playB k F.C) := fun ⟨hA, hB⟩ =>
  F.prov₁_stable_of_playA_C k hA
    (fun h₁ => F.not_prov₂_of_playB_C k hB ((F.search_symmetry k).1 h₁))

/-- **`(D, D)` is excluded by symmetry alone** (`search_symmetry`, `fireA`, `elseB`,
    `detA`, `detB`, `hCD`; NO soundness): Cupod plays `D` only when its guard fires
    (`elseB` + `detB`), so by symmetry Dupoc's fires too and Dupoc plays `C`
    (`fireA`), not `D` (`detA`). Axiom-free. -/
theorem not_DD (k : Nat) : ¬ (F.playA k F.D ∧ F.playB k F.D) := fun ⟨hA, hB⟩ =>
  F.prov₂_stable_of_playB_D k hB
    (fun h₂ => F.not_prov₁_of_playA_D k hA ((F.search_symmetry k).2 h₂))

/-- **`(C, D)` is excluded by soundness** (`sound₂`, `fireA`, `elseA`, `search_symmetry`,
    `detA`, `hCD`): Dupoc plays `C` only if its guard fires; then its τ-image `ρ₂` is
    derivable at the same budget and — being SOUND — true, so Dupoc plays `D` as well
    as `C`. Axiom-free. -/
theorem not_CD (k : Nat) : ¬ (F.playA k F.C ∧ F.playB k F.D) := fun ⟨hA, _⟩ =>
  F.prov₁_stable_of_playA_C k hA
    (fun h₁ => F.hCD (F.detA k _ _ hA (F.sound₂ k ((F.search_symmetry k).1 h₁))))

/-- **Both guards fail at every budget**: `□_k ρ₁` would make Dupoc play `C` (`fireA`)
    while its τ-image `□_k ρ₂` is sound and makes Dupoc play `D` (`sound₂`) — determinism
    refutes it; `ρ₂` follows by symmetry. -/
theorem guards_fail (k : Nat) : ¬ F.Prov k (F.ρ₁ k) ∧ ¬ F.Prov k (F.ρ₂ k) := by
  have h₁ : ¬ F.Prov k (F.ρ₁ k) := fun h =>
    F.hCD (F.detA k _ _ (F.fireA k h) (F.sound₂ k ((F.search_symmetry k).1 h)))
  exact ⟨h₁, fun h => h₁ ((F.search_symmetry k).2 h)⟩

/-- **The red cell**: at every shared budget `k`, Dupoc plays `D` and Cupod plays `C`
    (`guards_fail` + the two else-branches). -/
theorem red_cell (k : Nat) : F.playA k F.D ∧ F.playB k F.C :=
  ⟨F.elseA k (F.guards_fail k).1, F.elseB k (F.guards_fail k).2⟩

end RedCellFramework

end PD
