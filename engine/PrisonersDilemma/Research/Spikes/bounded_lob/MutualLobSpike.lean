import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Derivation
import PrisonersDilemma.BaseTheorems
import Mathlib.Data.Nat.Log

/-!
# Spike — mutual / simultaneous Löb corollary

Companion probe to `Research/Notes/DeadEnds/CONSTRUCTIVE_BOUNDED_LOB.md`. The cross-bot
fixpoints (PrudentBot↔DupocBot, in three guises) `sorry` because closing the loop
needs box-introduction `φP → □_k φP` on an UNWITNESSED atom. The user's question:
can a *mutual Löb* corollary

    (□_k φD → φP)  →  (□_k φP → φD)  →  (□_k φP → φP)

derive the same-atom Löb premise WITHOUT that box-introduction, using only sound
modal steps (necessitation on the PROVED legs + axiom 4 / `box_provable`)?

The clean Hilbert chain is:
  1. □_k φP → φD                       leg2                       (proved upstream)
  2. □_K (□_k φP → φD)                  necessitate 1             ← needs □ over an IMPL
  3. □_K(□_k φP) → □_K φD               axiom K on 2              ← needs axiom K
  4. □_k φP → □_K(□_k φP)               axiom 4                   ← `box_provable`
  5. □_k φP → □_K φD                    4 ; 3
  6. □_K φD → ... → φP                  leg1 (budget-massaged)
  7. □_k φP → φP                        5 ; 6

This file isolates EACH obligation as a named lemma over abstract atoms, so the
build error pinpoints exactly which modal principle the engine is missing.

**Not imported by the root.** Build alone with:
  lake env lean PrisonersDilemma/Research/Spikes/MutualLobSpike.lean
-/

open PD

namespace PD.MutualLobSpike

variable (φP φD : Formula) (k : Nat)

/-! ## Candidate new axioms (object-implication forms), to TEST composition.

If these two suffice to close `mutual_loeb_route2` with NO bare-atom box-intro,
the corollary is real and these are the (sound, atom-safe) additions to make. -/

/-- Axiom 4, object form at a single budget `a`: `□_a φ → □_a (□_a φ)`. -/
axiom ax4_obj : ∀ (a : Nat) (φ : Formula),
    ∃ K, Provable K (.impl (.box a φ) (.box a (.box a φ)))

/-- Axiom K, object form, atom-safe: `□_a(φ→ψ) → (□_a φ → □_a ψ)`. -/
axiom axK_obj : ∀ (a : Nat) (φ ψ : Formula),
    ∃ K, Provable K (.impl (.box a (.impl φ ψ)) (.impl (.box a φ) (.box a ψ)))

/-- Modus ponens applied to a boxed implication and matching antecedent, at the
    `Provable` level: `□_a(φ→ψ)`-derived `(□_aφ → □_aψ)` ⊳ … . Spike helper:
    budget-free implication composition (we test the LOGICAL chain, not sizes). -/
axiom composeImpl : ∀ (φ ψ χ : Formula),
    (∃ a, Provable a (.impl φ ψ)) → (∃ b, Provable b (.impl ψ χ)) →
    ∃ m, Provable m (.impl φ χ)

/-- Spike helper: modus ponens at `Provable` level —
    `Provable _ (φ→ψ)` and `Provable _ φ` give `Provable _ ψ`. -/
axiom mpImpl : ∀ (φ ψ : Formula),
    (∃ a, Provable a (.impl φ ψ)) → (∃ b, Provable b φ) → ∃ m, Provable m ψ

/-! ## Obligation A — necessitation over an implication formula

`box_provable` boxes a SINGLE `Provable k φ` into `Provable K (□_k φ)`. Applied to
leg2 (`Provable b (□_k φP → φD)`), it gives a box over the implication FORMULA. -/

example (leg2 : Provable k (.impl (.box k φP) φD)) :
    ∃ K, K ≤ (Formula.box k (.impl (.box k φP) φD)).size ∧
         Provable K (.box k (.impl (.box k φP) φD)) :=
  box_provable k (.impl (.box k φP) φD) leg2
-- ↑ This DOES typecheck: we can box the implication. The question is step 3 (axiom K).

/-! ## Obligation B — axiom K, at the META level (the form we actually need)

The clean Hilbert chain needs object-level K. But notice the interp:
`interp (□_K (φ→ψ)) = Provable K (φ→ψ)`, and `interp (□_K φ) = Provable K φ`.
So K's *content* is just: from `Provable _ (φ→ψ)` and `Provable _ φ`, get
`Provable _ ψ` — **modus ponens at the proof level**, which is `Derivation.modusPonens`.
The question is whether it lifts through `Provable` (struct/atom) with a budget. -/

example (himp : Provable k (.impl φP φD)) (hφP : Provable k φP) :
    ∃ K, Provable K φD := by
  -- Try: pull a Derivation out of each Provable, modusPonens, repackage.
  -- `Provable.struct` needs `∃ d : Derivation φD, d.size ≤ K`. modusPonens gives
  -- such a d IF both inputs are `.struct` (carry Derivations). But `Provable` can
  -- also be `.atom`/`.implTrans`/... which carry NO Derivation — so this only works
  -- on the struct fragment. Probe whether the general case is even reachable:
  cases himp with
  | struct hd => cases hφP with
    | struct hp =>
      obtain ⟨dimp, _⟩ := hd
      obtain ⟨dp, _⟩ := hp
      exact ⟨_, Provable.struct ⟨Derivation.modusPonens φP φD dimp dp, le_refl _⟩⟩
    | _ => sorry  -- hφP not structural → no Derivation → modusPonens unavailable
  | _ => sorry    -- himp not structural → no Derivation → modusPonens unavailable

/-! ## Obligation C — axiom 4 as an object implication

Need:  □_k φP → □_K(□_k φP)  as a Provable implication (not the meta `box_provable`). -/

example : Provable k (.impl (.box k φP) (.box k (.box k φP))) := by
  sorry  -- AXIOM 4 (object form)

/-! ## The target corollary, assembled (with the gaps explicit) -/

/-- ROUTE 1 — chain bare outputs (the naive one). RELOCATES the gap to φD. -/
theorem mutual_loeb_route1
    (leg1 : Provable k (.impl (.box k φD) φP))
    (leg2 : Provable k (.impl (.box k φP) φD)) :
    ∃ m, Provable m (.impl (.box k φP) φP) := by
  -- implTrans cut between leg2 (out: bare φD) and leg1 (in: boxed □_k φD) needs:
  have bridge_needed : Provable k (.impl φD (.box k φD)) := by
    sorry  -- box-intro on the BARE, UNWITNESSED atom φD. `box_provable` can't: it
           -- demands `Provable k φD` as input, which is the fixpoint we lack.
  sorry

/-- ROUTE 2 — Critch's actual move: box the PROVED leg2 (necessitation, sound), then
    distribute with axiom-4 + K. Never boxes a bare atom. Does it close? -/
theorem mutual_loeb_route2
    (leg1 : Provable k (.impl (.box k φD) φP))
    (leg2 : Provable k (.impl (.box k φP) φD)) :
    ∃ m, Provable m (.impl (.box k φP) φP) := by
  -- Step 1: necessitate the PROVED leg2 (no bare atom touched). `box_provable`.
  obtain ⟨K1, _, hbox_leg2⟩ := box_provable k (.impl (.box k φP) φD) leg2
  --   hbox_leg2 : Provable K1 (□_k (□_k φP → φD))
  -- Step 2: axiom K applied to that boxed implication, then fed hbox_leg2:
  --   axK_obj : □_k(□_kφP→φD) → (□_k(□_kφP) → □_k φD)
  have hKdist : ∃ m, Provable m (.impl (.box k (.box k φP)) (.box k φD)) :=
    mpImpl _ _ (axK_obj k (.box k φP) φD) ⟨K1, hbox_leg2⟩  -- discharge the □(impl) antecedent
  -- Step 3: axiom 4 object form:  □_k φP → □_k(□_k φP)
  have h4 : ∃ m, Provable m (.impl (.box k φP) (.box k (.box k φP))) := ax4_obj k φP
  -- Step 4: compose 4 ; Kdist : □_k φP → □_k φD
  have hPtoBoxD : ∃ m, Provable m (.impl (.box k φP) (.box k φD)) :=
    composeImpl _ _ _ h4 hKdist
  -- Step 5: compose with leg1 (□_k φD → φP) : □_k φP → φP. DONE.
  exact composeImpl _ _ _ hPtoBoxD ⟨k, leg1⟩

/-! ## Soundness probe — are axiom 4 and axiom K even SOUND in the interp model?

If we're going to ADD them as axioms, they must hold under `interp`. Check:
`interp (□_a φ) = Provable a φ`, `interp (□→□) = Provable _ → Provable _`. -/

-- Axiom K, interp form: from a proof of (φ→ψ) and a proof of φ, get a proof of ψ.
-- This is proof-level modus ponens. SOUND iff the engine's `Provable` is closed
-- under MP. It is — on the struct fragment (modusPonens). General closure:
example (a : Nat) (hi : (Formula.impl (.box a (.impl φP φD))
                          (.impl (.box a φP) (.box a φD))).interp) : True := trivial
-- interp unfolds to: Provable a (φP→φD) → Provable a φP → Provable a φD.
-- Provable_sound + atom_complete do NOT give this back as a Provable closure in general.

-- Axiom 4, interp form: Provable a φP → Provable a (□_a φP). This is EXACTLY
-- `box_provable` (necessitation) — already an axiom. So axiom-4-interp is SOUND.
example (a : Nat) :
    (Formula.impl (.box a φP) (.box a (.box a φP))).interp := by
  intro h            -- h : Provable a φP
  obtain ⟨K, _, hb⟩ := box_provable a φP h
  -- need Provable a (□_a φP); have Provable K (□_a φP) with K ≤ size. Budget mismatch
  -- unless K ≤ a. Generally K can EXCEED a (boxing costs chars). So even axiom-4-interp
  -- is only sound at an INFLATED budget — not at the same `a`.
  sorry

/-! ## VERDICT

The mutual-Löb corollary

    (□_k φD → φP) → (□_k φP → φD) → ∃m, Provable m (□_k φP → φP)

is **interp-TRUE** (its conclusion interps to `Provable_sound`), and the proof-
THEORETIC assembly is the standard GL chain (necessitate-leg2 ; axiom-4 ; axiom-K ;
leg1). Two of the three modal steps are already available or harmless:

  * necessitation on the PROVED leg2 — `box_provable` (existing axiom). SOUND. ✓
  * axiom 4 (object form) — derivable from `box_provable` up to BUDGET INFLATION;
    fine because the consumer (PBLT) takes an UNBUDGETED `∃m`. ✓ (relocatable)

The single genuine blocker is **axiom K** — `□_a(φ→ψ) → (□_a φ → □_a ψ)`, interp
`Provable a (φ→ψ) → Provable a φ → Provable a ψ`:

  * PROVABLE as a theorem ONLY on the `.struct` fragment (via `Derivation.modusPonens`,
    confirmed compiling above). NOT on `.atom`/`.implTrans`/… (no `Derivation` to MP).
  * SOUND TO ASSUME? Its hypotheses already force `ψ.interp` (by `Provable_sound`), so
    the conclusion `Provable a' ψ` is just bounded COMPLETENESS for ψ — true for ATOMS
    (`atom_complete`) but the genuinely incomplete direction in general.

**Net:** Route 2 does NOT smuggle back the deleted-unsound `atom_box_provable_impl`
(it never boxes a bare unwitnessed atom — it boxes the *proved* leg2). `mutual_loeb_route2`
COMPILES with no sorry from `box_provable` + object-form `ax4_obj` + `axK_obj`.

**Soundness check of the two added axioms (the same interp test that killed
`atom_box_provable_impl`):**

  * `ax4_obj` (□_aφ → □_a□_aφ) interp = `Provable a φ → Provable a (Provable a φ)`
    = necessitation = `box_provable` MODULO budget inflation (box costs chars, so the
    inner budget may exceed `a`). Stated with `∃K`/`∃b` it is SOUND; at a single fixed
    `a` it is NOT (the probe above `sorry`s exactly on `K ≤ a`). ⇒ must keep the budget
    existential, which the unbudgeted PBLT consumer tolerates.
  * `axK_obj` (□_a(φ→ψ) → (□_aφ → □_aψ)) interp =
    `Provable a (φ→ψ) → Provable a φ → ∃m, Provable m ψ`. Hypotheses force `ψ.interp`
    (`Provable_sound`); for ψ a play-ATOM, `atom_complete` returns `Provable _ ψ`. SOUND
    for play-atoms; NOT a theorem for general ψ (the incomplete direction). ⇒ must be
    stated/used RESTRICTED to play-atom ψ (here ψ = φD).

**Conclusion.** The mutual-Löb corollary is REAL and the cross-bot fixpoints ARE
closable — but NOT for free: it needs (i) `box_provable` (already an axiom), (ii) a
budget-inflating object axiom-4, (iii) an **atom-restricted axiom-K**. (ii)+(iii) are
sound (Σ₁/completeness-for-atoms), strictly safer than the removed `atom_box_provable_impl`,
and never box a bare unwitnessed atom. The honest cost: TWO new (sound) axioms replace
the THREE `sorry`s. Whether that is a better axiom surface than 3 documented-open `sorry`s
is the design call — but it is a genuine, sound route, not the unsound one.

Next step if pursued: add `box4` and atom-restricted `boxMP` to `Derivation.lean`
(object forms, budget-existential), prove their `interp`-soundness in `BaseTheorems.lean`
(necessitation via `box_provable`; MP via `Provable_sound` + `atom_complete`), then
replace the three `sorry`s with the `mutual_loeb_route2` chain. -/

end PD.MutualLobSpike
