import PrisonersDilemma.Dynamics
import PrisonersDilemma.Derivation
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.ComputableEval.PlaysCheck
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.CooperateBot

/-!
# Step 0 spike — `Provable_fin`, the falsification gate for the cycle-break

Plan: `~/.claude/plans/dazzling-coalescing-rivest.md`. Before any engine edit, test the SINGLE
riskiest assumption of Step 1: can a `Provable_fin` (a decidable, `proofSearch`-free bounded
provability predicate, defined OUTSIDE the `PlaysProof ↔ Provable` mutual block) satisfy:

  (a) WELL-FOUNDED / decidable — terminating, no `proofSearch`, `Decidable`;
  (b) FALSE at the Löb fixpoint — at CUPOD self-play it decides `false` while `Provable` is
      axiom-true (the proof-vs-witness separation);
  (c) AGREES with the real `Provable` on the false-guard fragment — `Provable_fin → Provable`.

The shipped `ppSize` (`ComputableEval/PlaysCheck.lean`) is the down-payment: it already decides the
play-atom fragment, soundly (`ppSize_sound`), and computes. So `Provable_fin` is a thin wrapper, and
this spike tests the parts `PlaysCheck` did NOT: the Löb-false fact (b) and the predicate-level
agreement (c) phrased as `Provable_fin`.

NOT root-imported. Build: `lake env lean PrisonersDilemma/Research/Spikes/ProvableFinSpike.lean`
-/

namespace PD.ProvableFinSpike
open PD PD.PlaysCheck PD.Bots

/-! ## 1. `Provable_fin` — the decidable, proofSearch-free predicate (wrapping `ppSize`)

For a PLAY-ATOM `.plays p q a`: a size-≤-k `PlaysProof` exists, decided by `ppSize`. For other
formulas (the non-false-guard fragment): `False` (out of scope — they go through the reflection
rules / `Derivation`, not the false guard). The point of `Provable_fin` is EXACTLY the fragment the
false guard reaches; it is deliberately NOT all of `Provable`. -/

def Provable_fin (k : Nat) (φ : Formula) : Prop :=
  match φ with
  | .plays p q a => ∃ s, ppSize (k+1) p q p a = some s ∧ s ≤ k
  | _            => False   -- out of the false-guard fragment

/-- (a) DECIDABLE — `Provable_fin` is decidable by a real procedure (no `proofSearch`, no Classical
    in the instance). This is what lets `search_f` carry `decide (Provable_fin …) = false`. -/
instance instDecProvableFin (k : Nat) (φ : Formula) : Decidable (Provable_fin k φ) := by
  unfold Provable_fin
  cases φ with
  | plays p q a => exact decAtomFiniteCheck k p q a
  | _ => exact isFalse (by simp)

/-! ## 2. (c) AGREEMENT — `Provable_fin k φ → Provable k φ` (on the fragment)

The new predicate only proves real things. Direct from `ppSize_sound` + `Provable.atom`. -/

theorem provableFin_sound (k : Nat) (φ : Formula) (h : Provable_fin k φ) : Provable k φ := by
  unfold Provable_fin at h
  cases φ with
  | plays p q a =>
      obtain ⟨s, hf, hsk⟩ := h
      exact Provable.atom (.mk (ppSize_sound (k+1) p q p a s hf) hsk)
  | _ => exact absurd h (by simp)

/-! ## 3. (b) FALSE AT THE LÖB FIXPOINT — the proof-vs-witness separation, machine-checked

CUPOD self-play: `CupodBot k` plays `D` vs `CupodBot k` is the canonical Löb fixpoint
(`CONSTRUCTIVE_BOUNDED_LOB.md` S3′). The atom `.plays (CupodBot k) (CupodBot k) .D` is
axiom-true in `Provable` (via `PBLT`) BUT has no finite proof term — so `Provable_fin` must decide
`false`. We check `ppSize` returns `none`/sub-budget-miss there (the finite search exhausts).

Concretely: `ppSize` at the fixpoint must NOT find a certificate (the guard recursion would need
the same atom at the same budget — S3′). We test the DECISION computes to `false`. -/

-- The fixpoint atom (CUPOD self-play defection).
abbrev cupodFix (k : Nat) : Formula := .plays (CupodBot k) (CupodBot k) .D

-- (b) machine-checked: `Provable_fin` DECIDES false at the fixpoint (finite search finds no term).
-- We pick a concrete small budget; the decision must be `false` (no finite certificate).
example : decide (Provable_fin 5 (cupodFix 3)) = false := by native_decide

/-! ## 4. The `search_f` premise is now EXPRESSIBLE and POSITIVE — the key Step-2 unblock

`search_f` would carry `decide (Provable_fin k guard) = false`. Since `Provable_fin` is a FINISHED,
decidable predicate (defined above, NOT mutually with `PlaysProof`), this premise is a Bool
equality — kernel-positive, no self-negation. We confirm a TOY `PlaysProof'` with such a constructor
typechecks (the real Step 2 adds it to the engine's `PlaysProof`). -/

inductive PPtoy : Prog → Action → Nat → Prop where
  | const : PPtoy (.const a) a 1
  -- the candidate false-guard constructor: premise is `decide (Provable_fin …) = false`, POSITIVE.
  | search_f (k : Nat) (φ : Formula) (p q : Prog) :
      decide (Provable_fin k φ) = false →
      PPtoy q a n →
      PPtoy (.search k φ p q) a (n + 1)

#check @PPtoy.search_f

/-! ## Result log — STEP 0 PASSED ✅ (decision gate: proceed with MINIMAL Prop-level Provable_fin)

All three falsification questions GREEN, machine-checked:

  (a) DECIDABLE — `instDecProvableFin` compiles; `#print axioms = [propext]` (no proofSearch, no
      Classical, no sorryAx). `Provable_fin` is a real decision procedure (wraps the shipped
      `ppSize`, `ComputableEval/PlaysCheck.lean`).
  (b) FALSE AT THE LÖB FIXPOINT — `decide (Provable_fin 5 (cupodFix 3)) = false` (by native_decide;
      `#eval` = false). At CUPOD self-play the finite search EXHAUSTS → no finite proof term →
      `false`, while `Provable` is axiom-true via `PBLT`. The proof-vs-witness separation is REAL
      and machine-located. Sanity: `Provable_fin 5 (CooperateBot plays C vs CupodBot)` = true (it
      discriminates — not vacuously false).
  (c) AGREEMENT — `provableFin_sound : Provable_fin k φ → Provable k φ`; `#print axioms =
      [propext, Quot.sound]`. The new predicate only proves real things (via `ppSize_sound` +
      `Provable.atom`).

KEY STEP-2 UNBLOCK confirmed: `PPtoy.search_f` carrying `decide (Provable_fin k φ) = false`
typechecks (kernel-POSITIVE — `Provable_fin` is a FINISHED, non-mutual predicate, so the premise is
a Bool equality, NOT `¬ PlaysProof`/`¬ Provable`). This is EXACTLY the constructor Step 2 adds to the
real `PlaysProof`. The self-negation wall that blocked every prior attempt is GONE because
`Provable_fin` is defined BEFORE the certificate type.

**DECISION GATE → take the MINIMAL Prop-level route (plan Step 1).** Well-foundedness was not even
contested — `Provable_fin` rides on `ppSize`'s structural fuel recursion (already proven total), so
no new well-founded-recursion obligation arises. The full size-INDEX refactor is NOT needed for the
axiom removal; `Provable_fin` as a thin `ppSize` wrapper suffices.

**LAYERING GREEN LIGHT (verified — the structural enabler for Step 2).** The `ppSize` DEFINITION
references ONLY `Prog`/`Formula`/`.subst`/cost constants (`c_leaf`/`c_node`/`c_guard`, already at
Derivation.lean:196–198) — ZERO references to `PlaysProof`/`Provable`/`proofSearch`/`AtomProvable`
(only the separate `ppSize_sound` theorem reaches into `PlaysProof`). So `ppSize` + `otherAction` +
`Provable_fin` + its `Decidable` instance can ALL be defined in `Derivation.lean` BEFORE the
`PlaysProof`/`Provable` mutual block. Then `PlaysProof.search_f`'s premise `decide (Provable_fin k
guard) = false` references an already-finished predicate → kernel-positive. `ppSize_sound` /
`provableFin_sound` move AFTER the block (they need `PlaysProof`). This is what makes Step 2 actually
land: the cyclic dependency is broken by RELOCATING the (cert-free) decider before the cert type.

**Caveats carried to engine promotion (Step 1–3):**
- The spike's (b) uses `native_decide` (fine for demo). In-engine soundness proofs (Step 3) must use
  the `Decidable` instance via ordinary `decide`/the instance, NOT `native_decide` (keep the kernel
  trail clean — no `Lean.ofReduceBool`).
- `Provable_fin`'s `_ => False` arm is the honest fragment boundary (play-atom only). For the
  FALSE-guard path this is already CORRECT for `.eq` too: when CupodTrollBot plays its else-branch
  (guard `.eq .opp CupodBot` FAILED, opp ≠ CupodBot), `search_f` needs the guard UNPROVABLE, and
  `_ => False` makes `decide (Provable_fin k (.eq …)) = false` ✓.
- BUT for `Provable_fin` to AGREE with `Provable` on TRUE `.eq` guards (CupodTrollBot vs CupodBot,
  plays D — routes through `atom_complete`'s TRUE branch via `search_t` + `Provable.struct
  ⟨eqRefl,…⟩`, CupodTrollBot.lean:34,62), the real `Provable_fin` SHOULD add a `.eq p q` arm:
  `decide (p = q)` (the `eqRefl` leaf). Add it in Step 1 — cheap, and makes agreement total on the
  fragment. (Not strictly needed for the false-guard removal, since that case is the true branch,
  but it keeps `Provable_fin` honest as a fragment-agreement predicate.) -/

end PD.ProvableFinSpike
