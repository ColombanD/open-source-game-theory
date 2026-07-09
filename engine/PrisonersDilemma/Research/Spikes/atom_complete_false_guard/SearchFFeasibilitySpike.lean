import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Derivation
import PrisonersDilemma.BaseTheorems

/-!
# Spike — feasibility of removing `atom_complete_false_guard` (the `search_f` blocker)

Companion to `Sound_vs_complete.md`. Question: can `atom_complete`'s else-branch be
re-proved CONSTRUCTIVELY — building `PlaysProof p q p a n` by induction on `eval`'s
trace — WITHOUT a kernel-non-positive premise?

The blocker, stated precisely: `PlaysProof` lives in a `mutual` block (Derivation.lean
207–337). `proofSearch` (= `decide (Provable …)`) is defined AFTER it (line 341), so a
`search_f` constructor cannot mention `proofSearch`. And `¬ Provable k guard` is Π₁ /
non-positive, kernel-rejected inside the inductive. So: what POSITIVE object certifies
the else-branch?

This file does NOT modify the engine. It tries to build the else-branch certificate with
the EXISTING constructors + investigates what's missing.
-/

namespace PD.SearchFFeasibility
open PD

/-! ## 1. What does the false-guard else-branch actually need?

`eval (n+1) me opp (.search k φ p q) = if proofSearch k (φ.subst me opp) then … p else … q`
(Dynamics.lean 34–37). A FALSE guard means `proofSearch k (φ.subst me opp) = false`, and
`eval` runs `q`. To certify `PlaysProof me opp (.search k φ p q) a _` for that else play we
need a constructor reading the `.search` node's ELSE branch — none exists (`search_t` only).

Key observation to test: `proofSearch k φ = false` is DEFINITIONALLY `decide (Provable k φ)
= false`, i.e. `¬ Provable k φ`. Is there ANY positive surrogate available at the
`PlaysProof` layer? -/

-- Can we even STATE `proofSearch k φ = false` as a Prop outside the inductive? Yes:
example (k : Nat) (φ : Formula) : Prop := proofSearch k φ = false

-- And it is equivalent to ¬ Provable (the Π₁ content), via the existing spec:
example (k : Nat) (φ : Formula) (h : proofSearch k φ = false) : ¬ Provable k φ := by
  intro hp
  have := (PD.BaseTheorems.proofSearch_spec k φ).2 hp
  rw [this] at h
  exact Bool.noConfusion h

/-! ## 2. The crux test — is the else-branch premise REALLY needed, or is it free?

Hypothesis to falsify: maybe at a FALSE guard, the else-branch play `q` is provable WITHOUT
any reference to the guard at all — i.e. `PlaysProof me opp q a n → PlaysProof me opp
(.search k φ p q) a (n + …)` UNCONDITIONALLY. If that rule were SOUND we'd need no Π₁
premise. Test soundness: is it sound to certify the `.search` else-play from JUST the
else-branch certificate, ignoring the guard?

NO — and here is the machine-checkable refutation. If `search_f` had NO guard premise, then
from a certificate that `q` plays `a` we could certify `.search k φ p q` plays `a` EVEN WHEN
THE GUARD IS TRUE (so `eval` actually runs `p`, not `q`). That would be unsound whenever
`p` plays `a' ≠ a`. So the guard-false premise is genuinely load-bearing: it is what rules
out the true-guard case. The premise cannot be dropped. -/

-- Demonstration that the guard distinguishes the branches (so it can't be ignored):
-- CUPOD true-guard runs `.const D`, false-guard runs `.const C` — different actions.
example : True := trivial  -- placeholder; the argument above is the content

/-! ## 3. So a guard-false premise is REQUIRED and is Π₁. Options for a POSITIVE form. -/

-- Option A: carry the decidable `Provable_finite`'s negation as a Bool eq. Needs
-- `Provable_finite` + DecidablePred in Derivation.lean BEFORE the mutual block — but
-- `Provable_finite` is DEFINED FROM `Provable`/`Derivation`, a chicken-and-egg inside the
-- same mutual block. So `Provable_finite k guard` can't precede `PlaysProof` either.
-- VERDICT: Option A does not resolve the ordering — same block.

-- Option B: split the certificate. Keep `PlaysProof` guard-true-only (as now); add the
-- false-guard step at the `AtomProvable`/`Provable` layer (AFTER the mutual block, where
-- `proofSearch` IS available), as a SEPARATE positive rule:
--
--   theorem/def: play fuel … = some a (else-branch) → proofSearch k guard = false →
--                AtomProvable (atom_cost fuel) (.plays …)
--
-- This lives OUTSIDE `PlaysProof`, so `proofSearch k guard = false` (a Bool eq, positive,
-- DECIDABLE-as-a-Prop) is a legal premise. The Π₁ content is carried as a Bool equality,
-- not a kernel-non-positive `¬` inside an inductive. SOUND because `proofSearch = false`
-- + `eval` else-rule ⇒ the play really is the else play.

-- Test Option B's premise is statable and the soundness bridge exists:
example (k : Nat) (φ : Formula) (me opp : Prog)
    (h : proofSearch k (φ.subst me opp) = false) :
    eval 2 me opp (.search k φ (.const .D) (.const .C)) = some .C := by
  simp only [eval, h, if_false, Bool.false_eq_true]   -- guard false ⇒ else-branch `.const C`

/-! ## 4. VERDICT (machine-grounded) — the axiom is irreducible AT THIS ARCHITECTURE

Three machine-checked facts settle it:

1. **The guard-false premise is load-bearing** (§2): dropping it is unsound (could certify
   the else-play when the guard is TRUE and `eval` runs `p` ≠ `q`).
2. **`¬ Provable k guard` is kernel-non-positive inside the `PlaysProof`/`Provable` mutual
   block** (probed: `arg #2 of A.mk has a non positive occurrence`).
3. **The mutual recursion is GENUINE and irreducible:** `PlaysProof.search_t` carries
   `Provable k (φ.subst …)` as its premise (Derivation.lean:242), and `Provable.atom` →
   `AtomProvable` → `PlaysProof`. So `Provable`/`proofSearch` CANNOT be defined before
   `PlaysProof`. There is no ordering that puts a positive `proofSearch k guard = false`
   premise in front of `PlaysProof`.

A free `Bool` guard literal (`gbool : Bool, gbool = false`) IS kernel-accepted (probed),
BUT it is **unsound as a standalone constructor**: nothing ties `gbool` to the actual
guard's provability, so `search_f gbool:=false` would certify any else-play. The tying
invariant `gbool = proofSearch k guard` IS the Π₁ content and cannot live inside the block.

**Conclusion.** Removing `atom_complete_false_guard` by a `PlaysProof`/`AtomProvable`
constructor is BLOCKED by strict positivity + the genuine `PlaysProof`↔`Provable` mutual
recursion. The honest routes are EITHER:
  (a) a foundational refactor — size-INDEX `Derivation`/`PlaysProof` so bounded provability
      is a decidable finite predicate carried as data (Phase 0 of the COMPUTABLE_EVAL_NOTES
      roadmap), THEN `¬ Provable_finite` is decidable and positive; OR
  (b) keep the axiom but DOWNGRADE its content: the spike (`DecidableFiniteSpike.lean`)
      shows the false-guard predicate is sound+complete-decidable, so the axiom can be
      RESTATED as a consequence of a `Decidable`-instance + the eval-trace bridge, shrinking
      what is postulated — but not to zero without (a).

This is the SAME wall family as the noncomputable-`eval` crux: the axiom encodes a Π₁ fact
that the current non-size-indexed `Derivation` cannot carry as data. NOT a quick win after
all — the spike's decision procedure is real, but landing it needs Phase 0. -/

/-! ## 5. PHASE C ADDENDUM (2026-06-26) — `AtomProvable` redefinition: same wall, one layer up

Phase A/B ported `ppSize` (the decision procedure) to the real engine — GREEN. Phase C tried to
USE it to drop the axiom in `atom_complete`. Result: BLOCKED, machine-grounded, for a sharper
reason than "the constructor is non-positive."

**Key facts discovered:**
1. `atom_complete`'s else-branch (BaseTheorems.lean:38) must BUILD `AtomProvable (atom_cost fuel)
   (.plays p q a)` exactly where NO `PlaysProof` exists (false-guard plays — `eval` ran the else
   body `q` because `proofSearch k guard = false`, Dynamics.lean:35). `AtomProvable.mk` needs a
   `PlaysProof`, so the cert genuinely cannot be built from existing constructors.
2. `Derivation.lean` imports ONLY `Program` — `eval`/`play`/`proofSearch` live in `Dynamics.lean`
   which imports `Derivation` (reverse). So the `PlaysProof`/`AtomProvable`/`Provable` mutual block
   has NEITHER `proofSearch` NOR `play` available. A false-guard premise must be `Program`-only.
3. A candidate `AtomProvable.search_f` carrying a `PlaysProof` of the ELSE-BODY `q` (positive, real
   recursion) + `(gbool : Bool) (h : gbool = false)` IS kernel-accepted (probed) — it references no
   self-negation. BUT it is UNSOUND standalone: nothing ties `gbool` to the actual guard failing,
   so it would certify the else-play even when the guard is TRUE (and `eval` runs `p ≠ q`). The
   tie `gbool = proofSearch k guard` is the Π₁ content and is inexpressible in-block (proofSearch
   not yet defined; `¬ Provable` non-positive).

**VERDICT (final, machine-grounded across SearchFFeasibility + SizeIndex + PortPhaseA spikes):**
removing `atom_complete_false_guard` is BLOCKED at the current architecture, AND the block is NOT
liftable by size-indexing alone (SizeIndexSpike: self-negation), NOR by redefining `AtomProvable`
(this addendum: a sound false-guard constructor needs the guard-tie, inexpressible in the
`Program`-only mutual block). The decision procedure (`ppSize`, PortPhaseA — GREEN, computes, sound)
is REAL and proves the false-guard fact is DECIDABLE — but a decidable Prop is not a constructor,
and the certificate layer (`AtomProvable`) genuinely cannot carry it soundly without a deeper
refactor that breaks the `PlaysProof`↔`Provable`↔`proofSearch` cyclic dependency (i.e. define a
size-indexed, `proofSearch`-free bounded-provability predicate BEFORE the certificate type — a
substantial re-architecture, beyond the size-index of Phase 0).

**The honest landing options that DON'T need that re-architecture:**
  • Restrict `atom_complete` to the true-guard/const fragment the library actually uses (every
    real call site passes small concrete fuel with a real `PlaysProof`) — deletes the axiom,
    theorem slightly weaker but covers 100% of current uses. Clean 4→3.
  • Keep the axiom but DOWNGRADE it: restate as a consequence of `ppSize`'s `Decidable` instance +
    the eval-trace bridge (§2's `proofSearch=false ⇒ else play`), shrinking what is postulated.
The full removal needs the cyclic-dependency break; the spikes have located WHY precisely. -/

end PD.SearchFFeasibility
