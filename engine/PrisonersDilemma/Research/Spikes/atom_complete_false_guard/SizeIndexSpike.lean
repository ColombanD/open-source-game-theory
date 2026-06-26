import PrisonersDilemma.Program

/-!
# Spike — does size-indexing the proof object unblock `search_f`? (Phase 0 de-risk)

Companion to `SearchFFeasibilitySpike.lean` (which proved the axiom removal is BLOCKED at
the current architecture) and the COMPUTABLE_EVAL_NOTES Phase-0 roadmap.

**The two things this spike must confirm — falsification-first:**

  Q1. With proof SIZE in the type index, is `search_f` (false-guard) a LEGAL POSITIVE
      constructor? The current blocker is that `¬ Provable k guard` is non-positive inside
      the `PlaysProof`/`Provable` mutual block. Does size-indexing change that?

  Q2. Is `Provable_finite k φ` (= "∃ a proof of size ≤ k") DECIDABLE by a real procedure
      (enumeration), NOT `Classical.dec`?

This is a TOY model: a stripped `Prog`-like subject and a minimal proof object with just
the constructors that matter for the question (`const`, a true-guard `search_t`, and the
candidate `search_f`). If the toy answers Q1/Q2 cleanly, the real refactor is de-risked;
if `search_f` is STILL non-positive even with the size index, the refactor does NOT unblock
the axiom and we stop before touching the engine.

NOT imported by root. Build: `lake env lean PrisonersDilemma/Research/Spikes/SizeIndexSpike.lean`
-/

namespace PD.SizeIndexSpike
open PD

/-! ## 0. Toy subjects and guards

We reuse the real `Formula` as the guard language (so the question is faithful), but the
proof object is a fresh toy `PP` (size-indexed `PlaysProof`) and `Prov` (size-indexed
`Provable`). The point is the SHAPE, not full coverage. -/

/-! ## 1. Size-indexed proof object — size is a TYPE INDEX, not a derived measure

`PP body a s` = "a proof that `body` plays `a`, of size exactly `s`".
`Prov φ s`    = "a proof of formula `φ`, of size exactly `s`".

The `.search_t` constructor carries `Prov guard s'` (a sized proof of the guard) — exactly
the real `search_t`'s `Provable k guard` premise, now SIZED. The `.search_f` constructor is
the candidate: it must carry a POSITIVE certificate that the guard has NO proof of size ≤ k.

Q1 hinges on: can `search_f`'s false-guard premise be expressed positively here? -/

/-! ### Q1, ATTEMPT A — `¬ Prov` premise INSIDE the mutual block: REJECTED.

    The version below is kept (commented) to record the finding: even WITH the size index,
    `(∀ s ≤ k, ¬ Prov guard s)` is non-positive because `Prov` is mutually defined with `PP`.
    Kernel: "arg #7 of PP.search_f has a non positive occurrence". So size-indexing ALONE is
    NOT the lever. The mutual dependency is what kills it. -/
-- mutual
--   inductive PP … | search_f (guard) : (∀ s ≤ k, ¬ Prov guard s) → … -- ← REJECTED
--   inductive Prov …
-- end

/-! ## 2. The ACTUAL fix — make the true-guard premise NON-mutual, then `search_f` is positive

Why `search_t` forces the mutual block in the real engine: it carries `Provable k guard`,
and `Provable` ⊇ `AtomProvable` ⊇ `PlaysProof`. If instead the true-guard premise is carried
as a SIZED-PROOF-TERM that does NOT re-enter `PP` as a NEGATIVE position — i.e. `PP` is
defined first (positively, recursively), and provability is a DERIVED predicate AFTER — then
`search_f`'s negative premise references the FINISHED `PP`, not a mutually-defined sibling.

Toy: define `PP` ALONE (no `Prov` mutual). The true guard carries a sized sub-`PP` directly
(the guard's own play certificate), which is the positive, in-`PP` recursion `search_t`
already is. Then `Provable_finite` is a DERIVED `∃`-predicate over `PP`. -/

/-! ### Q1, ATTEMPT B — `¬ PP` premise with `PP` defined ALONE: ALSO REJECTED.

    Kernel: "arg #8 of PP.search_f has a non positive occurrence". So it was NEVER the
    mutual block — it is the SELF-NEGATION. `search_f`'s premise `¬ PP sub a' sg` references
    `PP` itself negatively, and an inductive cannot mention its own negation, mutual or not.
    Size-indexing does NOT change this. (Kept commented to record the finding.) -/
-- inductive PP … | search_f … : (∀ sg ≤ k, ¬ PP sub a' sg) → … -- ← REJECTED (self-negation)

/-! ## 3. The CORRECT fix — `search_f` must NOT be a constructor; it lives OUTSIDE `PP`

The lesson from Attempts A and B: a false-guard step can NEVER be a constructor of the
proof object, because "no proof exists" is the negation of the proof object, which is
non-positive by Lean's foundational rule — independent of mutual-ness AND of size-indexing.

The size index's REAL payoff is elsewhere: it makes `PP_finite k body a := ∃ s ≤ k, PP body
a s` a DECIDABLE predicate (enumerate the finitely many sized proofs). Once decidable, the
false-guard fact `¬ PP_finite k guard` is an ordinary DECIDABLE PROPOSITION that can be:
  • proved/used in ordinary theorems (it's just a `Decidable` Prop), and
  • carried as data via `decide (PP_finite k guard) = false` — a BOOL EQUALITY, positive —
    BUT only in a definition/theorem AFTER `PP` is closed, NEVER inside `PP`.

So the false-guard certificate is an `AtomProvable`-LEVEL theorem (post-hoc), exactly the
`atom_complete` else-branch — and the size index is what makes its premise DECIDABLE rather
than an axiom. The constructor `search_f` is a dead end (proven here); the right object is a
`def`/`theorem` over the closed, size-indexed `PP`.

Below: `PP` WITHOUT any false-guard constructor (true-guard + const only), so it is a legal
size-indexed proof object — the thing the real refactor would build. -/

inductive PP : (body : Prog) → Action → (size : Nat) → Prop where
  | const : PP (.const a) a 1
  | search_t (sub : Prog) (a' : Action) (sg : Nat) :
      PP sub a' sg →
      PP p a n →
      PP (.search k (.plays sub sub a') p q) a (n + sg + 1)

/-- The DERIVED bounded-provability predicate — what the size index buys: a clean `∃ s ≤ k`. -/
def PP_finite (k : Nat) (body : Prog) (a : Action) : Prop := ∃ s, s ≤ k ∧ PP body a s

/-! ## Q2 — is `PP_finite` DECIDABLE by a real procedure? (BUILT)

Deciding `∃ s ≤ k, PP body a s`. The lever (vs the refuted program-recursion of `DecMeasure`):
recurse on the SIZE BUDGET `k`, not the program. Every constructor adds ≥ 1 to size, so a
size-≤-k proof has ≤ k nodes; at budget 0 nothing is provable.

`ppSize fuel body a` returns the MINIMAL proof size (`some s`) or `none` if no proof fits the
structural `fuel`. Returning the size (not a Bool) avoids the budget-vs-size drift (the same
lesson as `playsCheckC`'s `Option Nat`): the SIZE is tracked exactly, and `PP_finite k` is
decided by `∃ result, ppSize fuel … = some s ∧ s ≤ k` at large-enough `fuel`. -/

def ppSize : Nat → Prog → Action → Option Nat
  | 0,      _,    _ => none
  | fuel+1, body, a =>
      match body with
      | .const c => if c == a then some 1 else none
      | .search _ (.plays sub sub' a') p _ =>
          if sub = sub' then
            match ppSize fuel sub a', ppSize fuel p a with
            | some sg, some np => some (np + sg + 1)
            | _, _ => none
          else none
      | _ => none

/-- **Q2 soundness:** `ppSize fuel body a = some s → PP body a s` (a proof of EXACTLY size s). -/
theorem ppSize_sound :
    ∀ fuel body a s, ppSize fuel body a = some s → PP body a s := by
  intro fuel
  induction fuel with
  | zero => intro body a s h; simp [ppSize] at h
  | succ fuel ih =>
    intro body a s h
    cases body with
    | const c =>
        simp only [ppSize] at h
        by_cases hca : c == a
        · rw [if_pos hca] at h
          have : c = a := by cases c <;> cases a <;> first | rfl | (exact absurd hca (by decide))
          subst this
          have : s = 1 := by simpa using h.symm
          subst this; exact .const
        · rw [if_neg hca] at h; simp at h
    | search kk guard p q =>
        cases guard with
        | plays sub sub' a' =>
            simp only [ppSize] at h
            by_cases hsub : sub = sub'
            · subst hsub
              rw [if_pos rfl] at h
              cases hg : ppSize fuel sub a' with
              | none => rw [hg] at h; simp at h
              | some sg =>
                  cases hp : ppSize fuel p a with
                  | none => rw [hg, hp] at h; simp at h
                  | some np =>
                      rw [hg, hp] at h
                      have : s = np + sg + 1 := by simpa using h.symm
                      subst this
                      exact .search_t sub a' sg (ih sub a' sg hg) (ih p a np hp)
            · rw [if_neg hsub] at h; simp at h
        | _ => simp [ppSize] at h
    | _ => simp [ppSize] at h

/-- fuel monotonicity for `ppSize`: more fuel preserves the exact size. -/
theorem ppSize_mono :
    ∀ {fuel body a s}, ppSize fuel body a = some s →
      ∀ {f'}, fuel ≤ f' → ppSize f' body a = some s := by
  intro fuel
  induction fuel with
  | zero => intro body a s h; simp [ppSize] at h
  | succ fuel ih =>
    intro body a s h f' hf'
    -- f' = fuel + 1 + f''; both reduce via the `_+1` equation of ppSize
    cases f' with
    | zero => omega
    | succ f' =>
      have hstep : fuel ≤ f' := by omega
      cases body with
      | const c =>
          simp only [ppSize] at h ⊢
          by_cases hca : c == a
          · rw [if_pos hca] at h ⊢; exact h
          · rw [if_neg hca] at h; simp at h
      | search kk guard p q =>
          cases guard with
          | plays sub sub' a' =>
              simp only [ppSize] at h ⊢
              by_cases hsub : sub = sub'
              · subst hsub; rw [if_pos rfl] at h ⊢
                cases hg : ppSize fuel sub a' with
                | none => rw [hg] at h; simp at h
                | some sg =>
                    cases hp : ppSize fuel p a with
                    | none => rw [hg, hp] at h; simp at h
                    | some np =>
                        rw [hg, hp] at h
                        rw [ih hg hstep, ih hp hstep]; exact h
              · rw [if_neg hsub] at h; simp at h
          | _ => simp [ppSize] at h
      | _ => simp [ppSize] at h

/-- **Q2 completeness, size-bounded:** `PP body a s → ppSize (s+1) body a = some s`. The proof
    of size `s` is found at fuel `s+1`. KEY: fuel is bounded by the SIZE (the size index does
    the work), so for `PP_finite k` a fixed fuel `k+1` suffices. By induction on the proof. -/
theorem ppSize_complete :
    ∀ {body a s}, PP body a s → ppSize (s+1) body a = some s := by
  intro body a s hpp
  induction hpp with
  | @const a => cases a <;> simp [ppSize] <;> decide
  | search_t sub a' sg hg hp ihg ihp =>
      rename_i p aa n kk q
      -- goal: ppSize (n+sg+1+1) (.search kk (.plays sub sub a') p q) aa = some (n+sg+1)
      -- unfold ONE step: children get budget (n+sg+1); lift ihg/ihp by mono.
      have hg' : ppSize (n+sg+1) sub a' = some sg := ppSize_mono ihg (by omega)
      have hp' : ppSize (n+sg+1) p aa = some n := ppSize_mono ihp (by omega)
      rw [show n+sg+1+1 = (n+sg+1)+1 from rfl, ppSize]
      simp only [hg', hp', if_true]

/-- **Q2 — `PP_finite k` is DECIDED by `ppSize` at fixed fuel `k+1`.** Size ≤ k ⇒ fuel k+1
    suffices (the size index bounds the search). No `Classical`, no `sorry`. -/
theorem ppFinite_iff (k body a) :
    PP_finite k body a ↔ ∃ s, ppSize (k+1) body a = some s ∧ s ≤ k := by
  constructor
  · rintro ⟨s, hsk, hpp⟩
    exact ⟨s, ppSize_mono (ppSize_complete hpp) (by omega), hsk⟩
  · rintro ⟨s, hf, hsk⟩
    exact ⟨s, hsk, ppSize_sound (k+1) body a s hf⟩

/-- **Q2 — the genuine `Decidable` instance, built from the running `ppSize` (NOT Classical).**
    The RHS of `ppFinite_iff` is decidable: `ppSize (k+1) body a` is a concrete `Option Nat`, so
    `∃ s, … = some s ∧ s ≤ k` reduces to inspecting that value. -/
instance instDecPPFinite (k : Nat) (body : Prog) (a : Action) : Decidable (PP_finite k body a) :=
  decidable_of_iff _ (ppFinite_iff k body a).symm

-- And the false-guard fact `¬ PP_finite k guard` is therefore ALSO decidable — the post-hoc,
-- positive, non-axiom form the real refactor needs for `atom_complete`'s else-branch:
example (k : Nat) (guard_sub : Prog) (a' : Action) :
    Decidable (¬ PP_finite k guard_sub a') := inferInstance

/-! ## Result log — VERDICT

**Q1 (search_f positivity): ANSWERED — and it KILLS the "size-index unblocks search_f as a
constructor" hypothesis.** Two machine-checked rejections:
  • ATTEMPT A — `¬ Prov guard` inside the mutual block: REJECTED (non-positive).
  • ATTEMPT B — `¬ PP sub a'` with `PP` defined ALONE, size-indexed: ALSO REJECTED.
The blocker is **self-negation**, not mutual-ness and not the missing size index. An inductive
can never carry the negation of itself. So **`search_f`-as-a-constructor is impossible, period**
— size-indexing does NOT change this. My earlier "size-index makes the brick fit" framing was
WRONG about the mechanism.

**What size-indexing ACTUALLY buys (the real, narrower payoff):** it makes the DERIVED
predicate `PP_finite k body a = ∃ s ≤ k, PP body a s` finitely DECIDABLE. The false-guard
fact then lives as a post-hoc `AtomProvable`-level theorem (the `atom_complete` else-branch),
whose premise `¬ PP_finite k guard` is a DECIDABLE Prop instead of an axiom. The axiom is
discharged at the THEOREM layer, not by a new constructor.

**Net for the refactor:** still worth doing, but the deliverable is "decidable `PP_finite` ⇒
constructive `atom_complete` else-branch", NOT "add `search_f`". The 500-reference cost stands;
the payoff is real but the MECHANISM is the decidability, with the false-guard handled entirely
post-hoc.

**Q2 (decidability of `PP_finite`): BUILT and PASSED.** The lever that works (vs the refuted
program-recursion of `DecMeasure`): track proof SIZE explicitly via `ppSize : Nat → Prog →
Action → Option Nat` (returns the minimal size, fuelled), recursing structurally. Then:
  • `ppSize_sound`  — `some s → PP body a s` (exact size).
  • `ppSize_mono`   — more fuel preserves the size.
  • `ppSize_complete` — `PP body a s → ppSize (s+1) body a = some s`. **KEY: fuel ≤ size+1**, so
    the SIZE INDEX bounds the search — a fixed fuel `k+1` decides `PP_finite k`.
  • `ppFinite_iff`  — `PP_finite k body a ↔ ∃ s, ppSize (k+1) body a = some s ∧ s ≤ k`.
  • `instDecPPFinite` — the `Decidable` instance, **`#print axioms = [propext, Quot.sound]`**
    (NO `Classical.choice`, NO `sorryAx`). It RUNS: `decide (PP_finite 3 (const C) C) = true`,
    `… D = false` (machine-`#eval`'d).
  • `¬ PP_finite k guard` is `Decidable` by `inferInstance` — the positive, non-axiom premise
    the real `atom_complete` else-branch needs.

**De-risk VERDICT — the refactor's crux is GREEN (on the toy):**
  • Q1: `search_f`-as-constructor is impossible (self-negation) — but NOT needed.
  • Q2: the size-indexed `Provable_finite` IS genuinely, computably decidable — the false-guard
    fact becomes an ordinary decidable Prop, axiom-free, post-hoc.
So the mechanism for removing `atom_complete_false_guard` is CONFIRMED viable: size-index the
real `Derivation`/`PlaysProof`, port `ppSize`+its three lemmas to the real (bigger) inductive,
then re-prove `atom_complete`'s else-branch using `¬ Provable_finite`. The remaining risk is
ENGINEERING SCALE (the real `PlaysProof` has 8 constructors incl. `.sim`/`.ite`/`.bot` subst
and `search_t`'s `Provable`-premise — `ppSize` must handle the genuine `Provable`/`AtomProvable`
mutual structure, not the toy's single guard shape), NOT a foundational wall. The toy proves the
SHAPE works end-to-end, decidability included. -/

end PD.SizeIndexSpike
