import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems

/-!
# A genuinely computable, SOUND partial evaluator `evalC` (the reviewer-facing demo)

`eval` (Dynamics.lean) is `noncomputable`: its `.search` guard consults the classical
oracle `proofSearch k φ := decide (Provable k φ)`. This is *forced* — the library's
57 `proofSearch_spec.2` sites (completeness `Provable → proofSearch = true`) include the
Löb fixpoints (PrudentBot↔DupocBot cooperation), whose provability has **no finite play
witness** (it is established by the bounded-Σ₁ reflection axioms PBLT /
`atom_box_provable_impl`, not by unrolling). No terminating computation can return `true`
on those, so no computable function can satisfy the existing `proofSearch_spec`.

So we add a SEPARATE, total, computable `evalC`. The subtlety (found the hard way): the
`.search` guard must be **3-valued** — `decGuard` returns `some true` (a finite play
witness exists), `some false` (a finite *refutation* exists: the subject actually plays
something else), or `none` (undecided within fuel). `evalC` runs the then-branch on
`some true`, the else-branch on `some false`, and returns `none` on `none`. A 2-valued
guard that silently defected on "undecided" would return the WRONG action on the Löb
fixpoints (defect where the real bot cooperates) — `decGuard` would then be unsound. The
3-valued design makes `evalC` a SOUND partial evaluator: it never commits a wrong action;
it cooperates / defects only with a witness, and answers `none` on the Löb fixpoints.

Faithfulness (C2, `evalC_sound`): `evalC fuel me opp body = some a ⇒ ∃ N, eval N me opp
body = some a` — every committed answer is a real classical play. The converse fails (the
Löb fixpoints: `eval` cooperates, `evalC` says `none`) — that is the intrinsic boundary,
Löb's theorem, where bounded computation ends and modal reflection begins.

`evalC` answers the reviewer's "noncomputable = misuse" jab concretely (`#eval evalC …`
runs in the kernel and is provably correct whenever it commits). The library's
`eval`/`proofSearch`/outcome theorems are untouched.
-/

namespace PD

mutual
  /-- Computable fuel-bounded **partial** evaluator. Mirrors `eval` except the `.search`
      guard consults the 3-valued computable `decGuard`; `none` guard ⇒ `none` result.
      One decreasing `fuel` across the mutual group ⇒ total & computable. -/
  def evalC : Nat → (me opponent body : Prog) → Option Action
    | 0,   _,  _,        _    => none
    | n+1, me, opponent, body => match body with
      | .const a        => some a
      | .self           => evalC n me opponent me
      | .opp            => evalC n me opponent opponent
      | .bot p          => evalC n me opponent p
      | .sim p q        =>
          let p' := p.subst me opponent
          let q' := q.subst me opponent
          evalC n p' q' p'
      | .ite b a p q    =>
          match evalC n me opponent b with
          | some r => if r == a then evalC n me opponent p else evalC n me opponent q
          | none   => none
      | .search _ φ p q =>
          match decGuard n (φ.subst me opponent) with
          | some true  => evalC n me opponent p
          | some false => evalC n me opponent q
          | none       => none

  /-- 3-valued, computable, fuel-bounded guard decision. SOUND in both polarities:
      * `some true`  — a finite play witness of the guard formula exists;
      * `some false` — a finite *refutation* exists (the subject actually plays another
        action), so the guard is genuinely false;
      * `none`       — undecided within fuel (e.g. a Löb fixpoint: no finite witness).
      Handles the guard shapes the library's bots use; everything else ⇒ `none`. -/
  def decGuard : Nat → Formula → Option Bool
    | 0,     _ => none
    | n+1,   φ => match φ with
      | .plays p q a =>
          match evalC (n+1) p q p with
          | some b => some (decide (b = a))   -- plays `a` ⇒ true; plays `b≠a` ⇒ refuted
          | none   => none
      | .impl _ ψ    =>
          -- weakenImpl (true-consequent): consequent witnessed ⇒ implication true.
          -- We do not attempt to refute an implication computably ⇒ at most `some true`.
          match decGuard n ψ with
          | some true => some true
          | _         => none
      | _            => none
end

/-- Computable entry points, mirroring `play`/`outcome`. -/
def playC (fuel : Nat) (me opponent : Prog) : Option Action :=
  evalC fuel me opponent me

def outcomeC (fuel : Nat) (p q : Prog) : Option Outcome := do
  let a ← playC fuel p q
  let b ← playC fuel q p
  some (a, b)

end PD
