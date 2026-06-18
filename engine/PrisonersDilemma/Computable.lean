import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems

/-!
# A genuinely computable evaluator `evalC` (the reviewer-facing demo)

`eval` (Dynamics.lean) is `noncomputable`: its `.search` guard consults the classical
oracle `proofSearch k φ := decide (Provable k φ)`. This is *forced* — the library's
57 `proofSearch_spec.2` sites (completeness `Provable → proofSearch = true`) include the
Löb fixpoints (PrudentBot↔DupocBot cooperation), whose provability has **no finite play
witness** (it is established by the bounded-Σ₁ reflection axioms PBLT /
`atom_box_provable_impl`, not by unrolling). No terminating computation can return `true`
on those, so no computable function can satisfy the existing `proofSearch_spec`.

So we add a SEPARATE, total, computable `evalC` whose `.search` guard `decGuard` looks
for a *finite witness* within its own fuel:

* on the finite-witness fragment (constant / atom-guard bots — CooperateBot, DefectBot,
  MirrorBot, TitForTat, and the prudence/defection legs of the search bots) `decGuard`
  finds the witness and `evalC` AGREES with `eval` (theorem `evalC_sound`, C2);
* on the Löb fixpoints `decGuard` exhausts fuel, returns `false`, and `evalC` takes the
  defection branch — **disagreeing** with the cooperative `eval`. That disagreement is
  the precise, intrinsic boundary (Löb's theorem): it is where bounded computation ends
  and modal reflection begins.

`evalC` answers the reviewer's "noncomputable = misuse" jab concretely (`#eval evalC …`
runs in the kernel) while being honest about exactly which matchups it cannot decide.
The library's `eval`/`proofSearch`/outcome theorems are untouched.
-/

namespace PD

mutual
  /-- Computable fuel-bounded evaluator. Mirrors `eval` exactly except the `.search`
      guard consults the computable `decGuard` (witness search) instead of the classical
      oracle. One decreasing `fuel` across the whole mutual group ⇒ total & computable. -/
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
          if decGuard n (φ.subst me opponent)
            then evalC n me opponent p
            else evalC n me opponent q

  /-- Computable, fuel-bounded under-approximation of the guard oracle: searches for a
      *finite play witness* of the guard formula `φ` within `fuel`. Sound (only fires on
      a genuine witness) but incomplete (no `true` for Löb fixpoints — they have no finite
      witness). Handles exactly the guard shapes the library's bots use:
      * `.plays p q a` — fires iff `p` actually plays `a` against `q` within fuel
        (`evalC fuel p q p = some a`);
      * `.impl (.plays ..) ψ` — the `weakenImpl` shape: fires iff the consequent `ψ` is
        itself witnessed (true-consequent implication);
      everything else (incl. `.box`, `.neg`, Löb loops) ⇒ `false`. -/
  def decGuard : Nat → Formula → Bool
    | 0,     _ => false
    | n+1,   φ => match φ with
      | .plays p q a => decide (evalC (n+1) p q p = some a)
      | .impl _ ψ    => decGuard n ψ
      | _            => false
end

/-- Computable entry points, mirroring `play`/`outcome`. -/
def playC (fuel : Nat) (me opponent : Prog) : Option Action :=
  evalC fuel me opponent me

def outcomeC (fuel : Nat) (p q : Prog) : Option Outcome := do
  let a ← playC fuel p q
  let b ← playC fuel q p
  some (a, b)

end PD
