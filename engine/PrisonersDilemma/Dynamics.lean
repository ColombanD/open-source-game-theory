import PrisonersDilemma.Program

namespace PD
open Classical

/-!
# Game dynamics and the explicit proof system `S`

This file holds the two co-defined layers of the model, in the order their
dependencies force:

1. **The proof system `S`** — the inductive `Derivation` (syntactic shape
   rules), the opaque `AtomProvable`, `Provable` (`Derivation`-or-atom), and
   the proof-search oracle `proofSearch` *defined* as decidable provability
   (no longer an axiom).
2. **The game dynamics** — the fuelled evaluator `eval`, plus `play`,
   `outcome`, and the denotational semantics `Formula.interp`.

They live together because they are mutually entangled: `eval`'s `.search`
guard calls `proofSearch`, while `Provable`/`interp` reason about `play`. The
ordering below (proof system first, dynamics second) is what keeps the
definitions acyclic. Soundness of `Derivation`, `proofSearch_spec`, and the
transparency theorems are proved separately in `BaseTheorems.lean`.

The only assumptions that survive are isolated to atomic `.plays` formulas
(σ₁-completeness and atom-soundness — see `AtomProvable` below). These cannot
be made constructive: any concrete definition of atom-provability that handles
`.search`-using programs must consult the truth of their guard `□_k ψ`, whose
meaning *is* `Provable` — closing the self-referential loop
`Provable → AtomProvable → (guard) Provable`. This is the Löb/Gödel
self-reference at the heart of the setup (the same reason critch22 needs PBLT),
not merely an artefact of `play` evaluation; Lean's termination checker rejects
every concrete form of it. So atom-provability stays opaque, pinned by axioms.
-/

-- 1. The derivation system: three syntactic shape-rules. No general
-- reflection, and crucially no atomic-`plays` rule (that would have to carry a
-- `play` hypothesis, recreating the cycle — atoms are handled by `AtomProvable`).
inductive Derivation : Formula → Type where
  /-- S can read a `.search` body: a successful guard makes `me` play `a`. -/
  | searchBranch (k : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
      (hme : me = .search k ψ (.const a) (.const b)) :
      Derivation (.impl (.box k (ψ.subst me opponent)) (.plays me opponent a))
  /-- S can read a `.sim` body: `me` plays `a` iff its closed body does. -/
  | simStep (me p q opponent : Prog) (a : Action) (hme : me = .sim p q) :
      Derivation (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                        (.plays me opponent a))
  /-- Hypothetical syllogism: a basic structural rule of any proof system. -/
  | hypSyll (φ ψ χ : Formula) :
      Derivation (.impl φ ψ) → Derivation (.impl ψ χ) → Derivation (.impl φ χ)

/-- Proof size; the budget measured by `proofSearch`. -/
def Derivation.size : {φ : Formula} → Derivation φ → Nat
  | _, .searchBranch ..   => 1
  | _, .simStep ..        => 1
  | _, .hypSyll _ _ _ d e => d.size + e.size + 1

-- 2. σ₁ atom-provability as an opaque predicate. It is opaque, not defined,
-- because any concrete definition is self-referential: justifying a `.plays`
-- atom whose subject is a `.search` program requires consulting that program's
-- guard `□_k ψ`, and `□`'s meaning is `Provable` — so `AtomProvable` would
-- depend on `Provable`, which already depends on `AtomProvable` (§3). That is a
-- genuine Löb-style loop (independent of `play`), which Lean's termination
-- checker rejects in every form we tried. The two atom axioms below pin it
-- down instead. Budget-independent: an atom is σ₁-true (hence provable at *some*
-- size) or not — no tight size bound to track, making proof-search
-- budget-monotonicity automatic.
opaque AtomProvable : Formula → Prop

-- 3. Provability in S: derivable by the structural rules within budget `k`, OR
-- an atomic σ₁ fact. This is the truth condition the box modality refers to.
def Provable (k : Nat) (φ : Formula) : Prop :=
  (∃ d : Derivation φ, d.size ≤ k) ∨ AtomProvable φ

-- 4. The proof-search oracle is now a *definition*, not an axiom: bounded
-- provability, reflected into `Bool` for the evaluator's guard. Classical
-- (hence noncomputable), which is correct for a model of an oracle.
noncomputable def proofSearch (k : Nat) (φ : Formula) : Bool := decide (Provable k φ)

-- 5. The fuelled evaluator. Because `proofSearch` is already defined above,
-- the `.search` guard inlines it directly — so `eval` is an ordinary
-- non-parametric definition here, defined *after* the oracle it consults.
-- This staging (oracle first, evaluator second) is what avoids the cycle
-- `eval → proofSearch → Provable → Derivation`; no oracle parameter is needed.
-- `me`/`opponent` are the fixed players; `body` is the subterm being reduced;
-- `Option` lets runs fail when fuel is exhausted.
noncomputable def eval : Nat → (me opponent body : Prog) → Option Action
  | 0,   _,  _,   _    => none
  | n+1, me, opponent, body => match body with
    | .const a        => some a
    | .self           => eval n me opponent me
    | .opp            => eval n me opponent opponent
    | .bot p          => eval n me opponent p
    | .sim p q        =>
        let p' := p.subst me opponent
        let q' := q.subst me opponent
        eval n p' q' p'
    | .ite b a p q    => do
        let r ← eval n me opponent b
        if r == a then eval n me opponent p else eval n me opponent q
    | .search k φ p q =>
        if proofSearch k (φ.subst me opponent)
          then eval n me opponent p
          else eval n me opponent q

noncomputable def play (fuel : Nat) (me opponent : Prog) : Option Action :=
  eval fuel me opponent me

noncomputable def outcome (fuel : Nat) (p q : Prog) : Option Outcome := do
  let a ← play fuel p q
  let b ← play fuel q p
  some (a, b)

-- 6. Denotational semantics. The box clause now refers to `Provable` directly
-- — the semantics no longer quotes a black-box oracle.
def Formula.interp : Formula → Prop
  | .plays p q a => ∃ n, play n p q = some a
  | .impl φ ψ    => φ.interp → ψ.interp
  | .neg φ       => ¬ φ.interp
  | .box n φ     => Provable n φ

end PD
