import PrisonersDilemma.Program

namespace PD
open Classical

/-!
# The proof system `S`

The agents' internal logic, made explicit. This file defines, as one mutual
`inductive` block:
* `Derivation : Formula → Type` — the structural proof objects of `S`;
* `PlaysProof me opp body a n` — a **play certificate**: a finite, character-
  costed transcript of `body` evaluating to `a` (one constructor per `eval`-step);
* `AtomProvable k φ` — a bounded play certificate for an atomic `.plays` fact;
* `Provable k φ` — a `Derivation` of size ≤ `k`, OR a bounded atom certificate;
* `proofSearch k φ` — the oracle agents query, *defined* as decidable `Provable`.

`Formula.interp` (Dynamics.lean) interprets `Formula`; `Derivation.sound` /
`AtomProvable_sound` (BaseTheorems.lean) bridge `provability → truth`.

Atom-provability used to be `opaque` (and `Provable` a `def`), on the belief that
the atom self-reference — a `.search` subject's guard `□_k ψ` means `Provable` —
was a Löb loop Lean must reject. It isn't: that was an artifact of unfolding a
`def` through an `opaque`. As one mutual inductive the recursion is accepted, and
being a *least* fixed point it even excludes the genuinely self-referential plays
for free (see §3). The single residue is `atom_complete`'s false-guard direction
(`¬ Provable`, Π₁) — still an axiom in `Axioms.lean`.
-/

-- 1. The derivation system. Each rule is (i) SOUND — its conclusion's `interp`
-- follows from its premises' (`Derivation.sound`, BaseTheorems.lean) — and
-- (ii) FAITHFUL to a PA-like `S` (critch22 Appendix B): a genuine capability of
-- `S`, with no semantic completeness / general reflection smuggled in. Two layers:
--   • LOGICAL CORE — propositional inference (modus ponens, hyp. syllogism).
--   • SOURCE-TRANSPARENCY BRIDGE — "S reads `Prog` source", one rule per
--     construct it inspects (`.search`, `.sim`); Appendix B(a).
--
-- Deliberately ABSENT as constructors:
--   • Atomic `.plays` — handled by the `PlaysProof` certificate (§3), not here.
--   • GL axiom 4 (`□φ → □□φ`): a sound PA principle (HBL D2) but needs a size
--     side-condition unstatable without size-indexing `Derivation`; it lives as
--     the axiom `box_provable` (Axioms.lean), like `PBLT`. GL's K, by contrast,
--     *is* derived — the theorem `K_provable`, from `modusPonens`.

/-- The inductive type for derivations in the proof system `S`. Here, we state what S can do.-/
inductive Derivation : Formula → Type where
  -- — Logical core —
  /-- Modus ponens: from `φ → ψ` and `φ`, infer `ψ`. Lets `S` *apply*
      implication-valued guards (needed for CIMCIC-style bots). -/
  | modusPonens (φ ψ : Formula) :
      Derivation (.impl φ ψ) → Derivation φ → Derivation ψ
  /-- Hypothetical syllogism: chain `φ → ψ` and `ψ → χ` into `φ → χ`. Primitive
      (not derivable from `modusPonens`: `Derivation` has no
      implication-introduction to discharge a hypothesis). -/
  | hypSyll (φ ψ χ : Formula) :
      Derivation (.impl φ ψ) → Derivation (.impl ψ χ) → Derivation (.impl φ χ)
  -- — Source-transparency bridge —
  /-- S can read a `.search` body: a successful guard makes `me` play `a`. -/
  | searchBranch (k : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
      (hme : me = .search k ψ (.const a) (.const b)) :
      Derivation (.impl (.box k (ψ.subst me opponent)) (.plays me opponent a))
  /-- S can read a `.sim` body: `me` plays `a` iff its closed body does. -/
  | simStep (me p q opponent : Prog) (a : Action) (hme : me = .sim p q) :
      Derivation (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                        (.plays me opponent a))
  /-- S can verify structural identity by reflexivity: any program equals itself. -/
  | eqRefl (p : Prog) :
      Derivation (.eq p p)

/-- Proof size: the character count of the **conclusion formula**. This is the
    quantity `proofSearch k φ` tests against: "is there a proof of `φ` whose
    conclusion fits in `k` characters?" Leaf rules (`searchBranch`, `simStep`,
    `eqRefl`) each contribute exactly their conclusion's size; combining rules
    (`modusPonens`, `hypSyll`) produce a conclusion that is strictly smaller than
    the sum of the premises, so existing size bounds are preserved. -/
def Derivation.size : {φ : Formula} → Derivation φ → Nat
  | φ, _ => φ.size

-- 2. Per-step proof-encoding costs (Critch's `e*`, Appendix B(d)): the character
-- cost of transcribing one `eval`-step into a proof. Opaque constants — any
-- concrete values work; only `c_guard`'s monotonicity is constrained (Axioms.lean).
opaque c_leaf  : Nat        -- leaf step (`.const a`)
opaque c_node  : Nat        -- structural step (`.self`/`.opp`/`.bot`/`.sim`/`.ite`)
opaque c_guard : Nat → Nat  -- `.search` guard at budget `k`; grows with `k` (see c_guard_mono)

-- 3. **Atom/provability layer, as one mutual inductive.**
-- * `PlaysProof me opp body a n` — a play certificate: `body` evaluates to `a`
--   (players `me`/`opp`) with a transcript of `n` characters: "with players me/opp,
--   the code body evaluates to action a, and writing down that fact takes n characters."
-- * `AtomProvable k (.plays me opp a)` — a certificate of cost ≤ `k` (`body = me`).
-- * `Provable k φ` — a `Derivation` of size ≤ `k` (`.struct`), or a bounded atom
--   certificate (`.atom`). Same meaning as the old `def`, now an inductive so it
--   can sit in the mutual block with `PlaysProof`.
--
-- `search_t` (true guard) carries `Provable k (guard)` — positive, fine. There is
-- deliberately NO `search_f`: a false-guard play certifies `¬ Provable k (guard)`
-- (Π₁, "no proof of size ≤ k exists"), which is non-positive (kernel-rejected)
-- and the genuinely hard direction. So `atom_complete`'s completeness for
-- false-guard plays stays an axiom (`Axioms.lean`); everything else is a theorem.
mutual
  inductive PlaysProof : (me opponent body : Prog) → Action → Nat → Prop where
    -- eval: `.const a => some a`
    | const :
        PlaysProof me opponent (.const a) a c_leaf
    -- eval: `.self => eval n me opponent me`
    | self :
        PlaysProof me opponent me a n →
        PlaysProof me opponent .self a (n + c_node)
    -- eval: `.opp => eval n me opponent opponent`
    | opp :
        PlaysProof me opponent opponent a n →
        PlaysProof me opponent .opp a (n + c_node)
    -- eval: `.bot p => eval n me opponent p`
    | bot :
        PlaysProof me opponent p a n →
        PlaysProof me opponent (.bot p) a (n + c_node)
    -- eval: `.sim p q => eval n p' q' p'` with `p' = p.subst me opp`, `q' = q.subst me opp`
    | sim :
        PlaysProof (p.subst me opponent) (q.subst me opponent) (p.subst me opponent) a n →
        PlaysProof me opponent (.sim p q) a (n + c_node)
    -- eval: `.ite b a' p q => (eval n .. b) >>= fun r => if r == a' then .. p else .. q`
    | ite_t :
        PlaysProof me opponent b r m → (r == a') = true →
        PlaysProof me opponent p a n →
        PlaysProof me opponent (.ite b a' p q) a (m + n + c_node)
    | ite_f :
        PlaysProof me opponent b r m → (r == a') = false →
        PlaysProof me opponent q a n →
        PlaysProof me opponent (.ite b a' p q) a (m + n + c_node)
    -- eval: `.search k φ p q => if proofSearch k (φ.subst ..) then .. p else .. q`
    -- (true-guard branch only; see the no-`search_f` note above)
    | search_t :
        Provable k (φ.subst me opponent) →
        PlaysProof me opponent p a n →
        PlaysProof me opponent (.search k φ p q) a (n + c_guard k + c_node)
  inductive AtomProvable : Nat → Formula → Prop where
    | mk : PlaysProof me opponent me a n → n ≤ k → AtomProvable k (.plays me opponent a)
  inductive Provable : Nat → Formula → Prop where
    | struct : (∃ d : Derivation φ, d.size ≤ k) → Provable k φ
    | atom : AtomProvable k φ → Provable k φ
end

-- 4. The proof-search oracle: bounded provability reflected into `Bool` for the
-- evaluator's guard. Classical (hence noncomputable), correct for an oracle.
noncomputable def proofSearch (k : Nat) (φ : Formula) : Bool := decide (Provable k φ)


/-- 5. Character budget for a `fuel`-step play's atom certificate. Honest `O(fuel)`
    (Critch's `e*`, Appendix B(d)): `c_node + c_guard fuel` per step, plus a leaf.
    `c_guard fuel` over-approximates every guard budget reachable in the run. -/
noncomputable def atom_cost (fuel : Nat) : Nat := c_leaf + (c_node + c_guard fuel) * fuel


end PD
