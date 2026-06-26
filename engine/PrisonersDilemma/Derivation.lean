import PrisonersDilemma.Program

namespace PD
open Classical


/- So basically S is semi-explicit with the Derivation Type. Its supposed to give
the rules that S follows to derive facts about formulas. Example, If S can derive
phi and phi implies psi, then S can derive psi. It is also supposed to be able to understand
the source code of the bots (the last constructors). These two concepts live together because
they are both things that S can legitimately conclude.

Now, the problem with S is that it cannot read the atom of formulas, which is a .play.
.play is the atom because in the end, we have to talk about what bots play, and .play is
how we do it.
Since S cannot read the atom (because atoms are decided by execution, not logic), we sidestep this issue
by creating a new inductive type PlaysProof that directly states whether a bot did .plays against another bot.
We use atomProvable just to incorporate that it is bounded. We still need derivation though because in some cases,
we can't get the final play without first deriving some logical reasoning in the middle: □_k ψ → plays a

Now, Provable is the link between both concepts as it states that a formula is provable if either there
is a derivation of it, or there is an atomProvable of it. So we can use Provable in the
last constructors of Derivation to link the two concepts together.
Other stuff (at the end) also are in Provable, kinda like for derivation, and they need to be there because
they combine formualas and atoms together.

                 ┌─────────────────────────────────────────┐
                 │  Provable k φ   ("φ provable in budget k")│  ← the oracle .search asks
                 │  = Derivation (small)  OR  AtomProvable    │
                 │    + 4 extra reasoning rules that need     │
                 │      "provability" as a premise            │
                 └───────────────┬──────────────┬────────────┘
                   reasoning      │              │   execution
                ┌─────────────────┘              └────────────────┐
        ┌───────▼────────┐                          ┌─────────────▼────────┐
        │  Derivation φ  │                          │  AtomProvable k φ     │
        │  logic + source│                          │  = PlaysProof + n ≤ k │
        │  reading; NO   │                          │  (only .plays atoms)  │
        │  atoms         │                          └─────────────┬─────────┘
        └────────────────┘                                        │
                                                          ┌───────▼────────┐
                                                          │  PlaysProof    │
                                                          │  = eval transcript│
                                                          └────────────────┘

--/

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
`def` through an `opaque`. As one mutual inductive the recursion is accepted.

The single residue is `atom_complete`'s false-guard direction (`¬ Provable`, Π₁) —
still the axiom `atom_complete_false_guard` in `Axioms.lean`. Its irreducibility is
now machine-located: a `.search`-bot's ELSE-action has NO certificate term at all
(neither `Derivation` nor `PlaysProof` produces it — `Research/Spikes/ExclusionSpike.lean`,
`no_deriv_else`/`provable_else_isAtom`, `[propext]` only). So the axiom postulates a
true `interp` (`play = some aElse`) whose proof TERM provably does not exist — the
proof-vs-witness gap at the certificate level. Removing it would need a `PlaysProof`
rule producing the else-action (a sound `search_f`), which is blocked (see the
`search_t` comment below and the `atom_complete_false_guard` doc).
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

/-- The inductive type for derivations in the proof system `S`. Here, we state
    what S can do. -/
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
  /-- S can read a `.bot`-wrapped `.sim` body: `me = .bot (.sim p q)`. `eval`
      unwraps the `.bot` (one step, keeping `me` as the player) and then runs the
      `.sim`, so `me` plays `a` iff its substituted body does — the `.bot (.sim …)`
      twin of `simStep`.

      Unlike the (unsound) general `.bot` transparency `plays z → plays (.bot z)`,
      this is sound: the `.bot` here is read as `me`'s *own body*, so `subst` uses
      the SAME `me = .bot (.sim p q)` throughout — there is no rebinding of a bare
      sub-program's `.self`. Needed for the `.bot MirrorBot` mirror leg (EBot's
      third probe substitutes `.opp ↦ .bot MirrorBot`, making `.bot MirrorBot` a
      *player* whose source S must read; `simStep` requires a bare `.sim`). -/
  | botSimStep (me p q opponent : Prog) (a : Action) (hme : me = .bot (.sim p q)) :
      Derivation (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                        (.plays me opponent a))
  /-- S can read a `.bot`-wrapped `.search` body: `me = .bot (.search k ψ (.const a)
      (.const b))`. `eval` unwraps the `.bot` (one step, keeping `me` as the player)
      and then runs the `.search`, so a successful guard makes `me` play `a` — the
      `.bot (.search …)` twin of `searchBranch`.

      Sound for the same reason as `botSimStep` (and unlike the unsound general
      `.bot` transparency `plays z → plays (.bot z)`): the `.bot` is read as `me`'s
      *own body*, so `subst` uses the SAME `me = .bot (.search …)` throughout — the
      guard `ψ.subst me opponent` is keyed to that very `me`, no bare sub-program's
      `.self`/`.opp` is rebound. Needed when a `.search`-bot appears `.bot`-wrapped
      as a *player* that S must read: e.g. JustBot's guard substitutes its opponent
      against `.bot (DupocBot k)`, making the `.bot`-wrapped DupocBot's `.search`
      body the leg of the PrudentBot↔DupocBot cooperation loop that `searchBranch`
      supplies for the bare DupocBot. Conclusion (same Löb/PBLT shape as
      `searchBranch`): `□_k ψ' → me plays a`, with `ψ' = ψ.subst me opponent`. -/
  | botSearchStep (k : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
      (hme : me = .bot (.search k ψ (.const a) (.const b))) :
      Derivation (.impl (.box k (ψ.subst me opponent)) (.plays me opponent a))
  /-- S can read a `.ite` whose **then-branch is itself a `.search`** — the
      PrudentBot shape: `me = .ite (.sim .opp (.bot z)) a' (.search k ψ (.const c0)
      (.const c1)) q`. This fuses the `.ite` guard reading and the inner
      `.search` reading into one sound, in-frame rule, concluding the Löb-shaped
      `□_k ψ' → me plays c0` once the guard fires.

      Why fused (and not a generic `.ite` branch rule): `eval`'s `.ite` rule runs
      both guard and selected branch in the *outer* frame (`eval n me opponent ·`),
      and for a `.search` branch that in-frame run consults
      `proofSearch k (ψ.subst me opponent)` — whereas the same `.search` run *as
      its own program* (`p.subst me opponent`) would consult a doubly-substituted
      guard. The two differ, so a generic "branch plays `a`" premise cannot be a
      `.plays` atom soundly. Keeping the `.search` explicit lets soundness reflect
      the *outer-frame* guard directly via `proofSearch_spec`.

      Restrictions, all met by real bots:
      * guard `= .sim .opp (.bot z)` — its value is frame-independent (it is
        `opponent` vs `.bot z`, lemma `eval_sim_opp_bot_of_play`), so the guard
        fact is the `.plays opponent (.bot z) a'` atom;
      * then-branch `= .search k ψ (.const c0) (.const c1)`.

      Conclusion (curried): `guard-plays-a' → (□_k ψ' → me plays c0)`, with
      `ψ' = ψ.subst me opponent`. `modusPonens` discharges the guard atom; the
      residual `□_k ψ' → me plays c0` is exactly the PBLT-shaped hypothesis that
      `searchBranch` supplies for a bare `.search` bot — now available when the
      `.search` sits under an `.ite` (PrudentBot, JustBot). Faithful: S reads the
      `.ite` node, its `.sim` guard, and the `.search` guard — each already an
      admitted transparency step. -/
  | iteBranchSearch_t (k : Nat) (z : Prog) (a' c0 c1 : Action) (ψ : Formula)
      (q me opponent : Prog)
      (hme : me = .ite (.sim .opp (.bot z)) a'
                       (.search k ψ (.const c0) (.const c1)) q) :
      Derivation (.impl (.plays opponent (.bot z) a')
                        (.impl (.box k (ψ.subst me opponent))
                               (.plays me opponent c0)))
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
-- cost of transcribing one `eval`-step into a proof. Concrete (not opaque): every
-- step costs ≥ 1 character, so a fuel-`n` play certificate has ≤ `n` steps — this is
-- what makes the decision procedure (`Checker.lean`) terminate, and lets the cost be
-- *computed* rather than reasoned about classically. `c_guard k = Nat.log2 k + 1` is
-- the `O(lg k)` character cost of writing the budget numeral `k` (Appendix B(b)); its
-- monotonicity (`c_guard_mono`, Axioms.lean) is now a theorem, not an axiom.
def c_leaf  : Nat := 1                          -- leaf step (`.const a`)
def c_node  : Nat := 1                          -- structural step (`.self`/`.opp`/`.bot`/`.sim`/`.ite`)
def c_guard (k : Nat) : Nat := Nat.log2 k + 1   -- `.search` guard at budget `k`; grows with `k`

-- `search_t` (true guard) carries `Provable k (guard)`. There is NO `search_f` (false-guard)
-- constructor — see the detailed note on `search_t` below for why (a candidate `search_f` carrying
-- `decide (Provable_fin k guard) = false` — `Provable_fin` lives in `ComputableEval/PlaysCheck.lean`
-- — would TYPECHECK but is NOT SOUND: the Löb/PBLT entanglement).
mutual
-- *PlaysProof* The code ran and produced this action with a cost.
-- PlaysProof takes in three programs, an action, and a natural number, and returns a proposition.
-- The proposition PlaysProof ... is true exactly when you can assemble it from the constructors below, and nothing else
-- | name (explicit args) : premise₁ → premise₂ → … → PlaysProof <indices>
  inductive PlaysProof : (me opponent body : Prog) → Action → Nat → Prop where
    -- Running the body .const a yields a at cost c_leaf
    | const :
        PlaysProof me opponent (.const a) a c_leaf
    -- If running me at cost n yields a, then running .self at cost n + c_node yields a
    | self :
        PlaysProof me opponent me a n →
        PlaysProof me opponent .self a (n + c_node)
    | opp :
        PlaysProof me opponent opponent a n →
        PlaysProof me opponent .opp a (n + c_node)
    | bot :
        PlaysProof me opponent p a n →
        PlaysProof me opponent (.bot p) a (n + c_node)
    | sim :
        PlaysProof (p.subst me opponent) (q.subst me opponent) (p.subst me opponent) a n →
        PlaysProof me opponent (.sim p q) a (n + c_node)
    -- If running the guard b at cost m yields r, and r = a', and running p at cost n yields a,
    -- then running .ite b a' p q at cost m + n + c_node yields a
    | ite_t :
        PlaysProof me opponent b r m → (r == a') = true →
        PlaysProof me opponent p a n →
        PlaysProof me opponent (.ite b a' p q) a (m + n + c_node)
    | ite_f :
        PlaysProof me opponent b r m → (r == a') = false →
        PlaysProof me opponent q a n →
        PlaysProof me opponent (.ite b a' p q) a (m + n + c_node)
    -- eval: `.search k φ p q => if proofSearch k (φ.subst ..) then .. p else .. q`
    -- (true-guard branch only). A `search_f` (false-guard) constructor is DELIBERATELY ABSENT.
    -- Two walls (machine-located; see `atom_complete_false_guard` doc in `Axioms.lean` and the
    -- spikes `{SearchFFeasibility,SizeIndex,ProvableFin,Exclusion}Spike.lean`):
    --   • POSITIVITY — `¬ Provable`/`¬ PlaysProof` is non-positive in-block. LIFTABLE: a candidate
    --     `search_f` carrying `decide (Provable_fin k guard) = false` (`Provable_fin` lives in
    --     `ComputableEval/PlaysCheck.lean`, references no in-block type) IS kernel-positive.
    --   • SOUNDNESS — NOT liftable. `playsProof_sound` would need `proofSearch k guard = false`
    --     (eval-exact) to run the else-branch, but `Provable_fin = false` diverges from
    --     `proofSearch = false` at the Löb fixpoints (`Provable` is `PBLT`-axiom-true there). And
    --     `eval` cannot be rewired to use `Provable_fin` — the PBLT cooperations (CupodBot.lean:112)
    --     need `proofSearch = true` at the fixpoint guard.
    -- Deeper still (`ExclusionSpike.lean`): a `.search`-bot's ELSE-action has NO certificate term
    -- at all — `no_deriv_else`/`provable_else_isAtom` prove (`[propext]` only) that neither
    -- `Derivation` nor `PlaysProof` produces it. So the axiom postulates a true `interp` whose proof
    -- TERM provably does not exist. The false-guard completeness stays the axiom.
    | search_t :
        Provable k (φ.subst me opponent) →
        PlaysProof me opponent p a n →
        PlaysProof me opponent (.search k φ p q) a (n + c_guard k + c_node)

-- *AtomProvable* The run cost fits in the budget k
  inductive AtomProvable : Nat → Formula → Prop where
    | mk : PlaysProof me opponent me a n → n ≤ k → AtomProvable k (.plays me opponent a)

-- *Provable* Provable within budget k by either a derivation or a budgeted atom.
  inductive Provable : Nat → Formula → Prop where
    | struct : (∃ d : Derivation φ, d.size ≤ k) → Provable k φ
    | atom : AtomProvable k φ → Provable k φ
    /-- **True-consequent implication** (`ψ ⊢ φ → ψ`, the premise of GL's K /
        intuitionistic axiom 1): if the consequent `ψ` is provable (at any budget
        `m`), then `φ → ψ` is provable, provided the conclusion's character size
        fits the budget `k`. Sound — `interp (.impl φ ψ)` is `φ.interp → ψ.interp`,
        which follows from `ψ.interp` by `fun _ => ·` — and faithful to a PA-like
        `S`, which can always weaken a proved formula into an implication with an
        arbitrary antecedent.

        This is the rule that makes proof-oracle bots whose guard is an *implication*
        (CIMCIC, DIMCID) provable: their guard `(.plays me opp .C) → (.plays opp me a)`
        is discharged whenever the consequent atom is itself provable (e.g. the
        opponent is a constant cooperator/defector). Unlike `searchBranch`/`simStep`
        it lives on `Provable` rather than `Derivation`, because its premise is the
        consequent's *provability* (atom or structural), which `Derivation` (a
        `Type`-valued object distinct from the `Prop`-valued `Provable`) cannot
        carry. -/
    | weakenImpl (φ ψ : Formula) (m : Nat) :
        Provable m ψ → m ≤ k → (Formula.impl φ ψ).size ≤ k → Provable k (.impl φ ψ)
    /-- **Stacked-`.search` transparency** (the canonical Critch PrudentBot shape):
        `me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q`. PrudentBot
        plays `c0` exactly when it can prove BOTH its conditions: the outer guard
        `ψ₁` (opponent cooperates with me) and the inner guard `ψ₂` (opponent
        defects vs DefectBot — prudence).

        The twin of `Derivation.iteBranchSearch_t`, but for two stacked `.search`
        nodes, and — crucially — living on `Provable` rather than `Derivation`. It
        must: the inner (prudence) guard is discharged here by its *provability*
        `Provable k₂ ψ₂'`, which is typically an ordinary Σ₁ atom (`□(atom)` has no
        `Derivation`, so a `Derivation`-level rule could not strip it — the same
        Type/Prop split that motivates `weakenImpl`). Carrying the inner proof as a
        premise collapses the two guards to a *single*-box conclusion `□_{k₁} ψ₁'
        → me plays c0`, which is exactly the Löb-premise shape `PBLT` consumes.

        Sound: once `proofSearch k₂ ψ₂'` holds (reflecting the premise) and the box
        antecedent gives `proofSearch k₁ ψ₁'`, `eval` runs the outer `.search` →
        inner `.search` → `.const c0` in-frame, so `me` plays `c0`
        (`Provable_sound`). Faithful: S reads the outer `.search` node and its
        `.search` then-branch — each an admitted transparency step — and consults
        the already-proved inner guard. The size side-condition keeps the
        conclusion within budget `k`, as for `weakenImpl`. -/
    | searchThenSearch_t (k₁ k₂ : Nat) (ψ₁ ψ₂ : Formula) (c0 c1 : Action)
        (q me opponent : Prog)
        (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) :
        Provable k₂ (ψ₂.subst me opponent) → k₂ ≤ k →
        (Formula.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0)).size ≤ k →
        Provable k (.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0))
    /-- **Transitivity of implication at the `Provable` level** (hypothetical
        syllogism for `Provable`): from `φ → ψ` and `ψ → χ`, infer `φ → χ`.
        `Derivation.hypSyll` already gives this for `Derivation` premises; this is
        its `Provable` twin, needed to chain a `Provable`-only implication (e.g. the
        `searchThenSearch_t` Löb leg, which has no `Derivation`) with another. Sound
        — `interp` of each `.impl` is Lean implication, so composition is function
        composition (`Provable_sound`). The size side-condition keeps the
        conclusion within budget `k`, as for `weakenImpl`. -/
    | implTrans (φ ψ χ : Formula) (a b : Nat) :
        Provable a (.impl φ ψ) → Provable b (.impl ψ χ) →
        a ≤ k → b ≤ k → ψ.size ≤ k →
        (Formula.impl φ χ).size ≤ k → Provable k (.impl φ χ)
    /-- **Object-level bounded Σ₁-completeness for play-atoms** (constructive,
        certificate-carrying): from a bounded play certificate `AtomProvable k
        (p plays a vs q)`, infer the *object implication*
        `(p plays a vs q) → □_k (p plays a vs q)` at budget `k`.

        This is the constructive twin of the former axiom `atom_box_provable_impl`
        (Axioms.lean), and the in-`Provable` realization of `box_provable`'s
        Σ₁-restricted case. The crucial difference from the axiom: it carries the
        **certificate** `AtomProvable k (.plays p q a)` as a premise, so it only fires
        when a size-≤-`k` play transcript actually exists. That is exactly the
        `atom_cost fuel ≤ k` budget threshold the reviewer flagged as missing — here
        supplied as a proof-term premise rather than a side hypothesis, which keeps it
        on the sound Σ₁ side (`φ → □φ` for a `.plays` atom is genuine bounded
        Σ₁-completeness, NOT the GL-excluded converse-necessitation).

        Sound with NO axiom: the consequent `(□_k φ).interp` is `Provable k φ`, which
        the premise `AtomProvable k φ` discharges directly via `Provable.atom` —
        independent of the antecedent (so the implication holds vacuously off the
        fixed point and genuinely on it). Faithful: S can always weaken a held
        certificate into the (true) implication, as `weakenImpl` does for a proved
        consequent. The size side-condition keeps the conclusion within budget `k`. -/
    | atomBoxImpl (kBox : Nat) (p q : Prog) (a : Action) :
        AtomProvable kBox (.plays p q a) →
        (Formula.impl (.plays p q a) (.box kBox (.plays p q a))).size ≤ k →
        Provable k (.impl (.plays p q a) (.box kBox (.plays p q a)))
end

-- 4. The proof-search oracle: bounded provability reflected into `Bool` for the
-- evaluator's guard. Classical (hence noncomputable), correct for an oracle.
noncomputable def proofSearch (k : Nat) (φ : Formula) : Bool := decide (Provable k φ)


/-- 5. Character budget for a `fuel`-step play's atom certificate. Honest `O(fuel)`
    (Critch's `e*`, Appendix B(d)): `c_node + c_guard fuel` per step, plus a leaf.
    `c_guard fuel` over-approximates every guard budget reachable in the run. -/
def atom_cost (fuel : Nat) : Nat := c_leaf + (c_node + c_guard fuel) * fuel


end PD
