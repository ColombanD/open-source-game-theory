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

/-- The inductive type for derivations in the proof system `S`, **indexed by a
    budget `k`** (route ii: bounded `S` so `Provable k φ` is decidable). The budget
    bounds the size of every *premise* of the two cut rules (`modusPonens`,
    `hypSyll`) — without it, a derivation of a size-≤k conclusion could rest on
    arbitrarily large premises (`Derivation.size = conclusion.size` hides them),
    making `Nonempty (Derivation φ)` non-finite. With every cut premise bounded by
    `k` and leaf conclusions determined by their parameters, the size-≤k derivation
    search is finite. Leaf rules are polymorphic in `k`; only the cuts constrain it.
    Here, we state what S can do. -/
inductive Derivation : Nat → Formula → Type where
  -- — Logical core —
  /-- Modus ponens: from `φ → ψ` and `φ`, infer `ψ`. Lets `S` *apply*
      implication-valued guards (needed for CIMCIC-style bots). The premise
      `.impl φ ψ` is bounded by the budget `k` (cut-formula bound for decidability). -/
  | modusPonens (φ ψ : Formula) :
      Derivation k (.impl φ ψ) → Derivation k φ → (Formula.impl φ ψ).size ≤ k → Derivation k ψ
  /-- Hypothetical syllogism: chain `φ → ψ` and `ψ → χ` into `φ → χ`. Primitive
      (not derivable from `modusPonens`: `Derivation` has no
      implication-introduction to discharge a hypothesis). Both premises are
      bounded by the budget `k` (cut-formula bound for decidability). -/
  | hypSyll (φ ψ χ : Formula) :
      Derivation k (.impl φ ψ) → Derivation k (.impl ψ χ) →
      (Formula.impl φ ψ).size ≤ k → (Formula.impl ψ χ).size ≤ k → Derivation k (.impl φ χ)
  -- — Source-transparency bridge —
  /-- S can read a `.search` body: a successful guard makes `me` play `a`. -/
  | searchBranch (k : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
      (hme : me = .search k ψ (.const a) (.const b)) :
      Derivation kb (.impl (.box k (ψ.subst me opponent)) (.plays me opponent a))
  /-- S can read a `.sim` body: `me` plays `a` iff its closed body does. -/
  | simStep (me p q opponent : Prog) (a : Action) (hme : me = .sim p q) :
      Derivation kb (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
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
      Derivation kb (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
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
      Derivation kb (.impl (.box k (ψ.subst me opponent)) (.plays me opponent a))
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
      Derivation kb (.impl (.plays opponent (.bot z) a')
                        (.impl (.box k (ψ.subst me opponent))
                               (.plays me opponent c0)))
  /-- S can verify structural identity by reflexivity: any program equals itself. -/
  | eqRefl (p : Prog) :
      Derivation kb (.eq p p)

/-- Proof size: the character count of the **conclusion formula**. This is the
    quantity `proofSearch k φ` tests against: "is there a proof of `φ` whose
    conclusion fits in `k` characters?" Leaf rules (`searchBranch`, `simStep`,
    `eqRefl`) each contribute exactly their conclusion's size; combining rules
    (`modusPonens`, `hypSyll`) produce a conclusion that is strictly smaller than
    the sum of the premises, so existing size bounds are preserved. -/
def Derivation.size : {kb : Nat} → {φ : Formula} → Derivation kb φ → Nat
  | _, φ, _ => φ.size

/-- **Budget weakening for derivations.** A derivation at budget `k₁` is also a
    derivation at any larger budget `k₂ ≥ k₁`: the only budget-sensitive fields are
    the cut-rule premise-size bounds (`modusPonens`/`hypSyll`), which only get easier
    (`size ≤ k₁ ≤ k₂`). Leaf rules are budget-polymorphic. This is what makes
    `proofSearch_monotone`'s structural disjunct go through under indexing. -/
def Derivation.weakenBudget : {k₁ k₂ : Nat} → {φ : Formula} →
    k₁ ≤ k₂ → Derivation k₁ φ → Derivation k₂ φ
  | _, _, _, h, .modusPonens φ ψ dI dφ hcut =>
      .modusPonens φ ψ (dI.weakenBudget h) (dφ.weakenBudget h) (Nat.le_trans hcut h)
  | _, _, _, h, .hypSyll φ ψ χ d1 d2 hc1 hc2 =>
      .hypSyll φ ψ χ (d1.weakenBudget h) (d2.weakenBudget h)
        (Nat.le_trans hc1 h) (Nat.le_trans hc2 h)
  | _, _, _, _, .searchBranch k ψ a b me opp hme => .searchBranch k ψ a b me opp hme
  | _, _, _, _, .simStep me p q opp a hme => .simStep me p q opp a hme
  | _, _, _, _, .botSimStep me p q opp a hme => .botSimStep me p q opp a hme
  | _, _, _, _, .botSearchStep k ψ a b me opp hme => .botSearchStep k ψ a b me opp hme
  | _, _, _, _, .iteBranchSearch_t k z a' c0 c1 ψ q me opp hme =>
      .iteBranchSearch_t k z a' c0 c1 ψ q me opp hme
  | _, _, _, _, .eqRefl p => .eqRefl p

@[simp] theorem Derivation.weakenBudget_size {k₁ k₂ : Nat} {φ : Formula}
    (h : k₁ ≤ k₂) (d : Derivation k₁ φ) : (d.weakenBudget h).size = d.size := rfl

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
    | struct : (∃ d : Derivation k φ, d.size ≤ k) → Provable k φ
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
end

-- 4. The proof-search oracle: bounded provability reflected into `Bool` for the
-- evaluator's guard. Classical (hence noncomputable), correct for an oracle.
noncomputable def proofSearch (k : Nat) (φ : Formula) : Bool := decide (Provable k φ)


/-- 5. Character budget for a `fuel`-step play's atom certificate. Honest `O(fuel)`
    (Critch's `e*`, Appendix B(d)): `c_node + c_guard fuel` per step, plus a leaf.
    `c_guard fuel` over-approximates every guard budget reachable in the run. -/
noncomputable def atom_cost (fuel : Nat) : Nat := c_leaf + (c_node + c_guard fuel) * fuel


end PD
