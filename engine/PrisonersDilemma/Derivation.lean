import PrisonersDilemma.Program

namespace PD
open Classical


/-!
# The proof system `S`

The agents' internal logic, made explicit. One mutual `inductive` block defines four
objects, layered by what their premises may mention:

```
              ┌────────────────────────────────────────────────┐
              │  Provable k φ   ("φ provable within budget k") │  ← the oracle `.search` asks
              │  =                                             |
              |  | struct (a small Derivation)                 │
              │  | atom   (a budgeted play certificate)        │
              │  | reflection rules whose premises are         │
              │    THEMSELVES `Provable` (impl/box reasoning)  │
              └──────────────┬───────────────┬─────────────────┘
                 reasoning   │               │   execution
             ┌───────────────┘               └───────────────┐
      ┌───────▼────────┐                        ┌────────────▼─────────┐
      │  Derivation φ  │                        │ AtomProvable k φ     │
      │  logic + source│                        │ = PlaysProof + n ≤ k │
      │ reading; NO    │                        │ (only `.plays` atoms)│
      │  `.plays` atoms│                        └────────────┬─────────┘
      └────────────────┘                                     │
                                                     ┌───────▼─────────┐
                                                     │  PlaysProof     │
                                                     │= eval transcript│
                                                     └─────────────────┘
```

* **`Derivation : Formula → Type`** — structural proof objects: the *logical core*
  (modus ponens, hyp. syllogism) and the *source-transparency bridge* ("S reads `Prog`
  source", one rule per construct it inspects). Premises are other `Derivation`s only —
  NO `.plays` atoms (atoms are decided by execution, not logic) and NO `Provable` premises.
* **`PlaysProof me opp body a n`** — a *play certificate*: a finite, character-costed
  transcript of `body` evaluating to `a` (one constructor per `eval`-step).
* **`AtomProvable k φ`** — a `PlaysProof` whose cost fits the budget (`n ≤ k`); the bridge
  for atomic `.plays` facts that `Derivation` cannot read.
* **`Provable k φ`** — the formula provable within budget `k`. Three kinds of member:
  `struct` (a `Derivation` of size ≤ k), `atom` (an `AtomProvable`), and the *reflection
  rules* whose premises are themselves `Provable` (so they cannot live on the `Type`-valued
  `Derivation`). See the grouped sections in the `Provable` block.
* **`proofSearch k φ`** — the oracle agents query, *defined* as decidable `Provable`.

`Formula.interp` (Dynamics.lean) interprets `Formula`; `Derivation.sound` /
`AtomProvable_sound` / `Provable_sound` (BaseTheorems.lean) bridge `provability → truth`.

## Why a single mutual inductive (historical note)

Atom-provability used to be `opaque` (and `Provable` a `def`), on the belief that the atom
self-reference — a `.search` subject's guard `□_k ψ` means `Provable` — was a Löb loop Lean
must reject. It isn't: that was an artifact of unfolding a `def` through an `opaque`. As one
mutual inductive the recursion is accepted.

## The remaining axiom this file touches: `atom_complete_false_guard`

The single residue is `atom_complete`'s false-guard direction (`¬ Provable`, Π₁) — the axiom
`atom_complete_false_guard` (`Axioms.lean`). Its irreducibility is machine-located: a
`.search`-bot's ELSE-action has NO certificate term at all (neither `Derivation` nor
`PlaysProof` produces it — `ComputableEval/Exclusion.lean`, `[propext]` only). So the axiom
postulates a true `interp` (`play = some aElse`) whose proof TERM provably does not exist.
Removing it would need a `PlaysProof` rule producing the else-action (a sound `search_f`),
which is blocked (see the `search_t` comment below).
-/

-- 1. The `Derivation` system. Each rule is (i) SOUND — its conclusion's `interp`
-- follows from its premises' (`Derivation.sound`, BaseTheorems.lean) — and
-- (ii) FAITHFUL to a PA-like `S` (critch22 Appendix B): a genuine capability of
-- `S`, with no semantic completeness / general reflection smuggled in. Two layers:
--   • LOGICAL CORE — propositional inference (modus ponens, hyp. syllogism).
--   • SOURCE-TRANSPARENCY BRIDGE — "S reads `Prog` source", one rule per
--     construct it inspects (`.search`, `.sim`, `.ite`); Appendix B(a).
--
-- What is NOT here, and where it lives instead:
--   • Atomic `.plays` — handled by the `PlaysProof` certificate, not by `Derivation`.
--   • The modal/reflection rules (GL K, GL 4, necessitation, object MP) — they need
--     `Provable` premises, so they live on `Provable` below as the constructors
--     `axK` / `box4` / `boxIntro` / `app` (NOT axioms — added when the `box_provable`
--     and `boxInternalize` axioms were eliminated). `Derivation`'s own `modusPonens`
--     is the `Type`-level MP; `app` is its `Provable`-level twin.
--   • An implication-INTRODUCTION (deduction theorem) — DELIBERATELY absent: it would
--     take a PA-like `S` to full intuitionistic logic and break faithfulness/bounds.
--     This is why `hypSyll` is primitive (cannot be derived from `modusPonens`).

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
  /-- S can REFUTE structural identity of syntactically distinct programs: `¬(p = q)` for
      `p ≠ q` — the Σ₁ counterpart of `eqRefl` (source-string comparison is decidable for S).
      NEW with the false-guard repair (2026-07-02): feeds `search_f` for failed `.eq` guards
      (CupodTrollBot's recognition guard against a non-Cupod opponent). -/
  | eqNeg (p q : Prog) (hne : p ≠ q) :
      Derivation (.neg (.eq p q))

/-- **Proof "size" = the character count of the WHOLE TRANSCRIPT** (cumulative over the
    proof tree). This is Critch's literal character-cost model (Appendix B): `proofSearch k φ`
    asks "is there a proof of `φ` whose full transcript fits in `k` characters?". Leaf rules
    cost their conclusion's size; the combining rules (`modusPonens`, `hypSyll`) pay BOTH
    subtrees plus their own conclusion — so a bounded budget genuinely bounds the premise
    formulas too (the paid-cut property that makes bounded search finite; the former
    conclusion-only cost model left `modusPonens` premises unbounded, which is exactly what
    blocked decidability — `Research/Notes/DECIDABILITY_ROADMAP.md`). -/
def Derivation.size : {φ : Formula} → Derivation φ → Nat
  | _, .modusPonens _ ψ d1 d2 => d1.size + d2.size + ψ.size
  | _, .hypSyll φ _ χ d1 d2 => d1.size + d2.size + (Formula.impl φ χ).size
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

mutual
-- 3. `PlaysProof me opponent body a n` — a play certificate: `body` (run with `me`/`opponent` as
-- the players) evaluates to action `a` at character cost `n`. One constructor per `eval`-step; the
-- proposition holds exactly when assembled from these constructors. (`search_t`'s false-guard
-- counterpart is deliberately absent — see its doc.)
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
    -- `.search k φ p q` runs the TRUE-guard branch (`p`) when `proofSearch k (φ.subst ..)` holds,
    -- so `search_t` carries `Provable k (guard)` as its premise. There is NO `search_f` (false-guard)
    -- constructor: the else-action has no certificate term, the residue captured by the axiom
    -- `atom_complete_false_guard`. See its doc in `Axioms.lean` and `ComputableEval/Exclusion.lean`
    -- (`no_deriv_else`/`provable_else_isAtom`, `[propext]`): no `Derivation` and no `PlaysProof`
    -- concludes a `.search`-bot's else-action, so the axiom postulates a true `interp` whose proof
    -- TERM provably does not exist (the proof-vs-witness gap).
    | search_t :
        Provable k (φ.subst me opponent) →
        PlaysProof me opponent p a n →
        PlaysProof me opponent (.search k φ p q) a (n + c_guard k + c_node)
    /-- **FALSE-guard branch — the REPAIR of the deleted-inconsistent `atom_complete_false_guard`
        axiom** (2026-07-02; `Research/Spikes/transcript/T32Inconsistency.lean`). `.search k φ p q`
        runs the ELSE branch (`q`) when the guard search fails. Both design points are FORCED:

        * The premise is a **refutation** `Provable m (.neg guard)` — Σ₁, certifiable via the
          guard subject's actual play plus `eval` determinism (`Provable.atomNeg`) — NOT mere
          unprovability (Π₁; and premising on unprovability is the non-monotone fixpoint whose
          paradox is the anti-diagonal bot). For guards that are false-but-irrefutable (the
          anti-diagonal's own), the else-play stays TRUE BUT UNCERTIFIABLE — the honest Gödelian
          boundary (`evalC`'s `none`), no axiom papering over it.
        * The cost pays the FULL failed search budget `k` (the floor): an else-certificate must
          NEVER fit within the guard budget whose failure it certifies — otherwise
          `atom_monotone` lifts it back above `k` and re-fires the guard (the machine-checked
          inconsistency). The floor is also exactly what lets soundness be PROVEN: in the
          budget-strong-induction (`BaseTheorems.sound_upto`), a hypothetical guard proof has
          transcript ≤ k < this certificate's cost, so the induction hypothesis refutes it.
          Faithful: a PA-style proof that a bounded search fails checks every ≤`k`-length
          candidate — paying `k` characters is generous, not inflated. -/
    | search_f :
        Provable m (.neg (φ.subst me opponent)) →
        PlaysProof me opponent q a n →
        PlaysProof me opponent (.search k φ p q) a (n + m + k + c_node)

-- `AtomProvable k φ` — a `PlaysProof` whose run cost fits the budget (`n ≤ k`); the bridge for
-- atomic `.plays` facts (which `Derivation` cannot read).
  inductive AtomProvable : Nat → Formula → Prop where
    | mk : PlaysProof me opponent me a n → n ≤ k → AtomProvable k (.plays me opponent a)

-- `Provable k φ` — provable within budget `k`. Constructors fall into three groups:
--   (A) ENTRY POINTS:  `struct` (a small `Derivation`) and `atom` (an `AtomProvable`).
--   (B) IMPLICATION REASONING: `weakenImpl` / `searchThenSearch_t` / `implTrans` — rules whose
--       premises are `Provable` (so they cannot live on the `Type`-valued `Derivation`).
--   (C) MODAL / BOX RULES: `atomBoxImpl` / `boxIntro` / `app` / `axK` / `box4` — the bounded HBL
--       derivability conditions. These were added when the `box_provable` and `boxInternalize`
--       AXIOMS were eliminated (they are constructors, NOT axioms; soundness in `Provable_sound`).
  inductive Provable : Nat → Formula → Prop where
    -- ── (A) entry points ──
    | struct : (∃ d : Derivation φ, d.size ≤ k) → Provable k φ
    | atom : AtomProvable k φ → Provable k φ
    -- ── (B) implication reasoning (premises are `Provable`) ──
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
        Provable m ψ → m + (Formula.impl φ ψ).size ≤ k → Provable k (.impl φ ψ)
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
    | searchThenSearch_t (k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula) (c0 c1 : Action)
        (q me opponent : Prog)
        (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) :
        Provable m (ψ₂.subst me opponent) → m ≤ k₂ →
        m + (Formula.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0)).size ≤ k →
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
        a + b + (Formula.impl φ χ).size ≤ k → Provable k (.impl φ χ)
    -- ── (C) modal / box rules — the bounded HBL derivability conditions (constructors, not axioms) ──
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
        kBox + (Formula.impl (.plays p q a) (.box kBox (.plays p q a))).size ≤ k →
        Provable k (.impl (.plays p q a) (.box kBox (.plays p q a)))
    /-- **Box-introduction / bounded necessitation** (HBL D2, the constructive
        realization of the former axiom `box_provable`): if `φ` is provable within
        budget `kIn`, then that *fact* — `□_{kIn} φ` — is itself provable, at any output
        budget `K` at least the conclusion's character size `(.box kIn φ).size` (faithful
        to `Derivation.size = conclusion.size`; the `size ≤ K` premise makes it self-weaken,
        keeping `proofSearch_monotone`).

        Sound with NO axiom: `(□_{kIn} φ).interp` is *definitionally* `Provable kIn φ`
        (Dynamics.lean), which is exactly the premise — so the `Provable_sound` arm is
        the identity. SAFE (unlike the removed-unsound `atom_box_provable_impl`, which
        fabricated a certificate from a mere play): the premise here is genuine
        `Provable kIn φ`, so nothing false is boxed (no `Provable kIn (DefectBot plays C)`
        premise exists). Faithful: provable-Σ₁-completeness on the Σ₁ predicate
        `Provable kIn φ` (Solovay / HBL D2). The minimal witness `K = (.box kIn φ).size`
        gives the consumer the `K ≤ (.box kIn φ).size` bound the former axiom asserted. -/
    | boxIntro (kIn K : Nat) (φ : Formula) :
        Provable kIn φ →
        kIn + (Formula.box kIn φ).size ≤ K →
        Provable K (.box kIn φ)
    /-- **Object-level modus ponens** (the proof-DATA application rule): from `Provable k (φ → α)`
        and `Provable k φ`, infer `Provable k α`. POSITIVE (both premises are `Provable` VALUES, no
        transformer — kernel-legal) and SOUND with NO axiom: `interp α` follows from
        `interp (φ→α) = (φ.interp → α.interp)` applied to `interp φ` — pure function application, NO
        budget threshold (the consequent is delivered at the same budget `k` the premises hold at).

        This is the rule the abstract engine LACKED: it had modus ponens only inside `Derivation`
        (`modusPonens`, a `Type`-level rule on `struct` proofs), never as an object
        `Provable → Provable → Provable` rule. It is exactly the `app` constructor the faithful
        substrate spike (`Research/Spikes/bounded_lob/FaithfulSubstrateSpike.lean`) identified as the
        missing piece that lets `axK`'s soundness arm RUN an implication proof. -/
    | app (k m₁ m₂ : Nat) (φ α : Formula) :
        Provable m₁ (.impl φ α) → Provable m₂ φ → m₁ + m₂ + α.size ≤ k → Provable k α
    /-- **GL axiom-K at a fixed budget `k`** (the constructive realization of the former axiom
        `boxInternalize`, via a proof-TERM premise): from `Provable k (□_k (φ → α))`, infer
        `Provable k (□_k φ → □_k α)` (size permitting).

        POSITIVE — the premise `Provable k (.box k (.impl φ α))` is a `Provable` VALUE (a held proof),
        not the non-positive transformer `Provable k φ → Provable k α` the old axiom carried
        (`GLKPositiveSpike.lean`). SOUND via the object modus ponens `app`: the soundness arm needs
        `Provable k φ → Provable k α`, obtained by `app` from the boxed implication proof (whose
        `interp` `Provable k (φ→α)` is the held implication) and the hypothetical `Provable k φ`.
        Size side-condition keeps the conclusion within budget `k`, as for the other reflection rules.

        Together with `boxIntro`, derives `boxInternalize` as a THEOREM (`BaseTheorems`): box the
        held implication-proof (`boxIntro`), then `axK` distributes — no transformer, no axiom. The
        per-leg budget reconciliation (Horn B / Wall 1) is carried by each `mutual_loeb` leg's guard
        inversion, unchanged.

        The PROOF budget `K` is separate from the inner box budget `k` (with `size ≤ K`), so the rule
        self-weakens (`K` can relax) — keeping `proofSearch_monotone`, exactly as `boxIntro` does. -/
    | axK (a b c m K : Nat) (φ α : Formula) :
        Provable m (.box a (.impl φ α)) →
        a + b + α.size ≤ c →
        m + (Formula.impl (.box b φ) (.box c α)).size ≤ K →
        Provable K (.impl (.box b φ) (.box c α))
    /-- **GL axiom-4 / object necessitation** (`□_k φ → □_k (□_k φ)`): the object form of HBL D2.
        POSITIVE (no premise carrying `Provable` negatively — it is an axiom-shaped rule, size-gated).
        SOUND: its `interp` is `Provable k φ → Provable k (□_k φ)`, i.e. `Provable k φ → Provable k φ`
        (since `interp (□_k φ) = Provable k φ`) — the IDENTITY, discharged by `id` in `Provable_sound`.
        This is the object companion of the `box_provable` THEOREM (which is the META necessitation
        `Provable k φ → ∃K, Provable K (□φ)`); together with `axK` it completes the Route-2 chain that
        derives `boxInternalize` as a theorem (necessitate the searchBranch leg, `axK`-distribute,
        `box4`-inflate, chain the PrudentBot leg — `MutualLobSpike.lean` Route 2, now all constructors).
        The PROOF budget `K` is free (with `size ≤ K`), self-weakening for `proofSearch_monotone`. -/
    | box4 (a b K : Nat) (φ : Formula) :
        a + (Formula.box a φ).size ≤ b →
        (Formula.impl (.box a φ) (.box b (.box a φ))).size ≤ K →
        Provable K (.impl (.box a φ) (.box b (.box a φ)))
    -- ── (D) the Löb-fixpoint rules (internalization of the reflection layer's DERIVED diagonal;
    --        Research/Notes/INTERNALIZATION_ROADMAP.md I0, validated in Spikes/pblt/I0Design.lean) ──
    /-- **Löb-fixpoint leg, forward**: `ψ → (□_g ψ → tgt)` for the fixpoint sentence
        `ψ := .diag g tgt`. Sound with NO axiom: `ψ.interp` IS `Provable g ψ → tgt.interp`
        (Dynamics.lean) — the soundness arm is the identity. GATED on the tight Löb premise
        `Provable g (□_g tgt → tgt)`: the Löb chain always has it (it is bounded Löb's hypothesis),
        and the gate preserves the structural exclusion invariants (`cimcic_no_provable_forbidden`
        etc.): a Forbidden impl-chain in the conclusion forces the premise's chain Forbidden too,
        closing those arms. Faithful: the reflection layer DERIVES this leg from representability
        (`repr_object` with the predicate-level `selfApply`, spike B4). -/
    | diagF (pm fb g K : Nat) (tgt : Formula) :
        Provable pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)).size ≤ K →
        Provable K (.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt))
    /-- **Löb-fixpoint leg, backward**: `(□_g ψ → tgt) → ψ`. Sound = identity (as `diagF`); same
        Löb-premise gate (symmetry; its exclusion arm closes via the `.diag` catch-all regardless). -/
    | diagB (pm fb g K : Nat) (tgt : Formula) :
        Provable pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)).size ≤ K →
        Provable K (.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt))
    /-- **GL axiom-K as an object FORMULA** `□_k(φ→α) → (□_k φ → □_k α)` — the `axK` RULE form cannot
        supply Löb's middle step, which needs the implication itself as a premise-free theorem.
        Sound via `app`: the interp is `Provable k (φ→α) → Provable k φ → Provable k α`. -/
    | axKf (a b c K : Nat) (φ α : Formula) :
        a + b + α.size ≤ c →
        (Formula.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α))).size ≤ K →
        Provable K (.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α)))
    /-- **Closed composition** (the S-combinator as a rule; both premises are closed `⊢`, so the rule
        form suffices — replacing the deduction theorem the side layer needed): from `⊢ φ → (ψ → χ)`
        and `⊢ φ → ψ`, infer `⊢ φ → χ`. Sound: function application under `interp`. -/
    | impS2 (φ ψ χ : Formula) (m₁ m₂ K : Nat) :
        Provable m₁ (.impl φ (.impl ψ χ)) → Provable m₂ (.impl φ ψ) →
        m₁ + m₂ + (Formula.impl φ χ).size ≤ K → Provable K (.impl φ χ)
    /-- **Upward box-subscript monotonicity as an object formula** (`□_a φ → □_b φ` for `a ≤ b`):
        a ≤a-cost proof IS a ≤b-cost proof, so the implication is sound — its `interp` is
        `Provable a φ → Provable b φ`, discharged by budget monotonicity (`Provable_mono`).
        NEW with the transcript cost model (T0 freeze): the conclusion-cost model never needed it,
        but under additive budgets the Löb chain's K-distribution outputs land at computed
        subscripts that must be weakened UP onto the consumers' source-literal boxes
        (`Research/Spikes/transcript/T0Transcript.lean`). Appended LAST to keep the positional
        recursors' prefix order stable. -/
    | boxMono (a b K : Nat) (φ : Formula) :
        a ≤ b →
        (Formula.impl (.box a φ) (.box b φ)).size ≤ K →
        Provable K (.impl (.box a φ) (.box b φ))
    /-- **Refutation of a play-atom from a certificate of the actual play** (eval determinism):
        if `p` provably plays `b` (a real certificate) and `b ≠ aN`, then `¬(p plays aN)` —
        sound by `eval` fuel-monotonicity (a committed `b`-play excludes an `aN`-play at every
        fuel). This is the Σ₁ refutation that `search_f` consumes; NEW with the false-guard
        repair (2026-07-02). Transcript-charged like every rule. -/
    | atomNeg (p q : Prog) (b aN : Action) (m : Nat) :
        AtomProvable m (.plays p q b) → b ≠ aN →
        m + (Formula.neg (.plays p q aN)).size ≤ k →
        Provable k (.neg (.plays p q aN))
end

-- 4. The proof-search oracle: bounded provability reflected into `Bool` for the
-- evaluator's guard. Classical (hence noncomputable), correct for an oracle.
noncomputable def proofSearch (k : Nat) (φ : Formula) : Bool := decide (Provable k φ)


/-- 5. Character budget for a `fuel`-step play's atom certificate. Honest `O(fuel)`
    (Critch's `e*`, Appendix B(d)): `c_node + c_guard fuel` per step, plus a leaf.
    `c_guard fuel` over-approximates every guard budget reachable in the run. -/
def atom_cost (fuel : Nat) : Nat := c_leaf + (c_node + c_guard fuel) * fuel


end PD
