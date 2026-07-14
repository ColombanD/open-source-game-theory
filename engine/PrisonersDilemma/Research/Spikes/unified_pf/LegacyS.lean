import PrisonersDilemma.Program
import PrisonersDilemma.Derivation

/-!
# LegacyS — the FROZEN pre-migration proof system `S` (namespace `PD.Legacy`)

**Phase 0 artifact of `Research/Notes/PF_ONLY_ROADMAP.md`.** A verbatim, self-contained copy of
the proof system as it stood BEFORE the `Pf`-only migration: `Derivation` (Type-valued, with its
structural `.size`) and the mutual `PlaysProof`/`AtomProvable`/`Provable` block. Extracted
mechanically from `Derivation.lean` at commit `1e711ee` (branch `pf-only`), then
re-namespaced `PD` → `PD.Legacy` — nothing else changed.

## Why this file exists

Phase 1 OVERWRITES `Derivation.lean` with the unified mutual block `{PlaysProof, AtomProvable,
Pf}` and DELETES `Derivation`/`Provable`. That changes the very relation the evaluator's oracle
consults (`proofSearch k φ := decide (Provable k φ)` becomes `decide (Pf k φ)`). Without an
anchor, "the bots still behave the same" would rest on re-running theorems whose *meaning* had
silently moved.

This snapshot is that anchor. The FIDELITY section below proves, today, that the copy is the same
relation as the live engine (`legacy_iff_live`); Phase 1 then proves `Pf k φ ↔ Legacy.Provable k φ`
against this frozen copy. Composing the two spans the migration:

    Pf  ↔  Legacy.Provable  ↔  (the S that proved the 81 golden outcomes)

so "the new oracle decides exactly the old relation" is a THEOREM, not a regression test.

## Invariants

* Depends only on `Program.lean` (syntax, `subst`, `size`, `numCost`) plus — for the fidelity
  section only — the live `Derivation.lean`. Phase 1 replaces the fidelity section's right-hand
  side with `Pf`; the frozen definitions themselves never change again.
* Costs are duplicated locally (`c_leaf`/`c_node`/`c_guard`) so a change to the engine's cost
  constants cannot silently rewrite the baseline — the fidelity `rfl`s below would break loudly.
* If any edit desynchronizes the snapshot from the live system, the fidelity section STOPS
  COMPILING. That is the intended alarm: the baseline may only be re-frozen deliberately.
* NOT root-imported. **Retire in Phase 4.5** (archive with a tombstone header).

Check: `lake env lean PrisonersDilemma/Research/Spikes/unified_pf/LegacyS.lean`
-/

namespace PD.Legacy

open PD

/-! ## Cost constants (frozen local copies — see the invariants above). -/

def c_leaf  : Nat := 1
def c_node  : Nat := 1
def c_guard (k : Nat) : Nat := numCost k

/-! ## The `Derivation` system (Type-valued — the half the migration merges away). -/

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


/-! ## Transcript size (structural recursion — the reason `Derivation` had to be `Type`). -/

def Derivation.size : {φ : Formula} → Derivation φ → Nat
  | _, .modusPonens _ ψ d1 d2 => d1.size + d2.size + ψ.size
  | _, .hypSyll φ _ χ d1 d2 => d1.size + d2.size + (Formula.impl φ χ).size
  | φ, _ => φ.size

/-! ## The mutual block: play certificates + atom bridge + `Provable`. -/

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
        c_guard k₂ +
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

/-! # ═══════════════════════════════════════════════════════════════════════════════════════
    ## FIDELITY — this frozen snapshot IS the live engine's `S` (the Phase-0 anchor)

A copy is only a trustworthy baseline if it is *provably* the same relation as the thing it
copies. We discharge that here, while both systems still exist:

    Legacy.Provable k φ  ↔  PD.Provable k φ        (every budget, both directions)

After Phase 1 deletes `PD.Provable`, this section's right-hand side becomes `Pf` — same proof
shape (the two rule sets are constructor-for-constructor twins, so every arm is its own image).
Composing gives `Pf ↔ Legacy.Provable ↔ (the S that proved the 81 golden outcomes)`.

If a future edit desynchronizes the snapshot, THIS SECTION STOPS COMPILING — the intended alarm.
    ═══════════════════════════════════════════════════════════════════════════════════════ -/

/-! ### Sanity: the frozen cost constants agree with the live ones (`rfl`). -/

example : Legacy.c_leaf = PD.c_leaf := rfl
example : Legacy.c_node = PD.c_node := rfl
example (k : Nat) : Legacy.c_guard k = PD.c_guard k := rfl

/-! ### `Derivation`: the two `Type`-valued systems agree, AT THE SAME SIZE.

The size equality is what makes the `struct` budgets transfer, so it is proved alongside the
embedding, not after it. -/

/-- Every legacy `Derivation` is a live one, at the same transcript size. -/
theorem deriv_fwd : ∀ {φ : Formula} (d : Legacy.Derivation φ),
    ∃ d' : PD.Derivation φ, d'.size = d.size := by
  intro φ d
  induction d with
  | modusPonens φ' ψ d1 d2 ih1 ih2 =>
      obtain ⟨e1, h1⟩ := ih1; obtain ⟨e2, h2⟩ := ih2
      exact ⟨.modusPonens φ' ψ e1 e2, by
        simp [PD.Derivation.size, Legacy.Derivation.size, h1, h2]⟩
  | hypSyll φ' ψ χ d1 d2 ih1 ih2 =>
      obtain ⟨e1, h1⟩ := ih1; obtain ⟨e2, h2⟩ := ih2
      exact ⟨.hypSyll φ' ψ χ e1 e2, by
        simp [PD.Derivation.size, Legacy.Derivation.size, h1, h2]⟩
  | searchBranch k ψ a b me opponent hme => exact ⟨.searchBranch k ψ a b me opponent hme, rfl⟩
  | simStep me p q opponent a hme => exact ⟨.simStep me p q opponent a hme, rfl⟩
  | botSimStep me p q opponent a hme => exact ⟨.botSimStep me p q opponent a hme, rfl⟩
  | botSearchStep k ψ a b me opponent hme =>
      exact ⟨.botSearchStep k ψ a b me opponent hme, rfl⟩
  | iteBranchSearch_t k z a' c0 c1 ψ q me opponent hme =>
      exact ⟨.iteBranchSearch_t k z a' c0 c1 ψ q me opponent hme, rfl⟩
  | eqRefl p => exact ⟨.eqRefl p, rfl⟩
  | eqNeg p q hne => exact ⟨.eqNeg p q hne, rfl⟩

/-- …and conversely. -/
theorem deriv_bwd : ∀ {φ : Formula} (d : PD.Derivation φ),
    ∃ d' : Legacy.Derivation φ, d'.size = d.size := by
  intro φ d
  induction d with
  | modusPonens φ' ψ d1 d2 ih1 ih2 =>
      obtain ⟨e1, h1⟩ := ih1; obtain ⟨e2, h2⟩ := ih2
      exact ⟨.modusPonens φ' ψ e1 e2, by
        simp [PD.Derivation.size, Legacy.Derivation.size, h1, h2]⟩
  | hypSyll φ' ψ χ d1 d2 ih1 ih2 =>
      obtain ⟨e1, h1⟩ := ih1; obtain ⟨e2, h2⟩ := ih2
      exact ⟨.hypSyll φ' ψ χ e1 e2, by
        simp [PD.Derivation.size, Legacy.Derivation.size, h1, h2]⟩
  | searchBranch k ψ a b me opponent hme => exact ⟨.searchBranch k ψ a b me opponent hme, rfl⟩
  | simStep me p q opponent a hme => exact ⟨.simStep me p q opponent a hme, rfl⟩
  | botSimStep me p q opponent a hme => exact ⟨.botSimStep me p q opponent a hme, rfl⟩
  | botSearchStep k ψ a b me opponent hme =>
      exact ⟨.botSearchStep k ψ a b me opponent hme, rfl⟩
  | iteBranchSearch_t k z a' c0 c1 ψ q me opponent hme =>
      exact ⟨.iteBranchSearch_t k z a' c0 c1 ψ q me opponent hme, rfl⟩
  | eqRefl p => exact ⟨.eqRefl p, rfl⟩
  | eqNeg p q hne => exact ⟨.eqNeg p q hne, rfl⟩

/-! ### The mutual block: `Provable` and its two companions agree.

The block is mutual, so all three motives must ride in the SAME induction (`Provable.atom` /
`atomNeg` / `atomBoxImpl` consume the certificate halves). Hence: one recursor application per
entry type, each carrying all three motives. Every arm is the same-named constructor of the other
system — the snapshot is verbatim, so the twins line up exactly. -/

/-- Legacy ⟶ live, all three components. -/
theorem legacy_to_live :
    (∀ {me opponent body : Prog} {a : Action} {n : Nat},
        Legacy.PlaysProof me opponent body a n → PD.PlaysProof me opponent body a n)
    ∧ (∀ {k : Nat} {φ : Formula}, Legacy.AtomProvable k φ → PD.AtomProvable k φ)
    ∧ (∀ {k : Nat} {φ : Formula}, Legacy.Provable k φ → PD.Provable k φ) := by
  refine ⟨fun h => ?fwdP, fun h => ?fwdA, fun h => ?fwdPr⟩
  case fwdP =>
    exact Legacy.PlaysProof.rec
      (motive_1 := fun me opponent body a n _ => PD.PlaysProof me opponent body a n)
      (motive_2 := fun k φ _ => PD.AtomProvable k φ)
      (motive_3 := fun k φ _ => PD.Provable k φ)
      PD.PlaysProof.const
      (fun _ ih => PD.PlaysProof.self ih) (fun _ ih => PD.PlaysProof.opp ih)
      (fun _ ih => PD.PlaysProof.bot ih) (fun _ ih => PD.PlaysProof.sim ih)
      (fun _ hr _ ihb ihp => PD.PlaysProof.ite_t ihb hr ihp)
      (fun _ hr _ ihb ihq => PD.PlaysProof.ite_f ihb hr ihq)
      (fun _ _ ihg ihp => PD.PlaysProof.search_t ihg ihp)
      (fun _ _ ihg ihq => PD.PlaysProof.search_f ihg ihq)
      (fun _ hle ih => PD.AtomProvable.mk ih hle)
      (fun hd => PD.Provable.struct
        (hd.elim fun d hsz => (deriv_fwd d).elim fun d' hd' => ⟨d', hd' ▸ hsz⟩))
      (fun _ ih => PD.Provable.atom ih)
      (fun φ ψ m _ hle ih => PD.Provable.weakenImpl φ ψ m ih hle)
      (fun k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme _ hmk hle ih =>
        PD.Provable.searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme ih hmk hle)
      (fun φ ψ χ a b _ _ hle ih1 ih2 => PD.Provable.implTrans φ ψ χ a b ih1 ih2 hle)
      (fun kBox p q a _ hle ih => PD.Provable.atomBoxImpl kBox p q a ih hle)
      (fun kIn K φ _ hle ih => PD.Provable.boxIntro kIn K φ ih hle)
      (fun k m₁ m₂ φ α _ _ hle ih1 ih2 => PD.Provable.app k m₁ m₂ φ α ih1 ih2 hle)
      (fun a b c m K φ α _ hgate hle ih => PD.Provable.axK a b c m K φ α ih hgate hle)
      (fun a b K φ hgate hsz => PD.Provable.box4 a b K φ hgate hsz)
      (fun pm fb g K tgt _ hle ih => PD.Provable.diagF pm fb g K tgt ih hle)
      (fun pm fb g K tgt _ hle ih => PD.Provable.diagB pm fb g K tgt ih hle)
      (fun a b c K φ α hgate hsz => PD.Provable.axKf a b c K φ α hgate hsz)
      (fun φ ψ χ m₁ m₂ K _ _ hle ih1 ih2 => PD.Provable.impS2 φ ψ χ m₁ m₂ K ih1 ih2 hle)
      (fun a b K φ hab hsz => PD.Provable.boxMono a b K φ hab hsz)
      (fun p q b aN m _ hne hle ih => PD.Provable.atomNeg p q b aN m ih hne hle)
      h
  case fwdA =>
    exact Legacy.AtomProvable.rec
      (motive_1 := fun me opponent body a n _ => PD.PlaysProof me opponent body a n)
      (motive_2 := fun k φ _ => PD.AtomProvable k φ)
      (motive_3 := fun k φ _ => PD.Provable k φ)
      PD.PlaysProof.const
      (fun _ ih => PD.PlaysProof.self ih) (fun _ ih => PD.PlaysProof.opp ih)
      (fun _ ih => PD.PlaysProof.bot ih) (fun _ ih => PD.PlaysProof.sim ih)
      (fun _ hr _ ihb ihp => PD.PlaysProof.ite_t ihb hr ihp)
      (fun _ hr _ ihb ihq => PD.PlaysProof.ite_f ihb hr ihq)
      (fun _ _ ihg ihp => PD.PlaysProof.search_t ihg ihp)
      (fun _ _ ihg ihq => PD.PlaysProof.search_f ihg ihq)
      (fun _ hle ih => PD.AtomProvable.mk ih hle)
      (fun hd => PD.Provable.struct
        (hd.elim fun d hsz => (deriv_fwd d).elim fun d' hd' => ⟨d', hd' ▸ hsz⟩))
      (fun _ ih => PD.Provable.atom ih)
      (fun φ ψ m _ hle ih => PD.Provable.weakenImpl φ ψ m ih hle)
      (fun k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme _ hmk hle ih =>
        PD.Provable.searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme ih hmk hle)
      (fun φ ψ χ a b _ _ hle ih1 ih2 => PD.Provable.implTrans φ ψ χ a b ih1 ih2 hle)
      (fun kBox p q a _ hle ih => PD.Provable.atomBoxImpl kBox p q a ih hle)
      (fun kIn K φ _ hle ih => PD.Provable.boxIntro kIn K φ ih hle)
      (fun k m₁ m₂ φ α _ _ hle ih1 ih2 => PD.Provable.app k m₁ m₂ φ α ih1 ih2 hle)
      (fun a b c m K φ α _ hgate hle ih => PD.Provable.axK a b c m K φ α ih hgate hle)
      (fun a b K φ hgate hsz => PD.Provable.box4 a b K φ hgate hsz)
      (fun pm fb g K tgt _ hle ih => PD.Provable.diagF pm fb g K tgt ih hle)
      (fun pm fb g K tgt _ hle ih => PD.Provable.diagB pm fb g K tgt ih hle)
      (fun a b c K φ α hgate hsz => PD.Provable.axKf a b c K φ α hgate hsz)
      (fun φ ψ χ m₁ m₂ K _ _ hle ih1 ih2 => PD.Provable.impS2 φ ψ χ m₁ m₂ K ih1 ih2 hle)
      (fun a b K φ hab hsz => PD.Provable.boxMono a b K φ hab hsz)
      (fun p q b aN m _ hne hle ih => PD.Provable.atomNeg p q b aN m ih hne hle)
      h
  case fwdPr =>
    exact Legacy.Provable.rec
      (motive_1 := fun me opponent body a n _ => PD.PlaysProof me opponent body a n)
      (motive_2 := fun k φ _ => PD.AtomProvable k φ)
      (motive_3 := fun k φ _ => PD.Provable k φ)
      PD.PlaysProof.const
      (fun _ ih => PD.PlaysProof.self ih) (fun _ ih => PD.PlaysProof.opp ih)
      (fun _ ih => PD.PlaysProof.bot ih) (fun _ ih => PD.PlaysProof.sim ih)
      (fun _ hr _ ihb ihp => PD.PlaysProof.ite_t ihb hr ihp)
      (fun _ hr _ ihb ihq => PD.PlaysProof.ite_f ihb hr ihq)
      (fun _ _ ihg ihp => PD.PlaysProof.search_t ihg ihp)
      (fun _ _ ihg ihq => PD.PlaysProof.search_f ihg ihq)
      (fun _ hle ih => PD.AtomProvable.mk ih hle)
      (fun hd => PD.Provable.struct
        (hd.elim fun d hsz => (deriv_fwd d).elim fun d' hd' => ⟨d', hd' ▸ hsz⟩))
      (fun _ ih => PD.Provable.atom ih)
      (fun φ ψ m _ hle ih => PD.Provable.weakenImpl φ ψ m ih hle)
      (fun k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme _ hmk hle ih =>
        PD.Provable.searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme ih hmk hle)
      (fun φ ψ χ a b _ _ hle ih1 ih2 => PD.Provable.implTrans φ ψ χ a b ih1 ih2 hle)
      (fun kBox p q a _ hle ih => PD.Provable.atomBoxImpl kBox p q a ih hle)
      (fun kIn K φ _ hle ih => PD.Provable.boxIntro kIn K φ ih hle)
      (fun k m₁ m₂ φ α _ _ hle ih1 ih2 => PD.Provable.app k m₁ m₂ φ α ih1 ih2 hle)
      (fun a b c m K φ α _ hgate hle ih => PD.Provable.axK a b c m K φ α ih hgate hle)
      (fun a b K φ hgate hsz => PD.Provable.box4 a b K φ hgate hsz)
      (fun pm fb g K tgt _ hle ih => PD.Provable.diagF pm fb g K tgt ih hle)
      (fun pm fb g K tgt _ hle ih => PD.Provable.diagB pm fb g K tgt ih hle)
      (fun a b c K φ α hgate hsz => PD.Provable.axKf a b c K φ α hgate hsz)
      (fun φ ψ χ m₁ m₂ K _ _ hle ih1 ih2 => PD.Provable.impS2 φ ψ χ m₁ m₂ K ih1 ih2 hle)
      (fun a b K φ hab hsz => PD.Provable.boxMono a b K φ hab hsz)
      (fun p q b aN m _ hne hle ih => PD.Provable.atomNeg p q b aN m ih hne hle)
      h

/-- Live ⟶ legacy, all three components. -/
theorem live_to_legacy :
    (∀ {me opponent body : Prog} {a : Action} {n : Nat},
        PD.PlaysProof me opponent body a n → Legacy.PlaysProof me opponent body a n)
    ∧ (∀ {k : Nat} {φ : Formula}, PD.AtomProvable k φ → Legacy.AtomProvable k φ)
    ∧ (∀ {k : Nat} {φ : Formula}, PD.Provable k φ → Legacy.Provable k φ) := by
  refine ⟨fun h => ?bwdP, fun h => ?bwdA, fun h => ?bwdPr⟩
  case bwdP =>
    exact PD.PlaysProof.rec
      (motive_1 := fun me opponent body a n _ => Legacy.PlaysProof me opponent body a n)
      (motive_2 := fun k φ _ => Legacy.AtomProvable k φ)
      (motive_3 := fun k φ _ => Legacy.Provable k φ)
      Legacy.PlaysProof.const
      (fun _ ih => Legacy.PlaysProof.self ih) (fun _ ih => Legacy.PlaysProof.opp ih)
      (fun _ ih => Legacy.PlaysProof.bot ih) (fun _ ih => Legacy.PlaysProof.sim ih)
      (fun _ hr _ ihb ihp => Legacy.PlaysProof.ite_t ihb hr ihp)
      (fun _ hr _ ihb ihq => Legacy.PlaysProof.ite_f ihb hr ihq)
      (fun _ _ ihg ihp => Legacy.PlaysProof.search_t ihg ihp)
      (fun _ _ ihg ihq => Legacy.PlaysProof.search_f ihg ihq)
      (fun _ hle ih => Legacy.AtomProvable.mk ih hle)
      (fun hd => Legacy.Provable.struct
        (hd.elim fun d hsz => (deriv_bwd d).elim fun d' hd' => ⟨d', hd' ▸ hsz⟩))
      (fun _ ih => Legacy.Provable.atom ih)
      (fun φ ψ m _ hle ih => Legacy.Provable.weakenImpl φ ψ m ih hle)
      (fun k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme _ hmk hle ih =>
        Legacy.Provable.searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme ih hmk hle)
      (fun φ ψ χ a b _ _ hle ih1 ih2 => Legacy.Provable.implTrans φ ψ χ a b ih1 ih2 hle)
      (fun kBox p q a _ hle ih => Legacy.Provable.atomBoxImpl kBox p q a ih hle)
      (fun kIn K φ _ hle ih => Legacy.Provable.boxIntro kIn K φ ih hle)
      (fun k m₁ m₂ φ α _ _ hle ih1 ih2 => Legacy.Provable.app k m₁ m₂ φ α ih1 ih2 hle)
      (fun a b c m K φ α _ hgate hle ih => Legacy.Provable.axK a b c m K φ α ih hgate hle)
      (fun a b K φ hgate hsz => Legacy.Provable.box4 a b K φ hgate hsz)
      (fun pm fb g K tgt _ hle ih => Legacy.Provable.diagF pm fb g K tgt ih hle)
      (fun pm fb g K tgt _ hle ih => Legacy.Provable.diagB pm fb g K tgt ih hle)
      (fun a b c K φ α hgate hsz => Legacy.Provable.axKf a b c K φ α hgate hsz)
      (fun φ ψ χ m₁ m₂ K _ _ hle ih1 ih2 => Legacy.Provable.impS2 φ ψ χ m₁ m₂ K ih1 ih2 hle)
      (fun a b K φ hab hsz => Legacy.Provable.boxMono a b K φ hab hsz)
      (fun p q b aN m _ hne hle ih => Legacy.Provable.atomNeg p q b aN m ih hne hle)
      h
  case bwdA =>
    exact PD.AtomProvable.rec
      (motive_1 := fun me opponent body a n _ => Legacy.PlaysProof me opponent body a n)
      (motive_2 := fun k φ _ => Legacy.AtomProvable k φ)
      (motive_3 := fun k φ _ => Legacy.Provable k φ)
      Legacy.PlaysProof.const
      (fun _ ih => Legacy.PlaysProof.self ih) (fun _ ih => Legacy.PlaysProof.opp ih)
      (fun _ ih => Legacy.PlaysProof.bot ih) (fun _ ih => Legacy.PlaysProof.sim ih)
      (fun _ hr _ ihb ihp => Legacy.PlaysProof.ite_t ihb hr ihp)
      (fun _ hr _ ihb ihq => Legacy.PlaysProof.ite_f ihb hr ihq)
      (fun _ _ ihg ihp => Legacy.PlaysProof.search_t ihg ihp)
      (fun _ _ ihg ihq => Legacy.PlaysProof.search_f ihg ihq)
      (fun _ hle ih => Legacy.AtomProvable.mk ih hle)
      (fun hd => Legacy.Provable.struct
        (hd.elim fun d hsz => (deriv_bwd d).elim fun d' hd' => ⟨d', hd' ▸ hsz⟩))
      (fun _ ih => Legacy.Provable.atom ih)
      (fun φ ψ m _ hle ih => Legacy.Provable.weakenImpl φ ψ m ih hle)
      (fun k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme _ hmk hle ih =>
        Legacy.Provable.searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme ih hmk hle)
      (fun φ ψ χ a b _ _ hle ih1 ih2 => Legacy.Provable.implTrans φ ψ χ a b ih1 ih2 hle)
      (fun kBox p q a _ hle ih => Legacy.Provable.atomBoxImpl kBox p q a ih hle)
      (fun kIn K φ _ hle ih => Legacy.Provable.boxIntro kIn K φ ih hle)
      (fun k m₁ m₂ φ α _ _ hle ih1 ih2 => Legacy.Provable.app k m₁ m₂ φ α ih1 ih2 hle)
      (fun a b c m K φ α _ hgate hle ih => Legacy.Provable.axK a b c m K φ α ih hgate hle)
      (fun a b K φ hgate hsz => Legacy.Provable.box4 a b K φ hgate hsz)
      (fun pm fb g K tgt _ hle ih => Legacy.Provable.diagF pm fb g K tgt ih hle)
      (fun pm fb g K tgt _ hle ih => Legacy.Provable.diagB pm fb g K tgt ih hle)
      (fun a b c K φ α hgate hsz => Legacy.Provable.axKf a b c K φ α hgate hsz)
      (fun φ ψ χ m₁ m₂ K _ _ hle ih1 ih2 => Legacy.Provable.impS2 φ ψ χ m₁ m₂ K ih1 ih2 hle)
      (fun a b K φ hab hsz => Legacy.Provable.boxMono a b K φ hab hsz)
      (fun p q b aN m _ hne hle ih => Legacy.Provable.atomNeg p q b aN m ih hne hle)
      h
  case bwdPr =>
    exact PD.Provable.rec
      (motive_1 := fun me opponent body a n _ => Legacy.PlaysProof me opponent body a n)
      (motive_2 := fun k φ _ => Legacy.AtomProvable k φ)
      (motive_3 := fun k φ _ => Legacy.Provable k φ)
      Legacy.PlaysProof.const
      (fun _ ih => Legacy.PlaysProof.self ih) (fun _ ih => Legacy.PlaysProof.opp ih)
      (fun _ ih => Legacy.PlaysProof.bot ih) (fun _ ih => Legacy.PlaysProof.sim ih)
      (fun _ hr _ ihb ihp => Legacy.PlaysProof.ite_t ihb hr ihp)
      (fun _ hr _ ihb ihq => Legacy.PlaysProof.ite_f ihb hr ihq)
      (fun _ _ ihg ihp => Legacy.PlaysProof.search_t ihg ihp)
      (fun _ _ ihg ihq => Legacy.PlaysProof.search_f ihg ihq)
      (fun _ hle ih => Legacy.AtomProvable.mk ih hle)
      (fun hd => Legacy.Provable.struct
        (hd.elim fun d hsz => (deriv_bwd d).elim fun d' hd' => ⟨d', hd' ▸ hsz⟩))
      (fun _ ih => Legacy.Provable.atom ih)
      (fun φ ψ m _ hle ih => Legacy.Provable.weakenImpl φ ψ m ih hle)
      (fun k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme _ hmk hle ih =>
        Legacy.Provable.searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme ih hmk hle)
      (fun φ ψ χ a b _ _ hle ih1 ih2 => Legacy.Provable.implTrans φ ψ χ a b ih1 ih2 hle)
      (fun kBox p q a _ hle ih => Legacy.Provable.atomBoxImpl kBox p q a ih hle)
      (fun kIn K φ _ hle ih => Legacy.Provable.boxIntro kIn K φ ih hle)
      (fun k m₁ m₂ φ α _ _ hle ih1 ih2 => Legacy.Provable.app k m₁ m₂ φ α ih1 ih2 hle)
      (fun a b c m K φ α _ hgate hle ih => Legacy.Provable.axK a b c m K φ α ih hgate hle)
      (fun a b K φ hgate hsz => Legacy.Provable.box4 a b K φ hgate hsz)
      (fun pm fb g K tgt _ hle ih => Legacy.Provable.diagF pm fb g K tgt ih hle)
      (fun pm fb g K tgt _ hle ih => Legacy.Provable.diagB pm fb g K tgt ih hle)
      (fun a b c K φ α hgate hsz => Legacy.Provable.axKf a b c K φ α hgate hsz)
      (fun φ ψ χ m₁ m₂ K _ _ hle ih1 ih2 => Legacy.Provable.impS2 φ ψ χ m₁ m₂ K ih1 ih2 hle)
      (fun a b K φ hab hsz => Legacy.Provable.boxMono a b K φ hab hsz)
      (fun p q b aN m _ hne hle ih => Legacy.Provable.atomNeg p q b aN m ih hne hle)
      h

/-- **THE PHASE-0 ANCHOR** — the frozen snapshot decides exactly the relation the live engine's
    oracle decides, at every budget, both directions. The 81 golden outcomes were proved against
    the right-hand side; Phase 1 re-anchors `Pf` to the left-hand side. -/
theorem legacy_iff_live {k : Nat} {φ : Formula} : Legacy.Provable k φ ↔ PD.Provable k φ :=
  ⟨legacy_to_live.2.2, live_to_legacy.2.2⟩

/-- Corollary: the ORACLE is literally unchanged by re-basing it on the snapshot. This is the
    statement Phase 1 must preserve with `Pf` in place of `PD.Provable`. (`proofSearch` is
    classical/noncomputable, hence the `Classical` decidability instance.) -/
theorem proofSearch_eq_legacy {k : Nat} {φ : Formula} :
    PD.proofSearch k φ = @decide (Legacy.Provable k φ) (Classical.propDecidable _) := by
  simp only [PD.proofSearch]
  congr 1
  exact propext legacy_iff_live.symm

#check @legacy_iff_live
#check @proofSearch_eq_legacy
#print axioms legacy_iff_live

end PD.Legacy
