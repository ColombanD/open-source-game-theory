import PrisonersDilemma.Program

namespace PD
open Classical


/-!
# The proof system `S` — ONE unified proof-term type `Pf`

The agents' internal logic, made explicit. One mutual `inductive` block defines three
objects — reasoning and execution, no longer split by a `Type`/`Prop` boundary:

```
        ┌──────────────────────────────────────────────────────────┐
        │  Pf k φ   ("φ has a proof transcript of ≤ k characters") │  ← the oracle `.search` asks
        │  = source transparency (S reads `Prog`)                  │
        │  | logical core (ONE `mp`, ONE `implTrans`, `weakenImpl`)│
        │  | modal / HBL tier (boxIntro, axK, box4, diag legs, …)  │
        │  | atom  ─────────────────────────┐  (the ONE bridge     │
        └───────────────────────────────────┼───  from execution)  │
                                            │                      │
                              ┌─────────────▼────────┐             │
                              │ AtomProvable k φ     │             │
                              │ = PlaysProof + n ≤ k │             │
                              └─────────────┬────────┘             │
                                            │                      │
                                   ┌────────▼────────┐             │
                                   │  PlaysProof     │◄────────────┘
                                   │= eval transcript│  (`search_t`/`search_f` guards
                                   └─────────────────┘   consult `Pf` — the back-edge)
```

* **`Pf k φ`** — the proof system `S`, as a single `Prop`-valued, budget-INDEXED proof-term
  type (27 constructors). `k` is the character count of the whole proof transcript
  (Critch's literal cost model, Appendix B). THREE FAMILIES (declaration order):
  - **Family A — READING RULES** (11): transparency. A1, the execution bridge — `atom`
    (the ONE entry from `PlaysProof`) and its Σ₁ refutation twin `atomNeg`. A2, source
    transparency — "S reads `Prog` source", one rule per syntactic shape it inspects
    (`searchBranch`, `simStep`, `botSimStep`, `botSearchStep`, `iteBranchSearch_t`,
    `searchThenSearch_t`, the depth-general telescope `searchChain`, `eqRefl`,
    `eqNeg`); Appendix B(a). Each carries its conclusion's
    size as the budget side-condition. This family tracks the (FROZEN) `Prog` grammar:
    it grows only when a new nesting shape must become readable.
  - **Family B — LOGICAL GLUE** (8): the propositional core — `mp` (modus ponens),
    `implTrans` (hypothetical syllogism), `weakenImpl`, `impS2` (closed composition),
    the completion leaves `implRefl` (`⊢ φ → φ`) and `implK` (`⊢ φ → (ψ → φ)`,
    which with `mp` derives `weakenImpl`), and the `.neg`-consumers `contrapose` and
    `negElim` (ex falso — VACUOUS in the consistent `S`, see its docstring). With
    these, Family B is the Hilbert basis for the impl/neg fragment minus the
    deduction theorem: COMPLETE.
    An implication-INTRODUCTION (deduction theorem) is DELIBERATELY absent: it would take a
    PA-like `S` to full intuitionistic logic and break faithfulness/bounds. This is why
    `implTrans`/`impS2` are primitive (they cannot be derived from `mp`).
  - **Family C — LÖB MACHINERY** (8): modal / HBL tier — the bounded derivability
    conditions (`boxIntro` = D2-necessitation, `atomBoxImpl` = atom Σ₁-completeness,
    `axK`/`axKf` = K-distribution, `box4` = object D2, `boxMono`) and the Löb-fixpoint
    legs (`diagF`/`diagB`), which internalize the diagonal that makes bounded Löb a
    THEOREM rather than an axiom.
* **`PlaysProof me opp body a n`** — a *play certificate*: a finite, character-costed transcript
  of `body` evaluating to `a` (one constructor per `eval`-step). Its `.search` guards consult
  `Pf` — this back-edge is why the block is mutual.
* **`AtomProvable k φ`** — a `PlaysProof` whose cost fits the budget (`n ≤ k`); the bridge for
  atomic `.plays` facts (which the reasoning rules cannot read).
* **`proofSearch k φ`** — the oracle agents query, *defined* as decidable `Pf`.

`Formula.interp` (Dynamics.lean) interprets `Formula`; `Pf_sound` (BaseTheorems.lean) bridges
`provability → truth`.

## The eliminators (`Pf.induct`, `PlaysProof.induct`) — READ THIS BEFORE PROVING

`Pf` is MUTUAL (the `search_t`/`search_f` back-edge above), and Lean's `induction … with`
tactic does not handle mutual inductives: it would force every proof into the raw 37-minor-
premise positional recursor. So this file ships **named `@[elab_as_elim]` eliminators**
(§4): use

    induction h using Pf.induct with
    | atom … | mp … | searchBranch … | …

and NEVER call `Pf.rec`/`PlaysProof.rec` directly outside §4. The motives take the proof term
(`motive : ∀ k φ, Pf k φ → Prop`) — a proof-irrelevant motive breaks `induction using`'s target
computation. Validated in `Research/Spikes/unified_pf/PfMutualInductSpike.lean`.

## History — why ONE type (and why it used to be two)

`S` was formerly split across `Derivation : Formula → Type` (structural rules) and
`Provable : Nat → Formula → Prop` (reflection rules), glued by `Provable.struct`/`.atom`. The
split existed for ONE reason: `Derivation.size` was defined by structural recursion, which
`Prop` forbids. The 2026-07-02 transcript-cost refactor made the budget an INDEX instead (the
`PlaysProof` pattern), removing that reason — so the two collapse into `Pf`, and with them the
`modusPonens`/`app` and `hypSyll`/`implTrans` duplicate pairs (25 constructors → 22; 27 since the 2026-07-28 family completion) and the
glue. The merge shipped first as a coexistence layer with an exact round-trip
`Pf k φ ↔ Provable k φ`; this file is the completed migration (`Research/Notes/PF_ONLY_ROADMAP.md`).
The frozen pre-migration system and the theorem that `Pf` decides exactly its relation live in
`Research/Spikes/unified_pf/LegacyS.lean`.

## ZERO axioms

Every principle of `S` in this file is a sound constructor; nothing is postulated. The former
`atom_complete_false_guard` axiom was machine-checked INCONSISTENT (the anti-diagonal bot —
`Research/Spikes/transcript/T32Inconsistency.lean`) and is replaced by the sound false-guard
machinery: `PlaysProof.search_f` (else-certificates from a REFUTATION of the guard, paying the
full failed budget — the floor), `Pf.atomNeg` (refute a play-atom from a certificate of the
actual play — eval determinism), and `Pf.eqNeg` (refute structural identity of distinct
programs). Soundness is `BaseTheorems.sound_upto`, a strong induction on the budget — the floor
is what makes `search_f`'s arm provable. Guards that are false but IRREFUTABLE (the
anti-diagonal's own) leave their else-plays true-but-uncertifiable: the honest Gödelian
boundary. Costs are TRANSCRIPT-cumulative throughout (`DECIDABILITY_ROADMAP.md`).
-/

-- 1. Per-step proof-encoding costs (Critch's `e*`, Appendix B(d)): the character
-- cost of transcribing one `eval`-step into a proof. Concrete (not opaque): every
-- step costs ≥ 1 character, so a fuel-`n` play certificate has ≤ `n` steps — this is
-- what makes the decision procedure terminate, and lets the cost be *computed* rather
-- than reasoned about classically. `c_guard k = numCost k` is the `O(lg k)` character
-- cost of writing the budget numeral `k` (Appendix B(b)).
def c_leaf  : Nat := 1                          -- leaf step (`.const a`)
def c_node  : Nat := 1                          -- structural step (`.self`/`.opp`/`.bot`/`.sim`/`.ite`)
def c_guard (k : Nat) : Nat := numCost k        -- `.search` guard at budget `k`; grows with `k`

/-! ### The search telescope (Family-A closure over `.search` nesting, 2026-07-28)

A telescope is a list of `.search` layers — (guard budget, guard formula, else-branch)
per layer — wrapped around a constant branch. `searchPlug` rebuilds the source,
`searchGuards` collects the IN-FRAME guard facts (outermost first; every layer's guard
substitutes the FULL `me`, which is why the telescope must be read as one rule), and
`implChain` folds them into the implication chain the `searchChain` rule concludes.
Design + kernel-checked soundness core:
`Research/Spikes/family_completion/FamilyCompletionSpike.lean` §4 (`EvalCtx`),
specialized to search-only layers — the ite-layer generalization stays open (its probe
antecedents are cheap plays-atoms, which the exclusion architecture prices differently;
see `Research/Notes/FAMILY_COMPLETION_DESIGN.md`). -/

def searchPlug : List (Nat × Formula × Prog) → Prog → Prog
  | [], p => p
  | (g, ψ, e) :: L, p => .search g ψ (searchPlug L p) e

def searchGuards (me opponent : Prog) : List (Nat × Formula × Prog) → List Formula
  | [] => []
  | (g, ψ, _) :: L => .box g (ψ.subst me opponent) :: searchGuards me opponent L

/-- Right-fold a guard list into an implication chain. -/
def implChain (gs : List Formula) (tgt : Formula) : Formula :=
  gs.foldr .impl tgt

/-! ### The MIXED telescope (Family-A closure over `.search`+`.ite`-probe nesting —
the ite frontier, 2026-07-28)

`CtxLayer` generalizes the search telescope's layers to BOTH shapes `eval` descends
through on a POSITIVE guard fact: a `.search` test and an `.ite` probe layer, each in
THEN-polarity. Probe guards are restricted to the frame-independent
`.sim .opp (.bot z)` shape — for any other guard the in-frame run differs from the
standalone atom, making the reading UNSOUND (see `iteBranchSearch_t`'s docstring).

Polarity status:
* search-ELSE: originally excluded when conceived with a `¬□` antecedent (which no
  rule of `S` can ever prove — vacuous). COVERED since 2026-08-04 by
  `searchElseChain` with the Σ₁ REFUTATION antecedent `.neg ψ'` instead (the
  `search_f` premise shape, dischargeable via `atomNeg`) and the `search_f` floor
  charged per crossed layer — which is also what keeps every floor census true: an
  else-crossing chain costs more than the crossed guard's literal budget, so it dies
  at census budgets by cost alone.
* ite-ELSE (full simulator transparency, what would read DBot's cooperation
  outright): SOUND (the soundness lemma `ctxPlug_eval` was validated for both
  polarities), and it flips no outcome (every zoo probe antecedent is
  Gödelian-uncertifiable, floor-priced, or false — kernel-checked:
  `Research/Spikes/family_completion/ProvenanceSpike.lean`) — but it FALSIFIES the
  floor censuses beyond repair by any finite tail-set widening: with the else rule,
  `implTrans` composes a searcher's own `searchBranch` self-read with the else-probe
  chain into a PROVABLE box-headed chain to the floor target (the concrete
  counterexample: `□_k("OBot plays D vs Cupod"-guard-inst) → (OBot plays D vs
  Cupod)` via Cupod's then-read ∘ OBot's else-chain), and excluding it requires a
  recursively-closed avoid-set over the modal tier (`axKf` defeats every finite
  attempt). That census re-architecture is the honest open frontier — see
  `FAMILY_COMPLETION_DESIGN.md`. -/

inductive CtxLayer where
  | searchL (g : Nat) (ψ : Formula) (e : Prog)
  | iteL (z : Prog) (aT : Action) (other : Prog)

def ctxPlug : List CtxLayer → Prog → Prog
  | [], p => p
  | .searchL g ψ e :: L, p => .search g ψ (ctxPlug L p) e
  | .iteL z aT other :: L, p => .ite (.sim .opp (.bot z)) aT (ctxPlug L p) other

/-- The guard fact one layer contributes: a box for a search test, a probe atom for
    an ite layer. Kept as its own function so `ctxChain`'s conclusion is SYNTACTICALLY
    an `.impl` (same design lesson as `searchChain`'s explicit head). -/
def ctxGuard (me opponent : Prog) : CtxLayer → Formula
  | .searchL g ψ _ => .box g (ψ.subst me opponent)
  | .iteL z aT _ => .plays opponent (.bot z) aT

def ctxGuards (me opponent : Prog) : List CtxLayer → List Formula
  | [] => []
  | hd :: L => ctxGuard me opponent hd :: ctxGuards me opponent L

/-! ### The MIXED-POLARITY search telescope (`searchElseChain`, 2026-08-04)

`SearchLayer2` generalizes the search telescope's layers to BOTH descent polarities:
a THEN-layer records its else branch and contributes a `.box` guard antecedent
(exactly `searchPlug`'s layers); an ELSE-layer records its then branch and
contributes the Σ₁ REFUTATION `.neg` of its guard — the `search_f` premise shape
lifted to Family A. Else-guards are restricted to PLAYS-ATOM shape, stored
structurally (the same design as `CtxLayer.iteL`'s probe): for a plays-atom the
modified valuations' falsity implies interp-falsity (`WV`-falsity of a `.plays` is
honest), which is what lets the master soundness induction discharge the census
motive with NO new interface obligation. Every zoo else-crossing has a plays guard.
`layersCost` charges each else-layer its FULL failed budget plus a node (the
`search_f` floor — forced by provable-soundness, see the constructor docstring) and
each then-layer the `c_guard` cite of its fired guard proof. -/

inductive SearchLayer2 where
  | thenL (g : Nat) (ψ : Formula) (e : Prog)
  | elseL (g : Nat) (P Q : Prog) (c : Action) (p : Prog)

def plug2 : List SearchLayer2 → Prog → Prog
  | [], p => p
  | .thenL g ψ e :: L, p => .search g ψ (plug2 L p) e
  | .elseL g P Q c q :: L, p => .search g (.plays P Q c) q (plug2 L p)

def guard2 (me opponent : Prog) : SearchLayer2 → Formula
  | .thenL g ψ _ => .box g (ψ.subst me opponent)
  | .elseL _ P Q c _ => .neg (.plays (P.subst me opponent) (Q.subst me opponent) c)

def guards2 (me opponent : Prog) : List SearchLayer2 → List Formula
  | [] => []
  | hd :: L => guard2 me opponent hd :: guards2 me opponent L

def layerCost : SearchLayer2 → Nat
  | .thenL g _ _ => c_guard g
  | .elseL g _ _ _ _ => g + c_node

def layersCost : List SearchLayer2 → Nat
  | [] => 0
  | hd :: L => layerCost hd + layersCost L

mutual
-- 2. `PlaysProof me opponent body a n` — a play certificate: `body` (run with `me`/`opponent` as
-- the players) evaluates to action `a` at character cost `n`. One constructor per `eval`-step; the
-- proposition holds exactly when assembled from these constructors.
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
    /-- `.search k φ p q` runs the TRUE-guard branch (`p`) when the guard is provable, so
        `search_t` carries `Pf k (guard)` as its premise. **This is the back-edge that makes the
        block mutual**: execution consults the proof system. -/
    | search_t :
        Pf k (φ.subst me opponent) →
        PlaysProof me opponent p a n →
        PlaysProof me opponent (.search k φ p q) a (n + c_guard k + c_node)
    /-- **FALSE-guard branch — the REPAIR of the deleted-inconsistent `atom_complete_false_guard`
        axiom** (2026-07-02; `Research/Spikes/transcript/T32Inconsistency.lean`). `.search k φ p q`
        runs the ELSE branch (`q`) when the guard search fails. Both design points are FORCED:

        * The premise is a **refutation** `Pf m (.neg guard)` — Σ₁, certifiable via the guard
          subject's actual play plus `eval` determinism (`Pf.atomNeg`) — NOT mere unprovability
          (Π₁; and premising on unprovability is the non-monotone fixpoint whose paradox is the
          anti-diagonal bot). For guards that are false-but-irrefutable (the anti-diagonal's own),
          the else-play stays TRUE BUT UNCERTIFIABLE — the honest Gödelian boundary, no axiom
          papering over it.
        * The cost pays the FULL failed search budget `k` (the floor): an else-certificate must
          NEVER fit within the guard budget whose failure it certifies — otherwise `atom_monotone`
          lifts it back above `k` and re-fires the guard (the machine-checked inconsistency). The
          floor is also exactly what lets soundness be PROVEN: in the budget-strong-induction
          (`BaseTheorems.sound_upto`), a hypothetical guard proof has transcript ≤ k < this
          certificate's cost, so the induction hypothesis refutes it. Faithful: a PA-style proof
          that a bounded search fails checks every ≤`k`-length candidate — paying `k` characters
          is generous, not inflated. -/
    | search_f :
        Pf m (.neg (φ.subst me opponent)) →
        PlaysProof me opponent q a n →
        PlaysProof me opponent (.search k φ p q) a (n + m + k + c_node)

-- 3. `AtomProvable k φ` — a `PlaysProof` whose run cost fits the budget (`n ≤ k`); the bridge for
-- atomic `.plays` facts (which the reasoning rules cannot read).
  inductive AtomProvable : Nat → Formula → Prop where
    | mk : PlaysProof me opponent me a n → n ≤ k → AtomProvable k (.plays me opponent a)

/-- **`Pf k φ` — "φ has a proof transcript of ≤ k characters"**: the proof system `S`, as ONE type.

Each rule is (i) SOUND — its conclusion's `interp` follows from its premises'
(`BaseTheorems.sound_upto`) — and (ii) FAITHFUL to a PA-like `S` (critch22 Appendix B): a genuine
capability of `S`, with no semantic completeness / general reflection smuggled in.

**Cost model**: every rule's side-condition bounds the CUMULATIVE transcript — leaves pay their
conclusion's `Formula.size`; combining rules pay both subtrees PLUS their own conclusion. A bounded
budget therefore genuinely bounds the premise formulas too (the paid-cut property that makes bounded
search finite). -/
  inductive Pf : Nat → Formula → Prop where
    -- ═══ Family A. READING RULES — transparency: S reads runs and `Prog` source ═══
    -- A1. The execution bridge: S reads *runs* (the ONE entry from `PlaysProof`,
    --     plus its Σ₁ refutation twin).
    | atom : AtomProvable k φ → Pf k φ
    /-- **Refutation of a play-atom from a certificate of the actual play** (eval determinism): if
        `p` provably plays `b` (a real certificate) and `b ≠ aN`, then `¬(p plays aN)` — sound by
        `eval` fuel-monotonicity. This is the Σ₁ refutation that `search_f` consumes. -/
    | atomNeg (p q : Prog) (b aN : Action) (m : Nat) :
        AtomProvable m (.plays p q b) → b ≠ aN →
        m + (Formula.neg (.plays p q aN)).size ≤ k →
        Pf k (.neg (.plays p q aN))
    -- A2. Source transparency: S reads `Prog` source (Appendix B(a)) — one rule per
    --     syntactic shape it inspects.
    /-- S can read a `.search` body: a successful guard makes `me` play `a`. -/
    | searchBranch (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
        (hme : me = .search g ψ (.const a) (.const b)) :
        (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a))
    /-- S can read a `.sim` body: `me` plays `a` iff its closed body does. -/
    | simStep (me p q opponent : Prog) (a : Action) (hme : me = .sim p q) :
        (Formula.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                      (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                    (.plays me opponent a))
    /-- S can read a `.bot`-wrapped `.sim` body. `eval` unwraps the `.bot` (one step, keeping `me`
        as the player) and then runs the `.sim`. Unlike the (unsound) general `.bot` transparency
        `plays z → plays (.bot z)`, this is sound: the `.bot` is read as `me`'s *own body*, so
        `subst` uses the SAME `me` throughout — no rebinding of a bare sub-program's `.self`.
        Needed for the `.bot MirrorBot` mirror leg (EBot's third probe). -/
    | botSimStep (me p q opponent : Prog) (a : Action) (hme : me = .bot (.sim p q)) :
        (Formula.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                      (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                    (.plays me opponent a))
    /-- S can read a `.bot`-wrapped `.search` body — the `.bot (.search …)` twin of `searchBranch`,
        sound for the same reason as `botSimStep`. Needed when a `.search`-bot appears
        `.bot`-wrapped as a *player* whose source S must read (JustBot's guard against
        `.bot (DupocBot k)`). -/
    | botSearchStep (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
        (hme : me = .bot (.search g ψ (.const a) (.const b))) :
        (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a))
    /-- S can read a `.ite` whose **then-branch is itself a `.search`** — the PrudentBot shape.
        Fuses the `.ite` guard reading and the inner `.search` reading into one sound, in-frame
        rule, concluding the Löb-shaped `□_g ψ' → me plays c0` once the guard fires.

        Why FUSED (not a generic `.ite` branch rule): `eval`'s `.ite` runs both guard and selected
        branch in the *outer* frame, and for a `.search` branch that in-frame run consults
        `proofSearch g (ψ.subst me opponent)` — whereas the same `.search` run *as its own program*
        would consult a doubly-substituted guard. The two differ, so a generic "branch plays `a`"
        premise could not be a `.plays` atom soundly. Restrictions (met by every real bot): the
        guard is `.sim .opp (.bot z)` (frame-independent), the then-branch a `.search` on
        constants. -/
    | iteBranchSearch_t (g : Nat) (z : Prog) (a' c0 c1 : Action) (ψ : Formula)
        (q me opponent : Prog)
        (hme : me = .ite (.sim .opp (.bot z)) a'
                         (.search g ψ (.const c0) (.const c1)) q) :
        (Formula.impl (.plays opponent (.bot z) a')
                      (.impl (.box g (ψ.subst me opponent))
                             (.plays me opponent c0))).size ≤ k →
        Pf k (.impl (.plays opponent (.bot z) a')
                    (.impl (.box g (ψ.subst me opponent))
                           (.plays me opponent c0)))
    /-- **Stacked-`.search` transparency** (the canonical Critch PrudentBot shape):
        `me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q`. PrudentBot plays `c0`
        exactly when it can prove BOTH its conditions: the outer guard `ψ₁` (opponent cooperates
        with me) and the inner guard `ψ₂` (opponent defects vs DefectBot — prudence).

        PRIMITIVE, not derivable from `searchBranch` + `mp`: the then-branch is a `.search`, not a
        `.const`. Carrying the inner proof as a premise collapses the two guards to a *single*-box
        conclusion `□_{k₁} ψ₁' → me plays c0` — exactly the Löb-premise shape the bounded-Löb engine
        consumes. -/
    | searchThenSearch_t (k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula) (c0 c1 : Action)
        (q me opponent : Prog)
        (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) :
        Pf m (ψ₂.subst me opponent) → m ≤ k₂ →
        c_guard k₂ +
          (Formula.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0)).size ≤ k →
        Pf k (.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0))
    /-- **The search-telescope reading rule** (Family-A closure over `.search`-only
        then-paths, 2026-07-28): for `me = .search g₁ ψ₁ (searchPlug L (.const a)) e₁`
        — a stack of `.search` layers of ANY depth over a constant then-branch — S
        proves the full guard chain `□_{g₁} ψ₁' → … → □_{gₙ} ψₙ' → me plays a`. The
        head layer is kept in constructor form so the conclusion is always an `.impl`
        with a `.box` antecedent. Depth 1 (with `L = []`) subsumes `searchBranch`
        modulo its const-else restriction; `searchThenSearch_t`-style single-box
        collapses are derivable via `boxIntro` + `mp` on the inner guards. Premise-free
        (a pure source-reading leaf); soundness is the telescope-eval induction
        (`searchPlug_eval` in Base/Soundness, ported from the spike). -/
    | searchChain (g₁ : Nat) (ψ₁ : Formula) (e₁ : Prog)
        (L : List (Nat × Formula × Prog)) (a : Action) (me opponent : Prog)
        (hme : me = .search g₁ ψ₁ (searchPlug L (.const a)) e₁) :
        (Formula.impl (.box g₁ (ψ₁.subst me opponent))
          (implChain (searchGuards me opponent L) (.plays me opponent a))).size ≤ k →
        Pf k (.impl (.box g₁ (ψ₁.subst me opponent))
          (implChain (searchGuards me opponent L) (.plays me opponent a)))
    /-- **The MIXED-telescope reading rule** (the ite frontier, 2026-07-28): for
        `me = ctxPlug (hd :: L) (.const a)` — any nonempty stack of `.search` layers
        (then-descent) and `.ite`-probe layers (BOTH polarities, frame-independent
        probes only) over a constant — S proves the full guard chain, with `.box`
        antecedents for search layers and `.plays opponent (.bot z) r` PROBE
        antecedents for ite layers. Subsumes `searchChain` (all-`searchL` layers) and
        completes simulator transparency: S now reads probe-first bots like DBot
        outright. Premise-free source-reading leaf; soundness = the mixed-telescope
        eval induction (`ctxPlug_eval` in Base/Soundness, generalizing the spike's
        `evalCtx_sound` to both polarities). The nonempty list keeps the conclusion an
        `.impl` after one `cases` on `hd`. -/
    | ctxChain (hd : CtxLayer) (L : List CtxLayer) (a : Action) (me opponent : Prog)
        (hme : me = ctxPlug (hd :: L) (.const a)) :
        (Formula.impl (ctxGuard me opponent hd)
          (implChain (ctxGuards me opponent L) (.plays me opponent a))).size ≤ k →
        Pf k (.impl (ctxGuard me opponent hd)
          (implChain (ctxGuards me opponent L) (.plays me opponent a)))
    /-- S can verify structural identity by reflexivity: any program equals itself. -/
    | eqRefl (p : Prog) :
        (Formula.eq p p).size ≤ k → Pf k (.eq p p)
    /-- S can REFUTE structural identity of syntactically distinct programs — the Σ₁ counterpart of
        `eqRefl` (source-string comparison is decidable for S). Feeds `search_f` for failed `.eq`
        guards (CupodTrollBot's recognition guard against a non-Cupod opponent). -/
    | eqNeg (p q : Prog) (hne : p ≠ q) :
        (Formula.neg (.eq p q)).size ≤ k → Pf k (.neg (.eq p q))

    -- ═══ Family B. LOGICAL GLUE — the propositional core ═══
    /-- **Modus ponens**: from `φ → α` and `φ`, infer `α`. ONE rule (the former split had
        `Derivation.modusPonens` for structural premises and `Provable.app` for reflective ones).
        Transcript: both subtrees plus the conclusion. -/
    | mp (m₁ m₂ : Nat) (φ α : Formula) :
        Pf m₁ (.impl φ α) → Pf m₂ φ → m₁ + m₂ + α.size ≤ k → Pf k α
    /-- **Hypothetical syllogism / transitivity of implication**: chain `φ → ψ` and `ψ → χ`.
        PRIMITIVE — not derivable from `mp`, because `S` has no implication-introduction to
        discharge a hypothesis (see the header). ONE rule (formerly `Derivation.hypSyll` +
        `Provable.implTrans`). -/
    | implTrans (φ ψ χ : Formula) (a b : Nat) :
        Pf a (.impl φ ψ) → Pf b (.impl ψ χ) →
        a + b + (Formula.impl φ χ).size ≤ k → Pf k (.impl φ χ)
    /-- **True-consequent implication** (`ψ ⊢ φ → ψ`): if the consequent is provable, so is the
        implication. Sound (`interp (.impl φ ψ)` follows from `ψ.interp` by `fun _ => ·`) and
        faithful (a PA-like `S` can always weaken a proved formula into an implication). This is
        what makes proof-oracle bots whose guard is an *implication* (CIMCIC, DIMCID) provable. -/
    | weakenImpl (φ ψ : Formula) (m : Nat) :
        Pf m ψ → m + (Formula.impl φ ψ).size ≤ k → Pf k (.impl φ ψ)
    /-- **Closed composition** (the S-combinator as a rule; both premises are closed `⊢`, so the
        rule form suffices — replacing the deduction theorem the side layer would need): from
        `⊢ φ → (ψ → χ)` and `⊢ φ → ψ`, infer `⊢ φ → χ`. -/
    | impS2 (φ ψ χ : Formula) (m₁ m₂ K : Nat) :
        Pf m₁ (.impl φ (.impl ψ χ)) → Pf m₂ (.impl φ ψ) →
        m₁ + m₂ + (Formula.impl φ χ).size ≤ K → Pf K (.impl φ χ)
    /-- **Identity implication** (`⊢ φ → φ`) — Family-B completion leaf (2026-07-28).
        Sound (its interp IS the identity) and faithful (a Hilbert axiom of any PA-like
        `S`). Previously UNDERIVABLE: with no deduction theorem and no premise-free
        implication leaf, `S` could not prove even this tautology (kernel-checked
        corollary of the CIMCIC census — `Research/Spikes/family_completion/
        FamilyCompletionSpike.lean` §3), so a bot guarding on `.impl A A` fell through.
        The exclusion censuses survive premise-free implication leaves via the Guarded
        `TailTo` invariant (Base/Exclusion): on `⊢ T → T` the invariant's two conjuncts
        annihilate. -/
    | implRefl (φ : Formula) :
        (Formula.impl φ φ).size ≤ k → Pf k (.impl φ φ)
    /-- **K as an object formula** (`⊢ φ → (ψ → φ)`) — Family-B completion leaf
        (2026-07-28). Sound (`fun h _ => h`), faithful (a Hilbert axiom). With `mp` it
        DERIVES `weakenImpl` (kept primitive for transcript tightness); with `implRefl`
        it completes the positive-implication fragment short of the deduction theorem
        (deliberately absent — see the header). Census-safe like `implRefl`. -/
    | implK (φ ψ : Formula) :
        (Formula.impl φ (.impl ψ φ)).size ≤ k → Pf k (.impl φ (.impl ψ φ))
    /-- **S as an object formula** (`⊢ (φ→(ψ→χ)) → ((φ→ψ) → (φ→χ))`) — Family-B
        completeness axiom (2026-07-28). Sound (the S combinator `fun f g x => f x (g x)`),
        faithful (a Hilbert axiom). With `implK` and `mp` this is the full basis of the
        POSITIVE implicational fragment: the deduction theorem becomes ADMISSIBLE
        (`Base/Closure.deduction_theorem`) and identity derivable (`SKK = I`,
        `identity_from_KS`). Census-safe by SELF-ANNIHILATION: its antecedent carries
        the consequent's own structure, so the Guarded invariant's two conjuncts
        contradict (like `implRefl`/`implK`). -/
    | implS (φ ψ χ : Formula) :
        (Formula.impl (.impl φ (.impl ψ χ))
          (.impl (.impl φ ψ) (.impl φ χ))).size ≤ k →
        Pf k (.impl (.impl φ (.impl ψ χ)) (.impl (.impl φ ψ) (.impl φ χ)))
    /-- **Contraposition** (`⊢ φ → ψ  ⟹  ⊢ ¬ψ → ¬φ`) — Family-B completion rule
        (2026-07-28), the first `.neg`-CONSUMER in the logical core. Sound classically
        (`fun hn hp => hn (ih hp)`), faithful (PA proves it). Costs mirror
        `weakenImpl`: premise + conclusion size. Census-safe outright: its conclusion's
        spine tail is a `.neg`, which no plays-atom census matches. -/
    | contrapose (φ ψ : Formula) (m : Nat) :
        Pf m (.impl φ ψ) →
        m + (Formula.impl (.neg ψ) (.neg φ)).size ≤ k →
        Pf k (.impl (.neg ψ) (.neg φ))
    /-- **Ex falso / negation elimination** (`⊢ ¬φ, ⊢ φ  ⟹  ⊢ ψ`) — Family-B
        completion rule (2026-07-28). Sound (`absurd`), faithful (PA proves ex falso).
        **VACUOUS in the consistent `S`**: by soundness its premises can never coexist,
        so the rule never actually fires — every census/metatheory case discharges by
        the soundness contradiction, it needs NO decider leg for completeness, and NO
        mirror in the gated strata (`PfG`) or the tree substrate (`ProvT`). It is here
        for the Hilbert-basis completeness of Family B, not for new theorems. -/
    | negElim (φ ψ : Formula) (m₁ m₂ : Nat) :
        Pf m₁ (.neg φ) → Pf m₂ φ →
        m₁ + m₂ + ψ.size ≤ k →
        Pf k ψ

    -- ═══ Family C. LÖB MACHINERY — modal / HBL tier (bounded derivability conditions) ═══
    /-- **Box-introduction / bounded necessitation** (HBL D2): if `φ` is provable within `kIn`,
        that *fact* — `□_{kIn} φ` — is itself provable. Sound with NO axiom: `(□_{kIn} φ).interp`
        is *definitionally* `Pf kIn φ` (Dynamics.lean), which is exactly the premise. -/
    | boxIntro (kIn K : Nat) (φ : Formula) :
        Pf kIn φ →
        kIn + (Formula.box kIn φ).size ≤ K →
        Pf K (.box kIn φ)
    /-- **Object-level bounded Σ₁-completeness for play-atoms** (constructive,
        certificate-carrying): from a bounded play certificate, infer the *object implication*
        `(p plays a vs q) → □_kBox (p plays a vs q)`. Carrying the CERTIFICATE as a premise is what
        keeps this on the sound Σ₁ side — it only fires when a size-≤-`kBox` transcript actually
        exists (genuine bounded Σ₁-completeness, NOT the GL-excluded converse-necessitation). -/
    | atomBoxImpl (kBox : Nat) (p q : Prog) (a : Action) :
        AtomProvable kBox (.plays p q a) →
        kBox + (Formula.impl (.plays p q a) (.box kBox (.plays p q a))).size ≤ k →
        Pf k (.impl (.plays p q a) (.box kBox (.plays p q a)))
    /-- **GL axiom-K, RULE form**: from a proof of `□_a (φ → α)`, infer `□_b φ → □_c α`.
        POSITIVE (the premise is a held proof, not a transformer) and sound via `mp`. -/
    | axK (a b c m K : Nat) (φ α : Formula) :
        Pf m (.box a (.impl φ α)) →
        a + b + α.size ≤ c →
        m + (Formula.impl (.box b φ) (.box c α)).size ≤ K →
        Pf K (.impl (.box b φ) (.box c α))
    /-- **GL axiom-K as an object FORMULA** `□_a(φ→α) → (□_b φ → □_c α)` — the `axK` RULE form
        cannot supply Löb's middle step, which needs the implication itself as a premise-free
        theorem. Sound via `mp`. -/
    | axKf (a b c K : Nat) (φ α : Formula) :
        a + b + α.size ≤ c →
        (Formula.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α))).size ≤ K →
        Pf K (.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α)))
    /-- **GL axiom-4 / object necessitation** (`□_a φ → □_b (□_a φ)`): the object form of HBL D2.
        Its `interp` is `Pf a φ → Pf a φ` (since `interp (□_a φ) = Pf a φ`) — the IDENTITY. -/
    | box4 (a b K : Nat) (φ : Formula) :
        a + (Formula.box a φ).size ≤ b →
        (Formula.impl (.box a φ) (.box b (.box a φ))).size ≤ K →
        Pf K (.impl (.box a φ) (.box b (.box a φ)))
    /-- **Upward box-subscript monotonicity as an object formula** (`□_a φ → □_b φ` for `a ≤ b`):
        a ≤a-cost proof IS a ≤b-cost proof. Needed under the transcript model, where the Löb chain's
        K-distribution outputs land at computed subscripts that must be weakened UP onto the
        consumers' source-literal boxes. -/
    | boxMono (a b K : Nat) (φ : Formula) :
        a ≤ b →
        (Formula.impl (.box a φ) (.box b φ)).size ≤ K →
        Pf K (.impl (.box a φ) (.box b φ))
    /-- **Löb-fixpoint leg, forward**: `ψ → (□_g ψ → tgt)` for the fixpoint sentence
        `ψ := .diag g tgt`. Sound with NO axiom: `ψ.interp` IS `Pf g ψ → tgt.interp`
        (Dynamics.lean) — the soundness arm is the identity. GATED on the tight Löb premise
        `Pf pm (□_fb tgt → tgt)`: the Löb chain always has it, and the gate preserves the
        structural exclusion invariants. -/
    | diagF (pm fb g K : Nat) (tgt : Formula) :
        Pf pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)).size ≤ K →
        Pf K (.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt))
    /-- **Löb-fixpoint leg, backward**: `(□_g ψ → tgt) → ψ`. Sound = identity (as `diagF`). -/
    | diagB (pm fb g K : Nat) (tgt : Formula) :
        Pf pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)).size ≤ K →
        Pf K (.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt))
    /-- **The MIXED-POLARITY search-telescope reading rule** (`searchElseChain`,
        integrated 2026-08-04 from the Tier-2 proposal bundle
        `app/generated/constructor_proposals/searchElseChain/`): for
        `me = plug2 (hd :: L) (.const a)` — `.search` layers descending the THEN slot
        (`.box` guard antecedent, as `searchChain`) or the ELSE slot (`.neg` guard
        antecedent — the Σ₁ REFUTATION of the crossed guard, the premise shape
        `search_f` consumes) — S proves the full guard chain. Faithful: S replays
        each FAILED bounded search, paying its full budget (`layersCost`, the
        `search_f` floor), and cites each fired guard (`c_guard`); the antecedent is
        a refutation, never an unprovability claim — no internal soundness-reflection
        is smuggled in. The floor is FORCED by provable-soundness (the master
        induction's arm refutes a hypothetical crossed-guard proof via the outer IH,
        which needs the guard budget strictly below this transcript — `search_f`'s
        argument verbatim) and is what keeps every floor census true: an
        else-crossing chain at a searcher's literal budget `g` costs `> g`, dying at
        census budgets by cost alone. Premise-free source-reading leaf; soundness =
        the mixed-polarity eval induction (`plug2_eval`, Base/ValuationSoundness). -/
    | searchElseChain (hd : SearchLayer2) (L : List SearchLayer2) (a : Action)
        (me opponent : Prog)
        (hme : me = plug2 (hd :: L) (.const a)) :
        layersCost (hd :: L) +
          (Formula.impl (guard2 me opponent hd)
            (implChain (guards2 me opponent L) (.plays me opponent a))).size ≤ k →
        Pf k (.impl (guard2 me opponent hd)
          (implChain (guards2 me opponent L) (.plays me opponent a)))
end

/-! ## 4. The NAMED eliminators — use these, never the raw recursors

`Pf` is mutual, so `induction h with` is unavailable (Lean does not do mutual structural
induction). These `@[elab_as_elim]` theorems repackage the raw 37-minor-premise recursor behind
NAMED hypotheses, restoring

    induction h using Pf.induct with | atom … | mp … | …

Each is ONE recursor application with the two irrelevant motives discharged to `True`. The motive
TAKES the proof term (`∀ k φ, Pf k φ → Prop`); a proof-irrelevant motive breaks `induction using`.
Derived and validated in `Research/Spikes/unified_pf/PfMutualInductSpike.lean`.

**Rule of thumb**: if you find yourself writing `Pf.rec` or `PlaysProof.rec` anywhere outside this
section, you want one of these instead. -/

/-- Named eliminator for `Pf` — the workhorse for exclusion proofs and soundness. -/
@[elab_as_elim]
theorem Pf.induct (motive : (k : Nat) → (φ : Formula) → Pf k φ → Prop)
    (atom : ∀ (k : Nat) (φ : Formula) (h : AtomProvable k φ), motive k φ (.atom h))
    (atomNeg : ∀ (k : Nat) (p q : Prog) (b aN : Action) (m : Nat)
        (hatom : AtomProvable m (.plays p q b)) (hne : b ≠ aN)
        (hle : m + (Formula.neg (.plays p q aN)).size ≤ k),
        motive k _ (.atomNeg p q b aN m hatom hne hle))
    (searchBranch : ∀ (k g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
        (hme : me = .search g ψ (.const a) (.const b))
        (hle : (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k),
        motive k _ (.searchBranch g ψ a b me opponent hme hle))
    (simStep : ∀ (k : Nat) (me p q opponent : Prog) (a : Action)
        (hme : me = .sim p q)
        (hle : (Formula.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                             (.plays me opponent a)).size ≤ k),
        motive k _ (.simStep me p q opponent a hme hle))
    (botSimStep : ∀ (k : Nat) (me p q opponent : Prog) (a : Action)
        (hme : me = .bot (.sim p q))
        (hle : (Formula.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                             (.plays me opponent a)).size ≤ k),
        motive k _ (.botSimStep me p q opponent a hme hle))
    (botSearchStep : ∀ (k g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
        (hme : me = .bot (.search g ψ (.const a) (.const b)))
        (hle : (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k),
        motive k _ (.botSearchStep g ψ a b me opponent hme hle))
    (iteBranchSearch_t : ∀ (k g : Nat) (z : Prog) (a' c0 c1 : Action) (ψ : Formula)
        (q me opponent : Prog)
        (hme : me = .ite (.sim .opp (.bot z)) a' (.search g ψ (.const c0) (.const c1)) q)
        (hle : (Formula.impl (.plays opponent (.bot z) a')
                             (.impl (.box g (ψ.subst me opponent))
                                    (.plays me opponent c0))).size ≤ k),
        motive k _ (.iteBranchSearch_t g z a' c0 c1 ψ q me opponent hme hle))
    (searchThenSearch_t : ∀ (k k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula) (c0 c1 : Action)
        (q me opponent : Prog)
        (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q)
        (hprud : Pf m (ψ₂.subst me opponent)) (hmk : m ≤ k₂)
        (hle : c_guard k₂ +
          (Formula.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0)).size ≤ k),
        motive m (ψ₂.subst me opponent) hprud →
        motive k _ (.searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle))
    (searchChain : ∀ (k g₁ : Nat) (ψ₁ : Formula) (e₁ : Prog)
        (L : List (Nat × Formula × Prog)) (a : Action) (me opponent : Prog)
        (hme : me = .search g₁ ψ₁ (searchPlug L (.const a)) e₁)
        (hle : (Formula.impl (.box g₁ (ψ₁.subst me opponent))
          (implChain (searchGuards me opponent L) (.plays me opponent a))).size ≤ k),
        motive k _ (.searchChain g₁ ψ₁ e₁ L a me opponent hme hle))
    (ctxChain : ∀ (k : Nat) (hd : CtxLayer) (L : List CtxLayer) (a : Action)
        (me opponent : Prog)
        (hme : me = ctxPlug (hd :: L) (.const a))
        (hle : (Formula.impl (ctxGuard me opponent hd)
          (implChain (ctxGuards me opponent L) (.plays me opponent a))).size ≤ k),
        motive k _ (.ctxChain hd L a me opponent hme hle))
    (searchElseChain : ∀ (k : Nat) (hd : SearchLayer2) (L : List SearchLayer2)
        (a : Action) (me opponent : Prog)
        (hme : me = plug2 (hd :: L) (.const a))
        (hle : layersCost (hd :: L) +
          (Formula.impl (guard2 me opponent hd)
            (implChain (guards2 me opponent L) (.plays me opponent a))).size ≤ k),
        motive k _ (.searchElseChain hd L a me opponent hme hle))
    (eqRefl : ∀ (k : Nat) (p : Prog) (hle : (Formula.eq p p).size ≤ k),
        motive k _ (.eqRefl p hle))
    (eqNeg : ∀ (k : Nat) (p q : Prog) (hne : p ≠ q)
        (hle : (Formula.neg (.eq p q)).size ≤ k),
        motive k _ (.eqNeg p q hne hle))
    (mp : ∀ (k m₁ m₂ : Nat) (φ α : Formula)
        (h1 : Pf m₁ (.impl φ α)) (h2 : Pf m₂ φ) (hle : m₁ + m₂ + α.size ≤ k),
        motive m₁ (.impl φ α) h1 → motive m₂ φ h2 →
        motive k α (.mp m₁ m₂ φ α h1 h2 hle))
    (implTrans : ∀ (k : Nat) (φ ψ χ : Formula) (a b : Nat)
        (h1 : Pf a (.impl φ ψ)) (h2 : Pf b (.impl ψ χ))
        (hle : a + b + (Formula.impl φ χ).size ≤ k),
        motive a (.impl φ ψ) h1 → motive b (.impl ψ χ) h2 →
        motive k _ (.implTrans φ ψ χ a b h1 h2 hle))
    (weakenImpl : ∀ (k : Nat) (φ ψ : Formula) (m : Nat)
        (hψ : Pf m ψ) (hle : m + (Formula.impl φ ψ).size ≤ k),
        motive m ψ hψ → motive k _ (.weakenImpl φ ψ m hψ hle))
    (impS2 : ∀ (φ ψ χ : Formula) (m₁ m₂ K : Nat)
        (h1 : Pf m₁ (.impl φ (.impl ψ χ))) (h2 : Pf m₂ (.impl φ ψ))
        (hle : m₁ + m₂ + (Formula.impl φ χ).size ≤ K),
        motive m₁ (.impl φ (.impl ψ χ)) h1 → motive m₂ (.impl φ ψ) h2 →
        motive K _ (.impS2 φ ψ χ m₁ m₂ K h1 h2 hle))
    (implRefl : ∀ (k : Nat) (φ : Formula)
        (hle : (Formula.impl φ φ).size ≤ k),
        motive k _ (.implRefl φ hle))
    (implK : ∀ (k : Nat) (φ ψ : Formula)
        (hle : (Formula.impl φ (.impl ψ φ)).size ≤ k),
        motive k _ (.implK φ ψ hle))
    (implS : ∀ (k : Nat) (φ ψ χ : Formula)
        (hle : (Formula.impl (.impl φ (.impl ψ χ))
          (.impl (.impl φ ψ) (.impl φ χ))).size ≤ k),
        motive k _ (.implS φ ψ χ hle))
    (contrapose : ∀ (k : Nat) (φ ψ : Formula) (m : Nat)
        (h : Pf m (.impl φ ψ))
        (hle : m + (Formula.impl (.neg ψ) (.neg φ)).size ≤ k),
        motive m (.impl φ ψ) h →
        motive k _ (.contrapose φ ψ m h hle))
    (negElim : ∀ (k : Nat) (φ ψ : Formula) (m₁ m₂ : Nat)
        (h1 : Pf m₁ (.neg φ)) (h2 : Pf m₂ φ)
        (hle : m₁ + m₂ + ψ.size ≤ k),
        motive m₁ (.neg φ) h1 → motive m₂ φ h2 →
        motive k ψ (.negElim φ ψ m₁ m₂ h1 h2 hle))
    (boxIntro : ∀ (kIn K : Nat) (φ : Formula)
        (hprem : Pf kIn φ) (hle : kIn + (Formula.box kIn φ).size ≤ K),
        motive kIn φ hprem → motive K _ (.boxIntro kIn K φ hprem hle))
    (atomBoxImpl : ∀ (k kBox : Nat) (p q : Prog) (a : Action)
        (hatom : AtomProvable kBox (.plays p q a))
        (hle : kBox + (Formula.impl (.plays p q a) (.box kBox (.plays p q a))).size ≤ k),
        motive k _ (.atomBoxImpl kBox p q a hatom hle))
    (axK : ∀ (a b c m K : Nat) (φ α : Formula)
        (hprem : Pf m (.box a (.impl φ α))) (hgate : a + b + α.size ≤ c)
        (hle : m + (Formula.impl (.box b φ) (.box c α)).size ≤ K),
        motive m (.box a (.impl φ α)) hprem →
        motive K _ (.axK a b c m K φ α hprem hgate hle))
    (axKf : ∀ (a b c K : Nat) (φ α : Formula)
        (hgate : a + b + α.size ≤ c)
        (hsz : (Formula.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α))).size ≤ K),
        motive K _ (.axKf a b c K φ α hgate hsz))
    (box4 : ∀ (a b K : Nat) (φ : Formula)
        (hgate : a + (Formula.box a φ).size ≤ b)
        (hsz : (Formula.impl (.box a φ) (.box b (.box a φ))).size ≤ K),
        motive K _ (.box4 a b K φ hgate hsz))
    (boxMono : ∀ (a b K : Nat) (φ : Formula)
        (hab : a ≤ b) (hsz : (Formula.impl (.box a φ) (.box b φ)).size ≤ K),
        motive K _ (.boxMono a b K φ hab hsz))
    (diagF : ∀ (pm fb g K : Nat) (tgt : Formula)
        (hgate : Pf pm (.impl (.box fb tgt) tgt))
        (hle : pm + (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)).size ≤ K),
        motive pm (.impl (.box fb tgt) tgt) hgate →
        motive K _ (.diagF pm fb g K tgt hgate hle))
    (diagB : ∀ (pm fb g K : Nat) (tgt : Formula)
        (hgate : Pf pm (.impl (.box fb tgt) tgt))
        (hle : pm + (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)).size ≤ K),
        motive pm (.impl (.box fb tgt) tgt) hgate →
        motive K _ (.diagB pm fb g K tgt hgate hle))
    {k : Nat} {φ : Formula} (h : Pf k φ) : motive k φ h :=
  Pf.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := motive)
    -- PlaysProof arms (9) + AtomProvable.mk (1): motive is `True`.
    trivial (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial)
    -- Pf arms (27, family order A/B/C): route each to its named hypothesis.
    (fun {k} {φ} hatom _ => atom k φ hatom)
    (fun {k} p q b aN m hatom hne hle _ => atomNeg k p q b aN m hatom hne hle)
    (fun {k} g ψ a b me opponent hme hle => searchBranch k g ψ a b me opponent hme hle)
    (fun {k} me p q opponent a hme hle => simStep k me p q opponent a hme hle)
    (fun {k} me p q opponent a hme hle => botSimStep k me p q opponent a hme hle)
    (fun {k} g ψ a b me opponent hme hle => botSearchStep k g ψ a b me opponent hme hle)
    (fun {k} g z a' c0 c1 ψ q me opponent hme hle =>
      iteBranchSearch_t k g z a' c0 c1 ψ q me opponent hme hle)
    (fun {k} k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle ih =>
      searchThenSearch_t k k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle ih)
    (fun {k} g₁ ψ₁ e₁ L a me opponent hme hle =>
      searchChain k g₁ ψ₁ e₁ L a me opponent hme hle)
    (fun {k} hd L a me opponent hme hle =>
      ctxChain k hd L a me opponent hme hle)
    (fun {k} p hle => eqRefl k p hle)
    (fun {k} p q hne hle => eqNeg k p q hne hle)
    (fun {k} m₁ m₂ φ α h1 h2 hle ih1 ih2 => mp k m₁ m₂ φ α h1 h2 hle ih1 ih2)
    (fun {k} φ ψ χ a b h1 h2 hle ih1 ih2 => implTrans k φ ψ χ a b h1 h2 hle ih1 ih2)
    (fun {k} φ ψ m hψ hle ih => weakenImpl k φ ψ m hψ hle ih)
    (fun φ ψ χ m₁ m₂ K h1 h2 hle ih1 ih2 => impS2 φ ψ χ m₁ m₂ K h1 h2 hle ih1 ih2)
    (fun {k} φ hle => implRefl k φ hle)
    (fun {k} φ ψ hle => implK k φ ψ hle)
    (fun {k} φ ψ χ hle => implS k φ ψ χ hle)
    (fun {k} φ ψ m h hle ih => contrapose k φ ψ m h hle ih)
    (fun {k} φ ψ m₁ m₂ h1 h2 hle ih1 ih2 => negElim k φ ψ m₁ m₂ h1 h2 hle ih1 ih2)
    (fun kIn K φ hprem hle ih => boxIntro kIn K φ hprem hle ih)
    (fun {k} kBox p q a hatom hle _ => atomBoxImpl k kBox p q a hatom hle)
    (fun a b c m K φ α hprem hgate hle ih => axK a b c m K φ α hprem hgate hle ih)
    (fun a b c K φ α hgate hsz => axKf a b c K φ α hgate hsz)
    (fun a b K φ hgate hsz => box4 a b K φ hgate hsz)
    (fun a b K φ hab hsz => boxMono a b K φ hab hsz)
    (fun pm fb g K tgt hgate hle ih => diagF pm fb g K tgt hgate hle ih)
    (fun pm fb g K tgt hgate hle ih => diagB pm fb g K tgt hgate hle ih)
    (fun {k} hd L a me opponent hme hle =>
      searchElseChain k hd L a me opponent hme hle)
    h

/-- Named eliminator for `PlaysProof` — the workhorse for the execution census
    (`Base/Exclusion`). Motive takes the certificate; the `Pf` premises of `search_t`/`search_f`
    are handed over as DATA (no induction hypothesis on them — that would need the `Pf` motive;
    use `Pf.induct` for that side, or the raw recursor if you genuinely need both at once). -/
@[elab_as_elim]
theorem PlaysProof.induct
    (motive : (me opponent body : Prog) → (a : Action) → (n : Nat) →
      PlaysProof me opponent body a n → Prop)
    (const : ∀ (me opponent : Prog) (a : Action),
        motive me opponent (.const a) a c_leaf .const)
    (self : ∀ (me opponent : Prog) (a : Action) (n : Nat) (h : PlaysProof me opponent me a n),
        motive me opponent me a n h →
        motive me opponent .self a (n + c_node) (.self h))
    (opp : ∀ (me opponent : Prog) (a : Action) (n : Nat)
        (h : PlaysProof me opponent opponent a n),
        motive me opponent opponent a n h →
        motive me opponent .opp a (n + c_node) (.opp h))
    (bot : ∀ (me opponent p : Prog) (a : Action) (n : Nat) (h : PlaysProof me opponent p a n),
        motive me opponent p a n h →
        motive me opponent (.bot p) a (n + c_node) (.bot h))
    (sim : ∀ (a : Action) (n : Nat) (me opponent p q : Prog)
        (h : PlaysProof (p.subst me opponent) (q.subst me opponent) (p.subst me opponent) a n),
        motive (p.subst me opponent) (q.subst me opponent) (p.subst me opponent) a n h →
        motive me opponent (.sim p q) a (n + c_node) (.sim h))
    (ite_t : ∀ (me opponent b : Prog) (r : Action) (m : Nat) (a' : Action) (p : Prog)
        (a : Action) (n : Nat) (q : Prog)
        (hb : PlaysProof me opponent b r m) (hr : (r == a') = true)
        (hp : PlaysProof me opponent p a n),
        motive me opponent b r m hb → motive me opponent p a n hp →
        motive me opponent (.ite b a' p q) a (m + n + c_node) (.ite_t hb hr hp))
    (ite_f : ∀ (me opponent b : Prog) (r : Action) (m : Nat) (a' : Action) (q : Prog)
        (a : Action) (n : Nat) (p : Prog)
        (hb : PlaysProof me opponent b r m) (hr : (r == a') = false)
        (hq : PlaysProof me opponent q a n),
        motive me opponent b r m hb → motive me opponent q a n hq →
        motive me opponent (.ite b a' p q) a (m + n + c_node) (.ite_f hb hr hq))
    (search_t : ∀ (k : Nat) (me opponent p : Prog) (a : Action) (n : Nat) (φ : Formula) (q : Prog)
        (hg : Pf k (φ.subst me opponent)) (hp : PlaysProof me opponent p a n),
        motive me opponent p a n hp →
        motive me opponent (.search k φ p q) a (n + c_guard k + c_node) (.search_t hg hp))
    (search_f : ∀ (m : Nat) (me opponent q : Prog) (a : Action) (n k : Nat) (φ : Formula)
        (p : Prog)
        (hg : Pf m (.neg (φ.subst me opponent))) (hq : PlaysProof me opponent q a n),
        motive me opponent q a n hq →
        motive me opponent (.search k φ p q) a (n + m + k + c_node) (.search_f hg hq))
    {me opponent body : Prog} {a : Action} {n : Nat} (h : PlaysProof me opponent body a n) :
    motive me opponent body a n h := by
  -- The 27 `Pf` arms + `AtomProvable.mk` are irrelevant here (their motives are `True`); let
  -- Lean generate them rather than hand-counting arities.
  refine PlaysProof.rec
    (motive_1 := motive)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True)
    (fun {me opponent} {a} => const me opponent a)
    (fun {me opponent} {a} {n} h ih => self me opponent a n h ih)
    (fun {me opponent} {a} {n} h ih => opp me opponent a n h ih)
    (fun {me opponent p} {a} {n} h ih => bot me opponent p a n h ih)
    (fun {a} {n} {me opponent p q} h ih => sim a n me opponent p q h ih)
    (fun {me opponent b} {r} {m} {a'} {p} {a} {n} {q} hb hr hp ihb ihp =>
      ite_t me opponent b r m a' p a n q hb hr hp ihb ihp)
    (fun {me opponent b} {r} {m} {a'} {q} {a} {n} {p} hb hr hq ihb ihq =>
      ite_f me opponent b r m a' q a n p hb hr hq ihb ihq)
    (fun {k} {me opponent p} {a} {n} {φ} {q} hg hp _ ihp =>
      search_t k me opponent p a n φ q hg hp ihp)
    (fun {m} {me opponent q} {a} {n k} {φ} {p} hg hq _ ihq =>
      search_f m me opponent q a n k φ p hg hq ihq)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_
    h <;>
  · intros; trivial

/-! ## 5. Budget monotonicity -/

/-- A ≤k₁-transcript proof is a ≤k₂-transcript proof (`k₁ ≤ k₂`). Structural under the transcript
    cost model: EVERY rule's final side-condition is `… ≤ k` with `k` the output budget, so each
    constructor re-applies with the bound relaxed — plain `cases`, no recursion. -/
theorem atom_monotone (k₁ k₂ : Nat) (φ : Formula) (hk : k₁ ≤ k₂) :
    AtomProvable k₁ φ → AtomProvable k₂ φ := by
  rintro ⟨cert, hle⟩; exact .mk cert (Nat.le_trans hle hk)

theorem Pf_mono : ∀ {k₁ : Nat} {φ : Formula}, Pf k₁ φ →
    ∀ {k₂ : Nat}, k₁ ≤ k₂ → Pf k₂ φ := by
  intro k₁ φ h k₂ hk
  cases h with
  | atom hatom => exact .atom (atom_monotone k₁ k₂ φ hk hatom)
  | searchBranch g ψ a b me opponent hme hle =>
      exact .searchBranch g ψ a b me opponent hme (Nat.le_trans hle hk)
  | simStep me p q opponent a hme hle =>
      exact .simStep me p q opponent a hme (Nat.le_trans hle hk)
  | botSimStep me p q opponent a hme hle =>
      exact .botSimStep me p q opponent a hme (Nat.le_trans hle hk)
  | botSearchStep g ψ a b me opponent hme hle =>
      exact .botSearchStep g ψ a b me opponent hme (Nat.le_trans hle hk)
  | iteBranchSearch_t g z a' c0 c1 ψ q me opponent hme hle =>
      exact .iteBranchSearch_t g z a' c0 c1 ψ q me opponent hme (Nat.le_trans hle hk)
  | eqRefl p hle => exact .eqRefl p (Nat.le_trans hle hk)
  | eqNeg p q hne hle => exact .eqNeg p q hne (Nat.le_trans hle hk)
  -- (`cases` unifies the constructor's `α` with the goal index `φ` and REORDERS the remaining
  -- fields, so bind them by display position via `rename_i`.)
  | mp =>
      rename_i m₁ m₂ φ' h2 h1 hle
      exact .mp m₁ m₂ φ' φ h1 h2 (Nat.le_trans hle hk)
  | implTrans φ' ψ χ a b h1 h2 hle =>
      exact .implTrans φ' ψ χ a b h1 h2 (Nat.le_trans hle hk)
  | weakenImpl φ' ψ m hψ hle => exact .weakenImpl φ' ψ m hψ (Nat.le_trans hle hk)
  | searchThenSearch_t k₁' k₂' m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle =>
      exact .searchThenSearch_t k₁' k₂' m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk
        (Nat.le_trans hle hk)
  | searchChain g₁ ψ₁ e₁ L a me opponent hme hle =>
      exact .searchChain g₁ ψ₁ e₁ L a me opponent hme (Nat.le_trans hle hk)
  | ctxChain hd L a me opponent hme hle =>
      exact .ctxChain hd L a me opponent hme (Nat.le_trans hle hk)
  | searchElseChain hd L a me opponent hme hle =>
      exact .searchElseChain hd L a me opponent hme (Nat.le_trans hle hk)
  | atomBoxImpl kBox p q a hatom hle =>
      exact .atomBoxImpl kBox p q a hatom (Nat.le_trans hle hk)
  | boxIntro kIn K φ' hprem hle => exact .boxIntro kIn k₂ φ' hprem (Nat.le_trans hle hk)
  | axK a b c m K φ' α hprem hgate hle =>
      exact .axK a b c m k₂ φ' α hprem hgate (Nat.le_trans hle hk)
  | box4 a b K φ' hgate hle => exact .box4 a b k₂ φ' hgate (Nat.le_trans hle hk)
  | diagF pm fb g K tgt hgate hle => exact .diagF pm fb g k₂ tgt hgate (Nat.le_trans hle hk)
  | diagB pm fb g K tgt hgate hle => exact .diagB pm fb g k₂ tgt hgate (Nat.le_trans hle hk)
  | axKf a b c K φ' α hgate hle => exact .axKf a b c k₂ φ' α hgate (Nat.le_trans hle hk)
  | impS2 φ' ψ χ m₁ m₂ K h1 h2 hle =>
      exact .impS2 φ' ψ χ m₁ m₂ k₂ h1 h2 (Nat.le_trans hle hk)
  | implRefl φ' hle => exact .implRefl φ' (Nat.le_trans hle hk)
  | implK φ' ψ hle => exact .implK φ' ψ (Nat.le_trans hle hk)
  | implS φ' ψ χ hle => exact .implS φ' ψ χ (Nat.le_trans hle hk)
  | contrapose φ' ψ m h hle => exact .contrapose φ' ψ m h (Nat.le_trans hle hk)
  -- (negElim's conclusion ψ unifies with the goal index φ and `cases` reorders the
  -- remaining fields — bind by display position via `rename_i`, as in `mp`.)
  | negElim =>
      rename_i φ' m₁ m₂ h1 h2 hle
      exact .negElim φ' φ m₁ m₂ h1 h2 (Nat.le_trans hle hk)
  | boxMono a b K φ' hab hle => exact .boxMono a b k₂ φ' hab (Nat.le_trans hle hk)
  | atomNeg p q b aN m hatom hne hle =>
      exact .atomNeg p q b aN m hatom hne (Nat.le_trans hle hk)

-- 6. The proof-search oracle: bounded provability reflected into `Bool` for the
-- evaluator's guard. Classical (hence noncomputable), correct for an oracle.
noncomputable def proofSearch (k : Nat) (φ : Formula) : Bool := decide (Pf k φ)


/-- 7. Character budget for a `fuel`-step play's atom certificate. Honest `O(fuel)`
    (Critch's `e*`, Appendix B(d)): `c_node + c_guard fuel` per step, plus a leaf.
    `c_guard fuel` over-approximates every guard budget reachable in the run. -/
def atom_cost (fuel : Nat) : Nat := c_leaf + (c_node + c_guard fuel) * fuel


end PD
