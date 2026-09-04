import PrisonersDilemma.Program

namespace PD
open Classical


/-!
# The proof system `S` — the unified proof-term type `Pf`

The agents' internal logic. One mutual `inductive` block defines execution
certificates and `S`-derivations together:

```
        ┌──────────────────────────────────────────────────────────┐
        │  Pf k φ   ("φ has a proof transcript of ≤ k characters") │  ← the oracle `.search` asks
        │  = source transparency (S reads `Prog`)                  │
        │  | logical core (`mp`, `implTrans`, `weakenImpl`, …)     │
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

* **`Pf k φ`** — "φ has a proof transcript of ≤ `k` characters" (Critch's literal cost
  model, Appendix B), as one budget-indexed `Prop`. Three families, in declaration order:
  - **A. Reading rules** — transparency. The execution bridge (`atom`, and its Σ₁
    refutation twin `atomNeg`), then source transparency: one rule per `Prog` shape `S`
    can inspect, each paying its conclusion's size. Grows only when a new nesting shape
    must become readable.
  - **B. Logical glue** — a Hilbert basis for the impl/neg fragment. Implication
    INTRODUCTION (the deduction theorem) is deliberately absent: it would take `S` to
    full intuitionistic logic and break faithfulness and the bounds. That is why
    `implTrans`/`impS2` are primitive rather than derived from `mp`.
  - **C. Löb machinery** — the bounded derivability conditions (`boxIntro`, `atomBoxImpl`,
    `axK`/`axKf`, `box4`, `boxMono`) and the fixpoint legs `diagF`/`diagB`, which make
    bounded Löb a theorem rather than an axiom.
* **`PlaysProof me opp body a n`** — a play certificate: a character-costed transcript of
  `body` evaluating to `a`, one constructor per `eval` step. Its `.search` guards consult
  `Pf` — the back-edge that makes the block mutual.
* **`AtomProvable k φ`** — a `PlaysProof` whose cost fits the budget: the bridge for
  `.plays` atoms, which the reasoning rules cannot read.
* **`proofSearch k φ`** — the oracle agents query, defined as decidable `Pf`.

`Formula.interp` (Dynamics.lean) gives the semantics (`⊨ φ`); `sound_upto` (Base/) is the
Lean theorem `⊢_k φ ⟹ ⊨ φ`, bridging `S`-provability to truth.

**Zero axioms.** Every rule is a sound constructor. False guards are handled by
`PlaysProof.search_f` (an else-certificate from a Σ₁ REFUTATION of the guard, paying the
full failed budget — the floor) with `Pf.atomNeg`/`Pf.eqNeg` as the refutation suppliers.
Guards that are false (`¬ ⊨ guard`) but irrefutable (no `⊢ ¬guard`) leave their else-plays
true (`⊨`) but uncertifiable (no `⊢`): the honest Gödelian boundary. Costs are transcript-cumulative throughout.

**Eliminators.** `Pf` is mutual, so use the named `Pf.induct`/`PlaysProof.induct` (§4);
the raw recursors are used only there and in `Base/ValuationSoundness.lean`.
-/

-- 1. Per-step proof-encoding costs (Critch's `e*`, Appendix B(d)): the character cost
-- of transcribing one `eval` step. Concrete, every step ≥ 1 character, so a fuel-`n`
-- certificate has ≤ `n` steps — what makes the decision procedure terminate.
-- `c_guard k = numCost k` is the `O(lg k)` cost of writing the budget numeral `k`.
def c_leaf  : Nat := 1                          -- leaf step (`.const a`)
def c_node  : Nat := 1                          -- structural step (`.self`/`.opp`/`.bot`/`.sim`/`.ite`)
def c_guard (k : Nat) : Nat := numCost k        -- `.search` guard at budget `k`; grows with `k`

/-! ### The search telescope

A telescope is a list of `.search` layers — (guard budget, guard formula, else-branch)
per layer — around a constant branch. `searchPlug` rebuilds the source, `searchGuards`
collects the in-frame guard facts (outermost first; every layer's guard substitutes the
FULL `me`, which is why the telescope is read as one rule), and `implChain` folds them
into the implication chain `searchChain` concludes. -/

def searchPlug : List (Nat × Formula × Prog) → Prog → Prog
  | [], p => p
  | (g, ψ, e) :: L, p => .search g ψ (searchPlug L p) e

def searchGuards (me opponent : Prog) : List (Nat × Formula × Prog) → List Formula
  | [] => []
  | (g, ψ, _) :: L => .box g (ψ.subst me opponent) :: searchGuards me opponent L

/-- Right-fold a guard list into an implication chain. -/
def implChain (gs : List Formula) (tgt : Formula) : Formula :=
  gs.foldr .impl tgt

/-! ### The mixed telescope

`CtxLayer` extends the telescope to both shapes `eval` descends through on a positive
guard fact: a `.search` test and an `.ite` probe, each in THEN polarity. Probe guards are
restricted to the frame-independent `.sim .opp (.bot z)` — for any other guard the
in-frame run differs from the standalone atom and the reading is unsound (see
`iteBranchSearch_t`). An ite-ELSE rule would be sound but falsifies the floor censuses
(`Research/Notes/FAMILY_COMPLETION_DESIGN.md`); search-ELSE is covered by
`searchElseChain` below. -/

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

/-! ### The mixed-polarity search telescope

`SearchLayer2` records either descent polarity: a THEN layer contributes a `.box` guard
antecedent, an ELSE layer the Σ₁ refutation `.neg` of its guard (the `search_f` premise
shape). Else-guards are restricted to plays-atoms, stored structurally. `layersCost`
charges each else-layer its full failed budget plus a node (the `search_f` floor) and
each then-layer the `c_guard` cite of its fired guard. -/

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
    /-- `.search k φ p q` runs the TRUE-guard branch (`p`) when `S` derives the guard (`⊢_k guard`), so
        `search_t` carries `Pf k (guard)` as its premise. **This is the back-edge that makes the
        block mutual**: execution consults the proof system. -/
    | search_t :
        Pf k (φ.subst me opponent) →
        PlaysProof me opponent p a n →
        PlaysProof me opponent (.search k φ p q) a (n + c_guard k + c_node)
    /-- FALSE-guard branch: `.search k φ p q` runs the else branch when the guard search
        fails. Two design points, both forced:
        * the premise is a Σ₁ REFUTATION `Pf m (.neg guard)`, certifiable from the guard
          subject's actual play (`Pf.atomNeg`) — never mere unprovability `¬ ⊢_k guard` (premising on
          unprovability is a non-monotone fixpoint; the anti-diagonal bot is its paradox);
        * the cost pays the FULL failed budget `k`, the floor: an else-certificate must
          never fit within the budget whose failure it certifies, or `atom_monotone`
          would lift it back and re-fire the guard (a machine-checked inconsistency).
          The floor is also what lets soundness be proven by budget induction.
        Faithful: a PA-style proof that a bounded search fails checks every candidate. -/
    | search_f :
        Pf m (.neg (φ.subst me opponent)) →
        PlaysProof me opponent q a n →
        PlaysProof me opponent (.search k φ p q) a (n + m + k + c_node)
    /- `.tvote` (weighted-threshold action vote): five stepwise rules mirroring the
       `eval` peel one step each. Unlike `.search`, an entry is a closed deterministic
       program whose play is an atom, so "it plays C" and "it plays D" are both positive
       facts with ordinary transcripts: NO floor and no `Pf` premise anywhere in this
       block — `eval` determinism replaces the refutation. Entries are run `.bot`-framed
       (`PlaysProof (.bot I) (.bot I) I a m`), the frame of the probe atom
       `.plays (.bot I) (.bot I) a`. A non-terminating entry has no transcript, matching
       `eval`'s `none`. -/
    /-- Residual threshold met: the vote already succeeded; remaining entries are not
        consulted (mirrors `eval`'s then short-circuit). -/
    | voteZero_t {me opponent p q : Prog} {a : Action} {n : Nat} {v : VoteList} :
        PlaysProof me opponent p a n →
        PlaysProof me opponent (.tvote v 0 p q) a (n + c_node)
    /-- Entries exhausted with residual threshold still positive: the vote failed. -/
    | voteNil_f {me opponent p q : Prog} {a : Action} {n θ : Nat} :
        θ ≠ 0 →
        PlaysProof me opponent q a n →
        PlaysProof me opponent (.tvote .nil θ p q) a (n + c_node)
    /-- Head entry PLAYS `C`: cite its transcript and continue peeling with the weight
        subtracted from the residual threshold. -/
    | voteCons_c {me opponent p q : Prog} {a : Action} {n θ w m : Nat} {I : Prog}
        {rest : VoteList} :
        θ ≠ 0 →
        PlaysProof (.bot I) (.bot I) I Action.C m →
        PlaysProof me opponent (.tvote rest (θ - w) p q) a n →
        PlaysProof me opponent (.tvote (.cons w I rest) θ p q) a (n + m + c_node)
    /-- Head entry PLAYS `D`: cite its transcript — a POSITIVE fact, no refutation and
        no floor — and continue peeling with the threshold unchanged. -/
    | voteCons_d {me opponent p q : Prog} {a : Action} {n θ w m : Nat} {I : Prog}
        {rest : VoteList} :
        θ ≠ 0 →
        PlaysProof (.bot I) (.bot I) I Action.D m →
        PlaysProof me opponent (.tvote rest θ p q) a n →
        PlaysProof me opponent (.tvote (.cons w I rest) θ p q) a (n + m + c_node)
    /-- The threshold exceeds the total mass: the else branch is forced without reading
        any entry's action. `hterm` is load-bearing: an entry may not terminate, and `eval`
        sinks the whole vote to `none` if one doesn't — `tvote [(1, MirrorBot)] 5 C D`
        evaluates to `none` at every fuel although `θ > totalMass`. The shortcut may skip
        READING the entries, not their TERMINATION; that evidence is charged (`+ c`). -/
    | voteHigh_f {me opponent p q : Prog} {a : Action} {n θ : Nat} {v : VoteList} :
        θ > v.totalMass →
        VoteAllPlay v c →
        PlaysProof me opponent q a n →
        PlaysProof me opponent (.tvote v θ p q) a (n + c + v.vsize + c_node)
    /-- `.sys` unfolding: component `i`, closed one level via `sysClose`, exactly as
        `eval`'s lazy-unfold arm. A syntactic rewrap, so it pays `c_node`. There is
        deliberately no rule for `.selfIdx`: a dangling reference evaluates to `none`,
        and nothing about it should be `S`-derivable. -/
    | sysStep {me opponent : Prog} {defs : ProgList} {i : Nat} {p : Prog} {a : Action}
        {n : Nat} :
        defs.get? i = some p →
        PlaysProof me opponent (p.sysClose defs) a n →
        PlaysProof me opponent (.sys defs i) a (n + c_node)

/-- "Every entry of this vote list plays SOMETHING" — `voteHigh_f`'s termination
    side-condition. Action-agnostic by design: once the threshold is unreachable the
    actions do not matter, only that they exist. -/
  inductive VoteAllPlay : VoteList → Nat → Prop where
    | nil : VoteAllPlay .nil 0
    | cons {w : Nat} {I : Prog} {rest : VoteList} {a : Action} {m c : Nat} :
        PlaysProof (.bot I) (.bot I) I a m → VoteAllPlay rest c → VoteAllPlay (.cons w I rest) (m + c)

-- 3. `AtomProvable k φ` — a `PlaysProof` whose run cost fits the budget (`n ≤ k`); the bridge for
-- atomic `.plays` facts (which the reasoning rules cannot read).
  inductive AtomProvable : Nat → Formula → Prop where
    | mk : PlaysProof me opponent me a n → n ≤ k → AtomProvable k (.plays me opponent a)

/-- **`Pf k φ` — "φ has a proof transcript of ≤ k characters"**: the proof system `S`, as ONE type.
Written `⊢_k φ` (`Research/Notes/PROVABILITY_NOTATION.md`); `⊢` never means Lean.

Each rule is (i) SOUND — `⊨` of its conclusion follows from `⊨` of its premises
(the Lean theorem `BaseTheorems.sound_upto`) — and (ii) FAITHFUL to a PA-like `S` (critch22 Appendix B): a genuine
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
        `p` plays `b` with an `S`-certificate (`AtomProvable`) and `b ≠ aN`, then `¬(p plays aN)` — sound by
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
    /-- S reads a `.bot`-wrapped `.sim`. Sound, unlike general `.bot` transparency
        `plays z → plays (.bot z)`: the `.bot` is read as `me`'s OWN body, so `subst`
        uses the same `me` throughout and no sub-program's `.self` is rebound. -/
    | botSimStep (me p q opponent : Prog) (a : Action) (hme : me = .bot (.sim p q)) :
        (Formula.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                      (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                    (.plays me opponent a))
    /-- The `.bot (.search …)` twin of `searchBranch`, sound as `botSimStep` is. Needed
        when a searcher appears `.bot`-wrapped as a PLAYER whose source S must read. -/
    | botSearchStep (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
        (hme : me = .bot (.search g ψ (.const a) (.const b))) :
        (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a))
    /-- The `.sys` twin of `botSearchStep`: component `i` of the system is a
        constant-branch searcher, and its guard is closed one level with `sysClose`,
        exactly where `eval`'s `.sys` arm closes it. For an entangled pair the closed
        guard names the PARTNER (`.selfIdx j ↦ .sys defs j`), so the conclusion is the
        cross-implication `□(partner plays …) → me plays a` the mutual Löb engine consumes. -/
    | botSysSearchStep (defs : ProgList) (i : Nat) (g : Nat) (ψ : Formula)
        (a b : Action) (me opponent : Prog)
        (hme : me = .bot (.sys defs i))
        (hget : defs.get? i = some (.search g ψ (.const a) (.const b))) :
        (Formula.impl (.box g ((ψ.sysClose defs).subst me opponent))
                      (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.box g ((ψ.sysClose defs).subst me opponent))
                    (.plays me opponent a))
    /-- The `.sys` twin of `botSimStep`: component `i` is a bare copy of component `j`
        (`.sim (.bot (.selfIdx j)) (.bot (.selfIdx j))`), the forwarder shape. Action-
        generic: one rule reads a Löb fixpoint on cooperation and one on defection alike.
        Sound because both operands are `.bot`-frozen, so the copied play does not depend
        on `opponent`. -/
    | botSysSimStep (defs : ProgList) (i j : Nat) (a : Action) (me opponent : Prog)
        (hme : me = .bot (.sys defs i))
        (hget : defs.get? i = some (.sim (.bot (.selfIdx j)) (.bot (.selfIdx j)))) :
        (Formula.impl (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) a)
                      (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) a)
                    (.plays me opponent a))
    /-- The `.sys` twin of `searchThenSearch_t`: component `i` is a searcher whose
        then-branch is itself a searcher (the PrudentBot shape), with the inner guard a
        held premise cited at `c_guard k₂`. -/
    | botSysSearchThenSearch (defs : ProgList) (i k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula)
        (c0 c1 : Action) (q me opponent : Prog)
        (hme : me = .bot (.sys defs i))
        (hget : defs.get? i = some (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q)) :
        Pf m ((ψ₂.sysClose defs).subst me opponent) → m ≤ k₂ →
        c_guard k₂ +
          (Formula.impl (.box k₁ ((ψ₁.sysClose defs).subst me opponent))
            (.plays me opponent c0)).size ≤ k →
        Pf k (.impl (.box k₁ ((ψ₁.sysClose defs).subst me opponent)) (.plays me opponent c0))
    /-- S reads an `.ite` whose then-branch is a `.search`, FUSED into one rule: `eval`
        runs the branch in the OUTER frame, where its guard is `proofSearch g (ψ.subst me
        opponent)`, whereas the same `.search` run as its own program would see a doubly
        substituted guard — so a generic "branch plays `a`" premise could not be a sound
        `.plays` atom. Restricted to a frame-independent `.sim .opp (.bot z)` guard and a
        constant-branch inner search, which every zoo bot satisfies. -/
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
    /-- Stacked `.search` (Critch's PrudentBot shape): `me` plays `c0` when both guards
        hold. Primitive — the then-branch is a `.search`, not a `.const` — and carrying
        the inner proof as a premise collapses the two guards to the single-box
        conclusion `□_{k₁} ψ₁' → me plays c0` the bounded-Löb engine consumes. -/
    | searchThenSearch_t (k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula) (c0 c1 : Action)
        (q me opponent : Prog)
        (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) :
        Pf m (ψ₂.subst me opponent) → m ≤ k₂ →
        c_guard k₂ +
          (Formula.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0)).size ≤ k →
        Pf k (.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0))
    /-- The search-telescope reading rule: for a stack of `.search` layers of any depth
        over a constant then-branch, S proves the full guard chain
        `□_{g₁} ψ₁' → … → □_{gₙ} ψₙ' → me plays a`. The head layer is kept explicit so
        the conclusion is syntactically an `.impl` with a `.box` antecedent. Premise-free;
        soundness is the telescope-eval induction (`searchPlug_eval`). -/
    | searchChain (g₁ : Nat) (ψ₁ : Formula) (e₁ : Prog)
        (L : List (Nat × Formula × Prog)) (a : Action) (me opponent : Prog)
        (hme : me = .search g₁ ψ₁ (searchPlug L (.const a)) e₁) :
        (Formula.impl (.box g₁ (ψ₁.subst me opponent))
          (implChain (searchGuards me opponent L) (.plays me opponent a))).size ≤ k →
        Pf k (.impl (.box g₁ (ψ₁.subst me opponent))
          (implChain (searchGuards me opponent L) (.plays me opponent a)))
    /-- The mixed-telescope reading rule: any nonempty stack of `.search` layers and
        frame-independent `.ite`-probe layers over a constant; `.box` antecedents for the
        former, `.plays opponent (.bot z) r` probe antecedents for the latter. Subsumes
        `searchChain`. Premise-free; soundness is `ctxPlug_eval`. -/
    | ctxChain (hd : CtxLayer) (L : List CtxLayer) (a : Action) (me opponent : Prog)
        (hme : me = ctxPlug (hd :: L) (.const a)) :
        (Formula.impl (ctxGuard me opponent hd)
          (implChain (ctxGuards me opponent L) (.plays me opponent a))).size ≤ k →
        Pf k (.impl (ctxGuard me opponent hd)
          (implChain (ctxGuards me opponent L) (.plays me opponent a)))
    /-- S can verify structural identity by reflexivity: any program equals itself. -/
    | eqRefl (p : Prog) :
        (Formula.eq p p).size ≤ k → Pf k (.eq p p)
    /-- S refutes structural identity of syntactically distinct programs — the Σ₁
        counterpart of `eqRefl`. Feeds `search_f` for failed `.eq` guards. -/
    | eqNeg (p q : Prog) (hne : p ≠ q) :
        (Formula.neg (.eq p q)).size ≤ k → Pf k (.neg (.eq p q))

    -- ═══ Family B. LOGICAL GLUE — the propositional core ═══
    /-- Modus ponens. Transcript: both subtrees plus the conclusion. -/
    | mp (m₁ m₂ : Nat) (φ α : Formula) :
        Pf m₁ (.impl φ α) → Pf m₂ φ → m₁ + m₂ + α.size ≤ k → Pf k α
    /-- Transitivity of implication. Primitive: with no implication introduction, `S`
        cannot derive it from `mp`. -/
    | implTrans (φ ψ χ : Formula) (a b : Nat) :
        Pf a (.impl φ ψ) → Pf b (.impl ψ χ) →
        a + b + (Formula.impl φ χ).size ≤ k → Pf k (.impl φ χ)
    /-- True-consequent implication: from `⊢_m ψ` infer `⊢_k φ → ψ`. Derivable from `implK` + `mp`; kept
        primitive for transcript tightness. This is what lets `S` derive the implication guards
        of CIMCIC and DIMCID. -/
    | weakenImpl (φ ψ : Formula) (m : Nat) :
        Pf m ψ → m + (Formula.impl φ ψ).size ≤ k → Pf k (.impl φ ψ)
    /-- Closed composition: from `⊢_{m₁} φ → (ψ → χ)` and `⊢_{m₂} φ → ψ`, infer `⊢_K φ → χ`. The
        rule form suffices because both premises are closed. -/
    | impS2 (φ ψ χ : Formula) (m₁ m₂ K : Nat) :
        Pf m₁ (.impl φ (.impl ψ χ)) → Pf m₂ (.impl φ ψ) →
        m₁ + m₂ + (Formula.impl φ χ).size ≤ K → Pf K (.impl φ χ)
    /-- `⊢_k φ → φ`. Without it `S` could not prove this tautology (no deduction theorem,
        no premise-free implication leaf), and a bot guarding on `.impl A A` fell through. -/
    | implRefl (φ : Formula) :
        (Formula.impl φ φ).size ≤ k → Pf k (.impl φ φ)
    /-- Hilbert K as an object formula, `⊢_k φ → (ψ → φ)`. -/
    | implK (φ ψ : Formula) :
        (Formula.impl φ (.impl ψ φ)).size ≤ k → Pf k (.impl φ (.impl ψ φ))
    /-- Hilbert S as an object formula. With `implK` and `mp` this completes the positive
        implicational fragment: the deduction theorem becomes ADMISSIBLE
        (`Base/Closure.deduction_theorem`) without being a rule. -/
    | implS (φ ψ χ : Formula) :
        (Formula.impl (.impl φ (.impl ψ χ))
          (.impl (.impl φ ψ) (.impl φ χ))).size ≤ k →
        Pf k (.impl (.impl φ (.impl ψ χ)) (.impl (.impl φ ψ) (.impl φ χ)))
    /-- Contraposition, `⊢_m φ → ψ ⟹ ⊢_k ¬ψ → ¬φ` — the logical core's `.neg` consumer. -/
    | contrapose (φ ψ : Formula) (m : Nat) :
        Pf m (.impl φ ψ) →
        m + (Formula.impl (.neg ψ) (.neg φ)).size ≤ k →
        Pf k (.impl (.neg ψ) (.neg φ))
    /-- Ex falso. VACUOUS in the consistent `S`: by soundness its premises never coexist,
        so every metatheory case discharges by contradiction. Present for the completeness
        of Family B, not for new theorems. -/
    | negElim (φ ψ : Formula) (m₁ m₂ : Nat) :
        Pf m₁ (.neg φ) → Pf m₂ φ →
        m₁ + m₂ + ψ.size ≤ k →
        Pf k ψ

    -- ═══ Family C. LÖB MACHINERY — modal / HBL tier (bounded derivability conditions) ═══
    /-- Bounded necessitation (HBL D2): from `⊢_{kIn} φ`, `S` derives `□_{kIn} φ` (at `K`).
        Sound with no axiom — `⊨ □_{kIn} φ` IS `⊢_{kIn} φ` (`Pf kIn φ`). -/
    | boxIntro (kIn K : Nat) (φ : Formula) :
        Pf kIn φ →
        kIn + (Formula.box kIn φ).size ≤ K →
        Pf K (.box kIn φ)
    /-- Bounded Σ₁-completeness for play-atoms, certificate-carrying: it fires only when a
        size-≤-`kBox` transcript exists, which keeps it on the sound Σ₁ side (not the
        GL-excluded converse necessitation). -/
    | atomBoxImpl (kBox : Nat) (p q : Prog) (a : Action) :
        AtomProvable kBox (.plays p q a) →
        kBox + (Formula.impl (.plays p q a) (.box kBox (.plays p q a))).size ≤ k →
        Pf k (.impl (.plays p q a) (.box kBox (.plays p q a)))
    /-- GL axiom K, rule form: from `⊢_m □_a (φ → α)`, infer `⊢_K □_b φ → □_c α`. -/
    | axK (a b c m K : Nat) (φ α : Formula) :
        Pf m (.box a (.impl φ α)) →
        a + b + α.size ≤ c →
        m + (Formula.impl (.box b φ) (.box c α)).size ≤ K →
        Pf K (.impl (.box b φ) (.box c α))
    /-- GL axiom K as an object formula — Löb's middle step needs it premise-free. -/
    | axKf (a b c K : Nat) (φ α : Formula) :
        a + b + α.size ≤ c →
        (Formula.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α))).size ≤ K →
        Pf K (.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α)))
    /-- GL axiom 4 / object necessitation, `□_a φ → □_b (□_a φ)`. Its interp is the
        identity `Pf a φ → Pf a φ`. -/
    | box4 (a b K : Nat) (φ : Formula) :
        a + (Formula.box a φ).size ≤ b →
        (Formula.impl (.box a φ) (.box b (.box a φ))).size ≤ K →
        Pf K (.impl (.box a φ) (.box b (.box a φ)))
    /-- Upward box-subscript monotonicity, `□_a φ → □_b φ` for `a ≤ b`: the transcript
        model lands K-distribution outputs at computed subscripts that must be weakened up
        onto the consumers' source-literal boxes. -/
    | boxMono (a b K : Nat) (φ : Formula) :
        a ≤ b →
        (Formula.impl (.box a φ) (.box b φ)).size ≤ K →
        Pf K (.impl (.box a φ) (.box b φ))
    /-- Löb-fixpoint leg, forward: `ψ → (□_g ψ → tgt)` for `ψ := .diag g tgt`. Sound with
        no axiom (`ψ.interp` IS `Pf g ψ → tgt.interp`). Gated on the Löb premise
        `Pf pm (□_fb tgt → tgt)`, which the Löb chain always has and which preserves the
        exclusion invariants. -/
    | diagF (pm fb g K : Nat) (tgt : Formula) :
        Pf pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)).size ≤ K →
        Pf K (.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt))
    /-- Löb-fixpoint leg, backward: `(□_g ψ → tgt) → ψ`. Sound as `diagF`. -/
    | diagB (pm fb g K : Nat) (tgt : Formula) :
        Pf pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)).size ≤ K →
        Pf K (.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt))
    /-- The mixed-polarity search-telescope reading rule: `.search` layers descending the
        THEN slot (`.box` antecedent) or the ELSE slot (`.neg` antecedent — the Σ₁
        refutation of the crossed guard, never an unprovability claim). S replays each
        failed search at its full budget (`layersCost`, the `search_f` floor — forced by
        provable soundness, and what keeps every floor census true) and cites each fired
        guard. Premise-free; soundness is `plug2_eval` (Base/ValuationSoundness). -/
    | searchElseChain (hd : SearchLayer2) (L : List SearchLayer2) (a : Action)
        (me opponent : Prog)
        (hme : me = plug2 (hd :: L) (.const a)) :
        layersCost (hd :: L) +
          (Formula.impl (guard2 me opponent hd)
            (implChain (guards2 me opponent L) (.plays me opponent a))).size ≤ k →
        Pf k (.impl (guard2 me opponent hd)
          (implChain (guards2 me opponent L) (.plays me opponent a)))
end

/-! ## 4. The named eliminators — use these, never the raw recursors

`Pf` is mutual, so `induction h with` is unavailable; these `@[elab_as_elim]` theorems
repackage the raw recursor behind named hypotheses: `induction h using Pf.induct with
| atom … | mp … | …`. The motive takes the proof term (a proof-irrelevant motive breaks
`induction using`). -/

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
    (botSysSearchStep : ∀ (k : Nat) (defs : ProgList) (i g : Nat) (ψ : Formula)
        (a b : Action) (me opponent : Prog)
        (hme : me = .bot (.sys defs i))
        (hget : defs.get? i = some (.search g ψ (.const a) (.const b)))
        (hle : (Formula.impl (.box g ((ψ.sysClose defs).subst me opponent))
                             (.plays me opponent a)).size ≤ k),
        motive k _ (.botSysSearchStep defs i g ψ a b me opponent hme hget hle))
    (botSysSimStep : ∀ (k : Nat) (defs : ProgList) (i j : Nat) (a : Action)
        (me opponent : Prog)
        (hme : me = .bot (.sys defs i))
        (hget : defs.get? i = some (.sim (.bot (.selfIdx j)) (.bot (.selfIdx j))))
        (hle : (Formula.impl (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) a)
                             (.plays me opponent a)).size ≤ k),
        motive k _ (.botSysSimStep defs i j a me opponent hme hget hle))
    (botSysSearchThenSearch : ∀ (k : Nat) (defs : ProgList) (i k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula)
        (c0 c1 : Action) (q me opponent : Prog)
        (hme : me = .bot (.sys defs i))
        (hget : defs.get? i = some (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q))
        (hprud : Pf m ((ψ₂.sysClose defs).subst me opponent)) (hmk : m ≤ k₂)
        (hle : c_guard k₂ +
          (Formula.impl (.box k₁ ((ψ₁.sysClose defs).subst me opponent))
            (.plays me opponent c0)).size ≤ k),
        motive m _ hprud →
        motive k _ (.botSysSearchThenSearch defs i k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hget
          hprud hmk hle))
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
    (motive_2 := fun _ _ _ => True)        -- VoteAllPlay
    (motive_3 := fun _ _ _ => True)
    (motive_4 := motive)
    -- PlaysProof arms (19) + VoteAllPlay arms (2) + AtomProvable.mk (1): motive is `True`.
    trivial (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial)
    -- tvote arms: Zero_t, Nil_f, Cons_c, Cons_d, High_f
    (fun _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial)
    -- sysStep arm
    (fun _ _ _ => trivial)
    -- VoteAllPlay arms: nil, cons
    trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial)
    -- Pf arms (27, family order A/B/C): route each to its named hypothesis.
    (fun {k} {φ} hatom _ => atom k φ hatom)
    (fun {k} p q b aN m hatom hne hle _ => atomNeg k p q b aN m hatom hne hle)
    (fun {k} g ψ a b me opponent hme hle => searchBranch k g ψ a b me opponent hme hle)
    (fun {k} me p q opponent a hme hle => simStep k me p q opponent a hme hle)
    (fun {k} me p q opponent a hme hle => botSimStep k me p q opponent a hme hle)
    (fun {k} g ψ a b me opponent hme hle => botSearchStep k g ψ a b me opponent hme hle)
    (fun {k} defs i g ψ a b me opponent hme hget hle =>
      botSysSearchStep k defs i g ψ a b me opponent hme hget hle)
    (fun {k} defs i j a me opponent hme hget hle =>
      botSysSimStep k defs i j a me opponent hme hget hle)
    (fun {k} defs i k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hget hprud hmk hle ih =>
      botSysSearchThenSearch k defs i k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hget hprud hmk hle ih)
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
    -- `.tvote` arms: the entry premises (`hI`) carry their own motive obligation in the
    -- entry's frame `I I I`; consumers that only care about the enclosing player
    -- discharge those with `fun _ => trivial`-style arguments.
    (voteZero_t : ∀ (me opponent p q : Prog) (a : Action) (n : Nat) (v : VoteList)
        (hp : PlaysProof me opponent p a n),
        motive me opponent p a n hp →
        motive me opponent (.tvote v 0 p q) a (n + c_node) (.voteZero_t hp))
    (voteNil_f : ∀ (me opponent p q : Prog) (a : Action) (n θ : Nat)
        (hθ : θ ≠ 0) (hq : PlaysProof me opponent q a n),
        motive me opponent q a n hq →
        motive me opponent (.tvote .nil θ p q) a (n + c_node) (.voteNil_f hθ hq))
    (voteCons_c : ∀ (me opponent p q : Prog) (a : Action) (n θ w m : Nat) (I : Prog)
        (rest : VoteList)
        (hθ : θ ≠ 0) (hI : PlaysProof (.bot I) (.bot I) I Action.C m),
        motive (.bot I) (.bot I) I Action.C m hI →
        ∀ (hp : PlaysProof me opponent (.tvote rest (θ - w) p q) a n),
        motive me opponent (.tvote rest (θ - w) p q) a n hp →
        motive me opponent (.tvote (.cons w I rest) θ p q) a (n + m + c_node)
          (.voteCons_c hθ hI hp))
    (voteCons_d : ∀ (me opponent p q : Prog) (a : Action) (n θ w m : Nat) (I : Prog)
        (rest : VoteList)
        (hθ : θ ≠ 0) (hI : PlaysProof (.bot I) (.bot I) I Action.D m),
        motive (.bot I) (.bot I) I Action.D m hI →
        ∀ (hq : PlaysProof me opponent (.tvote rest θ p q) a n),
        motive me opponent (.tvote rest θ p q) a n hq →
        motive me opponent (.tvote (.cons w I rest) θ p q) a (n + m + c_node)
          (.voteCons_d hθ hI hq))
    (voteHigh_f : ∀ (me opponent p q : Prog) (a : Action) (n θ c : Nat) (v : VoteList)
        (hθ : θ > v.totalMass) (hterm : VoteAllPlay v c)
        (hq : PlaysProof me opponent q a n),
        motive me opponent q a n hq →
        motive me opponent (.tvote v θ p q) a (n + c + v.vsize + c_node)
          (.voteHigh_f hθ hterm hq))
    (sysStep : ∀ (me opponent : Prog) (defs : ProgList) (i : Nat) (p : Prog) (a : Action)
        (n : Nat) (hget : defs.get? i = some p)
        (h : PlaysProof me opponent (p.sysClose defs) a n),
        motive me opponent (p.sysClose defs) a n h →
        motive me opponent (.sys defs i) a (n + c_node) (.sysStep hget h))
    {me opponent body : Prog} {a : Action} {n : Nat} (h : PlaysProof me opponent body a n) :
    motive me opponent body a n h := by
  -- The `Pf` arms + `AtomProvable.mk` are irrelevant here (their motives are `True`).
  refine PlaysProof.rec
    (motive_1 := motive)
    (motive_2 := fun _ _ _ => True)        -- VoteAllPlay
    (motive_3 := fun _ _ _ => True)
    (motive_4 := fun _ _ _ => True)
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
    (fun {me opponent p q} {a} {n} {v} hp ihp =>
      voteZero_t me opponent p q a n v hp ihp)
    (fun {me opponent p q} {a} {n θ} hθ hq ihq =>
      voteNil_f me opponent p q a n θ hθ hq ihq)
    (fun {me opponent p q} {a} {n θ w m} {I} {rest} hθ hI hp ihI ihp =>
      voteCons_c me opponent p q a n θ w m I rest hθ hI ihI hp ihp)
    (fun {me opponent p q} {a} {n θ w m} {I} {rest} hθ hI hq ihI ihq =>
      voteCons_d me opponent p q a n θ w m I rest hθ hI ihI hq ihq)
    (fun hθ hterm hq _ihterm ihq =>
      voteHigh_f _ _ _ _ _ _ _ _ _ hθ hterm hq ihq)
    (fun {me opponent} {defs} {i} {p} {a} {n} hget h ih =>
      sysStep me opponent defs i p a n hget h ih)
    -- VoteAllPlay arms (motive `True`): nil, cons
    trivial (fun _ _ _ _ => trivial)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_
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
  | botSysSearchStep defs i g ψ a b me opponent hme hget hle =>
      exact .botSysSearchStep defs i g ψ a b me opponent hme hget (Nat.le_trans hle hk)
  | botSysSimStep defs i j a me opponent hme hget hle =>
      exact .botSysSimStep defs i j a me opponent hme hget (Nat.le_trans hle hk)
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
  | botSysSearchThenSearch defs i k₁' k₂' m ψ₁ ψ₂ c0 c1 q me opponent hme hget hprud hmk hle =>
      exact .botSysSearchThenSearch defs i k₁' k₂' m ψ₁ ψ₂ c0 c1 q me opponent hme hget hprud hmk
        (Nat.le_trans hle hk)
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

-- 6. The proof-search oracle: bounded `S`-provability (`⊢_k φ`) reflected into `Bool` for the
-- evaluator's guard. Classical (hence noncomputable), correct for an oracle.
noncomputable def proofSearch (k : Nat) (φ : Formula) : Bool := decide (Pf k φ)


/-- 7. Character budget for a `fuel`-step play's atom certificate. Honest `O(fuel)`
    (Critch's `e*`, Appendix B(d)): `c_node + c_guard fuel` per step, plus a leaf.
    `c_guard fuel` over-approximates every guard budget reachable in the run. -/
def atom_cost (fuel : Nat) : Nat := c_leaf + (c_node + c_guard fuel) * fuel


end PD
