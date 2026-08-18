namespace PD

inductive Action
  | C
  | D
  deriving DecidableEq, Repr, BEq

abbrev Outcome := Action × Action

-- `Prog` is the language of agents from Critch 2022 (the Python-style
-- pseudocode). It is pure *source code*: no constructor produces an
-- `Action` directly — actions only appear after evaluation via `eval`
-- in Dynamics.lean. Keeping everything at the syntactic level is what lets
-- agents be nested, substituted, and passed as subjects of formulas.

-- `Formula` is the part of the proof system `S` that agents query through the oracle,
-- just enough to express hypotheses like `"opp(CUPOD_k.source) == D"`.
-- We can see `Formula` as the language of the ambient logic in which agents reason about each other.
-- Note: `Formula` is not a full internalization of the ambient logic — it only has the constructs we need to express the theorems in this file.

-- They are mutually recursive because `.search` carries a formula as
-- its guard, and a formula's `.plays` atom takes programs as subjects:
-- agents reason about agents reasoning about agents.

mutual
  inductive Prog: Type where
    | const  : Action → Prog                      -- trivial bots like CB/DB: ignore opp, play a fixed action
    | self   : Prog                               -- placeholder for "my own source" — closed by `subst`
    | opp    : Prog                               -- placeholder for the opponent's source — closed by `subst`
    | bot    : Prog → Prog                        -- closed bot reference; `subst` does not descend
    | sim    : Prog → Prog → Prog                 -- source code for "run p with q as opponent"
    | ite    : Prog → Action → Prog → Prog → Prog -- if evaluating guard yields action a, run p, else q
    | search : Nat → Formula → Prog → Prog → Prog -- proof_search(k, φ): if oracle verifies φ in ≤k chars, run p, else q
    | tsearch : Nat → GuardList → Nat → Prog → Prog → Prog
        -- weighted-THRESHOLD proof search (the Def-4 TauBot primitive, 2026-08-11):
        -- `tsearch k gs θ p q` peels the weighted guards `gs` IN LIST ORDER; a guard
        -- `(w, φ)` fires iff the oracle verifies `φ` within `k` chars, and firing
        -- subtracts `w` from the residual threshold (truncated). Residual 0 → run `p`;
        -- guards exhausted (or unreachable) with residual > 0 → run `q`.
        -- `.search k φ p q` is behaviorally the singleton `tsearch k [(1,φ)] 1 p q`,
        -- but is kept as its own constructor: the modal reading rules
        -- (`searchBranch`/`botSearchStep`) and all 81 outcome theorems stay untouched.
        -- SCHEDULED FOR REMOVAL (DEF4_TVOTE_ROADMAP.md Phase 4b): `.tvote` subsumes it
        -- (`tsearch k [(wᵢ,φᵢ)] θ p q ≡ tvote [(wᵢ, .search k φᵢ C D)] θ p q`).
    | tvote : VoteList → Nat → Prog → Prog → Prog
        -- weighted-threshold ACTION vote (the refined Def-4 TauBot primitive, 2026-08-18):
        -- `tvote v θ p q` peels the weighted entries `v` IN LIST ORDER; an entry
        -- `(w, I)` fires iff the closed program `I` PLAYS `C` (running against itself —
        -- entries are `.opp`-free instances), and firing subtracts `w` from the residual
        -- threshold (truncated). Residual 0 → run `p`; entries exhausted with residual
        -- > 0 → run `q`.
        --
        -- The vote reads TRUE PLAYS, not provability: that is the whole point of the
        -- refined Def 4 (`DEF4_TVOTE_ROADMAP.md` §0). A tau player votes once over the
        -- compound decisions of its own δ-instances; every `proofSearch` lives INSIDE
        -- an entry, exactly where the lifted base bot's own code puts it. NO budget
        -- argument: the vote itself never consults the oracle.
        --
        -- Entries are FROZEN (like `.bot` / the `.eq` RHS / `.diag`): `subst` does not
        -- descend into a `VoteList`. That is what keeps tau players `.opp`-free by
        -- construction — an entry is a closed instance, never a window on the current
        -- frame.
  /-- The weighted entry list carried by `.tvote`: a specialized list kept INSIDE the
      mutual block, for the same reason `GuardList` is (a nested `List (Nat × Prog)`
      payload would make `Prog` a nested inductive). `cons w I rest` = hypothesis
      instance `I` with signal weight `w`. -/
  inductive VoteList : Type where
    | nil  : VoteList
    | cons : Nat → Prog → VoteList → VoteList
  /-- The weighted guard list carried by `.tsearch`: a specialized list kept INSIDE the
      mutual block (a nested `List (Nat × Formula)` payload would make `Prog` a nested
      inductive — recursor complications in `subst`/`size`/enumeration everywhere).
      `cons w φ rest` = hypothesis guard `φ` with signal weight `w`. -/
  inductive GuardList : Type where
    | nil  : GuardList
    | cons : Nat → Formula → GuardList → GuardList
  inductive Formula: Type where
    | plays : Prog → Prog → Action → Formula      -- atomic: "p(q.source) == a"
    | impl  : Formula → Formula → Formula         -- φ → ψ (needed for Löb-style hypotheses like □C → C)
    | neg   : Formula → Formula                   -- ¬ φ
    | box   : Nat → Formula → Formula             -- □_n φ: "φ is provable by the oracle with budget n"
    | eq    : Prog → Prog → Formula               -- structural identity: "p and q are the same program". The 2nd arg is a frozen literal target (subst does not descend into it); the 1st is the probe (typically `.opp`), which subst resolves to the concrete player.
    | diag  : Nat → Formula → Formula             -- the Löb-fixpoint sentence for target `tgt` at box budget `g`: ψ with ψ ↔ (□_g ψ → tgt). Its meaning (Dynamics.interp) is the fixpoint BY DESIGN — same pattern as `.box` meaning `Pf`; the meta-justification that a faithful arithmetization contains such a sentence is the Reflection layer's DERIVED diagonal (Research/Notes/INTERNALIZATION_ROADMAP.md, I0). Never appears in bot source; used only by the meta Löb chain (bounded Löb / PBLT).
end
deriving instance DecidableEq for Prog, GuardList, VoteList, Formula

-- Closing self-reference via substitution.
--
-- `.self` and `.opp` are *placeholders* (free variables) standing for
-- "my own source" and "the opponent's source" — the Python pseudocode's
-- `subst` walks replaces every `.self` with `me` and every `.opp` with `opponent`;


-- This matters because the oracle `proofSearch : Nat → Formula → Bool`
-- expects a *closed* formula — one with no free placeholders. So at every
-- evaluation boundary where a new context is entered (`.sim` and
-- `.search` in Eval.lean), the evaluator calls `subst` to freeze the
-- placeholders to the concrete programs currently playing the game.

-- The two definitions are mutually recursive for the same reason the
-- types are: `Prog.subst` descends into formulas at `.search`, and
-- `Formula.subst` descends into programs at `.plays`.

-- Note: `subst` is one-shot, not a fixed point. Placeholders inside the
-- freshly inserted `me`/`opponent` are *not* re-substituted — they remain
-- bound to whatever context will enclose them next.

-- Scope barrier: `.bot p` marks `p` as a *closed bot reference* — i.e. one
-- bot literally naming another bot in its source. `Prog.subst` does NOT
-- descend into `.bot p`, so the outer frame's `me`/`opponent` cannot capture
-- the placeholders inside `p`. Without this barrier, when EBot's body
-- contains `.sim .opp MirrorBot` (with `MirrorBot = .sim .opp .self`), the
-- outer `subst` rewrites `MirrorBot.subst me opp = .sim opp me` — turning a
-- probe of "what does opp do against MirrorBot?" into a self-simulation
-- shape, breaking EBot vs EBot. `.bot` is the fix point at the substitution
-- layer; `eval` (Eval.lean) handles `.bot` separately by simply
-- unwrapping it (one fuel decrement) so any `.self`/`.opp` inside the
-- wrapped body bind to the *current* frame, as intended.
mutual
  def Prog.subst : Prog → (me opponent : Prog) → Prog
    | .const a,        _, _ => .const a
    | .self,           m, _ => m
    | .opp,            _, o => o
    | .bot p,          _, _ => .bot p
    | .sim p q,        m, o => .sim (p.subst m o) (q.subst m o)
    | .ite b a p q,    m, o => .ite (b.subst m o) a (p.subst m o) (q.subst m o)
    | .search k φ p q, m, o => .search k (φ.subst m o) (p.subst m o) (q.subst m o)
    | .tsearch k gs θ p q, m, o => .tsearch k (gs.gsubst m o) θ (p.subst m o) (q.subst m o)
    -- Entries are FROZEN — `subst` rewrites only the branches. A `VoteList` holds closed
    -- δ-instances; descending would let the enclosing frame's `me`/`opponent` capture an
    -- instance's internal placeholders (the `.bot` barrier rationale, one level up), and
    -- would break the `.opp`-freeness that makes tau players extensionally constant.
    | .tvote v θ p q,      m, o => .tvote v θ (p.subst m o) (q.subst m o)
  termination_by structural p _ _ => p

  /-- `subst` mapped over a guard list: weights and structure unchanged, every guard
      formula closed against the current frame (same boundary discipline as `.search`). -/
  def GuardList.gsubst : GuardList → (me opponent : Prog) → GuardList
    | .nil,           _, _ => .nil
    | .cons w φ rest, m, o => .cons w (φ.subst m o) (rest.gsubst m o)
  termination_by structural gs _ _ => gs

  def Formula.subst : Formula → (me opponent : Prog) → Formula
    | .plays p q a, m, o => .plays (p.subst m o) (q.subst m o) a
    | .impl φ ψ,    m, o => .impl (φ.subst m o) (ψ.subst m o)
    | .neg φ,       m, o => .neg (φ.subst m o)
    | .box n φ,     m, o => .box n (φ.subst m o)
    | .eq p q,      m, o => .eq (p.subst m o) q   -- only the LHS (probe) substitutes; the RHS is a frozen literal target
    | .diag g φ,    _, _ => .diag g φ             -- FROZEN (like `.bot`/`.eq`-RHS): the diagonal is a closed meta-construction; subst does not descend
  termination_by structural f _ _ => f
end

-- Syntactic size = character count of source. This is the unit the proof system
-- measures budgets in: `□_k φ` means "φ has a proof of ≤ k characters", and a
-- proof's length is bounded in terms of the sizes of the formulas it manipulates.
-- A numeral `k` costs `Nat.log2 k + 1` characters (critch22 Appendix B(b):
-- numbers are written in `O(lg k)` characters), so e.g. `.search`/`.box` pay that
-- for their index. Everything else is `(sum of children) + 1` for the node.
/-- The character cost of writing the numeral `k` (Critch Appendix B(b): numbers are
    written in `O(lg k)` characters). Single source of truth for `Prog.size`,
    `Formula.size` and the proof-step cost `c_guard`. -/
def numCost (k : Nat) : Nat := Nat.log2 k + 1

mutual
  def Prog.size : Prog → Nat
    | .const _        => 1
    | .self           => 1
    | .opp            => 1
    | .bot p          => p.size + 1
    | .sim p q        => p.size + q.size + 1
    | .ite b _ p q    => b.size + p.size + q.size + 1
    | .search k φ p q => numCost k + φ.size + p.size + q.size + 1
    | .tsearch k gs θ p q => numCost k + numCost θ + gs.gsize + p.size + q.size + 1
    | .tvote v θ p q      => numCost θ + v.vsize + p.size + q.size + 1

  /-- Character count of an entry list: each entry pays its weight numeral, its instance
      program, and one separator character; the empty list is free (the node itself is
      charged by `.tvote`). Mirrors `GuardList.gsize`. -/
  def VoteList.vsize : VoteList → Nat
    | .nil           => 0
    | .cons w I rest => numCost w + I.size + rest.vsize + 1

  /-- Character count of a guard list: each entry pays its weight numeral, its formula,
      and one separator character; the empty list is free (the node itself is charged
      by `.tsearch`). -/
  def GuardList.gsize : GuardList → Nat
    | .nil           => 0
    | .cons w φ rest => numCost w + φ.size + rest.gsize + 1

  def Formula.size : Formula → Nat
    | .plays p q _ => p.size + q.size + 1
    | .impl φ ψ    => φ.size + ψ.size + 1
    | .neg φ       => φ.size + 1
    | .box k φ     => numCost k + φ.size + 1
    | .eq p q      => p.size + q.size + 1
    | .diag g φ    => numCost g + φ.size + 1   -- numeral cost for `g`, like `.box`
end

/-- Syntactic `.search`-freeness: a program that contains no proof-search node. A search-free
    pair's run never consults the oracle (`subst` cannot introduce a `.search` that isn't in one
    of its inputs — `hasSearch_subst`), so its play certificates are purely structural — the
    constructive fragment of the deleted `atom_complete` (see `atom_complete_searchfree`). -/
def Prog.hasSearch : Prog → Bool
  | .const _        => false
  | .self           => false
  | .opp            => false
  | .bot p          => p.hasSearch
  | .sim p q        => p.hasSearch || q.hasSearch
  | .ite b _ p q    => b.hasSearch || p.hasSearch || q.hasSearch
  | .search _ _ _ _ => true
  | .tsearch _ _ _ _ _ => true   -- consults the oracle, like `.search`
  -- UNCONDITIONALLY true, NOT a fold over the entries: a vote whose entries happened to
  -- be search-free would otherwise enter the search-free fragment and add a `.tvote`
  -- case to `atom_complete_searchfree` — for no benefit, since tau players are never
  -- census subjects and need no atom certificates. Conservative over-approximation
  -- (DEF4_TVOTE_ROADMAP.md §2).
  | .tvote _ _ _ _     => true

/-- Total weight carried by a guard list — the mass an all-fire run would accumulate.
    `θ > totalMass` means the threshold is unreachable (the else short-circuit). -/
def GuardList.totalMass : GuardList → Nat
  | .nil           => 0
  | .cons w _ rest => w + rest.totalMass

/-- Mass of the guards selected by a predicate on (closed) guard formulas. It is the sum of all weights
    where proofSearch returns true. Used for lemmas in the Meta theory.
    Instantiated with `fun φ => proofSearch k (φ.subst me opp)` in the
    tau-layer lemma statements; kept abstract here so Program.lean stays oracle-free. -/
def GuardList.massWhere (f : Formula → Bool) : GuardList → Nat
  | .nil           => 0
  | .cons w φ rest => (if f φ then w else 0) + rest.massWhere f

/-- Total weight carried by an entry list — the mass an all-cooperate signal would
    accumulate. `θ > totalMass` means the threshold is unreachable (the else
    short-circuit, `voteHigh_f`). -/
def VoteList.totalMass : VoteList → Nat
  | .nil           => 0
  | .cons w _ rest => w + rest.totalMass

/-- Mass of the entries selected by a predicate on (closed) instance programs: the sum of
    the weights whose entry plays `C`. Instantiated with `fun I => eval … I I I == some .C`
    in the tau-layer lemma statements; kept abstract here so `Program.lean` stays free of
    the evaluator. The action-valued twin of `GuardList.massWhere`. -/
def VoteList.massWhere (f : Prog → Bool) : VoteList → Nat
  | .nil           => 0
  | .cons w I rest => (if f I then w else 0) + rest.massWhere f

end PD
