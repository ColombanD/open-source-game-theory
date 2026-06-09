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
  inductive Prog where
    | const  : Action → Prog                      -- trivial bots like CB/DB: ignore opp, play a fixed action
    | self   : Prog                               -- placeholder for "my own source" — closed by `subst`
    | opp    : Prog                               -- placeholder for the opponent's source — closed by `subst`
    | bot    : Prog → Prog                        -- closed bot reference; `subst` does not descend
    | sim    : Prog → Prog → Prog                 -- source code for "run p with q as opponent"
    | ite    : Prog → Action → Prog → Prog → Prog -- if evaluating guard yields action a, run p, else q
    | search : Nat → Formula → Prog → Prog → Prog -- proof_search(k, φ): if oracle verifies φ in ≤k chars, run p, else q
  inductive Formula where
    | plays : Prog → Prog → Action → Formula      -- atomic: "p(q.source) == a"
    | impl  : Formula → Formula → Formula         -- φ → ψ (needed for Löb-style hypotheses like □C → C)
    | neg   : Formula → Formula                   -- ¬ φ
    | box   : Nat → Formula → Formula             -- □_n φ: "φ is provable by the oracle with budget n"
    | eq    : Prog → Prog → Formula               -- structural identity: "p and q are the same program"
end

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

  def Formula.subst : Formula → (me opponent : Prog) → Formula
    | .plays p q a, m, o => .plays (p.subst m o) (q.subst m o) a
    | .impl φ ψ,    m, o => .impl (φ.subst m o) (ψ.subst m o)
    | .neg φ,       m, o => .neg (φ.subst m o)
    | .box n φ,     m, o => .box n (φ.subst m o)
    | .eq p q,      m, o => .eq (p.subst m o) (q.subst m o)
end

-- Syntactic size = character count of source. This is the unit the proof system
-- measures budgets in: `□_k φ` means "φ has a proof of ≤ k characters", and a
-- proof's length is bounded in terms of the sizes of the formulas it manipulates.
-- A numeral `k` costs `Nat.log2 k + 1` characters (critch22 Appendix B(b):
-- numbers are written in `O(lg k)` characters), so e.g. `.search`/`.box` pay that
-- for their index. Everything else is `(sum of children) + 1` for the node.
mutual
  def Prog.size : Prog → Nat
    | .const _        => 1
    | .self           => 1
    | .opp            => 1
    | .bot p          => p.size + 1
    | .sim p q        => p.size + q.size + 1
    | .ite b _ p q    => b.size + p.size + q.size + 1
    | .search k φ p q => (Nat.log2 k + 1) + φ.size + p.size + q.size + 1

  def Formula.size : Formula → Nat
    | .plays p q _ => p.size + q.size + 1
    | .impl φ ψ    => φ.size + ψ.size + 1
    | .neg φ       => φ.size + 1
    | .box k φ     => (Nat.log2 k + 1) + φ.size + 1
    | .eq p q      => p.size + q.size + 1
end

end PD
