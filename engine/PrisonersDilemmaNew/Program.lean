namespace PDNew

inductive Action
  | C
  | D
  deriving DecidableEq, Repr, BEq

abbrev Outcome := Action × Action

-- `Prog` is the language of agents from Critch 2022 (the Python-style
-- pseudocode). It is pure *source code*: no constructor produces an
-- `Action` directly — actions only appear after evaluation via `eval`
-- in Dynamics.lean. Keeping everything at the syntactic level is what lets agents be nested,
--  substituted, and passed as subjects of formulas.

-- `Formula` is the part of the proof system `S` that agents query through the oracle,just enough to
-- just enough to express hypotheses like `"opp(CUPOD_k.source) == D"`.

-- They are mutually recursive because `.search` carries a formula as
-- its guard, and a formula's `.plays` atom takes programs as subjects:
-- agents reason about agents reasoning about agents.

mutual
  inductive Prog where
    | const  : Action → Prog                      -- trivial bots like CB/DB: ignore opp, play a fixed action
    | self   : Prog                               -- placeholder for "my own source" — closed by `subst`
    | opp    : Prog                               -- placeholder for the opponent's source — closed by `subst`
    | sim    : Prog → Prog → Prog                 -- source code for "run p with q as opponent"
    | ite    : Prog → Action → Prog → Prog → Prog -- if evaluating guard yields action a, run p, else q
    | search : Nat → Formula → Prog → Prog → Prog -- proof_search(k, φ): if oracle verifies φ in ≤k chars, run p, else q
  inductive Formula where
    | plays : Prog → Prog → Action → Formula      -- atomic: "p(q.source) == a"
    | impl  : Formula → Formula → Formula         -- φ → ψ (needed for Löb-style hypotheses like □C → C)
    | neg   : Formula → Formula                   -- ¬ φ
    | box   : Nat → Formula → Formula             -- □_n φ: "φ is provable by the oracle with budget n"
end

-- Closing self-reference via substitution.
--
-- `.self` and `.opp` are *placeholders* (free variables) standing for
-- "my own source" and "the opponent's source" — the Python pseudocode's
-- `subst` walks replaces every `.self` with `me` and every `.opp` with `opponent`;


-- This matters because the oracle `proofSearch : Nat → Formula → Bool`
-- expects a *closed* formula — one with no free placeholders. So at every
-- evaluation boundary where a new context is entered (`.sim` and
-- `.search` in Dynamics.lean), the evaluator calls `subst` to freeze the
-- placeholders to the concrete programs currently playing the game.

-- The two definitions are mutually recursive for the same reason the
-- types are: `Prog.subst` descends into formulas at `.search`, and
-- `Formula.subst` descends into programs at `.plays`.

-- Note: `subst` is one-shot, not a fixed point. Placeholders inside the
-- freshly inserted `me`/`opponent` are *not* re-substituted — they remain
-- bound to whatever context will enclose them next.
mutual
  def Prog.subst : Prog → (me opponent : Prog) → Prog
    | .const a,        _, _ => .const a
    | .self,           m, _ => m
    | .opp,            _, o => o
    | .sim p q,        m, o => .sim (p.subst m o) (q.subst m o)
    | .ite b a p q,    m, o => .ite (b.subst m o) a (p.subst m o) (q.subst m o)
    | .search k φ p q, m, o => .search k (φ.subst m o) (p.subst m o) (q.subst m o)

  def Formula.subst : Formula → (me opponent : Prog) → Formula
    | .plays p q a, m, o => .plays (p.subst m o) (q.subst m o) a
    | .impl φ ψ,    m, o => .impl (φ.subst m o) (ψ.subst m o)
    | .neg φ,       m, o => .neg (φ.subst m o)
    | .box n φ,     m, o => .box n (φ.subst m o)
end

end PDNew
