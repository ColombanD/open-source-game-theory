namespace PDNew

inductive Action | C | D
  deriving DecidableEq, Repr, BEq

abbrev Outcome := Action × Action

-- `Prog` and `Formula` are mutually recursive: `.search` carries a
-- formula, and a formula can mention programs as its subjects.
mutual
  inductive Prog where
    | const  : Action → Prog -- constant program that always plays the same action
    | self   : Prog -- refers to the current program
    | opp    : Prog -- refers to the opponent program
    | sim    : Prog → Prog → Prog -- simulate one program against another
    | ite    : Prog → Action → Prog → Prog → Prog -- if a guard program returns action a, then run p else run q
    | search : Nat → Formula → Prog → Prog → Prog
-- Formula is the language of statements the oracle can reason about.
  inductive Formula where
    | plays : Prog → Prog → Action → Formula   -- "p(q.source) = a"
    | impl  : Formula → Formula → Formula -- "if φ then ψ"
    | neg   : Formula → Formula -- "not φ"
end

-- How to handle the self-reference.
-- Substitute `.self` / `.opp` in both programs and formulas. When a
-- `.search` fires we resolve its formula against the current agent
-- and opponent so that the oracle receives a closed statement.
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
end

end PDNew
