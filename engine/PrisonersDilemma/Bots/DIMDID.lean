import PrisonersDilemma.Program

open PD

namespace PD.Bots

/-- DIMDID: Defect If My Defection Implies Defection — "defect only when defection is provably
    reciprocated". It is the C/D transposition `τ̂` of `CIMCIC` (`Base/Transpose.lean`):
    `(CIMCIC k).transpose = DIMDID k` by `rfl`, so every transposition theorem about CIMCIC
    speaks about it. Uses the proof oracle to check whether "if I defect, the opponent defects"
    is derivable within budget `k` (`⊢_k`); if so, defect, otherwise cooperate. Its PA-`S'` row is
    `arith/ArithS/Cells/Dimdid.lean` (2026-10-13). -/
def DIMDID (k : Nat) : Prog :=
  .search k
    (.impl (.plays .self .opp Action.D) (.plays .opp .self Action.D))
    (.const Action.D)
    (.const Action.C)

end PD.Bots
