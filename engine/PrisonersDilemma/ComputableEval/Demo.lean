import PrisonersDilemma.ComputableEval.Computable
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot

/-!
# `#eval` demo — *illustrating* the computability boundary (a figure, not the proof)

This file is an ILLUSTRATION, not the argument. The claim that the central evaluator
cannot be made totally computable is a fact about the *theory*, not our implementation,
and it is established elsewhere — NOT here:
  * the reflection argument: the Löb-fixpoint outcomes are reflected through
    `proofSearch_spec.2` and have no finite proof-search witness (Löb's theorem), so no
    terminating function can satisfy the existing `proofSearch_spec`; and
  * its machine-checked half, `DecMeasure.lean`, which refutes the naive well-founded
    measure (self-substituting a `.search` bot into its own guard *increases* depth).
That pair is what proves the limit is fundamental. The library's `eval`/`play`/`outcome`
stay `noncomputable` for that reason (their `.search` guard is the classical oracle
`proofSearch k φ := decide (Provable k φ)`).

What this file adds is only that the boundary is **constructively locatable**, by example.
`evalC`/`outcomeC` (Computable.lean) are a SOUND, total, **computable** *partial* evaluator
that runs here in the kernel via `#eval`. By `outcomeC_sound`, every `some _` answer below
is exactly the classical `outcome` — these kernel computations are theorems, not
coincidences — and on the PrudentBot↔DupocBot Löb fixpoint `outcomeC` returns `none`: it
refuses exactly at the fixpoint rather than giving a wrong answer. The cooperative `(C,C)`
for that matchup is the theorem `outcome_PrudentBot_vs_DupocBot`, established via the
bounded-Σ₁ reflection axioms (PBLT / `atom_box_provable_impl`) — not by computation.

This is a worked example of *where* bounded computation ends and modal reflection begins;
it does not, by itself, explain *why* — see the reflection argument and `DecMeasure.lean`.

NOTE on fuel/budget: `#eval` on search bots can be costly (the guard re-runs `evalC`), so
the search-bot demos below use small fuel and a modest budget `k`. The constant/mirror
matchups are cheap at any fuel.
-/

namespace PD.Demo
open PD PD.Bots

-- ### Constant- and reactive-bot matchups (cheap; agree with `eval`)

-- CooperateBot vs DefectBot → (C, D).
#eval outcomeC 50 CooperateBot DefectBot
-- DefectBot vs DefectBot → (D, D).
#eval outcomeC 50 DefectBot DefectBot
-- CooperateBot vs CooperateBot → (C, C).
#eval outcomeC 50 CooperateBot CooperateBot
-- MirrorBot vs CooperateBot → (C, C); vs DefectBot → (D, D).
#eval outcomeC 50 MirrorBot CooperateBot
#eval outcomeC 50 MirrorBot DefectBot
-- TitForTatBot vs CooperateBot → (C, C).
#eval outcomeC 50 TitForTatBot CooperateBot

-- ### Search bots on the finite-witness fragment (agree with `eval`)

-- DupocBot's cooperation search fires on a real cooperator: (C, C).
#eval outcomeC 10 (DupocBot 100) CooperateBot
-- …and is refuted by a defector: (D, D).
#eval outcomeC 10 (DupocBot 100) DefectBot

-- ### The Löb boundary (computation cannot witness it ⇒ `none`, honestly)

-- PrudentBot vs DupocBot: the modal fixpoint. `outcomeC` returns `none` — no finite
-- witness. The cooperative `(C, C)` is the *theorem* `outcome_PrudentBot_vs_DupocBot`,
-- not a computation. This `none` is the precise, intrinsic boundary (Löb's theorem).
#eval outcomeC 8 (PrudentBot 100) (DupocBot 100)

end PD.Demo
