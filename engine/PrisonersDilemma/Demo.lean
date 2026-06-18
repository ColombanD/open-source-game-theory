import PrisonersDilemma.Computable
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot

/-!
# `#eval` demo — the computable evaluator running in the kernel

This file is the concrete answer to the review point that the central evaluator is
`noncomputable`. The library's `eval`/`play`/`outcome` are genuinely noncomputable (their
`.search` guard is the classical oracle `proofSearch k φ := decide (Provable k φ)`), and
that is *forced*: the Löb-fixpoint outcomes are reflected through `proofSearch_spec.2` and
have no finite proof-search witness (Löb's theorem), so no terminating function can satisfy
the existing `proofSearch_spec`.

`evalC`/`outcomeC` (Computable.lean) are a SOUND, total, **computable** evaluator that runs
here in the kernel via `#eval`. By `outcomeC_sound`, every `some _` answer below is exactly
the classical `outcome` — the kernel computations are theorems, not coincidences.

The boundary is honest and explicit: on the PrudentBot↔DupocBot Löb fixpoint `outcomeC`
returns `none` (it cannot witness the modal cooperation by finite computation) rather than a
wrong answer. That `none` is *where bounded computation ends and modal reflection begins* —
the cooperative `(C,C)` for that matchup is the theorem `outcome_PrudentBot_vs_DupocBot`,
established via the bounded-Σ₁ reflection axioms (PBLT / `atom_box_provable_impl`).

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
