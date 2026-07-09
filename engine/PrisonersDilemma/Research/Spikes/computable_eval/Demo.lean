import PrisonersDilemma.Research.Spikes.computable_eval.Computable
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot

/-!
# `#eval` demo — *illustrating* the computability boundary (a figure, not the proof)

This file is an ILLUSTRATION, not the argument. The precise claim (see
`Research/Notes/COMPUTABLE_EVAL_NOTES.md`, corrected 2026-06-23) is: `eval` is computable
on the **finite fragment** (every non-self-referential matchup — `evalC` commits there) but
**not at the Löb fixpoints**, and that residue is NOT removable by making `S` explicit. The
reason is the **proof-vs-witness gap**, established elsewhere — NOT here:
  * a proof of bounded Löb (classical, or constructive à la Critch's diagonal lemma)
    establishes the fixpoint outcome is provable as an *existence* statement
    `∃ m, Provable m φ` — it does NOT exhibit a finite proof *term*. The guard search needs
    the term, so no terminating function satisfies the existing `proofSearch_spec` at the
    fixpoint; and
  * its machine-checked halves: `DecMeasure.lean` refutes the naive structural measure
    (self-substituting a `.search` bot into its own guard *increases* depth), and spikes
    S3/S3′ (`Research/Notes/CONSTRUCTIVE_BOUNDED_LOB.md`) refute the budget-recursion /
    term-builder route — the witness it would need is `Provable k φ` at the same budget `k`
    the bot searches.
That is why the limit is permanent (though NOT a Gödel/Π₁ wall — the finite fragment is
genuinely decidable). The library's `eval`/`play`/`outcome` stay `noncomputable` for that
reason (their `.search` guard is the classical oracle `proofSearch k φ := decide (Provable
k φ)`).

What this file adds is only that the boundary is **constructively locatable**, by example.
`evalC`/`outcomeC` (Computable.lean) are a SOUND, total, **computable** *partial* evaluator
that runs here in the kernel via `#eval`. By `outcomeC_sound`, every `some _` answer below
is exactly the classical `outcome` — these kernel computations are theorems, not
coincidences — and on the PrudentBot↔DupocBot Löb fixpoint `outcomeC` returns `none`: it
refuses exactly at the fixpoint rather than giving a wrong answer. The cooperative `(C,C)`
for that matchup is the theorem `outcome_PrudentBot_vs_DupocBot`, established via the
bounded-Σ₁ reflection axioms (PBLT / `atom_box_provable_impl`) — not by computation.

This is a worked example of *where* bounded computation ends and modal reflection begins;
it does not, by itself, explain *why* — see the proof-vs-witness argument above,
`DecMeasure.lean`, and the S3/S3′ spikes.

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
