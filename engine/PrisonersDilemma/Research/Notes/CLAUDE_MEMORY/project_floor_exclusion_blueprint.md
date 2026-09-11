---
name: project-floor-exclusion-blueprint
description: ¬Provable k for floor-killed pairs — Base/Exclusion census + generalized no_provable_probeFirst_C_tail; ALL SEVEN floor tombstones resolved (incl. same-k self-play (D,D))
metadata: 
  node_type: memory
  type: project
  originSessionId: 45e03dc3-6b3d-4188-b97e-57f9c3c1ed30
---

**The `search_f` floor is a formalized cost lower bound and ALL SIX floor tombstones
are resolved** (2026-07-09): `outcome_DupocBot_vs_DBot` (every budget),
`outcome_DupocBot_vs_EBot` (k ≥ 2), `outcome_PrudentBot_vs_EBot` (Löb threshold —
EBot's third probe rides `prudent_botmirror_coop`), `outcome_JustBot_vs_DBot` (every
budget), `outcome_JustBot_vs_EBot` (k ≥ 2) — all (D, C), searcher defects / simulator
cooperates — and `outcome_CupodBot_vs_OBot = (C, D)` (k ≥ 2): the defection-DETECTOR
exploited (OBot's real defection uncertifiable within Cupod's budget → sucker payoff).
JustBot pairs use the `_botOpp` variant (guard target = frozen `.bot (DupocBot k)`).
PLUS the same-k `outcome_PrudentBot_vs_PrudentBot = (D, D)` via the THIRD shape
`no_provable_searcherPlay_tail` (target = the searcher's OWN else-play; extra
hypotheses: branches not both const → census, inner then-action ≠ target →
searchThenSearch_t). The same-k retirements with staggered replacements
(PrudentBot×Dupoc, JustBot×Prudent, JustBot×CupodTroll) stand; their same-k DEFECTION
outcomes would need an ACTION-AWARE census (both-const searchers ARE readable, but
only their then-action plays) — optional. NO retired outcome remains unreplaced;
JustBot×MirrorBot stays open for semantic (bistable) reasons.

**The FREEZE TRICK (constructive converse)**: JustBot2 K k (search budget K decoupled
from the frozen snapshot .bot (DupocBot k); JustBot k = JustBot2 k k) —
outcome_JustBot2_vs_DBot = (C,C) at JustBot2 (2k+64) k, every k. The staggered
certificate provable_DBot_C_vs_botDupoc costs exactly k + log2 k + 26 (hand-built
PlaysProof term: ite_f ∘ sim ∘ bot ∘ search_f(atomNeg)). Design dichotomy (in
DESIGN_CHOICES.md): Löbian self-fulfillment (same tier, .self, cooperation facts only)
vs budget hierarchy over frozen proxies (any facts, proxy ≠ self spoofing surface).
.self guards cannot be tuned (one node one dial); freezing points strictly down.

**The blueprint** (fully generalized):
1. `Base/Exclusion.lean` — reusable: `rightTail` (implication spine tail), `ReadableMe`
   (the 5 bridge-readable player shapes), `tail_plays_readable` (the Derivation census:
   plays-atom spine tails only for readable players), `Formula.size_pos`, and
   `no_provable_probeFirst_tail` (+ `_botOpp` for .bot-wrapped searchers) — THE
   generalized floor bound: probe-first simulator `.ite (.sim .opp (.bot z)) aT p q`
   (test/branches fully general — the kill is at the guard cert both ite polarities
   carry, needs `hshape`: then-branch not a const-branched .search, for the census) vs
   budget-k searcher with a false probe-guard instance (`hfalse`). All six pairs are
   instances (the floor fires at the FIRST probe).
2. The proof: strong induction on budget (`Nat.strong_induction_on`),
   `cases` on `Provable`. Three kill mechanisms:
   - `struct` → census (bot shape not readable; DBot = `.ite` with `.const` then-branch);
   - `atom` → invert the `PlaysProof` replay down to the opponent's `.search`: `search_t`
     dies by SOUNDNESS (probe guard false), `search_f` by the floor summand `k` + omega;
   - `app`/`weakenImpl`/`implTrans`/`diagF`/`impS2` → recurse (premise budgets strictly
     smaller by transcript cumulativity + `Formula.size_pos`); all box/neg/diag-tailed
     constructors close by `simp at htail`.
   Crucially the non-cumulative budget citations (`search_t`, `searchThenSearch_t`) never
   enter the induction — killed semantically/shape-wise. That's why this works while the
   universal closure (arbitrary trees) stays open.

**Lean gotchas hit**: `cases hp with | app ...` — `app` has an EXPLICIT budget binder
and its conclusion indices (k, α) unify away; name all 8 constructor-order fields, the
unified ones just don't bind (naming them is harmless). Probe binder layouts with a
`trace_state` scratch file instead of guessing. Name clash: `proofSearch_false_for_DBot`
already existed in CupodBot.lean → mine is `proofSearch_false_for_DBot_vs_Dupoc`.

**Why the floor is optimal** (user asked; documented in
`Research/Notes/DESIGN_CHOICES.md`): consistency lower-bounds else-certs at > k
(anti-diagonal bot), we charge k+3 with every character accounted; literal verification
would cost exp(k) — we undercharge if anything. Σ₁/Π₁ asymmetry: success cites a witness
(c_guard = numCost), failure certifies absence (the floor) — bounded Gödel II.
