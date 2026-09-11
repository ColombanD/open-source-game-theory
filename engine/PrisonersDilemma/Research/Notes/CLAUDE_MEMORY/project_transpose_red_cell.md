---
name: transpose-red-cell-proven
description: "The red cell (CupodBot, DupocBot) is PROVEN and PROMOTED into the library (Base/Transpose + Theorems/DupocBot/vs_CupodBot); stipulation deleted, critch8 fully proven"
metadata: 
  node_type: memory
  type: project
  originSessionId: 9f185fe3-3248-4615-8296-71602aa8ae1b
  modified: 2026-08-20T12:25:48.891Z
---

**PROMOTED 2026-08-20 (working tree only — user reviews+commits).** Library homes:
`Base/Transpose.lean` (τ̂ + the 47-arm `Pf.transpose`; in the BaseTheorems umbrella),
`Theorems/DupocBot/Helpers.lean` `-- CupodBot --` section (Prop 1.12 + determinism
clash + play lemmas), `Theorems/DupocBot/vs_CupodBot.lean` (ONE theorem
`outcome_DupocBot_vs_CupodBot = (D,C)` per the one-file-per-unordered-pair convention;
mirror + the audit differential tests live there as `example`s). Spike folder =
tombstone only (TOMBSTONES.md + README). App side, ATOMIC (the loader raises on a
stipulation shadowing a proven cell): red cell removed from `CUPOD_STIPULATIONS` →
critch8 zoo fully proven; `outcome_status.toml` entry dropped; EGT report prose
generalized; ~10 test sites updated. Promotion finds: (1) `test_every_named_zoo_loads`
conflated stipulations with superficial-standalone's CONTRADICTION cells (masked by
the red-cell stipulation) — invariant now counts both; (2) `llm_outcome_JustBot_vs_MirrorBot`
EXISTS — never use that pair as a "no theorem" fixture (use PrudentBot/CupodBot);
(3) `build_outcome_matrix` cells are keyed upper-triangular in zoo order (swapped
orientation keys ABSENT). Verified: `lake build` green (3330 jobs), 107 tau/matrix
tests + egt/def4 suites green, axioms 3-standard / `propext`-only.

**2026-08-19 — the red cell fell.** The spike (now tombstoned) mechanized `latex/Cupod_vs_Dupco_proof.tex`:

- `Pf.transpose : Pf k φ → Pf k φ.transpose` — 47-arm joint induction over the whole
  mutual block via raw `Pf.rec` (the sanctioned both-motives case). SAME budget: τ̂ is
  exactly size-preserving, so no `+c` splice. Axiom footprint: `propext` only.
- `outcome_DupocBot_vs_CupodBot k (fuel+2) = some (.D, .C)` and the `(C, D)` mirror —
  ALL k, same budget both sides, 3 standard axioms. Closes the cell Critch 2022 leaves
  open and the EGT `critch8` zoo STIPULATES; at promotion the stipulation can be deleted.

**Key design facts** (will bite anyone extending this):
1. τ̂ must FREEZE `VoteList` entries (like `subst` does): `.tvote` thresholds on C-mass,
   so descending into entries flips votes and kills `Pf`-invariance at `voteCons_*`.
   Vote certificates are reused verbatim in the induction.
2. The endgame needs NO floor/exclusion census: `□_k ρ₁ ↔ □_k ρ₂` (τ) + `Pf_sound` +
   `eval_det` gives the contradiction; both guards fail, both bots default.
3. Every paper hypothesis discharged: automorphism = the 47-arm closure; equal encoding
   length = exact (`size_transpose`); τ-equivariant encoding = `subst_transpose`;
   soundness = `Pf_sound`. The paper's final "unexploitability" step is redundant.
4. Any NEW `Pf` constructor must add a transposition arm — the induction breaks loudly.

Promotion path + watch items in the spike's README.md (per-pair files, root imports,
sheet sync, delete the critch8 stipulation, re-check Metatheory).

**AUDITED same day** (`AuditTests.lean` in the spike): kernel-`decide` non-triviality +
involution + Def-1.11 (`rfl` works); DIFFERENTIAL TEST — `Pf.transpose` maps
`dupoc_loeb_premise` ⟷ `cupod_loeb_premise` (two independently hand-proven library Löb
premises, both at transcript `5·log2 k + 33`) onto each other at the same budget, both
directions; zero conflicting pair claims library-wide; `outcome_status.toml` had the cell
open for "no forcing rule" — Pf.transpose IS the new forcing rule. One defect found &
fixed: README had overclaimed unprovability at K > k (mechanized scope is K ≤ k via
Pf_mono; ρ₁ is true and the K>k question is untouched). BOUNDARY: same-parameter pairs
only — staggered Dupoc(k₁)/Cupod(k₂) cells remain open (τ maps them to a different
matchup, no self-clash).

**Update 2026-08-25 — the red cell has TWO proofs, and base/tau share ONE census library.**
The base cell ALSO closes by the `search_f` floor with no transpose (`not_Pf_dupoc_guard_floor`/
`not_Pf_cupod_guard_floor`, `Theorems/DupocBot/Helpers.lean` — the tau argument verbatim: the
guard names the partner's ELSE-action, so `search_t` dies by `decide`, `search_f` pays `k`). Do
not re-ask "could the floor work in base" — yes, kernel-checked. The asymmetry was chronology
(bare else-floor census `no_provable_searcherElse_tail` landed 08-25, after the 08-20 transpose).
Epistemic scope (DESIGN_CHOICES.md 2026-08-25 entry): transpose = theorem about ANY sound τ-closed
deterministic formalization (transfers to Critch's PA agents) → the paper's theorem; floor = theorem
about `S` (constructor census + cost stipulation) → the tau workhorse (transpose is structurally
unavailable in tau: the `.sys` binder makes the pair one object). Agreement = corroboration.
Census unification commit `8de7fb0`: 7 tau shape-general censuses moved into `Base/Exclusion.lean`,
4 hand-rolled base censuses are now one-line instances, EDITION TABLE in the Exclusion header
(family × bare/.bot/.sys). Then the last hand-rolled one fell too: `no_provable_nestedSearcher_D_tail`
(bare nested-searcher D edition) with `no_provable_PrudentBot_D_tail` as its one-line instance. The `.bot` nested D/C editions (`no_provable_botNested_D_tail`/`_C_tail`) fill the shared column. TRAP:
the BARE nested-C census is FALSE as a `TailTo` statement — `searchChain` reads a bare searcher's
then-chain premise-free (`□g₁' → □g₂' → P plays C` is a TailTo formula; that is why
`no_provable_searcherPlay_tail` carries `hplug` as a hypothesis). Only the FROZEN/`.sys` C editions exist.
Table legend now: n/a (shape cannot arise in that layer) / ✗ (false, reason given) — no `—` left.
