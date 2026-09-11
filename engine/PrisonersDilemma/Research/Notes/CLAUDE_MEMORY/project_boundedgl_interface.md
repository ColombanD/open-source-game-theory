---
name: project-boundedgl-interface
description: "Base/BoundedGL (2026-08-27) — the abstract bounded-GL interface landed on branch colomban-bounded-gl; Pf is a model by rfl, bloeb/pblt generic; Zulip exchange with Foundation; Metatheory target pre-broken"
metadata: 
  node_type: memory
  type: project
  originSessionId: 08e0b1bc-7161-43ab-b866-ee4becf88bde
  modified: 2026-08-27T09:51:42.418Z
---

2026-08-27: `engine/PrisonersDilemma/Base/BoundedGL.lean` landed on the NEW branch
`colomban-bounded-gl` (cut from `colomban-taubots`; 4 commits e0be2a2..c8b2527; MERGED into
colomban-taubots 2026-08-31, build green with ConfidenceBot, 17/17 tau rows; not pushed). `structure BoundedGL (Sent)` = 10 costed modal/glue
schemes (`mono mp implTrans impS2 boxIntro axKf box4 boxMono diagF diagB`) + `SizeExact`
mixin; `pfBoundedGL` discharges every field by the same-named `Pf` constructor;
`BoundedGL.mutual_loeb/bloeb/pblt/pblt_bounded` are `Base/Loeb`'s theorems proved
generically, engine versions are instances by `rfl`. Spike kept at
`Research/Spikes/bounded_gl/` with `#print axioms`. `Pf` untouched.

Provenance: Zulip #Formalized Formal Logic (web-public), 2026-08-27 — Palalansoukî
("these abstract formalizations seem legitimate"; suggested "GL with proof-length-bounded
modalities" over a `ProvabilityAbstraction.Provability` variant), SnO₂WMaN (agreed,
suggested separate repo). Foundation's only bounded object is `RestrictedProvability`
(`∃ d < 2^e`, restricted Gödel sentence + lower bound; no bounded HBL/Löb).

**Why:** the user wanted the "interface formalization" middle path (DESIGN_CHOICES
2026-08-20 row) done cheaply after the Zulip validation; the user chose generic-over-Sent,
model + bloeb + pblt scope, and paper edits included ((S4) of `latex/Cupod_vs_Dupco_proof.tex`
+ a remark).

**How to apply:** don't refactor `Pf` to consume it; size laws must stay EXACT equations
(inequalities break `omega` in the PBLT wrapper); keep the Löb-premise gate on `diagF/diagB`
(load-bearing for `Base/Exclusion` censuses). Candidate second model: Metatheory's `ProvT`.
Leads before claiming novelty: Verbrugge feasible provability logic, Parikh 1971, Artemov LP.

Also learned: `lake build Metatheory` is BROKEN independently of this work —
`Decidability.lean` has its module docstring BEFORE the imports ("invalid 'import'
command"), since b2ff4ee; the lakefile comment "still explicitly buildable" is stale.
And the real `Pf` constructor count is 33 (fixed in CLAUDE.md and Base/Closure header).
See [[project-transpose-red-cell]], [[project-outcome-template-export]].
