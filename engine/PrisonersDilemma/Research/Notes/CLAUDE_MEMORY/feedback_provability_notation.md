---
name: provability-notation-convention
description: "Fixed 2026-09-04 — ⊢_k φ = Pf k φ (S, object), ⊨ φ = φ.interp (truth), meta = prose only; never a turnstile for Lean"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 69b34809-b4d6-4695-8498-835f8a9e742b
  modified: 2026-09-04T13:03:38.258Z
---

Three levels, three notations (note: `engine/PrisonersDilemma/Research/Notes/PROVABILITY_NOTATION.md`):
`⊢_k φ` is `Pf k φ` (S derives φ at budget k; unsubscripted = ∃k); `⊨ φ` is `φ.interp`;
the meta level (Lean, "we show", "theorem") gets NO symbol. `⊢` always means S, never Lean.
`⊨ □_k φ ≡ ⊢_k φ` by definition of interp. Soundness `sound_upto` reads `⊢_k φ ⟹ ⊨ φ`,
a Lean theorem about S. Three distinct negations: `¬⊢_k φ` (meta, the floor censuses),
`⊢_k ¬φ` (S refutes), `⊢ ¬□_k φ` (internal). In Lean comments a goal is written `goal:`,
not `⊢`; the tactic goal marker (`at h ⊢`) is untouched.

**Why:** Colomban asked whether S is Lean's meta layer; it is not, and prose saying
"provable"/"true" without naming the level had blurred it (e.g. the proof-agent prompt
used "unprovable" for both a Lean outcome theorem and an S guard).

**How to apply:** in any comment, note, prompt or paper text, name the level: "S derives
(`⊢_k`)", "`⊨`", or "a Lean theorem". "Unprovable" means `¬⊢_k φ`, never "false".
See [[jmlr-paper-decisions]] (trust boundary §4) and [[computable-eval-routeii]].
