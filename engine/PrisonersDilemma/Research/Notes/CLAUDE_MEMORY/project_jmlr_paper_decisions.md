---
name: jmlr-paper-decisions
description: JMLR paper — WRITING IN PROGRESS since 2026-09-01; fixed framing/scoping decisions and the agreed skeleton (Lean + Experiments sections)
metadata: 
  node_type: memory
  type: project
  originSessionId: ff357ffe-cc0f-4a7a-bfc5-6078caad5838
  modified: 2026-09-01T09:36:07.520Z
---

**Colomban is actively WRITING the JMLR paper** (drafting started 2026-09-01; structure fixed over 2026-08-31 feedback rounds; first content commits on `colomban-taubots`: intro notes on OSGT + a caveats section). Existing theory notes: `latex/Cupod_vs_Dupco_proof.tex` (Defs (S1)–(S4), τ-automorphism theorem, BoundedGL remark).

FIXED decisions (do not re-litigate):
1. **No incident-narrative framing in the body.** The cost floor is justified FORWARD and impersonally (forced by consistency + decidability + provable soundness); the `atom_complete_false_guard` story only in the appendix "Lessons" subsection, design-space register, never confession.
2. **Limitations and Conclusion section exists.** Lean obligations (PA model of BoundedGL, Solovay completeness, universal closure) AND experiment limitations (zoo dependence above all; payoff convention; tau-twin ceiling).
3. **LLM pipeline deliberately OUT OF SCOPE** — one-two provenance sentences in §5.1.2 (proofs drafted by Opus/Fable, judged by the kernel), nothing more.

Agreed skeleton highlights:
- **§3 Theory** owns: role of S, (S1)–(S4), Löb as the cooperation engine (Gödel/Löb + Pudlák/Parikh substance cited HERE); Dupoc-vs-Cupod pen-and-paper; transparency defs (bots/α/τ/σ) incl. the STATEMENT of Def 3 ≡ Def 4 as a claim with forward ref.
- **§4 Lean** opens with the trust-boundary half-page + dataflow figure (kernel-checked | Python-computed-from-JSON-exports | open; nothing stipulated). 4.1.1: Prog/Formula without `.tvote` (footnote), Dupoc running example, honest noncomputable-eval paragraph → appendix. 4.1.2 opens DIRECTLY at the design fork (arithmetized theory vs rule set; 2–3-sentence bridge on what a formalization must preserve), then: choice (BoundedGL = (S4) verbatim, Pf model by rfl, Löb/PBLT generic, zero axioms — BoundedGL appears ONLY here, not in the requirements beat), soundness (+ ValuationSoundness footnote, atom completeness AtomCerts), consequences (cumulative cost ← Pudlák payoff; floor forced ← Gödel payoff; Exclusion staggering/two-tier). 4.2 = Base/Transpose (47-arm, robustness = soundness+τ-closure only). 4.3 = Spec DSL → .tvote/inst → roster with stated exclusions → RowSpec rows; ConfidenceBot as "lifts are linear thresholds, max escapes" (confidence_not_linear).
- **Base/ file map**: body names BoundedGL, Soundness, Loeb, Exclusion, Transpose centrally; TowerCensus one sentence in 4.3.1; ValuationSoundness/AtomCerts footnote-level; Asymptotics/Closure/Helpers appendix table ONLY (with stated reasons).
- **§5 opener states: 5.1 is the boundary condition of 5.2** (full-transparency anchor = base matrix); write claims first, not procedures. 5.1.1 bot table BY FORMAL CLASS, zoos fixed once. 5.1.2 matrix figure legend (shared-budget cells, ⇄ staggered, †), design-consequence cells as explicit callback to 4.1.2. 5.1.3: coop rate = descriptive vs EGT = selective (corrects zoo-sensitivity); body reports Moran stochastic stability (+basins), stage catalog to appendix. 5.2.2 retitled as VALIDATION (Def3≡Def4 instance-wise over roster, never claim universal). 5.2.3 report per phase REGION; (t,α) phase diagram = centerpiece figure. 5.2.4 = the paper's destination (anchor → degradation of stochastically-stable set → α interaction). Comparability caveat (swept matrices never contain "N") in 5.2.1, recalled 5.2.4. "Aggregation operator" in appendix B must not collide with tau aggregator terminology.
- **Appendix**: A.1 executability/decidability (~1–1.5 pp, T31–T54 pointer), A.2 lessons (inconsistent axiom, CutRelevance, rejected Defs 1–2), A.3 Cupod/Dupoc correspondence table (statements not proofs), A.4 Base-file inventory; B: zoo/aggregation sensitivity, EGT stage catalog, (M,β) sweep, grid→matrix mapping, non-convergence stats.

Related: [[boundedgl-interface]], [[confidencebot-native-player]].
