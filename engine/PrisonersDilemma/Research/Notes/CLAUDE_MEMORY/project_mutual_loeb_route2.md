---
name: project_mutual_loeb_route2
description: "DONE 2026-06-23 — the 3 cross-bot sorrys are CLOSED via the sound mutual-Löb axiom boxAtomLoeb. Full build green, no sorry. ONE new sound axiom. See body for the guard-inversion trick that dodges the atom_cost budget gap."
metadata: 
  node_type: memory
  type: project
  originSessionId: 8474ae12-a7c3-402f-8f5e-c8acd27c4c7b
---

## IMPLEMENTED 2026-06-23 — all three matchups CLOSED, build green, no sorry.

Final axiom = `boxInternalize` (Axioms.lean), at a SINGLE FIXED budget k, between
play-atoms: `(Provable k φ → Provable k α) → (size) → Provable k (□_k φ → □_k α)`.
Soundness `boxInternalize_sound` (BaseTheorems.lean): interp of `□_kφ→□_kα` is
DEFINITIONALLY the proof-transformer premise — proof is `:= hfitD`, tautological, deps =
only the 3 Lean-standard axioms. `mutual_loeb` derives `□_k φP → φP` = `boxInternalize ⊳
hfitD` (→ □_kφP→□_kφD) then `implTrans` with `legDP : □_k φD → φP`. NON-COLLAPSIBLE +
NOT FALSE: caller supplies hfitD only via guard inversion at a genuine two-bot fixpoint;
for a false atom (DefectBot plays C, machine-checked interp-false) no hfitD exists ⇒ inert.

NAMING: it is NOT GL axiom K. Real K has an OBJECT antecedent □(φ→ψ); this has a META
Lean proof-transformer and keeps the output box at k (no necessitation cost). Honestly
named `boxInternalize` after the user (rightly) pushed back on the "axiom K" label and on
fixing k. The faithful object-antecedent K is a DEAD END (spike `HonestKSpike.lean`): real
K is sound only with an EXISTENTIAL output box budget = cert cost, which can't be reconciled
to the k that PBLT + legDP force; bridging □_{cert}α → □_k α needs UNSOUND box-index
weakening. And separate K+4+necessitation don't compose (existential budgets b1/b3/b2 can't
align — `MutualLobSpike.lean`). So fixed-k is FORCED by the semantics (bot searches at its
own k, S3′), not a shortcut. Two prior drafts replaced: box4/boxMP pair, then fused
`boxAtomLoeb` — both superseded by `boxInternalize`.

**The trick that dodges the atom_cost budget gap:** `hfitD` is built NOT by completing the
φD play at `atom_cost n` (may exceed k), but via the GUARD INVERSION lemmas
(`ps_k_of_play_dupoc`, `ps_k_of_play_botdupoc`, inline for JustBot×Dupoc): a real φD play
⟹ the bot's search guard fired ⟹ `proofSearch k φP = true` = `Provable k φP` — AT BUDGET k.

`#print axioms`: the 3 theorems use propext/Classical.choice/Quot.sound + PBLT +
atom_complete_false_guard + boxAtomLoeb. `box_provable` NOT needed; unsound
`atom_box_provable_impl` gone. Files: Axioms.lean, BaseTheorems.lean, PrudentBot.lean
(loeb_premise_provable), JustBot.lean (prudent_botdupoc_loeb_premise + JustBot_vs_DupocBot).

DEAD-END (don't repeat): first attempt gave boxAtomLoeb a trivial `hcoop : Provable k α →
∃n,play=b` premise = just Provable_sound, satisfiable for ANY atom ⇒ free reflection ⇒ PBLT
proves DefectBot cooperates ⇒ UNSOUND. Fix: premise must be the LEGS, not the trivial fact.

---
## Original exploration (spike `MutualLobSpike.lean`):

The 3 `sorry`s (PrudentBot×DupocBot, JustBot×PrudentBot, JustBot×DupocBot) were ONE
hole: box-introduction `φP → □_k φP` on the unwitnessed cooperative atom at the Löb
fixpoint, formerly supplied by the removed-unsound `atom_box_provable_impl`.

**Explored 2026-06-23 (spike `Research/Spikes/MutualLobSpike.lean`, not root-imported).**
Colomban's idea: a MUTUAL Löb corollary `(□φD→φP) → (□φP→φD) → ∃m,Provable m (□φP→φP)`
(then PBLT strips the box). Findings, machine-checked:

- **Route 1 (chain bare outputs)**: FAILS — just RELOCATES the box-intro from φP to φD
  (implTrans cut needs `φD → □φD`, still a bare unwitnessed atom; `box_provable` demands
  `Provable k φD` = the fixpoint).
- **Route 2 (Critch's actual move)**: box the PROVED leg2 via `box_provable` (necessitation,
  sound — never boxes a bare atom), then distribute with object axiom-4 + axiom-K, then
  chain leg1. **`mutual_loeb_route2` COMPILES with no sorry** from `box_provable` + `ax4_obj`
  + `axK_obj`. The logical chain is REAL.

**The catch — soundness of the 2 needed object axioms:**
- `ax4_obj` (□φ→□□φ): = `box_provable` up to BUDGET INFLATION. Sound only with the budget
  EXISTENTIAL (`∃K`), not at a single fixed `a`. OK because PBLT's hypothesis is unbudgeted.
- `axK_obj` (□(φ→ψ)→(□φ→□ψ)): interp = `Provable a(φ→ψ)→Provable a φ→∃m,Provable m ψ`.
  Sound ONLY for ψ a play-ATOM (hypotheses force ψ.interp via Provable_sound, then
  `atom_complete` rebuilds `Provable _ ψ`). NOT a theorem for general ψ (incomplete direction).
  Provable as a theorem on the `.struct` fragment via `Derivation.modusPonens`.

**Verdict:** cross-bot fixpoints ARE soundly closable — but the honest cost is TWO new
sound axioms (budget-existential axiom-4 + atom-restricted axiom-K) replacing THREE
documented-open `sorry`s. Both are strictly safer than the removed `atom_box_provable_impl`
(never box a bare unwitnessed atom). Design call: is +2 sound axioms better than 3 open
sorrys? Not yet decided. If pursued: add `box4`+atom-restricted `boxMP` to Derivation.lean,
prove interp-soundness in BaseTheorems.lean, swap the chain in. Relates to
[[project_pblt_vs_constructive_lob]] (this is route A, faithful-axiom side — NOT the
refuted constructive boundedLob route B) and [[project_prudent_dupoc_gl4]].
