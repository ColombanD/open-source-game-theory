---
name: project_atom_complete_false_guard_removal
description: "Plan + Change-1 spike (PASSED) to remove the Π₁ axiom atom_complete_false_guard; bounded guard is decidable, fixpoint-free unlike the Löb true-branch"
metadata: 
  node_type: memory
  type: project
  originSessionId: 21d435ac-0ba4-40a8-a623-8231c525b105
---

**⚠️⚠️ SUPERSEDING UPDATE 2026-07-02: the axiom is INCONSISTENT — machine-checked False.**
`Research/Spikes/transcript/T32Inconsistency.lean` (`engine_inconsistent : False`, on 3 std
axioms + this one). Witness: anti-diagonal bot `G := .search 100 (.plays .self .self .D)
(.const .C) (.const .D)` — the axiom injects G's else-cert at atom_cost 2 = 7, atom_monotone
lifts it above the guard budget (100), flipping the guard; guard-true side contradicts
soundness. So "irreducible & load-bearing" below is now "irreducible & FALSE": every theorem
whose #print axioms lists it (all atom_complete users, PrudentBot/JustBot outcomes) is VACUOUS.
Predates the transcript refactor. Repair = the CHARGED atom model (DECIDABILITY_ROADMAP T3.2):
then-certs pay the guard proof's transcript (possible post-PBLT-internalization), else-certs
must EXCEED the guard budget they refute; search_f via a stratified pre-defined decider
(naive self-referential D is a non-monotone fixpoint — this bot is its paradox).

**T3.2a STEP 1 SHIPPED (2026-07-02, commit 3d02e00, build green):** `PlaysProof.search_f`
(REFUTATION premise `Provable m (.neg guard)` + cost FLOOR pays full failed budget k) +
`Provable.atomNeg` (refute play-atom from cert of actual play, eval determinism); soundness
rebuilt as `sound_upto` (STRONG INDUCTION ON BUDGET — floor makes the hypothetical guard proof
strictly smaller); Exclusion no_pp_else/no_provable_forbidden COST-QUALIFIED (≤ guard budget).
Axiom still present; **STEP 2 (deletion) is NOT mechanical — outcome theorems CHANGE**: bots
consuming another bot's else-play within the same budget (DBot/OBot/EBot probes of Dupoc;
PrudentBot×Dupoc & JustBot prudence) lose same-k cooperation — need staggered budgets
(Critch-faithful) or a new refutation-transparency Derivation rule. Search-free-probe results
survive. Colomban chose STAGGERED BUDGETS.

**⚑ STEP 2 SHIPPED (2026-07-03, commit f146671): THE AXIOM IS DELETED — ZERO PROJECT AXIOMS,
build green.** Every surviving theorem on [propext, Classical.choice, Quot.sound] only.
NEW Derivation.eqNeg; atom_complete deleted → constructive toolkit (atom_complete_searchfree
3^fuel; atom_search_t_top log2k+3; atom_search_f_top floor m+k+2); decGuard true-commits
restricted to search-free. SURVIVORS (hand-certified): Dupoc/Cupod self+const/sim/TFT/OBot,
Prudent×Mirror (consts 27/81), JustBot self/TFT/OBot/Dupoc, CupodTroll×Cupod, CupodTroll×Dupoc
STAGGERED (first staggered thm, eqNeg+search_f cert). RETIRED (self-referential floor, honest):
Dupoc×{DBot,EBot}, Cupod×OBot, Prudent×{EBot,Dupoc,SELF}, JustBot×{DBot,Troll,EBot,Prudent} —
same-k prudence is self-referentially impossible (= why MIRI PrudentBot uses PA+1). **T3.2b CORE SHIPPED (2026-07-03, commit 3830cd0):** PrudentBot(2k+64)×DupocBot(k) and
JustBot(k)×PrudentBot(2k+64) → (C,C) RECOVERED via mutual_pblt_engine_staggered (two-budget
wrapper) + floored prudence certs (prudence_dupoc k+log2k+15, prudence_botdupoc +17,
justbot_prudence +16 — all search_f-over-atomNeg). KEY: searchThenSearch_t now CITES its
inner search (c_guard k₂) instead of charging the premise — Critch-faithful like search_t;
staggering still forced through the m ≤ k₂ gate. **T3.2b TAIL SHIPPED (2026-07-03, commit 3223d7a):** PrudentBot2 (kOut kIn) two-tier bot
(bounded PA+1) + outcome_PrudentBot2_self (k, 4k+100) → (C,C); outcome_JustBot_vs_CupodTrollBot
(JustBot (4j+100) vs Troll j, ∀j no eventuality); log2_stagger4_le; CLAUDE.md + Derivation.lean
headers refreshed (zero axioms). Remaining T3.2b: honest (D,C) outcomes for retired probes
(need ¬Provable side — Exclusion-style or the decider). **T3.2c PART 1 SHIPPED (2026-07-03, commit b8815cf):** T31EngineDecider spike repaired
(eqNeg/atomNeg/STS-cite) + upgraded: decProv covers all 16 rules; decProv_mono (fuel
monotonicity); decProv_complete in ∃-FUEL form (∀-fuel≥K is IMPOSSIBLE under the cite model —
inner premises at source literals unbounded by conclusion budgets; that's the precise residual
of decidability); **decProv_iff: Provable k φ ↔ ∃ fuel, decProv O fuel k φ = true** given
OracleSound+Complete — semidecidability relative to the atom layer, computable enumerator.
Remaining: atom-side enumerator (absolute semidecidability), then the OPEN fuel-bound /
query-universe-finiteness question (full decidability → proofSearch := D → computable eval).

The Π₁ axiom `atom_complete_false_guard` (`Axioms.lean:64`) is **removable** — unlike the
Löb-fixpoint noncomputability (`[[project_computable_eval_routeii]]`, settled negative). Why
the boundedness lever cuts the OTHER way here: the false guard certifies `¬ Provable k (guard)`,
a *negation* over a FINITE proof space ⇒ decidable by enumeration; AND the guard carries no Löb
fixpoint (CUPOD's guard self-references the SIBLING atom `CUPOD plays D`, not the cooperation
`CUPOD plays C` being certified — no same-budget `k'=k` cycle, contrast `CONSTRUCTIVE_BOUNDED_LOB.md`
S3′). CUPOD true-branch (defection) stays `PBLT`; false-branch (cooperation) is the eliminable one.

⚠️ **2026-06-26 COURSE CORRECTION — landing the axiom removal is BLOCKED at current architecture
(machine-grounded, `Research/Spikes/SearchFFeasibilitySpike.lean`).** The original 4-change plan's
`search_f` constructor CANNOT be added soundly: (1) guard-false premise is load-bearing (dropping
it is unsound — could certify else-play when guard TRUE); (2) `¬ Provable k guard` is
kernel-NON-POSITIVE inside the PlaysProof/Provable mutual block (probed: "non positive occurrence");
(3) the mutual recursion is GENUINE — `PlaysProof.search_t` carries `Provable k (φ.subst)` as
premise (Derivation.lean:242), so `proofSearch`/`Provable` CANNOT precede `PlaysProof`; no ordering
puts a positive `proofSearch=false` premise before `PlaysProof`. A free `Bool gbool=false` IS
kernel-accepted but UNSOUND standalone (nothing ties gbool to the actual guard provability; the tie
= the Π₁ content, can't live in the block). **SAME wall family as the noncomputable-eval crux.**
Honest routes: (a) Phase 0 size-INDEX Derivation/PlaysProof; or (b) keep axiom but downgrade/restate
via the spike's Decidable instance.

⚠️ **2026-06-26 SECOND CORRECTION (SizeIndexSpike.lean, machine-checked) — "size-index makes search_f
a legal constructor" is FALSE.** Two kernel rejections: (A) ¬Prov inside mutual block — REJECTED;
(B) ¬PP with PP defined ALONE + size-indexed — ALSO REJECTED ("non positive occurrence"). **The real
blocker is SELF-NEGATION, not mutual-ness and not the missing size index.** An inductive can NEVER
carry the negation of itself. So search_f-AS-A-CONSTRUCTOR is impossible, period — size-indexing does
not change it. What size-indexing ACTUALLY buys: the DERIVED predicate PP_finite k body a := ∃ s≤k,
PP body a s is finitely DECIDABLE; the false-guard fact ¬PP_finite then lives as a POST-HOC
AtomProvable-level THEOREM (the atom_complete else-branch), premise decidable instead of axiom.
**Axiom discharged at the THEOREM layer, NOT by a new constructor.** Refactor still worth it but
deliverable = "decidable PP_finite ⇒ constructive atom_complete else-branch", NOT "add search_f".
500-ref cost stands; the false-guard lives outside the inductive, decidably (negation can't be a
brick of its own box).

**Q2 SPIKED & PASSED (2026-06-26, SizeIndexSpike.lean) — decidability of PP_finite is REAL.** Lever
(vs DecMeasure's refuted program-recursion): track proof SIZE via `ppSize : Nat→Prog→Action→Option
Nat` (minimal size, fuelled), recurse structurally. `ppSize_sound` (some s→PP body a s exact),
`ppSize_mono` (more fuel preserves size), `ppSize_complete` (PP body a s → ppSize (s+1)=some s — KEY:
fuel ≤ size+1, so size index BOUNDS the search, fixed fuel k+1 decides PP_finite k), `ppFinite_iff`
(PP_finite k ↔ ∃s, ppSize(k+1)=some s ∧ s≤k), `instDecPPFinite` Decidable instance **#print axioms =
[propext, Quot.sound]** (NO Classical.choice, NO sorryAx) — and it RUNS (#eval: PP_finite 3 (const C)
C = true, …D = false). `¬PP_finite` Decidable by inferInstance = the positive non-axiom premise
atom_complete else-branch needs.

**DE-RISK VERDICT: refactor crux is GREEN on the toy.** Q1: search_f-as-constructor impossible
(self-negation) but NOT needed. Q2: size-indexed Provable_finite genuinely computably decidable.
Mechanism CONFIRMED viable: size-index real Derivation/PlaysProof, port ppSize+3 lemmas to the real
(8-constructor) inductive, re-prove atom_complete else-branch via ¬Provable_finite. Remaining risk =
ENGINEERING SCALE (real PlaysProof has .sim/.ite/.bot subst + search_t's Provable-premise / the
genuine Provable<->AtomProvable mutual structure, vs toy's single guard shape), NOT a foundational
wall. Toy proves the SHAPE works end-to-end incl decidability. Next if pursued: the full size-index
refactor (~500 refs, long red-build valley) — but now de-risked, mechanism known, payoff confirmed.

**PHASE A SPIKED & PASSED (2026-06-26, PortPhaseASpike.lean) — ppSize on the REAL PlaysProof.** All
8 arms (const/self/opp/bot/sim/ite_t+f/search_t) with real cost model (c_leaf/c_node/c_guard k) +
full ppSize_sound. Clean, NO sorry/Classical, #print axioms = [propext, Quot.sound]. **The RISKY
search_t arm WORKS:** guard's `Provable k (φ.subst me opp)` premise reconstructed via `Provable.atom
(AtomProvable.mk hguard_pp hsgk)` — hguard_pp from recursive ppSize on the guard ATOM (subject vs
target, body=subject, matching AtomProvable.mk's `PlaysProof me opp me a n` shape), hsgk=`sg ≤ k`
budget gate. Non-atom guards (impl/box/neg/eq) → none (correct: struct/reflection/axiom/fixpoint
cases, no finite cert). ppSize NEVER touches non-decidable Provable reflection rules — only rebuilds
Provable.atom (the decidable fragment). Cost index `n + c_guard k + c_node` matches real search_t
exactly; guard's own size sg NOT in total (lives in budget k). **Single riskiest port piece = GREEN.**
**PHASE B PASSED (2026-06-26, PortPhaseASpike.lean, honest scope) — sorry-free.** Ported the proven
DecidableFiniteSpike chain to REAL types: `plays_det` (engine LACKED play determinism; via
playsProof_sound + eval_mono_le), `ppSize_no_false` (soundness+determinism), `ppSize_mono_lift`
(fuel-lift ≤-cost; .ite non-monotonicity killed by no_false; search_t arm lifts guard+then with
c_guard-aware cost) [propext,Classical.choice,Quot.sound], `ppSize_search_complete` (the NEW content:
search_t completeness reconstruction, cost ≤ n+c_guard k+c_node matching real index, CONDITIONAL on
guard+then witnesses) [propext], `atomFinite_iff` + worked Decidable instance that COMPUTES (#eval
ppSize 5 (.const C)… = some 1) [propext,Quot.sound]. **HONEST SCOPE:** full ppSize_complete over the
whole PlaysProof.rec needs threading guard-provability through Provable's reflection rules
(weakenImpl/searchThenSearch_t/implTrans/atomBoxImpl — NOT finitely decidable, out-of-scope
fixpoint/reflection), so atomFinite_iff carries the completeness bound as hypothesis complete_bound
scoped to atom-realized fragment; soundness unconditional. The c_guard-aware cost ASSEMBLY (load-bearing
de-risk) fully proven; only reflection recursion excluded by design.

**PHASE C BLOCKED (2026-06-26, SearchFFeasibilitySpike §5 addendum, machine-grounded).** Tried to USE
ppSize to drop the axiom in atom_complete. Result: BLOCKED. (1) atom_complete else-branch
(BaseTheorems.lean:38) must BUILD AtomProvable exactly where NO PlaysProof exists (false-guard plays,
eval ran else-body q b/c proofSearch=false). AtomProvable.mk needs a PlaysProof → cert can't be built.
(2) Derivation.lean imports ONLY Program; eval/play/proofSearch are in Dynamics.lean (imports
Derivation, reverse). So the PlaysProof/AtomProvable/Provable mutual block has NEITHER proofSearch NOR
play — a false-guard premise must be Program-only. (3) Candidate AtomProvable.search_f carrying a
PlaysProof of the ELSE-BODY q + (gbool:Bool, gbool=false) IS kernel-accepted (probed) but UNSOUND
standalone — nothing ties gbool to the guard failing, would certify else-play when guard TRUE. The tie
gbool=proofSearch k guard is the Π₁ content, inexpressible in-block.

**FINAL VERDICT (across SearchFFeasibility+SizeIndex+PortPhaseA):** removing the axiom is BLOCKED at
current architecture; NOT liftable by size-indexing alone (self-negation) NOR by redefining AtomProvable
(guard-tie inexpressible in Program-only block). Full removal needs breaking the
PlaysProof↔Provable↔proofSearch cyclic dependency (define a size-indexed proofSearch-free
bounded-provability predicate BEFORE the cert type — beyond Phase 0). ppSize (PortPhaseA, GREEN,
computes, sound) PROVES the false-guard fact DECIDABLE — but a decidable Prop ≠ a constructor.

**Call-site survey (2026-06-26) FALSIFIED the "axiom is inert" claim.** ≈5 GENUINE false-guard plays
route through the axiom: a .search-bot playing its ELSE action — PrudentBot plays D vs .bot DefectBot
(prudence_self_prudent, PrudentBot.lean:1135), JustBot plays D vs .bot DefectBot, CupodTrollBot plays C
vs DupocBot/.bot DupocBot, DupocBot plays D vs .bot DefectBot. They feed real cross-bot outcomes. **So
option (b) RESTRICT is NOT viable — it would BREAK these 5 theorems** (no other way to certify them;
search_f impossible). The axiom is LOAD-BEARING.

**OPTION (a) LANDED (2026-06-26) — build GREEN.** New engine module `ComputableEval/PlaysCheck.lean`
(root-imported, lake build 3143 jobs green): `ppSize` (computable sound decider for bounded
play-certificate, real PlaysProof 8-arm + cost model) + `ppSize_sound` [propext,Quot.sound], `plays_det`
(play determinism, engine LACKED it), `AtomFinite` + `decAtomFiniteCheck` (genuine Decidable instance,
[propext], COMPUTES: #eval ppSize 5 (.const C)… = some 1), `check_sound`, `eval_search_false`
(eval-trace bridge: proofSearch=false ⇒ else-branch play). NONE depend on atom_complete_false_guard
(module independent). Axiom RETAINED (count still 4) but DOC DOWNGRADED in Axioms.lean: from
"witness-free/inert" → "LOAD-BEARING + DECIDABLE-but-uncarried"; documents the cyclic-dependency boundary
(PlaysProof↔Provable↔proofSearch) + points to the 4 spikes + PlaysCheck. **Net: axiom honestly reframed
as a decidable fact the architecture can't yet carry, with the computable witness shipped in-engine.**
Full removal still needs breaking the cyclic dependency (define size-indexed proofSearch-free
bounded-provability predicate before the cert type) — beyond Phase 0; documented, not done.

⚠️ **2026-06-26 CYCLE-BREAK ATTEMPTED & TWO-WALL RESULT (plan dazzling-coalescing-rivest, build
GREEN throughout).** Did the cycle-break for real: relocated `ppSize`/`otherAction`/`Provable_fin`
(decidable, proofSearch-free finite-provability predicate) + `instDecProvableFin` into Derivation.lean
BEFORE the PlaysProof/Provable mutual block; `provableFin_sound`/`ppSize_sound` after (PlaysCheck.lean).
Step-0 spike (ProvableFinSpike.lean) confirmed: Provable_fin decidable [propext], false at CUPOD
fixpoint (native_decide), agrees with Provable ([propext,Quot.sound]), and a search_f-shaped
constructor carrying `decide(Provable_fin)=false` TYPECHECKS.

**WALL 1 (positivity) — LIFTED:** with Provable_fin before the block, `search_f` carrying
`decide(Provable_fin k guard)=false` is kernel-POSITIVE and typechecks in the REAL PlaysProof
(verified transiently). The self-negation wall is gone.

**WALL 2 (soundness) — NOT LIFTED, the deeper boundary:** search_f is still UNSOUND. playsProof_sound
must discharge EVERY search_f cert, needing `proofSearch k guard=false` (eval-exact). But
`Provable_fin=false` does NOT imply `proofSearch=false` — at a Löb fixpoint Provable_fin=false while
proofSearch=Provable is PBLT-axiom-TRUE. And eval CANNOT be rewired to use Provable_fin — PBLT
cooperations (CupodBot.lean:112) need proofSearch=TRUE at the fixpoint guard. So the sound premise is
the Π₁ `¬Provable k guard`, irreducibly non-positive in-block. Verified by filling playsProof_sound's
search_f case → goal is exactly "eval runs else-branch" needing proofSearch=false, unprovable from
Provable_fin=false. REVERTED search_f; KEPT Provable_fin/ppSize/instDecProvableFin/provableFin_sound
as in-engine assets. Axiom stays 4, doc updated with the TWO-WALL finding.

**Wall-2 VERDICT (pre-exclusion):** removal entangled with PBLT — premise coincides with
proofSearch=false only off-fixpoints. Cycle-break lifts Wall 1, not Wall 2.

⚠️ **2026-06-26 EXCLUSION LEMMA — the DEFINITIVE, DEEPEST result (ExclusionSpike.lean, [propext]
only, NO dep on atom_complete_false_guard).** User idea: prove the false-guard else-play is
Provable_fin-exact (no fixpoint path). PROVEN, but it EXPLAINS the axiom rather than removing it:
- `no_deriv_else` (induction on Derivation, `Forbidden` motive): NO Derivation concludes a
  .search-bot's ELSE-action `.plays meS opp aE` (meS=.search k ψ (.const aT)(.const aE), aT≠aE).
  modusPonens/hypSyll recurse; source-transparency rules (searchBranch etc.) conclude the THEN-action
  aT, contradiction.
- `provable_else_isAtom`: Provable k (else-play) ⟹ AtomProvable (struct excluded by no_deriv_else;
  reflection rules conclude .impl; only atom survives; PBLT/boxInternalize assert Provable terms but
  every inhabitant IS a constructor app, all excluded but atom).
- **KEY:** AtomProvable.mk needs PlaysProof meS opp meS aE n — DOES NOT EXIST (search_t, the only
  .search rule, concludes THEN-action aT not aE). So the else-play's CERTIFICATE TYPE IS PROVABLY
  EMPTY. The axiom inhabits AtomProvable(else-play) = a PlaysProof-existential with NO constructor
  witness. CONSISTENT because its only used consequence (AtomProvable_sound → play=some aE) is TRUE
  (bot really plays aE), just not witnessable by a term.

**FINAL DEFINITIVE VERDICT:** removing atom_complete_false_guard requires a PlaysProof rule producing
the ELSE-action (= search_f as a real constructor) — blocked by Walls 1+2. The exclusion lemma PROVES
(machine-checked, [propext]) the missing certificate genuinely does not exist as a term; the axiom
postulates its true `interp` consequence. **This is the paper-grade crux:** the false-guard axiom is
irreducible because the else-play has NO finite proof TERM, only a true interp — the proof-vs-witness
gap machine-located AT THE CERTIFICATE LEVEL, independent of the axiom itself. Engine assets shipped:
Provable_fin/instDecProvableFin/provableFin_sound/ppSize (decider) + the ExclusionSpike lemmas
(scratch, could promote). Build green throughout, axioms still 4 with two-wall+exclusion doc.

**2026-06-26 CLEANUP + PHASE-0 FINDING.** (1) Decider code (otherAction/ppSize/Provable_fin/
instDecProvableFin) MOVED out of Derivation.lean core → ComputableEval/PlaysCheck.lean (it had NO
real consumers — search_f is impossible — so it's quarantined off the critical path as the
decidability-WITNESS for the axiom doc; plays_det is a genuinely useful new lemma). Derivation.lean
comments fixed (removed the self-contradicting "search_f removes the axiom" vs "search_f absent"
text). Build green 3143, 4 axioms.
(2) **FuelledImplSpike.lean RETIRES Phase 0 as a Phase-2 prerequisite.** The Phase-2-enumerator
write-up claimed size-indexing Derivation (Phase 0, ~500-ref) is MANDATORY to terminate-check
"enumerate proofs of size ≤ k". FALSE: the decreasing measure can be FUEL (like eval itself).
provDecide (fuelled) decides CIMCIC's .impl/weakenImpl guard: #eval false for CIMCIC-vs-DefectBot
(consequent DefectBot-plays-C false ⇒ unprovable ⇒ (D,D)), #eval true for CIMCIC-vs-CooperateBot
(consequent provable via ppSize). Runs, terminates, no size-index. So Phase 0 is at most a
cleanliness choice, NOT gating. Remaining Phase-2 work = SOUNDNESS proof of the fuelled decider over
the weakenImpl fragment (incl. excluding searchBranch/simStep/etc. concluding the .impl, ExclusionSpike-style)
— moderate, same flavour as ppSize_sound. Löb fixpoints stay none/axiom permanently (unchanged).

**2026-06-26 CIMCIC vs DefectBot + DIMCID vs CooperateBot — PROVED, NO axiom, NOW LIVE IN ENGINE.**
The two "deliberately omitted incompleteness-boundary" theorems are now real outcome theorems
(CIMCIC.lean / DIMCID.lean), [propext, Classical.choice, Quot.sound] — NOT atom_complete_false_guard.
KEY MECHANISM (general for .impl-guard false cases): the guard implication is vacuously TRUE but
its CONSEQUENT is a genuinely-FALSE atom (DefectBot-plays-C / CooperateBot-plays-D), refuted by
Provable_sound (consequent_not_provable). That blocks weakenImpl (the main path). A ForbiddenC/D
motive induction (no_deriv_forbidden + no_provable_forbidden via Provable.rec over all 6 Provable
constructors) excludes the Derivation/implTrans/searchThenSearch_t/atomBoxImpl paths (searchThenSearch
/atomBoxImpl auto-eliminate by .box shape; leaf Derivation rules need consequent-subject to be
.sim/.ite/.search but it's .const). ⇒ ¬Provable k guard ⇒ proofSearch=false ⇒ defect/cooperate ⇒
(D,D)/(C,C). **This is the CONCRETE payoff of the FuelledImplSpike verdict: the .impl-guard false
fragment is dischargeable WITHOUT Phase 0 and WITHOUT the axiom, because the consequent is a false
atom.** CONTRAST: play-atom false guards (DupocBot/JustBot/CupodTrollBot) still route through
atom_complete_false_guard (no false-consequent handle — the guard IS a play-atom). Full build green
3143, 4 axioms (axiom now load-bearing for fewer cases). Scratch spike CimcicDefectSpike.lean deleted.

**ORIGINAL plan (4 changes) — now known blocked at step 2 without Phase 0:**
1. DecidablePred for bounded play-certificate (done as spike).
2. `search_f` constructor — BLOCKED (see correction above): can't be positive+sound in current block.
3. Re-prove `atom_complete` else-branch (`BaseTheorems.lean:38`) via `by_cases` on the decision.
4. Extend `Derivation.sound`/`playsProof_sound` to `search_f`.

**Change 1 SPIKED & PASSED (2026-06-26):** `Research/Spikes/DecidableFiniteSpike.lean` (NOT
root-imported; `lake env lean ...`). NO sorry/Classical/axiom in proofs. `playsCheck` (total,
fuel-decreasing Bool checker for the PlaysProof/play-atom fragment, parameterised by guard oracle
`gd`) + `playsCheck_sound` + `playsCheck_complete` (via `PlaysProof.rec`, mutual block — mirrors
`playsProof_sound`) + `_mono`/`_mono_le` + `decidableAtBudget` (computes, not Classical.dec).
Confirms the predicate `search_f` negates is genuinely decidable.

**§6 first tie-off `gdRec` SUPERSEDED:** reused budget k as STRUCTURAL fuel → `gdRec_sound` only
modulo named `gd_budget`, which is FALSE: cost-bound finding shows a play accepted at checker-fuel F
has PlaysProof cost ~2^F (.ite branches both children same fuel; .search adds c_guard k uncounted),
so k-as-fuel can't enforce atom_cost(witness)≤k.

**§7 FIX — budget-match CLOSED ✅ (2026-06-26):** cost-tracking checker. `playsCheckC : Nat→Prog³→
Action→Option Nat` returns cert cost; `.search` adds c_guard k+c_node; `.ite` cheaper branch.
`playsCheckC_sound` (some n → PlaysProof cost EXACTLY n, sorry-free). `gdRecB d k (.plays p q a)` =
run playsCheckC then gate `decide (n≤k)`. **`gdRecB_sound` UNCONDITIONAL sorry-free:
`gdRecB d k φ = true → Provable k φ`** — n≤k gate + AtomProvable.mk → Provable k at guard's OWN
budget. gd_budget DISCHARGED not assumed. **`#print axioms`: gdRecB_sound + playsCheckC_sound depend
on [propext, Quot.sound] ONLY** — no sorryAx, no Classical.choice, NONE of project reflection axioms.
Direction chosen by user = "reframe gdRec to enumerate certs ≤ k".

**§8 cost-aware COMPLETENESS — CLOSED ✅ (2026-06-26):** three lemmas bottom-up, all sorry-free.
`plays_det` (play determinism — engine LACKED it; via playsProof_sound + eval_mono_le).
`playsCheckC_no_false` (checker never reports a non-existent play; soundness+determinism — TAMES
the .ite tie-break). `playsCheckC_mono_lift` (fuel-lift F≤F', cost ≤; .ite non-monotonicity killed
by no_false — earlier naive playsCheckC_step FAILED for lack of determinism). `playsCheckC_complete`
(every PlaysProof n found at some fuel, cost ≤ n, via .rec). `gdRecB_accepts` (payoff: cert cost ≤ k
⇒ gdRecB(d+1) accepts, given inner oracle sound+complete). `#print axioms`: completeness lemmas =
[propext, Classical.choice, Quot.sound] (Classical.choice only transitive from engine's classical
meta-theory); still 3 standard axioms, no sorryAx, no project reflection axioms.

**§9 depth recursion — inner_bwd IS the fixpoint boundary (FINDING, not a gap):** hfuel now
DISCHARGED (playsCheckC_complete strengthened to F ≤ n+1 ≤ k+1). gdRecB_accepts keeps only
inner_fwd(=gdRecB_sound) + inner_bwd. gdRecB_complete = per-level reduction to inner_bwd.
inner_bwd does NOT vanish by induction on d: depth bottoms out IFF certificate guard-nesting is
FINITE — off fixpoint yes; AT fixpoint CUPOD self-play references itself same budget (S3′),
nesting INFINITE, no finite d, gdRecB=false (correct, =evalC none). So inner_bwd-as-hypothesis =
EXACTLY "certificate has finite guard-depth" = the precise off-fixpoint condition; a concrete
searchDepth≤d side-cond carries same finiteness, NOT new math. Boundary LOCATED inside the
completeness machinery.

**FINAL STATUS:** SOUNDNESS (budget-match, gdRecB_sound) CLOSED unconditional [propext,Quot.sound].
COMPLETENESS (cost-aware, playsCheckC_complete incl F≤n+1) CLOSED sorry-free. gdRecB_accepts/
gdRecB_complete per-level CLOSED; sole residual inner_bwd = the fixpoint boundary itself, NOT
mechanical. All sorry-free, ≤3 standard Lean axioms, no project reflection axioms. Two hard math
pieces (budget-match soundness; determinism-based completeness) DONE. Spike is the complete
sound+complete decision-procedure story for the play-atom fragment, boundary located.
**Scope:** covers Provable-via-AtomProvable/PlaysProof only; reflection rules (weakenImpl,
searchThenSearch_t, atomBoxImpl) + `.struct` NOT enumerable, out of scope (correctly — failed guard
= play-atom w/ no certificate). Currently the axiom is INERT (no library theorem forces it); to
EXERCISE the win need a "CupodProber" bot forcing a failed-guard cooperation. See [[project_pblt_vs_constructive_lob]].
