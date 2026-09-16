---
name: project-arithmetized-s-roadmap
description: "Arithmetized S on Foundation (arith/ArithS): U10 DONE 2026-09-16 (BoundedInnerNec 16, headline theorems unconditional); M6 merge: atom re-cost DONE on colomban-recost, BOX OBSTRUCTION found (additive engine box vs polynomial S' ⇒ no polynomial bridge budget) — user decision A/B/C pending; T1 red cell proven; M3 DONE 2026-09-10 on canonical branch colomban-arith-m3 (~/wt/osgt-arith-m3, engine on v4.33.1) — T2 = T2-CORE + T2-NEG + T2-AGENT, all 3-axiom; what is out of scope (box compositionality, tau constructors, LAct Σ₁-completeness) and the traps"
metadata: 
  node_type: memory
  type: project
  originSessionId: 1a734d76-f764-480d-8461-59dedf4d8e0a
  modified: 2026-09-10T13:50:42.554Z
---

Decision 2026-09-09 (Colomban): ARITHMETIZED instance of `S` on Foundation, proof LENGTH
measure, standalone package `arith/` (`ArithS`). Plan + full status log:
`engine/PrisonersDilemma/Research/Notes/ARITHMETIZED_S_ROADMAP.md` (kept in sync on both
branches); design materials `Research/Notes/M3_TRANSFER/`.

**STATE 2026-09-10 (end of the M3 push), canonical branch `colomban-arith-m3` in
`~/wt/osgt-arith-m3` (engine bumped to Lean v4.33.1 + arith merged; `lake build ArithS`
green, ~3200 jobs, incremental ~15 s). OneDrive checkout stays on `colomban-arith-s`
(arith-only, engine v4.28) — develop on `-m3`, sync docs to `-s` by copying the roadmap.**
Proven, all `#print axioms` = the three standard ones:
- T1 `red_cell` (Dupoc, Cupod) = (D, C) every k; non-vacuous: `guard_fits` (binary
  descriptions, Critch's (b)). 6-variable templates `pSearch k g p q`, τ acts on templates
  (`relabelTemplate`), `psubst`/`pSim` semantics with unconditional τ-equivariance.
- T2-CORE `Core.Pf_core_sound`: budget-erased modal-propositional core sound over PA
  (ProvabilityAbstraction D1–D3, kreisel fixpoint), non-core rules as the `Leaf` hypothesis.
- T2-NEG `no_budget_keeping_transfer`: no inflation `e` makes `Pf k φ → PA ⊢_{e k} tr φ`
  true (atoms are charged by evaluation steps: `Pf 1 (plays (const C) (bot^m (const C)) C)`).
- T2-AGENT `playsProof_evalGraph`: engine evaluation certificates are arith evaluator runs
  at the same budgets, given `GuardAgreeT/F` on the consulted guards; unconditional
  `playsProof_evalGraph_searchFree`; truth equation `models_trAt_plays`. Fragment = the
  engine's MODEST programs (`modestP`, all sim arguments placeholder-or-closed — true of
  the whole zoo), players `Proper` (≠ .self/.opp).
- AFTER M3 (same day): `AgentConverse` — `eval_iff_evalGraph`/`play_iff`/`outcome_iff` under ONE
  two-sided `GuardAgree` (restricted to modest proper frames); `GuardAgreeF` derived from engine
  soundness. `Inst` — hom `inst : LAct →ᵥ ℒₒᵣ` (c_C ↦ 0, c_D ↦ 1); `pa_proves_trAt_inst`: PA proves
  the atom sentence of every modest play (Σ₁-completeness), unconditional for search-free
  programs; T2-CORE's atom leaves discharged (`leaf_atom_sound`, `leaf_atomBoxImpl_sound`,
  `transfer_of_leaves`). Still hypotheses: the 12 source-reading leaves (= bounded D1) and
  `atomNeg` (needs PA-internal determinism, ~150 lines of general-model eval lemmas). Audit.lean
  census: 33 theorems, all three standard axioms.
- Code translation `pcode/tmpl/tcode` with substitution code equations + τ on the box-free
  search-bot fragment `fragP/fragF`.

**Boundaries (honest, recorded, not gaps in proofs):** `.box` cannot be translated
compositionally under LENGTH-bounded provability (the box carries its body's code as a
numeral; provable equivalence ≠ identity) — so T2-AGENT's box facts are hypotheses, exactly
bounded D1 (Critch's (d), M4). Truth → `TAct ⊢` for `trAt` sentences needs Σ₁-completeness
over `LAct` with the two constants (Foundation's is ℒₒᵣ-only) — open. tvote/sys/selfIdx
outside (code 0). `GuardAgreeF` from engine soundness needs the converse of T2-AGENT.
Paper sentence: "S is sound relative to PA wherever a character count exists; where the
engine charges steps/cheap citations, no PA proof length can match — proven; bounded
soundness is exactly Critch's (d)". The budget-erased world is Berns/Barász's — novelty
stays the BOUNDED S.

**Traps:** closed constants built from the template (`flen Gtmpl`, `⌜Gtmpl⌝` pairs) must
never enter kernel-compared `Nat` arithmetic — package existentially; `lake env lean` output
is block-buffered when redirected (bisect by truncation with `timeout`); at V = ℕ `<` is
Nat's but `≤` is PeanoMinus's (`le_def`); omega useless on Foundation orders; `Formula`
must be `PD.Formula`; `simp` never rewrites the instance-implicit structure of
`Semiformula.Eval` (use `rw [stdAct_lMap_emb]`); never compile Foundation/mathlib;
LeanInteract has no REPL tag for v4.33.1 yet. See [[project-arith-numeral-vacuity]],
[[project-boundedgl-interface]], [[project-transpose-red-cell]].

**DECISIONS 2026-09-11 (Colomban, new session):** goal restated = a working S' (PA + length-bounded
□_k) in which PBLT (parametric bounded Löb, Critch Lemma 3.6) is a theorem, Cupod-vs-Dupoc holds
(done, T1) and all zoo programs run; the MERGE onto the rule-based `Pf` (the T2 bridge) is
DEFERRED — do not extend T2-CORE/AGENT/Inst/Det further. Ordering agreed: M4 (bounded D1/D3, parametric
diagonal lemma) → PBLT → Löbian cells re-proved in S'. CORRECTION to an earlier claim: the
`tmpl (.box k ψ)` node-data coding fix (FitBox design fix) is NOT a prerequisite for PBLT — Dupoc's
guard is box-free and fits. What PBLT needs is the PARAMETRIC box: `□_x ψ(x)` written as
"LenProvableV x (subst (bnum x) ⌜ψ⌝)" via internal substitution, never as a numeral of ⌜ψ(k̄)⌝
(that numeral has ≥ k symbols by `size_bnum_ge`, so no proof of it fits). The `tmpl` fix serves only
LegibleBot/OptimBot + the bridge — behind M4. Method: written brief + verbatim reader reports in
`Research/Notes/M4_BOUNDED_HBL/`, then agent-sized proof tasks (≤2 concurrent Lean agents).

**CHECKPOINT 2026-09-11 (evening, user away ~2h).** Design brief `Research/Notes/M4_BOUNDED_HBL/BRIEF.md`
(+ 3 reader reports) committed 05ccd3b; roadmap has the M4-start entry. Design: Critch 2019's UNIFORM
PBLT proof (Properties 1 impl-distribution, 2 quantifier-distribution, 4 bounded INNER necessitation
`□_a ψ → □_{E a} □_a ψ` with E subexponential = THE crux; Property 3 reduces to unbounded
Σ₁-completeness, free); all bounded lemmas V-GENERIC on codes + `complete`; guard mismatch fixed by
re-coding programs on `ppair x y = (x+y)²+y` (term-expressible; Foundation's `pair` has an `if`).
LANDED: a1aa1b9 `ppair` re-pairing of Prog.lean, green, 62 census lines, no statement weakened.
IN FLIGHT (background agents, each commits when green or as `wip`): (1) `ArithS/CutV.lean` — bounded
D2 on codes inside every model of IΣ₁ with dlen accounting (may carry a named `ProperV` hypothesis);
(2) `progT`/`progTT` term descriptions replacing `bnum (dnum x)` in descVec/dnumT, `guard_fits`
re-proved, HEADLINE `exists_dupoc_instance : ∃ q : Semisentence LAct 1, ∀ k, guardSentenceA 0
(Dupoc k) (Dupoc k) = q ⇜ ![bnumT k]` (+ code form, V-generic if time). If a session was closed,
check `git status`/`git log` in ~/wt/osgt-arith-m3 for partial files before assuming loss.
NEXT (brief §3 ladder): U1 parametric box `bewB a n k := ∃ g, g = subst (bnum k ∷ 0) n ∧ L a g`;
U3 instantiation-with-dlen in V; U6 parametric diagonal lemma with bnum instances
(Foundation's `parameterizedFixedpoint` uses unary numerals — re-do with bnum); U7 Dupoc
transparency in V (V twins of the ℕ-only evaluation lemmas listed in READ_arith_for_m4 §4(iv));
U8/U9 pblt_uniform + dupoc_self_coop conditional on `BoundedInnerNec E`; U10 discharge it.
**2026-09-11 later — U2 LANDED (f4a1a0b, `ArithS/CutV.lean`):** bounded D2 on derivation CODES in
every model of IΣ₁: `lenDerivable_cut_V` UNCONDITIONAL for `LenDerivable T k φ := ∃ d, Proof T d φ ∧
dlen T d ≤ k` (Σ₁, no fbound); `lenProvableV_cut_V` under named `ProperV V T` (theorem at ℕ:
`properV_nat_TAct`; OPEN for general V — needs V-internal induction on derivation codes);
`pa_proves_cutSentence`/`tact_proves_cutSentence` via `complete`. LESSON: write the Löb argument
with `LenDerivable` (no fbound); `LenProvableV`/`ProperV` enter only where the evaluator's guard is
consulted. Agents stall silently on long commands — tell them "short tool calls, timeout 600, print
progress". IN FLIGHT: `ProgT.lean`+descriptions+`Instance.lean` (exists_dupoc_instance);
`InstV.lean` (instB, bewB, lenDerivable_inst_V = Property 2 with dlen accounting).
**2026-09-12 — M4 ladder progress (all three axioms, census 104):** U0 done (ppair re-pairing a1aa1b9;
ProgT/Instance/InstanceV: `guardCode_DupocV_eq_instB` — Dupoc's guard IS `instB ⌜qDupoc⌝ k` in every
model); U1+U3 InstV (47fa241; `bewB`, Quantifier Distribution `+5|χ[t]|+3|χ|+|t|+7`); U2 CutV (f4a1a0b);
U6 Diag (669704c; parametric diagonal lemma over TAct; `tact_complete` = completeness on REAL-equality
models, `𝗘𝗤 LAct ⪯ TAct`; TRAP: `simp` on a goal containing `⌜tactDiag θ⌝` overflows the kernel
numeral — prove for a variable sentence); U7 Transparency (54aee07). VACUITY FOUND + being fixed
(U0b): TAct with only `c_C ≠ c_D` has models reading constants as e.g. 5,7 where the guard is FALSE ⇒
`TAct ⊬ guard(k)` ⇒ Dupoc never cooperates; fix = axiom `axAct : (c_C=0 ∧ c_D=1) ∨ (c_C=1 ∧ c_D=0)`
(+ swap image). Brief §6 = exact U5/U8/U9 statements; §7 = the correction. Remaining: ProperV V
(agent), axAct (agent), NumeralFacts (`k̂ ≤ bnumT k` short proofs), U8 assembly, U9 cell; U10 = E.
**2026-09-12 later:** axAct LANDED (7908336; `tact_complete'` over stdActS/swapActS); ProperV LANDED
unconditional (5d9fc0a; `lenDerivable_iff_lenProvableV` in every model); Assembly/Prep LANDED (ec5a8b6,
census 138): conjunction family `pConj = qDupoc ⋏ qCupod` (Critch's PBLT-on-the-conjunction move —
avoids evaluator τ-equivariance in V), `psi_fixed_point`, `BoundedInnerNec (d c c₁ c₀)`. IN FLIGHT:
Assembly/Uniform (U8), Assembly/Cell (U9 `dupoc_self_coop`), NumeralFacts. After U9: only U10
(discharge BoundedInnerNec, polynomial E) remains for the Löbian cell; then mutual-Löb cells.
**U10 design 2026-09-12 (`M4_BOUNDED_HBL/DESIGN_inner_necessitation.md`):** eigenvariable construction
(never write a code as a numeral; ~40 universal lemma-sentences by `complete`; recursion by
`Derivation.induction1`), expected E(a)=O(a³) (O(a²) with binary variable indices in Length.lean),
2.5–4 MONTHS — the user's call. LESSON/TRAP: the first `BoundedInnerNec d c c₁ c₀` was UNSATISFIABLE
(target contains the unary numeral ⌜χ⌝ ⇒ dlen ≥ encode χ, exponential in flen χ): any bound on a
sentence naming a formula by numeral must be per-family (`∀ χ, ∃ C`), never uniform in flen.
Restated `BoundedInnerNec d`. Risk to check first: Foundation's `𝗣𝗔.Δ₁` recognizer for the `axm` leaves.
**MILESTONE 2026-09-12 (4c8ecc9, census 162/3 axioms, tree clean):** `pblt_uniform` and
`dupoc_self_coop`/`dupoc_finds_guard` are THEOREMS conditional on the single hypothesis
`BoundedInnerNec d` (Critch (d)); Cupod-defects-vs-Cupod comes with it (conjunction family). Docs:
roadmap status log, results addendum, handover §4 update, brief rows — all committed. NOT synced to
OneDrive `-s` (outside allowed dirs; user does it by copy). NEXT = USER DECISION: U10 (prove
BoundedInnerNec 3; 2.5–4 months) vs mutual-Löb cells vs paper; cheap independent improvement: binary
variable indices in Length.lean (one factor of a off E).
**U10 STARTED 2026-09-12 on branch `colomban-arith-u10`** (same worktree ~/wt/osgt-arith-m3; `-m3` frozen
at 15b015a). Plan = DESIGN_inner_necessitation.md §5 + brief §9: Necessitation/Primitives (useLemma,
elimExists codes), Lib/{Basic,Sets,Formulas,Lengths} (agents launched), then Lib/Nodes (Intro/Dlen/axm
sentences), describeFormula, per-tag fragments, Derivation.induction1 recursion, top → BoundedInnerNec 3.
**Agent ops (2026-09-12):** the account's session rate limit (resets ~4:10am Berlin) kills background
agents mid-task; their wip commits and untracked files stay on disk. RESUME the same agent by
SendMessage (it keeps its transcript) with the exact on-disk state (`git status`, single-file check
output) — no relaunch needed. Two Lean agents concurrently max. `pgrep -f 'bin/lake build'` (plain
`'lake build'` matches the agent's own polling shell). U10 state: Primitives landed (204c012);
Lib/{Basic,Sets,Formulas,Lengths} wip-committed (e898999, 02e43c6), Nodes.lean drafted; both resumed.
**U10 progress 2026-09-12 (branch colomban-arith-u10):** Primitives 204c012, Lib A f6536fc (145 rows),
Lib/Nodes d95ba66 (Intro/Dlen/axm), Lib/Bridge 637df06 (ℒₒᵣ/LAct), Steps wip 3e4de8e (useHorn/introFact).
ARCHITECTURE (brief §10): CPS recursion is impossible internally (changing continuation; Π₂) → a
flat STEP LIST + a PR chain builder folding from the end with fixed params (`chainCode`), contexts
precomputed (`ctxVec`), `StepOK` Δ₁, proofs by IΣ₁ induction on the index; producers are
list-valued Σ₁ functions (`describeSteps`, fragments, `verifySteps`). Chain agent launched.
**HANDOVER 2026-09-13 (user moving to another account):** U10 landed modules on `colomban-arith-u10`:
Primitives, Lib A (145 rows), Lib/Nodes, Lib/Bridge, Steps, ShiftLen, Lib/Walk+WalkLemmas (census 292);
Chain.lean = partial vector twins (wip), RowInst/describeSteps/fragments/verifySteps/top NOT started.
Handover doc rewritten (HANDOVER_ARITHMETIZED_S.md), CLAUDE_MEMORY/ refreshed from this memory dir.
**2026-09-13 takeover (new account, same machine/worktree):** build green 3231 jobs, census 292.
Chain.lean's 30-min stall = BLUEPRINT TRAP (direct `!(qVecGraph L) y ih` / `!(impGraph L) y x ih`
clauses; ∃-wrapped → 9 s), then 25 real errors (guessed `VecRec.Construction.result_defined_iff`,
A.5 rewrites) — Part A never end-to-end checked. Committed 3e5813e. Agents: Chain repair + Part B;
RowInst. Not pushed (user did not ask).
**Chain.lean DONE 9bf20ba (census 301): chainCode_proof/dlen_chainCode_le; VecRec definability lemma is `eval_resultDef` (PR: `result_defined_iff`). In flight: RowInst, Steps _occ swap. Next: describeSteps.**
**RowInst DONE a40e816 (87 rows, 28 fact codes, census 334); Steps _occ c2cfd17; Describe (the walk) agent launched; Lib/Occ in flight. Flag: isSemiformulaSubsts1B/isFormulaFreeB write arity 1 as numeral 1, not cT 1.**
**Lib/Occ DONE 18b6a91 (census 347; DSL numeral 1 ≠ oneO by rfl — bridge row dslSuccEqSuccO). In flight: Describe (walk), DESIGN_fragments.md (read-only), cT-arity variants of two rows.**
**DESIGN_fragments.md 2026-09-13 (brief §11):** no sub-chain step (circular PR) → flat tags `sGoal` (6) and
`sLemma` (7); canonical LAYOUT instead of an environment; ū = bnum(dlen) numerals with one `dlenBinaryLe`
+ one `sLemma` per node; derived formulas RE-DESCRIBED + certified (Occ rows unneeded); `VerifyGraph`
fixpoint on ⟪ρ, L⟫; cost cubic = BoundedInnerNec 3; M = 9; ~150 rows + ~6–7k lines of producers.
ORDER: tags 6/7 (agent launched) → numSteps → copy/chain/eq walks → certX/lenSteps → frag<Tag> +
VerifyGraph → verifySteps_ok → top. Walk (Describe) in progress (wip df3ffe3, 127e2ab).
**Chain Part C (sGoal/sLemma) DONE 6d4ebab; Describe wip through term-walk D3 (86cb745, a6aff62 wired); numSteps agent launched. Agents on this account stall on background waits — resume by SendMessage with explicit polling; check git status first (their work is usually committed).**
**Describe (the walk) DONE 1ccea31 (5616 lines; D1–D5 terms+formulas; corrected bounds descCount+1 ≤ 2|r|, len ≤ 12|r|; cost cubic). In flight: NumSteps, Lib/Frag+RowInstB (§8.1 rows). Next: copySteps/chainSteps/eqSteps → certX/lenSteps → frag<Tag>+VerifyGraph → top.**
**Lib/Frag+RowInstB DONE 3a3cad2 (196 rows, census 396; generator scripts/gen_frag.py). In flight: NumSteps (resumed), Layout (copySteps/chainSteps/eqSteps). TRAP: self-matching watcher shells loop forever — poll with pgrep -f 'bin/lake build ArithS'.**
**NumSteps DONE ded402f (addCode/leCode/bin3Fact/cTEq as sLemma steps, cubic). In flight: Layout (copy/chain/eq), Cert (certNeg/Shift/Subst/Free + lenSteps). Then: frag<Tag> + VerifyGraph + verifySteps_ok → top → BoundedInnerNec 3.**
**2026-09-14: Layout wip Parts 2–3 (copySteps, chainSteps; eqSteps pending), Cert wip Part 0 + CertRows (producers pending); both resumed 09:01 after the 02:10 kill. Rate-limit resets so far: 04:10, 16:20, 15:10, 20:50, 02:10.**
**Layout DONE 0a076a4 (copySteps/chainSteps/eqSteps; layout l_s=&0,s=&1,s_i=&(i+1); bridges dossFacts↔walk and eqCount=descCountF still to prove). In flight: Cert (producers), Frag1 (axL/verum/and/or/wk/cut). Then Frag2 (all/exs/shift/axm) → VerifyGraph → top.**
**PAUSED 2026-09-14 10:40 (user switching to Opus / low Fable credits): agents stopped; Cert/Frag1/Frag1Rows committed UNVERIFIED wip; HANDOVER §8 rewritten with the resume procedure and remaining ladder; branch -u10 never pushed.**
**2026-09-14 (Opus 5 session, stopped cleanly):** takeover triage recovered all three unverified
files (Frag1Rows green; Frag1's 2 errors = `norm_num` cannot do V-arithmetic with a cast natural;
Cert's 30-min HANG = blanket `simp` over a five-disjunct Fixpoint blueprint in `passGraph_defined`,
fixed by targeted `simp only` + `rw [eval_fixpointDef]`, 44 s — THE HOUSE PATTERN for every
fixpoint). LANDED: Frag2 (ALL TEN per-tag fragments now exist), Cert's term+formula certification
passes (passT/passV/passF, certNeg/certShift, eqCount bridge), tsvAdjCert into the table at M=9,
Verify (VerifyGraph + StrongFinite + ten inversion lemmas + verifyGraph_exists). Build 3247 jobs,
census 451, all standard. HONEST WEAKENING (Verify §3.6): verifyGraph_unique is FALSE as the clause
is written (prologue left existential) — the fix is to replace `∃ pro ≤ L` by the Σ₁ calls that
compute it; everything above survives. DESIGN FINDING: the vector walk emits `tvPiFact`, not
`utvPiFact` — a bridge row is needed before certSubst. LESSONS: verify a reported blocker against
the tree (2 of 2 dissolved); sentinel-test a suspiciously fast green on generated files; only
exit 124 + empty log is a stall; never end an agent turn while its own check runs.
**2026-09-15 (Fable session, stopped for a model switch):** TOP DONE — `boundedInnerNec_four_of_kit :
KitPackage' → BoundedInnerNec 4` (and `_three_of_kit`); TARGET IS DEGREE 4 (user-confirmed; the
generic cost lemmas charge 4·B·E per step → one factor of g over the design's cubic; 3 = optional
occurrence-accounting refinement; linear impossible). Landed: certSubst/certFree/lenSteps (Cert
Parts 5–6), Dossier bridge, NumLength/NumMul, Members, NumId (numeral identification for standard
codes), Pin assembly modulo two oracles, Prologue for 7/10 tags + Layout/Layout0 + costs + the
empty-sequent decision (∅ occurs; nonemptiness FALSE under ¬Con), Cert §6.7 qVec caps (quadratic).
REMAINING = exactly `KitPackage'`: PinKit' (bnumSteps oracle, SubstOracle instance, coarse costs);
VerifyKit' (all/exs/axm prologues, Verify's clause edit, the per-tag layout theorems glued by
induction1 𝚷 at the root, costs). Census 606, build green, branch pushed 09-14 (push again).
Design bugs caught this week: neg pass certified against the wrong vector; cert/frag row tables
collided (re-indexing wrapper in Prologue §0). 4 of 5 reported blockers dissolved on inspection.
**2026-09-16 — U10 COMPLETE, THE HYPOTHESIS DISCHARGED.** `BoundedInnerNec 16` is a THEOREM
(`ArithS.boundedInnerNec_sixteen`), and with it `dupoc_self_coop_unconditional` and
`pblt_unconditional` hold with NO hypothesis — Critch's assumption (d) is no longer assumed. Build
3270 jobs, census 918, all three standard axioms, zero sorry/axiom/native_decide. Degree 16 not 3:
every loss traces to UNARY variable-index charging in the M1 length measure (the cap, the qVec
iterate, per-step context growth); Critch asserts only polynomial expansion and the M4 results are
parametric in `d`, so nothing downstream depends on it. Optional fixes deferred: substitution
certificate redesign, occurrence accounting, binary index charging (root cause, touches M1).
Branch `colomban-arith-u10`, NOT pushed since 09-14 — push first.
LESSONS: a COMPLETION CLAIM must be re-derived from the tree, never repeated (the final agent report
quoted three theorem names that did not exist; the work was two lines short — caught by grep). An
interface written AHEAD of its consumer has PROVISIONAL binders until the consumer compiles against
it (six corrections from that one pattern; two were mine). Check CALLABILITY before transcribing.
Compile a skeleton rather than read when the question is structural. Never edit Lean by script.
Only a must-fail probe distinguishes a real edit from a stale olean.
**2026-09-16 (later) — M6, THE MERGE `S`→`S'`: design fixed with Colomban, then an obstruction found.**
DESIGN (roadmap §3 "M6"): `S'` is THE formal system; each of the engine's 33 `Pf` rules becomes a
DERIVED RULE of `S'` (theorem at budget `f`(engine budget)); the ~155 outcome theorems stay untouched
(one induction over `Pf` composes the rules); rule layer = API; BUDGET-KEEPING (erased = Barász/FAF
territory); OptimBot/LegibleBot out. Trusted definitions = `tr` (must rewrite budgets inside PROGRAMS
too, `search k ↦ search (f k)`, else self-referential bots don't translate to themselves) and `f`.
ORDER agreed: (1) recost branch green, (2) check M3 lemmas at explicit budgets, (3) the induction.
STEP 1 — branch `colomban-recost`: `AtomProvable.mk` charges `n + (Formula.plays me opponent a).size ≤ k`
(FULL conclusion; a first pass charged `opponent.size` only — WRONG, the subject side has an untaken-
`.ite`-branch witness, `ite_t` never pays the unrun branch). Blast radius ≈ 70 errors / 30 theorem
files, all budget arithmetic — DONE the same day: engine 3278 jobs green, export BYTE-IDENTICAL
(155 cells / 4 companions / 18 tau rows keep values, regimes, pads; only witnesses/thresholds grew;
WaryBot "defended" companion moved 16→32, the k=16 statement is FALSE now). Method: Helpers layer
first (one agent with `lake build`), then per-pair files in parallel with `lake env lean` ONLY (never
two `lake build`s); agents that "wait" on their own background checks stop — resume by SendMessage.
`ArithS/Neg.lean`: T2-NEG RETIRED, replaced by `no_budget_keeping_witness_pays` + `pf_size`
(needs `import PrisonersDilemma.Base.Exclusion`, `PD.BaseTheorems.pf_size_or_atom`). Arith 3271 jobs,
census 908, all standard. Committed on `colomban-recost` (on top of -u10), NOT pushed.
STEP 2 — cut YES (`lenDerivable_cut_V_TAct`), instantiation YES (`lenDerivable_instB_V`), diagonal NO
(`tact_parametric_diagonal_inst` unbounded; wrapper via `exists_forward_length` pattern), bounded D1
PARAMETRIC ONLY (`BoundedInnerNec 16` at `gBudget k = ‖k‖³`; closed-sentence arbitrary-budget form
must be re-packaged from `Necessitation/Top.lean`).
THE OBSTRUCTION (not repaired, USER DECISION): engine box rules are ADDITIVE (`Pf a φ → Pf (a+|□_a φ|)
(□_a φ)`), `S'` expansion is POLYNOMIAL (deg 16) ⇒ `f(a + log a + s) ≥ C f(a)^16` ⇒ no polynomial or
single-exponential `f`; `f = 2^{2^{5a}}` works. Löbian cells then DOMINATED by M5 (direct parametric
PBLT gives all large k; bridge gives budgets `f k` only). AND `search_t` cites at `log k` ⇒ unsatisfiable
for any monotone f ⇒ needs a second recost (charge `k`). Options: A uniform bridge + doubly-exp f +
search_t recost; B no rule bridge, direct S' proofs per Löbian family (erased T2-CORE doesn't cover
search-bot reading leaves); C `S''` = arithmetized derivations with a primitive `cite` node charging
`|□_k σ|` (Critch (c)/(d) as a rule) — engine rules derived at the SAME budgets, U10 = "S'' reduces to
PA polynomially per box level". I lean C or B; A realizes the wording literally but budgets become nominal.
LESSON: I told the user "the budget-keeping bridge is the same induction with f threaded through" —
wrong; composition through nested boxes was not checked. Check composition, not just per-rule.
**2026-09-16 (evening) — THE D SPIKE (branch `colomban-boxcost`, `Research/Notes/BOXCOST_SPIKE.md`):**
polynomial box gate `boxCost a φ = (a + |□_a φ|)^boxDeg`, `boxDeg = 2`, on `boxIntro`/`box4`/`atomBoxImpl`.
RESULT: `pblt_engine_id`/`_bounded`/`mutual_pblt_engine_id`/`_staggered` statements byte-identical (agent
re-assigned the chain: `bloeb_std`, `mutual_loeb_std`, `poly_envelope_le`); ALL 155 cells + 4 companions
+ 18 tau rows compile unchanged except 3 OptimBot staggered cells (out of scope) which FAIL AT EVERY
THRESHOLD: premise pays `search_f` floors (`pm ≥ 2k`) ⇒ fixpoint box costs `≥ 4k²` ⇒ linear stagger
insufficient — cooperation across a floor needs a POLYNOMIAL stagger. The in-scope `_staggered`
companions survive only because `searchThenSearch_t` CITES its floor-paying inner premise at `c_guard`
(second citation rule, the search_t half). Degrees: single Löb W⁴, mutual W¹⁶, vector W¹²⁸ (2⁴⁰²⁹).
LegibleBot's inner-dial `box4 k (2k+64)` dead under the gate (repaired via polylog fixpoint). Metatheory
target pre-broken (docstring-before-imports) — its PfG mirror has 164 box sites if this lands.
PAPER SENTENCE: the additive rule was never load-bearing; the engine satisfies Critch (a)–(d) as rules
with the polynomial U10 proves. Also `MERGE_CROSSROAD.md` (routes A–D), `RED_CELL_AUDIT.md` +
`ArithS/RedCellAudit.lean` (trusted base / negative controls / mutation protocol, one probe executed).
Agent lesson: raw `bloeb_engine` users → switch to `bloeb_std`; keep squares opaque (`obtain ⟨V,hV⟩`),
never let omega/decide see `2^34`-size literals (recursion depth).
**2026-09-16 (night) — RED CELL STATED ONCE, INSTANTIATED TWICE + SOUNDNESS MUTATION.** `Base/RedCellFramework.lean`
(engine, imports nothing): hypothesis package (H0)–(H6) of the July-27 paper note, `red_cell`/`search_symmetry`/
`guards_fail`/`not_CC`/`not_DD`/`not_CD` with NO axioms (split needs determinism of BOTH plays). Instances:
`PD.Theorems.red_cell_engine` (Pf, Formula.transpose, Pf.transpose) and `ArithS.red_cell_via_framework`
(LenProvableV TAct, lMap swap). `ArithS/RedCellUnsound.lean`: `TBad := TAct + c_C = c_D (+swap)` inconsistent,
3-node ex-falso proofs, `red_cell_flips_when_unsound` (cell → (C,D) for large k) = the note's Prop 6.1;
`EvalGraphBad` is a COPY of the evaluator with the theory swapped (evaluator not parametric in the theory —
a refactor candidate). Arith 3295 jobs, census 917. The July note (dupoc_vs_cupod_proof.pdf) makes the SAME
symmetric-axiom assumption (its (H1), Remark 3.4); its theory lacks `axAct`, so by its own Prop 6.2 it cannot
prove positive guard instances (Löbian cooperation unprovable there) — our `axAct` is the minimal symmetric fix.
Design rationale for every trusted definition: `SPRIME_DESIGN_RATIONALE.md`.
