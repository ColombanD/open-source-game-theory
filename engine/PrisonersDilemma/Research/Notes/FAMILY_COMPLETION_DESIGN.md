# Family completion — closing Families A and B of `S`

**Status (2026-07-28): steps 1–5 INTEGRATED (build green 3238 jobs) — FAMILY B
COMPLETE; FAMILY A closed over search telescopes at every depth (`Pf.searchChain`,
27 constructors); the CLOSURE CERTIFICATES are kernel-checked theorems
(`Base/Closure.lean`). Remaining: ONE modeling decision — ite-probe reading — which
FLIPS OUTCOMES (below), and is deliberately left to the human.**
Evidence spike: `Research/Spikes/family_completion/FamilyCompletionSpike.lean`
(compiles against the current engine; no sorry, no axiom).

Context: `ProofSystem.lean` declares the `Pf` constructors in three families —
A (reading rules, 10), B (logical glue, 6 since 2026-07-28: `implRefl`/`implK`
landed), C (Löb machinery, 8; already complete) — 24 total.
This note is the plan to *finish* A and B, after which `S` grows only by derived
lemmas (`LlmLemmas`), never by constructors.

---

## Family B — the finishing rule set

| rule | shape | kind | certificate (spike §1) |
|---|---|---|---|
| `implRefl` | `⊢ φ → φ` | leaf | `implRefl_sound` |
| `implK` | `⊢ φ → (ψ → φ)` | leaf | `implK_sound` |
| `contrapose` | `⊢ φ→ψ  ⟹  ⊢ ¬ψ→¬φ` | 1-premise | `contrapose_sound` |
| `negElim` | `⊢ ¬φ, ⊢ φ ⟹ ⊢ ψ` | 2-premise | `negElim_sound` |

Notes:
- `implRefl` was **provably absent** from the pre-integration `S` (spike §3, now the
  positive demo `implRefl_now_in_S`): a bot guarding on the tautology `.impl A A`
  fell through — the concrete gap, closed 2026-07-28.
- `implK` + `mp` derives `weakenImpl` (spike `weakenImpl_derivable`); keep
  `weakenImpl` primitive anyway (tighter transcripts, zero-cost compat).
- `contrapose`/`negElim` are the first `.neg`-CONSUMERS. `negElim`'s census case
  discharges by `Pf_sound` on its contradictory premises. Faithful (PA proves both).
- With these four, family B = the Hilbert basis for the impl/neg fragment MINUS the
  deduction theorem (deliberately absent, see ProofSystem header). **B is then done.**
- Costs: leaves pay conclusion size (like `eqRefl`); rules pay subtrees + conclusion
  (like `mp`) — no new cost machinery.

### THE CENSUS BREAK AND ITS REPAIR (the load-bearing finding)

`implRefl`/`implK` FALSIFY the tail-recursing census invariant used by every
structural exclusion proof (`Forbidden (.impl _ ψ) := Forbidden ψ`): they are
premise-free with an arbitrary tail, so `⊢ A → A` is derivable and tail-forbidden
(spike §2 `old_invariant_falsified`). The underlying unprovability facts are NOT
false — extracting the tail of `φ → φ` via `mp` needs `φ` itself — but every census
THEOREM as stated breaks. This is the canary doing its job.

**The repair** (validated, spike §2 `guarded_census`):

    Guarded (.impl α ψ) := Guarded ψ ∧ ¬ Guarded α

("the forbidden tail is reachable only through unforbidden antecedents"). Reflexive
and K shapes self-destruct; every premise-carrying rule closes via `by_cases` on the
antecedent, with the premise IH refuting the forbidden branch. Real guards stay
covered (`guarded_covers_real_guards`). Integration therefore REWRITES the forbidden
predicates in `Base/Exclusion`, `Theorems/CIMCIC/*`, `Theorems/DIMCID/*` to the
`Guarded` shape — do this TOGETHER with the planned regrouping of all censuses into
`Base/Exclusion` (one parameterized census family), so the per-constructor cost is
paid once, not per matchup file.

## Family A — the general in-frame rule `ctxBranch`

**Problem.** `eval` runs a bot's body in frame: `.search` guards on the way to the
played branch substitute the FULL `me`, so "S reads source" needs one fused rule per
then-path nesting shape (`searchBranch`, `iteBranchSearch_t`, `searchThenSearch_t`,
`botSearchStep`…) — the family grows with the bots.

**Solution.** Reify the then-path as a telescope (spike §4):

    EvalCtx ::= hole | searchT g ψ elseB rest | iteT z a' elseB rest
    plug   : rebuild the source around the branch
    guards : the in-frame guard facts, outermost first
             (searchT ↦ □_g (ψ.subst me opp);  iteT ↦ opp plays a' vs .bot z)

ONE constructor replaces the zoo:

    | ctxBranch (C : EvalCtx) (a : Action) (me opponent : Prog)
        (hme : me = C.plug (.const a)) :
        (implChain (C.guards me opponent) (.plays me opponent a)).size ≤ k →
        Pf k (implChain (C.guards me opponent) (.plays me opponent a))

- Soundness core PROVEN against the current engine: spike `evalCtx_sound` +
  `ctxBranch_certificate` (induction on the telescope; search layers commit via
  `proofSearch_spec`, ite layers via the frame-independent `.sim .opp (.bot z)`
  probe — the SAME restriction as `iteBranchSearch_t`, and for the same reason:
  arbitrary ite guards are frame-dependent, exposing them as standalone `.plays`
  atoms is unsound).
- `searchBranch` and `iteBranchSearch_t` conclusions are definitional instances
  (`rfl` demos); depth-3 shapes (PrudentBot3) come free.
- `searchThenSearch_t`-style single-box collapses are DERIVED: apply the chain to
  the inner `□` obtained by `boxIntro` on the held inner proof, via `mp`
  (guards are ordered outermost-first, so order the chain so the inner box is the
  first antecedent consumed — or add antecedent-exchange as a derived lemma).
- `.bot`-wrapped variants (`botSimStep`/`botSearchStep`): add a `botT` layer or a
  root flag to `EvalCtx`; sound for the fused rules' reason (the `.bot` is `me`'s
  own body, same `me` throughout).
- Keep the existing fused rules as constructors for compatibility (zero migration),
  or later retire them once `ctxBranch` transports (they become derivable instances).
  **A is then closed under the frozen `Prog` grammar**: every then-path of
  search/ite(/bot) layers over a constant branch is readable, at every depth.

## Integration cost (why this is staged, not done inline)

Adding ANY constructor ripples through (measured via `axKf`'s footprint):
`ProofSystem` (inductive + `Pf.induct` + `Pf_mono`), `Base/Soundness` (`sound_upto`
arm — for `ctxBranch` this is exactly `evalCtx_sound`, already proven),
all censuses (with the `Guarded` swap), and the ENTIRE Decidability chain:
PfB/PfG mirrors + gating (T42), decider legs + soundness + completeness (T44, T31
`decFull`), literal bounds/trichotomy (T48), the tree substrate — ProvT node, size,
extraction machine, normalization, excisor, rawness (~40 arms in T49), instance gate
(T50), gate-parametric decider (T52/T53), zoo re-certification (T54).
Estimate: leaves ≈ mechanical (copy the `eqRefl`/`axKf` arms), `ctxBranch` ≈ real
work in T48/T49 (its conclusion is a fold — the literal/antecedent accounting needs
an `implChain` induction per invariant).

**Recommended order** (each step ends green):
1. ✅ **DONE (2026-07-28)** — Regroup all censuses into `Base/Exclusion` on the
   `Guarded` invariant (pure refactor, prepaying step 2's canary cost). Landed as:
   `TailTo` (+ per-constructor `@[simp]` iffs), `tail_plays_readable` migrated,
   the generic kernel `no_provable_tailTo_floor` (ONE budget-strong-induction; the
   three pair-shaped floor lemmas are now thin instances), and the budget-free
   `no_provable_tailTo_unreadable` (which absorbed the four hand-rolled 22-arm
   censuses in `Theorems/CIMCIC/{vs_DBot,vs_EBot,vs_DefectBot}` and
   `Theorems/DIMCID/vs_CooperateBot` — each is now a ~10-line instance). Six floor
   consumers updated (statement swap only; `simpa [...] using ht` bodies and
   `(by simp)` call sites survived verbatim). Full build green, 3237 jobs.
   **Constructor-addition cost after this step**: ONE new arm in
   `no_provable_tailTo_floor` + one in `tail_plays_readable` (+ sound_upto/Pf_mono/
   Pf.induct as always) — the per-matchup files no longer see constructors at all.
2. ✅ **DONE (2026-07-28, full build green 3237 jobs)** — Family-B leaves `implRefl`,
   `implK` landed as `Pf` constructors (Family B is now 6; 24 total), carried through:
   `Pf.induct`/`Pf_mono`/`sound_upto` (identity/const arms), Exclusion censuses
   (self-annihilating `⟨h1,h2⟩ → h2 h1` arms), PfG mirror + 4 recursor proofs (T42;
   new PfG constructors appended LAST — PfG order ≠ Pf order now), `chkLeaf` checkers
   + firing lemmas + both deciders' completeness (T31/T44/T52), T48 (`pf_posImpl_ant`
   gained the honest size-paid third leg — the leaves' arbitrary spines force it;
   trichotomy cases via the §9 vacuity witness), T49 substrate (2 new ProvT nodes +
   ~20 arm families: boxInvGo consumes `implRefl`'s discharge as the consequent's
   walker, `implK` wraps its first discharge in `weakenImpl` / discards the second),
   T50 transport (trivial gate arms), T51 (`ModChain_not_modest` helper). The spike's
   §3 negative theorem flipped to the positive demo, as predicted.
3. ✅ **DONE (2026-07-28, full build green 3237 jobs) — FAMILY B COMPLETE (8 rules =
   the Hilbert basis for the impl/neg fragment minus the deduction theorem).**
   `contrapose` (1-premise, ungated — its premise is reconstructible from the
   conclusion) rode `chkWeaken` as a second disjunct via an inner match (keeping the
   16-wide decider or-chains and every existing firing proof intact), mirrored in
   `PfG` and as a `ProvT` node; its exclusion arms are trivial (`.neg` tails match no
   plays census). **The key finding: `negElim` is VACUOUS in the consistent `S`** —
   its premises can never coexist by soundness — so it needs NO `PfG`/`ProvT` mirror
   and NO decider leg: every metatheory arm discharges by the soundness contradiction
   (`absurd (Pf_sound h2) (Pf_sound h1)`). Second finding: a machine-crossed
   `contrapose` costs an irreducible `app` node that `crossWt` cannot absorb, so
   `ProvT.dbFree` excludes it (exactly like the ITE leaves) and `boxInvGo` returns
   `none` on its cons stacks — the honest boundary of the crossing-total fragment.
   Congruence twins in T47/T53 extended for the new `chkWeaken` leg (the un-negated
   query stays in the finite space: negs are transparent to `playsArgsF`/`maxLitF`).
4. ✅ **DONE (2026-07-28, build green 3237 jobs)** — landed as `searchChain`, the
   SEARCH-ONLY telescope (`searchPlug`/`searchGuards`/`implChain` in ProofSystem;
   head layer kept in constructor form so the conclusion is always `.impl (.box …) …`).
   Reads `.search`-stacks of ANY depth over a constant branch — subsumes
   `searchBranch` (modulo const-else), goes past `searchThenSearch_t`, PrudentBot3+
   shapes free. Fused rules kept. Carried through: telescope-eval soundness
   (`searchPlug_eval`, ported from the spike), the Exclusion kernel's new `hplug`
   hypothesis (`P ≠ searchPlug L (.const aTgt)` — the telescope's census kill; 3 floor
   instances + unreadable census + 5 consumer files updated), a REAL decider leg (the
   lockstep chain parser `chkChainGo`/`chkSearchChain` with kernel-checked soundness
   and completeness, shared by decFull/decB/decG), T48 size-paid arms, T49 as a
   dbFree-excluded premise-free leaf (its spine has no cores — `implChain_endsInPlays`
   discharges totality/fundamental), and T51's regress via `ModChain_chain_plays` +
   the first-guard-not-modest contradiction.
   **THE OPEN FRONTIER — ite-layer telescopes**: an unrestricted `ctxBranch` with
   `iteT` layers makes probe-implication chains provable (`(opp plays a' vs .bot z) →
   me plays c`), whose antecedents are CHEAP plays-atoms — the Guarded/TailTo census
   cannot price them; blocking mp-extraction then genuinely requires the budget-aware
   "antecedent-provenance" analysis (T48 §10's corrected foundation). That redesign is
   the remaining family-A work; the underlying outcome facts are safe (probe atoms
   stay floor-priced), only the census architecture must evolve again.
5. ✅ **DONE (2026-07-28, build green 3238 jobs)** — `Base/Closure.lean`, the
   kernel-checked closure certificates: `identity_provable` (the gap that drove the
   program, closed), `weakenImpl_from_implK` (Family B's basis is minimal-redundant),
   `searchChain_reads_all_depths` + `searchBranch_from_searchChain` (depth-1 is an
   instance, const-else restriction lifted) and the flagship
   `searchThenSearch_t_from_searchChain` — the stacked-search primitive's exact
   conclusion DERIVED from telescope + boxIntro/boxMono/weakenImpl/impS2. The fused
   rules survive as transcript-cheaper conveniences only.

## THE CLOSURE AUDIT (2026-07-28, after Colomban's challenge) — what "complete" is
## CERTIFIED to mean, family by family, and what remains

**Family B — COMPLETED 2026-07-28 (the honest, certified scope).** LANDED: **S as an
object formula** (`Pf.implS`, 29 constructors) through the full 16-file pipeline
(census-safe by SELF-ANNIHILATION — its antecedent carries its consequent's
structure, like `implRefl`/`implK`; T49 substrate: `freeS2 := False` — it IS the
S-contraction — with a depth-3 raw-app-composition walker `(d1⊛d3)⊛(d2⊛d3)` whose
gate residue `G ψ` and `s2d := 1` keep every ledger exact; `fundamental`'s arm
composes via `Good_app`). **THE DEDUCTION THEOREM is ADMISSIBLE**
(`Base/Closure.deduction_theorem`): `Deriv`-hypothesis derivations discharge to
`⊢ hyp → ψ` by exactly `implRefl`/`weakenImpl`/`impS2` — the S-rule IS the deduction
theorem's mp-case. `identity_from_KS` certifies SKK = I (implRefl now redundant,
like weakenImpl). K+S+mp = the COMPLETE basis of the positive implicational fragment.

TWO PRINCIPLED BOUNDARIES, both discovered and pinned during integration:
* **PEIRCE'S LAW (classical →) is SUBSTRATE-BLOCKED**: sound, census-safe
  (self-annihilating!), but its T49 crossing is `call/cc` — `boxInvGo` is a
  constructive λ-evaluator and `fundamental`'s totality would be falsified (a
  Peirce-leaf with a core-tailed good stack has no constructive walker). **The
  proof-term substrate is intrinsically INTUITIONISTIC**; classical reasoning lives
  at the RULE level (`contrapose`/`negElim` — classically sound arms, no classical
  TERMS). Landing Peirce requires a continuation-passing substrate — research.
* **The classical NEGATION axiom-forms are CENSUS-blocked** (`(¬ψ→¬φ)→(φ→ψ)`,
  `¬¬φ→φ`): their `.neg`-buried antecedents never self-annihilate against a
  plays-census, and with `weakenImpl`+`atomNeg` they make `.impl φ T` provable for
  refutable `φ` — the SAME false-antecedent wall as the ite-ELSE frontier. One
  unified open problem now blocks both remaining expressiveness cells.

So the certified claim: Family B is COMPLETE for the intuitionistic positive
implicational fragment (basis + admissible deduction theorem, kernel-checked), with
the classical extensions blocked by two named, pinned walls — one substrate
(intuitionism of the walker), one census (false antecedents).

**Family C.** CERTIFIED: complete FOR ITS PURPOSE — the HBL derivability conditions
(D1 `boxIntro`, D2 `axK`/`axKf`, D3 `box4`) + `atomBoxImpl` + `boxMono` + the diag
legs suffice to derive bounded Löb IN-ENGINE (`bloeb_engine`), and T54 certifies
every zoo Löb pattern. NOT certified: an absolute criterion such as bounded
GL-completeness ("every GL-provable schema holds under the bounded translation") —
research-grade, unformulated. Known concrete gap that has never been needed:
Σ₁-completeness beyond play-atoms (boxed `eqRefl`/`atomNeg` conclusions).

**Family A.** STATUS AFTER THE 2026-07-28 FRONTIER INTEGRATION — the grid is closed
except one census-blocked polarity:
  (a) MIXED telescopes — CLOSED: `Pf.ctxChain` reads any depth of search+ite-probe
      then-nesting (incl. ite-over-const layers); subsumes `searchChain` and
      `iteBranchSearch_t` (Closure certificates).
  (b) the ELSE polarity (full simulator transparency) — SOUND but census-BLOCKED
      (see the counterexample section below); the census-invariant skeleton (`Bad`:
      box/diag transparency + the self-box exemption) is kernel-validated in
      `ProvenanceSpike.lean` §4 — two of its three walls fall; the implTrans-cut
      leak remains the open edge.
  (c) frame-dependent ite-guards — excluded ON PRINCIPLE (unsound), not by omission.
  (d) composition lemmas — CLOSED: `read_compose`/`simStep_compose`/
      `botSimStep_compose` (Base/Closure.lean) certify that any (sim∘search∘ite∘…)
      nesting with readable inner layers is readable by iterated `implTrans`.
So Family A's certified claim is now: every positive-execution-path reading of the
grammar, at every depth, except the else polarity — which adds NO extractable
theorem and stays out pending the recursive-census research edge.

## THE ITE FRONTIER — CORRECTED ANALYSIS (2026-07-28): NO OUTCOME FLIPS

Working the antecedent-provenance analysis to its end shows the ite-telescope is not
an integration task at all but a MODELING CHOICE:

**RETRACTION of the earlier flip-claim.** The previous draft asserted ite-reading
would flip `llm_outcome_CIMCIC_vs_DBot` to `(C, C)` because the probe antecedent
"CIMCIC plays D vs `.bot DefectBot`" is "cheaply certifiable". That conflated
EVAL-truth with CERTIFIABILITY: the probe is CIMCIC's own Gödelian fall-through —
`search_t` dies on the guard census, `search_f` dies on soundness (the guard instance
is vacuously TRUE), so the probe atom has **no certificate at any budget** —
kernel-checked: `Research/Spikes/family_completion/ProvenanceSpike.lean`
(`cimcic_probe_uncertifiable`). The audit extends across the zoo: every probe
antecedent is Gödelian-uncertifiable, floor-priced above the consuming budget, or
semantically false. **Full ite-reading flips NO current outcome** — it is pure added
expressiveness. What it breaks is the census ARCHITECTURE only: probe chains become
provable with priced-out antecedents, invisible to the Guarded `TailTo` invariant.

The spike also certifies the provenance CORE: `SpineW` (witnessed extraction spines
with exact transcript bookkeeping) + `SpineW.extract` (iterated `mp` at the recorded
cost) + the `mp`-arm ledger arithmetic. The `implTrans` arm does NOT close by naive
extraction (the cut-size wall, as in T48's C2); the correct design is the
SUFFIX-CLASS census: the class = Guarded chains ∪ suffixes of the target's own
telescope conclusions, with per-instance PRICING hypotheses for probe atoms (the
spike's §1 lemmas are those hypotheses for the CIMCIC family) and soundness kills
for guard boxes.

## INTEGRATION OUTCOME (2026-07-28, same day): half (i)+ LANDED, half (ii) BLOCKED
## BY A NEW COUNTEREXAMPLE

**(i)+ LANDED — the THEN-polarity mixed telescope, `Pf.ctxChain` (28 constructors).**
Stronger than the planned (i): ite-layers may sit over CONSTANT then-branches too
(only the else polarity is excluded). Full 16-file integration on the `searchChain`
recipe: `CtxLayer`/`ctxPlug`/`ctxGuard`/`ctxGuards` + the head-explicit constructor
(the conclusion is SYNTACTICALLY an `.impl` — mirroring `searchChain`'s design lesson;
the first, implChain-opaque draft broke T48's `box_inversion` dependent elimination);
`ctxPlug_eval` soundness; the SET-VALUED census kernel `TailToS`/
`no_provable_tailToS_floor` in Base/Exclusion (action-refined per-rule kills, `hibs`
S-closure, `hctx` decomposition discipline) with the singleton kernel re-derived as a
wrapper (+1 `hctx` hypothesis; all 13 consumer call sites discharge it with
`const_ne_ctxPlug`-style one-liners — no statement changed, no outcome moved);
`chkCtxGo`/`chkCtxChain` parser with kernel-checked soundness+completeness wired into
decFull/decB/decG; ProvT node dbFree-EXCLUDED like contrapose/searchChain; T51 regress
via `chainHead_guard_not_modest` (searchL head) + shape contradiction (iteL head);
Closure certificates: `searchChain_from_ctxChain`, `iteBranchSearch_from_ctxChain`
(the fused rule is a DEFINITIONAL instance). Build green, 3238 jobs, T54 re-certified.

**(ii) BLOCKED — the ELSE polarity falsifies the floor censuses beyond finite
widening.** Discovered mid-integration, working the OBot instance: with an else rule,
`implTrans` composes Cupod's own `searchBranch` self-read
`□_k(gC-inst-vs-botCoop) → (Cupod plays D vs .bot CooperateBot)` with OBot's
else-probe chain `(Cupod plays D vs .bot CooperateBot) → (OBot plays D vs Cupod)`
into a PROVABLE, Guarded-classed, box-headed chain to the floor target — so
`no_provable_OBot_D_tail` (and its ∀-chain siblings) would be FALSE as stated. The
probe here is semantically FALSE (Cupod really plays C), so extraction still dies and
the OUTCOME stays true — but every census repair needs the avoid-set closed over
false probes AND the box family `□_n(gC-inst)` AND boxes-of-chains-to-those… and
`axKf` (an impl-factory with arbitrary antecedents and box tails) defeats every
finite widening tried (plays-only sets, truth-conditioned antecedents, box-content
exemptions — each closed one arm and reopened another). The honest characterization:
the else polarity requires the RECURSIVE avoid-set (suffix-class) census — the same
open problem as T50's universal closure, now with a concrete counterexample chain
pinned. Since else-reading adds NO extractable theorem (every probe is priced or
false), deferring it loses nothing except the aesthetic of full simulator
transparency.

**Progress on the block (same day, second pass — `ProvenanceSpike.lean` §4,
kernel-checked):** the census-invariant skeleton `Bad` (chains to `S`-atoms; BOX and
DIAG transparency `Bad(□φ)=Bad(φ)`; the SELF-BOX EXEMPTION `¬Bad α ∨ α = □_n ψ` on
antecedents) resolves TWO of the three walls: the axKf impl-factory self-annihilates
under box-transparency (`bad_axKf_not`, with `bad_boxMono_not`/`bad_box4_not`/
`bad_atomBoxImpl_not`), and the Löb tier is handled exactly (diagF-conclusions leave
the class `bad_diagF_not`; diagB premises stay classed and recursable
`bad_lob_premise`; the counterexample legs stay excluded `bad_not_elseChain`/
`bad_not_boxHeaded`). THE RESIDUAL: the implTrans-cut leak — conclusion `□_n T → T`
(exemption-classed) cut at a Bad ψ: premise-2 `ψ → T` is the provable else-chain
(correctly unclassed), premise-1 `□_n T → ψ` is unclassed-yet-semantically-unprovable
and the arm has no classed premise to recurse into. A principled account of
`□(Bad) → Bad'` implications with UNRELATED content/tail is what's missing.

**Third pass (same day): three more refinement rounds — diag-opacity (gate-recursion
replaces diag-transparency), the TARGET/GUARD sort split (`BadT` acceptance —
separates provable `searchBranch` box-heads from unprovable box-of-target heads,
which no shape condition can), and `boxCore` comparison (excludes the boxMono/box4
factories while keeping Löb premises). Each round closed the mapped hole and exposed
a strictly more exotic one; the current leak is an `impS2` corner at
box-tower-height-mismatched cuts, where one premise is provable via `atomBoxImpl`
and the other is semantically unprovable but unclassifiable. VERDICT: the else
polarity needs cut-elimination-strength machinery over the modal tier — a dedicated
research track (thesis-chapter scale), not an integration task. Family A is
COMPLETE-over-derivable-content; the else cell is expressiveness-only, blocked, and
its attack ladder is fully recorded (`ProvenanceSpike.lean` §4).

**THE WALL'S FIRST OUTCOME CASUALTY (2026-07-28, CIMCIC vs OBot).** The wall is no
longer expressiveness-only: it now blocks a REAL outcome theorem. CIMCIC vs OBot is
semantically DETERMINED `(D, D)` — OBot's play is pure eval (probe1: CIMCIC
cooperates with `.bot CooperateBot`, weakenImpl-provable guard; probe2: CIMCIC
defects vs `.bot DefectBot`, the Gödelian fall-through → OBot's inner else fires D),
and CIMCIC's guard `(CIMCIC plays C vs OBot) → (OBot plays C vs CIMCIC)` is
vacuously-true-but-unprovable. The proof agent PROVED this on 2026-07-27 against the
22-constructor engine (git `621d183`, `CIMCIC_vs_OBot_pass.*`, never landed in the
library) using two hand-rolled right-tail censuses. Post-completion, that proof is
DOUBLY dead: the unguarded right-tail class is falsified by `implRefl` (`⊢ B → B` is
provable and in-class), and even the modern Guarded/TailToS classes are falsified by
`ctxChain` — OBot has a THEN-THEN decomposition
(`probe1 → probe2 → OBot plays C`), and since probe2 ("CIMCIC plays C vs
`.bot DefectBot`") is FALSE over a THEN-readable searcher (CIMCIC's then-branch is
`.const .C` = probe2's action), it cannot enter any tail-set (its `searchBranch`
self-read `□(g') → probe2` is provable-and-classed) — the exact false-probe wall.
The 2026-07-28 re-run agent independently re-derived ALL of this (kernel-verifying
the census-falsifying chains in Lean, transcript in
`app/generated/outcomes/CIMCIC_vs_OBot_fail_transcript.json`) and correctly declined
to propose a constructor (a negative metatheorem is not a rule). Verdict taxonomy:
`open_blocked`, NOT bistable. Consolation: extraction through the new chains still
dies at the false probe, so `(D, D)` remains TRUE — only its mechanization awaits
the recursive-avoid-set census. This raises the wall's stakes from aesthetics to a
concrete bounty: whoever solves it re-earns `llm_outcome_CIMCIC_vs_OBot` (and its
DIMCID sibling).

## Traps (learned while spiking)

- `rw [eval]` fails while the body is still `C.plug …` — `show` the plug-unfolded
  constructor form first (defeq), THEN `rw [eval, if_pos …]`.
- In `ctxBranch`-style certificates, `subst hme` BEFORE introducing the eval witness;
  `rw [hme]` rewrites all three `me` occurrences and misaligns the hypothesis.
- This toolchain: `List.mem_cons_self` takes no explicit args; `ψ ∈ []` closes with
  `nomatch`.
