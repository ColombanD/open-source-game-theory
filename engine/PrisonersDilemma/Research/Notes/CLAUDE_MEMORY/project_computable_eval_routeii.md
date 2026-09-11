---
name: project-computable-eval-routeii
description: "Computable-eval: the project crux. Why eval is noncomputable NOW (axioms-as-IOUs, not Gödel), and why fully-explicit S would make it computable."
metadata: 
  node_type: memory
  type: project
  originSessionId: 9a797e25-2761-4701-b739-b3b6b3b2833b
---

**THE CRUX OF THE WHOLE PROJECT.** Notes: `engine/PrisonersDilemma/Research/Notes/COMPUTABLE_EVAL_NOTES.md`
(authoritative, §0 = Colomban's, §1–4 align). Plan: `~/.claude/plans/i-want-to-go-abstract-wand.md`.

**⚑⚑ O2 WINDOW REFINEMENT (decisive): DON'T flip the defs — DUPLICATE.** Define a NEW
wide predicate family `GoodW`/`GoodStackW` (nil := True, plays-ContentGood enriched)
alongside the old, prove the extended fundamental FOR IT (`fundamentalW`, dbFree-
hypothesized, with GoodD/atomize_halts per the plan below), and leave Good/fundamental/
machine_total/boxInv_total/boxInvT/the-normalization-theorem COMPLETELY UNTOUCHED (the
old IsCore-nil makes iteBranch-states vacuous there — unconditional totality preserved).
Zero downstream ripples; cost ≈ 80 duplicated definition lines. The excisor's crossing-
totality then comes from fundamentalW at the wild-app states.

**⚑ UPDATE 2026-07-03 late (O2 DESIGNED-TO-THE-ARM + transports landed — commit
eab6cd0).** Landed: `boxInvGo_regate_cons` (cons-stacks mono-invisible; statement WITHOUT
casts — impl-typed t directly; sTS-arm needs cases hme) + `atomize_mono` (atom rebuilds
cert with transported bound; struct/app field-identical). **THE O2 WINDOW (one fresh
session, ~450 lines, design COMPLETE):**
(1) Def-flip: GoodStack-nil := True; ContentGood plays-case := `∃ F a, atomizeGo F r.2 =
some a` (THE ENRICHMENT — breaks the fundamental↔atomize circularity: atomize-halting
flows through Good itself). (2) `derivITEFree d` (iteBranch → False; mp/hypSyll recurse)
+ `ProvT.dbFree` (struct → derivITEFree; recursive). (3) `Good_mono (hmm) : Good k t →
Good k (t.mono hmm)`: cases S: cons → regate_cons; nil → cases t: identity-formula arms
(impl/neg/eq: fresh ⟨1, ⟨m', t.mono⟩, rfl, True⟩; plays-atom: fresh cert; plays-struct:
atomize_mono on hcont); computing arms (boxIntro/app/censuses: outputs FIELD-identical —
`cases F` first (stuck matcher on variable fuel!), zero → hrun-contradiction, succ →
exact hrun/hcont). (4) `atomize_halts (u) (hu : Good 0 u) : ∃ F a, atomizeGo F u = some
a`: hu@(nil, plays): ⟨F, r, hrun, hatom⟩; cases u: atom direct; struct → hrun is the
IDENTITY (mkSelf = some ⟨m, u⟩ rfl) ⇒ hatom IS the claim; app → hrun unfolds to the
inner run, hatom + crossFuelMono-part-3 compose. (5) `GoodD (d) (derivITEFree d) : ∀ hd
k, Good k (.struct d hd)` by structural d-induction: mp: nil → rcases derivation_shape
(no box/diag ✓): plays → identity + INLINE atomizability (GoodD-d1-IH at
(struct-d2)::nil gives ⟨F,r,hrun,hatom⟩; atomizeGo (F+2) → atomizeStruct → mp-match →
fuel_mono-rewrite hrun → hatom; compose); impl/eq/neg → True; cons → GoodD-d1-IH at
(struct-d2)::(u::S') (stack-goods: GoodD-d2-IH ∀j + hS); hypSyll: cons → Good_app (GoodD
d1-IH) + GoodD-d2-IH at mat::S'; censuses: dive via hS.1 + census-atom + atomizability
⟨1,…,rfl⟩ + fuel-compose; sim: atomize_halts (hS.1 0) + compose; iteBranch: hfree.elim;
eqRefl/Neg: nil-True, cons index-impossible. (6) Fundamental: + (hfree : t.dbFree);
struct-arm := `GoodD d hfree hd k` (ONE LINE, all stacks); atom-nil → ⟨1, ⟨_, a⟩, rfl⟩
atomizability; sTS-cons → censusSTS-atom atomizability; all formerly-absurd nil-arms →
identity + ContentGood-True; box4-transport → Good_mono. (7) Downstream: DELETE
GoodStack_isCore + Good_of_no_core; GoodStack_of_wellTyped nil → trivial (+dbFree-hyp
threading!! machine_total gains dbFree); diagInv_total/boxInv_total updated;
Good_box_levels's `(by unfold GoodStack; trivial)` still fine. NOTE: fundamental's
statement change (dbFree) ripples to machine_total/boxInv_total/boxInvT/boxInvT_spec/
box_inversion_diet/certify-pipeline?? — boxInvT uses boxInv_total: EITHER thread dbFree
everywhere OR note dbFree-True for iteBranch-free trees and provide `dbFree`-instances…
CHEAPEST: keep OLD boxInv_total name for dbFree-trees; the zoo… iteBranch IS used by
PrudentBot-family ⇒ their trees aren't dbFree ⇒ boxInvT partial there — acceptable,
enumerate.

**⚑ UPDATE 2026-07-03 evening (O1+O3 ✅, sTS census ✅ — commits 9e4e952, a64093f).**
O1: `exciseFix` (iterate to fixpoint, early-exit on gateOKb) + **`certifyExcised`** (the
ONE-CALL pipeline: excise→check→certify, returns Σ' m' PLift (ProvableG (modestGate N)
m' ξ); wild-app demo certifies ✓). O3 BY INSPECTION: axK/diagF/diagB gates
conclusion-tied+size-paid ⇒ only app/implTrans/impS2 cuts can be wild. sTS CENSUS:
`censusSTS` (the node's own premise IS the inner guard cite — two-layer search_t) +
machine cons-arm (substitutable-discriminants match (me,u,tw,hme)) + all five package
arms + regate (cases hme before rfl — stuck inner match). KEY SCOPING FACT: EVERY
Provable-level constructor's discharge state is now total; the ONLY fallback left is
the iteBranchSearch DERIVATION census — UNRECONSTRUCTIBLE without closedP z (its
constructor lacks it) ⇒ the assembly theorem carries that side condition. REMAINING:
O2 (GoodStack-nil := True + ContentGood general := True + fundamental extension with
derivGood-part (induction on d) + atomizeGood-part (wt-strong-induction via crossWt's
strict app-bound) + regate_cons + machine_total unconditional-ish — ~1 session);
O4 (wild middles → app-cuts after outer crossing — check); O5 (the pool lemma).

**⚑⚑ UPDATE 2026-07-03 (D2g-3 ✅ THE EXCISOR — commit 943db77) — walk/check/β-reduce,
demo passes (before: false → after: true).** `contentToTree` (crossing results → trees
of the core judgment; box contents re-box via mono at the subscript; diag falls back) +
`excise fuel Gb` (bottom-up rebuild; gate-failing app-cuts β-reduced through the
machine; TOTAL + judgment-preserving by construction; boxIntro rebuilds carry a
decidable budget-check with identity fallback). THE EXECUTABLE PIPELINE IS COMPLETE
END-TO-END: build/synthesize tree → EXCISE → gateOKb-CHECK → certify ⇒ ProvableG
(modestGate N). REMAINING for full CutRelevance (the final assembly theorem): "for
modest roots the excised tree always passes the gate" — the pool analysis (T43-closure
+ backward-tameness wired through the excisor's walk); plus iteBranchSearch census
(PrudentBot coverage) and strict-k budget conservation. Also still pending: tree
SYNTHESIS from Provable (decFullT) for Prop-level roots; T48/T49 promotion out of
spikes.

**⚑⚑ UPDATE 2026-07-03 (D2g-2 ✅✅ COMPLETE — commit 931699c) — THE DERIVATION-CROSSING
MACHINE LANDS, all conservation packages green.** Stage C executed in-session: the five
conservation theorems rebuilt as packaged strong-fuel-induction proofs over machine +
dispatchers jointly — crossWt/crossS2d/crossWtLt (two-part), crossFuelMono/crossGateOK
(four-part incl. atomize-parts) — original-signature corollaries preserve all call
sites. KEY MOVES: (1) census helpers TERM-MODE over concrete programs (structCross does
`cases hme` first) ⇒ wt/diet/depth reduce by rfl; (2) gateOK's struct-case strengthened
to `derivGateOK` (mp/hypSyll premise formulas join the diet — size-paid ⇒ within
self-calibrated gates; ripples: derivGateOKb + sound, gateOKb struct-arm; toG unaffected
— ProvableG's struct stays ungated); (3) transformation recipe for packaging: extract
old succ-body, `have ih : <ascribed type> := (ihS F (lt_succ_self F)).1`, replace
struct-cons arm with the part-2 appeal, fresh part-2/3/4 bodies (~10 Derivation-arms:
mp/hypSyll via part-1 at F with the pushed-stack hypotheses — derivGateOK components
feed segsOK exactly; censuses destructure the dive + census-def-simp; sim-arms via
part-3). TRAPS: bare `.1`-projections of And-of-∀ need type ascriptions; pasted-body
first-line indentation; part-2's `cases heq` must precede `cases d`. REMAINING:
the excisor walk (cutOKb-check + β-reduce wild cuts via this machine) →
TreeModestRelevance → T47 ⇒ eval computable. iteBranchSearch census = stage 3 (needed
for PrudentBot-shaped zoo coverage).

**⚑ UPDATE 2026-07-03 (D2g-2 stages A✅+B-stashed — superseded, landed).**
Stage A LANDED: `dNodes` (unfold-conserving struct weight: mp/hypSyll count
sub-derivations, leaves 1 — because the mp-arm creates TWO structs from one),
dNodes_pos/le_size, wt/wt_pos/wt_le_budget retrofitted, Formula.size_pos relocated
ahead. Stage B IN STASH@{0}, **MACHINE COMPILES**: mutual
boxInvGo+structCross+atomizeGo+atomizeStruct, all fuel-STRUCTURAL (each dispatcher owns
a fuel tick — WF-recursion would kill the definitional rfls downstream!); census
helpers censusBotSearchStep/censusSimStep/censusBotSimStep landed pre-machine
(censusSearchBranch moved up); iteBranchSearch punted (none). LEAN TRAPS (critical for
resuming): (1) the EQUATION COMPILER cannot refine Derivation/ProvT indices in
multi-discriminant or implicit-underscore matches — TACTIC-MODE bodies (`| fuel+1, …
=> by cases d with …`) refine perfectly; (2) `cases heq` with heq : concrete = VAR
substitutes the var (flip equations so the pattern-side is the var); after cases heq
some pattern binders get substituted away — use `_` in bodies; (3) structCross
signature: (B rest : Formula) → Formula.impl B rest = ξ → …, machine calls
`structCross fuel d _ _ rfl mD u S'`. REMAINING (stage C, ~half session): the 5
conservation theorems' struct-cons arms (wt_le/gateOK/s2d_le/fuel_mono/wt_lt): h :
structCross F d _ _ rfl mD u s = some r — needs STRONG fuel-induction (structCross F
calls boxInvGo (F−1)) or joint four-part statements; per-theorem ~10 Derivation
sub-arms (mp: state-wt (dNodes d −1)+stack ✓; hypSyll: EQUAL; censuses: result-atoms
wt 1/gateOK-via-cert/s2d 0); gateOK additionally needs atomize-parts (cert gateOK from
u's); fundamental/§12-total/machine_total UNCHANGED (vacuous struct-arms). Then the
excisor + TreeModestRelevance.

**⚑ UPDATE 2026-07-03 (D2g-2 prep ✅ — commit c812936) — census reconstruction
VALIDATED; stage-2 design COLLAPSED.** `censusSearchBranch(_of_box)` kernel-checked:
discharged guard box → extracted content (via TOTAL boxInvT) → `PlaysT.search_t` with
the content-TREE as cite + `.const`-branch → `.atom`-tree at c_leaf + c_guard k +
c_node. LEAN NOTE: `subst hme` not `▸` (the discharge's type must rewrite along the
me-shape equation). DESIGN COLLAPSE: derivCross is NOT a separate walker — the
machine's struct-cons arm gets a nested Derivation-match: modusPonens PUSHES its
argument (as .struct-tree) and walks d1; hypSyll materializes like implTrans; censuses
reconstruct inline (searchBranch/botSearchStep via censusSearchBranch-recipe; sim-
censuses need `atomizeGo` — a MUTUAL fuel-def peeling plays-trees to certs past the
identity base: .atom → done; .struct(mp d1 d2) → machine on (struct d1, struct-d2::nil)
then re-peel; .app → machine at nil then re-peel). REMAINING stage-2: the mutual
boxInvGo+atomizeGo extension (existing arms unchanged ⇒ proofs survive EXCEPT
struct-cons arms across the 6 conservation theorems — retrofit like stage 1), then the
excisor + TreeModestRelevance → T47 ⇒ eval computable.

**⚑ UPDATE 2026-07-03 (D2g-1 ✅ LANDED — commit 1ab8477) — general cores + full
retrofit, zero sorries.** The stash was popped and completed in-session: CoreContent
general cores ↦ Σ' trees; identity nil-bases everywhere (full reconstruction);
`mkSelf` + four property lemmas (placed AFTER their dependencies — forward refs fail);
partial-discharge general-core states stay `none` (KEY SIMPLIFICATION: identity returns
conserve everything ⇒ wt_le/gateOK/s2d_le/fuel_mono needed NO signature change — only
wt_lt/regate gained IsCore, one regate call site via `GoodStack_isCore _ hS''`).
RETROFIT TRAPS (for reuse): (1) 12-space inner nil-arms CONTAIN the 8-space pattern as
a substring — python replace mangles them (protect with placeholder first); (2)
fuel_mono's diagB/atomBox base arms need `simp only [boxInvGo] at h; cases h; rfl`
(simp reduces h to a pair-eq; the goal reduces by defeq/rfl after cases); (3) after
`cases (a : AtomT)` the formula is concrete ⇒ cons-stack alternatives become
"not needed" — drop them. NEXT (D2g-2): derivCross per the committed build-spec
(Derivation walker + census cert reconstruction with boxInvT), then the excisor +
TreeModestRelevance → T47 ⇒ eval computable.

**⚑ UPDATE 2026-07-03 (D2g stage 1 WAS IN GIT STASH) — superseded, popped and landed.** The extended machine (CoreContent general cores ↦
Σ' trees; identity nil-bases via full constructor RECONSTRUCTION; `mkSelf` helper for
opaque-formula struct/atom arms; diagF/axKf/sTS cons-nil arms materialize one app-node)
COMPILES with demos passing — stashed because 92 proof-arm retrofits remain across
wt_le/gateOK/s2d_le/wt_lt/fuel_mono/regate. EXECUTION NOTES for the fresh session
(hard-won): (1) @-patterns `t@(.ctor …)` FAIL in the dependent match (namedPattern
type-mismatch) — RECONSTRUCT the constructor with all fields bound instead; (2)
struct/atom have OPAQUE formulas — their nil-identity needs `mkSelf : {core} → ProvT m
core → Option (CoreContent core)` (match on core; box/diag ↦ none) + per-property
mkSelf-lemmas for the proofs; (3) wt_le AND wt_lt must gain `(hc : IsCore core)`
(materialized cons-nil arms ADD one app-node — weight-conservation fails at general
cores; all existing uses are box/diag — pass `trivial`, one call site in §12-total's
diagF); gateOK/s2d_le/fuel_mono stay general (their materialized arms are provable —
gateOK's new obligations come from segsOK + hf); (4) regate gains IsCore too
(identity-returns differ under mono: budgets/nodes differ) — its box4-use derives
IsCore via `GoodStack_isCore _ hS''`; (5) two stacked doc-comments = parse error;
(6) Good/GoodStack/ContentGood/fundamental/machine_total need NO changes (GoodStack-nil
:= IsCore keeps general-core stacks out of Good — general-core totality is a separate
trivial lemma if wanted). Plan: pop stash, rewrite the six theorem regions arm-by-arm,
then stage 2 (derivCross + struct/atom cons-arms + plays-core extraction per the spec).

**⚑ UPDATE 2026-07-03 (D2g READY — commits ff20ebd, e8f87e4) — full-strength
normalization + the executable build-spec.** `machine_total` (T49 §23): EVERY well-typed
state with box/diag core halts (GoodStack_of_wellTyped feeds fundamental element-wise);
`boxInvT` total computable extractor; `box_inversion_diet`. D2g SPEC (CUT_RELEVANCE.md,
census inventory complete): extended CoreContent (plays ↦ Σ' AtomT; eq/neg/impl ↦ Σ'
ProvT-tree; identity nil-bases — restate wt_lt with IsCore); `derivCross` (Derivation
walker: hypSyll composes GATE-FREE — C1 middles tame; modusPonens pushes .struct-wrapped
args; census leaves reconstruct: ALL search-censuses have .const branches ⇒ certs =
PlaysT.const + search_t; T49-PlaysT takes ProvT-guards DIRECTLY ⇒ plug boxInvT content
straight in, diet via box_inversion_diet; simStep extracts the discharge's AtomT
(plays-core, mutual); iteBranchSearch_t needs closedP z (substP_id — free for modest));
totality/diet rerun the §19–21 Good pattern (general bases terminal). KEY DISCOVERY: N₀
self-calibration ⇒ ONLY fresh-atom middles in implTrans/app/impS2 are genuinely wild
(C0 covers logic-layer literals; axK/diag premise-gates conclusion-tied). Then excisor →
TreeModestRelevance → T47 ⇒ eval computable. D2g = pattern-execution, 1–2 sessions.

**⚑⚑⚑ UPDATE 2026-07-03 (D2f-b ✅✅ THEOREM PROVEN — commit 9161231) — `boxInv_total`:
THE NORMALIZATION THEOREM IS KERNEL-CHECKED, UNCONDITIONAL, ZERO SORRIES.**
`boxInv_total : ∀ t : ProvT m (.box c ψ), ∃ fuel, (boxInv fuel t).isSome` — no
contraction-freedom hypothesis. The extraction machine weakly normalizes on every
well-typed box judgment: BOUNDEDNESS DEFUSES THE LÖB/Y-COMBINATOR. Proof = the §8
design verbatim (T49 §19–21): Good/GoodStack/ContentGood on lex (k, μ(box)=0, phase);
fundamental lemma by structural induction (16 arms, FIRST-PASS COMPILE): contraction
free (impS2's discharge hypothesis used twice), diagF composed at max-fuel+1 via
fuel_mono, modal leaves via Good_box_levels (cumulative determinism — hd (j+1) + det
gives content-goodness at every j ≤ k−1), box4 via regate-transport. The fundamental
lemma gives FULL weak normalization (every state, every good stack). Plausibly the
FIRST normalization theorem for a bounded provability logic — the paper is real.
REMAINING to CutRelevance (all mechanical now): excisor/spineCross totality on the same
Good-machinery, TreeModestRelevance for zoo roots, plug into T47 ⇒ Provable decidable ⇒
proofSearch computable ⇒ EVAL COMPUTABLE. Also: promote T48/T49 out of spikes;
per-instance certify-pipeline already executable.

**⚑ UPDATE 2026-07-03 (D2f-b FORMALIZATION UNDERWAY — commits 4f507b0, 6b60d6f) — the
`Good` DEFINITION COMPILES.** Part 1 (T49 §19): `muF` (μ(box)=0!), `DStack.mu_core_le`,
`boxInvGo_fuel_mono` (+`boxInvGo_det` — fuel-determinism: ∀j≤k instantiations speak
about the SAME content), `boxInvGo_regate` (machine ignores root gates ⇒ Good transports
along mono; proof: cases t, atom-arm needs nested `cases a` first, rest rfl). Part 2a
(T49 §20): **Good/GoodStack/ContentGood as mutual WF-def on lex (k, muF ξ, phase)
ACCEPTED** — Good = biorthogonal (∀ good stacks: halts + ContentGood); GoodStack nil :=
IsCore core (makes Good VACUOUS at plays/eq/neg — never-run trees); cons := (∀j≤k Good j
d) ∧ rest (cumulativity replaces the antitonicity lemma — with determinism, different
j-instantiations give the same content at every level!); ContentGood box := k>0 →
Good(k-1) content (Nakano ▷), diag := Good k unfold (μ-descent). LEAN TRAPS: (1)
decreasing_by: bullets inside `first`-alternatives misparse — use TERM-MODE lex helpers
(lex_fst/snd/thd/le_lt/le3 with explicit `Prod.Lex (·<·) (Prod.Lex (·<·) (·<·))`); (2)
rename_i grabs match-auxiliaries — omega reads inaccessible hyps directly, use `(by
omega)` for context-≤s; (3) `simp [muF]` may CLOSE goals leaving omega stranded — `simp
only [muF]; omega`; (4) mutual per-function termination_by tuples must share one type.
REMAINING for BoxInvTotal: application lemma + 16-arm fundamental lemma + k:=1
corollary — mechanical, one session, pattern established.

**⚑ UPDATE 2026-07-03 (D2f-b LEMMA C DESIGNED — commit 4ab7be2) — THE INDEX CLOSES.**
Two inventions repair all nine failed routes at once: (1) **μ(box) := 0** — boxes are
ATOMS for the formula measure because crossing them decrements the guard index k instead
(the box-guard IS Nakano's ▷): hence μ(diag-unfold) = μ(tgt)+1 < μ(diag) = μ(tgt)+2 —
the negative recursive occurrence hides behind a box and formula recursion becomes
well-founded; (2) **∀j≤k cumulative arrows** — antitonicity definitional (fixes
mixed-variance; needed at box4). Good/GoodStack/ContentGood by WF-recursion on lex
(k, μ): arrows/stack-cons by μ, box-CONTENT quality by k (HALTING demanded at EVERY
level incl. k=0 — only quality degrades), diag-content same k by μ. Fundamental lemma
(∀k-motive, structural on trees, 16 arms) checked on paper: impS2 free (hypothesis
reuse), diagF closes circle-free (dive content Good at SAME k, applied to the
□-discharge), axK/axKf levels match exactly at k−1 + application lemma, box4 via
antitonicity, plays-ended/eq/neg VACUOUS (no good stacks — never-run trees).
BoxInvTotal = fundamental at k := 1. Design risk ZERO modulo Lean engineering
(WF-recursion via termination_by (k, μ ξ); antitonicity; application lemma; 16-arm
fundamental with a step-composition lemma; 1–2 sessions).
`BOUNDED_LOB_NORMALIZATION.md` §8 = the full design (the paper's proof skeleton).

**⚑ UPDATE 2026-07-03 (D2f-b THE Y-FINDING — commit b69bdf6) — diag is a NEGATIVE
recursive type; the theorem = defusing the Y-combinator.** The Lemma-C design attack hit
bedrock: `.diag g tgt ≅ (□g D) → tgt` with D in ANTECEDENT position — the Curry/Y
recipe; negative recursive types make normalization FALSE in general; the Löb fixpoint
IS Y at the modal level. This explains ALL prior failures at once (formula recursion,
type-order, Tarski — they fail for Y) and pins the novelty: BOUNDEDNESS DEFUSES Y via
exactly two kernel-checked facts: the Löb cap (contents ≤ subscript) and STRICT
consumption (`boxInvGo_wt_lt`, T49 §18, NEW: extraction returns strictly lighter
material — contraction-free hyps exact). Y-escape routes closed: literal self-reference
impossible (finite trees), dynamic regeneration impossible (strictness), unfold-chains
strictly descend. Sole remaining divergence candidate: impS2-duplication feeding
unfolds — the Tait ∀-quantification's job. Truth-conjecture: BoxInvTotal TRUE.
Research doc `BOUNDED_LOB_NORMALIZATION.md` has the full statement, 9-route failure
map, 3-lemma plan (Reach-closure, Good-with-reachable-args, fundamental), §6 the
Y-analysis. Also NEW route-failures recorded: Prop-level bypass (soundness one-liner
`Provable m (□cψ) → Provable c ψ` — worth knowing! — but wild-cut app still needs the
crossing) and Knaster-Tarski (diag-operator ANTITONE — two polarity flips).

**⚑ UPDATE 2026-07-03 (D2f-b deep-dive — commit 6331ae6) — the ROUTE-MAP + the
QUANTITATIVE LÖB CAP.** Seven normalization techniques pushed to exact failure points
(note has full detail): local charges (stack×stack), Tait-on-formulas (.diag is a
RECURSIVE type — unfolds to impl(box g diag) tgt containing itself), type-order
(order(diag)=∞), step-indexing (safety≠termination), budget-indexed Tait
(arrow-quantification unbounded), counting/towers (nested contraction), fragments
(app(axKf-leaf, Löb-arg) violates stack-monotonicity). VERDICT: normalization for a
bounded-Löb modal proof calculus — plausibly NOVEL (GL lacks cut-elim; boundedness
restores it), paper-sized, needs offline iteration; thesis proceeds via instance route.
LANDED (T49 §17): wt(sTS) := 1 (cite-jumped premise never walked);
`ProvT.wt_le_budget` (walkable weight ≤ judgment budget — every gate pays ≥1/node;
helpers Formula.size_pos, PlaysT.cost_pos); **`content_wt_le_subscript`** — box contents
weigh ≤ their own subscript: □g(diag g tgt)-unfoldings all yield material of weight ≤ g,
SAME g pinned by the formula ⇒ diag unfold-chains weight-capped at fixed formula — the
well-foundedness leg for the future Tait diag-case. LEAN NOTE: size_pos-instantiations
need bound constructor variables (underscores in the formula args = unsynthesizable
placeholders).

**⚑ UPDATE 2026-07-03 (D2f-c ✅ — T49 §16, commit c69bff9) — EXECUTABLE diet
certificates.** `gateOKb` (Boolean mirror of the cut-diet check, full mutual triple),
`gateOKb_sound` (bridges Gb to any G it underapproximates; instantiate cutOKb N via
cutOKb_iff), and `certify : gateOKb (cutOKb N) t = true → ProvableG (modestGate N) k φ`
(via toG). Pipeline runs live: #eval extracts + checks (true at modestGate 2).
PER-INSTANCE CutRelevance = build tree → excise → check → certify, all executable.
MISSING for zoo-scale: tree synthesis (decFullT-style Option-ProvT-returning decider, or
hand-built trees for flagship cooperation theorems) — the natural next component.

**⚑ UPDATE 2026-07-03 (D2f-b VERDICT + consolidation — commits 2432391, 308821e).**
Machine groundwork: diagF continuation INLINED ((x, d2::S'') directly — appNode-charge
gone from the measure design space); `ProvT.s2d`/`mono_s2d`/`boxInvGo_s2d_le` (extraction
never increases contraction depth, unconditional — 4th machine-induction, compiled first
pass: the proof pattern is rote now). THE MEASURE VERDICT (post-inlining re-check): the
failure is deeper than diagF-promotion — even Φ-CONSERVATION breaks at the axKf LEAF
(result app(r1,r2) = Φd1·(Φd2+2), stack×stack product, premise-free leaf has only a
constant charge). **Every local-charge scheme is provably insufficient** — contraction
cost depends on discharged material unknown at the node. Routes: (i) Tait computability
over ProvT (honest SN, heavyweight); (ii) Gentzen rank on segment formulas; (iii)
per-instance fuel — machine semidecides, zoo trees excisable by #eval with per-theorem
certificates (E-grade without SN). Roadmap + CLAUDE.md consolidated with the full D-arc.

**⚑ UPDATE 2026-07-03 (D2f-a′ ✅ — T49 §14, commit f6b7619) — gate instances + the
contraction-measure MAP.** `litGate_box_closed`/`modestGate_box_closed` (both
box-content-closed ⇒ §13 applies; maxLitF box = max n ·, modestF ignores subscripts);
§12's closed-form fuel #eval-validated. D2f-b FRONTIER (note has full detail — start
there): measure attempts with exact failure points: (1) linear-stack Ψ = Φ(t)(1+ΣΦdᵢ)
with multiplicative node-charges Φ(impS2 tf tx) = Φtf(Φtx+2), Φ(app f x) = Φf(Φx+2)
closes impS2/app/weaken/implTrans STRICTLY but breaks on diagF (extracted tree promoted
to WALKER over the tail ⇒ triple products); (2) fully-multiplicative Ψ = Φ(t)·Π(Φdᵢ+2)
closes diagF but impS2's duplicate is QUADRATIC in ΦdB — no dB-independent node charge
pre-pays it; (3) semi-multiplicative same. RESOLUTION SHAPE: stratify by s2depth —
multiplicative below walker depth, linear at-or-above; depth-indexed Ψ_d family, outer
induction on d, depth-0 = the proven boxInvGo_total. Or shared-environment/mix. One
fresh design session, then one Lean session. Then spineCross + TreeModestRelevance.

**⚑ UPDATE 2026-07-03 (D2f-a ✅ — T49 §13, commit 0a3fe0a) — cut-diet bookkeeping:
extraction preserves the gate UNCONDITIONALLY.** `boxInvGo_gateOK`: input tree + stack
pass G, stack segments pass G, G box-content-closed (G (□b ψ) → G ψ — litGate/modestGate
✓) ⇒ extracted tree passes G. THE ALIGNMENT: every materialized app's gated argument is
a stack segment whose G comes from the node that PUSHED it (app's G φ, implTrans's G ψ,
impS2's G ψ) — the ProvableG gates and the machine's materializations fit exactly;
axK/axKf leaves consume segment-box CONTENTS (the one closure hypothesis). Holds for ALL
trees incl. impS2 — only totality needs freedom; diet safety is unconditional. Dives
never leak exotic cuts. D2f-b OPEN (last gap to full BoxInvTotal): contraction
totality — insight: every duplication runs under a strictly SHALLOWER impS2-walker
(arm→tf at depth−1; duplicate consumed inside tx's walk at depth−1) ⇒ tower fuel
~wt·2^(2^D) EXISTS; unresolved: deep-discharge-in-stack (d_dB > d_t — its depth drops
only at its own consumption); routes: DM-stratified weight vectors or
shared-environment/mix. Then spineCross, TreeModestRelevance → T47.

**⚑ UPDATE 2026-07-03 (D2e-2 ✅ — T49 §12) — THE MASTER TOTALITY THEOREM lands.**
`boxInvGo_total`: contraction-free states + box/diag core ⇒ the machine halts with
`some`; corollary `boxInv_total_of_freeS2`: BOX HONESTY IS TOTAL on the free fragment
with closed-form fuel (wt t + 1)² + wt t + 1. PROOF ARCHITECTURE (reusable): induction
on FUEL alone — every call burns one unit; the lex measure (potential, wt t) lives in
threshold ARITHMETIC not in the induction: helpers thr_step (potential drops: (P'+1)² ≤
P·P via Nat.mul_le_mul + expand (P+1)² = P·P+2P+1 via succ_mul/mul_succ + omega) and
thr_same (implTrans: same P, smaller tree). none-arms close by IsCore reduction, DStack
index chasing, EndsInPlays.no_core_stack (derivation_shape). LEAN TRAPS: (1) pin
thr_step's P' := explicitly or omega sees metavariables; (2) `cases hd : e` substitutes
e in the GOAL — later `rw [hd]` finds nothing; use `obtain ⟨r, hd⟩ :=
Option.isSome_iff_exists.mp` + rw instead; (3) Nat.le_of_succ_le_succ aligns +1+1 ≤ F+1
threshold shapes; (4) don't reference cases-eliminated explicit constructor budgets (K
unified with the outer index). REMAINING for full BoxInvTotal: ONLY the impS2 case
(modest-pool ranks / bounded-contraction fuel). Then: gateOK bookkeeping, spineCross,
TreeModestRelevance → T47 decider.

**⚑ UPDATE 2026-07-03 (D2e-1 ✅ — T49 §11, commit 02ce701) — the totality toolkit:
extraction never manufactures weight.** Landed: `ProvT.wt`/`DStack.wt` (walkable weight —
atom certs/Derivations terminal, count 1), `freeS2` (no impS2 in the walkable layer),
`mono_wt`/`mono_freeS2` (re-gating preserves both, rfl per arm), and the JOINT lemma
`boxInvGo_wt_le`: on contraction-free states, the extraction result weighs ≤ the state
consumed AND is itself contraction-free (prove them TOGETHER — the diagF recursion needs
the freedom of extracted trees; both halves fail on impS2, so the hypotheses are exact).
LEAN TRAP (major): the machine's combined deep dependent match (t + multi-layer stack
patterns) DEFEATS the equational-theorem generator ⇒ `simp only [boxInvGo]` dead ⇒
restructured: match the TREE first, stacks in small nested per-arm matches (one dependent
match per constructor) — equations generate, simp fires. Also: no type-ascriptions on
nested dependent matches (blocks core-refinement); tactic `match t, s with` in proofs
breaks hypothesis types — use `cases t with` + nested `cases s`. D2e-2 NEXT: master
totality `boxInv_total_of_impS2Free`, strong induction on lex (wt t + wt s, wt t), fuel
threshold θ(P,T) := (P+1)² + T (per-arm arithmetic verified on paper), ≤-quantified form
absorbs fuel-monotonicity; includes none-arm uninhabitedness for box/diag cores.

**⚑ UPDATE 2026-07-03 (D2d ✅ — T49 revised) — totality audit caught a LOOP; Löb pair =
second core; the ledger is written.** The original diagF arm (apply-self) returns to its
own state in 2 steps — sound but totality-fatal (fuel-partial designs HIDE loops: audit
arms against a measure before trusting them). FIX: `CoreContent` extends extraction to
`.diag` cores (content = the implication it abbreviates, budget-free); `diagB`+stack is
the diag BASE (its discharge IS the content); `diagF` extracts its diag discharge's
content and applies it — strictly decreasing. #eval: extraction through a full
diagF/diagB fixpoint pair to a real box ✓ at the subscript. TOTALITY LEDGER (measure
W = |t|+Σ|stack|): app −1; weaken −1−|d|; implTrans 0 but |t| down (lex (W,|t|)); diagF
strictly down; dives fresh-smaller; leaves terminal; SOLE obstruction = impS2 (+|d|,
Gentzen contraction). All none-arms have UNINHABITED state types for box/diag cores.
D2e PLAN: `boxInv_total_of_impS2Free` via `∀ W, Ψ(t,s) ≤ W → isSome (boxInvGo W t s)` —
the ≤-quantified form ABSORBS fuel-monotonicity (no 15-arm mono lemma!); then impS2 via
modest-pool ranks; then gateOK bookkeeping, spineCross, TreeModestRelevance.

**⚑ UPDATE 2026-07-03 (D2c ✅ — T49 §9–10) — `boxInvGo` RUNS: fueled box-content
extraction, correct by construction.** The spine machinery collapsed to a STACK MACHINE:
`DStack ξ core` (dependent discharge stack for ξ's impl-spine), push at app, drop at
weakenImpl (excision), compose at implTrans, duplicate at impS2 (FUEL absorbs the
Gentzen contraction — no termination proof needed, the decFull pattern), apply-self at
diagF, consume at modal leaves where EACH GATE PAYS ITS OWN EXTRACTION (axK/axKf at
a+b+|α| ≤ c; box4 re-boxes mono-lifted content at a+|□aφ| ≤ b; boxMono passes a ≤ b;
boxIntro's subscript IS the content budget). Return type COMPUTED from the core
(`BoxContent : Formula → Type`, box ↦ Σ' m' ≤ c ProvT m' ψ, else PEmpty) ⇒ every `some`
correct by construction: BOX HONESTY — contents derivable within their own subscripts.
#eval demos extract through real trees (direct + app/weaken detours) at exactly the
subscript. LEAN TRAP: dependent match over DStack GENERALIZES AWAY the core's
box-structure (index generalization) — computing the return type from the core fixes it
with zero casts; shape-excluded arms return `none` (sound; unreachability = totality's
job). Remaining: `BoxInvTotal` (fuel sufficiency — modest-pool rank argument), cut-diet
bookkeeping of extracted trees, spineCross on the same machine, TreeModestRelevance.

**⚑ UPDATE 2026-07-03 (D2b-probe ✅ — T49 §8 + note §5g) — THE REDUCTION TO ATOM MODESTY
+ the Gentzen wall.** Kernel-checked: `ProvT.box_size_le` (only boxIntro/app conclude
boxes, both pay their conclusion; Type layer concludes no box via T48.derivation_no_box;
T49 now imports T48) and `ProvT.box_subscript_lt` (budget-k boxes have subscript < 2^k —
the compression ceiling; proof via Nat.log2_lt, positivity side-goal by omega not
Nat.pos_iff). THE REDUCTION (§5g): C0 (cuts < 2^local-budget, logic budgets descend) +
compression ceiling + backward-tameness ⇒ literal half FREE at N₀ := 2^max(k, maxLitF φ)
+ maxLitF φ; escalation channel = cite budgets from CUT ATOMS' fresh programs only ⇒
**conjecture ⟺ some minimal tree's cut atoms stay in the root's program pool** = atom
modesty = exactly what T43 polices. Fork (B) is the main road. THE GENTZEN WALL:
spineCross structural on t1 EXCEPT discharge-diving bases (axK/axKf/box4/diagF dive
contents) and impS2 DUPLICATES its head discharge ⇒ total-size termination fails;
strict-k budgets SURVIVE if excision is per-subtree-budget-preserving (duplication was
already paid by the wild tree). Failed fork-(C) forcings (recorded): nested compression
(root absorbs via maxLitF φ), fresh-provable-middle (axKf pairing forces root to carry
its own wildness). D2c PLAN: box_inv on trees (axK-dive pays its own gate a+b+|α| ≤ c);
spineCross with segments/discharges in the T43 pool (finite ranks ⇒ termination cheap);
assemble TreeModestRelevance for zoo roots → T47 decider.

**⚑ UPDATE 2026-07-03 (D2a ✅ — T49 §7 + note §5f) — excision toolkit layer 1 + the D2b
design.** Landed: `ProvT.mono` (budget monotonicity = root re-gating only, structure
reused — every constructor's conclusion budget sits in ONE relaxable ≤-gate; boxIntro's
explicit budget arg must be `_` in the rebuild), `mono_gateOK` (diet preserved, all arms
Iff.rfl), `impl_size_le` (every impl node pays its conclusion size; atom arm `nomatch`;
struct via `Derivation.concl_size_le` in BaseTheorems), `cross_weaken(_gateOK)` (first
excision: weakenImpl-headed apps drop their argument — kills all §5e counterexamples).
THE D2b DESIGN (note §5f, worked on paper): (1) SUBSCRIPTS ARE BACKWARD-TAME through
gates (axK/axKf: a+b+|α| ≤ c; boxMono: a ≤ b; box4; search rules pin to goal literals) —
budget-compression can't cross tame interfaces; (2) CONTENT IS BACKWARD-TAME through
shapes (atomBoxImpl/axKf/box4/boxMono/censuses put B's content inside α — crossing arms
vacuous; only weakenImpl + recursive arms survive); (3) BUDGET WALL: β-style rewriting
exceeds budgets (materializing intermediates re-pays cut sizes) — FIX: spineCross carries
impl/argument pairs abstractly, returns ≤ m₁ + Σmᵢ + |α|, consumer pays target once;
(4) MASTER STATEMENT: spineCross (impl-spine over segments with tame final target +
discharge TREES per segment ⇒ tame-cut tree), mutual with the main tameness induction —
dodges all three §5e refutations because it holds trees, not judgments. Sub-questions:
diagF/B's free fb (gate absorbs), atom guard cites (maxLitF_subst keeps tame),
struct-embedded mp/hypSyll chains (C1's DAnt).

**⚑ UPDATE 2026-07-03 (D0+D1 ✅ — T49TreeSubstrate.lean) — fork (A) taken; the TREE
SUBSTRATE is live.** Type-valued mirror triple `PlaysT`/`AtomT`/`ProvT` of
PlaysProof/AtomProvable/Provable (constructor-for-constructor; struct carries its
Derivation witness explicitly), with `sound` (mutual theorem, structural match — compiles
directly) and `complete` (`Provable k φ ↔ Nonempty (ProvT k φ)`, mutual Prop match into
Nonempty — also direct, no positional .rec needed). `gateOK G t` = the cut diet of ONE
tree (six T42 gate positions + the atom layer's search_t/search_f guard cites); `toG`
transfers a passing tree into `ProvableG G`. THE OFFICIAL REDUCTION:
`tree_cutRelevance : TreeCutRelevance N₀ → CutRelevance N₀` (+ `tree_modestRelevance`),
where `TreeCutRelevance N₀ := ∀ k φ, Provable k φ → ∃ t : ProvT k φ, gateOK (litGate (N₀
k φ)) t` — an ∃-over-trees statement that dead implications CANNOT refute (excision may
replace the tree). LEAN NOTE: mutual Type-inductive + mutual theorems by match worked
first-try; gateOK needed explicit `{k} → {φ} →` binders before the match discriminant;
names ProvableG/litGate/modestGate need `open PD.T42 PD.T44`. NEXT (D2): tree
weight/measures, live sub-judgments, the excision lemma (dead subtrees removable, weight
decreasing), assemble TreeCutRelevance for zoo roots — or the forcing that defeats
excision (undecidability).

**⚑ UPDATE 2026-07-03 (C3b-ii′ ✗ KERNEL REFUTED — T48 §11, note §5e) — the judgment-local
program is CLOSED.** Probing HBoxHead before building on it (the §5c lesson, applied):
FALSE, kernel-checked. `deadJ : Provable 10000 (.impl (.box 300 ψ₀) (.box 1000 eqCD))` —
a DEAD implication (both sides unprovable, never fires via app) with wild ψ₀ and tame
unprovable consequent, refuting HBoxHead AND the head-level dichotomy at an UNGUARDED HEAD.
Recipe (the wild-injection tool): eqRefl makes provable formulas with arbitrary search
literals (`wildA := .eq wildQ wildQ`); weakenImpl plants arbitrary antecedents;
boxIntro+axK distribute into box-antecedent position; impS2 vs free axKf composes away the
middle. NO PAIRWISE REPAIR: budget-bounded degeneracy fails even for LIVE pairs (box
subscripts are BUDGET COMPRESSORS — .box c χ has size ~log c but asserts budget-c
provability); unbounded degeneracy is trivial. Three refutations total (§9 vacuity, §10
content/guarded-tail, §11 unguarded-head): every informative judgment-local statement is
false, every true one empty. CONJECTURE SURVIVES (counterexamples are excisable dead
weight). THE FORK (next session): (A) tree-level minimality/EXCISION — weighted derivation
trees, live sub-judgments, dead-subtree removal; live judgments carry real app-siblings
(the guard context §5d wanted, with witnesses); (B) specialize (A) to zoo-universe roots
(all decB needs); (C) undecidability via box budget-compression (maxLitF counts box
subscripts ⇒ compressed cuts are exotic; force tame goals through them ⇔ defeat excision).
(A) and (C) are the two faces of: is excision always possible?

**⚑ UPDATE 2026-07-03 (C3b-i′ ✅ diagnostic RESOLVED BY REFUTATION — T48 §10, note §5d).**
The linked trichotomy is FALSE, kernel-checked twice: `ppair_linked_false` (axKf is
premise-free ⇒ its consequent-box content is ARBITRARY ⇒ box-content pairs defeat any
judgment-local lemma — boxT descent must go; contents sourced only at consumption via
box_inversion) and `spine_boxlinked_false` (guarded tail pairs — behind undischarged
antecedents — carry NO pairwise info even granting the box escape its content link; guard
context is NECESSARY). Cheap unprovability helpers via double soundness:
`eq_const_unprovable`, `box_eq_unprovable` (interp .box = Provable ⇒ Provable_sound twice).
THE CORRECTED FOUNDATION (C3b-ii′, next): (1) motive = pairs with guard context
`PosImplCtx φ Γ B C` (hypothesis: all of Γ provable — supplied by discharge siblings at
apps); (2) BUDGET-strong-induction with inversion, legal because pair-queries never cross
cites (checked rule-by-rule) — kills the D2/opaque-witness wall (smaller-budget judgments,
same strong IH), no transform-carrying; (3) single kernel
`HBoxHead : Provable m (.impl (□b₀ ψ₀) C) → (Tame C → Tame ψ₀) ∨ (∃ m' ≤ m, Provable m' C)`
— heads are unguarded, producer census applies (searchBranch/chains/axK-premise/discharged
axKf); on paper all arms close given HBoxHead. Deliverable: `HBoxHead ⇒ full dichotomy`,
then HBoxHead itself (box-depth induction) — or its failure = the undecidability entry.

**⚑ UPDATE 2026-07-03 (C3b-i ✗ RETRACTED — commit 5593acb) — `Tri` was VACUOUS.** External
review (Opus) caught it; kernel-confirmed at full strength: `Tri_always` (T48 §9) — the
DboxMid/DboxPos disjuncts never mention the analyzed pair, one fixed box4 witness inhabits them
for EVERY input, so `tame_trichotomy` follows in one line with no induction. THE LESSON (note
§5c, internalize this): unlinking an escape disjunct to make compositions close = making it
`True` = making the theorem hollow; composition pressure is the SIGNAL that pairwise
judgment-local statements can't carry the info — keep links, treat breaking arms as real lemma
obligations. Same disease milder in C2's `PAnt.axkPair` (trivial on box-box pairs, leaks via
trans). STILL STANDING: C0/C1/C2-nonbox/C3a, maxSLit machinery, gate_bound, all of T3/T4.
CORRECTED COURSE (C3b-i′, note §5c): (1) LINKED trichotomy diagnostic — tight target
`(Tame C → Tame B) ∨ (∃ b ψ₀, B = .box b ψ₀) ∨ degenerate`, rerun the arms, HARVEST the
breakage list (predicted: box-middle compositions in implTrans/impS2 heads; premise-free rules'
consequent-content pairs); (2) box-chain grounding lemma — `.impl (□ψ₀) χ` with χ NON-box:
producer census forces ψ₀ = guard-subst (tame rel. χ) ∨ degenerate; all-box chains recurse on
consequent box-depth. If grounding fails → the undecidability-encoding entry point.

**⚑ UPDATE 2026-07-03 (C3b-i, WITHDRAWN — see above) — the tame trichotomy (T48 §8, commits 8faead9+7ceac01).**
`tame_impl_trichotomy : Provable m (.impl B C) → Tri L m B C` with Tri = D1 (maxSLitF C ≤ L →
maxSLitF B ≤ L, IMPLICATIONAL — composes) ∨ DboxAnt (B a box — sibling-resolvable at discharge
app) ∨ DboxMid (box-antecedent pair recorded in a judgment — the implTrans-box-middle KERNEL) ∨
DboxPos (box-interior pair of a judgment — box_inversion-resolvable) ∨ D2 (degenerate ≤ budget).
Over PPair (spines + ONE box-content descent). KEY: obstruction disjuncts are SELF-CONTAINED
(own witnesses, no ambient-pair reference) ⇒ compositions pass verbatim ⇒ the 26-arm induction
closes. Degeneracy reassemblies (implTrans/impS2) fit ORIGINAL budgets via Provable.app. The
conjecture's residue = exactly the 3 box obstructions. NEXT (C3b-ii): thread carried transforms
through Tri; resolve DboxAnt/DboxPos via siblings/box_inversion; DboxMid = the open kernel
(side-induction on middle's box-structure or D2-absorption via wildness-confinement).
LEAN TRAP (cost a near-loss): `grep -c` exits 1 on zero matches — an && chain aborted and a
trailing `cp backup` restore CLOBBERED uncommitted work; ALWAYS use `;` separators around greps
and re-make backups fresh per turn (recovered by re-applying from the transcript).

**⚑ UPDATE 2026-07-03 (T4.1b C3b-SPEC — the split measure) — CUT_RELEVANCE.md §5a′.**
THE BREAKTHROUGH: cite targets are ONLY .search literals of programs; box/diag SUBSCRIPTS never
become budgets (boxes never opened) ⇒ the tameness invariant tracks `maxSLitF` (T48 §7: defs +
subst-lemma + split-lemma `maxLitF ≤ maxSLitF + 2^size` + `gate_bound`). Consequences: budget
invariant M = max k L holds; diagFInner/boxMono/axkf-head/axK-head all become genuine D1; the
trichotomy: D1 (Tame C → Tame B — IMPLICATIONAL, composes through chains where absolute doesn't)
∨ D2 (degenerate-w/-carried-transform) ∨ D3 (ONLY axKf's tail pair; shape-recorded; patched at
its discharge-app — peel order: compositions preserve head antecedents so the matching sibling
(.box a (.impl ψ₀ α₀)) always arrives first; its boxT-content-pair supplies the link). Wildness
confinement = the truth of the theorem: census steps are maxSLit-NONINCREASING ⇒ wild can't
antecede tame non-degenerately; D2 bypasses. TARGET:
`Provable k φ → ProvableB (2^(max k (maxSLitF φ) + 2)) k φ`. REMAINING: PPair (impl-tails +
ONE box-content descent — deeper box interiors never consumed) + the master Provable.rec
(~26 arms; 3×3 subcases at implTrans/impS2 heads — all verified on paper: D2 absorbs, D1
composes, D3 passes; app-arm patches D3 by sibling-shape-match). Then modesty via enriched Tame.

**⚑ UPDATE 2026-07-03 (T4.1b C3b-DESIGN, earlier pass — superseded by §5a′) — the master induction's shape.**
CUT_RELEVANCE.md §5a — start C3b HERE next session. Three load-bearing refinements: (1) BUDGET
INVARIANT: formula-tameness (maxLitF ≤ L) ⇒ all cites ≤ L ⇒ ALL budgets ≤ M := max k L ⇒ FIXED
N₀ := 2^(M+2), no aggregation; tameness threads DOWNWARD (premise formulas = conclusion-material
∪ cite-substs ∪ census-antecedents ∪ cuts-resolved-by-dichotomy). (2) The literal half STILL
needs the census (a 2^M-literal cut's cert obligations cite its own guards at ~2^M — tower
restarts; only ≤L-tame cuts keep cites ≤ L). (3) Holes don't compose through PAnt.trans ⇒ NO
generic PAnt_lit lemma; the merged motive carries hole-info: THREE components — transform ∧
pair-dichotomy-w/-transforms ∧ BOX-CONTENT-transforms (resolves axkPair/box4 holes structurally;
no opaque box_inversion witnesses in the induction). Target (literal half first):
`Provable k φ → ProvableB (2^(max k (maxLitF φ) + 2)) k φ`; modesty rides the same induction by
enriching Tame with argsIn-universe (T43 step lemmas + T47 enumArg_mem supply the threading).
Watch: axK degenerate-content rewrite arithmetic (first budget-inflation candidate — inflation
`ProvableB N₀ (F m) φ` for fixed computable F is HARMLESS for decidability).

**⚑ UPDATE 2026-07-03 (T4.1b C3a ✅) — master-induction ARCHITECTURE + sibling-sourcing kit.**
CUT_RELEVANCE.md §5 (READ FIRST next session): the tree-invariant and transformation MERGE into
ONE Provable.rec (motive = transform ∧ dichotomy-with-transformed-degenerates — rewrites are
covered because degenerate witnesses CARRY their transforms; cites are structural so no budget
induction). BOXES ARE NEVER OPENED (no reflection; Derivation concludes no boxes —
`derivation_shape`/`derivation_no_box`, T48 §6) ⇒ box contents never become judgments;
`box_inversion` (boxIntro-content-was-a-judgment ∨ app-spine, on [propext] only) = the
sibling-sourcing tool for the axkPair/box4 census holes. `provable_pos` (degeneracy recursion
well-founded). OPEN DESIGN QUESTION for C3b (stated in note §5): the Inv-contract — input
(consumer-supplied) fails at app-cuts; candidate = `SelfInv` OUTPUT form (each judgment reports
its own non-conclusion-sourced material GATE-tame, bottom-up) + the N₀ aggregation across
cite-local budgets (should ground at 2^(max k L(root-closure) + c) — verify).

**⚑ UPDATE 2026-07-03 (T4.1b C2 ✅) — the FULL Provable-layer spine dichotomy (Lemma A pairwise).**
T48 §5, first-compile green: `provable_impl_ant : Provable m (.impl B C) → PAnt B C ∨ ∃ m' ≤ m,
Provable m' C`. `PAnt` = census (DAnt embedded + 8 modal constructors + trans + TWO honest ones:
`imps2Ant` RECORDS its judgment (budget-decreasing, C3 unfolds); `axkPair` SHAPE-ONLY — box-box
antecedent content lives in the SIBLING judgment at the consuming app, pairwise-invisible).
PosImpl absorbed the chains (planned C3 work landed early): app/weaken tails spine-embed;
implTrans degeneracy-propagation REASSEMBLES within budget (app at b+m₁'+|χ| < k since gate pays
|impl A χ| > |χ| — first evidence AGAINST the Lemma-B budget risk!); diagF deep-tail recurses
through the Löb premise. C3 = the TREE-invariant: every judgment of a degeneracy-normalized
derivation ∈ Cl(root); consume the dichotomy at app sites with BOTH premises (resolves axkPair),
unfold imps2Ant records, extend to box-content positions if needed. Then C4 (budgets — partly
de-risked) and C5 (assembly into CutRelevance → T47 plug-in).

**⚑ UPDATE 2026-07-03 (T4.1b C1 ✅) — the Derivation layer has NO free antecedents.**
T48 §3–4: `PosImpl φ B C` (positive-spine pairs) is THE invariant formulation — mp needs no cut
analysis (`ih₁ (.tail hp)`: conclusion's spine ⊆ impl-premise's spine), hypSyll = `DAnt.trans`.
`DAnt` = census inductive (6 transparency constructors w/ hme-equations + trans);
`derivation_posImpl_ant` (9-case induction, first-compile green; `derivation_impl_ant` depends on
NO axioms); `DAnt_lit` (census steps literal-NONINCREASING via maxLitF_subst);
`struct_ant_lit` (struct-entry antecedents < 2^k). NEXT: C2 = the Provable-layer chain-free
dichotomy — reuse the PosImpl pattern; the new elements vs C1: weakenImpl (degenerate disjunct
enters), STS/atomBoxImpl/axK/axKf/box4/boxMono/diagF/diagB leaf-shapes (a `PAnt` census
inductive), and app-produced impls (spine-embed like mp ✓ same trick); implTrans/impS2 =
trans-like but with BUDGETED premises (dichotomy: degenerate ∨ census) — the induction is on the
DERIVATION (Provable.rec, 26 arms) with motive over PosImpl-pairs + the degeneracy disjunct.

**⚑ UPDATE 2026-07-03 (T4.1b C0) — cut-relevance ATTACK LAUNCHED.** Analysis:
`Research/Notes/CUT_RELEVANCE.md` (READ FIRST when resuming); foundations: spike
`T48CutRelevance.lean` (green). THE SHARPENING: every gated premise is size-paid at its own
judgment ⇒ literals < 2^(local budget) (cut_lit_bound/box_lit_bound/diag_lit_bound) — the tower
is fed ONLY by size-exempt cut ATOMS. THE CENSUS: every impl-producer's antecedent is
conclusion-determined (all transparency/modal/diag rules) ∨ weakening-DEGENERATE (consequent
provable outright — cut eliminable) ∨ chain-recursive (implTrans/impS2/app-nesting). REDUCTION:
conjecture ⇐ Lemma A (impl-inversion dichotomy; well-founded on budget; positive-position
invariant for app-nesting) + Lemma B (degeneracy-elimination rewrites, transcript-decreasing —
BUDGET BOOKKEEPING is the risk; fallback: budget-INFLATED form `Provable k φ ↔ ProvableG
(modestGate N₀) (f k) φ` still gives decidability!). Milestones C0 ✅ /C1 (Derivation-layer
antecedent determinacy — hme-equations make it mechanical-ish, mp/hypSyll recursion the wrinkle)
/C2 (chain-free dichotomy)/C3 (full Lemma A)/C4 (Lemma B budgets)/C5 (assembly → plug into T47).
Failure branch: undecidability encoding via unbounded cite-escalation. ALSO fixed: the T5 root
import had silently failed — PrisonersDilemma.lean NOW really imports Decidability (3152 jobs).

**⚑ UPDATE 2026-07-03 (T5) — the chain is PROMOTED: `PrisonersDilemma/Decidability/`.**
The seven modules T31/T42/T43/T44/T45/T46/T47 moved out of Research/Spikes into the engine tree
(milestone names + namespaces KEPT — PD.T31 etc.); umbrella `Decidability.lean` re-exports the
headline API under PD.Decidability; the whole chain is in the default `lake build` (permanent
regression protection). `evalC` (ComputableEval/Computable.lean) marked HISTORICAL/superseded-by-
evalG (header rewritten; stale pre-repair axiom claims retired; still builds). Deferred to a
future session (recorded in roadmap): proofSearch rewiring (form depends on CutRelevance — either
keep classical eval + evalG companion, or redefine agents as stratum-searchers and re-verify the
outcome theorems) and by-decide outcome demos. NEXT big open: the CutRelevance conjecture.

**⚑ UPDATE 2026-07-03 — T4.4c pt2b SHIPPED: PIPELINE (i) COMPLETE.**
`T47Stabilization.lean` (~990 lines): **`decideProvableG : Decidable (ProvableG (modestGate N)
k₀ φ₀)`** with computable fuel bound |SL| — bounded provability over the zoo's query universe
decided by a terminating computation. Machinery: fold-based enum size ceilings (EB := foldMax
over the list ITSELF — no structural enum bound needed); stratification ZS b := Z₀ +
(RR−b)(EBR+RR+3); InvP (args ∈ allowedProgs ∧ lits ≤ LL); stepB_congr (16 checkers: descending
reads via ZS_step; cut sweeps CASE ON cutOKb — false ⇒ both sides false, no read-rewriting
needed!; chkDiagFEB/BEB have DUPLICATED pattern vars equated only by runtime beqs — case on the
beqs first, subst in the true branch; jumps land in GFall via T45/T46); T4.1a countP
stabilization verbatim. Proof-craft traps: `cases h : e` substitutes e in the goal (so
`simp only [h]` afterwards = "no progress" error); ZS-argument normalization — `simp only
[Formula.size]` must hit the hstep hypotheses TOO or omega sees distinct ZS-atoms; beta-unreduced
oracle lambdas need type-ascribed `have h' : (fun ..) x y = (fun ..) x y := h` before rw;
implicit args of lemmas must be pinned before `(by simp)` proofs (metavariables). REMAINING of
T4: ONLY the T4.1b cut-relevance conjecture (ProvableG (modestGate N) vs full Provable) +
optional consolidation (promote spike chain into engine tree; wire proofSearch).

**⚑ UPDATE 2026-07-03 — T4.4c pt2a SHIPPED: the GLOBAL query universe (`T46LogicSpace`).**
KEYSTONE: budget ceiling NON-CIRCULAR — reads either strictly decrease budget or jump to guard-cite
LITERALS; literals ≤ max(roots' L₀, gate N) =: LU; R := max k₀ LU bounds all reachable budgets.
maxLit kit (subterm + subst monotonicity, mutual pairs; omega handles Nat.max natively — use
`simp only [defs] at *; omega` per case); `allowedProgs` := subterm closure of roots + self/opp +
(enumProg R).filter (closed && modest && lit≤N) — subterm-closed/modest/lit-bounded; `GF` :=
guardU u v glued over allowedProgs² with GF_args (args re-enter universe) + GF_lit;
`certRead_budget` (≤ max b LU) + `certRead_mem_GF`. Remaining pt2b (FINALE): stratified formula
space SL (Z b := Z₀ + (R−b)(R+2); GF∪negs fit at every budget), 16-checker closure + stepB
congruence (cert cases via T45 decCertG_congr + these lemmas), countP stabilization ⇒ fuel bound
|SL| ⇒ Decidable (ProvableG (modestGate N) k φ).

**⚑ UPDATE 2026-07-03 — T4.4c pt1 SHIPPED: `CertRead`, the cert layer's read interface.**
`T45CertReads.lean`: the stabilization's last opaque piece — decCertG's oracle reads — made
first-class. `CertRead b me oppo body m ψ` (budget-indexed reachability; constructors per
consultation site (citeT `(kg, g.subst)`, citeF `(m ≤ b, .neg (g.subst))`) + per recursion site,
OVERAPPROXIMATING sweeps); `decCertG_congr` (agreement on CertRead-set ⇒ same Bool at every fuel —
induction on fuel, anyCongr through sweeps, per-case hD-lifts `fun m ψ hr => hD m ψ (.selfR hr)`);
`certRead_mem_guardU` (over the T4.3 universe every read ∈ guardU ∨ .neg thereof — induction on
CertRead consuming step_search/step_sim; named-field access in induction arms via `@searchT _ _ _
kg g p q _ _ _ ih` patterns). Remaining T4.4c pt2: logic-side space (stratified size bound Z(b) =
Z₀ + (M−b)(M+2) handles cut-composite growth; hop formulas ≤ Z₀), 16-checker closure + stepB
congruence, countP stabilization ⇒ Decidable over the zoo universe.

**⚑ UPDATE 2026-07-03 — T4.4b SHIPPED: `decB` COMPLETE — modest stratum semidecidable.**
T44 §6–8: stepB_mono/decB_mono (decProv_mono idiom; lagged certOG slots via certOG_mono2);
decB_complete (26-arm ProvableG.rec; cert motive at FIXED fuel b+1 — cert budgets strictly
decrease, only the guard-oracle slot grows; checkers consume the approximation at the SAME level —
no lagged bridge, simpler than decFull_complete); **ProvableG_modest_iff_decB : ProvableG
(modestGate N) k φ ↔ ∃ fuel, decB N fuel k φ**. Remaining T4.4c (LAST assembly): formula-side
space (gated enumFormula ∪ guardU-subformula closure) + in-space/congr + countP stabilization ⇒
Decidable over the zoo universe. Then only the T4.1b conjecture separates from full decidability.

**⚑ UPDATE 2026-07-03 — T4.4a SHIPPED: `decB` the modest-bounded decider, SOUND.**
T42 REFACTORED to gate-parametric `ProvableG (G : Formula → Prop)` (six conclusion-absent
premise formulas gated; axK/diag gate the WHOLE premise formula subsuming subscripts;
`ProvableB N := ProvableG (litGate N)` keeps all statements). Decidable gate `modestGate N B :=
maxLitF B ≤ N ∧ modestF B = true`. `T44BoundedDecider.lean`: SPIKE OLEANS BUILD via
`lake build PrisonersDilemma.Research.Spikes.transcript.<Name>` — spikes import each other (T44
imports T31+T42+T43; reuses T31's ten ungated checkers + decCertG + decDeriv VERBATIM); six
gated variants (cutOKb in the sweeps); `stepB N S` = one rule-firing pass (atom side = decCertG
with S as guard oracle, fuel k+1 — cert budgets strictly decrease, no cert stabilization
needed); `decB N fuel := stepB^[fuel] ⊥`; decCertG_soundG/certOG_soundG; **decB_sound** (hits →
ProvableG (modestGate N) → Provable). Remaining T4.4b: ∃-fuel completeness, formula-side space
(gated enumFormula ∪ guardU-subformula closure), in-space+congr, countP stabilization ⇒ modest-
stratum decidability. Proof-craft: T31's decProv_sound inversion skeleton (16-disjunct rcases,
per-checker `unfold; split at h; rename_i; simp only [...]; obtain`) transfers verbatim; gated
patterns just add `⟨⟨⟨⟨hlit, hmod⟩, hsz⟩, h1⟩, h2⟩` nesting (cutOKb in the simp set).

**⚑ UPDATE 2026-07-03 — T4.3 SHIPPED: the MODEST universe (pipeline (i) foundation).**
`Spikes/transcript/T43ModestUniverse.lean`: program growth under subst is the engine obstacle to
a finite query space; MODESTY (all .sim args and guard .plays-atom args ∈ {.self,.opp,frozen})
kills it. closedP/F = subst-invariance (.bot/.diag/.eq-RHS frozen BY Prog.subst itself; closed
(.bot p) = true even for open p!); substP_id/substF_id; subsP/subsF (closure through guard
formulas) + trans + modesty-inheritance; playsArgsF_subst (substituted modest atoms → players or
frozen originals; .eq excluded — never evaluated; .diag frozen+meta-only → not collected);
universe certU/players/guardU (finite lists) + step lemmas step_sim/step_search/guardU_args =
the T4QueryBound in-space closure for real programs. WHOLE ZOO MODEST by rfl. Remaining for (i):
assemble the two-sided ProvableB step operator over (budgets ≤ max k N) × (gated enumFormula ∪
guardU-subformulas) × (players² × certU) + T4.1a stabilization verbatim. Lean traps: `induction`
unusable on mutual Prog/Formula (use Formula.rec with motive_1 := fun _ => True when the Prog
side is irrelevant); simp-reshaping BOTH hyp and goal breaks or-associativity matching — reshape
the hyp only and build memberships with List.mem_cons_of_mem/mem_append_left/right; mutual
tactic theorems over Prog/Formula with recursive calls terminate via auto-wf (sizeOf), no
termination_by needed.

**⚑ UPDATE 2026-07-03 — T4.2 SHIPPED: `ProvableB N`, the literal-bounded strata.**
`Spikes/transcript/T42ProvableB.lean`: maxLitP/maxLitF; mutual PlaysProofB/AtomProvableB/
ProvableB N = engine triple verbatim + SIX gates, exactly where premises carry material absent
from conclusions: implTrans/app/impS2 cuts (maxLitF ≤ N), axK inner subscript a ≤ N, diagF/diagB
fb ≤ N; struct ungated (Derivation size-paid ⇒ literals < 2^k). Theorems (on [propext,
Quot.sound] only): ProvableB_sound, PlaysProofB_monoN/ProvableB_monoN,
**Provable_iff_exists_ProvableB : Provable k φ ↔ ∃ N, ProvableB N k φ**, and `CutRelevance N₀ :=
∀ k φ, Provable → ProvableB (N₀ k φ)` — THE T4.1b conjecture as engine Prop +
Provable_iff_ProvableB_of_cutRelevance. Proof engineering: 4 rec invocations × 26 positional
arms; binder orders copied from decFull_complete's (they transfer to the B-mirror since
constructors are declared identically, gates appended LAST); section `variable (hNN)` used only
in proof bodies is NOT auto-included — put it in the signature. Next: stabilization port
(ProvableB finite query space; "modest" bots = guards mention .self/.opp only atomically ⇒
finite subst-closure ⇒ zoo decidable), then the conjecture.

**⚑ UPDATE 2026-07-03 — T4.1a SHIPPED: budget jumps DECIDABLE over bounded literals.**
`Spikes/transcript/T4QueryBound.lean` (self-contained mini, 3 std axioms): mutual Good/Bad with
`sr kg g p q` guards CITED at literal kg ≫ k (fuel=budget method unavailable) — yet
`Good_iff_decN`: fuel bound = |Qs| (budgets ≤ max(k, source lits) × subterm closure × polarity),
via lfp STABILIZATION: stepF + soundness + chain mono + ∃-fuel completeness + in-space closure
(false side pays floor LINEARLY ⇒ only source literals jumped to) + countP pigeonhole
(exists_agree ≤ |Qs|) + agreement propagation (agree_succ/agree_ge) ⇒ decN_bound converts ∃-fuel
to fuel |Qs| ⇒ `Decidable (Good k p)`. This is the TEMPLATE for engine `ProvableB N`
(literal-≤-N-cut Provable): its query space = budgets × size-≤-budget formulas over bounded
vocabulary × cert layer (finite per query). REMAINING OPEN (T4.1b): CUT RELEVANCE — exotic-literal
cut formulas (enumerated cuts can carry fresh 2^K literals → tower) never NECESSARY, i.e.
Provable = ProvableB N₀(k,φ). bloeb's cut diet is O(k) ✓ consistent. If FALSE → Provable is a
candidate UNDECIDABLE bounded-provability predicate — either resolution thesis-grade. Lean traps:
`by_contra`/`push_neg`/`List.any_congr` NOT in core (no Mathlib!) — use Classical.byContradiction,
hand-roll anyCongr/countP_le/countP_lt/countP_le_len; simpa on `Agree`-shaped goals loops
(maxRecDepth) — use defeq `exact`/`rw at`.

**⚑ UPDATE 2026-07-03 (later) — T4.0 SHIPPED: `evalG`, computable evaluation of search bots.**
Spike §9: 3-valued guard sound in BOTH polarities (true via decFull_sound; false via a DERIVABLE
refutation `Provable m (.neg φ)` + soundness/consistency — excludes Provable at EVERY budget, no
floor); `evalG G` = eval's recursion parametric in the guard, `evalG_sound` at the SAME fuel
(sharper than evalC's ∃N); `guardFull` (converges on the whole r.e. fragment) vs `guardFast`
(goal-directed certs, `#eval`-practical). Demos RAN: Mirror-bot vs Coop → (C,C), vs Defect →
(D,D), self-play → none (Löb boundary). PERF LAW: decProv TRUE answers are cheap (Bool.|| short-
circuits at decDeriv/certOG before the sweeps); FALSE answers are inherently exponential (chkAppE
sweeps enumFormula K on every shape — app's conclusion is unrestricted). Demo bots need guard
literals ≤ 2 (enumFormula budget-2 is EMPTY, atoms have size ≥ 3). T4.1 = the open math, analysis
in roadmap: exactly TWO budget-raising hops (search_t guard cite; searchThenSearch_t inner premise
at k₂ — both log-paid source literals); tower obstruction = enumerated CUT formulas carrying fresh
2^K literals; route = cut-relevance theorem + budget-depth-slice finiteness (cert answers depend
only on the top-b program slice), fallback = positive-rule least fixpoint.

**⚑ UPDATE 2026-07-03 — ZERO AXIOMS + ABSOLUTE SEMIDECIDABILITY SHIPPED.** The axiom
`atom_complete_false_guard` was machine-checked INCONSISTENT (anti-diagonal bot
`G := .search 100 (.plays .self .self .D) (.const .C) (.const .D)`; else-cert at `atom_cost 2=7`
lifted by atom_monotone above the guard budget it refutes) and DELETED. Repair (all additive, no
axioms): `PlaysProof.search_f` (else-cert from Σ₁ refutation `Provable m (.neg guard)` + cost
FLOOR `+m+k` — floor forced by consistency+decidability+soundness-provability),
`Provable.atomNeg`, `Derivation.eqNeg`; soundness = `sound_upto` (budget strong induction).
CITE vs CHARGE: search_t/searchThenSearch_t CITE (`c_guard`), search_f CHARGES. Prudence facts
are floored ⇒ consumers need STAGGERED budgets (2k+64, 4k+100): PrudentBot×Dupoc, JustBot×Prudent,
PrudentBot2 (two-tier bounded-PA+1) self-play, JustBot×Troll all recovered; probe pairs needing
false-guard outcomes at same-k (Dupoc×DBot etc.) RETIRED pending ¬Provable side. Engine verified
`#print axioms` = 3 Lean-standard EVERYWHERE. THEN T3.2c (spike `T31EngineDecider.lean`, ~1900
lines, green, 3 std axioms): `decProv O` (backward search, all 16 rules) sound+mono+∃-fuel-complete
relative to atom oracle (`decProv_iff`); then the knot untied — `decCertG` (cost-tracking cert
search, guards consult D; false-guard sweeps `m ∈ range(b+1)` paying the floor), `certOG`,
**`decFull (fuel+1) = decProv (certOG (decFull fuel) fuel) (fuel+1)`** (fuel stratification,
plain structural recursion), monotonicity lattice (`decFull_mono`/`decFull_le_inner`), joint
`Provable.rec` completeness (motives `∃F, …`), payoff **`Provable_iff_decFull : Provable k φ ↔
∃ fuel, decFull fuel k φ = true`** — bounded provability is r.e. with a verified computable
enumerator, NO oracle, NO hypothesis. ∀-fuel completeness IMPOSSIBLE under CITE model (cited
premises live at source literals unbounded by conclusion budget) — that's the precise residual.
REMAINING (T4, the only open piece): computable fuel bound f(k,φ) (query-universe finiteness
across guard hops) ⇒ full decidability ⇒ `proofSearch := D` ⇒ computable eval ⇒ `by decide`.
Key Lean traps hit: Provable.rec positional arm binder orders (app's index unification eats k/α);
`||` left-assoc rcases nesting; `rw [f.eq_def]` for parametric defs; pattern var `opp` shadows
`Prog.opp`.

**⚑ UPDATE 2026-07-02 (later) — T1 refactor SHIPPED, build green, T2 absorbed.** Engine now runs
FULLY on transcript accounting: `Derivation.size` structural (mp/hypSyll pay subtrees); all
`Provable` rules additive (implTrans cut gate DROPPED — premises pay it; axK/axKf/box4 in
three-subscript form; `boxMono` NEW appended last; `searchThenSearch_t` premise at own transcript
`m ≤ k₂`); NEW `Provable_mono` (by cases); `bloeb_engine` = T0 21-condition chain; `pblt_engine_id`
takes pm at HONEST transcript (never weaken premises to k!); NEW `mutual_pblt_engine_id` (consumers
pass the two O(log k) legs directly; old same-subscript mutual_loeb factoring deleted). Consumer
premises transcript-tight, unconditional (`atom_cost 2/3/4 = 7/10/17`). Outcome axiom footprints
UNCHANGED. decGuard `.impl` case consults consequent at reduced budget `k − |φ'→ψ|`. ALSO T3.0
PASSED same day (`Spikes/transcript/T3DeciderMini.lean`): `Prov` DECIDABLE for the full mini
additive rule set incl. diagF/diagB (Löb ≠ undecidable) — decP sound+complete, 3 std axioms,
#eval'd consistency. Method: fuel=budget (premise budgets strictly decrease); cuts range over
finite enumF k (paid conclusions, `prov_size`); diag's fb < 2^(k+2) (gate pays log2 fb);
maximal-budget instantiation via Prov_mono; named per-rule checkers with callback recursion.
T3.1 ALSO PASSED same day (`Spikes/transcript/T31EngineDecider.lean`, 3 std axioms — NOT
atom_complete_false_guard): engine Provable decidable RELATIVE to an atom oracle
(`provableRelDecidable`); decDeriv (Derivation search, transparency leaves = shape-matching) +
decProv (15 rules). Key: atoms NOT size-paid → `provable_size_or_atom` + `provable_impl_size`
(AtomProvable never concludes .impl) re-bounds cuts through the impl premise; axK inner
subscript ≤ its gate's c; mutual enumProg/enumFormula complete. Provable.rec positional
(mutual block — `induction` unusable). Next: T3.2 (decide AtomProvable itself: source-literal
guard budgets ≤ 2^k, fuel-stratified evalC pattern with decProv for guards; all rules POSITIVE
⇒ least-fixpoint over finite query universe as fallback) → T4 (proofSearch := decProv O;
delete `atom_complete_false_guard` ⇒ ZERO axioms).

**⚑ UPDATE 2026-07-02 — Route B (transcript-length accounting) is GO; T0 spike PASSED.**
Branch `colomban-transcript-length-accounting-comp-eval-no-axiom`; plan =
`Research/Notes/DECIDABILITY_ROADMAP.md` (Route B recommended over cut-elimination and chosen by
Colomban). T0 (`Research/Spikes/transcript/T0Transcript.lean`): mini-engine with fully ADDITIVE
budgets (each rule pays premise transcripts + conclusion size) — `Prov_mono`/`Prov_sound`/
`bloeb_transcript` axiom-FREE, `pblt_transcript` (kill-criterion, f=id, O(log k) premise
transcripts) on 3 std axioms. The g ≺ f subscript dance CLOSES: all budgets multiples of
W = pm+|tgt|+log2 k+8; g=1024W absorbs ψ's proof (c₁₃=768W ≤ g); only headroom = 8192W ≤ k.
Freeze: diag gate kept+charged but at subscript fb (not g); boxMono object-rule; axKf additive
(sound arm = app); do NOT merge Derivation into Provable (atom layer already transcript-style).
Next: T1 accounting refactor → T3 decider D → T4 delete `atom_complete_false_guard` ⇒ ZERO axioms.

**⚑ UPDATE 2026-07-01 (supersedes the framing below — read this first):** `PBLT` is now a THEOREM
and DELETED as an axiom (internalization: `Formula.diag` fixpoint + `diagF/diagB/axKf/impS2` rules,
`BaseTheorems.bloeb_engine`; see [[project_pblt_removal_plan]]). Engine is at ONE axiom
(`atom_complete_false_guard`). Consequences for THIS memory's story:
- The "witness-free axiom injects Löb members" claim is OBSOLETE: every Löb-fixpoint cooperation now
  has a real constructor tree in `Provable`.
- `eval` is STILL noncomputable, but the reason SHARPENED: (a) decidability of `Provable k φ` is OPEN
  — the "decidable by enumeration" claim below was REFUTED for the full system (mp-cut ranges over
  ∞-many provable cut formulas; atom-closure false — machine-checked, `MN1_decidable.lean`); a decider
  needs cut-elimination-style normal forms (open); (b) `atom_complete_false_guard` still injects
  witness-free `AtomProvable` members. So "Löb proven" ≠ "eval computable" — the internalization
  DECOUPLED them. The "axioms 4→3 / Provable collapses to Provable_finite" plan below did NOT survive
  contact: the internalized rules are sound constructors, not enumeration-friendly certificates.
- `evalC` (option D) remains the correct reviewer-facing artifact, boundary unchanged.

**Settled conclusion (the framing that matters — do NOT regress to "impossible/Gödel"):**
`eval` is `noncomputable` **today only because the reflection principles are kept as
WITNESS-FREE AXIOMS** (`PBLT`, `atom_box_provable_impl`). It is **NOT** a Gödel/Π₁ wall and
**NOT** fundamental. The limit is **axiom-relative and removable.**

Why: two different predicates get conflated.
- `Provable_finite k φ` = "∃ finite proof TERM of size ≤ k" — **DECIDABLE** by enumeration
  (bounding k makes it finite; this is Critch's whole point vs Barász's RE PA-tower).
- our `Provable k φ` = `Provable_finite` PLUS axiom-injected members (Löb fixpoints, e.g.
  PrudentBot↔DupocBot cooperation) with NO proof term. `decide` can't enumerate a witness
  the axiom never built. Axiom = IOU; a running eval needs cash (a searchable witness).

**How the block lifts (fully-explicit S):** replace the reflection axioms with CONSTRUCTIVE
theorems (mechanize bounded provability logic + a constructive parametric bounded Löb / PBLT
that EXHIBITS a size-≤-k proof term). Then `Provable` collapses to `Provable_finite`,
decidable by enumerating proof terms of size ≤ k → **eval becomes TOTALLY computable, Löb
fixpoints included**, and project axioms 4→3 (Lean standard). This is finite ordinary
metamathematics, hard but no undecidability wall. ONE foundational lever = two payoffs
(computable eval + fewer axioms).

**What that means for the Lean proofs (asked 2026-06-19):** still need them, but they change
character. Concrete fixed-(k,fuel) outcomes become `by decide` (huge cleanup — the
`play_X_against_Y` / `ps_k_of_play_*` inversion scaffolding + proofSearch/atom_complete
plumbing all evaporate). The ∀k FAMILY outcome theorems (`∃k₂,∀k>k₂,…`) STILL need proofs —
no #eval proves a ∀k — but simpler: `decide` does finite reductions, a now-PROVED Löb/PBLT
carries the irreducibly-modal core. Analogy: `2^31−1 prime` by decide vs "∞ many Mersenne
primes" stays a theorem.

**Refuted shortcut (kept so we don't retry):** deciding `Provable k φ` by STRUCTURAL recursion
on the program does NOT terminate — `search_t` guard `Provable kg (ψ.subst me opp)`: kg is a
source literal ≤2^k but not <k, and subst of a .search-bot into its own guard RAISES
search-depth (machine-checked `meP` in `ComputableEval/DecMeasure.lean`). So lex `(k,
search-depth)` is false. The right route is enumerate-proof-TERMS, not recurse-on-program.
Also dead: the `derivable`/`playsCheck` checker (separate search-gas conflated "not found yet"
with "unprovable" → non-monotone).

**Shipped today (option D, build green ~3142, no new axioms):**
`engine/PrisonersDilemma/ComputableEval/` — `Computable.lean` (`evalC` = sound TOTAL
computable PARTIAL evaluator; 3-valued budget-aware `decGuard`: some true=witness fits k→p /
some false=refutation→q / none=undecided→none; a 2-valued v1 was UNSOUND. Faithfulness
`evalC_eq_and_decGuard_sound` → `evalC_sound`/`playC_sound`/`outcomeC_sound`: every committed
#eval = classical eval). `Demo.lean` (#eval runs; Löb fixpoint → none, the honest boundary).
`DecMeasure.lean` (the refutation, NOT wired into build's logic). N1 also landed: `Derivation`
indexed by budget `Derivation k φ` with cut-rule premise-size bounds (commit b77abad).

`atom_complete_false_guard` is bounded + atom-layer (no reflection) → SHOULD be eliminable
as a constructive theorem by enumeration (the nearest real win, Colomban wants it removed).
The other 3 axioms (PBLT, box_provable, atom_box_provable_impl) need the constructive-Löb work.

See [[project_weakenimpl_rule]] (Provable cuts), [[project_prudent_dupoc_gl4]] (the Löb
fixpoint that goes `none`). `Enumerate.lean` (`progsOfSizeLE`/`formulasOfSizeLE` + completeness)
is the proof-term universe for any future enumerate-route.

## O2 WINDOW — CLOSED 2026-07-08 (all in T49 §27–§28)

Chain: GoodW family + GoodW_app (O2-1) → atomizeW_halts (O2-2) → GoodW_mono (O2-3) →
GoodD (O2-4) → machine totalization (O2-5) → fundamentalW + GoodW_box_levels (O2-6) →
crossTotalW (O2-DONE). O1 ✓ (exciseFix/certifyExcised), O3 ✓ (by inspection).

Key design facts (do NOT re-derive):
- The machine had TWO none-arms at type-valid wide states: diagF@cons-nil (fixed:
  extract diag content — its tree IS the impl core, weight ≤ via ih) and axKf@cons-nil
  (fixed: repackage `.axK a b c mD1 _ φ α d1 hg1 (le_refl)` — gate paid by segsOK.1,
  weight EXACTLY d1.wt+1 ≤ 1+d1.wt). Without these fundamentalW is FALSE.
- All 10 conservation arms (5 packages × 2) repaired in one pass; crossWtLt/total
  stay vacuous (impl NOT IsCore → `exact hc.elim`).
- fundamentalW arms: struct = GoodD one-liner; atom needs `cases a` BEFORE `cases S`
  (the plays index refines ξ; otherwise cons-alternative undischargeable + ⟨⟩ fails on
  unreduced CoreContent match); sTS census fuel F+1 (ONE tick, no structCross), GoodD
  censuses F+2 (structCross owns a tick); box4 inner transport = GoodW_mono∘
  GoodW_box_levels (NO regate, NO IsCore); nested `by unfold GoodStackW` must stay on
  ONE LINE inside parens (parser); `hS.2 : GoodStackW k (cons …)` is already the right
  type for stack args — do NOT unfold-repack.
- crossTotalW: ∀ f x dbFree, ∃ fuel r, boxInvGo fuel f (x::nil) = some r ∧
  ContentGoodW 0 r. The excisor beta-step is total on dbFree trees.

## O4/O5 — THE REMAINING ASSEMBLY (next session)

O4(a) COUNTER-SCENARIO (recorded in ledger): never-applied implTrans/impS2 middles
(impl-shaped roots ending in implTrans) have no upstream app — the middle can't become
an app-cut. O4 FOLDS INTO O5: the pool induction needs a simultaneous strand
"conclusion formulas of subtrees are pool-good" (middles = conclusions of tA); the
app-conversion story only covers applied middles. O5 = crossPool induction in the
crossWt style over the totalized machine + the fixpoint argument (surviving wild gate
must be an app-cut → excisor would have fired → contradiction). Literal half FREE
(C0 + compression ceiling §5g).

## O5 DESIGN SETTLED 2026-07-08 (two routes, scoped route chosen)

Applied middles LAUNDER through the machine (result assembled from subtree internals +
censuses; the middle formula vanishes). Never-applied implTrans/impS2 middles are the
ONLY gap. General route: virtual discharge + bracket abstraction — weakenImpl IS
rule-K, impS2 IS rule-S; walls: object-I underivable (bare returns), box-embeddings
hit necessitation. Dichotomy conjecture recorded in ledger. SCOPED ROUTE WINS for the
thesis: zoo audit shows every guard is a plays ATOM except CIMCIC/DIMCID's single
shape `impl (plays …) (plays …)` (depth-1). CutRelevance-over-the-zoo needs middle
analysis for ONE impl-shape, whose derivations are weakenImpl(atom-cert) or the Löb
chain (middles box-shaped, conclusion-tied). Next session: the crossPool induction
(crossWt-style package over the totalized machine) + the impl-atom-atom root case +
plug into T47.

## censusITE DONE 2026-07-08

The iteBranchSearch census is IN (T49): `censusITE` = .atom(.mk (ite_t (sim pl1)
(actionBeqSelf a') (search_t (tc.mono hc) .const))). The recorded `closedP z`
side-condition was WRONG — dissolved: .opp/.bot-z substs reduce on the nose. Machine
crosses saturated ite at (u1::u2::nil); 5 packages extended. TRAP: two-scrutinee match
with nested `.mk` pattern breaks equation-lemma generation ("failed to generate
equational theorem") — use nested single-scrutinee matches; destructure the atomize
result (obtain ⟨k', pl1, hn⟩) BEFORE the second dive so the outer match in h reduces
(rw can't rewrite under the unreduced match's binders). REMAINING ite gap: one-discharge
(u1::nil) stays none — no ProvT constructor for the ite-me Löb premise; dbFree still
guards GoodD/fundamentalW. Options: partial-ite ProvT constructor OR saturation
pre-pass (zoo uses the rule saturated via mp). T49 arm-name trap: the file's pattern
`iteBranchSearch_t k z a' c0 c1 ψg me opnt hme1 hme2` maps to engine's
(k z a' c0 c1 ψ q me opponent hme) — "me"=else-branch q, "opnt"=the ite, "hme1"=opponent!

## O5 SITE INVENTORY 2026-07-08 (in ledger, verified against defs)

certifyExcised = exciseFix -> gateOKb check -> certify; every `some` is kernel-certified
ProvableG (modestGate N). Completeness obligation by gate site: (1) app cuts = fixpoint
(progress via crossWtLt + crossTotalW); (2) axK premise = DONE modestGate_axK_tied
(maxLitF counts box subscripts, hg1 gives a<=c); (3) diag gates = DONE
modestGate_diag_tied mod fb<=N (the one ProvT-level literal-half consumer);
(4) implTrans/impS2 middles = zoo-scoped (one impl-shape); (5) NEW SITES: derivGateOK
mp cuts + hypSyll middles — derivation_shape constrains to census shapes/eq p p/
neg(eq p q); exotic risk = eqNeg cuts on arbitrary programs; (6) sTS stored premise
recurses. Plus ONE global literal-half induction (budget bounds stored formulas'
maxLitF — extend the wt_le_budget/§17 pattern). Next session: literal-half induction
first (mechanical, unblocks 3+middle sizes), then the derivation-cut analysis (5),
then fixpoint-progress (1), then middles (4), assemble.

## LITERAL HALF RESOLVED + INTERLOCK FINDING 2026-07-08

Literal half at Provable level ALREADY kernel-checked (T48CutRelevance: cut_lit_bound,
box_lit_bound, diag_lit_bound, local_lit_bound, maxLitF_lt_two_pow_size; Formula.size
charges log2+1 per numeral). weakenImpl antecedents ARE size-charged. Fixpoint progress
needs NO strict package (beta-reduced app supplies its own +1 via crossWt). DO NOT
attempt a standalone tree-wide literal lemma (gateOK (litGate 2^m)): PlaysT.gateOK
recurses into search_t cites at PROGRAM-SUBSCRIPT budgets (escalation channel) — the
literal and pool halves interlock at cites. The assembly theorem's irreducible shape:
ONE simultaneous induction `t.gateOK (modestGate N0)` under the cut-atoms-in-pool
hypothesis. Gate-tie bricks banked in T49: modestGate_axK_tied, modestGate_diag_tied.

## crossDbFree DONE 2026-07-08

Sixth conservation package: machine outputs stay iteBranch-free (DStack.dbFree,
CoreContent.dbFree, ProvT.mono_dbFree Iff.rfl per-constructor since mono only touches
the top budget field). One-iteration compile. Notes: part-2 with `cases heq` FIRST
auto-eliminates eqRefl/eqNeg arms (do not write them); atom@cons needs full
`simp [boxInvGo] at h` (simp only leaves `none = some r` open). exciseFix's
re-crossing license is now kernel-checked. REMAINING assembly items: the interlocked
induction (gateOK (modestGate N0) under pool hypothesis), derivation-cut analysis,
excise-walk progress bookkeeping, zoo middles.

## excise_dbFree CHAIN DONE 2026-07-08

crossDbFree lifted through the excisor: excise_dbFree + exciseFix_dbFree +
contentToTree_dbFree + excise_fire_dbFree_aux. TRAPS: PSigma-valued if/dite refuse
`split` (dependent motive) — use by_cases + rw [if_pos/if_neg/dif_pos/dif_neg];
excise's fire-branch nested match has SHADOWING binders — cases/generalize on the
scrutinee can't abstract occurrences under them — extract an aux lemma over a clean
Option scrutinee (unshadowed binder names!) + `show` to force the iota after cases;
pin PSigma args explicitly at aux call sites (metavar blocks anonymous constructor).
REMAINING assembly: interlocked induction (centerpiece), derivation-cut analysis,
excise-walk progress (fuel threading + diag-cut fallback scoping), zoo middles.

## excise_wt_freeS2 DONE 2026-07-08 + PROGRESS-SCOPE CORRECTION

Excision never gains weight + preserves freeS2 (kernel-checked; contentToTree adds
at most the boxIntro +1, absorbed by the fired app's own +1). So on the
CONTRACTION-FREE fragment, wt-many exciseFix rounds reach the app-clean fixpoint —
progress CLOSED there. CORRECTION of an earlier over-claim: crossWt is
freeS2-conditioned (impS2 crossings have NO weight bound — Gentzen wall §5g), and
Löb-bearing zoo proofs contain impS2 (bloeb uses it) — their progress still needs the
s2depth-stratified potential (part of the centerpiece work). CoreContent.wt is a
match-def: identity arms need `simp only [CoreContent.wt]` before omega.

## SITE 5 CLOSED 2026-07-08: DAnt_gate

modestP_subst/modestF_subst (mutual theorems by structural recursion, T49; frozen
.bot/.diag/.eq-RHS arms are identities; argOK_subst_argOK helper) -> DAnt_modest ->
DAnt_gate. Derivation-level mp cuts + hypSyll middles pass modestGate whenever the
conclusion does (T48's DAnt census + DAnt_lit). eqNeg cuts IMPOSSIBLE at Derivation
level (DAnt has no eq antecedent). TRAP: simp only [T43.modestP, Bool.and_eq_true]
turns `true = true` conjuncts into True but does NOT collapse `X ∧ True` — projection
paths must count the True slots (e.g. sim-part = ((argOKpair ∧ True) ∧ modestP z));
goal-side modestP (.bot z) vs hypothesis modestP z is fine (exact is defeq-tolerant).
Assembly remaining: interlocked induction (centerpiece), Löb-tree progress
stratification, zoo middles (one impl-shape).

## THE TIE-DOWN (centerpiece) OPENED 2026-07-08 — T49 §28

Design in ledger (CUT_RELEVANCE.md §6, "THE TIE-DOWN DESIGN"): gateOK_of_cutsOK —
root conclusion gated + cutsOK (only app/implTrans/impS2 sites) + citesLE M
(hereditary cite-budget cap) + m ≤ M + 2^M ≤ N ⟹ full gateOK (modestGate N).
DONE: modestGate_impl_iff; derivGateOK_of_conclusion (struct arm standalone —
DAnt_gate recursion); cutsOK + citesLE mutual def families (named-implicit match
patterns `(k := kg)` WORK). KEY INSIGHT: atoms' plays formulas are never gate-checked
— no atom-pool needed in the tie-down; the pool/zoo hypothesis enters ONLY as citesLE
of the original tree. PlaysT-half invariant: carry modestP+litP of (me, o, b);
sim-arm via argOK_subst; search_t cite via modestF_subst. NEXT: the main mutual
induction gateOK_of_cutsOK, then crossCites package, then consumers (fixpoint
app-half, zoo middles, citesLE of original zoo trees).

## THE INSTANCE-GATE PIVOT 2026-07-08 (CRITICAL — supersedes the tie-down as centerpiece)

Guard-INSTANCE formulas are NEVER modestF (substituted frames fail argOK: closedP
false through guard formulas with .self/.opp). T42's diagF/diagB gate the WHOLE Löb
premise => no bloeb-style derivation is in ProvableG (modestGate N) for any N; same
for axK-over-instances and mp-cuts on box-instances. The tie-down over arbitrary
excised trees is the WRONG centerpiece (its conclusion-gate hypothesis is false at
census shapes; DAnt_gate/derivGateOK_of_conclusion true-but-vacuous at instances).
RIGHT centerpiece: FULL NORMALIZATION — the machine is the Löb-unroller; survivors of
core-rooted zoo facts are atoms+censuses+glue with empty-or-modest gate sites;
instance facts flow through search_t CITES at strictly descending budgets (bloeb's
descent). CutRelevance-over-zoo = "normal forms are gate-light" by cite-budget
induction. NEXT SESSION FIRST TASK: characterize the normal-form grammar (what
boxInvGo/atomizeGo outputs contain at core roots; mkSelf-at-impl-cores = the residual
hard case, aligns with zoo-middles). Bricks/citesLE/cutsOK all remain useful; rescope
gateOK_of_cutsOK to the normal-form grammar. Full pivot note in ledger §6 (top).

## 💥 THE FALSIFICATION 2026-07-08 (T50InstanceLob.lean) — READ FIRST NEXT SESSION

CutRelevance AS STATED (modestGate) IS FALSE, machine-checked on the real DupocBot
self-coop tree (bloeb_engine mirrored into ProvT, kD=2^21, W=224 multiples, 21x by
decide). Verdicts: raw tree fails gate (modesty alone); excision can't repair;
atomizeGo TRUE (the machine unrolls real instance-Löb!); but the atom's cite chain
NEVER DESCENDS (fixpoint cites itself at the same budget kD) — only diag breaks the
regress, and modestGate blocks diag on instances (instance formulas never modestF).
So ProvableG (modestGate N) proves NO self-referential search fact at any N.
THE REPAIR: instGate P N B := B is a pool-instance of a modest formula (P = T46
players; guardU is already instance-based so finiteness survives). REVISED
CONJECTURE: Provable k φ → ProvableG (instGate P N₀) k φ for zoo roots. Expect
treeD to pass instOKb DIRECTLY (no excision needed for Löb chains). NEXT: (i)
T44 cutOKb→instOKb + refinish T44-T47 finiteness; (ii) formalize the regress lemma
(the falsification half — thesis content); (iii) rerun T50 verdicts with instOKb.
All T48/T49 machinery (normalization, excisor, 8 packages, bricks) carries over.

## (d) THE REPAIR CONFIRMED 2026-07-08: instance gate works

`treeD.gateOKb (instOKb [meD] kD) = true` — the RAW bloeb tree passes the instance
gate (T50: argOKP admits pool members at arg positions; instModestP/instModestF).
Löb chains need NO excision under instGate. The §28 gate-transport program
RESURRECTS at instGate (census conclusions ARE instance-modest — the
conclusion-threading that was vacuous at modestGate is live). PLAN OF RECORD:
(i) instGate versions of the bricks (DAnt_gate, ties, subst-closure — natively
easier); (ii) T44-T47 rework cutOKb→instOKb (guardU already instance-based,
pigeonhole transfers); (iii) revised CutRelevance = Provable → ProvableG (instGate
P N₀), zoo trees plausibly by direct transport, excision for fresh cuts only;
(iv) the regress lemma (modestGate proves no self-referential fact) = the
falsification half, thesis content.

## INSTANCE-GATE BRICKS 2026-07-08 (T50 §2, compiling; (d) still true)

DESIGN CORRECTION: instModestP's search-arm requires RAW-modest guards (T43.modestF,
not instModestF) — rules only substitute raw guards; instance-modest guards are not
subst-stable (.bot frames were the hole). Sim-args KEEP argOKP (instance frames like
.sim v u with v,u ∈ P appear as deeper plays-args). Bricks done: instOKb_iff,
argOK_argOKP, modestP/F_instModestP/F monotonicity, arg_subst_inst (argOK args
resolve atomically — NO program recursion needed), modestF_subst_inst (raw-modest ×
instance-modest players → instance-modest; formula-only recursion). NEXT:
DAnt_instGate — searchBr/botSearchSt cases are direct (guard raw-modesty is IN
instModestP now); the simSt/botSimSt cases need a POOL-CLOSURE hypothesis
(p ∈ P sim-args: p.subst me opnt ∈ P = exactly T43.step_sim for P := players r₁ r₂).
Then derivGateOK_of_conclusion and the §28 transport at instGate; then T44-T47
cutOKb→instOKb rework; then revised CutRelevance.

## DERIVATION-LAYER TRANSPORT DONE AT instGate 2026-07-08 (T50 §3)

PoolOK structure (modest: members instance-modest; argStep: member arg-subst by
admissible frames stays in — both THEOREMS for P := T43.players r1 r2 via
certU_modest/step_sim, discharge later); argOKP_subst_inst (4-case arg resolution,
uses substP_id for frozen); DAnt_instModest (7 arms; guard raw-modesty direct from
instModestP search-arm — no closed-helper needed; same accessor paths as
DAnt_modest incl. True-slots); DAnt_instGate; instGate_impl_iff;
derivGateOK_of_conclusion_inst. NEXT: (1) PoolOK (players r1 r2) instance —
discharge via T43 step lemmas; (2) ProvT-level transport at instGate (§28
tie-down rescoped: conclusions ARE instance-modest now — thread conclusion-gate
through the 16 arms; cites via citesLE; axK/diag ties at instGate = trivial ports
of modestGate_axK_tied/diag_tied); (3) T44-T47 cutOKb→instOKb; (4) revised
CutRelevance assembly; (5) regress lemma (falsification half).

## 🏆 THE TRANSPORT PROVEN 2026-07-08 (T50 §4) — the tie-down at the repaired gate

ProvT.transport/AtomT.transport/PlaysT.transport (mutual structural): instance-gated
conclusion + cutsOK (app/implTrans/impS2 only) + citesLE M (sTS k2 cap added to T49
citesLE) + m ≤ M + 2^M ≤ N + PoolOK P ⟹ FULL gateOK (instGate P N). With
gate-generic ProvT.toG ⟹ ProvableG (instGate P N) k φ. REVISED CutRelevance now =
supplying the hypotheses: (1) cutsOK via excision (machinery done) or raw (zoo per
T50 (d)); (2) citesLE = the zoo/pool hypothesis; (3) PoolOK for players r₁ r₂ (T43
discharge; argStep closed-frame flag); (4) T44-T47 instOKb rework for decidability.
TRAPS: subst-casts break mutual structural recursion — use rfl PATTERNS for hme;
bind outer implicit frames positionally in arms (metavars in have-types strand
omega); modestF_subst_inst arg order (hu hv hum hvm); T49 was NOT in the lake graph
— stale olean — now wired into PrisonersDilemma.lean root (T50 still lean-direct).

## 🏆 dupoc_selfcoop_certified 2026-07-08 (T50 §5) — first certified instance

`T42.ProvableG (instGate [meD] kD) (4096*W) tgtD` KERNEL-CHECKED (by decide on the
full gateOKb + gateOKb_sound + gate-generic toG). The fact that FALSIFIED
modestGate-CutRelevance certifies into the repaired stratum. NOTE: the transport
route for this demo was blocked by the PoolOK-argStep design knot (arbitrary
admissible frames make argStep unprovable for finite pools; fix = MEMBERSHIP-
strengthened frame invariant in PlaysT.transport — frames ∈ P, descent via
step_sim-style closure + closed-args ∈ P; entry needs membership-based conclusion
info). The direct decide-route sidesteps it for concrete atom-free trees. NEXT:
(1) membership-strengthened PlaysT invariant OR PoolOK discharge for players r₁ r₂;
(2) citesLE/cutsOK Bool checkers + sound bridges (decide-able hypotheses for
trees WITH atoms); (3) T44-T47 instOKb rework; (4) regress lemma. ProvableG is
PD.T42.ProvableG (qualify in T50).

## TRANSPORT v2 DESIGN 2026-07-08 (PoolOK knot RESOLVED — in ledger, top)

Frames stay RAW MEMBERS through walks (sim-steps resolve atomically — step_sim);
pool-args are DEAD CODE inside walks (only formula gates need the ∈P disjunct);
b-invariant = subterm-of-member (subsP + subsP_trans). PoolOK v2 = modest/memStep/
closedArgs — ALL theorems for players r₁ r₂. New third tree-certificate: framesInb
(atoms' formula args ∈ P, hereditary). NEXT SESSION: implement PlaysT.transport v2
(membership invariant), discharge PoolOK v2 for players, then T44-T47 instOKb
rework, then the regress lemma (designed, in ledger).

## TRANSPORT v3 2026-07-08 (POOL-FREE — supersedes v2; in ledger top)

Closed frames are argOKP via closedP => frames never need membership. v3 walk
invariant: frames (argOKP + T43.modestP RAW + lit ≤ N), run-program b (RAW-modest +
lit). Self-propagating (raw b's sim-args are argOK-atomic; guards stay raw). NO
PoolOK in the transport. New 4th certificate: rawAtoms/rawAtomsb (atom formula args
raw-modest, hereditary through cites). Implementation = v1 transport with frame
hypotheses swapped + hP dropped + rawAtoms threaded to atom arms. PoolOK survives
only in DAnt_instGate simSt (optional raw-variant cleanup). IMPLEMENT NEXT SESSION,
then T44-T47 instOKb rework, then regress lemma.

## v3 BLOCKER + FIX 2026-07-08 (final entry of the day; ledger top has full detail)

PoolOK.argStep is UNPROVABLE for real pools (substituting a search-member
instantiates its guard — violates raw-guard instModestP) => v1 DAnt tie vacuously
conditioned; transport struct-arm blocks concrete use. FIX (next session, in order):
(1) rawArgsF φ (plays/eq args raw-modest, argOK NOT required) + subst lemma
(mirror modestF_subst_inst); (2) DAnt_rawGate : DAnt B C → instGate C → rawArgsF C →
instGate B ∧ rawArgsF B (simSt ∈P-branch unreachable — raw frames' sim-args are
argOK-atomic); (3) derivGateOK_of_conclusion_inst with rawArgsF; (4) transport v3
(frames argOKP∧raw∧lit; b raw∧lit; rawAtoms 4th certificate — family drafted in the
reverted attempt; struct arms take rawArgsF). PoolOK deleted everywhere. The v3
arm-bodies all elaborated except the struct-arm reference — reproduce from design.

## 🏆 TRANSPORT v3 LANDED 2026-07-08 (pool-free; T50)

rawArgsF + modestF_rawArgsF + rawArgsF_subst; DAnt_rawModest/DAnt_rawGate (pool-free
census tie — simSt ∈P-branch eliminated); derivGateOK_of_conclusion_raw; rawAtoms
(4th certificate, _root_.PD.T49-qualified defs for dot-notation from other
namespaces — TRAP: defs in a different namespace than the type break dot-notation);
transport v3 with raw-frame invariant. PoolOK dead code (v1 tie + structure remain
in file; prune later). Revised CutRelevance per concrete tree = 4 decide-able
certificates + 2^M ≤ N. REMAINING: rawAtoms Bool-checker is trivial (it IS
decidable Props of modestP — add rawAtomsb if needed for decide); T44-T47 instOKb
rework (decidability at the repaired gate); regress lemma (designed); prune PoolOK.
TRAPS this round: `induction` tactic refuses mutual inductives (use match-recursion);
two stacked doc-comments = parse error (again); DAnt_lit inside induction arms can't
synthesize constructor implicits — hoist lit out via the original h.

## 🏆 THE REGRESS LEMMA PROVEN 2026-07-08 (T51Regress.lean, in root build)

cutRelevance_modestGate_false : (∃ m, Provable m tgtD) ∧ ∀ N m,
¬ProvableG (modestGate N) m tgtD — the falsification is a THEOREM. Structure:
ModChain (modest-antecedent impl chains into tgtD); DAnt_box_consequent +
DAnt_chain_to (census antecedents into chains = the guard box; trans dies on
box-consequent-freeness); no_deriv_tgtD/no_deriv_chain; main regress via
T42.ProvableG.rec with FORDING MOTIVES (motive_1 carries frame equations + a
const-action ford killing search_f; motive_2 = ModChain φ → False). TRAPS:
structural-recursion search on mutual Prop triples STACK-OVERFLOWS (exit 134,
'Stack overflow detected') — use the .rec directly (T42 line 190 pattern, exact
binder orders copied from ProvableG_sound's cases); `injection` can auto-close
goals (No-goals error on the following exact — use simp only [C.injEq] instead);
new spike files MUST be wired into PrisonersDilemma.lean root or oleans go stale
silently (T49/T50/T51 all wired now). REMAINING: T44-T47 instOKb rework (the
decidability payoff — checkers hardcode cutOKb; enumFormula must extend its
alphabet with pool members for instance-cut coverage); prune dead PoolOK/v1-tie.

## 🏆 T52 LANDED 2026-07-09: gate-parametric decider; instGate SEMIDECIDABLE

T52DecInst.lean (root build): T44 copy-transformed to (Gb, G, hGb) — mechanical
(gate enters at exactly 8 sites; sed-style transform + 6 obtain-shape fixes where
cutOKb-unfolding became an opaque Gb fact + qualify T31.Formula.size_pos vs T49
ambiguity). KEY: enumFormula enumerates ALL formulas by size (enum_complete) — NO
coverage work needed for instance cuts. Results: ProvableG_iff_decG (parametric),
ProvableG_modest_iff_decG (sanity), ProvableG_inst_iff_decG (the payoff:
ProvableG (instGate P N) k φ ↔ ∃ fuel, decG (instOKb P N) fuel k φ). REMAINING for
full Decidable: T47 stabilization fuel-bound parametrized (988 lines — the
pigeonhole is over the finite enumFormula space, gate enters via filters; expect
the same mechanical transform pattern). Then: prune PoolOK/v1-tie; promote spikes;
the general Provable→certificates closure.

## 🏆🏆 T53 LANDED 2026-07-09: FULL DECIDABILITY AT THE INSTANCE GATE

decideProvableG_inst : Decidable (ProvableG (instGate (players r₁ r₂) N) k₀ φ₀)
(fuel bound |SL|; hypotheses = modest roots + root args ∈ AP — same as modest
original). The T44–T47 rework is COMPLETE. Route: argOKP tightened (closed args
must be RAW-modest — needed so the finite universe classifies instance-gated
reads; all T50 verdicts survived); T53 stage 1 = players_sub_AP +
playsArgs_instModest + enumArg_mem_inst; stage 2 = T47[congruence+stabilization+
payoff] transformed mechanically (651 lines, ONE compile) — T47's space is
gate-free, reused verbatim. REMAINING for the conjecture: the general
Provable→certificates closure (the research residue); housekeeping (prune
PoolOK/v1-tie; promote T48–T53). The decidability payoff chain now EXISTS:
transport (4 decide-able certificates) → ProvableG (instGate) → DECIDABLE.

## AUTONOMOUS RUN 2026-07-09 COMPLETE (user away): T53 + prune + pipeline

Landed in one run: (1) argOKP tightening (closed→closed∧raw-modest; verdicts
survive); (2) T53 = FULL DECIDABILITY at instGate (decideProvableG_inst, fuel |SL|;
T47's space gate-free — 651-line transform in ONE compile); (3) PoolOK chain pruned
from T50; (4) certifyTransport = the four-check pipeline (rawAtomsb 4th checker +
sound). TRAP again: defs extending PD.T49 types from other namespaces need
_root_.PD.T49-qualified names; AtomT.mk's field is `opponent` not `o`. REMAINING:
the general Provable→certificates closure (THE research residue — needs user scope
decision per thesis timeline); promote T48–T53 out of spikes; chapter write-up
offer stands.

## 🏆 OPTION C UNDERWAY 2026-07-09: T54 — the flagship cross-bot fact CERTIFIED

prudent_dupoc_certified : ProvableG (instGate [PB, DB] kP) (32768·V) (plays DB PB C)
— PrudentBot(2k+64)×DupocBot(k) staggered cooperation, k=2^29, V=2091, RAW tree
passes the gate. THE ZOO-CERTIFICATION PATTERN (reusable): legs (searchBranch struct
/ sTS-with-prudence-cite / atomNeg+search_f certs) → mutualLoebT (mirrored) → bloebT
→ gateOKb (instOKb) by decide → toG. Numbers recipe: p₁ (leg1 budget, hsz needs
~c_guard+size ≈ 30·log2+700), p₂ = leg-Derivation.size (#eval), V = p₁+p₂+|Af|+|Bf|+
log2 k+16, need 131072·V ≤ k, fb = k−64V; mutualLoebT multipliers
(8,16,32,16,64,16,96,8,128,160)·V; bloebT (8192,512,16384,16384,65536 | 256,256,
1024,512,2048,512,512,3072,4096,256,5120,6144,7168,16384,32768)·V. TRAPS: pin AtomT/
atomNeg indices via explicit constructor args (metavars strand decide); atomNeg arg
order (b=actual, aN=refuted). REMAINING ZOO TARGETS: JustBot legs (same pattern),
CIMCIC/DIMCID self (impl guards — weakenImpl legs?), CupodTrollBot (eqNeg guards),
Dupoc-self ✓ (T50). Then the zoo table + chapter write-up.

## OPTION C: GUARD-SHAPE COVERAGE COMPLETE 2026-07-09 (T54)

Certified into ProvableG (instGate …): (1) Dupoc-self plays-atom Löb (T50);
(2) PrudentBot(2k+64)×DupocBot(k) staggered — the flagship (T54, V-recipe);
(3) CIMCIC impl-guard via weakenImpl-over-atom (cut-free); (4) CupodTroll eq-guard
via eqRefl struct (cut-free). atomNeg/search_f exercised inside prudenceT. All
FOUR zoo guard shapes covered. REMAINING C-targets (optional depth): JustBot legs
(T54 pattern rerun), DIMCID (symmetric), per-pair outcome table. NEXT BIG ITEMS:
chapter write-up (offer stands); promote T48–T54 out of spikes; the universal
closure stays the open frontier (option B, not chosen).

## ✅ OPTION C COMPLETE 2026-07-09 (T54ZooCert)

The certified zoo: dupoc_selfcoop_certified (T50), prudent_dupoc_certified +
botdupoc_prudent_certifiedA + justbot_guard_certified (Bf via app-over-boxed-
fixpoint — boxIntro budget must EXCEED the box subscript kP!) + cimcic_coop_certified
+ dimcid_defect_certified + cupodtroll_eq_certified. Every zoo guard shape (plays/
impl/eq), every Löb pattern (self, staggered mutual, bot-wrapped mutual), every
refutation route (atomNeg, search_f, bot-wrapped search_f) — ALL RAW, kernel-sealed
into ProvableG (instGate). C IS DONE. Remaining project items: chapter write-up;
promote T48-T54 out of spikes; universal closure = open frontier (declined for now).
