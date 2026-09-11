---
name: family-completion-arc
description: "Pf constructors regrouped into 3 families (2026-07-28); family A/B completion designed + kernel-checked in spike, NOT integrated; implRefl BREAKS the tail census invariant — Guarded repair validated"
metadata: 
  node_type: memory
  type: project
  originSessionId: e0fe1799-fa75-4928-b015-101b623163c3
  modified: 2026-07-28T09:50:19.181Z
---

**2026-07-28.** `ProofSystem.lean` reordered into three families (A reading 10 /
B glue 4 / C Löb 8 — C complete); 7 positional `Pf.rec` sites permuted in lockstep
(ProofSystem §4, Soundness ×2, T42/T48×2/T31×2); build green. `PfG` mirror in
Decidability still uses the OLD constructor order internally (harmless, cosmetic).

**Completion arc** (design: `Research/Notes/FAMILY_COMPLETION_DESIGN.md`; evidence:
`Research/Spikes/family_completion/FamilyCompletionSpike.lean`, compiles clean):
- Family B finishers: `implRefl`, `implK`, `contrapose`, `negElim` — soundness
  certificates kernel-checked; `implRefl` PROVABLY absent from current S (corollary
  of `dbot_no_provable_forbidden`); `implK`+`mp` derives `weakenImpl`.
- **KEY FINDING**: `implRefl`/`implK` FALSIFY the tail-recursing census invariant
  (`Forbidden(.impl _ ψ) := Forbidden ψ`) used by ALL exclusion proofs — machine-
  checked falsification. Repair (validated): `Guarded(.impl α ψ) := Guarded ψ ∧
  ¬Guarded α`; premise-carrying rules close via by_cases on the antecedent.
- Family A closer: `ctxBranch` over an `EvalCtx` telescope (searchT/iteT layers,
  plug/guards/implChain); soundness core `evalCtx_sound` proven against the real
  engine; fused rules' conclusions are `rfl`-instances; ite guards stay restricted
  to frame-independent `.sim .opp (.bot z)` (general ite guards frame-dependent =
  unsound).
- **Why not integrated**: any new constructor touches 16 files (PfB/PfG mirrors,
  both deciders' sound+complete, T48 trichotomy, T49 substrate ~40 arms each, T50
  gate, T54); staged order in the note — (1) census regroup into Base/Exclusion on
  Guarded, (2) leaves, (3) neg rules, (4) ctxBranch, (5) closure theorem.
- **STEP 1 DONE (2026-07-28, build green 3237 jobs)**: `TailTo` in Base/Exclusion
  (+@[simp] iffs), generic kernel `no_provable_tailTo_floor` (one strong-induction;
  probeFirst/botOpp/searcherPlay floors are instances), budget-free
  `no_provable_tailTo_unreadable` absorbed the 4 hand-rolled CIMCIC/DIMCID censuses
  (~10-line instances now); 6 floor consumers = statement swap only. Engine now
  closed under implRefl/implK BEFORE they land. rightTail kept but census-unused.
  Proof-craft: glue arms = by_cases on antecedent using BOTH ihs; bridge arms =
  obtain ⟨h1,-⟩ then plays.injEq; ⟨rfl, by simp [BotDefs]⟩ discharges guard TailTo.

**Why:** Colomban wants S "almost exhaustive" then frozen (constructors converge,
lemma library grows freely). **How to apply:** before adding ANY constructor, swap
censuses to the Guarded invariant first, else every exclusion theorem breaks as
stated. Spike traps recorded at the bottom of the design note.
- **STEP 2 DONE (2026-07-28, full build green 3237 jobs)**: `implRefl`/`implK` are
  `Pf` CONSTRUCTORS (24 total, Family B=6). Carried through ALL 16 metatheory files.
  Key per-file facts for step 3/4: PfG mirror appends new ctors LAST (PfG order ≠ Pf
  order — its positional recursor sites differ); `chkLeaf` gained chkImplRefl/chkImplK
  (or-chain now 9 wide — rcases patterns updated); T48 `pf_posImpl_ant` gained the
  honest size-paid 3rd leg `(impl B C).size ≤ m` (the leaves' arbitrary spines force
  it; T48 dichotomy/trichotomy are T48-INTERNAL, no downstream consumers); trichotomy
  cases discharged via the §9 vacuity witness; T49 ProvT gained 2 leaf NODES (NOT via
  LeafPf — leafPf_shape/DAnt can't hold them): boxInvGo treats implRefl's discharge AS
  the consequent's walker, implK wraps 1st discharge in weakenImpl / drops the 2nd;
  T51 got helper `ModChain_not_modest`. Spike §3 flipped to positive demo.
- **STEP 3 DONE (2026-07-28, build green 3237): FAMILY B COMPLETE** — `contrapose` +
  `negElim` landed; Pf = 26 constructors (B=8 = Hilbert basis minus deduction thm).
  Craft facts: negElim VACUOUS (premises contradictory by soundness) → NO PfG/ProvT
  mirror, NO decider leg, all arms = `absurd (Pf_sound h2) (Pf_sound h1)`; contrapose
  rode chkWeaken as 2nd disjunct via INNER match (or-chains stay 16-wide, firing
  proofs close via first disjunct + true_or); machine-crossed contrapose costs an
  irreducible app node → ProvT.dbFree excludes it (like ITE leaves), boxInvGo none on
  cons (crossWt/fundamentalW both survive); congruence twins T47+T53 both needed the
  new chkWeaken-leg case (negs transparent to playsArgsF/maxLitF; keep ZS atoms
  un-simp'd for omega). Next: step 4 = ctxBranch (family A closure).
- **STEP 4 DONE (2026-07-28, build green 3237): `searchChain` LANDED** — Pf = 27
  constructors; family A closed over search-only telescopes at every depth. Craft:
  head layer kept in constructor form (conclusion always .impl(.box…)… — keeps
  box_inversion/atomize index-refuted); Exclusion kernel gained `hplug : ∀ L, P ≠
  searchPlug L (.const aTgt)`; decider leg = real lockstep parser (chkChainGo, sound
  via size-strong-induction + nested cases — `induction φ` IMPOSSIBLE, Formula is
  mutual!); Action == lacks LawfulBEq → use `decide (a = a')` in checkers; T49 =
  dbFree-excluded leaf, no-core spine via implChain_endsInPlays; T51 via
  ModChain_chain_plays (generalize-then-cases to avoid delta-unification on tgtD).
  **OPEN: ite-layer telescopes need the antecedent-provenance census redesign**
  (probe antecedents are cheap atoms — Guarded/TailTo can't price them; T48 §10's
  PosImplCtx program). Step 5 (closure theorem) also open.
- **STEP 5 DONE (2026-07-28, build green 3238): Base/Closure.lean** — kernel-checked
  closure certificates: identity_provable, weakenImpl_from_implK,
  searchChain_reads_all_depths, searchBranch_from_searchChain (const-else lifted),
  and searchThenSearch_t_from_searchChain (stacked primitive REDUNDANT: telescope +
  boxIntro/boxMono/weakenImpl/impS2; all budgets by le_refl-sums). **PROGRAM
  COMPLETE except ONE HUMAN DECISION: ite-probe reading FLIPS OUTCOMES** —
  probe antecedents are cheap atom certs → mp extracts simulator plays →
  CIMCIC-vs-DBot flips (D,C)→(C,C) etc.; requires the budget-threaded
  antecedent-provenance census (SpineW witnesses; mp arithmetic closes, implTrans
  needs pf_impl_size cut bookkeeping) + re-deriving flipped outcomes. Both choices
  Critch-defensible; recorded in FAMILY_COMPLETION_DESIGN.md's decision section.
- **ITE-FRONTIER CORRECTED (2026-07-28, ProvenanceSpike.lean kernel-checked)**: the
  earlier flip-claim was WRONG — probe antecedents are eval-TRUE but UNCERTIFIABLE
  (cimcic_probe_uncertifiable: search_t dies on census, search_f on soundness) or
  floor-priced → **full ite-reading flips NO outcome**; only the census architecture
  needs the suffix-class provenance kernel (SpineW.extract certified; mp-arm ledger
  closes, implTrans hits the cut-size wall → suffix-class design). CLOSURE AUDIT
  (Colomban's challenge): B complete per checklist NOT per tautology-completeness
  (S/contraposition only rule-form; exchange/Peirce unsettled; certifiable target =
  axiom-forms + ADMISSIBLE deduction metatheorem + completeness); C complete FOR
  PURPOSE (bounded Löb derivable) not vs bounded-GL; A = search-closure certified,
  remainder = mixed telescopes (i) + simulator transparency (ii) + sim-composition
  lemmas (d); frame-dependent ite-guards excluded ON PRINCIPLE (unsound).
- **ITE FRONTIER LANDED (then-polarity), 2026-07-28**: Pf.ctxChain (28th ctor, HEAD-EXPLICIT
  conclusion `.impl (ctxGuard me opp hd) (implChain …)` — implChain-opaque draft broke T48
  box_inversion dependent elim; searchChain's design lesson applies to EVERY telescope rule).
  CtxLayer = searchL | iteL (then-descent only, probe `.sim .opp (.bot z)`); subsumes
  searchChain + iteBranchSearch_t (Closure certs, the latter DEFINITIONAL). Census: TailToS
  set-kernel (action-refined kills; hibs S-closure; hctx decomposition discipline), singleton
  wrapper +hctx param; 13 consumers = one const_ne_ctxPlug bullet each; NO statement/outcome
  changed. Parser chkCtxGo/chkCtxChain (lockstep, ite-arm pattern `.ite (.sim .opp (.bot z))`)
  into decFull/decB/decG; T49 ProvT dbFree-excluded (~30 mirror arms); T51 via
  chainHead_guard_not_modest. **ELSE-polarity BLOCKED — kernel-grade counterexample**: implTrans
  ∘ (Cupod searchBranch self-read □_k(gC-inst)→CupodD-vs-botCoop) ∘ (OBot else-chain) = provable
  Guarded-classed chain to the OBot floor target → no_provable_OBot_D_tail FALSE as stated;
  repair needs recursively-closed avoid-set (axKf defeats every finite widening: plays-only,
  truth-conditioned, box-content-exempt all fail). Else adds NO extractable theorem (probes
  priced/false) → deferred honestly. Build 3238 jobs green. PY-PATCH TRAP: assert-then-write
  scripts lose ALL edits if a later assert fires — write incrementally or assert first.
- **FAMILY-A REMAINDERS CLOSED (2026-07-28, follow-up)**: (d) composition certs LANDED
  (read_compose/simStep_compose/botSimStep_compose in Base/Closure — sim-depth-n =
  iterated implTrans, no new constructor). ELSE-POLARITY: skeleton VALIDATED
  (ProvenanceSpike §4, kernel-checked): `Bad` invariant = chains-to-S + BOX/DIAG
  TRANSPARENCY (kills axKf wall: bad_axKf_not — box-content mirrors impl structure,
  self-annihilation like implRefl-under-Guarded) + SELF-BOX EXEMPTION `¬Bad α ∨ α=□_n ψ`
  (kills diag wall: diagB premises classed via bad_lob_premise, diagF excluded,
  counterexample legs excluded). OPEN RESIDUAL = implTrans-cut leak: conclusion □_nT→T
  exemption-classed, cut Bad-ψ: premise-1 □_nT→ψ unclassed-yet-unprovable, no recursion
  target. Next family-A attacker starts at the Bad-kernel implTrans arm. Family B
  queued next: tautology-completeness target (S/contraposition axiom-forms + ADMISSIBLE
  deduction metatheorem).
- **ELSE-POLARITY VERDICT (2026-07-28, third pass — DO NOT retry as an integration
  task)**: invariant pushed to v3 (diag-OPACITY + gate-recursion; TARGET/GUARD SORT
  SPLIT — BadT acceptance is the only separator of provable searchBranch box-heads
  (content ∈ Sg) from unprovable box-of-target heads (content chains to St), shape
  conditions CANNOT do it since S proves GL-invalid box-elim by design; boxCore
  comparison kills boxMono/box4 factories, keeps Löb β=ψ). v3 leak: impS2 corner at
  box-tower-height-mismatched cuts (one premise provable via atomBoxImpl, other
  unprovable-unclassifiable). 4 refinement rounds, each spawning a more exotic corner
  = needs cut-elimination-strength machinery over the modal tier. Thesis-chapter-scale
  research track; else adds ZERO extractable theorems so deferral is consequence-free.
  Attack ladder recorded in ProvenanceSpike §4.
- **FAMILY B COMPLETED (2026-07-28, one-pass)**: Pf.implS landed (29 ctors, 16-file
  recipe; census: SELF-ANNIHILATION like implRefl/implK — positive axioms whose
  antecedents carry their consequents annihilate; verified for K/S/Peirce/identity).
  DEDUCTION THEOREM ADMISSIBLE (Closure.Deriv + deduction_theorem: hypo→implRefl,
  thm→weakenImpl, mp→impS2 — impS2 IS the deduction theorem's mp-case).
  identity_from_KS (SKK=I). T49 for implS: freeS2 := False (it IS the S-contraction);
  walker = depth-3 RAW-APP composition (d1⊛d3)⊛(d2⊛d3) (NOT an impS2-node — its s2d+1
  breaks crossS2d's MAX-ledger); gateOK/cutsOK(implS) := G ψ (the crossing's cut
  diet — NOT True, else crossGateOK/T50-transport break; transport arm passes hc
  through); fundamental arm = Good_app² over stack discharges. **PEIRCE REVERTED —
  SUBSTRATE-BLOCKED**: sound + census-safe, but crossing = call/cc; boxInvGo is a
  constructive λ-evaluator; total `fundamental` falsified (core-tailed good stacks
  exist, no walker term). THE SUBSTRATE IS INTUITIONISTIC — classical → stays
  rule-level. Neg-axiom-forms census-blocked (false-antecedent wall = ite-else wall;
  ONE unified open problem blocks both remaining cells). B = complete intuitionistic
  positive fragment, certified.
- **CIMCIC vs OBot = the wall's first OUTCOME casualty (2026-07-28)**: determined (D,D),
  PROVEN 2026-07-27 pre-completion (git 621d183, never landed in library), proof now
  DOUBLY dead: unguarded right-tail class falsified by implRefl; Guarded/TailToS
  falsified by ctxChain (OBot then-then decomposition; probe2 = "CIMCIC plays C vs
  botDefect" FALSE over then-readable CIMCIC (then=.const .C = probe2 action) → the
  false-probe wall, THEN-polarity!). The wall is NOT else-only. Re-run agent
  independently re-derived the whole analysis + Lean-verified the falsifying chains,
  correctly refused a constructor proposal (negative metatheorem ≠ rule). New verdict
  taxonomy: open_blocked (parser + prompt). DIMCID vs OBot likely same class. Solving
  the recursive-avoid-set census re-earns both outcomes — concrete bounty.
