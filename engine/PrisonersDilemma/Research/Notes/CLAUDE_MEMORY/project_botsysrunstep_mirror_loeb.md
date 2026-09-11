---
name: tau-tree-dsl-mirror-closed
description: "2026-08-24/25 — tau Spec DSL is a TREE; τ(Mirror) = sim self; all 16 phases unconditional (tower census for DIMCID); PrudentBot ported at ONE budget via Pf.botSysSearchThenSearch; certification 225/219/6 (TauTFTPf uncompared); porting CLOSED at 16 (Wary/Legible/Optim excluded)"
metadata:
  type: project
---

**2026-08-24: the tau DSL became a TREE, and every mirror gate closed.** Supersedes
the mid-day state (botSysRunStep, 2/5 gates) recorded here earlier, and the
"five gates remain" state in [[entangled-cells-closed]].

**The design lesson (Colomban's, and right): the DSL must resemble the base source.**
Def 4 IS the uniform source lift, so `Spec` should be `Prog` with a hole where the
base says "`.opp` facing Q". The old stage list (`⟨mode, target, test, fire⟩` rows +
default) was a decision-list COMPRESSION that covered every classifier but could not
say a FORWARDER: MirrorBot has no test/fire/fall-through. I had encoded it as a
one-stage threshold test — behaviourally identical on {C,D}, intensionally a
different program — and `S` reads shape: a bare `.sim` is legible by ONE rule in
both polarities, an `.ite` needs a rule per branch. That mis-encoding (a) blocked
the mirror×cupod cells (Löb fixpoint on DEFECTION = the else branch) and (b) made
me add a then-only core rule. Roadmap §6.1 had explicitly recorded "MirrorBot's raw
copy: out of scope by design"; I smuggled it in through the cascade door.

**Now:** `Spec ι = const a | sim (t : Target) | ite g test p q | search (m : Mode) t test p q`,
`Mode = prove | proveImpl | proveImplD | proveEq` (`run` is gone: it is `ite ∘ sim`).
All 15 rows rewritten as trees (they read like `Bots/*.lean`). τ(Mirror) = `.sim .self`.
Compiler: `instAt` (the ONE entanglement dispatch, per instance — the old one sat
inside the self-stage arm and discarded the cascade continuation), `instGo`,
`sysGo`, with `guardOf`/`eqGuardOf` factoring the guard shapes. Gate: every
classifier's compiled term is BYTE-IDENTICAL — Zoo.lean's `rfl` peels + every
phase theorem's pinned shape closed with ZERO theorem edits; only τ(Mirror)'s
term moved.

**Core:** `Pf.botSysSimStep` (defs i j a me opp; `hget : get? i = .sim (.bot (.selfIdx j)) (.bot (.selfIdx j))`)
concludes `(plays (bot sys j) (bot sys j) a) → (plays me opp a)`, action-generic —
the `.sys` twin of `botSimStep`. It REPLACED `botSysRunStep` (same 33 census sites;
`hbotsyssim` slot appended LAST in `no_provable_tailToS_floor`, 3 binders `defs i j`).
`pblt_engine_id_bounded`/`pblt_engine_bounded` (Base/Loeb) report `2*m ≤ k` —
needed to RE-CERTIFY a Löb bit at a `proofSearch k` gate. Use these, not the plain
engine, for probe gates.

**All three entangled mirror pairs use the SINGLE-formula engine**: the mirror's
leg is unboxed (forwarder), so the mutual engine cannot fit; chain the partner's
BOXED leg (`sys_cross_at`, now action-generic in shared Helpers; `sys_cross_impl_cim`
hoisted there too) after the mirror's via `implTrans` → `□φ → φ`. Dupoc: φ = mirror
self-C. Cupod: φ = mirror self-D. CIMCIC: φ = the GUARD itself (tau consults by
SELF-play, the guard names the CROSS frame; no frame-transfer rule in `S`, so `implK`
from the consequent + one Löb pass — base `llm_outcome_CIMCIC_vs_MirrorBot` needs
none because base Mirror sims `.opp` against `.self` = the cross frame).

**`Tau/Theorems/Matrix.lean` is GONE (Colomban's call, 2026-08-24 evening).** Tau
players are `.opp`-free, so a match is two INDEPENDENT plays; the per-bot
`Phase.lean` theorems ARE the matrix and the Python certification reads them.

**"Finish all phases unconditional" — state at end of 2026-08-24:** 14 of 15
phases stated, ZERO gated hypotheses anywhere in the phase layer.
- `tauCupod_phase` unconditional: dimcid×cupod (first ALIGNED-on-D pair) closed
  by `mutual_pblt_engine_id` in both orientations (`dimCupSys`/`cupDimSys` in
  TauDIMCID/Helpers — `dcSys`/`cdSys` already meant DUPOC×cupod in TauCupod/Helpers,
  name clash trap). Probe bit at budget k via `sysSearcher_fired_of_plays` (eval
  inversion) + cheap re-cert, as `ps_probe_inst_cimcic_dupoc` does.
- `tauMirror_phase` EXISTS (TauMirror/Phase.lean): `C` below `mirrorMass` (the
  14-slot prefix mass), and honestly `none` above it — the vote commits before
  consulting the divergent diagonal (`Vote.lean`: `VoteList.app` [must be
  `_root_.PD.VoteList.app`], `eval_tvote_prefix_C/none`, `tauPlayer_phase_prefix`).
  Scanner row = 14-slot prefix over `tauOrderInit`, diagonal recorded "N"; base
  `none` compares "N" too (compare.py). Certification: 210 cells / 204 agree /
  same 6 whitelisted, with MirrorBot in FULL_BOTS.
- Three more Löb closures: mirror×cimcic (mirror at head), mirror×dimcid both
  ways (`dimFwd_loeb_premise` generic in the system). Pattern for a forwarder
  partner: Löb on the GUARD via implK from the consequent + single engine.

**THE WALL FELL 2026-08-25 — `Base/TowerCensus.lean`, the tower census.** ALL 15
phases stated + unconditional; certification 225/219/6, no missing rows; DIMCID's
row agrees with base on all 15 cells (obot/guardian/cupodTroll included).
Why both old techniques failed (keep — it is the design rationale): tail census's
class contains `□(partner's guard) → T` (a real theorem); valuation census needs the
forced pair `(bot I, bot P)` — a `.bot` OPPONENT — and `h_nb` is what keeps
`iteBranchSearch_t` sound; in the DIMCID-defects world S derives `¬A`, so no sound
valuation designates A. Proof-theoretic fact: `¬A ⊬ A → T` (no object-level ex falso).
THE KERNEL: a target CHAIN (T → Y → T₃: each = the guard-box of the previous one's
reading rule, ending at a player nothing reads) and per level a TOWER of classes by
box depth: `TowerAt Z dead n (impl a ψ) := TowerAt n ψ ∧ (∀ m ≤ n, ¬TowerAt m a) ∧ ¬dead n a`,
index 0 ends at Z, index n+1 ends at a box of an index-n formula; `DeadAll rest n` =
deeper levels at indices ≤ n+1, ≤ n+2, … . The two exclusions make every
premise-free axiom self-annihilate (implK/implS/box4/axKf/boxMono) and let
mp/implTrans with a box middle be killed by the DEEPER level's already-proven
THEOREM (not an ih — the box index is unbounded, so an ih can't reach it). Prove
levels bottom-up; `DeadAll_cons_kill` packages a level as the next `hdead`.
`tower_census`: 31 arms, 3 axioms. Instantiation: `dimcid_guardian_plays_C`
(3 levels), `dimcid_cupodTroll_plays_C` (2 levels; second target is the `.eq`
atom — `GoodTarget` admits eq-of-distinct). Traps: `cases` substitutes `mp`'s
conclusion index so the field `α` is inaccessible (use the outer φ; antecedent is
φ'); `obtain ⟨…, rfl, rfl⟩` fails when an equality became `D = D` — use `-`;
abbrev targets must be `simp only [Y₂] at h` before a peel `rw`; `grep -c … && …`
breaks a shell chain on a zero count.

**Traps:** the two orientations of a pair are DIFFERENT `.sys` terms (`rfl` fails) —
run Löb once per orientation. `Pf.atom`'s budget stays a metavariable if the
transcript is built inside `refine` — build it as a `have` with a concrete cost.
`ite_f`'s implicit `r`/`a'` must be named explicitly (`(r := .D) (a' := .C)`, ASCII prime).
In the sys-else floor census the `hbotsyssim` arm is a CONSTRUCTOR CLASH (`.search`
vs `.sim`), not a shape kill. Touching ProofSystem.lean = full 3352-job rebuild
(>10 min on OneDrive) — run it in the background.

**PrudentBot PORTED 2026-08-25 (evening), SINGLE budget — Colomban's call ("yes,
single budget"): the tau zoo has ONE `k`; staggered base cells become whitelisted
budget-staggering divergences.** Row = D everywhere but `.mirror = C`; one mechanism
(`TauPrudent/Helpers`): inner `probeD (inst T defect)` is an else-play floor for the
searcher partners (`nested_plays_D_of_inner`), else the OUTER probe fails (soundness /
ebot watch-cost floor / guardian else-floor / `ps_botSys_mismatch_false` for cupod &
dimcid). Mirror cell: NEW core rule `Pf.botSysSearchThenSearch` (`.sys` twin of
`searchThenSearch_t`, ctor placed before `iteBranchSearch_t`; induct/eliminator lambdas
in CONSTRUCTOR order; `hbotsyssts` LAST hypothesis of `no_provable_tailToS_floor`, 17
binders at 33 sites) + `botSysSimStep`, `implTrans`, `pblt_engine_id_bounded`, both
orientations. `no_provable_sysNested_{D,C}_tail`: D-tail = ctor clash on `c0 = C`;
C-tail = killed by the inner guard's unprovability (`hinner`). τ(EBot) gained the
Löb-gated `hpm` hypothesis (third watch); `guardMass` MUST be written as the
right-nested sum (simp cannot re-associate `simMass w + w .prudent`). Certification
256/246/10; whitelist +4 (Prudent×Dupoc, Prudent×Just, both ways: base theorems at
`PrudentBot (2k+64)`). Self-play D (`prudent_quine_plays_D`). Trap: `(inst … .mirror
.defect).size` needs a `rfl` peel in the simp set for the Löb size arithmetic;
`sysClose_subst_probeD` needs `hI : I.sysClose defs = I` (rfl at use sites).
**Tau→base diff (2026-08-25): NO missing base cells over the 15 lifted bots; the 4 staggered pairs got `_samek` theorems** (same-k values (D,D)/(D,D)/(D,C)/(D,C)) via the generic `no_provable_searcherElse_tail` (Base/Exclusion; bare twin of the bot kernel; needs `exfalso` before the ctx-bullet's `cases hd` — that hypothesis is an escape clause, not False). `_samek` names are outside the strict scan; canonical-budget convention still open.

**BASE `outcome_PrudentBot_vs_CupodBot = (D, C)` PROVEN 2026-08-25 (every same k)**: the tau argument transplanted — `no_provable_CupodBot_C_tail k (PrudentBot k)` + new `no_provable_PrudentBot_D_tail` (singleton kernel `no_provable_tailTo_floor` with `no_provable_prudence_self_tail`'s telescope bullets). Last tau stipulation gone: `CUPOD_STIPULATIONS = {}`, default/enlarged zoos fully proven; tests that needed a hole now use the genuinely open (WaryBot, CupodBot). Trap: pass the opponent EXPLICITLY to the tail kernels (`_` leaves TailTo un-unifiable).

**TauTFTPf is compared NOWHERE (Colomban, 2026-08-25 evening)**: no base bot (`BASE_OF` has no entry), its 4 prover-floor whitelist entries removed; certification 225/219/6 over 15 templates, whitelist = the 6 budget-staggering dagger cells only.

**PORTING CLOSED AT 16 (Colomban, 2026-08-25): WaryBot/LegibleBot/OptimBot EXCLUDED** — base rows floor-only/open at one budget (Wary: the `.neg` refutation-floor wall, 5 open base cells; Legible: two-budget box guard, large-k only at `(2k+64) k`). Do NOT propose porting them again unless the base rows get proven first.

**Still out of scope in the DSL:** `.neg`/`.box` guards (WaryBot, LegibleBot) — the
recorded extension is a new `Mode` on `search`, not a new node. τ(Mirror)'s own
VoteBits row is PERMANENTLY unstateable (diagonal `.sim .self .self` = `none`).
