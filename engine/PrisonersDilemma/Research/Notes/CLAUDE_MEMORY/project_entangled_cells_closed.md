---
name: entangled-cells-closed
description: "2026-08-21 evening — ALL tau entangled cells are THEOREMS (floor census + mutual Löb through .sys); 13-template zoo total, no open cells; CIMCIC lifted"
metadata: 
  node_type: memory
  type: project
  originSessionId: b183cd9a-24de-42a5-9709-1bb395f61fb9
  modified: 2026-08-21T13:10:34.152Z
---

**2026-08-21 (evening): the entangled `.sys` cells are CLOSED — do not treat them as open.**
Supersedes the morning's "genuinely open / enter as hypotheses (hdc, hcdP)" state in
[[def4-tvote-refactor]] and the cupod milestone notes.

Three mechanisms, all in the library:

1. **Wrapped emission** (fidelity fix): `sysGo` self-arms emit `.bot (.selfIdx j)` —
   uniform with off-cycle `.bot P` freezing. This made entangled guards literal
   `probe`/`probeD` shapes of the wrapped partner component.
2. **The floor decides anti-aligned 2-cycles**: `no_provable_botSysSearcherElse_tail`
   (Base/Exclusion) — if the guard's target ≠ the partner's then-action, `search_t` is
   killed by mismatch and everything else pays the partner's `search_f` floor → both
   bits provably FALSE → both play defaults. Closed cupod×dupoc as `(D, C)` (= base
   red cell) and cimcic×cupod as `(D, C)`. **No bistability survives the cost floor**
   — the JustBot-vs-MirrorBot bistability analogy fails inside `.sys`. The kernel's
   `hbotsys` obligation is now ACTION-REFINED (like hbotsearch); 25 call sites.
3. **Mutual Löb through the binder**: aligned cycles (cimcic×dupoc — each guard's
   target == partner's fire action) cooperate via `botSysSearchStep` +
   `mutual_pblt_engine_id`, transferring base `llm_outcome_CIMCIC_vs_DupocBot`
   verbatim → `outcome_TauCIMCIC_vs_TauDupoc = (C, C)`.

**State**: 13 templates (CIMCIC lifted — first `.impl`-guard row; its row is
IDENTICAL to TauDupoc's), 169 cells all stated, `open_cells() == ()`, every phase
theorem unconditional except `∃k₂` Löb gates. Python `_resolve_entangled` implements
the alignment rule: cooperate-by-Löb iff each member's test (or C for proveImpl)
equals the other's fire action; else floor. Kernel check 169/169; Def-3 coincidence
144 cells / 5 whitelisted.

**Traps recorded**: `weakenImpl` charges the IMPL's formula size (needs
`hL : 100·log2 k + 1000 ≤ k` hypotheses threaded through Columns/phases); omega
needs `Nat.log2 0/1 = 0` by decide for `.sys` index literals; never unfold `c_guard`
on only one side of an omega goal; constructors elaborated against unpeeled `inst`
terms mangle to raw `instGo` (rw ALL peels before `refine`); TailTo needs
`simp only [Formula.subst, Prog.subst, TailTo]` before refuting subst-wrapped atoms.

**Debt PAID (2026-08-21, evening, commit 7af4859)**: the tau closures were
transplanted to base — `outcome_JustBot_vs_CupodBot = (D,C)`,
`outcome_CIMCIC_vs_CupodBot = (D,C)` (FALSIFIED the (C,C) stipulation),
`outcome_CIMCIC_vs_OBot = (D,D)`. First two: generic-opponent else-play floor
censuses (GuardianBot-census pattern; `no_provable_CupodBot_C_tail`,
`no_provable_JustBot_D_tail`); third: SOUNDNESS alone (provable guard would fire
its own search making the false consequent true — eval_det). All ∀k (no Löb
gate) except the OBot pair (weakenImpl threshold). ENLARGED_STIPULATIONS pruned
to the two DIMCID cells; Def-3 coincidence runs on a TOTAL base matrix;
DupocBot/JustBot are PROVEN behavioral twins even with CupodBot admitted.
Remaining stipulated frontier: (DIMCID, CupodBot) (D,D), (DIMCID, DupocBot)
(D,D) — the DIMCID lift should settle both the same way.

**DIMCID LIFTED 2026-08-21 (14th template, commit 5417dd3) — NOT the cheap twin
it looked like.** Needed a DSL extension (`Mode.proveImplD`: `Stage.test` fed
BOTH sides of a proveImpl guard, and a new field would break all 13 positional
spec rows — Lean 4 does not apply structure defaults to `⟨…⟩`). PROVEN: the
diagonal (genuine Löb fixpoint on DEFECTION, staggered box `f k = k - O(log k)`
forced by axK, unlike CIMCIC's free implRefl), the two ground cells, two of
three entangled pairs (anti-aligned → floor: dimcid×dupoc and dimcid×cimcic both
`(C, D)`), and its whole COLUMN — so all 13 prior phases carry their 14th slot.

**BLOCKED: DIMCID's own off-cycle row — a POLARITY obstruction.** Its guard fires
into `D`, so a provable guard FALSIFIES its own antecedent and the implication is
vacuously true; the soundness route that closed `outcome_CIMCIC_vs_OBot` is
therefore unavailable. then-`C` partners still go through (else-play floor);
then-`D` partners (guardian, cupodTroll) need a census the current kernel cannot
express — `botSearchStep` legitimately concludes the target atom from a box the
syntactic census cannot see is unprovable. Three candidate repairs are written
in `Tau/Theorems/TauDIMCID/Helpers.lean` (smallest: a guard-falsity-parameterized
`hbotsearch` slot, mirroring `no_provable_botTwoWatchD`). NOT a bistability —
`Pf.atomNeg` needs a certificate of the very play being assumed, and with the
self-reference through `.bot`-frozen instances there is no diag knot.
Consequently the dimcid×cupod pair (first ALIGNED-on-**D** pair) and TauDIMCID's
own `VoteBits` row are Löb-gated. DIMCID is the zoo's FOURTH floor bot.

Kernel check now 182/182 cells, zero mismatches, `unstated = ("TauDIMCID",)`.

**BASE TRANSPLANTS COMPLETE (2026-08-21, commit e3079e3).** Five base cells now
proven by transplanting tau closures, and the ALIGNMENT RULE predicted every
value before the proof was written:
`outcome_JustBot_vs_CupodBot = (D,C)`, `outcome_CIMCIC_vs_CupodBot = (D,C)`
(falsified a stipulation), `outcome_CIMCIC_vs_OBot = (D,D)`,
`outcome_DIMCID_vs_DupocBot = (C,D)` (**falsified a second stipulation**),
`outcome_DIMCID_vs_CupodBot = (D,D)` (confirmed). ENLARGED_STIPULATIONS is down
to ONE entry: `(PrudentBot, CupodBot) ↦ (D,C)`.

**Proof-craft trap for aligned base pairs**: taking `Bf` to be a plays-atom
forces an `axK` whose obligation `a + k + size ≤ k` is UNSATISFIABLE under the
same-k engine. Take `Bf` to be the impl-guard bot's GUARD FORMULA instead (as
base `llm_outcome_CIMCIC_vs_DupocBot` does) — both legs then stay inside
`implTrans` and no `axK` is needed.

**DIMCID row blocker is a FALSE CENSUS, not a missing hypothesis** (commit
d762f7e, machine-checked): `botSearchStep` proves a formula that genuinely
`TailTo`-tails at the target (box antecedent ≠ plays-atom), so "no Pf tails
here" is FALSE and NO hypothesis refinement can rescue it. The real fix is a
tail predicate forbidding BOX antecedents (`TailToA`), a refactor of the 31-arm
kernel + 25 call sites — deferred until a SECOND bot needs it (WaryBot .neg).

Next lifts: WaryBot (.neg), MirrorBot, LegibleBot, PrudentBot/OptimBot.
