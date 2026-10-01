# EGT findings under PA-`S'` — the `S'` twin of `EGT_FINDINGS.md`

*2026-10-01. Phase 5 of `SPRIME_SOURCE_OF_TRUTH.md`: the six frozen paper sweeps re-run with the
PA-`S'` cells as the source (`--source sprime`, `FloorPolicy = engine_side`), read with the same
toolchain, and every engine finding F1–F7 re-stated against its `S'` counterpart. Same section
structure as `EGT_FINDINGS.md`; the engine numbers quoted here are the ones recorded there (and, for
the full engine Moran ladder, in the verified memory note `project_base_zoo_egt_numbers.md`) — this
worktree holds no engine runs.*

---

## 1. What was run (provenance)

Code state: commit `ceea086` (branch `colomban-route-b`), runs written 2026-09-30 18:10 → 2026-10-01
02:18 under `app/generated/egt/runs/<zoo>_sprime[_<family>]_t…_a…_<fp>/` (95 directories). Cells:
`app/generated/sprime_outcome_theorems.json` (`system: sprime`, digest `17364852590439865859`, 107
theorems + 26 floor dichotomies; the engine export it replaces: digest `6922152188568947437`, 155
theorems). Every `summary.json` carries `cell_source: "sprime"`, `is_fully_proven: true`,
`stipulated_cells: []` and its `floor_cells` list (`ess/assumptions.json` repeats them).

| zoo | family | grid | distinct matrices (engine) | wallclock | `floor_cells` per run |
|---|---|---|---|---|---|
| `body` (10) | behavioral | 6×6 | 15 (16) | 290.4 s | 8 ordered = 4 pairs |
| `body` | syntactic | 6×6 | 16 (16) | 132.5 s | 8 = 4 pairs |
| `body+twins` (12) | behavioral | 6×6 | 17 (17) | 807.2 s | 25 ordered = 13 pairs (Prudent×Prudent once) |
| `body+twins` | syntactic | 6×6 | 17 (15) | 1447.4 s | 25 = 13 pairs |
| `body+twins+natives` (14) | behavioral | 6×6 | 17 (18) | 5865.1 s | 41 ordered = the 13 pairs + the two natives' clones of DupocBot's four floors |
| `body+twins+natives` | epsilon | 6×6 | 13 (12) | 3997.8 s | 41 |

Distinct-matrix counts and `floor_cells` from `runs/*/summary.json`; wallclocks from the sweep
driver's `sweep done` lines (the three surviving top-level `sweep_summary*.json` — natives/behavioral
5865.06 s, twins/syntactic 1447.39 s, natives/epsilon 3997.83 s — agree; the other three were
clobbered, as the engine note warns). Grid t ∈ {0, 0.2, 0.4, 0.6, 0.8, 1.0} × α ∈ {0, 0.3, 0.45,
0.62, 0.8, 1.0}; payoffs b=3, c=1 (`(D,C)=b, (C,C)=b−c, (D,D)=0, (C,D)=−c`); Moran M ∈ {10, 50, 100}
× β ∈ {0.01, 0.1, 1}; "the headline" = M=100, β=1. NOT re-run: `critch8`; the per-zoo tau-layer
reports (`generated/tau_report_*.html` are dated 2026-09-09, i.e. engine-era).

Integrity (`python -m pd_runner.egt.integrity`, 95 run directories): **0 hard failures**; sole soft
finding = Nash cross-check absent in 95/95 runs (`lrsnash` not installed — the same Limitations
sentence). Anchors OK: at t=1 (α>0) both families of a zoo share the base matrix's fingerprint
(`body` b6f236fdf423, `body+twins` 83a8502130b7, `body+twins+natives` f50f03268a55).
**VERDICT: CLEAN.**

## 2. Conventions — what changes under `S'`

* **Provenance of the cells** (`app/generated/source_diff.md`). Body zoo, 55 unordered pairs: 44
  agree with the engine, 7 FLIP, 4 are floor pairs. Twins zoos (12 base bots), 78 pairs: 56 / 9 / 13
  (14 floor rows — Cupod×Prudent has a dichotomy in each orientation). `critch8`: 33 / 0 / 3.
* **The floor policy.** Under `engine_side` a floor pair takes the engine's value (`¬A_k`, the
  dichotomy's engine-side branch), so the body's four floors — Cupod×OBot (C,D), CupodTroll×Dupoc
  (C,D), DBot×Dupoc (C,D), Dupoc×EBot (D,C) — are BYTE-IDENTICAL to the engine's cells; they are
  labelled, not changed. Consequently **every difference between this record and `EGT_FINDINGS.md`
  on the body zoo is downstream of DIMCID's seven flips** (CooperateBot, CupodTrollBot, DBot: (C,C) →
  (C,D); DupocBot, OBot: (C,D) → (D,D); EBot, TitForTatBot: (C,C) → (D,D)). On the twins zoos the
  CIMCIC×DIMCID (D,C) → (D,D) and DIMCID×PrudentBot (C,D) → (D,D) flips come on top; the 13 floor
  pairs are again engine values.
* **DIMCID's row.** In `S'` DIMCID defects against every closed program, so at t=1 its payoff row is
  DefectBot's row to the digit (`runs/body_sprime_t100_a030_b6f236fdf423/ess/payoff_matrix_numeric.csv`:
  both `3 0 3 3 0 0 0 0 0 0`) and its stationary share equals DefectBot's at all 9 (M, β) points
  (`moran/stationary.json`). DIMCID is a PAYOFF-EXACT twin of DefectBot: it joins every SS set
  DefectBot is in (`DIM+Def` throughout `phase_maps.md`), and the body zoo is no longer twin-free.
* **Pure ESS: 0 on all 95 matrices** (`tidy.csv`, `n_pure_ess`); the engine record's single
  exception (EBot at body/syntactic (0.2, 0.8), memory note) does not recur.
* Everything else in the engine's §2 stands verbatim — α=0 degenerate; "uniquely stochastically
  stable" is a strong-selection claim (robustness is still 6/9 at t=1 on body, 8/9 on twins, 7/9 on
  natives, `findings.md` §3); per-region reporting; vertex counts are geometry; the natives'
  behavioral run is the twinning observation, never the ablation; basins group by support. The
  **identity ≠ cooperation** rule becomes load-bearing for F3′ (below).

## 3. The toolchain (unchanged)

The four modules of the engine note (`integrity`, `analysis`, `findings`, `nash_structure`) ran
unmodified over `generated/egt/runs/`; outputs under `generated/egt/analysis/` (`tidy.csv` 216 rows,
`phase_maps.md`, `family_diffs.md`, `findings.md`, `nash_structure.{csv,md}`, six
`fig_collapse_*.png`) are **the `S'` results** — the engine's were overwritten and live only in
`EGT_FINDINGS.md`. The only switch is the pipeline's `--source sprime` (`pipeline.py`): it is hashed
into the run-directory name (`_sprime`), and `summary.json`/`assumptions.json` carry `cell_source`
and `floor_cells`. Drill-downs used as before: `moran/stationary.json`, `nash_structure.csv`
(`max_ne_coop` = static ceiling, `realized_coop` = stationary cooperation rate at M=100/β=1),
`ess/payoff_matrix_numeric.csv`.

## 4. Findings F1′–F7′, each against the engine's F1–F7

**F1′ — Baseline (body, t=1). SURVIVES; the vertex count moves.** `S'`: 0 pure ESS, **33 extreme NE
in 3 components** (engine 21 in 3), **5 stable faces / 1013 supports** (engine 6), **invasion SCCs 4**
(engine 3), replicator dominant support {Coop, Dup, TFT} with a **94% basin** (engine 95%), realized
stationary cooperation 0.924 (engine 0.9426); DupocBot's share rises **11% → 87%** with selection
(engine 11% → 89%; full ladder in §5), SS set {Dup} at the same 6/9 points as the engine (empty at
(10, 0.01); Dup+TFT at (50, 0.1) and (100, 0.01)). (`findings.md` §1, `tidy.csv`.) The component
count — the statistic the paper reports — is unchanged; the extra 12 vertices and the fourth SCC are
DefectBot's new twin.

**F2′ — Critical transparency (body/behavioral). SHIFTS.** Engine: Dup uniquely SS on all of
t ∈ [0.4, 1] × α ∈ [0.3, 0.8]; collapse between 0.4 and 0.2, latest for α ∈ {0.45, 0.62}; t=0 =
defector ties. `S'` (`findings.md` §2, `phase_maps.md`): Dup uniquely SS on t ∈ [0.4, 1] for
α ∈ {0.3, 0.45, 0.62} and at (0.8, 0.8) — but **at α = 0.8 TFT is the unique SS type at t = 0.6 and
0.4** (realized cooperation 0.950 / 0.874, `nash_structure.csv`: cooperation persists, the carrier
changes); Dup survives at t = 0.2 for α ∈ {0.3, 0.45, 0.62} (engine: 0.45, 0.62 only) and at
(0, 0.3) with 66% of the stationary mass; at (0.2, 0.8) the SS set is the defector tie
DIM+Def+Dup+EB+OB. **t = 0:** α = 0.45 a four-way tie DIM+Def+Dup+OB at 25% each; α = 0.62 NO SS set
(seven types at 14.3%). α = 1 dies immediately below t=1 (unchanged). Net: the collapse band moves
DOWN one grid step for α ≤ 0.62 (0.2 → 0 instead of 0.4 → 0.2), the α = 0.8 column is TFT's, and the
t=0 ties now contain DIMCID. Syntactic channel for contrast: α = 0.3 ends in Def (82.6%) at t=0,
α = 0.62 departs at t=0.2 (Dup+OB), α = 0.8 at 0.6 (DIM+Def).

**F3′ — Static and dynamic collapses. SHIFTS: the coincidence survives in COOPERATION, not in
SS identity.** Engine: t_static = t_moran at every α (0.45→0, 0.62→0.2, 0.8→0.4, 1→0.8), realized
cooperation tracks the static ceiling, stable faces → 0 below the collapse. `S'` body/behavioral
(`nash_structure.md`): α = 0.45 → 0.0/0.0 and α = 1 → 0.8/0.8 coincide; **α = 0.62: t_static 0.2 vs
t_moran 0.0**; **α = 0.8: t_static 0.2 vs t_moran 0.6** — 2 of 4. Reading the same rows through
`realized_coop`: at (0.2, 0.62) Dup is SS with realized cooperation **0.035** under a ceiling of 0.0
— the Löbian IDENTITY survives one step further as a DEFECTOR (the engine's §2 warning, now
realized); at (0.6, 0.8)/(0.4, 0.8) TFT is SS with 0.950/0.874 under a ceiling of 1.0 — the identity
changes, cooperation does not. So "the population saturates what rationality permits" holds at every
α on `S'` as well; what decoupled is the SS-set-departure marker `t_moran`. On body/**syntactic** the
two markers coincide exactly at all five α (0.0/0.0, 0.0/0.0, 0.2/0.2, 0.6/0.6, 0.8/0.8). The
asymmetric α = 0.3 exception survives (t_static = none; realized cooperation 0.924 → 0.677 at t=0;
engine ~0.64). "Stable faces → 0 below the collapse" SHIFTS: 4 at (0.2, 0.62) and 3 at (0.2, 0.8)
under a zero ceiling; 0 only at t=0 and along the α = 1 row. (`fig_collapse_body_behavioral.png`.)

**F4′ — Confusion structure at matched information. SURVIVES in cooperation terms; the citable
instance must be re-stated.** Disagreement counts (`family_diffs.md`): body 8/36 (engine 7/36),
body+twins 7/36 (7/36), natives behavioral-vs-epsilon 11/36 (14/36). The engine's sharpest instance
(α = 0.8: syntactic dies at t* = 0.6, behavioral at 0.4) no longer separates at the SS level — BOTH
depart Dup at 0.6 (syntactic → DIM+Def, behavioral → TFT) — but the cooperation contrast is sharper:
realized cooperation **0.219 (syntactic) vs 0.950 (behavioral) at t = 0.6, 0.012 vs 0.874 at
t = 0.4**; static ceiling 0.61 → 0 on syntactic vs 1.0 through t = 0.4 on behavioral; t_static 0.6
vs 0.2. HIGH CAUTION UNDER SOURCE-BLUR STILL FAILS EARLIER THAN UNDER BEHAVIOR-BLUR — by two grid
steps in realized cooperation and in the static ceiling, not by one step in the SS set.

**F5′ — The aggregator ablation. SURVIVES (shares move by 2–5 points).** `body+twins+natives`/epsilon
at M=100/β=1 (`findings.md` §4): for t ≥ 0.6 the Löbian class {Dup, CIM, Max, Min} holds **95%** in
the neutral split (sum 47%, max 24%, min 24% — identical to the engine's); MinConfidence exits first
(0% at (0.4, 0.3), as before); the mid-blur band is MaxConfidence alone at **85% at (0.2, 0.45), 85%
at (0.2, 0.62), 87% at (0.6, 0.8)** (engine 89–90%); at α = 1 everything flattens to a 31% class
total with no SS set. Ordering pessimist < expectation < optimist unchanged.

**F6′ — Zoo sensitivity. SURVIVES.** body → body+twins (behavioral) changes the SS set at **24/30**
points (engine 24/30), **28/30** twins-zoo points have a mixed {Dup, CIM} dominant support (engine
29/30), and at t=1 all five α>0 changes are Dup → CIM+Dup (`findings.md` §5). Twins zoo at t=1:
CIM = Dup = **45.6%** each (engine 45.8), robustness 8/9, basin 0.980, realized cooperation 0.945
(engine 0.9495). The class is robust under `S'` exactly as under `S`; the one new feature is that the
t=0 ties carry DIM beside Def (e.g. (0, 0.45): CIM+DIM+Def+Dup+OB+Pru).

**F7′ — The Max band under twinning. SURVIVES verbatim; the bonus gains a member.** On the 14-bot
behavioral run MaxConfidence is uniquely SS at exactly the engine's four cells {(0.2, 0.45),
(0.2, 0.62), (0.4, 0.62), (0.4, 0.8)} (`findings.md` §6). The low-α SS set is now
**DIM+Def+Pru+TFT** at (0.6, 0.3), (0.4, 0.3), (0.6, 0.45), (0.6, 0.62) — the engine's {Def, Pru,
TFT} plus DIMCID, which surfaces for the same reason PrudentBot does: it is DefectBot's payoff twin.
Every t* on this run is 0.6 (`findings.md` §2; the engine's per-α t* for this run was not recorded).

## 5. The Moran ladder (body, t=1) under `S'`, and the t=0 ties

DupocBot's share of the stationary distribution, `S'` (engine in parentheses, from the verified
memory note; `runs/body_sprime_t100_a030_b6f236fdf423/moran/stationary.json`):

| M \ β | 0.01 | 0.1 | 1 |
|---|---|---|---|
| 10 | 11.2 (11.5) | 24.2 (27.1) | 58.5 (59.8) |
| 50 | 17.4 (18.8) | 55.0 (56.5) | 80.5 (82.0) |
| 100 | 25.7 (28.5) | 65.0 (66.5) | **87.1** (88.5) |

SS set {Dup} at the same 6/9 points (empty at (10, 0.01); Dup+TFT at (50, 0.1) and (100, 0.01)).
The `CLAUDE.md` diagonal "27% → 56% → 82% → 88%" reads **24% → 55% → 80% → 87%** under `S'`; the
runner-up at the headline is TFT 3.2%, then DIMCID = DefectBot 3.0% each. **t = 0 (M=100, β=1):**
α = 0.3 → {Dup} at 66.0% (syntactic channel: {Def} at 82.6%); α = 0.45 → the four-way tie
{DIMCID, DefectBot, DupocBot, OBot} at 25.0% each (engine: {DefectBot, DupocBot, OBot}); α = 0.62 →
no stochastically stable set, seven types (Cupod, OBot, TFT, Def, Dup, EBot, DIMCID) at 14.3% each
(engine: {DefectBot, DupocBot, EBot, OBot}). The §5 narrative of the engine note (Nash cannot
select, ESS returns nothing, replicator 94% conditional on starts, Moran decides) stands; the
one-breath summary must read "robustly down to t ≈ 0.4 for α ≤ 0.62, with the collapse to defection
between 0.2 and 0, and TFT replacing DupocBot at α = 0.8 before that".

## 6. Side by side — engine (`S`) vs `S'` (headline = M=100, β=1; `tidy.csv`, `nash_structure.csv`)

| metric | body `S` | body `S'` | twins `S` | twins `S'` | natives `S` | natives `S'` |
|---|---|---|---|---|---|---|
| extreme NE (t=1) | 21 | 33 | not recorded | 100 | not recorded | 292 |
| NE components | 3 | 3 | not recorded | 2 | not recorded | 2 |
| stable faces / supports | 6 / 1013 | 5 / 1013 | n.r. | 5 / 4083 | n.r. | 5 / 16369 |
| invasion SCCs | 3 | 4 | n.r. | 6 | n.r. | 8 |
| replicator dominant support, basin | {Coop, Dup, TFT} 95% | same, 94% | mixed {Dup, CIM}, 0.980 | {CIM, Coop, Dup, TFT} 0.980 | n.r. | {CIM, Coop, Dup, Max, Min, TFT} 0.985 |
| Dupoc share, M=100 β=1 | 88.5% | 87.1% | 45.8% (= CIM) | 45.6% (= CIM) | ≈24% each of 4 | 23.7% each of 4 |
| realized cooperation, t=1 | 0.9426 | 0.924 | 0.9495 | 0.945 | n.r. | 0.972 |
| SS at (1, 0.45) | Dup | Dup | CIM+Dup | CIM+Dup | CIM+Dup+Max+Min | CIM+Dup+Max+Min |
| SS at (0.4, 0.45) | Dup | Dup | n.r. | CIM+Dup | n.r. | TFT (beh.) / CIM+Dup+Max+Min (eps.) |
| SS at (0.2, 0.45) | Dup | Dup | n.r. | CIM+Dup | Max (beh., F7) | Max (beh. and eps.) |
| SS at (0, 0.45) | Def+Dup+OB | DIM+Def+Dup+OB | n.r. | CIM+DIM+Def+Dup+OB+Pru | n.r. | CIM+DIM+Def+Dup+Max+OB+Pru |
| SS at (0, 0.62) | Def+Dup+EB+OB | — (none) | n.r. | CIM | n.r. | CIM+DIM+Def+Dup+Max+OB+Pru |

Body syntactic coincides with body behavioral at t=1 (anchor) and at the listed points except
(0.4, 0.45): 7 stable faces, and (0.2, 0.45): 42 extreme NE, 2 stable faces, 6 SCCs, basin 0.866 —
SS still Dup at both. Twins/syntactic likewise except (0.4, 0.45): 100 NE in 2 components, 7 faces
(behavioral 101 / 3 / 5), and (0.2, 0.45): 72 NE, 2 faces, 8 SCCs. "n.r." = not recorded in
`EGT_FINDINGS.md` or the memory note; "not computed" nowhere — every `S'` cell above exists.

## 7. What the paper must change, and what stays

**Must change.**
1. The "twin-free body zoo whose behavioral σ-scale spans [0, 1]" sentence: DIMCID is a payoff-exact
   twin of DefectBot under `S'` (§2); the body zoo has one twin pair, and the confusion-structure
   comparison (F4′) must be read with that in mind — the behavioral channel now blurs DIMCID into
   DefectBot by construction.
2. The collapse-point statements of F2/F3: "between 0.4 and 0.2" → "between 0.2 and 0 for
   α ≤ 0.62; TFT replaces DupocBot at α = 0.8 for t ∈ {0.6, 0.4}"; the F3 coincidence must be
   claimed for REALIZED COOPERATION against the static ceiling (holds at every α on both channels),
   not for the SS-set departure (2/4 on behavioral, 5/5 on syntactic); drop "stable faces → 0 below
   the collapse" or restrict it to t=0 and α = 1.
3. The t=0 ties: {Def, Dup, OB} → {DIMCID, Def, Dup, OB} at α = 0.45; the α = 0.62 four-way tie is
   gone (no SS set — seven types at 1/7 each).
4. The F4 citable instance: state it as the realized-cooperation gap (0.22 vs 0.95 at (0.6, 0.8);
   t_static 0.6 vs 0.2), not as "t* = 0.6 vs 0.4".
5. The ladder numbers: 11 → 87% (headline 87.1%), diagonal 24/55/80/87; F5's Max band 85–87%
   (was 89–90%); F6's 28/30 (was 29/30); F1's 33 extreme NE, 5 stable faces, 4 SCCs, 94% basin;
   `CLAUDE.md`'s "headline result" paragraph accordingly. Add the F1 sentence "0 pure ESS on all 95
   matrices" (the engine's one EBot exception does not recur).
6. Provenance: cells are PA-`S'` theorems (107) plus 26 labelled floor dichotomies carried at the
   engine-side value; 95 runs; `lrsnash` absent 95/95.

**Stays verbatim.** The two-analyses design and its ESS/Nash/replicator/Moran ladder (§5); F1's
component count (3) and dominant support; F2's qualitative headline — DupocBot uniquely SS at full
and high transparency and its share rising with selection; F3's saturation statement and the α = 0.3
asymmetric exception; F4's direction (source-blur fails earlier under high caution); F5 in full
(95% neutral split, Min exits first, Max band, α = 1 flattening, the aggregator ordering); F6's
class-level robustness (24/30, Dup → CIM+Dup at t=1, CIM = Dup shares, 8/9); F7's four Max cells;
the α = 1 knife edge; every §2 convention; the Limitations sentence on the Nash cross-check. Open
items of the engine's §7 remain open (`critch8` unswept under either source; tau-layer figures not
regenerated under `S'`; finer-t robustness of the F3 coincidence — now more pressing, since the two
markers already separate at grid resolution).
