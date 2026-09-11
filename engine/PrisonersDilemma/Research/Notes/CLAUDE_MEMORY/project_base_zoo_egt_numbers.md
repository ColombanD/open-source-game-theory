---
name: base-zoo-egt-numbers
description: Verified §5.1.3 numbers for the body zoo at t=1 (frozen sweep df56c99) + two record errors found (EGT_FINDINGS F1 'no pure ESS anywhere' is FALSE; CLAUDE.md Moran ladder is from a 9-bot re-run)
metadata:
  type: project
---

2026-09-10, workflow-verified against `app/generated/egt/runs/body_t100_a030_3e68620cd1cf` (10-bot body zoo, t=1, fingerprint 3e68620cd1cf; shared by 11 grid points; α=0 corner is the ALL-C matrix, never cite). Material: `latex/notes/sec513_base_zoo_material.md`; tables `latex/tables/moran_body.tex`, `latex/tables/statics_body.tex`.

**Numbers (use these, not CLAUDE.md's):** payoffs b=3,c=1. Matrix: 37 CC / 23 DD / 40 mixed of 100 cells; C-play rate 0.57 (descriptive, tau-layer statistic — NOT in tidy.csv). Statics: 0 pure ESS (Dupoc fails only by 2=2 ties with Coop, TFT); 21 extreme NE in 3 components (C0 full-coop on {Coop,Dup,TFT}; C1 one mixed NE {Coop,EBot,OBot} coop 11/18; C2 all-defect {Def,OBot}) — report COMPONENTS in body, vertices appendix only; 6/1013 stable faces, all invadable; invasion 3 SCCs (Dup, Def sources → 8-bot terminal). Replicator: 201/201 converged; support {Dup,Coop,TFT} basin 0.950 (neutral continuum, spread 0.41) — quote support+basin, not the point. Moran (M∈{10,50,100}×β∈{0.01,0.1,1}): Dupoc share 11.5/27.1/59.8; 18.8/56.5/82.0; 28.5/66.5/88.5 %; SS set {Dup} at 6/9 points (empty at (10,0.01); Dup+TFT at (50,0.1),(100,0.01)); cut = 1.5/N. Realized stationary coop rate (M=100,β=1) 0.9426 vs static ceiling 1.0. Twins zoo (12): CIMCIC is a payoff-exact twin of Dupoc; SS {CIM,Dup} 45.8% each (91.5% combined), 8/9 robustness (cut 0.125); basin 0.980; realized coop 0.9495; F6: SS changes at 24/30 α>0 grid points, at t=1 all five are Dup→CIM+Dup.

**Record errors found:** (1) EGT_FINDINGS.md F1 line 93 "No pure ESS on any zoo/family/point" is FALSE — body/syntactic t=0.2 α=0.8 (run body_syntactic_t020_a080_0792726f07bc) has EBot as a pure ESS; correct = 93/94 matrices. CLAUDE.md Phase-6 "No pure ESS exists on any zoo tried" same caveat. (2) CLAUDE.md's "27→56→82→88" ladder is the 2026-08-27 9-bot re-run; frozen 10-bot sweep = 27/57/82/89 at the same points (rounding-level, but cite the frozen values). (3) provenance key `input_csv_sha256` is a cell fingerprint, not a file hash.

**Conventions (from EGT_FINDINGS §2, all enforced in the material):** α=0 degenerate; SS claims need (M,β) qualifier or 6/9; share ≠ cooperation; per-region reporting; vertex counts = geometry; lrsnash cross-check absent 94/94 → Limitations sentence. Related: [[jmlr-paper-decisions]], [[egt-analysis-toolchain]].
