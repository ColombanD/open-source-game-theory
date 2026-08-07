# Pure-strategy ESS verdict on the OSGT payoff matrix

PD payoffs: `b=3.0`, `c=1.0` → `(T=3.0, R=2.0, P=0.0, S=-1.0)`. See `assumptions.json` for the full convention.

Bot order: CooperateBot, CupodBot, DBot, DefectBot, DupocBot, OBot, TitForTatBot, EBot.

## Verdict

**No pure ESS exists.** Every type is invaded by at least one other type under the Maynard-Smith two-condition definition. See `ess_summary.csv` for per-type detail and the per-non-ESS narrative below.

| bot | is_ESS | failing_invaders | notes |
|---|---|---|---|
| CooperateBot | False | DBot, DefectBot, DupocBot, EBot, TitForTatBot | — |
| CupodBot | False | CooperateBot, DBot, DefectBot, DupocBot, EBot, OBot, TitForTatBot | depends on red cell |
| DBot | False | CupodBot, DefectBot, DupocBot, EBot, OBot, TitForTatBot | — |
| DefectBot | False | CupodBot, DupocBot, EBot, OBot, TitForTatBot | — |
| DupocBot | False | CooperateBot, EBot, TitForTatBot | depends on red cell |
| OBot | False | CooperateBot, CupodBot, DefectBot, DupocBot | — |
| TitForTatBot | False | CooperateBot, DupocBot, OBot | — |
| EBot | False | DupocBot, OBot, TitForTatBot | — |

## Why each non-ESS fails

### CooperateBot
- invaded by **DBot** — clause (a): A[CooperateBot,CooperateBot]=2 < A[DBot,CooperateBot]=3 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=CooperateBot, j=DBot).
- invaded by **DefectBot** — clause (a): A[CooperateBot,CooperateBot]=2 < A[DefectBot,CooperateBot]=3 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=CooperateBot, j=DefectBot).
- invaded by **DupocBot** — clause (a): A[CooperateBot,CooperateBot]=2 == A[DupocBot,CooperateBot]=2 (tie); clause (b): A[CooperateBot,DupocBot]=2 ≤ A[DupocBot,DupocBot]=2. See `ess_pairwise.csv` (i=CooperateBot, j=DupocBot).
- invaded by **EBot** — clause (a): A[CooperateBot,CooperateBot]=2 < A[EBot,CooperateBot]=3 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=CooperateBot, j=EBot).
- invaded by **TitForTatBot** — clause (a): A[CooperateBot,CooperateBot]=2 == A[TitForTatBot,CooperateBot]=2 (tie); clause (b): A[CooperateBot,TitForTatBot]=2 ≤ A[TitForTatBot,TitForTatBot]=2. See `ess_pairwise.csv` (i=CooperateBot, j=TitForTatBot).

### CupodBot
- invaded by **CooperateBot** — clause (a): A[CupodBot,CupodBot]=0 < A[CooperateBot,CupodBot]=2 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=CupodBot, j=CooperateBot).
- invaded by **DBot** — clause (a): A[CupodBot,CupodBot]=0 < A[DBot,CupodBot]=2 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=CupodBot, j=DBot).
- invaded by **DefectBot** — clause (a): A[CupodBot,CupodBot]=0 == A[DefectBot,CupodBot]=0 (tie); clause (b): A[CupodBot,DefectBot]=0 ≤ A[DefectBot,DefectBot]=0. See `ess_pairwise.csv` (i=CupodBot, j=DefectBot).
- invaded by **DupocBot** — clause (a): A[CupodBot,CupodBot]=0 < A[DupocBot,CupodBot]=3 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=CupodBot, j=DupocBot).
- invaded by **EBot** — clause (a): A[CupodBot,CupodBot]=0 < A[EBot,CupodBot]=2 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=CupodBot, j=EBot).
- invaded by **OBot** — clause (a): A[CupodBot,CupodBot]=0 == A[OBot,CupodBot]=0 (tie); clause (b): A[CupodBot,OBot]=0 ≤ A[OBot,OBot]=0. See `ess_pairwise.csv` (i=CupodBot, j=OBot).
- invaded by **TitForTatBot** — clause (a): A[CupodBot,CupodBot]=0 < A[TitForTatBot,CupodBot]=2 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=CupodBot, j=TitForTatBot).

### DBot
- invaded by **CupodBot** — clause (a): A[DBot,DBot]=0 < A[CupodBot,DBot]=2 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=DBot, j=CupodBot).
- invaded by **DefectBot** — clause (a): A[DBot,DBot]=0 < A[DefectBot,DBot]=3 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=DBot, j=DefectBot).
- invaded by **DupocBot** — clause (a): A[DBot,DBot]=0 < A[DupocBot,DBot]=2 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=DBot, j=DupocBot).
- invaded by **EBot** — clause (a): A[DBot,DBot]=0 < A[EBot,DBot]=3 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=DBot, j=EBot).
- invaded by **OBot** — clause (a): A[DBot,DBot]=0 < A[OBot,DBot]=3 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=DBot, j=OBot).
- invaded by **TitForTatBot** — clause (a): A[DBot,DBot]=0 < A[TitForTatBot,DBot]=3 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=DBot, j=TitForTatBot).

### DefectBot
- invaded by **CupodBot** — clause (a): A[DefectBot,DefectBot]=0 == A[CupodBot,DefectBot]=0 (tie); clause (b): A[DefectBot,CupodBot]=0 ≤ A[CupodBot,CupodBot]=0. See `ess_pairwise.csv` (i=DefectBot, j=CupodBot).
- invaded by **DupocBot** — clause (a): A[DefectBot,DefectBot]=0 == A[DupocBot,DefectBot]=0 (tie); clause (b): A[DefectBot,DupocBot]=0 ≤ A[DupocBot,DupocBot]=2. See `ess_pairwise.csv` (i=DefectBot, j=DupocBot).
- invaded by **EBot** — clause (a): A[DefectBot,DefectBot]=0 == A[EBot,DefectBot]=0 (tie); clause (b): A[DefectBot,EBot]=0 ≤ A[EBot,EBot]=2. See `ess_pairwise.csv` (i=DefectBot, j=EBot).
- invaded by **OBot** — clause (a): A[DefectBot,DefectBot]=0 == A[OBot,DefectBot]=0 (tie); clause (b): A[DefectBot,OBot]=0 ≤ A[OBot,OBot]=0. See `ess_pairwise.csv` (i=DefectBot, j=OBot).
- invaded by **TitForTatBot** — clause (a): A[DefectBot,DefectBot]=0 == A[TitForTatBot,DefectBot]=0 (tie); clause (b): A[DefectBot,TitForTatBot]=0 ≤ A[TitForTatBot,TitForTatBot]=2. See `ess_pairwise.csv` (i=DefectBot, j=TitForTatBot).

### DupocBot
- invaded by **CooperateBot** — clause (a): A[DupocBot,DupocBot]=2 == A[CooperateBot,DupocBot]=2 (tie); clause (b): A[DupocBot,CooperateBot]=2 ≤ A[CooperateBot,CooperateBot]=2. See `ess_pairwise.csv` (i=DupocBot, j=CooperateBot).
- invaded by **EBot** — clause (a): A[DupocBot,DupocBot]=2 == A[EBot,DupocBot]=2 (tie); clause (b): A[DupocBot,EBot]=2 ≤ A[EBot,EBot]=2. See `ess_pairwise.csv` (i=DupocBot, j=EBot).
- invaded by **TitForTatBot** — clause (a): A[DupocBot,DupocBot]=2 == A[TitForTatBot,DupocBot]=2 (tie); clause (b): A[DupocBot,TitForTatBot]=2 ≤ A[TitForTatBot,TitForTatBot]=2. See `ess_pairwise.csv` (i=DupocBot, j=TitForTatBot).

### OBot
- invaded by **CooperateBot** — clause (a): A[OBot,OBot]=0 < A[CooperateBot,OBot]=2 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=OBot, j=CooperateBot).
- invaded by **CupodBot** — clause (a): A[OBot,OBot]=0 == A[CupodBot,OBot]=0 (tie); clause (b): A[OBot,CupodBot]=0 ≤ A[CupodBot,CupodBot]=0. See `ess_pairwise.csv` (i=OBot, j=CupodBot).
- invaded by **DefectBot** — clause (a): A[OBot,OBot]=0 == A[DefectBot,OBot]=0 (tie); clause (b): A[OBot,DefectBot]=0 ≤ A[DefectBot,DefectBot]=0. See `ess_pairwise.csv` (i=OBot, j=DefectBot).
- invaded by **DupocBot** — clause (a): A[OBot,OBot]=0 == A[DupocBot,OBot]=0 (tie); clause (b): A[OBot,DupocBot]=0 ≤ A[DupocBot,DupocBot]=2. See `ess_pairwise.csv` (i=OBot, j=DupocBot).

### TitForTatBot
- invaded by **CooperateBot** — clause (a): A[TitForTatBot,TitForTatBot]=2 == A[CooperateBot,TitForTatBot]=2 (tie); clause (b): A[TitForTatBot,CooperateBot]=2 ≤ A[CooperateBot,CooperateBot]=2. See `ess_pairwise.csv` (i=TitForTatBot, j=CooperateBot).
- invaded by **DupocBot** — clause (a): A[TitForTatBot,TitForTatBot]=2 == A[DupocBot,TitForTatBot]=2 (tie); clause (b): A[TitForTatBot,DupocBot]=2 ≤ A[DupocBot,DupocBot]=2. See `ess_pairwise.csv` (i=TitForTatBot, j=DupocBot).
- invaded by **OBot** — clause (a): A[TitForTatBot,TitForTatBot]=2 < A[OBot,TitForTatBot]=3 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=TitForTatBot, j=OBot).

### EBot
- invaded by **DupocBot** — clause (a): A[EBot,EBot]=2 == A[DupocBot,EBot]=2 (tie); clause (b): A[EBot,DupocBot]=2 ≤ A[DupocBot,DupocBot]=2. See `ess_pairwise.csv` (i=EBot, j=DupocBot).
- invaded by **OBot** — clause (a): A[EBot,EBot]=2 < A[OBot,EBot]=3 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=EBot, j=OBot).
- invaded by **TitForTatBot** — clause (a): A[EBot,EBot]=2 < A[TitForTatBot,EBot]=3 (no tie, clause (b) inapplicable). See `ess_pairwise.csv` (i=EBot, j=TitForTatBot).

## Flagged input

The following pairwise rows reference the red cell `(CupodBot, DupocBot)`, which is unresolved in Critch et al. 2022 and was filled from `config.undefined_outcomes.cupod_vs_dupoc`. Verdicts that depend on these rows should be regarded as conditional on the chosen resolution; re-running with the opposite action pair is planned but not in scope here.

- i=CupodBot, j=DupocBot: A_ii=0, A_ji=3, A_ij=-1, A_jj=2, i_survives_j=False.
- i=DupocBot, j=CupodBot: A_ii=2, A_ji=-1, A_ij=3, A_jj=0, i_survives_j=True.

## Methodology

Pure-strategy ESS in the Maynard-Smith two-condition form (Sandholm 2010 Ch. 8; Weibull 1995 Def. 2.1):

> Type *i* is an ESS iff, for every *j* ≠ *i*, **A[i,i] > A[j,i]** (clause **a**), or **A[i,i] = A[j,i]** *and* **A[i,j] > A[j,j]** (clause **b**).

The matrix A is not symmetrised; the asymmetric form of both clauses is used throughout. Equality tolerance: `atol = 1e-12`.
