# Cross-check: invasion graph vs ESS verdict

The strict invasion graph captures only clause (a) of Maynard-Smith ESS, so `in_degree(G_strict, v) == 0` is a NECESSARY (not sufficient) condition for v to be an ESS. Every pure ESS in `ess_summary.csv` should therefore appear with in-degree zero; the converse can fail via clause (b), in which case the responsible tied invader(s) are listed below.

## Agreement table

| vertex | candidate_ESS_by_clause_a | is_ESS_per_ess_summary | agrees | responsible_ties |
|---|---|---|---|---|
| CooperateBot | False | False | True | CupodBot→CooperateBot, DupocBot→CooperateBot, OBot→CooperateBot, TitForTatBot→CooperateBot |
| CupodBot | False | False | True | DefectBot→CupodBot, OBot→CupodBot |
| DBot | False | False | True | — |
| DefectBot | True | False | False | CupodBot→DefectBot, DupocBot→DefectBot, OBot→DefectBot, TitForTatBot→DefectBot, EBot→DefectBot |
| DupocBot | True | False | False | CooperateBot→DupocBot, DBot→DupocBot, TitForTatBot→DupocBot, EBot→DupocBot |
| OBot | False | False | True | CupodBot→OBot, DefectBot→OBot, DupocBot→OBot |
| TitForTatBot | False | False | True | CooperateBot→TitForTatBot, CupodBot→TitForTatBot, DupocBot→TitForTatBot |
| EBot | False | False | True | CupodBot→EBot, DupocBot→EBot |

## Disagreements

Every disagreement below has shape *clause-(a) candidate that ESS rejects*; the rejection is mediated by the listed clause-(b) tie(s).

- **DefectBot**: candidate by clause (a) but ESS rejects it via tie(s): CupodBot→DefectBot, DupocBot→DefectBot, OBot→DefectBot, TitForTatBot→DefectBot, EBot→DefectBot. See `ties.csv` rows with `j == DefectBot`.
- **DupocBot**: candidate by clause (a) but ESS rejects it via tie(s): CooperateBot→DupocBot, DBot→DupocBot, TitForTatBot→DupocBot, EBot→DupocBot. See `ties.csv` rows with `j == DupocBot`.

