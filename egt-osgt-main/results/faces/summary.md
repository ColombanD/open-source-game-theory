# Face equilibria — summary

- Numeric matrix: `results/ess/payoff_matrix_numeric.csv`
- Number of types (N): **8**
- Supports enumerated (|S| >= 2): **247**

All claims below trace to specific rows in
`face_equilibria.parquet` (column `support_id`).

## Counts by overall_class

| overall_class | count |
| --- | --- |
| asymp_stable | 0 |
| asymp_stable_invadable | 3 |
| saddle | 3 |
| unstable | 0 |
| non_interior | 175 |
| singular | 66 |
| non_hyperbolic | 0 |

## Asymptotically stable interior equilibria

Rows with `overall_class` ∈ {`asymp_stable`, `asymp_stable_invadable`}.

| support_id | support_tuple | support_size | overall_class | max_re_eigval | max_external_fitness |
| --- | --- | --- | --- | --- | --- |
| 7 | (CupodBot, DBot) | 2 | asymp_stable_invadable | -1 | 1.5 |
| 36 | (CooperateBot, DBot, OBot) | 3 | asymp_stable_invadable | -0.1875 | 0.625 |
| 47 | (CooperateBot, OBot, EBot) | 3 | asymp_stable_invadable | -0.0833333 | 0 |

## Singular faces

Rows with `A_SS` singular — equilibrium columns are NaN.

| support_id | support_tuple | support_size | overall_class | max_re_eigval | max_external_fitness |
| --- | --- | --- | --- | --- | --- |
| 1 | (CooperateBot, DBot) | 2 | singular | NaN | -inf |
| 2 | (CooperateBot, DefectBot) | 2 | singular | NaN | -inf |
| 3 | (CooperateBot, DupocBot) | 2 | singular | NaN | -inf |
| 5 | (CooperateBot, TitForTatBot) | 2 | singular | NaN | -inf |
| 8 | (CupodBot, DefectBot) | 2 | singular | NaN | -inf |
| 9 | (CupodBot, DupocBot) | 2 | singular | NaN | -inf |
| 10 | (CupodBot, OBot) | 2 | singular | NaN | -inf |
| 16 | (DBot, TitForTatBot) | 2 | singular | NaN | -inf |
| 17 | (DBot, EBot) | 2 | singular | NaN | -inf |
| 19 | (DefectBot, OBot) | 2 | singular | NaN | -inf |
| 23 | (DupocBot, TitForTatBot) | 2 | singular | NaN | -inf |
| 24 | (DupocBot, EBot) | 2 | singular | NaN | -inf |
| 25 | (OBot, TitForTatBot) | 2 | singular | NaN | -inf |
| 26 | (OBot, EBot) | 2 | singular | NaN | -inf |
| 31 | (CooperateBot, CupodBot, OBot) | 3 | singular | NaN | -inf |
| 32 | (CooperateBot, CupodBot, TitForTatBot) | 3 | singular | NaN | -inf |
| 42 | (CooperateBot, DefectBot, EBot) | 3 | singular | NaN | -inf |
| 44 | (CooperateBot, DupocBot, TitForTatBot) | 3 | singular | NaN | -inf |
| 55 | (CupodBot, DefectBot, OBot) | 3 | singular | NaN | -inf |
| 65 | (DBot, DefectBot, OBot) | 3 | singular | NaN | -inf |
| 74 | (DefectBot, DupocBot, OBot) | 3 | singular | NaN | -inf |
| 75 | (DefectBot, DupocBot, TitForTatBot) | 3 | singular | NaN | -inf |
| 76 | (DefectBot, DupocBot, EBot) | 3 | singular | NaN | -inf |
| 84 | (CooperateBot, CupodBot, DBot, DefectBot) | 4 | singular | NaN | -inf |
| 85 | (CooperateBot, CupodBot, DBot, DupocBot) | 4 | singular | NaN | -inf |
| 89 | (CooperateBot, CupodBot, DefectBot, DupocBot) | 4 | singular | NaN | -inf |
| 90 | (CooperateBot, CupodBot, DefectBot, OBot) | 4 | singular | NaN | -inf |
| 94 | (CooperateBot, CupodBot, DupocBot, TitForTatBot) | 4 | singular | NaN | -inf |
| 101 | (CooperateBot, DBot, DefectBot, TitForTatBot) | 4 | singular | NaN | -inf |
| 104 | (CooperateBot, DBot, DupocBot, TitForTatBot) | 4 | singular | NaN | -inf |
| 105 | (CooperateBot, DBot, DupocBot, EBot) | 4 | singular | NaN | -inf |
| 106 | (CooperateBot, DBot, OBot, TitForTatBot) | 4 | singular | NaN | -inf |
| 108 | (CooperateBot, DBot, TitForTatBot, EBot) | 4 | singular | NaN | -inf |
| 110 | (CooperateBot, DefectBot, DupocBot, TitForTatBot) | 4 | singular | NaN | -inf |
| 112 | (CooperateBot, DefectBot, OBot, TitForTatBot) | 4 | singular | NaN | -inf |
| 115 | (CooperateBot, DupocBot, OBot, TitForTatBot) | 4 | singular | NaN | -inf |
| 117 | (CooperateBot, DupocBot, TitForTatBot, EBot) | 4 | singular | NaN | -inf |
| 120 | (CupodBot, DBot, DefectBot, OBot) | 4 | singular | NaN | -inf |
| 124 | (CupodBot, DBot, DupocBot, TitForTatBot) | 4 | singular | NaN | -inf |
| 125 | (CupodBot, DBot, DupocBot, EBot) | 4 | singular | NaN | -inf |
| 126 | (CupodBot, DBot, OBot, TitForTatBot) | 4 | singular | NaN | -inf |
| 127 | (CupodBot, DBot, OBot, EBot) | 4 | singular | NaN | -inf |
| 129 | (CupodBot, DefectBot, DupocBot, OBot) | 4 | singular | NaN | -inf |
| 132 | (CupodBot, DefectBot, OBot, TitForTatBot) | 4 | singular | NaN | -inf |
| 133 | (CupodBot, DefectBot, OBot, EBot) | 4 | singular | NaN | -inf |
| 135 | (CupodBot, DupocBot, OBot, TitForTatBot) | 4 | singular | NaN | -inf |
| 136 | (CupodBot, DupocBot, OBot, EBot) | 4 | singular | NaN | -inf |
| 139 | (DBot, DefectBot, DupocBot, OBot) | 4 | singular | NaN | -inf |
| 147 | (DBot, DupocBot, TitForTatBot, EBot) | 4 | singular | NaN | -inf |
| 148 | (DBot, OBot, TitForTatBot, EBot) | 4 | singular | NaN | -inf |
| 162 | (CooperateBot, CupodBot, DBot, OBot, EBot) | 5 | singular | NaN | -inf |
| 163 | (CooperateBot, CupodBot, DBot, TitForTatBot, EBot) | 5 | singular | NaN | -inf |
| 166 | (CooperateBot, CupodBot, DefectBot, DupocBot, EBot) | 5 | singular | NaN | -inf |
| 176 | (CooperateBot, DBot, DefectBot, DupocBot, EBot) | 5 | singular | NaN | -inf |
| 182 | (CooperateBot, DBot, DupocBot, TitForTatBot, EBot) | 5 | singular | NaN | -inf |
| 187 | (CooperateBot, DefectBot, OBot, TitForTatBot, EBot) | 5 | singular | NaN | -inf |
| 189 | (CupodBot, DBot, DefectBot, DupocBot, OBot) | 5 | singular | NaN | -inf |
| 202 | (CupodBot, DefectBot, OBot, TitForTatBot, EBot) | 5 | singular | NaN | -inf |
| 211 | (CooperateBot, CupodBot, DBot, DefectBot, DupocBot, TitForTatBot) | 6 | singular | NaN | -inf |
| 216 | (CooperateBot, CupodBot, DBot, DupocBot, OBot, TitForTatBot) | 6 | singular | NaN | -inf |
| 218 | (CooperateBot, CupodBot, DBot, DupocBot, TitForTatBot, EBot) | 6 | singular | NaN | -inf |
| 220 | (CooperateBot, CupodBot, DefectBot, DupocBot, OBot, TitForTatBot) | 6 | singular | NaN | -inf |
| 227 | (CooperateBot, DBot, DefectBot, DupocBot, TitForTatBot, EBot) | 6 | singular | NaN | -inf |
| 229 | (CooperateBot, DBot, DupocBot, OBot, TitForTatBot, EBot) | 6 | singular | NaN | -inf |
| 235 | (CupodBot, DBot, DupocBot, OBot, TitForTatBot, EBot) | 6 | singular | NaN | -inf |
| 243 | (CooperateBot, CupodBot, DefectBot, DupocBot, OBot, TitForTatBot, EBot) | 7 | singular | NaN | -inf |

## Non-hyperbolic faces

Rows with at least one tangent eigenvalue on the imaginary axis (within numerical tolerance).

_(none)_
