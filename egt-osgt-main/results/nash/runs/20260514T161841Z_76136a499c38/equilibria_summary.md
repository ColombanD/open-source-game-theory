# Nash equilibria — summary

N = 8 bot types: CooperateBot, CupodBot, DBot, DefectBot, DupocBot, OBot, TitForTatBot, EBot

Total extreme NE: **16**

| idx | class | pair | component | support_row | support_col | u | v | Pr[(C,C)] | finders |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | symmetric | — | 0 | CooperateBot,DefectBot,DupocBot,OBot,EBot | CooperateBot,DefectBot,DupocBot,OBot,EBot | 0.8571 (6/7) | 0.8571 (6/7) | 0.2925 (43/147) | lrsnash,pygambit |
| 1 | symmetric | — | 1 | CooperateBot,DupocBot,TitForTatBot | CooperateBot,DupocBot,TitForTatBot | 2 (2/1) | 2 (2/1) | 1 (1/1) | lrsnash,pygambit |
| 2 | asymmetric | 0 | 1 | CooperateBot,DupocBot,TitForTatBot | DupocBot | 2 (2/1) | 2 (2/1) | 1 (1/1) | lrsnash,pygambit |
| 3 | asymmetric | 2 | 1 | CooperateBot,DupocBot,TitForTatBot | DupocBot,TitForTatBot | 2 (2/1) | 2 (2/1) | 1 (1/1) | lrsnash,pygambit |
| 4 | symmetric | — | 2 | CooperateBot,OBot,EBot | CooperateBot,OBot,EBot | 1.5 (3/2) | 1.5 (3/2) | 0.6111 (11/18) | lrsnash,pygambit |
| 5 | symmetric | — | 3 | DefectBot | DefectBot | 0 (0/1) | 0 (0/1) | 0 (0/1) | lrsnash,pygambit |
| 6 | asymmetric | 1 | 3 | DefectBot | DefectBot,OBot | 0 (0/1) | 0 (0/1) | 0 (0/1) | lrsnash,pygambit |
| 7 | asymmetric | 0 | 1 | DupocBot | CooperateBot,DupocBot,TitForTatBot | 2 (2/1) | 2 (2/1) | 1 (1/1) | lrsnash,pygambit |
| 8 | symmetric | — | 1 | DupocBot | DupocBot | 2 (2/1) | 2 (2/1) | 1 (1/1) | lrsnash,pygambit |
| 9 | asymmetric | 3 | 1 | DupocBot | DupocBot,TitForTatBot | 2 (2/1) | 2 (2/1) | 1 (1/1) | lrsnash,pygambit |
| 10 | symmetric | — | 4 | CooperateBot,DupocBot,OBot,EBot | CooperateBot,DupocBot,OBot,EBot | 1.333 (4/3) | 1.333 (4/3) | 0.5185 (14/27) | lrsnash,pygambit |
| 11 | asymmetric | 1 | 3 | DefectBot,OBot | DefectBot | 0 (0/1) | 0 (0/1) | 0 (0/1) | lrsnash,pygambit |
| 12 | symmetric | — | 3 | DefectBot,OBot | DefectBot,OBot | 0 (0/1) | 0 (0/1) | 0 (0/1) | lrsnash,pygambit |
| 13 | asymmetric | 2 | 1 | DupocBot,TitForTatBot | CooperateBot,DupocBot,TitForTatBot | 2 (2/1) | 2 (2/1) | 1 (1/1) | lrsnash,pygambit |
| 14 | asymmetric | 3 | 1 | DupocBot,TitForTatBot | DupocBot | 2 (2/1) | 2 (2/1) | 1 (1/1) | lrsnash,pygambit |
| 15 | symmetric | — | 1 | DupocBot,TitForTatBot | DupocBot,TitForTatBot | 2 (2/1) | 2 (2/1) | 1 (1/1) | lrsnash,pygambit |
