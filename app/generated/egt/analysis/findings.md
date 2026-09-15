# Findings — claim-driven analysis over the frozen sweeps


## 1. Baseline — body zoo, t = 1 (the anchor matrix = the base matrix)

pure ESS: 0 · extreme NE: 21 in 3 components · invasion SCCs: 3 · stable faces: 6/1013 supports

dominant replicator support: Coop+Dup+TFT (basin 95%)

Full (M, β) Moran table (DupocBot share of the stationary distribution):

```
beta       0.01 0.10 1.00
population               
10          11%  27%  60%
50          19%  57%  82%
100         29%  67%  89%
```

Stochastically stable set per (M, β):

```
beta           0.01     0.10 1.00
population                       
10                —      Dup  Dup
50              Dup  Dup+TFT  Dup
100         Dup+TFT      Dup  Dup
```


## 2. Critical transparency — how far down t the t=1 winners survive

Per α: the M=100/β=1 SS set along t (1.0 → 0.0); `t*` = first t where it departs from the t=1 set.

### body — behavioral

```
α=0.3   [t*=0.2→Def+Dup]  1:Dup  0.8:Dup  0.6:Dup  0.4:Dup  0.2:Def+Dup  0:Def+Dup+OB
α=0.45  [t*=0→Def+Dup+OB]  1:Dup  0.8:Dup  0.6:Dup  0.4:Dup  0.2:Dup  0:Def+Dup+OB
α=0.62  [t*=0.2→Dup+OB]  1:Dup  0.8:Dup  0.6:Dup  0.4:Dup  0.2:Dup+OB  0:Cup+Def+Dup+EB+OB
α=0.8   [t*=0.4→Dup+OB]  1:Dup  0.8:Dup  0.6:Dup  0.4:Dup+OB  0.2:Def+Dup+OB  0:—
α=1     [t*=0.8→—]  1:Dup  0.8:—  0.6:—  0.4:—  0.2:—  0:—
```

### body — syntactic

```
α=0.3   [t*=0→Def]  1:Dup  0.8:Dup  0.6:Dup  0.4:Dup  0.2:Dup  0:Def
α=0.45  [t*=0→Def+Dup+OB]  1:Dup  0.8:Dup  0.6:Dup  0.4:Dup  0.2:Dup  0:Def+Dup+OB
α=0.62  [t*=0.2→Dup+OB]  1:Dup  0.8:Dup  0.6:Dup  0.4:Dup  0.2:Dup+OB  0:Cup+Def+Dup+EB+OB
α=0.8   [t*=0.6→Def]  1:Dup  0.8:Dup  0.6:Def  0.4:Dup+OB  0.2:EB  0:—
α=1     [t*=0.8→—]  1:Dup  0.8:—  0.6:—  0.4:—  0.2:—  0:—
```

### body+twins — behavioral

```
α=0.3   [t*=0→Def+OB+Pru]  1:CIM+Dup  0.8:CIM+Dup  0.6:CIM+Dup  0.4:CIM+Dup  0.2:CIM+Dup  0:Def+OB+Pru
α=0.45  [t*=0→CIM+Def+Dup+OB+Pru]  1:CIM+Dup  0.8:CIM+Dup  0.6:CIM+Dup  0.4:CIM+Dup  0.2:CIM+Dup  0:CIM+Def+Dup+OB+Pru
α=0.62  [t*=0→CIM+Def+Dup+OB+Pru]  1:CIM+Dup  0.8:CIM+Dup  0.6:CIM+Dup  0.4:CIM+Dup  0.2:CIM+Dup  0:CIM+Def+Dup+OB+Pru
α=0.8   [t*=0.6→CIM+Dup+TFT]  1:CIM+Dup  0.8:CIM+Dup  0.6:CIM+Dup+TFT  0.4:CIM+Dup+TFT  0.2:CIM+Dup  0:—
α=1     [t*=0.8→—]  1:CIM+Dup  0.8:—  0.6:—  0.4:—  0.2:—  0:—
```

### body+twins — syntactic

```
α=0.3   [t*=0→Def+OB+Pru]  1:CIM+Dup  0.8:CIM+Dup  0.6:CIM+Dup  0.4:CIM+Dup  0.2:CIM+Dup  0:Def+OB+Pru
α=0.45  [t*=0→CIM+Def+Dup+OB+Pru]  1:CIM+Dup  0.8:CIM+Dup  0.6:CIM+Dup  0.4:CIM+Dup  0.2:CIM+Dup  0:CIM+Def+Dup+OB+Pru
α=0.62  [t*=0.2→OB+Pru]  1:CIM+Dup  0.8:CIM+Dup  0.6:CIM+Dup  0.4:CIM+Dup  0.2:OB+Pru  0:CIM+Def+Dup+OB+Pru
α=0.8   [t*=0.6→Def+Pru]  1:CIM+Dup  0.8:CIM+Dup  0.6:Def+Pru  0.4:OB+Pru  0.2:CIM+Dup+OB+Pru  0:—
α=1     [t*=0.8→—]  1:CIM+Dup  0.8:—  0.6:—  0.4:—  0.2:—  0:—
```

### body+twins+natives — behavioral

```
α=0.3   [t*=0.8→Def+Pru+TFT]  1:CIM+Dup+Max+Min  0.8:Def+Pru+TFT  0.6:Def+Pru+TFT  0.4:Def+Pru+TFT  0.2:Def+Max+Pru  0:Def+Max+OB+Pru
α=0.45  [t*=0.8→Def+Pru+TFT]  1:CIM+Dup+Max+Min  0.8:Def+Pru+TFT  0.6:Def+Pru+TFT  0.4:Def+Pru+TFT  0.2:Max  0:CIM+Def+Dup+Max+OB+Pru
α=0.62  [t*=0.8→Max+TFT]  1:CIM+Dup+Max+Min  0.8:Max+TFT  0.6:Max+TFT  0.4:Max  0.2:Max  0:CIM+Def+Dup+Max+OB+Pru
α=0.8   [t*=0.8→Max+TFT]  1:CIM+Dup+Max+Min  0.8:Max+TFT  0.6:TFT  0.4:Max  0.2:CIM+Dup+Max  0:—
α=1     [t*=0.8→Def+OB+Pru]  1:CIM+Dup+Max+Min  0.8:Def+OB+Pru  0.6:—  0.4:—  0.2:—  0:—
```

### body+twins+natives — epsilon

```
α=0.3   [t*=0.4→CIM+Dup+Max]  1:CIM+Dup+Max+Min  0.8:CIM+Dup+Max+Min  0.6:CIM+Dup+Max+Min  0.4:CIM+Dup+Max  0.2:CIM+Dup+Max  0:Def+Max+OB+Pru
α=0.45  [t*=0.2→Max]  1:CIM+Dup+Max+Min  0.8:CIM+Dup+Max+Min  0.6:CIM+Dup+Max+Min  0.4:CIM+Dup+Max+Min  0.2:Max  0:CIM+Def+Dup+Max+OB+Pru
α=0.62  [t*=0.2→Max]  1:CIM+Dup+Max+Min  0.8:CIM+Dup+Max+Min  0.6:CIM+Dup+Max+Min  0.4:CIM+Dup+Max+Min  0.2:Max  0:CIM+Def+Dup+Max+OB+Pru
α=0.8   [t*=0.6→Max]  1:CIM+Dup+Max+Min  0.8:CIM+Dup+Max+Min  0.6:Max  0.4:CIM+Dup+Max  0.2:CIM+Dup+Max  0:—
α=1     [t*=0.8→—]  1:CIM+Dup+Max+Min  0.8:—  0.6:—  0.4:—  0.2:—  0:—
```


## 3. Selection robustness — # of the 9 (M, β) combos whose SS set equals the M=100/β=1 headline

9 = fully robust; low values mean the headline is a strong-selection statement (weak selection usually clears no stochastic-stability cut at all, which depresses these counts honestly).

### body — behavioral

```
t      1.0  0.8  0.6  0.4  0.2  0.0
alpha                              
0.30   6.0  6.0  6.0  2.0  7.0  5.0
0.45   6.0  6.0  6.0  6.0  7.0  7.0
0.62   6.0  6.0  6.0  8.0  8.0  6.0
0.80   6.0  6.0  7.0  7.0  5.0  9.0
1.00   6.0  9.0  9.0  9.0  9.0  9.0
```

### body — syntactic

```
t      1.0  0.8  0.6  0.4  0.2  0.0
alpha                              
0.30   6.0  6.0  6.0  8.0  7.0  2.0
0.45   6.0  6.0  6.0  6.0  7.0  7.0
0.62   6.0  6.0  6.0  7.0  8.0  6.0
0.80   6.0  6.0  1.0  5.0  7.0  9.0
1.00   6.0  9.0  9.0  9.0  9.0  9.0
```

### body+twins — behavioral

```
t      1.0  0.8  0.6  0.4  0.2  0.0
alpha                              
0.30   8.0  8.0  8.0  8.0  5.0  7.0
0.45   8.0  8.0  8.0  8.0  8.0  7.0
0.62   8.0  8.0  8.0  8.0  8.0  7.0
0.80   8.0  8.0  7.0  7.0  8.0  9.0
1.00   8.0  9.0  9.0  9.0  9.0  9.0
```

### body+twins — syntactic

```
t      1.0  0.8  0.6  0.4  0.2  0.0
alpha                              
0.30   8.0  8.0  8.0  8.0  8.0  7.0
0.45   8.0  8.0  8.0  8.0  8.0  7.0
0.62   8.0  8.0  8.0  8.0  5.0  7.0
0.80   8.0  8.0  3.0  4.0  7.0  9.0
1.00   8.0  9.0  9.0  9.0  9.0  9.0
```

### body+twins+natives — behavioral

```
t      1.0  0.8  0.6  0.4  0.2  0.0
alpha                              
0.30   8.0  1.0  1.0  1.0  4.0  7.0
0.45   8.0  1.0  1.0  1.0  5.0  7.0
0.62   8.0  2.0  2.0  5.0  3.0  7.0
0.80   8.0  2.0  2.0  5.0  5.0  9.0
1.00   8.0  5.0  9.0  9.0  9.0  9.0
```

### body+twins+natives — epsilon

```
t      1.0  0.8  0.6  0.4  0.2  0.0
alpha                              
0.30   8.0  8.0  8.0  8.0  7.0  7.0
0.45   8.0  8.0  8.0  8.0  5.0  7.0
0.62   8.0  8.0  8.0  8.0  6.0  7.0
0.80   8.0  8.0  6.0  2.0  2.0  9.0
1.00   8.0  9.0  9.0  9.0  9.0  9.0
```


## 4. Aggregator ablation — body+twins+natives on epsilon, stationary shares at M=100, β=1

Columns: the three aggregators over Dupoc's test (sum = the Dup+CIM lifts, payoff-twins at t=1) and the Löbian class total.

```
 alpha   t sum(Dup+CIM) max(Max) min(Min) class total                     SS
  0.30 1.0          47%      24%      24%         95%        CIM+Dup+Max+Min
  0.30 0.8          47%      24%      24%         95%        CIM+Dup+Max+Min
  0.30 0.6          47%      24%      24%         95%        CIM+Dup+Max+Min
  0.30 0.4          60%      30%       0%         91%            CIM+Dup+Max
  0.30 0.2          60%      30%       0%         91%            CIM+Dup+Max
  0.30 0.0           0%      25%       0%         25%         Def+Max+OB+Pru
  0.45 1.0          47%      24%      24%         95%        CIM+Dup+Max+Min
  0.45 0.8          47%      24%      24%         95%        CIM+Dup+Max+Min
  0.45 0.6          47%      24%      24%         95%        CIM+Dup+Max+Min
  0.45 0.4          47%      24%      24%         95%        CIM+Dup+Max+Min
  0.45 0.2           3%      89%       0%         92%                    Max
  0.45 0.0          33%      17%       0%         50% CIM+Def+Dup+Max+OB+Pru
  0.62 1.0          47%      24%      24%         95%        CIM+Dup+Max+Min
  0.62 0.8          47%      24%      24%         95%        CIM+Dup+Max+Min
  0.62 0.6          47%      24%      24%         95%        CIM+Dup+Max+Min
  0.62 0.4          47%      24%      24%         95%        CIM+Dup+Max+Min
  0.62 0.2           2%      89%       1%         92%                    Max
  0.62 0.0          33%      17%       0%         50% CIM+Def+Dup+Max+OB+Pru
  0.80 1.0          47%      24%      24%         95%        CIM+Dup+Max+Min
  0.80 0.8          47%      24%      24%         95%        CIM+Dup+Max+Min
  0.80 0.6           2%      90%       1%         94%                    Max
  0.80 0.4          57%      28%       1%         86%            CIM+Dup+Max
  0.80 0.2          57%      28%       1%         86%            CIM+Dup+Max
  0.80 0.0          18%       9%       0%         27%                      —
  1.00 1.0          47%      24%      24%         95%        CIM+Dup+Max+Min
  1.00 0.8          15%       8%       8%         31%                      —
  1.00 0.6          15%       8%       8%         31%                      —
  1.00 0.4          15%       8%       8%         31%                      —
  1.00 0.2          15%       8%       8%         31%                      —
  1.00 0.0          15%       8%       8%         31%                      —
```


## 5. Zoo sensitivity — body vs body+twins (behavioral)

SS set changes at 24/30 grid points; 29/30 twins-zoo points have a dominant support mixing Dup and CIM (the Löbian niche splitting across the twin pair).

```
  t  alpha     moran_ss_body     moran_ss_twins
1.0   0.30               Dup            CIM+Dup
1.0   0.45               Dup            CIM+Dup
1.0   0.62               Dup            CIM+Dup
1.0   0.80               Dup            CIM+Dup
1.0   1.00               Dup            CIM+Dup
0.8   0.30               Dup            CIM+Dup
0.8   0.45               Dup            CIM+Dup
0.8   0.62               Dup            CIM+Dup
0.8   0.80               Dup            CIM+Dup
0.6   0.30               Dup            CIM+Dup
0.6   0.45               Dup            CIM+Dup
0.6   0.62               Dup            CIM+Dup
0.6   0.80               Dup        CIM+Dup+TFT
0.4   0.30               Dup            CIM+Dup
0.4   0.45               Dup            CIM+Dup
0.4   0.62               Dup            CIM+Dup
0.4   0.80            Dup+OB        CIM+Dup+TFT
0.2   0.30           Def+Dup            CIM+Dup
0.2   0.45               Dup            CIM+Dup
0.2   0.62            Dup+OB            CIM+Dup
0.2   0.80        Def+Dup+OB            CIM+Dup
0.0   0.30        Def+Dup+OB         Def+OB+Pru
0.0   0.45        Def+Dup+OB CIM+Def+Dup+OB+Pru
0.0   0.62 Cup+Def+Dup+EB+OB CIM+Def+Dup+OB+Pru
```


## 6. The Max band — body+twins+natives on BEHAVIORAL (twinning, not ablation)

Cells where MaxConfidence is UNIQUELY stochastically stable at M=100/β=1. Archived pre-freeze observation (10-member zoo): t ∈ [0.2, 0.6] at α ≥ 0.45.

```
  t  alpha
0.2   0.45
0.2   0.62
0.4   0.62
0.4   0.80
```

Full SS map for context:

```
t                  1.0          0.8          0.6          0.4          0.2                     0.0
alpha                                                                                             
0.30   CIM+Dup+Max+Min  Def+Pru+TFT  Def+Pru+TFT  Def+Pru+TFT  Def+Max+Pru          Def+Max+OB+Pru
0.45   CIM+Dup+Max+Min  Def+Pru+TFT  Def+Pru+TFT  Def+Pru+TFT          Max  CIM+Def+Dup+Max+OB+Pru
0.62   CIM+Dup+Max+Min      Max+TFT      Max+TFT          Max          Max  CIM+Def+Dup+Max+OB+Pru
0.80   CIM+Dup+Max+Min      Max+TFT          TFT          Max  CIM+Dup+Max                       —
1.00   CIM+Dup+Max+Min   Def+OB+Pru            —            —            —                       —
```
