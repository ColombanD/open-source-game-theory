# Phase maps — cells sharing a value form the phase regions

α=0 row: degenerate unconditional cooperation (`≥ α`).

## body — behavioral

### stochastically stable (M=100, β=1)

```
t      1.0  0.8  0.6     0.4         0.2                0.0
alpha                                                      
0.00     —    —    —       —           —                  —
0.30   Dup  Dup  Dup     Dup     Def+Dup         Def+Dup+OB
0.45   Dup  Dup  Dup     Dup         Dup         Def+Dup+OB
0.62   Dup  Dup  Dup     Dup      Dup+OB  Cup+Def+Dup+EB+OB
0.80   Dup  Dup  Dup  Dup+OB  Def+Dup+OB                  —
1.00   Dup    —    —       —           —                  —
```


### dominant replicator support

```
t                                         1.0                                     0.8                                     0.6                                     0.4                                     0.2                                     0.0
alpha                                                                                                                                                                                                                                                
0.00   Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT  Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT  Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT  Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT  Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT  Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT
0.30                             Coop+Dup+TFT                            Coop+Dup+TFT                            Coop+Dup+TFT                            Coop+Dup+TFT                       Coop+CupT+Dup+TFT             Coop+CupT+DB+DIM+Dup+EB+TFT
0.45                             Coop+Dup+TFT                            Coop+Dup+TFT                            Coop+Dup+TFT                            Coop+Dup+TFT                                 Dup+TFT                              Def+Dup+OB
0.62                             Coop+Dup+TFT                            Coop+Dup+TFT                            Coop+Dup+TFT                                 Dup+TFT                              Def+Dup+OB                       Cup+Def+Dup+EB+OB
0.80                             Coop+Dup+TFT                            Coop+Dup+TFT                                 Dup+TFT                      Cup+DIM+Def+Dup+OB                      Cup+DIM+Def+Dup+OB            Cup+DB+DIM+Def+Dup+EB+OB+TFT
1.00                             Coop+Dup+TFT       Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT       Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT       Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT       Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT       Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT
```

## body — syntactic

### stochastically stable (M=100, β=1)

```
t      1.0  0.8  0.6     0.4     0.2                0.0
alpha                                                  
0.00     —    —    —       —       —                  —
0.30   Dup  Dup  Dup     Dup     Dup                Def
0.45   Dup  Dup  Dup     Dup     Dup         Def+Dup+OB
0.62   Dup  Dup  Dup     Dup  Dup+OB  Cup+Def+Dup+EB+OB
0.80   Dup  Dup  Def  Dup+OB      EB                  —
1.00   Dup    —    —       —       —                  —
```


### dominant replicator support

```
t                                         1.0                                     0.8                                     0.6                                     0.4                                     0.2                                     0.0
alpha                                                                                                                                                                                                                                                
0.00   Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT  Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT  Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT  Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT  Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT  Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT
0.30                             Coop+Dup+TFT                            Coop+Dup+TFT                            Coop+Dup+TFT                            Coop+Dup+TFT                            Coop+Dup+TFT                                  Def+OB
0.45                             Coop+Dup+TFT                            Coop+Dup+TFT                            Coop+Dup+TFT                            Coop+Dup+TFT                            Coop+Dup+TFT                              Def+Dup+OB
0.62                             Coop+Dup+TFT                            Coop+Dup+TFT                            Coop+Dup+TFT                            Coop+Dup+TFT                              Def+Dup+OB                       Cup+Def+Dup+EB+OB
0.80                             Coop+Dup+TFT                            Coop+Dup+TFT                              Def+Dup+OB                              Def+Dup+OB                                      EB            Cup+DB+DIM+Def+Dup+EB+OB+TFT
1.00                             Coop+Dup+TFT       Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT       Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT       Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT       Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT       Cup+CupT+DB+DIM+Def+Dup+EB+OB+TFT
```

## body+twins — behavioral

### stochastically stable (M=100, β=1)

```
t          1.0      0.8          0.6          0.4      0.2                 0.0
alpha                                                                         
0.00         —        —            —            —        —                   —
0.30   CIM+Dup  CIM+Dup      CIM+Dup      CIM+Dup  CIM+Dup          Def+OB+Pru
0.45   CIM+Dup  CIM+Dup      CIM+Dup      CIM+Dup  CIM+Dup  CIM+Def+Dup+OB+Pru
0.62   CIM+Dup  CIM+Dup      CIM+Dup      CIM+Dup  CIM+Dup  CIM+Def+Dup+OB+Pru
0.80   CIM+Dup  CIM+Dup  CIM+Dup+TFT  CIM+Dup+TFT  CIM+Dup                   —
1.00   CIM+Dup        —            —            —        —                   —
```


### dominant replicator support

```
t                                                 1.0                                             0.8                                             0.6                                             0.4                                             0.2                                             0.0
alpha                                                                                                                                                                                                                                                                                                
0.00   CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT
0.30                                 CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                           CIM+Coop+CupT+Dup+TFT                                      Def+OB+Pru
0.45                                 CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                     CIM+Dup+TFT                              CIM+Def+Dup+OB+Pru
0.62                                 CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                     CIM+Dup+TFT                                         CIM+Dup                              CIM+Def+Dup+OB+Pru
0.80                                 CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                     CIM+Dup+TFT                                     CIM+Dup+TFT                              CIM+Def+Dup+OB+Pru            CIM+Cup+DB+DIM+Def+Dup+EB+OB+Pru+TFT
1.00                                 CIM+Coop+Dup+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT
```

## body+twins — syntactic

### stochastically stable (M=100, β=1)

```
t          1.0      0.8      0.6      0.4             0.2                 0.0
alpha                                                                        
0.00         —        —        —        —               —                   —
0.30   CIM+Dup  CIM+Dup  CIM+Dup  CIM+Dup         CIM+Dup          Def+OB+Pru
0.45   CIM+Dup  CIM+Dup  CIM+Dup  CIM+Dup         CIM+Dup  CIM+Def+Dup+OB+Pru
0.62   CIM+Dup  CIM+Dup  CIM+Dup  CIM+Dup          OB+Pru  CIM+Def+Dup+OB+Pru
0.80   CIM+Dup  CIM+Dup  Def+Pru   OB+Pru  CIM+Dup+OB+Pru                   —
1.00   CIM+Dup        —        —        —               —                   —
```


### dominant replicator support

```
t                                                 1.0                                             0.8                                             0.6                                             0.4                                             0.2                                             0.0
alpha                                                                                                                                                                                                                                                                                                
0.00   CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT
0.30                                 CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                      Def+OB+Pru
0.45                                 CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                              CIM+Def+Dup+OB+Pru
0.62                                 CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                              CIM+Def+Dup+OB+Pru                              CIM+Def+Dup+OB+Pru
0.80                                 CIM+Coop+Dup+TFT                                CIM+Coop+Dup+TFT                              CIM+Def+Dup+OB+Pru                              CIM+Def+Dup+OB+Pru                              CIM+Def+Dup+OB+Pru            CIM+Cup+DB+DIM+Def+Dup+EB+OB+Pru+TFT
1.00                                 CIM+Coop+Dup+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+OB+Pru+TFT
```

## body+twins+natives — behavioral

### stochastically stable (M=100, β=1)

```
t                  1.0          0.8          0.6          0.4          0.2                     0.0
alpha                                                                                             
0.00                 —            —            —            —            —                       —
0.30   CIM+Dup+Max+Min  Def+Pru+TFT  Def+Pru+TFT  Def+Pru+TFT  Def+Max+Pru          Def+Max+OB+Pru
0.45   CIM+Dup+Max+Min  Def+Pru+TFT  Def+Pru+TFT  Def+Pru+TFT          Max  CIM+Def+Dup+Max+OB+Pru
0.62   CIM+Dup+Max+Min      Max+TFT      Max+TFT          Max          Max  CIM+Def+Dup+Max+OB+Pru
0.80   CIM+Dup+Max+Min      Max+TFT          TFT          Max  CIM+Dup+Max                       —
1.00   CIM+Dup+Max+Min   Def+OB+Pru            —            —            —                       —
```


### dominant replicator support

```
t                                                         1.0                                                     0.8                                                     0.6                                                     0.4                                                     0.2                                                     0.0
alpha                                                                                                                                                                                                                                                                                                                                                
0.00   CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT
0.30                                 CIM+Coop+Dup+Max+Min+TFT                                          Def+Max+OB+Pru                                          Def+Max+OB+Pru                                          Def+Max+OB+Pru                                          Def+Max+OB+Pru                                          Def+Max+OB+Pru
0.45                                 CIM+Coop+Dup+Max+Min+TFT                                          Def+Max+OB+Pru                                          Def+Max+OB+Pru                                          Def+Max+OB+Pru                                          Def+Max+OB+Pru                                  CIM+Def+Dup+Max+OB+Pru
0.62                                 CIM+Coop+Dup+Max+Min+TFT                                          Def+Max+OB+Pru                                          Def+Max+OB+Pru                                          Def+Max+OB+Pru                                          Def+Max+OB+Pru                                  CIM+Def+Dup+Max+OB+Pru
0.80                                 CIM+Coop+Dup+Max+Min+TFT                                          Def+Max+OB+Pru                                                     TFT                                          Def+Max+OB+Pru                                  CIM+Def+Dup+Max+OB+Pru                CIM+Cup+DB+DIM+Def+Dup+EB+Max+OB+Pru+TFT
1.00                                 CIM+Coop+Dup+Max+Min+TFT               CIM+Cup+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT
```

## body+twins+natives — epsilon

### stochastically stable (M=100, β=1)

```
t                  1.0              0.8              0.6              0.4          0.2                     0.0
alpha                                                                                                         
0.00                 —                —                —                —            —                       —
0.30   CIM+Dup+Max+Min  CIM+Dup+Max+Min  CIM+Dup+Max+Min      CIM+Dup+Max  CIM+Dup+Max          Def+Max+OB+Pru
0.45   CIM+Dup+Max+Min  CIM+Dup+Max+Min  CIM+Dup+Max+Min  CIM+Dup+Max+Min          Max  CIM+Def+Dup+Max+OB+Pru
0.62   CIM+Dup+Max+Min  CIM+Dup+Max+Min  CIM+Dup+Max+Min  CIM+Dup+Max+Min          Max  CIM+Def+Dup+Max+OB+Pru
0.80   CIM+Dup+Max+Min  CIM+Dup+Max+Min              Max      CIM+Dup+Max  CIM+Dup+Max                       —
1.00   CIM+Dup+Max+Min                —                —                —            —                       —
```


### dominant replicator support

```
t                                                         1.0                                                     0.8                                                     0.6                                                     0.4                                                     0.2                                                     0.0
alpha                                                                                                                                                                                                                                                                                                                                                
0.00   CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT  CIM+Coop+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT
0.30                                 CIM+Coop+Dup+Max+Min+TFT                                CIM+Coop+Dup+Max+Min+TFT                                CIM+Coop+Dup+Max+Min+TFT                                CIM+Coop+Dup+Max+Min+TFT                                CIM+Coop+Dup+Max+Min+TFT                                          Def+Max+OB+Pru
0.45                                 CIM+Coop+Dup+Max+Min+TFT                                CIM+Coop+Dup+Max+Min+TFT                                CIM+Coop+Dup+Max+Min+TFT                                CIM+Coop+Dup+Max+Min+TFT                                          Def+Max+OB+Pru                                  CIM+Def+Dup+Max+OB+Pru
0.62                                 CIM+Coop+Dup+Max+Min+TFT                                CIM+Coop+Dup+Max+Min+TFT                                CIM+Coop+Dup+Max+Min+TFT                                CIM+Coop+Dup+Max+Min+TFT                                          Def+Max+OB+Pru                                  CIM+Def+Dup+Max+OB+Pru
0.80                                 CIM+Coop+Dup+Max+Min+TFT                                CIM+Coop+Dup+Max+Min+TFT                                          Def+Max+OB+Pru                                  CIM+Def+Dup+Max+OB+Pru                                  CIM+Def+Dup+Max+OB+Pru                CIM+Cup+DB+DIM+Def+Dup+EB+Max+OB+Pru+TFT
1.00                                 CIM+Coop+Dup+Max+Min+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT       CIM+Cup+CupT+DB+DIM+Def+Dup+EB+Max+Min+OB+Pru+TFT
```
