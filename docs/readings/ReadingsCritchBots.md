# Cooperative and Uncooperative Institution Designs — Strategy-by-Strategy Breakdown

This document extracts the named agent strategies stated in Readings Critch.pdf and rewrites them in a tournament-style format.

Setting: one-shot Prisoner's Dilemma with source-code access. Each strategy receives opponent source code and returns C (cooperate) or D (defect).

Payoffs: CC -> 2/2, CD -> 0/3, DC -> 3/0, DD -> 1/1.

---

## CB (CooperateBot) — Always Cooperate

```python
# "CooperateBot":
def CB(opp_source):
    return C
```

Behavior: Ignores the opponent and always cooperates.

Key property: Fully exploitable.

---

## DB (DefectBot) — Always Defect

```python
# "DefectBot":
def DB(opp_source):
    return D
```

Behavior: Ignores the opponent and always defects.

Key property: Unexploitable baseline, but no mutual-cooperation upside with itself.

---

## CUPOD(k) — Cooperate Unless Proof of Defection

```python
# "Cooperate Unless Proof Of Defection" (CUPOD):
def CUPOD(k):
    def CUPOD_k(opp_source):
        if proof_search(k, opp_source, "opp(CUPOD_k.source) == D"):
            return D
        else:
            return C
    CUPOD_k.source = ...
    return CUPOD_k
```

Behavior: Tries to find a bounded-length proof that the opponent defects against CUPOD(k). If found, defects; otherwise cooperates.

Key properties from the paper:
- Never exploits the opponent (never gets D,C).
- Self-play result for large k: outcome(CUPOD(k), CUPOD(k)) == (D,D).

---

## DUPOC(k) — Defect Unless Proof of Cooperation

```python
# "Defect Unless Proof Of Cooperation" (DUPOC):
def DUPOC(k):
    def DUPOC_k(opp_source):
        if proof_search(k, opp_source, "opp(DUPOC_k.source) == C"):
            return C
        else:
            return D
    DUPOC_k.source = ...
    return DUPOC_k
```

Behavior: Tries to find a bounded-length proof that the opponent cooperates against DUPOC(k). If found, cooperates; otherwise defects.

Key properties from the paper:
- Is never exploited (never gets C,D).
- Self-play result for large k: outcome(DUPOC(k), DUPOC(k)) == (C,C).
- Highlighted as broadly cooperative with legible cooperators (via G-fairness discussion).

---

## PDUPOC(k, q) — Probabilistic DUPOC

```python
# Probabilistic DUPOC (PDUPOC):
def PDUPOC(K, Q):
    def PDUPOC_k(opp_source):
        k = K
        q = Q
        if proof_search(k, opp_source, "Prob('opp(DUPOC_k.source) == C' >= q)"):
            if random.uniform(0, 1) <= q:
                return C
            else:
                return D
    PDUPOC_k.source = ...
    return PDUPOC_k
```

Behavior: Looks for a proof that the opponent cooperates with probability at least q; if found, randomizes to cooperate with probability q.

Key theorem in paper:
- For large k and q >= 0.5, self-play mutual cooperation has probability at least 2q - 1.
- If independent randomness is assumed, bound improves to q^2.

Note: OCR/extraction around this snippet is noisy in the PDF text dump; the structure above follows the stated intent in the surrounding explanation.

---

## CIMCIC(k) — Cooperate If My Cooperation Implies Opponent Cooperation

```python
# "Cooperate If My Cooperation Implies Cooperation from the opponent" (CIMCIC):
def CIMCIC(k):
    def CIMCIC_k(opp_source):
        if proof_search(k, opp_source,
                        "(CIMCIC_k(opp.source)==C) => (opp(CIMCIC_k.source)==C)"):
            return C
        else:
            return D
    CIMCIC_k.source = ...
    return CIMCIC_k
```

Behavior: Cooperates if it can prove the implication: if I cooperate, then you cooperate.

Key properties/theorems:
- Unexploitable.
- For large k: outcome(CIMCIC(k), CIMCIC(k)) == (C,C).
- For large k: outcome(DUPOC(k), CIMCIC(k)) == (C,C).

---

## DIMCID(k) — Defect If My Cooperation Implies Opponent Defection

```python
# "Defect if My Cooperation Implies Defection from the opponent" (DIMCID):
def DIMCID(k):
    def DIMCID_k(opp_source):
        if proof_search(k, opp_source,
                        "(DIMCID_k(opp.source)==C) => (opp(DIMCID_k.source)==D)"):
            return D
        else:
            return C
    DIMCID_k.source = ...
    return DIMCID_k
```

Behavior: Preemptive anti-exploitation strategy. If it can prove that its own cooperation would induce opponent defection, it defects.

Key theorem in paper:
- For large k: outcome(DIMCID(k), DIMCID(k)) == (D,D).
- For large k: outcome(CUPOD(k), DIMCID(k)) == (D,D).

---

## CDEBot (conceptual, open-problem strategy)

The paper proposes CDEBot conceptually (not with full final code): in a 3-action game (C, D, E), it tries to prove and target outcomes in priority order:
1. First target (C,C).
2. If that fails, target (D,D).
3. If that fails, play E (encroach).

Status in paper: posed as an implementation challenge (Open Problem 10).

---

## EUPOD(k) (conceptual, open-problem strategy)

Described conceptually as Encroach Unless Proof of Defection, analogous to DUPOC with symbols shifted for the C/D/E game.

Status in paper: used as counterpart to CDEBot in Open Problem 10.

---

## PrudentBot (referenced external strategy)

The paper references PrudentBot from earlier work as a computationally unbounded design and asks whether bounded versions exist.

Status here: referenced but not fully redefined in this paper.

---

## Summary Table

| Strategy | Class | Main criterion | Key stated outcome/property |
|---|---|---|---|
| CB | Constant-cooperate | Always C | Exploitable baseline |
| DB | Constant-defect | Always D | Unexploitable baseline |
| CUPOD(k) | Proof-based cautious cooperator | Defect only if proof of opponent defection | Self-play tends to (D,D) for large k |
| DUPOC(k) | Proof-based cautious defector | Cooperate only if proof of opponent cooperation | Self-play tends to (C,C) for large k |
| PDUPOC(k, q) | Probabilistic proof-based | Cooperate with prob q if proof of prob-cooperation >= q | Self-play cooperation probability lower-bounded |
| CIMCIC(k) | Conditional-proof cooperator | Cooperate if own cooperation implies opponent cooperation | Self-play and vs DUPOC yield (C,C) for large k |
| DIMCID(k) | Conditional-proof preemptive defector | Defect if own cooperation implies opponent defection | Self-play and vs CUPOD yield (D,D) for large k |
| CDEBot | 3-action conceptual policy | Target (C,C), then (D,D), else E | Open implementation problem |
| EUPOD(k) | 3-action conceptual policy | Encroach unless proof-of-defection analogue | Open implementation problem |
| PrudentBot | Referenced external family | Additional anti-CooperateBot proof search | Bounded version posed as open problem |
