# Robust Program Equilibrium — Agent-by-Agent Breakdown

This document extracts all named agents/program schemas stated in `robust_program_equi.pdf`.

As in your tournament notes, each section gives:
- a compact program sketch
- what the strategy does
- why it matters

Setting: one-shot Prisoner's Dilemma with source-code access. Each agent receives opponent source `X` and returns `C` (cooperate) or `D` (defect).

Payoffs: `CC -> 2/2`, `CD -> 0/3`, `DC -> 3/0`, `DD -> 1/1`.

---

## CooperateBot (CB) — Always Cooperate

From Algorithm 1.

```text
Input: source code of agent X
Output: C or D
return C
```

**Behavior:** Ignores the opponent and always cooperates.

**Why it matters:** Baseline naive bot; trivially exploitable.

---

## DefectBot (DB) — Always Defect

From Algorithm 2.

```text
Input: source code of agent X
Output: C or D
return D
```

**Behavior:** Ignores the opponent and always defects.

**Why it matters:** Baseline hardline bot; unexploitable but never gets mutual-cooperation upside.

---

## CliqueBot — Exact Self-Recognition via Source Equality

From Algorithm 3.

```text
Input: source code of agent X
Output: C or D
if X == CliqueBot then
  return C
else
  return D
```

**Behavior:** Cooperates only with exact syntactic copies of itself; defects otherwise.

**Why it matters:** Safe from exploitation, but brittle: small source-level differences break cooperation.

---

## FairBot (FB) — Loebian Proof-Based Cooperation

From Algorithm 4.

```text
Input: source code of agent X
Output: C or D
if PA proves [X(FairBot) = C] then
  return C
else
  return D
```

**Behavior:** Cooperates iff it can prove the opponent cooperates with FairBot.

**Why it matters:** More flexible than CliqueBot: can cooperate across different implementations/languages if proof obligations line up.

---

## PrudentBot (PB) — FairBot + Anti-Naive Safety Check

From Algorithm 5.

```text
Input: source code of agent X
Output: C or D
if (PA proves [X(PrudentBot) = C])
   and (PA+1 proves [X(DefectBot) = D]) then
  return C
return D
```

**Behavior:** Cooperates only when it can prove both:
1. opponent cooperates with PrudentBot, and
2. opponent defects against DefectBot (in a stronger system).

**Why it matters:** Preserves robust cooperation with sophisticated bots while avoiding FairBot's over-cooperation with naive cooperators.

---

## JustBot (JB) — Cooperate with FairBot-Cooperators

From Algorithm 6.

```text
Input: source code of agent X
Output: C or D
if PA proves [X(FairBot) = C] then
  return C
else
  return D
```

**Behavior:** Cooperates exactly with agents provably cooperative with FairBot.

**Why it matters:** Behaviorally equivalent to FairBot over modal opponents, despite different source code.

---

## FiniteFairBot — Bounded Proof-Search FairBot Variant

Named in a remark (not numbered as an algorithm).

```text
Input: source code of agent X
Parameter: proof-length bound N
Search all proofs of length <= N
if some proof establishes [X(FiniteFairBot) = C] then
  return C
else
  return D
```

**Behavior:** Practical finite approximation of FairBot.

**Why it matters:** Connects abstract Loebian definitions to implementable bounded agents.

---

## TrollBot — DefectBot-Cooperation Filter

Named as an example in Section 5.

```text
Input: source code of agent X
Output: C or D
if PA proves [X(DefectBot) = C] then
  return C
else
  return D
```

**Behavior:** Cooperates only with agents that cooperate with DefectBot.

**Why it matters:** Demonstrates how modal agents can be selectively rewarded/punished by arbitrary logical criteria.

---

## WaitFairBot_K — Stronger-System FairBot Family

Named as a family in Section 5.

Formal definition in the paper:

```text
[WaitFairBot_K(X) = C] <-> ((not Box^K false)
                            and Box(not Box^K false -> [X(WaitFairBot_K) = C]))
```

Informal reading:

```text
Input: source code of agent X
Output: C or D
if (K-level consistency condition holds)
   and (in that stronger system it is provable that
        consistency implies X cooperates with WaitFairBot_K)
then return C
else return D
```

**Behavior:** A hierarchy of FairBot-like agents with increasing deductive strength.

**Why it matters:** Highlights deductive-limit issues: some agents that defect vs DefectBot fail to cooperate with sufficiently strong WaitFairBot levels.

---

## Summary Table

| Agent | Source in paper | Strategy class | Core rule |
|---|---|---|---|
| CooperateBot (CB) | Algorithm 1 | Constant | Always `C` |
| DefectBot (DB) | Algorithm 2 | Constant | Always `D` |
| CliqueBot | Algorithm 3 | Syntactic self-match | `C` iff opponent source equals own source |
| FairBot (FB) | Algorithm 4 | Loebian/modal | `C` iff provable that opponent cooperates with FB |
| PrudentBot (PB) | Algorithm 5 | Loebian/modal + safety check | Requires proof of cooperation with PB and proof opponent defects vs DB |
| JustBot (JB) | Algorithm 6 | Modal/reference bot | `C` iff provable that opponent cooperates with FB |
| FiniteFairBot | Remark after Theorem 3.1 | Bounded proof search | Searches proofs up to bound `N` |
| TrollBot | Section 5 example | Modal filter | `C` iff provable opponent cooperates with DB |
| WaitFairBot_K | Section 5 family | Strong-system modal family | FairBot-style criterion in stronger system indexed by `K` |
