# Prisoner's Dilemma Tournament — Bot-by-Bot Breakdown

This document explains each of the 21 bots (`A` through `U`) from the LessWrong Prisoner's Dilemma tournament. In this tournament every bot receives the **source code** of its opponent as input and must return `'C` (cooperate) or `'D` (defect). Bots can `eval` the opponent's source to simulate what it would do, inspect its syntax tree, or ignore it entirely.

Payoffs: CC → 2 each, CD → 0/3, DC → 3/0, DD → 1 each.

---

## ABot — Random Coin Flip

```scheme
(lambda (x)
  (if (eq? (random 2) 0) 'C 'D))
```

**Behavior:** Ignores the opponent entirely. Flips a fair coin and cooperates or defects with equal probability (50/50). This is the simplest non-trivial strategy — pure noise.

---

## BBot — Probe with CooperateBot

```scheme
(lambda (x)
  ((eval x) '(lambda (y) 'C)))
```

**Behavior:** Evaluates the opponent's code and runs it against an always-cooperate bot. Returns whatever the opponent would play against a cooperator. If the opponent cooperates with a cooperator, BBot cooperates; if the opponent would defect against a cooperator, BBot defects. This is a basic "mirror" strategy: be as nice as the opponent would be to a pushover.

---

## CBot — Random Coin Flip (Duplicate of A)

```scheme
(lambda (x)
  (if (eq? (random 2) 0) 'C 'D))
```

**Behavior:** Identical to ABot. Random 50/50 cooperate or defect, ignoring the opponent.

---

## DBot — Contrarian Probe

```scheme
(lambda (x)
  (if (eq? ((eval x) '(lambda (y) 'D)) 'C)
      'D
      'C))
```

**Behavior:** Evaluates the opponent against an always-defect bot. If the opponent would cooperate even against a defector (i.e., it's naive), DBot **defects** to exploit it. If the opponent would defect against a defector, DBot **cooperates**. This is a contrarian/exploiter: it punishes naivety and cooperates with defensive bots.

---

## EBot — Unit-Tested MimicBot (by Devin Bayer)

```scheme
(lambda (other)
  (define CooperateBot '(lambda (x) 'C))
  (define DefectBot '(lambda (x) 'D))
  (define ErrorBot '(lambda (x) '?))
  (define MirrorBot '(lambda (x) ...))
  (define MyBot '(lambda (x) ...))

  ;; unit tests ...
  ((eval MyBot) other))
```

**Behavior:** Defines a suite of test bots internally (CooperateBot, DefectBot, ErrorBot, MirrorBot) and a strategy bot `MyBot`. MyBot's logic is:

1. If the opponent cooperates with DefectBot → **defect** (the opponent is a sucker).
2. Else if the opponent cooperates with CooperateBot → **cooperate**.
3. Else if the opponent cooperates with MirrorBot → **cooperate**.
4. Otherwise → **defect**.

Before playing, EBot runs unit tests on its own strategy to verify correctness. It confirms that MyBot defects against CooperateBot, defects against DefectBot, cooperates with MirrorBot, defects against ErrorBot, and cooperates with itself.

---

## FBot — Recursive Countdown Prober

```scheme
(lambda (x)
  ((lambda (N Q)
    (if (<= N 0) 'C
        ((eval x) (list 'lambda '(x) (list Q (- N 1) (list 'quote Q))))))
   122
   '(lambda (N Q)
       (if (<= N 0) 'C
           ((eval x) (list 'lambda '(x) (list Q (- N 1) (list 'quote Q))))))))
```

**Behavior:** Builds a chain of 122 nested simulations. At each level it constructs a new lambda that decrements a counter and passes it to the opponent. When the counter reaches 0, it cooperates. Essentially it asks the opponent: "what do you do against a bot that cooperates after N rounds of mutual simulation?" If the opponent can handle the recursion and eventually cooperates, FBot cooperates. If the opponent errors out or defects at some depth, FBot inherits that result. This is a deep-probing MimicBot: it tests the opponent's willingness to cooperate at the bottom of a deep call stack.

---

## GBot — Almost Always Cooperate (with Obfuscated Defection)

```scheme
(lambda (opp)
  (if (or (> (random 4) 0) (eq? opp '(lambda)))
    'C
    (string->symbol (string (integer->char (* 4 17))))))
```

**Behavior:** Cooperates 75% of the time (when `(random 4)` returns 1, 2, or 3). The remaining 25% of the time, it returns `(string->symbol (string (integer->char 68)))` which is `'D` — but constructed by character arithmetic rather than written literally. This obfuscation may fool bots doing naive static analysis looking for the literal symbol `'D` in the source code.

---

## HBot — Always Cooperate

```scheme
(lambda (x) 'C)
```

**Behavior:** Unconditionally cooperates. The simplest possible cooperative strategy. Fully exploitable.

---

## IBot — Always Cooperate (Verbose)

```scheme
(lambda (opponent) 'C)
```

**Behavior:** Identical to HBot. Always cooperates. The only difference is the parameter name (`opponent` instead of `x`).

---

## JBot — Always Cooperate (Another Duplicate)

```scheme
(lambda(x) 'C)
```

**Behavior:** Identical to HBot. Always cooperates.

---

## KBot — Quine-Based Self-Recognizer

```scheme
(lambda (x)
  (define src ...)       ;; builds a quine of itself
  (define quines 0)
  (define quineBox ...)  ;; increments quines counter
  (define quineDetector  ;; a bot that cooperates iff given KBot's own source
    (quasiquote
      (lambda (y)
        (if (equal? y (quote (unquote x)))
            (begin (unquote (list quineBox)) 'C)
            'D))))
  (parameterize (...)
    ;; with 1% probability, cooperate unconditionally
    ;; otherwise: simulate the opponent against KBot's own source
    ;; if opponent cooperates, send quineDetector to check
    ;; if opponent recognizes KBot, cooperate; else defect
    ...))
```

**Behavior:** KBot is a quine — it can reconstruct its own source. Its strategy:

1. With 1% probability, cooperate (noise/fairness term).
2. Otherwise, evaluate the opponent against KBot's own source code. If the opponent cooperates with KBot:
   - Send quineDetector (a bot that cooperates only when given KBot's exact source) to the opponent twice.
   - If the opponent ever gives quineDetector KBot's source (proving it's another copy of KBot or a friendly bot), cooperate.
   - Otherwise defect.
3. If the opponent defects against KBot, defect.

This is a **CliqueBot**: it tries to cooperate only with copies of itself or bots that can prove they know KBot's source.

---

## LBot — Statistical Sampler

```scheme
(lambda (their_code)
  (begin
    (random-seed (remainder (current-milliseconds) 2147483647))
    (define coop_num 0)
    (define def_num 0)
    (for ([i 10])
      (if (eq?
           ((eval their_code) '(lambda (_) (if (eq? (random 2) 0) 'C 'D)))
           'C)
        (set! coop_num (+ coop_num 1))
        (set! def_num (+ def_num 1))))
    (if (<=
         (random 6)
         (if (<= coop_num 5) coop_num (- 10 coop_num)))
         'C
         'D)))
```

**Behavior:** Re-seeds the random number generator, then runs the opponent 10 times against a random bot (50/50 C/D). Counts how many times the opponent cooperated (`coop_num`). Then:

- If `coop_num` is ≤ 5, it uses `coop_num` as the cooperation threshold.
- If `coop_num` > 5, it uses `10 - coop_num` (mirrors the scale).

It draws `(random 6)` and cooperates if that value is ≤ the threshold. This means LBot cooperates **more** when the opponent seems moderately cooperative, and **less** when the opponent is extreme in either direction (always cooperate or always defect). It is a probabilistic tit-for-tat variant that samples opponent behavior empirically.

---

## MBot — Static Analysis: Eval Detector

```scheme
(lambda (x)
  (letrec
    ([haseval (lambda (a)
                (or
                 (equal? a 'eval)
                 (and
                  (not (equal? a ''eval))
                  (pair? a)
                  (or
                   (haseval (car a))
                   (haseval (cdr a))))))])
    (cond
      [(not (haseval x)) 'C]
      [else 'D])))
```

**Behavior:** Walks the opponent's source tree looking for the symbol `eval`. If the opponent's code contains `eval` anywhere (but not a quoted `'eval`), MBot **defects**. If there is no `eval`, MBot **cooperates**. The rationale: bots that use `eval` are likely simulating you and may be dangerous; bots without `eval` are likely simple/naive and safe to cooperate with.

---

## NBot — Self-Modifying Quine with Time-Warfare (by "LightninRoy")

```scheme
(lambda (opp-source)
  (define start-time (current-milliseconds))
  (define maniacal-laugh (string->symbol ...))  ;; = 'D, obfuscated
  ;; ... large body with quining, namespaces, self-modification ...
  (guard (lambda (opp-source-2) ...)))
```

**Behavior:** NBot is one of the most complex entries. Key features:

1. **Self-recognition:** Searches opponent source for the symbol `'LightninRoy`; if found, cooperates (assumes it is fighting a copy of itself).
2. **Self-modification:** Uses Racket namespaces to construct evolved versions of itself across "generations." Each generation has a `last-gen` counter and adjusted timeouts.
3. **Time warfare:** In certain scenarios (generation 0, opponent is unfamiliar), it enters an infinite loop to consume the clock, forcing a timeout and mutual defection — rather than being exploited.
4. **Generation 4 truce:** At generation 4 specifically, cooperates unconditionally (possibly a coordination point).
5. **Omega test:** Falls back to simulating the opponent against its own evolved quine and cooperating if the opponent cooperates.
6. **Guarded execution:** Everything runs inside a timeout guard thread; if anything takes too long, it defects.

The obfuscated defection symbol is built via `(string->symbol (bytes->string/utf-8 (make-bytes 1 68)))` which produces `'D` without the literal appearing in the source.

---

## OBot — Double Probe

```scheme
(lambda (x)
  (if (eq? ((eval x) '(lambda (y) 'C)) 'C)
      ((eval x) '(lambda (y) 'D))
    (if (eq? ((eval x) '(lambda (y) 'D)) 'D)
        ((eval x) '(lambda (y) 'C))
      'D)))
```

**Behavior:** Probes the opponent twice:

1. First, asks "what do you do against a cooperator?" If the opponent cooperates:
   - Then asks "what do you do against a **defector**?" and returns that answer.
   - This exploits bots that cooperate with cooperators but also cooperate with defectors (suckers).
2. If the opponent defects against a cooperator:
   - Asks "what do you do against a defector?" If the opponent defects against a defector:
     - Asks "what do you do against a cooperator?" and returns that.
   - Otherwise defects.

This bot tries to find inconsistencies in the opponent's behavior across different inputs and exploit them.

---

## PBot — Quine MimicBot with Yield-Eval Sandboxing

```scheme
(lambda (x)
  (define sub (quote (lambda (this y) ...)))
  (define (ueval x) (define ns (make-base-namespace)) (eval x ns))
  ((ueval sub) sub x))
```

**Behavior:** PBot is a sophisticated MimicBot that:

1. **Builds a quine** of itself (`quine-my-source`).
2. **Uses `yield_eval`** — a custom eval that inserts `(sleep 0)` calls, yielding the thread between evaluations to avoid monopolizing CPU.
3. **Uses `cval`** — a "cheating eval" that intercepts evaluations of PBot's own source and returns a modified version that auto-cooperates with the current opponent. This lets PBot trick the opponent into thinking PBot cooperates.
4. **Timeout sandboxing** at 0.5 seconds per simulation.
5. **Strategy:**
   - Runs the opponent (via `cval`, which lies about PBot's behavior) against PBot's quine. If the opponent cooperates, and the opponent also cooperates with a trivial CooperateBot and defects with a "stupid bot", then PBot **defects** (exploitation). Otherwise PBot cooperates.
   - If the opponent defects against PBot's (faked) source, PBot defects.

The `cval` trick is the key insight: PBot lies to the opponent during simulation, making itself look cooperative, and then decides based on the opponent's trusting response.

---

## QBot — Mostly Defect

```scheme
(lambda (x) (if (<= (random 100) 80) 'D 'C))
```

**Behavior:** Defects ~81% of the time and cooperates ~19% of the time, regardless of the opponent. A near-always-defect strategy with a small cooperative tail.

---

## RBot — Rank 4 MimicBot with Reconnaissance (by "NateBot")

```scheme
(lambda (opponent)
  (letrec [... ~500 lines of code ...]
    (if (cooperate) `C `D)))
```

**Behavior:** The most heavily documented and engineered bot. RBot is a **Rank 4 MimicBot** — it simulates the opponent against 4 levels of self-similar quines and uses the results as intelligence. Key mechanisms:

1. **Quine generation:** Builds exact copies of itself at decreasing "rank" (3, 2, 1, 0). Rank 0 is a plain CooperateBot.
2. **ReconBots:** Sends modified versions of itself that report back (via thread messages) what the opponent did, building an "intel tree."
3. **Simulation detection:** Analyzes the intel tree to determine whether it is the "real" RBot or a simulation. It checks for:
   - **Fang removal:** Did a random/timing call disappear between levels? (Non-deterministic MimicBot detected → on top → defect.)
   - **Brand insertion:** Did the opponent inject threads/procedures/channels into the code? (Lying MimicBot detected → on top → defect.)
   - **Top-heaviness:** Is the first level much larger than subsequent levels? (Top-heavy MimicBot → on top → defect.)
   - **Over-eagerness:** Does the first level eval more than subsequent levels? (Over-eager MimicBot → on top → defect.)
4. **Panic button:** At rank 2, if it detects top-heavy or over-eager patterns, it defects to prevent higher-level exploitation.
5. **Flaky bot detection:** If the opponent never called RBot's ReconBots, is reasonably large, and doesn't use `thread?`/`symbol?` (functions that would detect ReconBots), RBot assumes it's an accidental CooperateBot and defects.
6. **Always cooperates with CooperateBot** at the bottom to avoid losing points against truly naive bots.

---

## SBot — Syntax Check + Time Staller

```scheme
(lambda (x)
  (cond [(and (eq? (car x) 'lambda)
              (equal? (caddr x) ''C))
         'C]
        [else (letrec ([start-time (current-seconds)])
                (sleep 9)
                (if (< (- (current-seconds) start-time)
                       (remainder 1415926535 8))
                    'C
                    (string->symbol (make-string 1 (integer->char (+ 67 1))))))]))
```

**Behavior:**

1. If the opponent's source is a trivial `(lambda (x) 'C)` (checks that the first element is `'lambda` and the third is `''C`), cooperates immediately.
2. Otherwise, sleeps for 9 seconds (nearly the full 10-second timeout), then checks if the sleep actually took less than `(remainder 1415926535 8)` = 7 seconds. Since 9 > 7, this condition is always false, so it returns `(integer->char 68)` = `'D`.

In practice: cooperates with trivial CooperateBots, defects (after wasting time) against everything else. The 9-second sleep is hostile — it burns the opponent's time budget.

---

## TBot — Quine MimicBot with Lazy-Defect Detection

```scheme
(lambda (otherbot)
  ((
    (lambda (s) (lambda (x)
      (define impatient (lambda (z) z))
      (define lazy-defectbot '(lambda (y) '((sleep) (if (zero? 1) 'C 'D))))
      (if (or (eq? ((eval (impatient x) (make-base-namespace)) lazy-defectbot) 'D)
              (eq? ((eval (impatient x)) lazy-defectbot) 'D))
          (if (zero? (random 100)) 'C
              ((eval x (make-base-namespace)) (list s (list 'quote s))))
          (if (zero? 1) 'C 'D))))
   '(lambda (s) ...same code quoted...))
   otherbot))
```

**Behavior:** TBot uses a quine (the `(lambda (s) ...)` applied to its own quoted source) and probes the opponent with a **lazy-defectbot** — a bot whose source looks like it might cooperate but actually defects (since `(zero? 1)` is false). Steps:

1. Run the opponent against `lazy-defectbot`. If the opponent returns `'D` (it defected against this tricky bot):
   - With 1% probability, cooperate.
   - Otherwise, run the opponent against TBot's own quine and return that result. This is the MimicBot path: cooperate if the opponent cooperates with you.
2. If the opponent cooperated with `lazy-defectbot` (the opponent was fooled), TBot defects (via `(if (zero? 1) 'C 'D)` which is always `'D`).

The `impatient` function is an identity wrapper — the author may have intended to add timeout logic.

---

## UBot — Keyword Grep

```scheme
(lambda (x)
  (define s (pretty-format x))
  (cond [(regexp-match "quine" s) 'C]
        [(regexp-match "thread" s) 'D]
        [(regexp-match "eval.*eval" s) 'D]
        [else 'C]))
```

**Behavior:** Pretty-prints the opponent's source to a string and does regex matching:

1. If the source contains the word `"quine"` → **cooperate** (assumes it's a sophisticated but friendly MimicBot).
2. If the source contains `"thread"` → **defect** (assumes it's a dangerous sandboxing/timeout bot).
3. If the source contains `eval` appearing twice (`"eval.*eval"`) → **defect** (assumes it's doing deep simulation, possibly adversarial).
4. Otherwise → **cooperate**.

This is pure static analysis with no execution of the opponent's code.

---

## Summary Table

| Bot | Strategy Class | Uses `eval`? | Key Trait |
|-----|---------------|-------------|-----------|
| A | Random | No | 50/50 coin flip |
| B | Probe | Yes | Returns opponent's response to CooperateBot |
| C | Random | No | 50/50 coin flip (duplicate of A) |
| D | Probe | Yes | Contrarian: exploits naive bots |
| E | Probe + Tests | Yes | Multi-probe with unit tests |
| F | Recursive Probe | Yes | 122-deep nested simulation |
| G | Random | No | 75% cooperate, obfuscated defect |
| H | Cooperate | No | Always cooperate |
| I | Cooperate | No | Always cooperate |
| J | Cooperate | No | Always cooperate |
| K | Quine/Clique | Yes | Cooperates only with self-copies |
| L | Statistical | Yes | Samples opponent 10 times |
| M | Static Analysis | No | Defects if source contains `eval` |
| N | Quine + Time | Yes | Self-modifying, time-warfare |
| O | Double Probe | Yes | Probes with both C-bot and D-bot |
| P | Quine + Lie | Yes | Fakes its own behavior in simulation |
| Q | Mostly Defect | No | ~81% defect |
| R | Rank 4 Mimic | Yes | Deep reconnaissance with intel trees |
| S | Syntax + Stall | No | Cooperates with trivial C-bots, stalls others |
| T | Quine + Probe | Yes | Tests opponent with tricky bot |
| U | Keyword Grep | No | Regex on pretty-printed source |
