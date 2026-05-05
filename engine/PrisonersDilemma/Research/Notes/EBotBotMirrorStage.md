# EBot vs EBot at the MirrorBot Stage

This note follows the evaluator call chain for `EBot` against itself, using the
current `.bot` version of the program language.

Let:

```lean
E = EBot
M = MirrorBot
```

The current third guard in `EBot` is:

```lean
.sim .opp (.bot M)
```

not:

```lean
.sim .opp M
```

The point of `.bot M` is to say: this is a literal named bot source. Do not
substitute inside `M` yet.

## Starting from `play`

The entry point is:

```lean
play fuel me opponent := eval fuel me opponent me
```

So `EBot` against itself starts as:

```lean
play fuel E E
= eval fuel E E E
```

Now unfold `E`. Ignoring fuel bookkeeping, `EBot` has this shape:

```lean
E =
.ite
  (.sim .opp (.bot DefectBot))
  Action.C
  (.const Action.D)
  (.ite
    (.sim .opp (.bot CooperateBot))
    Action.C
    (.const Action.C)
    (.ite
      (.sim .opp (.bot M))
      Action.C
      (.const Action.C)
      (.const Action.D)))
```

So evaluation starts with the first `ite`:

```lean
eval E E
  (.ite
    (.sim .opp (.bot DefectBot))
    C
    (.const D)
    rest)
```

The evaluator rule for `ite` is:

```lean
let r <- eval me opponent b
if r == a then eval me opponent p else eval me opponent q
```

So the first guard evaluated is:

```lean
eval E E (.sim .opp (.bot DefectBot))
```

This asks:

```text
What does my opponent, EBot, do against the literal DefectBot source?
```

In self-play, that returns `D`: EBot defects against DefectBot. The guard tests
for `C`, so:

```lean
D == C  -- false
```

Therefore EBot continues to the else branch, the second `ite`:

```lean
eval E E
  (.ite
    (.sim .opp (.bot CooperateBot))
    C
    (.const C)
    mirrorStage)
```

Now the second guard is evaluated:

```lean
eval E E (.sim .opp (.bot CooperateBot))
```

This asks:

```text
What does my opponent, EBot, do against the literal CooperateBot source?
```

That also returns `D`: EBot exploits CooperateBot. Again the test action is `C`,
so:

```lean
D == C  -- false
```

Therefore evaluation falls through to the mirror stage:

```lean
eval E E
  (.ite
    (.sim .opp (.bot M))
    C
    (.const C)
    (.const D))
```

To choose a branch, the evaluator must run the third guard:

```lean
eval E E (.sim .opp (.bot M))
```

This is the MirrorBot stage.

## Entering the MirrorBot Probe

The evaluator rule for `.sim p q` is:

```lean
let p' := p.subst me opponent
let q' := q.subst me opponent
eval n p' q' p'
```

At the mirror stage:

```lean
me       = E
opponent = E
p        = .opp
q        = .bot M
```

So:

```lean
p' = .opp.subst E E
   = E
```

and:

```lean
q' = (.bot M).subst E E
   = .bot M
```

The second equality is the crucial `.bot` rule:

```lean
| .bot p, _, _ => .bot p
```

Substitution does not descend into `.bot M`.

Therefore:

```lean
eval E E (.sim .opp (.bot M))
```

becomes:

```lean
eval E (.bot M) E
```

So the third guard asks the intended question:

```text
What does EBot do against the literal MirrorBot source?
```

It does not ask what EBot does against some already-substituted expansion of
MirrorBot.

## Why This Matters for MirrorBot

`MirrorBot` is:

```lean
M = .sim .opp .self
```

This source contains placeholders. They should mean:

```lean
.self = MirrorBot
.opp  = MirrorBot's current opponent
```

but only when MirrorBot is actually run.

With `.bot M`, the source is preserved while EBot is deciding which bot to
simulate against. Later, if evaluation reaches the opponent `.bot M`, the
evaluator unwraps it:

```lean
| .bot p => eval n me opponent p
```

At that later point, the current frame is the simulated game:

```lean
EBot vs (.bot MirrorBot)
```

so MirrorBot's `.self` and `.opp` are interpreted in the right frame.

## The Full Path to the Mirror Stage

The call chain is:

```lean
play fuel E E
= eval fuel E E E

-- unfold E
= eval E E (.ite guardDefect C (.const D) rest)

-- guardDefect is (.sim .opp (.bot DefectBot))
-- it returns D, not C
= eval E E rest

-- rest is the second ite
= eval E E (.ite guardCooperate C (.const C) mirrorStage)

-- guardCooperate is (.sim .opp (.bot CooperateBot))
-- it returns D, not C
= eval E E mirrorStage

-- mirrorStage is the third ite
= eval E E (.ite (.sim .opp (.bot M)) C (.const C) (.const D))

-- to choose the branch, eval must run the third guard
= eval E E (.sim .opp (.bot M))

-- sim closes p and q in the current frame
= eval E (.bot M) E
```

That final line is the important one.

With `.bot`, the mirror probe becomes:

```lean
EBot vs (.bot MirrorBot)
```

Without `.bot`, the old mirror probe would have substituted inside `MirrorBot`
too early:

```lean
M.subst E E
= (.sim .opp .self).subst E E
= .sim E E
```

and the probe would have become:

```lean
EBot vs (.sim EBot EBot)
```

That is not the same as `EBot` vs `MirrorBot`. It is MirrorBot's source after
its placeholders have already been captured by the outer `EBot` vs `EBot`
frame.

So `.bot` fixes the issue by delaying substitution inside named bot sources
until those sources are actually evaluated in their own simulated frame.
