# DBot Flow Tutorial

This note explains the exact reduction flow behind the theorem

```lean
theorem dbot_vs_cooperate_actions :
    (dBotAction cooperateSource, C) = (D, C) := by
  simp [dBotAction, dBotStrategy, actionFor, evalActionExpr]
```

The goal is simple: show that DBot plays `D` against a cooperating opponent, so the final pair is `(D, C)`.

## The Key Idea

`dBotAction` does not directly return an action literal. It runs a small strategy expression through the DSL.

In this case, the strategy says:

- if the opponent is tagged as `cooperateTag`, play `D`
- otherwise, play `C`

## Reduction Flow

Starting from the left side of the theorem:

```lean
dBotAction cooperateSource
```

the definition unfolds as follows:

```lean
dBotAction cooperateSource
```

becomes

```lean
actionFor dBotStrategy cooperateSource
```

because `dBotAction` is defined using `actionFor`.

Then `actionFor` unfolds to:

```lean
evalActionExpr dBotStrategy cooperateSource.tag
```

and since `cooperateSource.tag = SourceTag.cooperateTag`, this becomes:

```lean
evalActionExpr dBotStrategy SourceTag.cooperateTag
```

Now unfold `dBotStrategy`:

```lean
ActionExpr.ifOppIs SourceTag.cooperateTag
  (ActionExpr.actionLit D)
  (ActionExpr.actionLit C)
```

So the evaluator checks whether the opponent tag matches `cooperateTag`.

Because the tag is exactly `cooperateTag`, the first branch is taken.

That reduces the expression to:

```lean
evalActionExpr (ActionExpr.actionLit D) SourceTag.cooperateTag
```

Finally, evaluating an action literal just returns that action:

```lean
D
```

So the whole theorem reduces to:

```lean
(D, C) = (D, C)
```

which is exactly what `simp` proves.

## Compact Summary

The full computation is:

```lean
dBotAction cooperateSource
=> actionFor dBotStrategy cooperateSource
=> evalActionExpr dBotStrategy cooperateSource.tag
=> evalActionExpr dBotStrategy SourceTag.cooperateTag
=> D
```

So DBot defects against `cooperateSource`, while the opponent cooperates.

## What `simp` Is Doing

The proof uses:

```lean
simp [dBotAction, dBotStrategy, actionFor, evalActionExpr]
```

This tells Lean to unfold the named definitions and simplify the resulting expression until both sides match.

In other words, this is a computation proof, not a long logical argument.