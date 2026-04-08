# DBot Flow Tutorial

This note explains the DBot vs CooperateBot proof flow using the pipeline-native theorem shape.

## Pipeline Matchup Through `ActionClaim`

```lean
theorem dbot_vs_cooperate_actionClaim :
    ActionClaim Bot.dBot Bot.cooperateBot D C := by
  unfold ActionClaim playActions
  change (evalSource Bot.dBot (source Bot.cooperateBot), evalSource Bot.cooperateBot (source Bot.dBot)) = (D, C)
  simp [evalSource, source, dBotAction, dBotStrategy, actionFor, evalActionExpr]
```

### What `ActionClaim` means

`ActionClaim left right aL aR` means:

```lean
playActions left right = (aL, aR)
```

So this theorem means:

- left bot (`dBot`) plays `D`
- right bot (`cooperateBot`) plays `C`

### Step-by-step pipeline flow

Start goal:

```lean
ActionClaim Bot.dBot Bot.cooperateBot D C
```

After:

```lean
unfold ActionClaim playActions
```

the goal is:

```lean
(ProgramModel.action Bot.dBot Bot.cooperateBot,
 ProgramModel.action Bot.cooperateBot Bot.dBot) = (D, C)
```

Then `change` rewrites the same goal into model-level functions:

```lean
(evalSource Bot.dBot (source Bot.cooperateBot),
 evalSource Bot.cooperateBot (source Bot.dBot)) = (D, C)
```

Now compute each component.

#### First component (left side): `dBot` against `cooperateBot`

```lean
evalSource Bot.dBot (source Bot.cooperateBot)
=> evalSource Bot.dBot cooperateSource
=> dBotAction cooperateSource
=> actionFor dBotStrategy cooperateSource
=> evalActionExpr dBotStrategy cooperateSource.tag
=> evalActionExpr dBotStrategy SourceTag.cooperateTag
=> D
```

#### Second component (right side): `cooperateBot` against `dBot`

```lean
evalSource Bot.cooperateBot (source Bot.dBot)
=> evalSource Bot.cooperateBot dBotSource
=> actionFor cooperateStrategy dBotSource
=> evalActionExpr cooperateStrategy dBotSource.tag
=> evalActionExpr (ActionExpr.actionLit C) SourceTag.defectTag
=> C
```

So the pair is `(D, C)`, exactly the target.

### Common pitfall (the one you ran into)

It is easy to accidentally write:

```lean
ProgramModel.actionFromSource Bot.cooperateBot (ProgramModel.source Bot.dBot) = D
```

but this is false. It should be `= C`, because `cooperateStrategy` is `ActionExpr.actionLit C`, which always evaluates to `C`.

### Why `unfold`, `change`, and `simp` are all used

- `unfold`: opens high-level wrappers (`ActionClaim`, `playActions`) so you can see the real goal.
- `change`: rewrites the goal into an equivalent but easier-to-simplify shape.
- `simp`: executes definitional computation and rewriting until both sides match.