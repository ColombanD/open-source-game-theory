#!/bin/zsh
# Re-run of every paper sweep on the NEW caution grid α ∈ {0, 0.2, 0.4, 0.5, 0.6, 0.8, 1} (DEFAULT_ALPHAS,
# 2026-10-19; was {0, 0.3, 0.45, 0.62, 0.8, 1}). Same stages per sweep as the runs on disk:
# body8 with Nash on both floor sides and both distance families; ladder rungs and natives Nash-free.
cd /Users/colomband/wt/osgt-arith-m3/app
NF=ess,invasion,faces,replicator,moran
run() { echo "=== $(date '+%H:%M:%S') START $*"; uv run python -m pd_runner.egt.pipeline --source sprime --t-steps 6 --resume --no-render "$@"; echo "=== $(date '+%H:%M:%S') END ($?) $*"; }
run --floor-policy engine_side --zoo body8 --family behavioral
run --floor-policy engine_side --zoo body8 --family syntactic
run --floor-policy hinge_side  --zoo body8 --family behavioral
run --floor-policy hinge_side  --zoo body8 --family syntactic
for Z in nonprovers+dupoc body8+trolls body8+trolls+provers; do
  run --floor-policy engine_side --zoo $Z --family behavioral --stages $NF
  run --floor-policy hinge_side  --zoo $Z --family behavioral --stages $NF
done
for F in behavioral syntactic epsilon; do
  run --floor-policy engine_side --zoo body8+natives --family $F --stages $NF
done
echo "=== $(date '+%H:%M:%S') CHAIN DONE"
