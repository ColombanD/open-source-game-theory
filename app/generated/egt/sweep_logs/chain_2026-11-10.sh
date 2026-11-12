#!/bin/zsh
# Re-run of every paper sweep after (a) the CupodBot x OBot correction of 2026-11-05 (the cell is the theorem
# (D, D)), (b) the Nash-component fix (bipartite graph instead of the midpoint test) and (c) the replicator
# rewrite (LSODA on log-shares, Nash convergence test at two times, metastable flag) of 2026-11-10.
# The runs on disk before this chain are in archive/runs_2026-10-22_pre_replicator_fix.
# Same stages per sweep as chain_2026-10-19.sh: body8 with Nash on both floor sides and both distance families;
# ladder rungs and natives Nash-free on the grid, with Nash at t = 1 (pass A, reused by pass B through --resume,
# so the t = 1 run of each rung carries its Nash components and the component-matched basins).
cd "$(dirname "$0")/../../.."  # app/
NF=ess,invasion,faces,replicator,moran
run() { echo "=== $(date '+%H:%M:%S') START $*"; uv run python -m pd_runner.egt.pipeline --source sprime --no-render "$@"; echo "=== $(date '+%H:%M:%S') END ($?) $*"; }
# pass A: t = 1 with every stage, for the zoo-ladder table
for Z in nonprovers+dupoc body8+trolls body8+trolls+provers; do
  run --floor-policy engine_side --zoo $Z --family behavioral --ts 1
  run --floor-policy hinge_side  --zoo $Z --family behavioral --ts 1
done
# pass B: the grids
run --t-steps 6 --resume --floor-policy engine_side --zoo body8 --family behavioral
run --t-steps 6 --resume --floor-policy engine_side --zoo body8 --family syntactic
run --t-steps 6 --resume --floor-policy hinge_side  --zoo body8 --family behavioral
run --t-steps 6 --resume --floor-policy hinge_side  --zoo body8 --family syntactic
run --ts 1      --resume --floor-policy hinge_side  --zoo body8 --family epsilon
for Z in nonprovers+dupoc body8+trolls body8+trolls+provers; do
  run --t-steps 6 --resume --floor-policy engine_side --zoo $Z --family behavioral --stages $NF
  run --t-steps 6 --resume --floor-policy hinge_side  --zoo $Z --family behavioral --stages $NF
done
for F in behavioral syntactic epsilon; do
  run --t-steps 6 --resume --floor-policy engine_side --zoo body8+natives --family $F --stages $NF
done
echo "=== $(date '+%H:%M:%S') CHAIN DONE"
