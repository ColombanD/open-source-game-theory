#!/bin/zsh
# Full re-run of every paper sweep with the FINAL replicator stage of 2026-11-11 (second-order invaders tested
# on tied types below a share of 1e-3, not only below 1e-6). Supersedes chain_2026-11-10{,b}.sh, whose runs are in
# archive/runs_2026-11-10_first_pass. Pass A: t = 1 with every stage for the ladder rungs. Pass B: the grids;
# --resume reuses pass A's t = 1 runs so each rung keeps its Nash components.
cd "$(dirname "$0")/../../.."  # app/
NF=ess,invasion,faces,replicator,moran
run() { echo "=== $(date '+%H:%M:%S') START $*"; uv run python -u -m pd_runner.egt.pipeline --source sprime --no-render "$@"; echo "=== $(date '+%H:%M:%S') END ($?) $*"; }
for Z in nonprovers+dupoc body8+trolls body8+trolls+provers; do
  run --floor-policy engine_side --zoo $Z --family behavioral --ts 1
  run --floor-policy hinge_side  --zoo $Z --family behavioral --ts 1
done
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
