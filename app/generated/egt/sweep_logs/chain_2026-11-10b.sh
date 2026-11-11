#!/bin/zsh
# Continuation of chain_2026-11-10.sh, which was stopped in the body8+trolls grid at a CYCLING game (every start
# exhausts its evaluation budget; 1000 starts cost ~17 min). The replicator stage now stops such a game after 100
# starts (basins.CYCLE_PROBE). --resume reuses every run the first chain completed; pass A (t = 1, all stages) is done.
cd "$(dirname "$0")/../../.."  # app/
NF=ess,invasion,faces,replicator,moran
run() { echo "=== $(date '+%H:%M:%S') START $*"; uv run python -u -m pd_runner.egt.pipeline --source sprime --no-render --t-steps 6 --resume "$@"; echo "=== $(date '+%H:%M:%S') END ($?) $*"; }
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
