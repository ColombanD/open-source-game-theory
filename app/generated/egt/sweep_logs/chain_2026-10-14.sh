#!/bin/zsh
# Partial-transparency sweeps missing for the paper (2026-10-14), engine side, S'.
# Ladder rungs Nash-free (replicator + Moran are what the transparency ladder reads);
# natives on both body families, Nash-free (Nash on natives was 20-30 min/matrix).
cd /Users/colomband/wt/osgt-arith-m3/app
NF=ess,invasion,faces,replicator,moran
run() { echo "=== $(date '+%H:%M:%S') START $*"; uv run python -m pd_runner.egt.pipeline --source sprime --floor-policy engine_side --t-steps 6 --resume --no-render "$@"; echo "=== $(date '+%H:%M:%S') END ($?) $*"; }
run --zoo nonprovers+dupoc     --family behavioral --stages $NF
run --zoo body8+trolls         --family behavioral --stages $NF
run --zoo body8+trolls+provers --family behavioral --stages $NF
run --zoo body8+natives        --family behavioral --stages $NF
run --zoo body8+natives        --family syntactic  --stages $NF
echo "=== $(date '+%H:%M:%S') CHAIN DONE"
