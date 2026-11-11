#!/bin/zsh
# The three low caution levels of the paper's grid (alpha = 0, 0.2, 0.4) on the fine t grid, floor side, both
# families; --resume adds their grid points to the runs of run_fine.sh that share a matrix. 2026-11-11.
cd "$(dirname "$0")/../.."  # app/
TS=$(python3 -c "print(','.join(f'{i/100:.2f}' for i in range(100,-1,-1)))")
for F in behavioral syntactic; do
  ( uv run python -u -m pd_runner.egt.pipeline --source sprime --no-render --resume --zoo body8 --family $F --floor-policy engine_side \
      --ts $TS --alphas 0,0.2,0.4 --stages ess,nash,replicator --out-root generated/egt_fine/${F}_engine_side \
      > generated/egt_fine/logs/${F}_engine_side_low_alpha.log 2>&1; echo "END $? $F" ) &
done
wait; echo "ALL DONE"
