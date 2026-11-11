#!/bin/zsh
# Fine-grid partial-transparency sweeps on body8 (t step 0.01, the paper's six caution levels), both distance
# families and both sides of the hinge; Nash + replicator only. Separate out-root so the paper's coarse-grid
# runs in generated/egt/runs keep their one-directory-per-(zoo, t=1) layout. 2026-11-11.
cd "$(dirname "$0")/../.."  # app/
TS=$(python3 -c "print(','.join(f'{i/100:.2f}' for i in range(100,-1,-1)))")
for F in behavioral syntactic; do for P in engine_side hinge_side; do
  ( uv run python -u -m pd_runner.egt.pipeline --source sprime --no-render --zoo body8 --family $F --floor-policy $P \
      --ts $TS --alphas 0.5,0.6,0.7,0.8,0.9,1 --stages ess,nash,replicator --out-root generated/egt_fine/${F}_${P} \
      > generated/egt_fine/logs/${F}_${P}.log 2>&1; echo "END $? $F $P" ) &
done; done
wait
echo "ALL DONE"
