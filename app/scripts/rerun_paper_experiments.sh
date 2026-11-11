#!/usr/bin/env bash
# Re-run every sweep behind the paper's experiments section, then rebuild the results snapshot.
#
#   app/scripts/rerun_paper_experiments.sh [OUT] [RESULTS]
#
# OUT      where the sweep output goes (default: app/generated, whose run folders are gitignored)
# RESULTS  where the snapshot goes (default: app/paper_results, the tracked folder)
#
# Input: the Lean export app/generated/sprime_outcome_theorems.json. About an hour on a four-core laptop. Afterwards
# `git diff app/paper_results` should be empty, and `uv run pytest tests/test_paper_numbers.py` checks the
# snapshot against the numbers the paper states. REPRODUCING.md at the repository root has the context.
set -euo pipefail
APP="$(cd "$(dirname "$0")/.." && pwd)"
OUT="${1:-$APP/generated}"
RESULTS="${2:-$APP/paper_results}"
mkdir -p "$OUT/egt_fine/logs" "$RESULTS"
OUT="$(cd "$OUT" && pwd)"
RESULTS="$(cd "$RESULTS" && pwd)"
cd "$APP"

sweep() {   # equilibria (Nash stage) and replicator dynamics of every distinct game of a grid
  uv run python -u -m pd_runner.egt.pipeline --source sprime --no-render --stages ess,nash,replicator "$@"
}

echo "== full transparency: the four libraries on the negative side of the hinge, Sigma on the positive side"
for LIBRARY in nonprovers+dupoc body8 body8+trolls body8+trolls+provers; do
  sweep --zoo "$LIBRARY" --family behavioral --floor-policy engine_side --ts 1 --alphas 1 --out-root "$OUT/egt"
done
sweep --zoo body8 --family behavioral --floor-policy hinge_side --ts 1 --alphas 1 --out-root "$OUT/egt"

echo "== partial transparency: Sigma, transparency 0, 0.01, ..., 1, both signal families, both sides of the hinge"
TS="$(uv run python -c "print(','.join(f'{i / 100:.2f}' for i in range(100, -1, -1)))")"
PIDS=()
for FAMILY in behavioral syntactic; do
  for SIDE in engine_side hinge_side; do
    sweep --zoo body8 --family "$FAMILY" --floor-policy "$SIDE" --ts "$TS" --alphas 0.5,0.6,0.7,0.8,0.9,1 \
      --out-root "$OUT/egt_fine/${FAMILY}_${SIDE}" > "$OUT/egt_fine/logs/${FAMILY}_${SIDE}.log" 2>&1 &
    PIDS+=($!)
  done
done
for PID in "${PIDS[@]}"; do wait "$PID"; done

echo "== partial transparency: the three low caution levels, negative side"
PIDS=()
for FAMILY in behavioral syntactic; do
  sweep --resume --zoo body8 --family "$FAMILY" --floor-policy engine_side --ts "$TS" --alphas 0,0.2,0.4 \
    --out-root "$OUT/egt_fine/${FAMILY}_engine_side" > "$OUT/egt_fine/logs/${FAMILY}_engine_side_low_caution.log" 2>&1 &
  PIDS+=($!)
done
for PID in "${PIDS[@]}"; do wait "$PID"; done

echo "== snapshot"
uv run python -m pd_runner.paper.snapshot --from "$OUT" --out "$RESULTS"
echo "== done: uv run python -m pd_runner.paper.numbers"
