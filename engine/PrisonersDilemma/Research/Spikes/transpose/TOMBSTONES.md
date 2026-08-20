# Tombstones — the transposition spike (promoted 2026-08-20)

All four spikes in this directory did their job and were **deleted**; their content
is now the engine itself. Recorded here so the reasoning survives the files.
History and the audit trail: `README.md` (this directory) and the design entry
"Why `S` is a RULE SET, not an arithmetized theory" in
`Research/Notes/DESIGN_CHOICES.md`.

| spike | what it proved | where it lives now |
|---|---|---|
| `Transpose.lean` | The C/D transposition τ̂ (paper Defs 1.3/1.8/1.11): mutual `Prog.transpose`/`Formula.transpose` with FROZEN `VoteList` entries, involution, EXACT size preservation, `subst`-equivariance, telescope-layer commutation. | `Base/Transpose.lean` (syntax-layer half) |
| `PfTranspose.lean` | Theorem 1.10 at the same budget: `Pf.transpose : Pf k φ → Pf k φ.transpose` — the 47-arm joint induction over the whole mutual block (raw `Pf.rec`, the sanctioned both-motives use-case), plus `Pf.transpose_iff`. | `Base/Transpose.lean` (second half) |
| `RedCell.lean` | The red cell: `transpose_DupocBot`/`rho*_transpose` (Prop 1.12), `not_Pf_dupoc_guard`/`not_Pf_cupod_guard` (the determinism clash), the failed searches and default plays, `outcome_DupocBot_vs_CupodBot = some (.D, .C)` for EVERY `k` (Thm 1.14). | machinery: `Theorems/DupocBot/Helpers.lean` (`-- CupodBot --` section); outcome: `Theorems/DupocBot/vs_CupodBot.lean` |
| `AuditTests.lean` | The 2026-08-19 audit: kernel-`decide` Def-1.11/involution checks, the DIFFERENTIAL TEST (τ maps `dupoc_loeb_premise` ⟷ `cupod_loeb_premise` at the same `5·log2 k + 33`), the `k = 0` edge. | ported as `example`s at the end of `Theorems/DupocBot/vs_CupodBot.lean` |

Downstream effects of the promotion (same landing): the tau/EGT stipulation for
`("CupodBot", "DupocBot")` was deleted from `app/src/pd_runner/tau/matrix.py`
(`CUPOD_STIPULATIONS`) — the loader raises on a stipulation shadowing a proven
cell, so the two changes are atomic — the `critch8` zoo became fully proven, and
the `[[open]]` entry left `app/outcome_status.toml`.
