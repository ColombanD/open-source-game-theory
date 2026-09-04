# The transposition spike — the red cell certified ✅ PROMOTED 2026-08-20

Mechanization of `latex/Cupod_vs_Dupco_proof.tex` (the C/D-transposition proof of
`outcome(Dupoc(k), Cupod(k)) = (D, C)`), written 2026-08-19, audited same day,
**promoted into the engine 2026-08-20**. The `.lean` files are deleted per the
spike-retirement convention — see `TOMBSTONES.md` for the file-by-file map. Promoted
homes:

* `Base/Transpose.lean` — τ̂ (Defs 1.3/1.8/1.11), involution, EXACT size
  preservation, `subst`-equivariance, telescope commutation, and **Thm 1.10**:
  `Pf.transpose : Pf k φ → Pf k φ.transpose` at the SAME budget (47-arm joint
  induction over the mutual block, raw `Pf.rec` — the sanctioned use-case).
* `Theorems/DupocBot/Helpers.lean` (`-- CupodBot --` section) — Prop 1.12, the
  determinism clash (`not_Pf_dupoc_guard`), failed searches, default plays.
* `Theorems/DupocBot/vs_CupodBot.lean` — **Thm 1.14**,
  `outcome_DupocBot_vs_CupodBot = some (.D, .C)` for EVERY `k`, plus the ported
  audit examples (differential test, `decide` checks, the `k = 0` edge).

This closed **the red cell**: `(CupodBot, DupocBot)`, the one matchup
Critch–Dennis–Russell 2022 leave open, which the tau/EGT layer had stipulated.
The stipulation is deleted (`app/src/pd_runner/tau/matrix.py`), the `critch8`
zoo is fully proven, and the `[[open]]` entry left `app/outcome_status.toml`.
Design rationale: the "Why `S` is a RULE SET" entry in
`Research/Notes/DESIGN_CHOICES.md`.

Everything below is the spike's original record, kept for the audit trail.

---

## How the paper's hypotheses fared in the engine

Every hypothesis the paper had to *assume* is either exact or a theorem here:

* **"τ is an automorphism of S" (Def 1.9).** In the engine, `S` is presented as
  a constructor-closed rule set (`Pf`, 30 rules), so the hypothesis becomes a
  finite closure check — the 47-arm induction. Every rule transposes. The
  paper's worry about axiomatizing `C ≠ D` symmetrically (the
  `⊢_k φ ⇒ ⊢_{k+c} φ^τ` slack) does not arise: the engine's disequality
  suppliers (`eqNeg`, `atomNeg`) take `p ≠ q` as a *side condition*, which
  transposes by injectivity of τ̂ at zero cost.
* **"Equal encoding length" (Thm 1.10's length clause).** Exact, not assumed:
  `Action.C`/`Action.D` are same-size constants and τ̂ touches nothing else
  (`size_transpose`), so every transcript keeps its budget — the same-`k`
  biconditional with **no `+c` splice**.
* **"τ-equivariant Gödel encoding" (Prop 1.12).** The engine's quotation is
  structural (formulas carry programs), so equivariance is commutation with
  `subst` (`subst_transpose`) — proved, not assumed.
* **"S is sound for the relevant statements" (Thm 1.14).** A theorem
  (`Pf_sound`), since the 2026-07-03 zero-axiom repair.
* **Def 1.11 (`Cupod = τ̂(Dupoc)`).** Holds definitionally — `rfl` type-checks
  (verified during the audit).

Two mechanization findings worth keeping:

1. **The paper's final "unexploitability of Dupoc" step is redundant.** Once
   `P` (the common truth value of `□_k ρ₁`/`□_k ρ₂`) is false, both bots fall
   through to their defaults directly — `(D, C)` needs no case exclusion. The
   mechanized Thm 1.14 is shorter than the paper's.
2. **One genuine τ-asymmetry exists in the extended engine language:** the
   tau-layer `.tvote` primitive thresholds on *C*-mass specifically, so τ̂ must
   **freeze `VoteList` entries** (exactly as `subst` already does) — descending
   would flip votes and kill `Pf`-invariance at the `voteCons_*` arms. On the
   paper's fragment (everything Dupoc/Cupod contain) τ̂ is the full literal
   source transposition. This freeze is the one place the mechanization had to
   make a choice the paper's language doesn't face.

## Contrast with the floor/exclusion route

The library's existing same-`k` negative results (e.g.
`outcome_PrudentBot_vs_PrudentBot = (D, D)`) go through the transparency census
+ cost-floor machinery of `Base/Exclusion` — hundreds of lines of telescope
case analysis per matchup. The transposition argument replaces ALL of that for
symmetric pairs: `¬ ⊢_k ρ₁` falls out of `⊢_k ρ₁ ⟺ ⊢_k ρ₂` (τ-closure) + soundness +
determinism of `eval`, never mentioning costs.

Scope, stated precisely (audit 2026-08-19): the mechanized lemma is
`¬ Pf k ρ₁` at the bots' own shared parameter `k` — which by `Pf_mono` also
kills every budget `K ≤ k`, i.e. everything the two `.search` guards can ever
consult. It says NOTHING about `K > k` (a `(D, C)` outcome needs nothing
there), and the whole symmetry inherently requires the two bots to carry the
SAME parameter: at staggered parameters `Dupoc(k₁)` vs `Cupod(k₂)`, τ̂ maps the
matchup to a DIFFERENT matchup and no self-clash arises — those cells remain
open, exactly like the library's staggered-cooperation phenomena
(`outcome_PrudentBot_vs_DupocBot`). Consequently the negative half is robust
to ANY τ-symmetric extension of `S`: it uses only soundness + τ-closure, never
the constructor list — the compiler forces a transposition arm for every new
`Pf` constructor, which is the right failure mode.

## Audit summary (2026-08-19)

* Axiom footprint: outcome theorems `[propext, Classical.choice, Quot.sound]`;
  `Pf.transpose` `[propext]` alone. Zero sorries.
* Kernel-`decide` checks: τ̂ non-trivial, involutive, Def 1.11 literal.
* **Differential test**: `Pf.transpose` maps the two INDEPENDENTLY hand-proven
  Löb premises (`dupoc_loeb_premise` ⟷ `cupod_loeb_premise`) onto each other
  at the same `5·log2 k + 33` transcript, both directions — two unrelated
  proof routes converging. Ported to `Theorems/DupocBot/vs_CupodBot.lean`.
* Library-wide sweep: no conflicting claims about either guard formula;
  `outcome_status.toml` had the cell open for "no forcing rule" — the
  τ-automorphism IS the new forcing rule.
* One defect found and fixed: an earlier draft of this README overclaimed
  unprovability at `K > k` (see the scope paragraph above for the honest
  statement).
