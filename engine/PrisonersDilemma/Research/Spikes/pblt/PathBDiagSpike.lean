import PrisonersDilemma.Theorems.DupocBot

/-!
# PBLT Path B spike — can the bot's OWN self-search supply the diagonal fixpoint?

GOAL: eliminate `PBLT` for the DupocBot self-play family WITHOUT a Gödel encoding, by exploiting that
DupocBot's `.search` guard IS the self-reference Critch's diagonal lemma constructs.

The fixpoint. `DupocBot k = .search k (.plays .opp .self C) (.const C) (.const D)`: it plays C iff it
can prove "opp plays C vs me". For self-play `φ k := (DupocBot k plays C vs DupocBot k)`, the guard
substitutes to `□_k φ`. So OPERATIONALLY:
    DupocBot k plays C   ↔   proofSearch k φ = true   ↔   Provable k φ          (the search rule)
i.e. `φ` (the play) ↔ `□_k φ` (its provability). That is Löb's fixpoint `ψ ↔ □ψ`, PHYSICALLY PRESENT
as the bot, not built by a diagonal lemma. The question: does that let us close PBLT here?

WHAT PBLT GIVES HERE (from `DupocBot_vs_DupocBot`):  `∃m, Provable m (□φ → φ)`  ⟹  `∃m, Provable m φ`.
We have the premise `dupoc_loeb_premise` (a real `searchBranch` derivation). We want `Provable k φ`.

This file PROBES whether the bot structure closes that gap directly (Path B viable) or whether it is
exactly the irreducible Löb step (Path B fails → Path A / encoding required). NOT root-imported.
-/

namespace PD.PathBDiagSpike
open PD PD.BaseTheorems PD.Theorems PD.Bots

/-- φ k = the DupocBot self-cooperation atom. -/
def φ (k : Nat) : Formula := .plays (DupocBot k) (DupocBot k) .C

/-! ## Step 1 — the OPERATIONAL fixpoint: `Provable k φ ↔ DupocBot plays C` (machine fact).

This is the bot's search rule, both directions, at a single budget `k`. If we can establish it, it is
the concrete `ψ ↔ □ψ` Critch builds abstractly. -/

/-- **The bot IS the fixpoint** (machine-checked): DupocBot self-play reduces to its own guard,
    `play (n+2) = if proofSearch k φ then C else D`. So `φ (plays C) ⟺ proofSearch k φ ⟺ Provable k φ`.
    Both branches are internally consistent — `eval` does NOT force C — which is exactly why Löb is
    needed to break the symmetry. (This is the FairBot fixpoint `ψ ↔ □ψ`, physically present.) -/
theorem dupoc_self_eval (k n : Nat) :
    play (n + 2) (DupocBot k) (DupocBot k) =
      (if proofSearch k (.plays (DupocBot k) (DupocBot k) .C) then some .C else some .D) := by
  show eval (n + 2) (DupocBot k) (DupocBot k) (DupocBot k) = _
  unfold DupocBot; simp [eval, Prog.subst, Formula.subst]

/-- Forward: if `DupocBot` self-plays C, the guard fired, so `proofSearch k φ = true` = `Provable k φ`. -/
theorem prov_of_play (k n : Nat) (h : play (n + 2) (DupocBot k) (DupocBot k) = some .C) :
    Provable k (φ k) := by
  have he := dupoc_self_eval k n
  rw [he] at h
  cases hps : proofSearch k (.plays (DupocBot k) (DupocBot k) .C) with
  | true  => exact (proofSearch_spec _ _).1 hps
  | false => rw [hps] at h; simp at h

/-- Backward: if `Provable k φ` then the guard fires, so `DupocBot` self-plays C — hence `φ.interp`.
    (This is just `Provable_sound` composed with the search rule; the EASY direction.) -/
theorem play_of_prov (k : Nat) (h : Provable k (φ k)) :
    ∃ n, play n (DupocBot k) (DupocBot k) = some .C := by
  -- `Provable k φ` → `φ.interp` (Provable_sound) → `∃n, play n = some C`. Direct.
  exact Provable_sound k (φ k) h

/-! ## Step 2 — the CRUX: does the fixpoint + the Löb premise give `Provable k φ` outright?

We have:
  • `legLoeb : Provable k (□_k φ → φ)`        (dupoc_loeb_premise — a real searchBranch derivation)
  • the operational fixpoint (Step 1).
We want: `Provable k φ`. THIS is the Löb step. Probe whether the bot structure closes it. -/

theorem dupoc_self_provable (k : Nat) (hk : k ≥ 1)
    (legLoeb : Provable k (.impl (.box k (φ k)) (φ k))) :
    Provable k (φ k) := by
  -- To use `legLoeb` via `app` we need `Provable k (□_k φ)`. The ONLY way to build `□_k φ` is
  -- `boxIntro`, which needs `Provable k φ` — the very goal. CIRCULAR (the Löb knot).
  --   have hboxφ : Provable k (.box k (φ k)) := Provable.boxIntro k k (φ k) ?GOAL …   -- needs the goal
  --   exact Provable.app k k _ _ legLoeb hboxφ (le_refl k)
  -- DupocBot's fixpoint is `φ ↔ □φ` (FairBot), available only as a PLAY/proofSearch equivalence
  -- (`dupoc_self_eval`), NOT as a `Provable` of a biconditional we can cut against. The classical
  -- Löb proof breaks the knot with a DIFFERENT sentence `ψ` (`ψ ↔ (□ψ → φ)`, the diagonal) — which
  -- DupocBot does NOT supply (it is `ψ↔□ψ`, not `ψ↔(□ψ→φ)`). No bot-structural route avoids
  -- constructing that ψ. So the knot does not close here:
  sorry

/-! ## VERDICT — Path B FAILS (decisive, machine-grounded). Path A (encoding) is required.

PROVEN sorry-free (the bot structure we DO get):
  • `dupoc_self_eval` — DupocBot self-play `= if proofSearch k φ then C else D`. The bot literally
    returns "C iff φ is provable": the FairBot fixpoint `φ ↔ □φ`, physically present.
  • `prov_of_play` / `play_of_prov` — both directions of `Provable k φ ↔ DupocBot plays C`.

BLOCKED (`dupoc_self_provable`, the crux): from `legLoeb : Provable k (□φ → φ)` we cannot reach
`Provable k φ`. Using `legLoeb` via `app` needs `Provable k (□φ)`; the only producer is `boxIntro`,
which needs `Provable k φ` — the goal. CIRCULAR (the Löb knot).

WHY THE BOT DOESN'T BREAK THE KNOT. Classical/bounded Löb breaks the circularity with a DIFFERENT
sentence — the diagonal `ψ` with `⊢ ψ ↔ (□ψ → φ)` — then necessitate + K + 4. DupocBot supplies a
fixpoint, but the WRONG one: it is `ψ ↔ □ψ` (FairBot), available only as a play/proofSearch
equivalence (`dupoc_self_eval`), NOT as a `Provable` of a biconditional, and NOT the `ψ ↔ (□ψ → φ)`
shape the proof needs. There is no bot-structural way to manufacture that `ψ`: the bot's self-search
is over `□φ` directly, never over `□ψ → φ` for a fresh `ψ`.

**So Path B does not bypass the Parametric Diagonal Lemma — it relocates the need for it.** The bot
gives the fixpoint's TRUTH (`φ ↔ □φ`) but not the diagonal SENTENCE inside `Provable`, which is
exactly the object the diagonal lemma constructs and `Formula` cannot encode. Eliminating `PBLT`
therefore requires Path A: extend the syntax with the means to form `ψ ↔ (□ψ → φ)` (a Gödel encoding
/ self-reference), then run Critch §5 over it (the chain `pblt_of_bpsb` already proves, given `diag`).

Net: cheap spike, clear answer — Path B is closed; the diagonal lemma is irreducible without
encoding. Next step for PBLT removal is Path A's first sub-step: the diagonal lemma over a minimal
encoded syntax. -/

end PD.PathBDiagSpike
