import PrisonersDilemma.Theorems.PrudentBot.Helpers

/-!
# Spike — can the PrudentBot↔DupocBot leg's box-internalization be built WITHOUT `boxInternalize`?

The leg (`loeb_premise_provable`, PrudentBot.lean) feeds `mutual_loeb`:
  • leg2 : Provable k (□_k φP → φD)         -- a real Derivation (searchBranch), no axiom
  • hfitD : Provable k φD → Provable k φP    -- transformer from the guard inversion (budget k)
`mutual_loeb` internalizes `hfitD` to `□_k φD → □_k φP` (via the `boxInternalize` AXIOM), then
`implTrans` with leg2 ⇒ □_k φD → φD (the PBLT premise).

THE EXPERIMENT: build `Provable k (□_k φD → □_k φP)` (or the whole closed premise `□_k φD → φD`) for
THIS leg using only POSITIVE constructors (`boxIntro` + `weakenImpl` + `implTrans` + the inversion),
WITHOUT `boxInternalize`. Two candidate routes:

  (R1) weakenImpl: if `Provable k (□_k φP)` held OUTRIGHT, `weakenImpl` gives `□φD → □φP` for free.
       But `□_k φP` = `Provable k φP` outright is NOT available here (φP's provability is conditional
       on φD's, which PBLT hasn't established yet). So R1 needs `Provable k φP` unconditionally —
       test whether the inversion gives it.

  (R2) Accept the transformer is essential and confirm the non-positivity returns (negative result).

We test R1: is `Provable k (φP k)` derivable OUTRIGHT at this point (making the box-intro positive)?
-/

namespace PD.PerLegBoxInternalizeSpike
open PD PD.BaseTheorems PD.Theorems

/-- R1 probe: is `Provable k φP` available OUTRIGHT (not via the transformer)? If yes, `boxIntro` +
    `weakenImpl` build `□φD → □φP` with NO `boxInternalize`. The inversion `ps_k_of_play_dupoc` needs
    a real `play n (DupocBot k) (PrudentBot k) = some .C` — i.e. the cooperation must ALREADY hold.
    At `loeb_premise_provable`'s call site that play is NOT yet in hand (PBLT establishes it later).
    So we test: can we get the play, or only conditionally? -/
example (k : Nat) : Provable k (φP k) → True := fun _ => trivial   -- placeholder anchor

/-- The honest test: assume ONLY what `loeb_premise_provable` has in scope (leg2 + the inversion as a
    transformer), and try to build `□_k φD → □_k φP` positively. We try EACH impl-producing
    constructor explicitly (commented attempts = recorded failures), leaving the residual `sorry`. -/
example (k : Nat)
    (hfitD : Provable k (φD k) → Provable k (φP k)) :
    Provable k (.impl (.box k (φD k)) (.box k (φP k))) := by
  -- ATTEMPT weakenImpl φ ψ m : Provable m ψ → m ≤ k → size → Provable k (□φD → □φP) with ψ = □φP.
  --   needs `Provable m (□_k φP)` = `Provable k φP` (via boxIntro) OUTRIGHT. hfitD is conditional.
  --   To discharge we'd need `Provable k φD` to feed hfitD — NOT in hand (it's the box antecedent).
  --   ⇒ blocked.
  -- ATTEMPT implTrans through a cut χ: needs `□φD → χ` and `χ → □φP` both provable. No χ available
  --   that bridges without re-introducing the same conditional. ⇒ blocked.
  -- ATTEMPT struct (Derivation): no Derivation concludes `□φD → □φP` (no box-headed Derivation,
  --   `no_box_headed_deriv`). ⇒ blocked.
  -- ATTEMPT atomBoxImpl / searchThenSearch_t: conclude `.plays`-headed or `□guard→plays`, not
  --   `□→□`. ⇒ don't unify.
  -- Net: every positive constructor is blocked; only `boxInternalize` (the transformer-consuming,
  -- non-positive axiom) produces this. The per-leg case does NOT escape Horn A.
  sorry

/-! ## VERDICT — NEGATIVE, confirmed (2026-06-29).

The per-leg route on the CURRENT engine is BLOCKED the same way the generic one is. Decisive fact
(grep-confirmed in `PrudentBot.lean`): `Provable k φP` is NEVER available OUTRIGHT in this leg — only
as the transformer `hfitD : Provable k φD → Provable k φP`, and `φD`'s provability is what PBLT
establishes LATER. So at `loeb_premise_provable`'s point the cooperation is genuinely CONDITIONAL:
  • `weakenImpl` needs `□_k φP` outright (→ `Provable k φP`) — not available;
  • `implTrans`/`struct`/`atomBoxImpl`/`searchThenSearch_t` don't produce `□φD → □φP` either;
  • only `boxInternalize` (transformer-consuming, NON-POSITIVE) produces it.

⇒ **Per-leg removal does NOT escape Horn A on the abstract engine.** The leg needs to turn a
transformer into an object box-implication, which is irreducibly the non-positive operation. So
`boxInternalize` requires BOTH the full proof-term substrate (to make the transformer a positive
value — Horn A) AND the per-leg guard inversion (to discharge the budget threshold — Horn B = Wall 1).
Neither alone suffices; there is no cheap per-leg shortcut on the current engine. The `sorry` is the
located, irreducible gap (kept as the record; this file is the negative result). -/

end PD.PerLegBoxInternalizeSpike
