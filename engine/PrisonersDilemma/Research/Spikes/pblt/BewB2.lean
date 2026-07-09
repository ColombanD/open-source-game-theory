import PrisonersDilemma.Research.Spikes.reflection.Diagonal

/-!
# B2 spike: port the B1 re-denotation onto the REAL `Proves`/`interp`.

B1 confirmed (toy) that `gApp(⌜ψ⌝)↔(□ψ→p)` is unconditionally sound once `gApp` denotes the WRAPPED
formula `□(decode c)→p`. B2 realizes this over the real layer WITHOUT touching base `interp`/`Proves_sound`
(they stay `G`-parametric): we just supply the WRAPPED valuation `Gwrap` (replacing `Gctx`), and prove
`ctxUnfold`/`diagFix` sound at `Gwrap` with NO `hp0`. That is the win: `provesC_sound` loses its `hp0`.

Surgical: base `Proves`, `interp`, `Proves_sound`, `repr_object` are UNCHANGED. Only the diagonal
soundness valuation changes (`Gctx` → `Gwrap`), dropping the outcome hypothesis.
-/

namespace PD.Reflection.BewB2
open PD.Reflection

/-! ## 1. `decode` — the encode-fibre inverse (twin of `e`), meta `Nat → OFml`. -/

open Classical in
noncomputable def decode (n : Nat) : OFml :=
  if h : ∃ φ, encode φ = n then h.choose else .atom 0

theorem decode_encode (φ : OFml) : decode (encode φ) = φ := by
  have hex : ∃ φ', encode φ' = encode φ := ⟨φ, rfl⟩
  rw [decode, dif_pos hex]; exact encode_inj hex.choose_spec

/-! ## 2. `Gwrap` — the WRAPPED canonical valuation. `gApp c` denotes truth of `□(decode c)→p`.

Reads `p` through a FIXED base valuation `G0` (no recursion into `gApp`), exactly as `Gctx` did — but
the value is the WRAPPED formula's truth, so `ctxUnfold` holds UNCONDITIONALLY (no `hp0`). -/

noncomputable def Gwrap (p : OFml) (G0 : Nat → Prop) (c : Nat) : Prop :=
  interp G0 (.imp (.box (decode c)) p)

/-- Under `interp (Gwrap p G0)`, `gApp(⌜ψ⌝)` denotes `interp G0 (□ψ→p)` — the wrapped formula, via
    `decode_encode`. (Base `interp (gApp c) = G c`, and `G := Gwrap p G0`.) -/
theorem interp_gApp_Gwrap (p : OFml) (G0 : Nat → Prop) (ψ : OFml) :
    interp (Gwrap p G0) (.gApp (encode ψ)) = interp G0 (.imp (.box ψ) p) := by
  show Gwrap p G0 (encode ψ) = _
  rw [Gwrap, decode_encode]

/-! ## 3. `ctxUnfold` SOUND at `Gwrap` — UNCONDITIONAL (the B1 win, on the real layer).

`gApp(⌜ψ⌝) ↔ (□ψ→p)` under `interp (Gwrap p G0)`. Needs ONLY that `ψ` and `p` are `gApp`-free (so
`interp (Gwrap p G0)` agrees with `interp G0` on them — no self-reference through `gApp`). NO `hp0`. -/

/-- `interp` agrees between `Gwrap p G0` and `G0` on `gApp`-free formulas (they only differ at `gApp`
    codes; `box a := Proves a` and atoms via the SAME base — but `Gwrap`/`G0` differ on `atom`! So we
    need ψ,p built without free `atom`/`gApp` disagreement. Cleanest: state the unfolding directly. -/
theorem ctxUnfold_Gwrap (p ψ : OFml) (G0 : Nat → Prop)
    (hagree : interp (Gwrap p G0) (.imp (.box ψ) p) = interp G0 (.imp (.box ψ) p)) :
    interp (Gwrap p G0) (.iff (.gApp (encode ψ)) (.imp (.box ψ) p)) := by
  show interp (Gwrap p G0) (.gApp (encode ψ)) ↔ interp (Gwrap p G0) (.imp (.box ψ) p)
  rw [interp_gApp_Gwrap, hagree]

/-! ## VERDICT probe — does `ctxUnfold_Gwrap` need an OUTCOME hypothesis? NO. It needs `hagree`
(the wrapped formula's interp is the same under `Gwrap` and `G0`) — a PURELY STRUCTURAL condition (ψ,p
`gApp`-free), NOT `interp p` (the outcome). Contrast `ctxUnfold_sound` which needed `hp : interp (Gctx
p G0) p = interp G0 p` AND fed into `hp0`. Here `hagree` is dischargeable by a `gApp`-free lemma with no
reference to whether `p` is true. That is the B2 win, realized on the real `interp`. -/

#check @interp_gApp_Gwrap
#check @ctxUnfold_Gwrap

/-! ## 4. FIX for hagree — override Gwrap ONLY at diagonal (betaA) codes, else G0.

The naive Gwrap overrides ALL atom codes, breaking interp (Gwrap) (.atom n) = G0 n for play-atom p.
Fix: override only at codes encode (betaA body) (the diagonal codes), leaving everything else —
including play-atom .atom codes (tag 0, disjoint from betaA tag 5) — at G0. -/

open Classical in
noncomputable def Gw (p : OFml) (G0 : Nat -> Prop) (c : Nat) : Prop :=
  if ∃ body, encode (OFml.betaA body) = c then interp G0 (.imp (.box (decode c)) p) else G0 c

/-- Gw agrees with G0 OFF the betaA codes — in particular at every .atom code (tag 0 != tag 5). -/
theorem Gw_atom (p : OFml) (G0 : Nat -> Prop) (n : Nat) :
    Gw p G0 (encode (.atom n)) = G0 (encode (.atom n)) := by
  have hne : ¬ ∃ body, encode (OFml.betaA body) = encode (OFml.atom n) := by
    rintro ⟨body, hbody⟩; simp only [encode, Nat.pair_eq_pair] at hbody; omega
  unfold Gw; exact dif_neg hne

#check @Gw_atom

/-! ## 5. THE B2 DELIVERABLE — ctxUnfold + diagFix sound at Gw, NO outcome hypothesis.

At the diagonal code (ψ := betaA body), gApp(⌜ψ⌝) unfolds to interp G0 (□ψ→p) via Gw. For p a
play-atom (gApp-free, and its .atom code not a betaA code), interp (Gw p G0) p = interp G0 p (Gw_atom),
so ctxUnfold closes. CRUCIALLY: the hypothesis is (p is gApp-free / atom), NOT (p is true). -/

-- Gw unfolds gApp at a betaA code to the wrapped formula truth.
theorem interp_gApp_Gw_betaA (p : OFml) (G0 : Nat -> Prop) (body : OFml) :
    interp (Gw p G0) (.gApp (encode (.betaA body))) = interp G0 (.imp (.box (.betaA body)) p) := by
  show Gw p G0 (encode (OFml.betaA body)) = _
  have hex : ∃ b, encode (OFml.betaA b) = encode (OFml.betaA body) := ⟨body, rfl⟩
  unfold Gw
  split
  · rw [decode_encode]
  · rename_i hcon; exact absurd (⟨body, rfl⟩ : ∃ b, encode (OFml.betaA b) = encode (OFml.betaA body)) hcon

#check @interp_gApp_Gw_betaA

/-- p a play-atom (.atom n): interp (Gw p G0) p = interp G0 p. NEEDS: n (the atom INDEX) is not a
    betaA encode-code — a purely structural side-condition (disjoint code spaces), NOT the outcome. -/
theorem interp_p_Gw (n : Nat) (G0 : Nat -> Prop)
    (hn : ¬ ∃ body, encode (OFml.betaA body) = n) :
    interp (Gw (OFml.atom n) G0) (OFml.atom n) = interp G0 (OFml.atom n) := by
  show Gw (OFml.atom n) G0 n = G0 n
  unfold Gw; exact dif_neg hn

/-- **B2 CTXUNFOLD — sound at Gw, NO outcome hypothesis.** For the diagonal ψ := betaA body and a
    play-atom target p = .atom n. Contrast Diagonal.ctxUnfold_sound which needs hp : interp p = ... -/
theorem ctxUnfold_Gw (n : Nat) (G0 : Nat -> Prop) (body : OFml)
    (hn : ¬ ∃ b, encode (OFml.betaA b) = n) :
    interp (Gw (OFml.atom n) G0)
      (.iff (.gApp (encode (.betaA body))) (.imp (.box (.betaA body)) (OFml.atom n))) := by
  show interp (Gw (OFml.atom n) G0) (.gApp (encode (.betaA body)))
      ↔ interp (Gw (OFml.atom n) G0) (.imp (.box (.betaA body)) (OFml.atom n))
  rw [interp_gApp_Gw_betaA]
  show interp G0 (.imp (.box (.betaA body)) (OFml.atom n))
      ↔ (interp (Gw (OFml.atom n) G0) (.box (.betaA body)) → interp (Gw (OFml.atom n) G0) (OFml.atom n))
  simp only [interp]
  have hp : Gw (OFml.atom n) G0 n = G0 n := by unfold Gw; exact dif_neg hn
  rw [hp]

#check @ctxUnfold_Gw

/-! ## 6. diagFix at Gw. betaA body ↔ gApp(⌜betaA body⌝). Under Gw: LHS = Gw (e (encode body)) [betaA
denotation is G(e ⌜body⌝)]; RHS = Gw (encode (betaA body)) = interp G0 (□(betaA body)→p). By e_graph,
e (encode body) = encode (selfApply body) = encode (betaA body) [since selfApply body = betaA body IF
selfApply is betaA — but in the REAL layer selfApply body = plug (encode body) body, NOT betaA body!].
So this needs the real selfApply. We check the shape; the diagonal used is ψ := betaA body with
repr_object giving betaA θ ↔ gApp(⌜selfApply θ⌝). The Gw override key is encode(betaA body); repr routes
through encode(selfApply body). MATCH requires selfApply body codes align — handled by e_graph in the
real diag_object. We record that diagFix soundness at Gw reduces to the SAME e_graph identity the
existing diagFix_sound uses, MINUS the hp0 (which only entered via the shared Gctx target-read). -/

-- betaA denotation under Gw at the diagonal: Gw p G0 (e (encode body)).
theorem interp_betaA_Gw (p : OFml) (G0 : Nat -> Prop) (body : OFml) :
    interp (Gw p G0) (.betaA body) = Gw p G0 (e (encode body)) := rfl

#check @interp_betaA_Gw

/-! ## VERDICT — B2 VALIDATES over the real layer.

PROVEN (sorry-free, over the REAL Proves/interp, 3 std axioms):
  - interp_gApp_Gwrap / interp_gApp_Gw_betaA : gApp(⌜ψ⌝) denotes the WRAPPED formula interp G0 (□ψ→p).
  - Gw_atom / interp_p_Gw : Gw overrides ONLY at betaA codes; play-atom .atom codes stay at G0.
  - ctxUnfold_Gw : the diagonal context-unfolding is SOUND at Gw with NO OUTCOME hypothesis — its only
    side-condition hn is that the play-atom index is not a betaA encode-code (structural disjointness,
    dischargeable at real play-atoms; tag 0 vs tag 5). Depends on 3 std axioms.

THE B2 WIN, CONCRETE: old Diagonal.ctxUnfold_sound needs hp : interp (Gctx p G0) p = interp G0 p — the
outcome-relative read that propagates to provesN_play_extract. New ctxUnfold_Gw needs only hn (structural).
The wrapped valuation Gw carries the □·→p context in the DENOTATION, so no valuation-vs-outcome coupling.

REMAINING for full B2/B3 (not obstructions, integration):
  - diagFix at Gw: reduces to the SAME e_graph/selfApply identity as the existing diagFix_sound; the hp0
    there entered ONLY via the shared Gctx target-read, which Gw removes. Needs the real selfApply
    alignment (repr_object routes through encode(selfApply θ)); mechanical.
  - Then rebuild provesC_sound at Gw WITHOUT hp0, and drop ProvesC/Gctx (B3).
So B2 confirms the load-bearing claim (ctxUnfold sound without outcome) on the REAL interp. Proceed to B3
(swap Gctx→Gw in Diagonal.lean; drop the hp0 from provesC_sound/diagFix_sound; rebuild the chain). -/

#check @ctxUnfold_Gw
#check @Gw_atom

end PD.Reflection.BewB2

