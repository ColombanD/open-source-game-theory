import PrisonersDilemma.Reflection.Diagonal
import PrisonersDilemma.Reflection.Bpsb
import PrisonersDilemma.Reflection.Bridge

/-!
# B3 spike: UNIFIED object system `ProvesU` + `Gw` soundness (NO hp0) — dissolving `provesN_play_extract`.

Route 2 (corrected diagnosis): the base-`Proves` `bloeb_object` path with a `Gw`-fixed diagonal, unified
into ONE system `ProvesU` (plumbing + HBL + repr + ctxUnfold + diagFix + engineLeaf), box := `ProvesU`
UNIFORMLY (as `interpN`), diagonal atoms wrapped by `Gw` — but now `Gw` wraps with the SAME `ProvesU`-box
context, so `ctxUnfold`/`diagFix` are sound with NO outcome hypothesis (only structural side-conditions).
If soundness + consistency close here without `hp0`, the extraction obligation is dissolved.
-/

namespace PD.Reflection.BewB3
open PD PD.Reflection

/-! ## 1. `decode` (from B2). -/

open Classical in
noncomputable def decode (n : Nat) : OFml :=
  if h : ∃ φ, encode φ = n then h.choose else .atom 0

theorem decode_encode (φ : OFml) : decode (encode φ) = φ := by
  have hex : ∃ φ', encode φ' = encode φ := ⟨φ, rfl⟩
  rw [decode, dif_pos hex]; exact encode_inj hex.choose_spec

/-! ## 2. `ProvesU p` — UNIFIED system. `ctxUnfold` restricted to betaA bodies (its only use). -/

inductive ProvesU (p : OFml) : OFml → Prop where
  | mp {a b : OFml} : ProvesU p (.imp a b) → ProvesU p a → ProvesU p b
  | impId (a : OFml) : ProvesU p (.imp a a)
  | impK (a b : OFml) : ProvesU p (.imp a (.imp b a))
  | impS (a b c : OFml) : ProvesU p (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))
  | iffIntro {a b : OFml} : ProvesU p (.imp a b) → ProvesU p (.imp b a) → ProvesU p (.iff a b)
  | iffMPF {a b : OFml} : ProvesU p (.iff a b) → ProvesU p (.imp a b)
  | iffMPB {a b : OFml} : ProvesU p (.iff a b) → ProvesU p (.imp b a)
  | D1_nec {a : OFml} : ProvesU p a → ProvesU p (.box a)
  | D2_K (a b : OFml) : ProvesU p (.imp (.box (.imp a b)) (.imp (.box a) (.box b)))
  | D3_four (a : OFml) : ProvesU p (.imp (.box a) (.box (.box a)))
  | gammaAx (n : Nat) : ProvesU p (.gamma n (e n))
  | betaGamma (body : OFml) (y : Nat) :
      ProvesU p (.imp (.gamma (encode body) y) (.iff (.betaA body) (.gApp y)))
  | ctxUnfold (body : OFml) :
      ProvesU p (.iff (.gApp (encode (.betaA body))) (.imp (.box (.betaA body)) p))
  /-- diagFix at the RESERVED fixpoint body `.atom 0` (the only body the chain uses; Engine.lean:60).
      Its `selfApply` = `.atom 0` (plug head-preserving), whose code `0` is in Gw's override domain. -/
  | diagFix : ProvesU p (.iff (.betaA (.atom 0)) (.gApp (encode (.betaA (.atom 0)))))
  | engineLeaf {m : Nat} {φ : Formula} : Provable m φ → ProvesU p (encodeF φ)

/-! ## 3. `Gw` — wraps with the `ProvesU`-box context (so it matches `interpU`'s box). At a betaA code
`c`, `Gw p G0 c := (ProvesU p (decode c) → interp G0 p)` = the context `□(decode c)→p` with box:=ProvesU.
Off betaA codes: `G0`. This is the KEY change vs B2 — the wrapping uses ProvesU, not base Proves. -/

open Classical in
/-- `Gw` overrides at the diagonal's TWO code families: betaA codes `⌜betaA body⌝` AND the reserved
    diagonal-inner code `⌜.atom 0⌝` (= the `selfApply`-image of the fixpoint body `.atom 0`, since
    `plug` is head-preserving ⟹ `selfApply (.atom 0) = .atom 0`). At an override code, denote the
    ProvesU-box context `ProvesU p (decode c) → interp G0 p`; else `G0`. Code `⌜.atom 0⌝ = 0` is DISJOINT
    from any play-atom `p = .atom (atomCode plays…)` since `atomCode(.plays…) ≠ 0` — so `p` stays out. -/
noncomputable def Gw (p : OFml) (G0 : Nat → Prop) (c : Nat) : Prop :=
  if (∃ body, encode (OFml.betaA body) = c) ∨ c = encode (OFml.atom 0)
  then (ProvesU p (decode c) → interp G0 p) else G0 c

/-! ## 4. `interpU` — box := ProvesU p (uniform); diagonal atoms via `Gw`. -/

noncomputable def interpU (p : OFml) (G0 : Nat → Prop) : OFml → Prop
  | .box a  => ProvesU p a
  | .imp a b => interpU p G0 a → interpU p G0 b
  | .iff a b => interpU p G0 a ↔ interpU p G0 b
  | φ        => interp (Gw p G0) φ

@[simp] theorem interpU_box (p G0 a) : interpU p G0 (.box a) = ProvesU p a := rfl
@[simp] theorem interpU_imp (p G0 a b) : interpU p G0 (.imp a b) = (interpU p G0 a → interpU p G0 b) := rfl
@[simp] theorem interpU_iff (p G0 a b) : interpU p G0 (.iff a b) = (interpU p G0 a ↔ interpU p G0 b) := rfl
@[simp] theorem interpU_gApp (p G0 c) : interpU p G0 (.gApp c) = interp (Gw p G0) (.gApp c) := rfl
@[simp] theorem interpU_betaA (p G0 b) : interpU p G0 (.betaA b) = interp (Gw p G0) (.betaA b) := rfl
@[simp] theorem interpU_gamma (p G0 x y) : interpU p G0 (.gamma x y) = (e x = y) := rfl

/-- At a betaA code, `interp (Gw…) (gApp ⌜betaA body⌝)` = the ProvesU-context. -/
theorem interp_gApp_Gw_betaA (p : OFml) (G0 : Nat → Prop) (body : OFml) :
    interp (Gw p G0) (.gApp (encode (.betaA body)))
      = (ProvesU p (.betaA body) → interp G0 p) := by
  show Gw p G0 (encode (OFml.betaA body)) = _
  have hex : (∃ b, encode (OFml.betaA b) = encode (OFml.betaA body))
      ∨ encode (OFml.betaA body) = encode (OFml.atom 0) := Or.inl ⟨body, rfl⟩
  unfold Gw
  split
  · rw [decode_encode]
  · rename_i hcon; exact absurd hex hcon

/-- betaA denotation via Gw + e_graph: `interp (Gw…) (betaA body) = Gw … (e ⌜body⌝)`; and `e ⌜body⌝ =
    ⌜selfApply body⌝`. For the diagonal `diagFix`, `selfApply body`'s betaA-ness must align. -/
theorem interp_betaA_Gw (p : OFml) (G0 : Nat → Prop) (body : OFml) :
    interp (Gw p G0) (.betaA body) = Gw p G0 (e (encode body)) := rfl

/-! ## 5. SOUNDNESS at `interpU` — NO hp0. -/

theorem provesU_sound (p : OFml) (G0 : Nat → Prop)
    (hpp : interp (Gw p G0) p = interp G0 p)      -- p gApp-free: Gw agrees with G0 on p (STRUCTURAL)
    (hpb : interpU p G0 p = interp (Gw p G0) p)    -- p box-free (play-atom): interpU = interp
    (hp0 : interp G0 p)                            -- ← the OUTCOME, needed ONLY by diagFix (see VERDICT)
    (hEL : ∀ {m : Nat} {φ : Formula}, Provable m φ → interpU p G0 (encodeF φ))
    {φ : OFml} (h : ProvesU p φ) : interpU p G0 φ := by
  induction h with
  | mp _ _ ihab iha => exact ihab iha
  | impId a => intro ha; exact ha
  | impK a b => intro ha _; exact ha
  | impS a b c => intro habc hab ha; exact (habc ha) (hab ha)
  | iffIntro _ _ ihab ihba => exact ⟨ihab, ihba⟩
  | iffMPF _ ih => exact ih.mp
  | iffMPB _ ih => exact ih.mpr
  | D1_nec hb ih => exact hb                       -- interpU (box a) = ProvesU p a; = the premise
  | D2_K a b => intro hab ha; exact ProvesU.mp hab ha
  | D3_four a => intro ha; exact ProvesU.D1_nec ha
  | gammaAx n => show e n = e n; rfl
  | betaGamma body y =>
      intro hg
      have hg' : e (encode body) = y := hg
      show interpU p G0 (.betaA body) ↔ interpU p G0 (.gApp y)
      simp only [interpU_betaA, interpU_gApp, interp]
      show Gw p G0 (e (encode body)) ↔ Gw p G0 y
      rw [hg']
  | ctxUnfold body =>
      -- LHS = interp (Gw) (gApp ⌜βbody⌝) = (ProvesU p (βbody) → interp G0 p)  [interp_gApp_Gw_betaA]
      -- RHS = interpU (box βbody) → interpU p = ProvesU p (βbody) → interpU p
      show interpU p G0 (.gApp (encode (.betaA body)))
          ↔ (interpU p G0 (.box (.betaA body)) → interpU p G0 p)
      rw [interpU_gApp, interpU_box, interp_gApp_Gw_betaA, hpb, hpp]
  | diagFix =>
      -- betaA (.atom 0) ↔ gApp ⌜betaA (.atom 0)⌝.
      -- LHS = Gw (e ⌜.atom 0⌝) = Gw ⌜.atom 0⌝ [selfApply(.atom 0)=.atom 0] = ProvesU p (.atom 0) → interp G0 p.
      -- RHS = ProvesU p (betaA (.atom 0)) → interp G0 p  [interp_gApp_Gw_betaA].
      -- ANTECEDENTS DIFFER: ProvesU p (.atom 0) vs ProvesU p (betaA (.atom 0)). The iff holds because
      -- interp G0 p (the OUTCOME, hp0) makes both `_ → interp G0 p` True. So diagFix ALONE needs hp0.
      show interpU p G0 (.betaA (.atom 0)) ↔ interpU p G0 (.gApp (encode (.betaA (.atom 0))))
      rw [interpU_betaA, interpU_gApp, interp_betaA_Gw, e_graph, interp_gApp_Gw_betaA]
      -- (B4 UPDATE: `selfApply` has since been redefined to `selfApply θ := betaA θ`, so
      -- `e ⌜.atom 0⌝ = ⌜betaA (.atom 0)⌝` — a betaA code. The antecedent MISMATCH this arm documented
      -- (the reason hp0 was needed) is GONE: both sides now denote the SAME context, and the arm
      -- closes WITHOUT hp0 — exactly the B4 fix. hp0 stays in the signature as a historical record.)
      have hsa : selfApply (OFml.atom 0) = OFml.betaA (OFml.atom 0) := rfl
      rw [hsa]
      have hex : (∃ b, encode (OFml.betaA b) = encode (OFml.betaA (OFml.atom 0)))
          ∨ encode (OFml.betaA (OFml.atom 0)) = encode (OFml.atom 0) := Or.inl ⟨OFml.atom 0, rfl⟩
      have hlhs : Gw p G0 (encode (OFml.betaA (OFml.atom 0)))
          = (ProvesU p (OFml.betaA (OFml.atom 0)) → interp G0 p) := by
        unfold Gw
        split
        · rw [decode_encode]
        · rename_i hcon; exact absurd hex hcon
      rw [hlhs]
  | engineLeaf hpr => exact hEL hpr

#check @provesU_sound

/-! ## VERDICT — B3: `ctxUnfold` dissolves (NO hp0), but `diagFix` STILL needs the outcome. HONEST.

The `ProvesU` unified system + `interpU` (box := ProvesU uniform) + the ProvesU-box-wrapping `Gw` makes
the diagonal `ctxUnfold` arm — which carried `hp0` via `Gctx` — SOUND with only STRUCTURAL conditions
(`hpp`/`hpb`, `p` gApp/box-free), NO outcome. That is real progress: HALF the diagonal's outcome-
dependence is gone.

BUT `diagFix` (the fixpoint `betaA ⌜body⌝ ↔ gApp ⌜betaA body⌝`) STILL needs `hp0 : interp G0 p`. Reason
(machine-exposed here): its two sides denote `ProvesU p (.atom 0) → interp p` (LHS, via
selfApply=.atom 0) and `ProvesU p (betaA (.atom 0)) → interp p` (RHS); the ANTECEDENTS differ
(`.atom 0` vs `betaA (.atom 0)`), so the iff holds only when `interp p` makes both consequents True —
i.e. the OUTCOME. This is the SAME `hp0` the old `diagFix_sound` used.

⇒ CORRECTED SCOPE: constructed-`Bew` (re-denoting `gApp`) removes the outcome-dependence from the
CONTEXT-representability (`ctxUnfold`), NOT from the DIAGONAL FIXPOINT (`diagFix`). The residual
`hp0` lives in `diagFix` — the self-reference, not the context. So `provesN_play_extract` is REDUCED
(ctxUnfold no longer contributes) but NOT fully dissolved: the fixpoint's soundness still reads the
outcome. Whether Critch's construction avoids this (his β/diagonal via a DIFFERENT representability that
makes diagFix definitional too) is the next question — see B3-followup. This is the honest boundary of
what constructed-`Bew` buys: it fixes the context, not the fixpoint. -/

end PD.Reflection.BewB3
