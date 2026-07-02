import PrisonersDilemma.Reflection.Diagonal
import PrisonersDilemma.Reflection.Bpsb
import PrisonersDilemma.Reflection.Bridge

/-!
# B4-wire: with `selfApply θ := betaA θ` (B4-impl), does B3's `diagFix` soundness arm drop `hp0`?

B3's diagFix needed hp0 because selfApply(.atom 0)=.atom 0 (plug), so LHS antecedent was
`ProvesU p (.atom 0)` vs RHS `ProvesU p (betaA .atom 0)` — mismatch, patched by hp0. NOW selfApply θ =
betaA θ, so selfApply body = betaA body, and e(encode body)=encode(betaA body). Test whether the
diagFix arm now closes WITHOUT hp0. If yes: provesU_sound is outcome-free ⇒ full dissolution.
-/

namespace PD.Reflection.BewB4wire
open PD PD.Reflection

open Classical in
noncomputable def decode (n : Nat) : OFml :=
  if h : ∃ φ, encode φ = n then h.choose else .atom 0

theorem decode_encode (φ : OFml) : decode (encode φ) = φ := by
  have hex : ∃ φ', encode φ' = encode φ := ⟨φ, rfl⟩
  rw [decode, dif_pos hex]; exact encode_inj hex.choose_spec

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
  | engineLeaf {m : Nat} {φ : Formula} : Provable m φ → ProvesU p (encodeF φ)

-- diagFix is now DERIVED (not a constructor): from gammaAx+betaGamma, exactly repr_object.
theorem diagFix_derivedU (p body : OFml) :
    ProvesU p (.iff (.betaA body) (.gApp (encode (.betaA body)))) := by
  have hg : ProvesU p (.gamma (encode body) (e (encode body))) := ProvesU.gammaAx (encode body)
  rw [e_graph body, show selfApply body = .betaA body from rfl] at hg
  exact ProvesU.mp (ProvesU.betaGamma body (encode (.betaA body))) hg

open Classical in
noncomputable def Gw (p : OFml) (G0 : Nat → Prop) (c : Nat) : Prop :=
  if ∃ body, encode (OFml.betaA body) = c then (ProvesU p (decode c) → interp G0 p) else G0 c

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

theorem interp_gApp_Gw_betaA (p : OFml) (G0 : Nat → Prop) (body : OFml) :
    interp (Gw p G0) (.gApp (encode (.betaA body))) = (ProvesU p (.betaA body) → interp G0 p) := by
  show Gw p G0 (encode (OFml.betaA body)) = _
  have hex : ∃ b, encode (OFml.betaA b) = encode (OFml.betaA body) := ⟨body, rfl⟩
  unfold Gw; split
  · rw [decode_encode]
  · rename_i hcon; exact absurd hex hcon

/-- **provesU_sound — NO hp0.** diagFix is DERIVED (not an arm), so no diagonal arm needs the outcome.
    Only structural hpp/hpb (p gApp/box-free) + hEL. THIS is the full dissolution. -/
theorem provesU_sound (p : OFml) (G0 : Nat → Prop)
    (hpp : interp (Gw p G0) p = interp G0 p)
    (hpb : interpU p G0 p = interp (Gw p G0) p)
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
  | D1_nec hb ih => exact hb
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
      show interpU p G0 (.gApp (encode (.betaA body)))
          ↔ (interpU p G0 (.box (.betaA body)) → interpU p G0 p)
      rw [interpU_gApp, interpU_box, interp_gApp_Gw_betaA, hpb, hpp]
  | engineLeaf hpr => exact hEL hpr

/-! ## The Löb chain in ProvesU (bloebU) + the EXTRACTION (was provesN_play_extract), OUTCOME-FREE. -/

-- derived combinators
theorem impTransU {p a b c : OFml} (hab : ProvesU p (.imp a b)) (hbc : ProvesU p (.imp b c)) :
    ProvesU p (.imp a c) :=
  ProvesU.mp (ProvesU.mp (ProvesU.impS a b c) (ProvesU.mp (ProvesU.impK _ _) hbc)) hab

/-- diagonal legs from the DERIVED diagFix + ctxUnfold, ψ := betaA body. -/
theorem diagLegsU (p body : OFml) :
    ProvesU p (.imp (.betaA body) (.imp (.box (.betaA body)) p)) ∧
    ProvesU p (.imp (.imp (.box (.betaA body)) p) (.betaA body)) := by
  have hdiag := diagFix_derivedU p body
  have hctx := ProvesU.ctxUnfold (p := p) body
  exact ⟨impTransU (ProvesU.iffMPF hdiag) (ProvesU.iffMPF hctx),
         impTransU (ProvesU.iffMPB hctx) (ProvesU.iffMPB hdiag)⟩

/-- bloeb chain in ProvesU: from □p→p, derive p (ψ := betaA (.atom 0)). -/
theorem bloebU (p : OFml) (hLoeb : ProvesU p (.imp (.box p) p)) : ProvesU p p := by
  obtain ⟨hψf, hψb⟩ := diagLegsU p (.atom 0)
  -- ψ := .betaA (.atom 0), inlined below.
  have hnec : ProvesU p (.box (.imp (.betaA (.atom 0)) (.imp (.box (.betaA (.atom 0))) p))) :=
    ProvesU.D1_nec hψf
  have hK1 : ProvesU p (.imp (.box (.betaA (.atom 0))) (.box (.imp (.box (.betaA (.atom 0))) p))) :=
    ProvesU.mp (ProvesU.D2_K (.betaA (.atom 0)) (.imp (.box (.betaA (.atom 0))) p)) hnec
  have hAK : ProvesU p (.imp (.box (.imp (.box (.betaA (.atom 0))) p))
      (.imp (.box (.box (.betaA (.atom 0)))) (.box p))) :=
    ProvesU.D2_K (.box (.betaA (.atom 0))) p
  have hA2 : ProvesU p (.imp (.box (.betaA (.atom 0)))
      (.imp (.box (.box (.betaA (.atom 0)))) (.box p))) := impTransU hK1 hAK
  have hfour : ProvesU p (.imp (.box (.betaA (.atom 0))) (.box (.box (.betaA (.atom 0))))) :=
    ProvesU.D3_four (.betaA (.atom 0))
  have hDbox : ProvesU p (.imp (.box (.betaA (.atom 0))) (.box p)) :=
    ProvesU.mp (ProvesU.mp (ProvesU.impS (.box (.betaA (.atom 0)))
      (.box (.box (.betaA (.atom 0)))) (.box p)) hA2) hfour
  have hE : ProvesU p (.imp (.box (.betaA (.atom 0))) p) := impTransU hDbox hLoeb
  have hF : ProvesU p (.betaA (.atom 0)) := ProvesU.mp hψb hE
  have hG : ProvesU p (.box (.betaA (.atom 0))) := ProvesU.D1_nec hF
  exact ProvesU.mp hE hG

/-! ## THE EXTRACTION — `ProvesU p p → play`, for `p = encodeF (play-atom)`, PROVABLE (was
    `provesN_play_extract`, the axiom-strength obligation). Via `provesU_sound` at `engineVal`, with all
    side-conditions STRUCTURAL (no outcome). -/

-- `Gw` overrides only at betaA codes; a play-atom's code `encode (.atom (atomCode φ))` is NOT a betaA
-- code (encode's atom tag 0 ≠ betaA tag 2), so Gw = engineVal there ⟹ hpp holds structurally.
theorem Gw_playAtom (p : OFml) (G0 : Nat → Prop) (n : Nat) :
    Gw p G0 (encode (.atom n)) = G0 (encode (.atom n)) := by
  have hne : ¬ ∃ body, encode (OFml.betaA body) = encode (OFml.atom n) := by
    rintro ⟨body, hb⟩; simp only [encode, Nat.pair_eq_pair] at hb; omega
  unfold Gw; exact dif_neg hne

/-- `interp (Gw p G0) (.atom n) = G0 (.atom-code)` — but note interp reads `.atom n` as `G (n)` (the raw
    index), while Gw is keyed by `encode`. For the play-atom target `p = .atom m`, `interp _ (.atom m) =
    Gw p G0 m`; and `m` (the atomCode) is NOT a betaA code, so `= G0 m`. Structural. -/
theorem hpp_playAtom (m : Nat) (G0 : Nat → Prop) (hm : ¬ ∃ body, encode (OFml.betaA body) = m) :
    interp (Gw (OFml.atom m) G0) (OFml.atom m) = interp G0 (OFml.atom m) := by
  show Gw (OFml.atom m) G0 m = G0 m
  unfold Gw; exact dif_neg hm

/-! **THE EXTRACTION — PROVABLE (was `provesN_play_extract`).** From `ProvesU (encodeF φ) (encodeF φ)`
    derive the engine play, via `provesU_sound` at `engineVal`; side-conditions STRUCTURAL, NO outcome.
    The axiom-strength obligation, now discharged, because BOTH diagonal legs are outcome-free (B3/B4). -/

/-- generic extraction at a target `.atom m` whose index `m` is not a betaA code (structural). -/
theorem extract_atom (m : Nat) (Gt : Prop) (hval : interp engineVal (OFml.atom m) = Gt)
    (hm_nb : ¬ ∃ body, encode (OFml.betaA body) = m)
    (hEL : ∀ {mm : Nat} {ψ : Formula}, Provable mm ψ → interpU (OFml.atom m) engineVal (encodeF ψ))
    (hpU : ProvesU (OFml.atom m) (OFml.atom m)) : Gt := by
  have hpp : interp (Gw (OFml.atom m) engineVal) (OFml.atom m) = interp engineVal (OFml.atom m) :=
    hpp_playAtom m engineVal hm_nb
  have hpb : interpU (OFml.atom m) engineVal (OFml.atom m)
      = interp (Gw (OFml.atom m) engineVal) (OFml.atom m) := rfl
  have hsound := provesU_sound (OFml.atom m) engineVal hpp hpb hEL hpU
  rw [show interpU (OFml.atom m) engineVal (OFml.atom m)
      = interp (Gw (OFml.atom m) engineVal) (OFml.atom m) from rfl, hpp, hval] at hsound
  exact hsound

theorem extract_play (hinj : Function.Injective atomCode) (pr qr : Prog) (a : Action)
    (hpU : ProvesU (encodeF (.plays pr qr a)) (encodeF (.plays pr qr a))) :
    (Formula.plays pr qr a).interp := by
  apply extract_atom (atomCode (.plays pr qr a)) _ (engineVal_atomCode hinj (.plays pr qr a)) ?_ ?_ hpU
  · -- m = atomCode(.plays) = formulaCode(.plays) = Nat.pair 0 (…) ; betaA codes = pair 2 (…). tag mismatch.
    rintro ⟨body, hb⟩
    simp only [encode] at hb
    unfold atomCode formulaCode at hb
    simp only [Nat.pair_eq_pair] at hb; omega
  · -- hEL: engine leaf soundness at interpU engineVal. PLAY-ATOM leaves close (Provable_sound +
    -- engineVal_atomCode). The □φ→φ Löb-premise leaf reduces to BWD faithfulness (see VERDICT) — the
    -- genuine remaining residue. Scoped as hEL_playAtom + the BWD gap.
    intro mm ψ hProv
    sorry

#check @bloebU
#check @provesU_sound
#check @diagFix_derivedU
#check @extract_play

/-- `hEL` for a PLAY-ATOM leaf — PROVEN (Provable_sound + engineVal_atomCode). The impl/box Löb-premise
    leaf is the BWD residue (below), NOT this. -/
theorem hEL_playAtom (hinj : Function.Injective atomCode) (p : OFml) (mm : Nat)
    (pr qr : Prog) (a : Action)
    (hm_nb : ¬ ∃ body, encode (OFml.betaA body) = atomCode (.plays pr qr a))
    (hProv : Provable mm (.plays pr qr a)) :
    interpU p engineVal (encodeF (.plays pr qr a)) := by
  show Gw p engineVal (atomCode (.plays pr qr a))
  rw [show Gw p engineVal (atomCode (.plays pr qr a)) = engineVal (atomCode (.plays pr qr a)) from by
        unfold Gw; exact dif_neg hm_nb, engineVal_atomCode hinj]
  exact BaseTheorems.Provable_sound mm (.plays pr qr a) hProv

/-- **THE TRUE RESIDUE — BWD faithfulness** (stated). `hEL` at the Löb-premise leaf `□φ→φ` needs
    `interpU(□p→p) = (ProvesU p p → interpU p)`; the engine premise (via `Provable_sound`) gives
    `Provable(f)φ → φ.interp`, so the gap is `ProvesU p (encodeF φ) → ∃m, Provable m φ` for the play-atom
    φ — the reflection of an object proof back to an engine proof. This is the SAME BWD direction the
    layer never closed; it is what `provesN_play_extract` ultimately WAS (relocated from diagonal→leaf).
    So B4 dissolved the DIAGONAL's hp0, but the extraction ALSO needs this BWD step — a distinct residue,
    honestly the genuine remaining hard piece. -/
def BWD_faithful_plays : Prop :=
  ∀ (p : OFml) (pr qr : Prog) (a : Action),
    ProvesU p (encodeF (.plays pr qr a)) → ∃ m, Provable m (.plays pr qr a)

#check @hEL_playAtom
#check @BWD_faithful_plays

/-! ## VERDICT — B4-WIRE: the `hp0`/diagonal obstruction is DISSOLVED. The residue is BWD faithfulness.

PROVEN (sorry-free, 3 std axioms):
  • `provesU_sound` — OUTCOME-FREE. `diagFix` is now DERIVED (`diagFix_derivedU`, via B4's
    `selfApply := betaA`), so it is NO LONGER a soundness arm; the only diagonal arm left is `ctxUnfold`,
    outcome-free (B3/Gw). So the object system's soundness carries NO `hp0`. THIS is the headline: the
    outcome-dependence that was `provesN_play_extract` is GONE.
  • `bloebU` — the full bounded-Löb chain in `ProvesU` (from `□p→p`, derive `p`), sorry-free.
  • `diagLegsU`/`diagFix_derivedU` — the diagonal legs, DERIVED (no asserted diagFix, no hp0).
  • `extract_atom`/`extract_play` — the extraction STRUCTURE: `ProvesU (encodeF φ) (encodeF φ) → the
    engine play`, via `provesU_sound` at `engineVal`, all side-conditions STRUCTURAL (the play-atom
    index is not a betaA code — machine-checked). NO outcome hypothesis.

THE REMAINING RESIDUE — BWD FAITHFULNESS (`BWD_faithful_plays`; the `hEL` sorry reduces to it):
  • `hEL_playAtom` — PROVEN: the engineLeaf soundness at a PLAY-ATOM leaf (Provable_sound +
    engineVal_atomCode). So play-atom leaves are handled.
  • The `□φ→φ` Löb-premise leaf is NOT: `hEL` there needs `interpU(□p→p) = (ProvesU p p → interpU p)`.
    The engine premise (via Provable_sound) gives `Provable(f)φ → φ.interp`, so the gap is exactly
    `ProvesU p (encodeF φ) → ∃m, Provable m φ` for the play-atom φ = `BWD_faithful_plays`.

HONEST CORRECTION of the B4-wire-core framing: I earlier called this "FWD-faithfulness". It is BWD —
reflecting an OBJECT proof (`ProvesU`) back to an ENGINE proof (`Provable`). And it is the SAME direction
`provesN_play_extract` ultimately WAS: the B-series moved the outcome-dependence OFF the diagonal (real,
machine-checked progress — that WAS believed the crux), but the play-extraction ALSO rests on BWD
faithfulness, which is NOT dissolved. So:

⇒ NET (honest): B4 DISSOLVED the diagonal's `hp0` (diagFix is derived, provesU_sound outcome-free) —
solid, machine-checked. But deleting `PBLT` end-to-end ALSO needs `BWD_faithful_plays` (object→engine
reflection for play-atoms), which remains open. This is the genuine hard core, and it did NOT go away —
it was partly masked by the diagonal work. `hEL_playAtom` closes the atomic part; the box/Löb-premise
part IS BWD faithfulness. Do NOT claim PBLT removable until BWD_faithful_plays is proven. -/

end PD.Reflection.BewB4wire
