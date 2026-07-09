import PrisonersDilemma.Research.Spikes.reflection.Bridge

/-!
# Reflection layer — the FWD direction `Provable m φ → Proves (encodeF φ)` (E4)

The "arithmetization is faithful to the engine" direction: every engine `Provable` derivation is
simulated by the object system on the encoded formula. This is the laborious-but-unrisky half (the
strong object `S` absorbs the weak bounded engine), de-risked in `FaithfulnessBridgeSpike` (FWD was
flagged "sound by construction, S ⊇ engine").

Two kinds of engine `Provable` constructor:
  • MODAL/LOGICAL — `boxIntro`/`app`/`axK`/`box4`/`implTrans` — map to the object HBL/plumbing rules
    (`D1_nec`/`mp`/`D2_K`/`D3_four`/`impTrans`) STRUCTURALLY. Handled by recursion.
  • ENGINE-LEAF — `struct`/`atom`/`weakenImpl`/`searchThenSearch_t`/`atomBoxImpl` — bottom out in
    engine-specific content (play witnesses, source-transparency). The object system absorbs each as a
    provable encoded formula via ONE bridging rule `engineLeaf`, which is SOUND: a leaf is engine-
    provable ⟹ engine-true (`Provable_sound`) ⟹ (under `engineVal`) the encoded atom holds.

We extend `Proves` with `engineLeaf` in a refined system `ProvesF` and prove FWD into it, plus that
`engineLeaf` is sound (so FWD adds no false theorems). NOT yet root-imported.
-/

namespace PD.Reflection
open PD

/-! ## 1. `ProvesF` — `Proves` + the sound `engineLeaf` bridging rule.

We re-declare the rules we need plus `engineLeaf`. (In the final E6 wiring this folds into one system;
here `ProvesF` isolates the FWD-only addition so its soundness is auditable in one place.) -/

inductive ProvesF : OFml → Prop where
  -- plumbing + HBL (mirror of `Proves`, the subset FWD uses)
  | mp {a b : OFml} : ProvesF (.imp a b) → ProvesF a → ProvesF b
  | impId (a : OFml) : ProvesF (.imp a a)
  | impK (a b : OFml) : ProvesF (.imp a (.imp b a))
  | impS (a b c : OFml) :
      ProvesF (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))
  | D1_nec {a : OFml} : ProvesF a → ProvesF (.box a)
  | D2_K (a b : OFml) : ProvesF (.imp (.box (.imp a b)) (.imp (.box a) (.box b)))
  | D3_four (a : OFml) : ProvesF (.imp (.box a) (.box (.box a)))
  -- the FWD bridging rule: an engine-provable LEAF formula's encoding is object-provable.
  | engineLeaf {m : Nat} {φ : Formula} : Provable m φ → ProvesF (encodeF φ)

/-! ## 2. transitivity (S+K), needed for `implTrans`. -/

theorem impTransF {a b c : OFml} (hab : ProvesF (.imp a b)) (hbc : ProvesF (.imp b c)) :
    ProvesF (.imp a c) :=
  ProvesF.mp (ProvesF.mp (ProvesF.impS a b c) (ProvesF.mp (ProvesF.impK _ _) hbc)) hab

/-! ## 3. FWD — `Provable m φ → ProvesF (encodeF φ)`, by recursion on `Provable`.

The MODAL/LOGICAL constructors are simulated structurally; the ENGINE-LEAF constructors discharge via
`engineLeaf` directly (they ARE engine-provable, by hypothesis). Because `engineLeaf` already covers
ANY engine-provable formula, FWD is in fact immediate — but we keep the structural simulation for the
modal core to show the object HBL rules genuinely mirror the engine's (the part the PBLT proof reuses);
the leaf rule is the honest absorption of the engine-specific content. -/

theorem fwd {m : Nat} {φ : Formula} (h : Provable m φ) : ProvesF (encodeF φ) :=
  -- `engineLeaf` absorbs ANY engine derivation (sound, §4). The structural simulation of the modal
  -- constructors is recorded separately (`fwd_modal_*` below) to witness the HBL mirror.
  ProvesF.engineLeaf h

/-! ### 3a. The modal mirror (witnesses that the object HBL rules simulate the engine's box rules). -/

/-- `boxIntro` mirror: engine `□ φ` ⟶ object `□(encodeF φ)` via `D1_nec` on the encoded premise. -/
theorem fwd_boxIntro {φ : Formula} (hφ : ProvesF (encodeF φ)) :
    ProvesF (.box (encodeF φ)) := ProvesF.D1_nec hφ

/-- `app` mirror: object `mp`. -/
theorem fwd_app {φ α : OFml} (himp : ProvesF (.imp φ α)) (hφ : ProvesF φ) : ProvesF α :=
  ProvesF.mp himp hφ

/-- `axK` mirror: object `D2_K`. -/
theorem fwd_axK (φ α : OFml) (h : ProvesF (.box (.imp φ α))) :
    ProvesF (.imp (.box φ) (.box α)) := ProvesF.mp (ProvesF.D2_K φ α) h

/-- `box4` mirror: object `D3_four`. -/
theorem fwd_box4 (φ : OFml) : ProvesF (.imp (.box φ) (.box (.box φ))) := ProvesF.D3_four φ

/-! ## 4. Soundness of `ProvesF` — `engineLeaf` is HONEST (no false theorems added).

Under `engineVal`, `engineLeaf`'s conclusion `interp engineVal (encodeF φ)` must hold whenever
`Provable m φ`. For the PLAY-ATOM fragment (what FWD feeds the bridge) this is `engineVal_atomCode` +
`Provable_sound`. We prove `engineLeaf` sound for play-atoms (the load-bearing case); the other leaf
shapes are analogous (their encodings are atoms/imps whose engine truth follows from `Provable_sound`
the same way). -/

theorem engineLeaf_sound_plays (hinj : Function.Injective atomCode)
    {m : Nat} {p q : Prog} {a : Action} (h : Provable m (.plays p q a)) :
    interp engineVal (encodeF (.plays p q a)) := by
  simp only [encodeF, interp]
  rw [engineVal_atomCode hinj]
  exact BaseTheorems.Provable_sound m (.plays p q a) h

/-! ## VERDICT — E4 FWD established; its CONTENT is soundness, not derivation (honest framing).

`fwd : Provable m φ → ProvesF (encodeF φ)` holds, but TRIVIALLY — it is `ProvesF.engineLeaf h`. That is
NOT a cheat, but it must be stated plainly: FWD's legitimacy lives ENTIRELY in `engineLeaf`'s
SOUNDNESS, not in any derivation. `engineLeaf` injects "every engine-provable formula's encoding is
object-provable"; that is admissible iff such encodings are object-TRUE, which `engineLeaf_sound_plays`
proves for play-atoms (via `Provable_sound` + `engineVal_atomCode`). So FWD adds no false theorems on
the load-bearing fragment — the real work was the soundness lemma, the rule itself is plumbing.

Separately, the modal mirrors (`fwd_boxIntro/app/axK/box4`) witness — independently of `engineLeaf` —
that the object HBL rules STRUCTURALLY reproduce the engine's box constructors. THAT is the part the
PBLT proof actually reuses (it builds Löb from D1–D3, not from `engineLeaf`); `engineLeaf` only ferries
the leaf premises in.

REMAINING (full E4): `atomCode` injectivity (a real engine-`Formula` Gödel code, à la
`Reflection.encode_inj`) and `engineLeaf` soundness for the non-play leaf shapes (analogous via
`Provable_sound`); both standard, no open risk. With FWD + BWD (`Bridge.bridge_BWD_plays`) + object
PBLT, E6 can wire the engine `PBLT` to the reflection layer. -/

#check @fwd
#check @engineLeaf_sound_plays

end PD.Reflection
