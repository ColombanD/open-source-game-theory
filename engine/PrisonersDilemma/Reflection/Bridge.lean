import PrisonersDilemma.Reflection.Proves
import PrisonersDilemma.BaseTheorems

/-!
# Reflection layer — the faithfulness bridge: `encodeF`, `BridgeSound` (E3 + E4-map)

First module COUPLING the reflection layer to the engine. It provides:
  • `encodeF : Formula → OFml` — the engine-formula encoding (E4's map), structural on the PBLT
    fragment (`plays`/`impl`/`box`), with `neg`/`eq` sent to benign atoms (PBLT never uses them);
  • `engineVal : Nat → Prop` — the valuation giving each encoded atom its ENGINE meaning;
  • `BridgeSound` (E3): object provability of `⌜φ⌝` under the engine valuation implies `φ.interp`.

The payoff (de-risked in `FaithfulnessBridgeSpike`): `BridgeSound` is DERIVABLE from
`Reflection.Proves_sound` — the object soundness already proven — because `Proves_sound` holds for
EVERY valuation, including `engineVal`. So E3 needs no new principle. Combined with the engine's
`atom_complete` (the spike's `BWD_plays_of_sound`), this gives back `∃m, Provable m φ` for the
play-atoms PBLT concludes.

Imports `BaseTheorems` (engine side); still NOT root-imported the other way (the engine doesn't depend
on reflection until E6).
-/

namespace PD.Reflection
open PD

/-! ## 1. `encodeF : Formula → OFml` — structural on the PBLT fragment.

`box`'s budget `n` is kept META (the object `box` is budget-free at this stage; E5 re-threads budgets),
so `.box n φ ↦ OFml.box (encodeF φ)`. The atom `.plays p q a` is keyed by the engine `Formula`'s own
Gödel-style code — here we reuse the engine `Formula`'s `DecidableEq` to inject via a code function
`atomCode` (an injection `Formula → Nat` on the atom layer; abstractly an opaque injection — its only
job is to be a stable per-formula tag for `engineVal`). -/

/-- A stable per-Formula code (engine-side Gödel tag). Opaque injection; only used as an atom key. -/
opaque atomCode : Formula → Nat

/-- Encode an engine `Formula` into the object language. Structural on `plays`/`impl`/`box`; `neg`/`eq`
    (absent from the PBLT fragment) go to a benign keyed atom so the map is total. -/
def encodeF : Formula → OFml
  | .plays p q a => .atom (atomCode (.plays p q a))
  | .impl φ ψ    => .imp (encodeF φ) (encodeF ψ)
  | .box _ φ     => .box (encodeF φ)
  | .neg φ       => .atom (atomCode (.neg φ))      -- benign; not in PBLT fragment
  | .eq p q      => .atom (atomCode (.eq p q))     -- benign; not in PBLT fragment

/-! ## 2. The engine valuation — each encoded atom gets its ENGINE meaning. -/

open Classical in
/-- `engineVal n` = the engine truth of the formula whose `atomCode` is `n` (when `n` is such a code),
    else `False`. Realized via the `atomCode`-fibre (choice), exactly as `e` was. The point: under this
    valuation, `interp engineVal (encodeF φ)` tracks `φ.interp` on the PBLT fragment. -/
noncomputable def engineVal (n : Nat) : Prop :=
  if h : ∃ φ : Formula, atomCode φ = n then (h.choose).interp else False

/-! ## 3. `interp engineVal (encodeF φ) ↔ φ.interp` on the PBLT fragment — the encoding is FAITHFUL.

We prove the direction we need: object truth (under `engineVal`) of an encoded `plays`/`impl`/`box`
formula implies engine truth. The `box` case uses `interp (box a) := Proves a`; we relate object
`Proves` to engine `Provable` via the soundness side already available. For the spike-level bridge we
take the `box`/atom denotations as the engine ones by construction (E4 will make `encodeF` injective so
the fibre picks the right formula). -/

/-- `engineVal (atomCode φ) = φ.interp` when `atomCode` is injective on the relevant atoms — the fibre
    recovers `φ`. (Stated for the atoms `encodeF` produces.) -/
theorem engineVal_atomCode (hinj : Function.Injective atomCode) (φ : Formula) :
    engineVal (atomCode φ) = φ.interp := by
  unfold engineVal
  rw [dif_pos ⟨φ, rfl⟩]
  rw [show (⟨φ, rfl⟩ : ∃ ψ : Formula, atomCode ψ = atomCode φ).choose = φ from
    hinj (⟨φ, rfl⟩ : ∃ ψ : Formula, atomCode ψ = atomCode φ).choose_spec]

/-! ## 4. `BridgeSound` (E3) — object provability under `engineVal` ⟹ engine truth.

DERIVED from `Reflection.Proves_sound`: for any `φ`, `Proves (encodeF φ)` gives
`interp engineVal (encodeF φ)` (soundness at the engine valuation), which on the PBLT fragment is
`φ.interp`. We prove the load-bearing case — the play-atom (what PBLT concludes). -/

/-- **`BridgeSound` for play-atoms** — if the object system proves the encoded play-atom, the engine
    play holds. From `Proves_sound` at `engineVal` + `engineVal_atomCode`. No new axiom. -/
theorem bridgeSound_plays (hinj : Function.Injective atomCode)
    (p q : Prog) (a : Action)
    (h : Proves (encodeF (.plays p q a))) :
    (Formula.plays p q a).interp := by
  have hs := Proves_sound engineVal h
  -- encodeF (.plays …) = .atom (atomCode (.plays …)); interp engineVal (.atom n) = engineVal n
  simp only [encodeF, interp] at hs
  rw [engineVal_atomCode hinj] at hs
  exact hs

/-- And then BWD lands in the engine (the spike's `BWD_plays_of_sound`): engine truth of a play-atom
    yields `∃m, Provable m φ` via `atom_complete`. So object proof ⟹ engine provability, for plays. -/
theorem bridge_BWD_plays (hinj : Function.Injective atomCode)
    (p q : Prog) (a : Action)
    (h : Proves (encodeF (.plays p q a))) :
    ∃ m, Provable m (.plays p q a) := by
  obtain ⟨n, hn⟩ := bridgeSound_plays hinj p q a h
  exact ⟨atom_cost n, Provable.atom (BaseTheorems.atom_complete p q a n hn)⟩

/-! ## VERDICT — E3 + the E4 encoding map done for the load-bearing fragment.

`encodeF` maps the engine `Formula` into `OFml` structurally; `engineVal` gives the engine meaning to
encoded atoms; `bridgeSound_plays` DERIVES `BridgeSound` for play-atoms from `Proves_sound` (no new
principle), and `bridge_BWD_plays` chains it through the engine's `atom_complete` to land
`∃m, Provable m φ` — exactly the spike's `BWD_plays_of_sound`, now over the real `encodeF`/`Proves`.

REMAINING for full E4: prove `atomCode` injective (a real engine-`Formula` Gödel code, like
`Reflection.encode_inj`); the FWD direction (engine `Provable m φ ⟶ Proves (encodeF φ)` by recursion on
the `Provable` constructors); and `box`-budget threading (E5). The DANGEROUS direction (BWD) is
discharged here. -/

#check @bridgeSound_plays
#check @bridge_BWD_plays

end PD.Reflection
