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

/-! A stable per-Formula code (engine-side Gödel tag), now a CONCRETE, provably injective Gödel code
(head-tagged `Nat.pair`, mutually recursive with a `Prog` code and an `Action` code — `Formula` atoms
carry `Prog`s, `Prog` carries `Formula`s at `.search`). This discharges the last atomic obligation:
`atomCode` is no longer opaque, and `atomCode_injective` replaces the `hinj` hypothesis threaded through
the bridge/forward/engine layers. Promoted from `Research/Spikes/pblt/AtomCodeSpike.lean`. -/

/-- `Action → Nat`, injective (2 constructors). -/
def actCode : Action → Nat
  | .C => 0
  | .D => 1

theorem actCode_inj : Function.Injective actCode := by
  intro a b h; cases a <;> cases b <;> simp_all [actCode]

mutual
  /-- Injective code for engine `Prog` (mutually recursive with `formulaCode` via `.search`). -/
  def progCode : Prog → Nat
    | .const a        => Nat.pair 0 (actCode a)
    | .self           => Nat.pair 1 0
    | .opp            => Nat.pair 2 0
    | .bot p          => Nat.pair 3 (progCode p)
    | .sim p q        => Nat.pair 4 (Nat.pair (progCode p) (progCode q))
    | .ite b a p q    => Nat.pair 5 (Nat.pair (actCode a) (Nat.pair (progCode b) (Nat.pair (progCode p) (progCode q))))
    | .search k φ p q => Nat.pair 6 (Nat.pair k (Nat.pair (formulaCode φ) (Nat.pair (progCode p) (progCode q))))

  /-- Injective code for engine `Formula` — this IS `atomCode` (see the `abbrev` below). -/
  def formulaCode : Formula → Nat
    | .plays p q a => Nat.pair 0 (Nat.pair (progCode p) (Nat.pair (progCode q) (actCode a)))
    | .impl φ ψ    => Nat.pair 1 (Nat.pair (formulaCode φ) (formulaCode ψ))
    | .neg φ       => Nat.pair 2 (formulaCode φ)
    | .box k φ     => Nat.pair 3 (Nat.pair k (formulaCode φ))
    | .eq p q      => Nat.pair 4 (Nat.pair (progCode p) (progCode q))
    | .diag g φ    => Nat.pair 5 (Nat.pair g (formulaCode φ))
end

mutual
  theorem progCode_inj : ∀ {p p' : Prog}, progCode p = progCode p' → p = p'
    | .const a, p', h => by
        cases p' with
        | const a' => simp only [progCode, Nat.pair_eq_pair] at h; rw [actCode_inj h.2]
        | _ => simp only [progCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .self, p', h => by
        cases p' with
        | self => rfl
        | _ => simp only [progCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .opp, p', h => by
        cases p' with
        | opp => rfl
        | _ => simp only [progCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .bot p, p', h => by
        cases p' with
        | bot p'' => simp only [progCode, Nat.pair_eq_pair] at h; rw [progCode_inj h.2]
        | _ => simp only [progCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .sim p q, p', h => by
        cases p' with
        | sim p'' q'' =>
            simp only [progCode, Nat.pair_eq_pair] at h
            obtain ⟨_, hp, hq⟩ := h; rw [progCode_inj hp, progCode_inj hq]
        | _ => simp only [progCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .ite b a p q, p', h => by
        cases p' with
        | ite b'' a'' p'' q'' =>
            simp only [progCode, Nat.pair_eq_pair] at h
            obtain ⟨_, ha, hb, hp, hq⟩ := h
            rw [actCode_inj ha, progCode_inj hb, progCode_inj hp, progCode_inj hq]
        | _ => simp only [progCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .search k φ p q, p', h => by
        cases p' with
        | search k'' φ'' p'' q'' =>
            simp only [progCode, Nat.pair_eq_pair] at h
            obtain ⟨_, hk, hφ, hp, hq⟩ := h
            rw [hk, formulaCode_inj hφ, progCode_inj hp, progCode_inj hq]
        | _ => simp only [progCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)

  theorem formulaCode_inj : ∀ {φ φ' : Formula}, formulaCode φ = formulaCode φ' → φ = φ'
    | .plays p q a, φ', h => by
        cases φ' with
        | plays p'' q'' a'' =>
            simp only [formulaCode, Nat.pair_eq_pair] at h
            obtain ⟨_, hp, hq, ha⟩ := h
            rw [progCode_inj hp, progCode_inj hq, actCode_inj ha]
        | _ => simp only [formulaCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .impl φ ψ, φ', h => by
        cases φ' with
        | impl φ'' ψ'' =>
            simp only [formulaCode, Nat.pair_eq_pair] at h
            obtain ⟨_, hφ, hψ⟩ := h; rw [formulaCode_inj hφ, formulaCode_inj hψ]
        | _ => simp only [formulaCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .neg φ, φ', h => by
        cases φ' with
        | neg φ'' => simp only [formulaCode, Nat.pair_eq_pair] at h; rw [formulaCode_inj h.2]
        | _ => simp only [formulaCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .box k φ, φ', h => by
        cases φ' with
        | box k'' φ'' =>
            simp only [formulaCode, Nat.pair_eq_pair] at h
            obtain ⟨_, hk, hφ⟩ := h; rw [hk, formulaCode_inj hφ]
        | _ => simp only [formulaCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .eq p q, φ', h => by
        cases φ' with
        | eq p'' q'' =>
            simp only [formulaCode, Nat.pair_eq_pair] at h
            obtain ⟨_, hp, hq⟩ := h; rw [progCode_inj hp, progCode_inj hq]
        | _ => simp only [formulaCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .diag g φ, φ', h => by
        cases φ' with
        | diag g'' φ'' =>
            simp only [formulaCode, Nat.pair_eq_pair] at h
            obtain ⟨_, hg, hφ⟩ := h; rw [hg, formulaCode_inj hφ]
        | _ => simp only [formulaCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
end

/-- The engine-`Formula` Gödel tag used as an atom key — now concrete (`= formulaCode`). -/
def atomCode : Formula → Nat := formulaCode

/-- **The last atomic obligation, DISCHARGED**: `atomCode` is injective. -/
theorem atomCode_injective : Function.Injective atomCode := fun _ _ h => formulaCode_inj h

/-- Encode an engine `Formula` into the object language. Structural on `plays`/`impl`/`box`; `neg`/`eq`
    (absent from the PBLT fragment) go to a benign keyed atom so the map is total. -/
def encodeF : Formula → OFml
  | .plays p q a => .atom (atomCode (.plays p q a))
  | .impl φ ψ    => .imp (encodeF φ) (encodeF ψ)
  | .box _ φ     => .box (encodeF φ)
  | .neg φ       => .atom (atomCode (.neg φ))      -- benign; not in PBLT fragment
  | .eq p q      => .atom (atomCode (.eq p q))     -- benign; not in PBLT fragment
  | .diag g φ    => .atom (atomCode (.diag g φ))   -- benign; the INTERNAL diagonal, not the layer's

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
