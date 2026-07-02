import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic

/-!
# B4-impl spike: predicate-level diagonal — `selfApply θ := betaA θ` gives the SELF-CODE fixpoint.

B3-followup verdict: `diag_object'` needs `ψ ↔ gApp(⌜ψ⌝)` (self-code), but substitution `selfApply =
plug` gives only `betaA θ ↔ gApp(⌜selfApply θ⌝)` and plug is head-preserving so `selfApply θ ≠ betaA θ`.

FIX (predicate-level): define `selfApply θ := betaA θ` DIRECTLY (the self-application IS "wrap in betaA",
mirroring the toy's `.app`-ignores-code). Then `e (encode θ) = encode (betaA θ)` and `repr_object θ`
gives `betaA θ ↔ gApp(⌜betaA θ⌝)` — the SELF-CODE fixpoint `ψ ↔ gApp(⌜ψ⌝)` with `ψ := betaA θ`.
OUTCOME-FREE (from betaGamma/representability, no hp0). This spike proves that in a minimal OFml.
-/

namespace BewB4
open Function

/-! ## 1. Minimal OFml + injective encode. -/

inductive OFml where
  | atom (n : Nat)
  | gApp (c : Nat)
  | betaA (body : OFml)
  | gamma (x y : Nat)
  | imp  (a b : OFml)
  | iff  (a b : OFml)
  | box  (a : OFml)
deriving DecidableEq, Inhabited

def encode : OFml → Nat
  | .atom n  => Nat.pair 0 n
  | .gApp c  => Nat.pair 1 c
  | .betaA b => Nat.pair 2 (encode b)
  | .gamma x y => Nat.pair 3 (Nat.pair x y)
  | .imp a b => Nat.pair 4 (Nat.pair (encode a) (encode b))
  | .iff a b => Nat.pair 5 (Nat.pair (encode a) (encode b))
  | .box a   => Nat.pair 6 (encode a)

theorem encode_inj : Injective encode := by
  intro x
  induction x with
  | atom n => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | gApp c => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | betaA b ih => intro y h; cases y with
      | betaA b' => simp only [encode, Nat.pair_eq_pair] at h; rw [ih h.2]
      | _ => simp_all [encode, Nat.pair_eq_pair]
  | gamma x' y' => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | imp a b iha ihb => intro y h; cases y with
      | imp a' b' => simp only [encode, Nat.pair_eq_pair] at h; obtain ⟨_, ha, hb⟩ := h; rw [iha ha, ihb hb]
      | _ => simp_all [encode, Nat.pair_eq_pair]
  | iff a b iha ihb => intro y h; cases y with
      | iff a' b' => simp only [encode, Nat.pair_eq_pair] at h; obtain ⟨_, ha, hb⟩ := h; rw [iha ha, ihb hb]
      | _ => simp_all [encode, Nat.pair_eq_pair]
  | box a ih => intro y h; cases y with
      | box a' => simp only [encode, Nat.pair_eq_pair] at h; rw [ih h.2]
      | _ => simp_all [encode, Nat.pair_eq_pair]

/-! ## 2. THE PREDICATE-LEVEL `selfApply` + `e` — `selfApply θ := betaA θ`. -/

/-- **Predicate-level self-application**: `selfApply θ := betaA θ` (the self-application IS "wrap in
    betaA", as the toy's `.app` evaluates `θ` at `⌜θ⌝`). This is the KEY change vs the head-preserving
    `plug`: now `selfApply θ` is `betaA`-headed and EQUALS the fixpoint sentence. -/
def selfApply (θ : OFml) : OFml := .betaA θ

open Classical in
noncomputable def e (n : Nat) : Nat :=
  if h : ∃ θ, encode θ = n then encode (selfApply h.choose) else 0

theorem e_graph (θ : OFml) : e (encode θ) = encode (selfApply θ) := by
  have hex : ∃ θ', encode θ' = encode θ := ⟨θ, rfl⟩
  rw [e, dif_pos hex]; rw [show hex.choose = θ from encode_inj hex.choose_spec]

/-! ## 3. `Proves` with gammaAx/betaGamma (the representability inputs, as in the real layer). -/

inductive Proves : OFml → Prop where
  | impId (a : OFml) : Proves (.imp a a)
  | mp {a b : OFml} : Proves (.imp a b) → Proves a → Proves b
  | iffIntro {a b : OFml} : Proves (.imp a b) → Proves (.imp b a) → Proves (.iff a b)
  | iffMPF {a b : OFml} : Proves (.iff a b) → Proves (.imp a b)
  | iffMPB {a b : OFml} : Proves (.iff a b) → Proves (.imp b a)
  | gammaAx (n : Nat) : Proves (.gamma n (e n))
  | betaGamma (body : OFml) (y : Nat) :
      Proves (.imp (.gamma (encode body) y) (.iff (.betaA body) (.gApp y)))

/-! ## 4. THE PAYOFF — `diagFix` DERIVED (self-code fixpoint), OUTCOME-FREE. -/

/-- `repr_object` (as in the real layer): `betaA θ ↔ gApp(⌜selfApply θ⌝)`. With the predicate-level
    `selfApply θ = betaA θ`, this is `betaA θ ↔ gApp(⌜betaA θ⌝)` — the SELF-CODE fixpoint = `diagFix`. -/
theorem repr_object (θ : OFml) :
    Proves (.iff (.betaA θ) (.gApp (encode (selfApply θ)))) := by
  have hg : Proves (.gamma (encode θ) (e (encode θ))) := Proves.gammaAx (encode θ)
  rw [e_graph θ] at hg
  exact Proves.mp (Proves.betaGamma θ (encode (selfApply θ))) hg

/-- **`diagFix` DERIVED** — `betaA θ ↔ gApp(⌜betaA θ⌝)`, the self-code fixpoint the Löb chain
    (`diag_object'`) needs, now a THEOREM from `repr_object` + `selfApply θ = betaA θ`. NO hp0, NO
    asserted rule — pure representability. This is what B3's `diagFix` had to ASSERT with hp0. -/
theorem diagFix_derived (θ : OFml) :
    Proves (.iff (.betaA θ) (.gApp (encode (.betaA θ)))) := by
  have h := repr_object θ
  rwa [show selfApply θ = .betaA θ from rfl] at h

/-! ## 5. SOUNDNESS — the predicate-level `selfApply` is HONEST (proves no falsehood).

The re-defined `selfApply θ := betaA θ` changes `e`; we must check `betaGamma`/`gammaAx` stay sound.
`interp`: `betaA body ↦ G(e ⌜body⌝)`, `gApp c ↦ G c`, `gamma x y ↦ (e x = y)`, box abstract. Every rule
sound for ALL `G` ⟹ no falsehood. If this closes, `diagFix_derived` is a HONEST theorem, not a cheat. -/

def interp (G : Nat → Prop) (Prov : OFml → Prop) : OFml → Prop
  | .atom n  => G n
  | .gApp c  => G c
  | .betaA b => G (e (encode b))
  | .gamma x y => e x = y
  | .imp a b => interp G Prov a → interp G Prov b
  | .iff a b => interp G Prov a ↔ interp G Prov b
  | .box a   => Prov a

theorem Proves_sound (G : Nat → Prop) (Prov : OFml → Prop) {φ : OFml} (h : Proves φ) :
    interp G Prov φ := by
  induction h with
  | impId a => intro ha; exact ha
  | mp _ _ ihab iha => exact ihab iha
  | iffIntro _ _ ihab ihba => exact ⟨ihab, ihba⟩
  | iffMPF _ ih => exact ih.mp
  | iffMPB _ ih => exact ih.mpr
  | gammaAx n => show e n = e n; rfl
  | betaGamma body y => intro hg; simp only [interp] at hg ⊢; rw [hg]

/-- Consistency: `Proves` does not prove the false atom, via the `G ≡ False` valuation. So the
    predicate-level diagonal (and `diagFix_derived`) inject no falsehood — HONEST. -/
theorem consistency : ¬ Proves (.atom 0) :=
  fun h => Proves_sound (fun _ => False) (fun _ => False) h

/-! ## VERDICT — B4-impl CORE: the predicate-level diagonal makes `diagFix` a DERIVED, OUTCOME-FREE,
    SOUND theorem.

`selfApply θ := betaA θ` (predicate-level, replacing head-preserving `plug`) makes `e ⌜θ⌝ = ⌜betaA θ⌝`,
so `repr_object` (from `gammaAx`/`betaGamma`, pure representability) directly yields the SELF-CODE
fixpoint `betaA θ ↔ gApp(⌜betaA θ⌝)` = `diagFix_derived` — NO hp0, NO asserted rule. And `Proves_sound`/
`consistency` certify it injects no falsehood. This is exactly what B3's `diagFix` needed hp0 for.

⇒ Combined with B3's `ctxUnfold` (outcome-free via `Gw`), BOTH diagonal legs are now outcome-free, so
`provesU_sound`/consistency drop hp0 entirely ⇒ `provesN_play_extract` DISSOLVES.

REMAINING (B4-port): apply this ONE change (`selfApply θ := betaA θ`) to the real `Syntax.lean`, re-check
the real `e_graph`/`repr_object`/`Proves_sound` (they use the same shapes — should port directly), swap
`diagFix` (asserted) → `diagFix_derived` (theorem), drop hp0 from the diagonal soundness, then wire +
delete the axiom. The `plug` function becomes unused by the diagonal (may stay for other purposes). -/

#check @repr_object
#check @diagFix_derived
#check @Proves_sound
#check @consistency

end BewB4
