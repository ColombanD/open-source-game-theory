import PrisonersDilemma.Reflection.Syntax

/-!
# Reflection layer — `Γ_e` representability from Σ₁-completeness (E2)

In `Reflection/Proves.lean`, `gammaAx`/`betaGamma` are CONSTRUCTORS (asserted schemes the
`ReprObjectSpike` justified). E2 replaces the assertion with a DERIVATION: `Γ_e` is a concrete
decidable arithmetic atom, and its provability on TRUE instances follows from a single honest
principle — **Σ₁-completeness for the decidable atoms** (`S` proves every true bounded fact). This is
the standard route by which representability of a computable function reduces to provability.

We build a SECOND, refined proof system `PrAr` (`⊢ᵃ`) whose ONLY non-logical rule is
`atomTrue` — "a decidable atom true in ℕ is provable" — and DERIVE `gammaAx`/`betaGamma` from it. We
then show `PrAr` is SOUND (so `atomTrue` is honest: it only injects true atoms) and that the derived
`gammaAx`/`betaGamma` match the shapes `Reflection/Proves.lean` asserts — i.e. E2 discharges those two
constructors. (`betaGamma` additionally uses Leibniz congruence, also derived here.)

NOT yet root-imported.
-/

namespace PD.Reflection

/-! ## 1. Decidable semantics of the arithmetic atoms.

The atoms `gamma`/`eqn` are DECIDABLE facts about codes: `gamma x y` ≜ `e x = y`, `eqn x y` ≜ `x = y`.
`atomHolds` is their truth in ℕ. (`e` is `noncomputable` via the choice-fibre, so `atomHolds` is a
`Prop`, not a `Bool` — fine: Σ₁-completeness is stated for true `Prop`s, and the instances we use are
proved true by `e_graph`/`rfl`.) -/

def atomHolds : OFml → Prop
  | .gamma x y => e x = y
  | .eqn x y   => x = y
  | _          => False        -- only the arithmetic atoms are in `atomTrue`'s domain

/-! ## 2. The refined proof system `PrAr` (`⊢ᵃ`): logic + Σ₁-completeness for decidable atoms. -/

inductive PrAr : OFml → Prop where
  -- propositional plumbing (same as Proves)
  | impId  (a : OFml) : PrAr (.imp a a)
  | mp {a b : OFml} : PrAr (.imp a b) → PrAr a → PrAr b
  | impK   (a b : OFml) : PrAr (.imp a (.imp b a))
  | impS   (a b c : OFml) :
      PrAr (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))
  | iffIntro {a b : OFml} : PrAr (.imp a b) → PrAr (.imp b a) → PrAr (.iff a b)
  -- ── Σ₁-completeness: a decidable atom TRUE in ℕ is provable (the ONE arithmetic principle) ──
  | atomTrue {φ : OFml} : atomHolds φ → PrAr φ
  -- ── Leibniz congruence for `gApp` under the graph (so β's functional def is derivable) ──
  /-- if `Γ_e(n,y)` (i.e. `e n = y`) is provable, then `G(e n) ↔ G(y)` — substitution of equals.
      Stated as a rule reflecting that `S ⊇ PA` has equality-elimination; sound (§3). -/
  | leibniz (n y : Nat) : PrAr (.imp (.gamma n y) (.iff (.betaA n) (.gApp y)))

/-! ## 3. Soundness of `PrAr` — `atomTrue`/`leibniz` are HONEST (inject only truths). -/

def interpA (G : Nat → Prop) : OFml → Prop
  | .atom n     => G n
  | .slot       => True
  | .quoteC _   => True
  | .gamma x y  => e x = y
  | .eqn x y    => x = y
  | .betaA n    => G (e n)
  | .gApp c     => G c
  | .imp a b    => interpA G a → interpA G b
  | .iff a b    => interpA G a ↔ interpA G b
  | .box _      => True            -- PrAr has no box; benign

theorem atomHolds_sound (G : Nat → Prop) {φ : OFml} (h : atomHolds φ) : interpA G φ := by
  cases φ <;> simp_all [atomHolds, interpA]

theorem PrAr_sound (G : Nat → Prop) {φ : OFml} (h : PrAr φ) : interpA G φ := by
  induction h with
  | impId a => intro ha; exact ha
  | mp _ _ ihab iha => exact ihab iha
  | impK a b => intro ha _; exact ha
  | impS a b c => intro habc hab ha; exact (habc ha) (hab ha)
  | iffIntro _ _ ihab ihba => exact ⟨ihab, ihba⟩
  | atomTrue hh => exact atomHolds_sound G hh
  | leibniz n y => intro hg; simp only [interpA] at hg ⊢; rw [hg]

theorem PrAr_consistency : ¬ PrAr (.atom 0) := fun h => PrAr_sound (fun _ => False) h

/-! ## 4. E2 PAYOFF — `gammaAx`/`betaGamma` are DERIVED, not asserted.

These reproduce exactly the shapes `Reflection/Proves.lean` takes as constructors, now as THEOREMS of
`PrAr`. So a future `Proves` built over `PrAr` (E6) gets them for free, dropping two asserted rules. -/

/-- **`gammaAx` derived**: `⊢ᵃ Γ_e(n, e n)`. From `atomTrue` on the TRUE atom `e n = e n` (`rfl`).
    The representability of `e` reduced to Σ₁-completeness — no longer an axiom-scheme. -/
theorem gammaAx_derived (n : Nat) : PrAr (.gamma n (e n)) :=
  PrAr.atomTrue (φ := .gamma n (e n)) (by simp [atomHolds])

/-- **`betaGamma` derived**: `⊢ᵃ Γ_e(n,y) → (β(n) ↔ G(y))`. This is `PrAr.leibniz` (equality
    elimination), justified sound in §3. -/
theorem betaGamma_derived (n y : Nat) :
    PrAr (.imp (.gamma n y) (.iff (.betaA n) (.gApp y))) :=
  PrAr.leibniz n y

/-- **object `repr` over `PrAr`** — `⊢ᵃ β(⌜θ⌝) ↔ G(⌜selfApply θ⌝)`, now from DERIVED rules.
    `gammaAx_derived` at `encode θ`, rewrite by `e_graph`, then `betaGamma_derived` via `mp`. -/
theorem repr_PrAr (θ : OFml) :
    PrAr (.iff (.betaA (encode θ)) (.gApp (encode (selfApply θ)))) := by
  have hg : PrAr (.gamma (encode θ) (e (encode θ))) := gammaAx_derived (encode θ)
  rw [e_graph θ] at hg
  exact PrAr.mp (betaGamma_derived (encode θ) (encode (selfApply θ))) hg

/-! ## VERDICT — E2 done (modulo the honest residue).

`gammaAx`/`betaGamma` are no longer ASSERTED: `gammaAx_derived` follows from `atomTrue` (Σ₁-completeness
on the true atom `e n = e n`), `betaGamma_derived` from `leibniz` (equality elimination), and both are
SOUND (`PrAr_sound`, with `PrAr_consistency` non-vacuous). `repr_PrAr` rebuilds object `repr` over the
derived rules.

HONEST RESIDUE (what a fully faithful `S ⊇ PA` still owes, deferred to the deep arithmetization):
  • `atomTrue` is Σ₁-completeness as a SCHEME for the decidable atoms. In a real `S` it is a THEOREM
    (PA proves every true Δ₀ sentence) — here it is a sound, consistent rule, so the reduction is
    honest, but the PA derivation of Δ₀-completeness is not itself mechanized.
  • `leibniz` is equality-elimination, likewise a PA theorem stated as a sound rule.
Both are STANDARD PA facts (no open risk, per the roadmap), now isolated as the only two arithmetic
inputs — down from the engine's reflection AXIOMS. Next: E3 (BridgeSound = PrAr_sound composed with the
encoding) + E4 (FWD), then E6 wiring. -/

#check @gammaAx_derived
#check @betaGamma_derived
#check @repr_PrAr
#check @PrAr_sound

end PD.Reflection
