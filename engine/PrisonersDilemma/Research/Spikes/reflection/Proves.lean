import PrisonersDilemma.Research.Spikes.reflection.Syntax

/-!
# Reflection layer — the object proof system `⊢_S` and its soundness (E1b + E1c)

Consolidates the de-risked spikes `ReprObjectSpike` (the `Γ_e` representability rules) and
`HBLObjectSpike` (the D1–D3 derivability conditions) into ONE inductive object proof system `Proves`
over the real `OFml` (`Reflection/Syntax.lean`). `box` is the arithmetized provability predicate
(E1c): `interp (box a) := Proves a`, so D1/D2/D3 are the standard Hilbert–Bernays–Löb facts.

Soundness (`Proves_sound`) + consistency (`¬ Proves ⊥-atom`) are the anti-cheat: no rule proves a
falsehood, and the system is non-vacuous, so the soundness is meaningful. With this in place, E2 will
PROVE `gammaAx`/`betaGamma` from a concrete arithmetized `Γ_e` (here they are still the schemes the
spikes justified; the soundness shows they are honest).

NOT yet root-imported (reflection layer builds independently until E6).
-/

namespace PD.Reflection

/-! ## 1. `⊢_S` — propositional plumbing + HBL D1–D3 + the `Γ_e`/β representability rules.

Each rule is justified by `Proves_sound` (§2). Budgets are kept META at this stage (the engine threads
them via `Formula.size`; E5 re-threads them — orthogonal to the logical/modal content here). -/

inductive Proves : OFml → Prop where
  -- ── propositional plumbing (S/K/MP/iff) ──
  | impId   (a : OFml) : Proves (.imp a a)
  | mp {a b : OFml} : Proves (.imp a b) → Proves a → Proves b
  | impK    (a b : OFml) : Proves (.imp a (.imp b a))
  | impS    (a b c : OFml) :
      Proves (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))
  | iffIntro {a b : OFml} : Proves (.imp a b) → Proves (.imp b a) → Proves (.iff a b)
  | iffMPF {a b : OFml} : Proves (.iff a b) → Proves (.imp a b)
  | iffMPB {a b : OFml} : Proves (.iff a b) → Proves (.imp b a)
  -- ── HBL derivability conditions (≈ engine boxIntro/axK/box4) ──
  | D1_nec {a : OFml} : Proves a → Proves (.box a)
  | D2_K   (a b : OFml) : Proves (.imp (.box (.imp a b)) (.imp (.box a) (.box b)))
  | D3_four (a : OFml) : Proves (.imp (.box a) (.box (.box a)))
  -- ── Γ_e representability (≈ ReprObject gammaAx/betaGamma); E2 will DERIVE these from arithmetic ──
  /-- the graph holds at the true value `e n` (representability of the self-evaluation `e`). -/
  | gammaAx (n : Nat) : Proves (.gamma n (e n))
  /-- β's functional definition via the graph: `Γ_e(⌜body⌝,y) → (β(⌜body⌝) ↔ G(y))` (= Leibniz
      congruence of `G` under `e ⌜body⌝ = y`, since `β(⌜body⌝)` means `G(e ⌜body⌝)`). Now structural in
      `body` (the atom carries the subformula so the diagonal's slot can sit inside). -/
  | betaGamma (body : OFml) (y : Nat) :
      Proves (.imp (.gamma (encode body) y) (.iff (.betaA body) (.gApp y)))

/-! ## 2. Soundness — `box` = provability (E1c). The ANTI-CHEAT.

`interp` reads each atom in the standard model:
  • `betaA n` ↦ `G (e n)`   (β's meaning, the tex definition)
  • `gApp c`  ↦ `G c`        (the target predicate at code `c`)
  • `gamma x y` ↦ `e x = y`  (the real graph)
  • `box a`   ↦ `Proves a`   (the provability predicate — makes D1–D3 the standard HBL facts)
Atoms/slot/quoteC/eqn get a denotation from the valuation `G` / equality. Then every rule is sound. -/

def interp (G : Nat → Prop) : OFml → Prop
  | .atom n     => G n
  | .slot       => True            -- the bare slot is never asserted; benign denotation
  | .quoteC _   => True            -- a code literal is a term, not a proposition; benign
  | .gamma x y  => e x = y
  | .eqn x y    => x = y
  | .betaA body => G (e (encode body))
  | .gApp c     => G c
  | .imp a b    => interp G a → interp G b
  | .iff a b    => interp G a ↔ interp G b
  | .box a      => Proves a

theorem Proves_sound (G : Nat → Prop) {φ : OFml} (h : Proves φ) : interp G φ := by
  induction h with
  | impId a => intro ha; exact ha
  | mp _ _ ihab iha => exact ihab iha
  | impK a b => intro ha _; exact ha
  | impS a b c => intro habc hab ha; exact (habc ha) (hab ha)
  | iffIntro _ _ ihab ihba => exact ⟨ihab, ihba⟩
  | iffMPF _ ihab => exact ihab.mp
  | iffMPB _ ihab => exact ihab.mpr
  | D1_nec ha _ => exact ‹Proves _›
  | D2_K a b => intro hab ha; exact Proves.mp hab ha
  | D3_four a => intro ha; exact Proves.D1_nec ha
  | gammaAx n => exact rfl
  | betaGamma body y => intro hg; simp only [interp] at hg ⊢; rw [hg]

/-- **Consistency** (anti-vacuous): `Proves` does not prove the atom `0`. Via the `G ≡ False`
    valuation through `Proves_sound`, so the soundness is meaningful, not trivial. -/
theorem consistency : ¬ Proves (.atom 0) := fun h => Proves_sound (fun _ => False) h

/-! ## 3. The object-level `repr` — DERIVED (the payoff, promoted from ReprObjectSpike).

For every `θ`, `⊢_S β(⌜θ⌝) ↔ G(⌜selfApply θ⌝)`. Instantiate `gammaAx` at `encode θ`, rewrite the value
by `e_graph`, feed to `betaGamma`. No new rule, no defeq. -/

theorem repr_object (θ : OFml) :
    Proves (.iff (.betaA θ) (.gApp (encode (selfApply θ)))) := by
  have hg : Proves (.gamma (encode θ) (e (encode θ))) := Proves.gammaAx (encode θ)
  rw [e_graph θ] at hg
  exact Proves.mp (Proves.betaGamma θ (encode (selfApply θ))) hg

/-! ## 4. The mutual-Löb skeleton — DERIVED from D1–D3 (promoted from HBLObjectSpike).

`pblt_of_bpsb` / the engine `mutual_loeb` consume exactly this Route-2 chain. -/

theorem impTrans {a b c : OFml} (hab : Proves (.imp a b)) (hbc : Proves (.imp b c)) :
    Proves (.imp a c) := by
  have h1 : Proves (.imp a (.imp b c)) := Proves.mp (Proves.impK _ _) hbc
  exact Proves.mp (Proves.mp (Proves.impS a b c) h1) hab

/-- From legs `□φP → φD` and `□φD → φP`, derive `□φP → φP` via D1/D2/D3. -/
theorem mutual_loeb_object (φP φD : OFml)
    (legPD : Proves (.imp (.box φP) φD))
    (legDP : Proves (.imp (.box φD) φP)) :
    Proves (.imp (.box φP) φP) := by
  have h1 : Proves (.box (.imp (.box φP) φD)) := Proves.D1_nec legPD
  have h2 : Proves (.imp (.box (.box φP)) (.box φD)) :=
    Proves.mp (Proves.D2_K (.box φP) φD) h1
  have h3 : Proves (.imp (.box φP) (.box (.box φP))) := Proves.D3_four φP
  exact impTrans (impTrans h3 h2) legDP

end PD.Reflection
