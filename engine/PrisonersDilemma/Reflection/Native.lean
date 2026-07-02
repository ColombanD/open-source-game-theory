import PrisonersDilemma.Reflection.Diagonal
import PrisonersDilemma.Reflection.Bridge


/-!
# ⚑ HISTORICAL (2026-07-01): superseded by the INTERNALIZATION — `PBLT` is deleted.

This module belongs to the side-reflection route, which bottomed out at `provesN_play_extract`
(object→engine reflection). That route is CLOSED and MOOT: bounded Löb is now proven INSIDE the
engine's own `Provable` (`BaseTheorems.bloeb_engine`/`pblt_engine`, via `Formula.diag` — see
`Research/Notes/INTERNALIZATION_ROADMAP.md`), and the `PBLT` axiom is deleted. This file is kept as
the meta-justification/history of the diagonal's derivation (`repr_object` etc. justify that a
faithful arithmetization contains the fixpoint sentence `.diag` internalizes). Do not build on the
`ProvesN`/extraction machinery here.
-/

/-!
# Reflection layer — the NATIVE object theory `ProvesN` (the correct PBLT wiring)

Last session's decisive finding: you cannot run the bounded-Löb chain in base `Proves` and reinterpret
`box` as the object theory — the `interp → interpC` bridge fails on NEGATIVE box occurrences (`□a → b`:
`embed : Proves a → ProvesN a` runs the wrong way in the contravariant antecedent). So `box` must mean
`ProvesN`-provability UNIFORMLY, and the chain must be proven NATIVELY over `ProvesN`.

This module builds that: ONE hypothesis-indexed system `ProvesN Γ p` (`Γ` = assumption list, `p` = the
fixed Löb target), with `box := ProvesN`-provability throughout. It carries:
  • the propositional core (hyp/S/K/id/mp/iff) so `deduction` (= `impI`) is admissible;
  • the HBL modal rules `necN`/`kN`/`fourN` (box = ProvesN — `necN` is the standard closed-necessitation);
  • the two diagonal rules `ctxUnfold`/`diagFix` (from `Diagonal`, now with box = ProvesN uniformly);
  • `embed` of base `Proves` for ATOMIC leaves only (never carrying box through a bridge).

`bloeb_native` then proves `□p → p ⟹ p` entirely inside `ProvesN`, and the diagonal legs come from
`diagFix`/`ctxUnfold` — no hypotheses. NOT yet root-imported.
-/

namespace PD.Reflection

/-! ## 1. The native system `ProvesN p Γ φ` (`p` = Löb target, `Γ` = hypotheses). -/

inductive ProvesN (p : OFml) : List OFml → OFml → Prop where
  -- propositional core (with hypotheses, for the deduction theorem)
  | hyp   {Γ : List OFml} {a : OFml} : a ∈ Γ → ProvesN p Γ a
  | impId (Γ : List OFml) (a : OFml) : ProvesN p Γ (.imp a a)
  | impK  (Γ : List OFml) (a b : OFml) : ProvesN p Γ (.imp a (.imp b a))
  | impS  (Γ : List OFml) (a b c : OFml) :
      ProvesN p Γ (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))
  | mp {Γ : List OFml} {a b : OFml} : ProvesN p Γ (.imp a b) → ProvesN p Γ a → ProvesN p Γ b
  | iffIntro {Γ : List OFml} {a b : OFml} :
      ProvesN p [] (.imp a b) → ProvesN p [] (.imp b a) → ProvesN p Γ (.iff a b)
  | iffMPF {Γ : List OFml} {a b : OFml} : ProvesN p [] (.iff a b) → ProvesN p Γ (.imp a b)
  | iffMPB {Γ : List OFml} {a b : OFml} : ProvesN p [] (.iff a b) → ProvesN p Γ (.imp b a)
  -- HBL modal rules — box denotes ProvesN-provability (necN = closed necessitation)
  | necN {Γ : List OFml} {a : OFml} : ProvesN p [] a → ProvesN p Γ (.box a)
  | kN   (Γ : List OFml) (a b : OFml) :
      ProvesN p Γ (.imp (.box (.imp a b)) (.imp (.box a) (.box b)))
  | fourN (Γ : List OFml) (a : OFml) : ProvesN p Γ (.imp (.box a) (.box (.box a)))
  -- diagonal rules (box = ProvesN uniformly)
  | ctxUnfold (Γ : List OFml) (φ : OFml) :
      ProvesN p Γ (.iff (.gApp (encode φ)) (.imp (.box φ) p))
  | diagFix (Γ : List OFml) (body : OFml) :
      ProvesN p Γ (.iff (.betaA body) (.gApp (encode (.betaA body))))
  -- embed base `Proves` (used for atomic leaves; a closed base theorem holds in any Γ)
  | embed {Γ : List OFml} {a : OFml} : Proves a → ProvesN p Γ a
  -- FWD bridge: an ENGINE-provable formula's encoding is object-provable (the Löb premise enters here).
  -- Sound: engine-provable ⟹ true (Provable_sound), so it holds under interpN at the engine valuation.
  | engineLeaf {Γ : List OFml} {m : Nat} {φ : Formula} : Provable m φ → ProvesN p Γ (encodeF φ)

/-! ## 2. Weakening + the deduction theorem (`impI`), native. -/

theorem weakenN {p : OFml} {Γ Δ : List OFml} {a : OFml} (hsub : Γ ⊆ Δ) (h : ProvesN p Γ a) :
    ProvesN p Δ a := by
  induction h generalizing Δ with
  | hyp hmem => exact ProvesN.hyp (hsub hmem)
  | impId _ a => exact ProvesN.impId _ a
  | impK _ a b => exact ProvesN.impK _ a b
  | impS _ a b c => exact ProvesN.impS _ a b c
  | mp _ _ ihab iha => exact ProvesN.mp (ihab hsub) (iha hsub)
  | iffIntro hab hba _ _ => exact ProvesN.iffIntro hab hba
  | iffMPF h _ => exact ProvesN.iffMPF h
  | iffMPB h _ => exact ProvesN.iffMPB h
  | necN h _ => exact ProvesN.necN h
  | kN _ a b => exact ProvesN.kN _ a b
  | fourN _ a => exact ProvesN.fourN _ a
  | ctxUnfold _ φ => exact ProvesN.ctxUnfold _ φ
  | diagFix _ body => exact ProvesN.diagFix _ body
  | embed hb => exact ProvesN.embed hb
  | engineLeaf hpr => exact ProvesN.engineLeaf hpr

/-- **Deduction theorem = `impI`** — `ProvesN p (q :: Γ) r → ProvesN p Γ (q → r)`. Admissible (S/K/mp);
    the closed premises of `iffIntro`/`iffMPF`/`iffMPB`/`necN` are re-derived and weakened via `impK`. -/
theorem deductionN {p : OFml} {Γ : List OFml} {q r : OFml} (h : ProvesN p (q :: Γ) r) :
    ProvesN p Γ (.imp q r) := by
  generalize hΓ : (q :: Γ) = Γ' at h
  induction h generalizing Γ with
  | @hyp Γ' a hmem =>
      subst hΓ
      rcases List.mem_cons.mp hmem with h | h
      · subst h; exact ProvesN.impId Γ a
      · exact ProvesN.mp (ProvesN.impK Γ a q) (ProvesN.hyp h)
  | impId Γ' a => subst hΓ; exact ProvesN.mp (ProvesN.impK _ _ _) (ProvesN.impId _ _)
  | impK Γ' a b => subst hΓ; exact ProvesN.mp (ProvesN.impK _ _ _) (ProvesN.impK _ _ _)
  | impS Γ' a b c => subst hΓ; exact ProvesN.mp (ProvesN.impK _ _ _) (ProvesN.impS _ _ _ _)
  | @mp Γ' a b _ _ ihab iha =>
      subst hΓ
      exact ProvesN.mp (ProvesN.mp (ProvesN.impS _ q a b) (ihab rfl)) (iha rfl)
  | iffIntro hab hba _ _ => subst hΓ; exact ProvesN.mp (ProvesN.impK _ _ _) (ProvesN.iffIntro hab hba)
  | iffMPF h _ => subst hΓ; exact ProvesN.mp (ProvesN.impK _ _ _) (ProvesN.iffMPF h)
  | iffMPB h _ => subst hΓ; exact ProvesN.mp (ProvesN.impK _ _ _) (ProvesN.iffMPB h)
  | necN h _ => subst hΓ; exact ProvesN.mp (ProvesN.impK _ _ _) (ProvesN.necN h)
  | kN Γ' a b => subst hΓ; exact ProvesN.mp (ProvesN.impK _ _ _) (ProvesN.kN _ _ _)
  | fourN Γ' a => subst hΓ; exact ProvesN.mp (ProvesN.impK _ _ _) (ProvesN.fourN _ _)
  | ctxUnfold Γ' φ => subst hΓ; exact ProvesN.mp (ProvesN.impK _ _ _) (ProvesN.ctxUnfold _ _)
  | diagFix Γ' body => subst hΓ; exact ProvesN.mp (ProvesN.impK _ _ _) (ProvesN.diagFix _ _)
  | embed hb => subst hΓ; exact ProvesN.mp (ProvesN.impK _ _ _) (ProvesN.embed hb)
  | engineLeaf hpr => subst hΓ; exact ProvesN.mp (ProvesN.impK _ _ _) (ProvesN.engineLeaf hpr)

/-! ## 3. Derived helpers: `impI` (closed), transitivity, and the diagonal legs. -/

/-- closed deduction: from a hypothesis-derivation `[q] ⊢ r`, get `⊢ q → r`. -/
theorem impIN {p q r : OFml} (h : ProvesN p [q] r) : ProvesN p [] (.imp q r) := deductionN h

/-- implication transitivity over `ProvesN`. -/
theorem impTransN {p : OFml} {Γ : List OFml} {a b c : OFml}
    (hab : ProvesN p Γ (.imp a b)) (hbc : ProvesN p Γ (.imp b c)) : ProvesN p Γ (.imp a c) := by
  have h1 : ProvesN p Γ (.imp a (.imp b c)) := ProvesN.mp (ProvesN.impK _ _ _) hbc
  exact ProvesN.mp (ProvesN.mp (ProvesN.impS Γ a b c) h1) hab

/-- The diagonal fixpoint `ψ ↔ (□ψ → p)` (both directions), for `ψ := betaA body`. Compose `diagFix`
    (`ψ ↔ gApp(⌜ψ⌝)`) with `ctxUnfold` (`gApp(⌜ψ⌝) ↔ (□ψ → p)`). All in `ProvesN`, no hypotheses. -/
theorem diagLegs (p body : OFml) :
    ProvesN p [] (.imp (.betaA body) (.imp (.box (.betaA body)) p)) ∧
    ProvesN p [] (.imp (.imp (.box (.betaA body)) p) (.betaA body)) := by
  have hdiag : ProvesN p [] (.iff (.betaA body) (.gApp (encode (.betaA body)))) :=
    ProvesN.diagFix [] body
  have hctx  : ProvesN p [] (.iff (.gApp (encode (.betaA body)))
                (.imp (.box (.betaA body)) p)) := ProvesN.ctxUnfold [] (.betaA body)
  exact ⟨impTransN (ProvesN.iffMPF hdiag) (ProvesN.iffMPF hctx),
         impTransN (ProvesN.iffMPB hctx) (ProvesN.iffMPB hdiag)⟩

/-! ## 4. `bloeb_native` — the bounded-Löb chain, NATIVE in `ProvesN`.

From the Löb premise `□p → p`, derive `p`, using the diagonal legs (`diagLegs`) and the HBL rules
(`necN`/`kN`/`fourN`) with `deductionN` for the hypothesis discharges. Everything at box = ProvesN. -/

/-- The Löb chain from ABSTRACT diagonal legs `hψf`/`hψb` — reusable, ψ generic. -/
theorem bloeb_from_legs (p ψ : OFml)
    (hψf : ProvesN p [] (.imp ψ (.imp (.box ψ) p)))
    (hψb : ProvesN p [] (.imp (.imp (.box ψ) p) ψ))
    (hLoeb : ProvesN p [] (.imp (.box p) p)) :
    ProvesN p [] p := by
  -- Step A: □ψ → □(□ψ → p)   [necN hψf ; kN], via deduction (context [□ψ]).
  have hA : ProvesN p [] (.imp (.box ψ) (.box (.imp (.box ψ) p))) := by
    have hnec : ProvesN p [] (.box (.imp ψ (.imp (.box ψ) p))) := ProvesN.necN hψf
    have hnecΓ : ProvesN p [.box ψ] (.box (.imp ψ (.imp (.box ψ) p))) := weakenN (by simp) hnec
    have hK : ProvesN p [.box ψ] (.imp (.box ψ) (.box (.imp (.box ψ) p))) :=
      ProvesN.mp (ProvesN.kN _ _ _) hnecΓ
    exact impIN (ProvesN.mp hK (ProvesN.hyp (by simp)))
  -- Step D: □ψ → □p   [A ; fourN ; kN], via deduction.
  have hD : ProvesN p [] (.imp (.box ψ) (.box p)) := by
    have hAΓ : ProvesN p [.box ψ] (.imp (.box ψ) (.box (.imp (.box ψ) p))) := weakenN (by simp) hA
    have hbψ : ProvesN p [.box ψ] (.box ψ) := ProvesN.hyp (by simp)
    have h1 : ProvesN p [.box ψ] (.box (.imp (.box ψ) p)) := ProvesN.mp hAΓ hbψ
    have h2 : ProvesN p [.box ψ] (.box (.box ψ)) := ProvesN.mp (ProvesN.fourN _ _) hbψ
    exact impIN (ProvesN.mp (ProvesN.mp (ProvesN.kN _ _ _) h1) h2)
  -- Step E: □ψ → p   [D gives □p ; hLoeb], via deduction.
  have hE : ProvesN p [] (.imp (.box ψ) p) := by
    have hDΓ : ProvesN p [.box ψ] (.imp (.box ψ) (.box p)) := weakenN (by simp) hD
    have hLΓ : ProvesN p [.box ψ] (.imp (.box p) p) := weakenN (by simp) hLoeb
    have hbψ : ProvesN p [.box ψ] (.box ψ) := ProvesN.hyp (by simp)
    exact impIN (ProvesN.mp hLΓ (ProvesN.mp hDΓ hbψ))
  -- Steps F,G,H: ψ ; □ψ ; p.
  have hF : ProvesN p [] ψ := ProvesN.mp hψb hE
  have hG : ProvesN p [] (.box ψ) := ProvesN.necN hF
  exact ProvesN.mp hE hG

/-- **`bloeb_native`** — bounded Löb with the diagonal supplied by `diagLegs` (`ψ := betaA body`, no
    hypotheses). From `□p → p`, derive `p`, entirely inside `ProvesN`. -/
theorem bloeb_native (p body : OFml)
    (hLoeb : ProvesN p [] (.imp (.box p) p)) :
    ProvesN p [] p :=
  let ⟨hψf, hψb⟩ := diagLegs p body
  bloeb_from_legs p (.betaA body) hψf hψb hLoeb

/-! ## 5. Soundness — `box := ProvesN`, UNIFORM (no bridge). The anti-cheat.

`interpN` reads `box a := ProvesN p [] a` (object-theory provability); `gApp`/`betaA`/base atoms via the
witnessing valuation `Gctx` (as `interp (Gctx p G0)`). The modal rules close DEFINITIONALLY (`necN` via
the derivation); `ctxUnfold`/`diagFix` via `Gctx`; base `embed` via `Proves_sound` lifted (base φ's box
means `Proves`, but a base theorem is also `ProvesN.embed`, so `interp`'s `Proves a → interpN`'s
`ProvesN a` holds POSITIVELY — and base `Proves` conclusions used here are atomic/box-free leaves, so
no negative-box bridge arises). -/

/-- `interpN p G0` — the object interpretation with `box := ProvesN`. -/
noncomputable def interpN (p : OFml) (G0 : Nat → Prop) : OFml → Prop
  | .box a  => ProvesN p [] a
  | .imp a b => interpN p G0 a → interpN p G0 b
  | .iff a b => interpN p G0 a ↔ interpN p G0 b
  | φ        => interp (Gctx p G0) φ

@[simp] theorem interpN_box (p : OFml) (G0 : Nat → Prop) (a : OFml) :
    interpN p G0 (.box a) = ProvesN p [] a := rfl
@[simp] theorem interpN_imp (p : OFml) (G0 : Nat → Prop) (a b : OFml) :
    interpN p G0 (.imp a b) = (interpN p G0 a → interpN p G0 b) := rfl
@[simp] theorem interpN_iff (p : OFml) (G0 : Nat → Prop) (a b : OFml) :
    interpN p G0 (.iff a b) = (interpN p G0 a ↔ interpN p G0 b) := rfl
@[simp] theorem interpN_gApp (p : OFml) (G0 : Nat → Prop) (c : Nat) :
    interpN p G0 (.gApp c) = interp (Gctx p G0) (.gApp c) := rfl
@[simp] theorem interpN_betaA (p : OFml) (G0 : Nat → Prop) (b : OFml) :
    interpN p G0 (.betaA b) = interp (Gctx p G0) (.betaA b) := rfl
@[simp] theorem interpN_eqn (p : OFml) (G0 : Nat → Prop) (x y : Nat) :
    interpN p G0 (.eqn x y) = (x = y) := rfl

/-- Base `Proves a` is sound under `interpN` — proven DIRECTLY (no negative-box bridge). The `D1_nec`
    arm produces `interpN (box a') = ProvesN p [] a'` from the base proof of `a'` via `ProvesN.embed`
    (POSITIVE direction). So base theorems embed soundly regardless of box occurrences. -/
theorem proves_interpN (p : OFml) (G0 : Nat → Prop) (_hp : interp (Gctx p G0) p = interp G0 p)
    (_hp0 : interp G0 p) {a : OFml} (h : Proves a) : interpN p G0 a := by
  induction h with
  | impId a => intro ha; exact ha
  | mp _ _ ihab iha => exact ihab iha
  | impK a b => intro ha _; exact ha
  | impS a b c => intro habc hab ha; exact (habc ha) (hab ha)
  | iffIntro _ _ ihab ihba => exact ⟨ihab, ihba⟩
  | iffMPF _ ihab => exact ihab.mp
  | iffMPB _ ihab => exact ihab.mpr
  | @D1_nec a' hb _ => exact ProvesN.embed hb                       -- interpN (box a') = ProvesN [] a'
  | D2_K a b =>
      -- interpN: ProvesN [](a→b) → ProvesN [] a → ProvesN [] b  (box unfolds); just object mp.
      intro hab ha; exact ProvesN.mp hab ha
  | D3_four a =>
      -- interpN: ProvesN [] a → ProvesN [] (box a); object necessitation.
      intro ha; exact ProvesN.necN ha
  | gammaAx n => show interp (Gctx p G0) (.gamma n (e n)); exact rfl
  | betaGamma body y =>
      show interpN p G0 (.imp (.gamma (encode body) y) (.iff (.betaA body) (.gApp y)))
      intro hg
      have hg' : e (encode body) = y := hg
      show interpN p G0 (.betaA body) ↔ interpN p G0 (.gApp y)
      simp only [interpN_betaA, interpN_gApp, interp]
      rw [hg']

/-- **`provesN_sound`** — `ProvesN p Γ φ` with all of `Γ` true implies `interpN φ`. Uniform box, no
    bridge. The anti-cheat that `ProvesN` proves no falsehood. -/
theorem provesN_sound (p : OFml) (G0 : Nat → Prop)
    (hp : interp (Gctx p G0) p = interp G0 p) (hp0 : interp G0 p)
    (hpN : interpN p G0 p = interp (Gctx p G0) p)     -- `p` box-free (a plays-atom): interpN = interp
    (hEL : ∀ {m : Nat} {ψ : Formula}, Provable m ψ → interpN p G0 (encodeF ψ))  -- engine leaf soundness
    {Γ : List OFml} {φ : OFml} (hΓ : ∀ a ∈ Γ, interpN p G0 a) (h : ProvesN p Γ φ) :
    interpN p G0 φ := by
  induction h with
  | hyp hmem => exact hΓ _ hmem
  | impId _ a => intro ha; exact ha
  | impK _ a b => intro ha _; exact ha
  | impS _ a b c => intro habc hab ha; exact (habc ha) (hab ha)
  | @mp Γ' a b _ _ ihab iha => exact (ihab hΓ) (iha hΓ)
  | iffIntro _ _ ihab ihba => exact ⟨ihab (by simp), ihba (by simp)⟩
  | iffMPF _ ih => exact (ih (by simp)).mp
  | iffMPB _ ih => exact (ih (by simp)).mpr
  | @necN Γ' a hb _ => exact hb                     -- interpN (box a) = ProvesN [] a; = the premise ⊢[] a
  | kN _ a b =>
      -- interpN: ProvesN [](a→b) → ProvesN [] a → ProvesN [] b  (all boxes unfold); object mp.
      intro hab ha; exact ProvesN.mp hab ha
  | fourN _ a =>
      -- interpN: ProvesN [] a → ProvesN [] (box a); object necessitation.
      intro ha; exact ProvesN.necN ha
  | ctxUnfold _ φ =>
      show interpN p G0 (.gApp (encode φ)) ↔ (interpN p G0 (.box φ) → interpN p G0 p)
      rw [interpN_gApp, interp_gApp_Gctx, hpN, hp]
      constructor <;> intro _ _ <;> exact hp0
  | diagFix _ body =>
      show interpN p G0 (.betaA body) ↔ interpN p G0 (.gApp (encode (.betaA body)))
      rw [interpN_betaA, interpN_gApp, interp_betaA_Gctx, interp_gApp_Gctx]
      constructor <;> intro _ _ <;> exact hp0
  | embed hb => exact proves_interpN p G0 hp hp0 hb
  | engineLeaf hpr => exact hEL hpr

/-- **Consistency** (anti-vacuous) — for an `interp`-stable, satisfiable target `p` (the PBLT case:
    `p` a true plays-atom), `ProvesN p [] (eqn 0 1)` is NOT derivable. `interpN (eqn 0 1) = (0 = 1)`,
    valuation-independent and false, so it can't be sound. Confirms the native system + its diagonal /
    HBL rules inject no falsehood. -/
theorem provesN_consistency {p : OFml} {G0 : Nat → Prop}
    (hp : interp (Gctx p G0) p = interp G0 p) (hp0 : interp G0 p)
    (hpN : interpN p G0 p = interp (Gctx p G0) p)
    (hEL : ∀ {m : Nat} {ψ : Formula}, Provable m ψ → interpN p G0 (encodeF ψ)) :
    ¬ ProvesN p [] (.eqn 0 1) := by
  intro h
  have hsound := provesN_sound p G0 hp hp0 hpN hEL (by simp) h
  have : (0 : Nat) = 1 := hsound
  exact absurd this (by decide)

/-! ## 6. `object_pblt_native` — object PBLT, native, from the Löb premise alone.

`bloeb_native` needs only the Löb premise `□p → p` (diagonal legs are `diagFix`/`ctxUnfold`, internal).
So object PBLT for a play-atom `p`: given the Löb premise, `ProvesN p [] p`. This is the object-side
theorem the engine bridge (FWD/BWD) consumes — with the diagonal fully discharged. -/

theorem object_pblt_native (p body : OFml)
    (hLoeb : ProvesN p [] (.imp (.box p) p)) :
    ProvesN p [] p :=
  bloeb_native p body hLoeb

end PD.Reflection
