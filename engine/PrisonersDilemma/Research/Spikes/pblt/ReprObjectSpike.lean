import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic

/-!
# Path A, step "object-level repr" — lift `repr` from meta-`Prop` to `⊢_S` derivability

`ReprConcreteSpike` proved the ARITHMETIC core: a real injective code, a real `e`, and
`e_graph : e (encode θ) = encode (selfApply θ)` (no defeq). But its `repr_proved` was a *Lean* `↔`
(`G : Nat → Nat → Prop` meta-level). The tex's `repr` is stronger: derivability INSIDE the object
theory `S`,
  `⊢_S  β(⌜θ⌝, k)  ↔  G(⌜selfApply θ⌝, k)`,
which needs `e` represented in `S` by a graph predicate `Γ_e` and `S` reasoning with it (Leibniz
substitution of equal numerals).

This spike builds the SMALLEST honest object system that lets this be a real DERIVATION:
  • an object `OFml` with a two-place graph atom `gamma x y` (Γ_e), equality `eqn`, the target `gApp`
    (G(·,k)) and the composite `betaAtom` (β(·,k)), plus `iff`/`imp`;
  • an inductive `Proves : OFml → Prop` (`⊢_S`) with STANDARD rules + the `Γ_e` representability
    axiom-scheme — `repr` is then DERIVED, not a rule;
  • a soundness interpretation `⟦·⟧` + `Proves_sound`, so we CHECK no false-proving rule was added
    (the anti-cheat: `repr` must follow from sound rules, not be smuggled in).

The arithmetic of `e`/`encode`/`e_graph` is reused verbatim. NOT root-imported.
`lake env lean PrisonersDilemma/Research/Spikes/pblt/ReprObjectSpike.lean`
-/

namespace PD.ReprObjectSpike

/-! ## 0. Reused arithmetic (identical to ReprConcreteSpike): code, e, e_graph. -/

inductive Fml where
  | slot | param | quote (c : Nat) | imp (a b : Fml)
deriving DecidableEq

instance : Inhabited Fml := ⟨.slot⟩

def encode : Fml → Nat
  | .slot      => Nat.pair 0 0
  | .param     => Nat.pair 1 0
  | .quote c   => Nat.pair 2 c
  | .imp a b   => Nat.pair 3 (Nat.pair (encode a) (encode b))

theorem encode_inj : Function.Injective encode := by
  intro x
  induction x with
  | slot => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | param => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | quote c => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | imp a b iha ihb =>
    intro y h; cases y with
    | imp a' b' =>
      simp only [encode, Nat.pair_eq_pair] at h
      obtain ⟨ha, hb⟩ := h.2
      exact congr (congrArg _ (iha ha)) (ihb hb)
    | _ => simp_all [encode, Nat.pair_eq_pair]

def plug (c : Nat) : Fml → Fml
  | .slot => .quote c | .param => .param | .quote d => .quote d
  | .imp a b => .imp (plug c a) (plug c b)

def selfApply (θ : Fml) : Fml := plug (encode θ) θ

open Classical in
noncomputable def e (n : Nat) : Nat :=
  if h : ∃ θ, encode θ = n then encode (selfApply h.choose) else 0

theorem e_graph (θ : Fml) : e (encode θ) = encode (selfApply θ) := by
  have hex : ∃ θ', encode θ' = encode θ := ⟨θ, rfl⟩
  rw [e, dif_pos hex]; rw [show hex.choose = θ from encode_inj hex.choose_spec]

/-! ## 1. The OBJECT formula language `OFml` (what `⊢_S` ranges over).

Atoms we need for `repr` (parameter `k` kept meta, as in our PBLT formulation — so `OFml` is the
`k`-fibre `Lang_r` predicate-as-statement). Numerals are codes `Nat`.
  • `gApp c`     — `G(numeral c, k)`           (the target, as an opaque object atom)
  • `betaAtom n` — `β(numeral n, k)`           (the composite β; its MEANING is `G(e n, k)`)
  • `gamma x y`  — `Γ_e(numeral x, numeral y)` (the graph predicate atom)
  • `eqn x y`    — `numeral x = numeral y`     (object equality of numerals) -/

inductive OFml where
  | gApp     (c : Nat)
  | betaAtom (n : Nat)
  | gamma    (x y : Nat)
  | eqn      (x y : Nat)
  | imp      (a b : OFml)
  | iff      (a b : OFml)        -- real biconditional constructor (honest interpretation in §3)
deriving DecidableEq

/-! ## 2. `⊢_S` — inductive object provability with STANDARD rules + the `Γ_e` scheme.

The rules are exactly those the `repr` derivation uses, each SOUND (checked in §3):
  • `betaDef`   — β's DEFINING equivalence: `⊢ β(n) ↔ G(e n)` reduced to the graph: actually we make β
    transparent via `gamma`: `⊢ β(n) ↔ (∃-free) G(y) where Γ_e(n,y)`. To keep it first-orderish without
    quantifiers we use the FUNCTIONAL form: `betaGamma : ⊢ Γ_e(n,y) → (β(n) ↔ G(y))`.
  • `gammaAx`   — representability: `⊢ Γ_e(⌜θ⌝, e ⌜θ⌝)`  (the graph holds at the true value).
  • `iffIntro/iffMP`, `impId`, Leibniz `eqLeibniz` for substituting equal numerals in `gApp`.
We DERIVE `repr` from these. -/

inductive Proves : OFml → Prop where
  -- implication: identity + modus ponens (enough plumbing)
  | impId (a : OFml) : Proves (.imp a a)
  | mp {a b : OFml} : Proves (.imp a b) → Proves a → Proves b
  -- ↔ as a pair of directions (abstract; `iff`'s body is never inspected)
  | iffIntro {a b : OFml} : Proves (.imp a b) → Proves (.imp b a) → Proves (a.iff b)
  | iffMPF {a b : OFml} : Proves (a.iff b) → Proves (.imp a b)
  | iffMPB {a b : OFml} : Proves (a.iff b) → Proves (.imp b a)
  -- the Γ_e REPRESENTABILITY axiom-scheme: the graph holds at the true value `e n`.
  | gammaAx (n : Nat) : Proves (.gamma n (e n))
  -- β's functional definition via the graph: if Γ_e(n,y) then β(n) ↔ G(y).
  | betaGamma (n y : Nat) : Proves (.imp (.gamma n y) ((OFml.betaAtom n).iff (OFml.gApp y)))
  -- Leibniz: equal numerals are interchangeable inside `gApp` (not actually needed if we go via β,
  -- but included to show the substitution principle is available and sound).
  | gAppCongr {x y : Nat} : Proves (.eqn x y) → Proves (.imp (.gApp x) (.gApp y))

/-! ## 3. Soundness — the ANTI-CHEAT. `⟦·⟧` interprets `OFml` in the standard model; every rule is
sound, so `Proves φ → ⟦φ⟧`. If `repr` then follows, it is HONEST (no false-proving rule). -/

/-- Standard interpretation, parametric in the real meaning `G : Nat → Prop` of `G(·,k)`. `β`'s
    meaning is `G (e n)` (the tex definition); `Γ_e`'s meaning is the real graph `e x = y`. -/
def interp (G : Nat → Prop) : OFml → Prop
  | .gApp c     => G c
  | .betaAtom n => G (e n)
  | .gamma x y  => e x = y
  | .eqn x y    => x = y
  | .imp a b    => interp G a → interp G b
  | .iff a b    => interp G a ↔ interp G b

theorem Proves_sound (G : Nat → Prop) {φ : OFml} (h : Proves φ) : interp G φ := by
  induction h with
  | impId a => intro ha; exact ha
  | mp _ _ ihab iha => exact ihab iha
  | iffIntro _ _ ihab ihba => exact ⟨ihab, ihba⟩
  | iffMPF hab ihab => exact ihab.mp
  | iffMPB hab ihab => exact ihab.mpr
  | gammaAx n => exact rfl
  | betaGamma n y => intro hg; simp only [interp] at hg ⊢; rw [hg]
  | gAppCongr _ ih => intro hx; simp only [interp] at ih ⊢; rw [← ih]; exact hx

/-! ## 4. THE OBJECT-LEVEL `repr` — DERIVED from the rules above (the payoff). -/

/-- **`repr` as `⊢_S`** — for every `θ`, the object theory proves `β(⌜θ⌝) ↔ G(⌜selfApply θ⌝)`.
    DERIVED: instantiate `gammaAx` at `n = encode θ` to get `⊢ Γ_e(⌜θ⌝, e ⌜θ⌝)`; rewrite
    `e ⌜θ⌝ = ⌜selfApply θ⌝` by `e_graph`; feed to `betaGamma` via `mp`. No new rule, no defeq cheat. -/
theorem repr_object (θ : Fml) :
    Proves ((OFml.betaAtom (encode θ)).iff (OFml.gApp (encode (selfApply θ)))) := by
  have hg : Proves (.gamma (encode θ) (e (encode θ))) := Proves.gammaAx (encode θ)
  rw [e_graph θ] at hg
  exact Proves.mp (Proves.betaGamma (encode θ) (encode (selfApply θ))) hg

/-! ## VERDICT — object-level `repr` CLOSES, HONESTLY (sound rules, no smuggling).

`repr_object` and `Proves_sound` are sorry-free on the 3 standard axioms. So `⊢_S β(⌜θ⌝) ↔
G(⌜selfApply θ⌝)` is a real DERIVATION in an object proof system, and that system is SOUND.

**Anti-cheat audit (the rules `repr` rests on are legitimate, not the conclusion in disguise):**
  • `gammaAx : ⊢ Γ_e(n, e n)` — "the graph holds at the true value." This is exactly the
    representability fact tex §rep grants for any computable `e` (Cori-Lascar 6.8). Honest.
  • `betaGamma : ⊢ Γ_e(n,y) → (β(n) ↔ G(y))` — since `β(n)` MEANS `G(e n)` and `Γ_e(n,y)` means
    `e n = y`, this is just `e n = y → (G(e n) ↔ G(y))`: LEIBNIZ congruence of `G` under equality, a
    theorem of any first-order theory. NOT a bespoke axiom, NOT `repr` in disguise.
  • `Proves_sound` PROVES both true in the standard model (`gammaAx`↦`rfl`, `betaGamma`↦`rw`), so no
    rule can derive a falsehood. `repr` therefore follows from {representability + congruence}, exactly
    as the tex intends — it is derived, not assumed.

`repr` uses `e_graph` ONLY to instantiate the numeral (`e ⌜θ⌝ ⇝ ⌜selfApply θ⌝`), i.e. the proved
arithmetic fact picks which true instance of `gammaAx` to feed `betaGamma`. No defeq, no axiom.

**NET — `repr` is fully discharged at the object level (modulo realism of the toy `S`).** Combined
with `ReprConcreteSpike` (the arithmetic core) and `DiagonalLemmaSpike` (the diagonal shape), the
`repr`/`diag` half of PBLT-removal is de-risked end-to-end: real code, real `e`, real graph, real
object derivation, soundness-checked. What this toy `S` ELIDES (the honest remaining scope): it has no
quantifiers (the parameter `k` and `∀y` in `Γ_e`'s functionality are meta), and `gammaAx`/`betaGamma`
are schemes asserted for the specific atoms — a faithful `S ⊇ PA` must PROVE them from PA + the
arithmetized `Bew`/`Γ_e` construction. But the LOGICAL CONTENT (how `repr` is derived, and that it is
sound) is now machine-checked. The wall has moved from "is `repr` provable?" (answered: yes) to "wire
`Γ_e`/`gammaAx`/`betaGamma` into a real arithmetized `S`" (PA-metamathematics engineering).

**Next sub-step:** the rest of the chain — HBL D1–D3 over the object box, then instantiate `BPSb`
(`pblt_of_bpsb`) with this `Proves`/`diag`/`repr`, getting object-S PBLT as a theorem (roadmap 6–7);
in parallel, spike the faithfulness bridge (roadmap 8). -/

#check @repr_object
#check @Proves_sound

end PD.ReprObjectSpike
