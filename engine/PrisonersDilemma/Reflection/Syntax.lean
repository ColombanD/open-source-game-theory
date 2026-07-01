import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic

/-!
# Reflection layer — object syntax `OFml`, Gödel `encode`, self-application `e` (E1a)

The first real module of the PBLT-removal build (`Research/Notes/PBLT_REMOVAL_ROADMAP.md`, step E1),
promoting the de-risked spikes (`Research/Spikes/pblt/Repr*Spike`) into a maintained foundation. This
file is the SYNTAX + the arithmetic of self-reference; `Reflection/Proves.lean` adds `⊢_S`.

We build a **bespoke minimal** object language (decision recorded in the roadmap): just the
constructors the diagonal lemma / `repr` / HBL need, with a genuine injective Gödel code. NOT a
Mathlib `FirstOrder.Language` (Mathlib has syntax+semantics but no proof theory, so we'd hand-build
`⊢`/`Bew` either way — bespoke is lighter and matches the spikes).

This module is self-contained (only Mathlib `Nat.Pairing`), NOT yet root-imported — the reflection
layer builds independently of the engine until E6 wires `PBLT` to it.
-/

namespace PD.Reflection

/-! ## 1. The object formula language.

`OFml` is `Lang_{r+1}`-skeleton for the PBLT use (one parameter `k`, kept META as in our PBLT
formulation, so an `OFml` is the `k`-fibre statement). Constructors:
  • `atom n`     — an opaque object atom keyed by a code `n` (the encoded engine `plays`-formula, the
                   target predicate `G`, etc.; concrete meaning supplied by the interpretation later);
  • `slot`       — the diagonal quote-slot `⌜-⌝`;
  • `quoteC c`   — a literal code numeral (`numeral c`);
  • `gamma x y`  — the graph predicate `Γ_e(numeral x, numeral y)`;
  • `eqn x y`    — numeral equality `numeral x = numeral y`;
  • `betaA n`    — the self-evaluation atom `β(numeral n)` (meaning `G(e n)`);
  • `gApp c`     — the target `G(numeral c)`;
  • `imp` / `iff` / `box` — connectives + the modality (`box` = provability). -/

inductive OFml where
  | atom   (n : Nat)
  | slot
  | quoteC (c : Nat)
  | gamma  (x y : Nat)
  | eqn    (x y : Nat)
  | betaA  (body : OFml)     -- β applied to the code of `body` (a subformula, so `slot` can sit inside)
  | gApp   (c : Nat)
  | imp    (a b : OFml)
  | iff    (a b : OFml)
  | box    (a : OFml)
deriving DecidableEq, Inhabited

/-! ## 2. A genuine, PROVABLY injective Gödel code `encode : OFml → Nat`.

Head-tagged `Nat.pair` scheme — distinct constructors land in distinct tag classes, so injectivity
follows constructor-wise. (Promoted & extended from `ReprConcreteSpike.encode`.) -/

def encode : OFml → Nat
  | .atom n     => Nat.pair 0 n
  | .slot       => Nat.pair 1 0
  | .quoteC c   => Nat.pair 2 c
  | .gamma x y  => Nat.pair 3 (Nat.pair x y)
  | .eqn x y    => Nat.pair 4 (Nat.pair x y)
  | .betaA body => Nat.pair 5 (encode body)
  | .gApp c     => Nat.pair 6 c
  | .imp a b    => Nat.pair 7 (Nat.pair (encode a) (encode b))
  | .iff a b    => Nat.pair 8 (Nat.pair (encode a) (encode b))
  | .box a      => Nat.pair 9 (encode a)

theorem encode_inj : Function.Injective encode := by
  intro x
  induction x with
  | atom n => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | slot => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | quoteC c => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | gamma x' y' => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | eqn x' y' => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | betaA body ih =>
      intro y h; cases y with
      | betaA body' => simp only [encode, Nat.pair_eq_pair] at h; exact congrArg _ (ih h.2)
      | _ => simp_all [encode, Nat.pair_eq_pair]
  | gApp c => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | imp a b iha ihb =>
      intro y h; cases y with
      | imp a' b' =>
          simp only [encode, Nat.pair_eq_pair] at h
          obtain ⟨ha, hb⟩ := h.2; exact congr (congrArg _ (iha ha)) (ihb hb)
      | _ => simp_all [encode, Nat.pair_eq_pair]
  | iff a b iha ihb =>
      intro y h; cases y with
      | iff a' b' =>
          simp only [encode, Nat.pair_eq_pair] at h
          obtain ⟨ha, hb⟩ := h.2; exact congr (congrArg _ (iha ha)) (ihb hb)
      | _ => simp_all [encode, Nat.pair_eq_pair]
  | box a iha =>
      intro y h; cases y with
      | box a' => simp only [encode, Nat.pair_eq_pair] at h; exact congrArg _ (iha h.2)
      | _ => simp_all [encode, Nat.pair_eq_pair]

/-! ## 3. Substitution into the quote-slot, self-application, and the `e`-graph.

(Promoted from `ReprConcreteSpike`; `plug`/`selfApply`/`e`/`e_graph` are unchanged in spirit, now over
the full `OFml`.) `plug c φ` substitutes the literal code `c` for every `slot` in `φ`; `selfApply θ`
plugs θ's OWN code. `e` is the substitution-on-codes function with the graph theorem. -/

def plug (c : Nat) : OFml → OFml
  | .slot       => .quoteC c
  | .atom n     => .atom n
  | .quoteC d   => .quoteC d
  | .gamma x y  => .gamma x y
  | .eqn x y    => .eqn x y
  | .betaA body => .betaA (plug c body)
  | .gApp d     => .gApp d
  | .imp a b    => .imp (plug c a) (plug c b)
  | .iff a b    => .iff (plug c a) (plug c b)
  | .box a      => .box (plug c a)

/-- `selfApply θ = θ(⌜θ⌝, -)` — plug θ's own code for its slot. -/
def selfApply (θ : OFml) : OFml := plug (encode θ) θ

open Classical in
/-- The substitution-on-codes function `e` (tex's `e`), realized via the encode-fibre (total by
    injectivity). Only ever applied at `n = encode θ`. -/
noncomputable def e (n : Nat) : Nat :=
  if h : ∃ θ, encode θ = n then encode (selfApply h.choose) else 0

/-- **The `e`-graph** — `e (encode θ) = encode (selfApply θ)`, PROVEN from injectivity (not defeq).
    The arithmetic heart of `repr`. -/
theorem e_graph (θ : OFml) : e (encode θ) = encode (selfApply θ) := by
  have hex : ∃ θ', encode θ' = encode θ := ⟨θ, rfl⟩
  rw [e, dif_pos hex]; rw [show hex.choose = θ from encode_inj hex.choose_spec]

end PD.Reflection
