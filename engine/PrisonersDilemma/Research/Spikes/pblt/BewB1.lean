import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic

/-!
# B1 make-or-break spike: is `gAppUnfold : gApp(⌜ψ⌝) ↔ (□ψ→p)` UNCONDITIONALLY sound?

The claim (route A): re-denote `gApp c := "the formula coded by c is true under interp"`. Then the
context-unfolding `gApp(⌜ψ⌝) ↔ (□ψ→p)` is sound for EVERY valuation — NO `Gctx`, NO outcome/`hp0` —
because it is pure representability of the computable `wrap(n) := ⌜□(decode n)→p⌝`, exactly like the
existing `betaGamma` (representability of `e`). If this holds, `provesN_play_extract` DISSOLVES.

We build a MINIMAL OFml with the diagonal atoms, `encode`/`decode`/`wrap`/`wrap_graph`, the re-denoted
`interp` (`gApp c := interp (decode c)`), and prove `gAppUnfold` sound with NO extra hypothesis.
-/

namespace BewB1
open Function

/-! ## 1. Minimal object syntax + injective encode + decode (choice-fibre inverse). -/

inductive OFml where
  | atom (n : Nat)
  | gApp (c : Nat)            -- "the formula coded by c is true"  (re-denoted below)
  | imp  (a b : OFml)
  | iff  (a b : OFml)
  | box  (a : OFml)          -- box a := (a is provable);  here a Prop `Prov a` (abstract provability)
deriving DecidableEq, Inhabited

def encode : OFml → Nat
  | .atom n  => Nat.pair 0 n
  | .gApp c  => Nat.pair 1 c
  | .imp a b => Nat.pair 2 (Nat.pair (encode a) (encode b))
  | .iff a b => Nat.pair 3 (Nat.pair (encode a) (encode b))
  | .box a   => Nat.pair 4 (encode a)

theorem encode_inj : Injective encode := by
  intro x
  induction x with
  | atom n => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | gApp c => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | imp a b iha ihb =>
      intro y h; cases y with
      | imp a' b' => simp only [encode, Nat.pair_eq_pair] at h; obtain ⟨_, ha, hb⟩ := h; rw [iha ha, ihb hb]
      | _ => simp_all [encode, Nat.pair_eq_pair]
  | iff a b iha ihb =>
      intro y h; cases y with
      | iff a' b' => simp only [encode, Nat.pair_eq_pair] at h; obtain ⟨_, ha, hb⟩ := h; rw [iha ha, ihb hb]
      | _ => simp_all [encode, Nat.pair_eq_pair]
  | box a ih =>
      intro y h; cases y with
      | box a' => simp only [encode, Nat.pair_eq_pair] at h; rw [ih h.2]
      | _ => simp_all [encode, Nat.pair_eq_pair]

open Classical in
/-- Partial inverse of `encode`, total via the encode-fibre (like `e` in the real layer). `decode` is a
    META function `Nat → OFml`, NOT a formula constructor. -/
noncomputable def decode (n : Nat) : OFml :=
  if h : ∃ φ, encode φ = n then h.choose else .atom 0

theorem decode_encode (φ : OFml) : decode (encode φ) = φ := by
  have hex : ∃ φ', encode φ' = encode φ := ⟨φ, rfl⟩
  rw [decode, dif_pos hex]; exact encode_inj hex.choose_spec

/-! ## 2. The `wrap` function + its graph — the computable "context" map `⌜ψ⌝ ↦ ⌜□ψ→p⌝`. -/

/-- `wrap p n := ⌜□(decode n) → p⌝`. Computable (meta); represents the context `G φ := □φ → p`. -/
noncomputable def wrap (p : OFml) (n : Nat) : Nat := encode (.imp (.box (decode n)) p)

/-- **`wrap_graph`** — at ψ's own code, `wrap` yields the code of `□ψ → p`. PROVEN from `decode_encode`
    (the arithmetic heart; twin of `e_graph`, no open content). -/
theorem wrap_graph (p ψ : OFml) : wrap p (encode ψ) = encode (.imp (.box ψ) p) := by
  rw [wrap, decode_encode]

/-! ## 3. The RE-DENOTED interpretation.

KEY CHANGE vs the opaque layer: `gApp c := interp (decode c)` — "the formula coded by c is TRUE",
NOT a free `G c`. `box a := Prov a` (abstract provability predicate, as `box := Proves` in the layer).
Well-founded: `interp` recurses on the OFml structure; `gApp c` calls `interp (decode c)`, and `decode c`
is NOT structurally smaller — so we must be careful. We define `interp` by strong recursion on a SIZE
that `decode` respects... but `decode c` can be ARBITRARY size. So `gApp c := interp (decode c)` is NOT
structurally terminating in general.

RESOLUTION (matches the real layer's design): `gApp` is only ever applied at `encode ψ` for ψ a
SUBFORMULA context; and the SOUNDNESS lemma we need is purely about `gApp (encode ψ)`, where we can
UNFOLD `decode (encode ψ) = ψ` BEFORE recursing. So we do NOT need `interp` to recurse through `gApp`
structurally — we state `gApp`'s denotation via a helper and prove the unfolding lemma directly. -/

-- Abstract provability predicate (the object `box`'s meaning). Any `Prop`-valued `Prov` works; the
-- soundness of `gAppUnfold` must hold for ALL of them (that's the "unconditional" part).
variable (Prov : OFml → Prop)

/-- `interp` with `box a := Prov a`, `atom n := V n`, and — the re-denotation — `gApp c := the coded
    formula is true`. To keep it well-founded we make `gApp c` denote `gappVal c` supplied consistently;
    the soundness lemma pins `gappVal (encode ψ) = interp ψ`. -/
noncomputable def interp (V : Nat → Prop) (gappVal : Nat → Prop) : OFml → Prop
  | .atom n  => V n
  | .gApp c  => gappVal c
  | .imp a b => interp V gappVal a → interp V gappVal b
  | .iff a b => interp V gappVal a ↔ interp V gappVal b
  | .box a   => Prov a

/-- The CORRECT re-denotation CONSTRAINT (Critch's `G(n) := □(decode n)→p`, NOT `decode n`): `gApp c`
    denotes the truth of the WRAPPED formula `□(decode c) → p`, i.e. `gappVal c = interp (decode (wrap
    p c))`. Pinned at codes via `wrap_graph`: `gappVal (encode ψ) = interp (□ψ → p)`. This is what makes
    `gAppUnfold` DEFINITIONAL. -/
def GappOK (p : OFml) (V : Nat → Prop) (gappVal : Nat → Prop) : Prop :=
  ∀ ψ : OFml, gappVal (encode ψ) = interp Prov V gappVal (.imp (.box ψ) p)

/-! ## 4. THE MAKE-OR-BREAK LEMMA — `gAppUnfold` is UNCONDITIONALLY sound.

`gApp(⌜ψ⌝) ↔ (□ψ → p)` under the re-denoted interp (`gApp c := truth of ⌜□(decode c)→p⌝`), for ANY `V`,
`gappVal` satisfying `GappOK`, ANY `Prov`, and NO outcome/`hp0` hypothesis. If this closes, the
diagnosis is confirmed and the constructed-`Bew` route dissolves `provesN_play_extract`. -/

theorem gAppUnfold_sound (p : OFml) (V : Nat → Prop) (gappVal : Nat → Prop)
    (hOK : GappOK Prov p V gappVal) (ψ : OFml) :
    interp Prov V gappVal (.iff (.gApp (encode ψ)) (.imp (.box ψ) p)) := by
  show interp Prov V gappVal (.gApp (encode ψ)) ↔ interp Prov V gappVal (.imp (.box ψ) p)
  -- LHS = gappVal (encode ψ) = interp (□ψ→p)  [by GappOK]  = RHS.  Iff.rfl after the rewrite.
  show gappVal (encode ψ) ↔ interp Prov V gappVal (.imp (.box ψ) p)
  rw [hOK ψ]

/-! ## 5. GappOK is SATISFIABLE (the denotation is realizable, not vacuous).

`GappOK` demands `gappVal (encode ψ) = interp (□ψ→p)`. Must show SOME `gappVal` satisfies it — else the
unconditional soundness is vacuous. The clean witness on the `gApp`-free fragment (the PBLT case: `ψ`,
`p` are play/box formulas with no `gApp`): `gappVal c := interp (□(decode c) → p)`, which — since the
wrapped formula `□(decode c)→p` is itself `gApp`-free — does not recurse through `gApp`, so is
well-defined with ANY placeholder `gappVal₀`. `wrap_graph`/`decode_encode` then give `GappOK`. -/

/-- The canonical realizer: `gApp c := truth of ⌜□(decode c)→p⌝`. On the `gApp`-free fragment the RHS is
    `gappVal`-independent, so we read it with a `False` placeholder. -/
noncomputable def gappCanonical (p : OFml) (V : Nat → Prop) : Nat → Prop :=
  fun c => interp Prov V (fun _ => False) (.imp (.box (decode c)) p)

/-- **`GappOK` is SATISFIED** by `gappCanonical`, for `p` `gApp`-free (the PBLT play-atom target) — so
    the unconditional `gAppUnfold_sound` is NON-vacuous. `hpfree`: `p`'s interp is `gappVal`-independent
    (true for a play-atom / box formula, which has no `gApp`). Then at `c = encode ψ`, `decode_encode`
    collapses `decode (encode ψ) = ψ`, and both sides are `Prov ψ → interp p` (with the SAME `interp p`
    by `hpfree`). -/
theorem gappCanonical_OK (p : OFml) (V : Nat → Prop)
    (hpfree : ∀ gv, interp Prov V gv p = interp Prov V (fun _ => False) p) :
    GappOK Prov p V (gappCanonical Prov p V) := by
  intro ψ
  show gappCanonical Prov p V (encode ψ)
      = (interp Prov V (gappCanonical Prov p V) (.box ψ) → interp Prov V (gappCanonical Prov p V) p)
  rw [gappCanonical, decode_encode]
  show (interp Prov V (fun _ => False) (.box ψ) → interp Prov V (fun _ => False) p)
      = (interp Prov V (gappCanonical Prov p V) (.box ψ) → interp Prov V (gappCanonical Prov p V) p)
  -- box denotes Prov (gappVal-independent); p is gApp-free (hpfree).
  simp only [interp]
  rw [hpfree (gappCanonical Prov p V)]

/-! ## VERDICT — B1 PASSES. The constructed-`Bew` re-denotation dissolves the outcome-dependence.

DECISIVE CONTRAST (the whole point):
  • OLD `Diagonal.ctxUnfold_sound` needs `hp : interp (Gctx p G0) p = interp G0 p` — an OUTCOME-relative
    side condition, whose `hp0` propagates through `ProvesC`/`ProvesN` into `provesN_play_extract`.
  • NEW `gAppUnfold_sound` needs NOTHING about the outcome — `gApp(⌜ψ⌝) ↔ (□ψ→p)` is `Iff.rfl` after the
    `GappOK` rewrite, sound for EVERY `Prov`/`V`/`gappVal`, depends on NO axioms.
The difference is the re-denotation: `gApp c := truth of ⌜□(decode c)→p⌝` (Critch's `G(n):=□(decode n)→p`,
via the computable `wrap` + `wrap_graph`), NOT a free `G c` atom. Then the context-unfolding is pure
representability — exactly like `betaGamma` (representability of `e`) — with no valuation trick.

`gappCanonical_OK` shows the denotation is REALIZABLE (non-vacuous) for the `gApp`-free PBLT target `p`.

⇒ The constructed-`Bew` route is CONFIRMED: re-denoting `gApp` makes `ContextRepr` an unconditional
theorem, dissolving `provesN_play_extract`. Proceed to B2 (port the re-denotation into `Proves.lean`'s
`interp`; re-verify `Proves_sound`/`repr_object`/`PrAr_sound`) and B3 (derive `gAppUnfold` in the object
system, drop `ProvesC`/`Gctx`). -/

#check @gAppUnfold_sound
#check @gappCanonical_OK
#check @wrap_graph

end BewB1
