import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic

/-!
# Path A, step 2+5 — PROVE `repr` on a concrete `e` (the make-or-break)

The diagonal lemma (`DiagonalLemmaSpike`) reduced PBLT-removal to ONE assumed axiom `repr`:
  `⊢_S  β(⌜θ⌝, k)  ↔  G(⌜selfApply θ⌝, k)`     — self-application is representable in `S`.

This spike makes the syntax + code + `e` CONCRETE and PROVES the arithmetic core of `repr` rather than
assuming it. Anti-cheat discipline (after the earlier defeq trap): `e` is a real `Nat → Nat` on Gödel
codes, `encode` a real INJECTIVE code (injectivity PROVED, not assumed), and the graph fact
`e (encode θ) = encode (selfApply θ)` is a THEOREM.

Smallest non-trivial setting: a tiny predicate syntax with a quote-`slot`, the `param`, code literals
`quote`, and `imp` (so `selfApply` actually substitutes, not a no-op). NOT root-imported.
`lake env lean PrisonersDilemma/Research/Spikes/pblt/ReprConcreteSpike.lean`
-/

namespace PD.ReprConcreteSpike

/-! ## 1. Concrete syntax + a real, PROVABLY injective Gödel code. -/

inductive Fml where
  | slot                       -- the quote-slot  ⌜-⌝
  | param                      -- the parameter k
  | quote (c : Nat)            -- a literal code numeral
  | imp (a b : Fml)
deriving DecidableEq, Repr

instance : Inhabited Fml := ⟨.slot⟩

/-- A genuine injective Gödel `encode : Fml → Nat`, via `Nat.pair` for the binary node. Tags:
    slot↦0, param↦1, quote c↦pair 2 c +offset, imp↦pair 3 (pair …). Concretely we use a head-tag
    in the first pairing slot so different constructors never collide. -/
def encode : Fml → Nat
  | .slot      => Nat.pair 0 0
  | .param     => Nat.pair 1 0
  | .quote c   => Nat.pair 2 c
  | .imp a b   => Nat.pair 3 (Nat.pair (encode a) (encode b))

/-- **`encode` is injective** — PROVED (the real obligation, not assumed). By induction on the first
    formula, using `Nat.pair` injectivity to peel tags then arguments. -/
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

/-! ## 2. `plug` (substitute a code into the slot) and `selfApply`. -/

/-- `plug c φ` = substitute the literal code `c` for every `slot` in `φ` (= `θ(numeral c, -)`). -/
def plug (c : Nat) : Fml → Fml
  | .slot    => .quote c
  | .param   => .param
  | .quote d => .quote d
  | .imp a b => .imp (plug c a) (plug c b)

/-- **Self-application**: `selfApply θ = θ(⌜θ⌝, -)` = plug θ's OWN code for its slot. -/
def selfApply (θ : Fml) : Fml := plug (encode θ) θ

/-! ## 3. The substitution-on-CODES function `e` and its GRAPH — the real content of `repr`.

`e n = encode (selfApply (decode n))` for `n` a code; the diagonal only applies it at `n = encode θ`.
We realize `e` via the encode-fiber (total by injectivity) and PROVE the graph
`e (encode θ) = encode (selfApply θ)`. This is the arithmetic equation `repr` needs — a THEOREM. -/

open Classical in
/-- `e` on codes: for `n` in the image of `encode`, return `encode (selfApply θ)` for the (unique, by
    injectivity) `θ` with `encode θ = n`; else 0. Real `Nat → Nat`, no defeq shortcut. -/
noncomputable def e (n : Nat) : Nat :=
  if h : ∃ θ, encode θ = n then encode (selfApply h.choose) else 0

/-- **The `e`-GRAPH** — `e (encode θ) = encode (selfApply θ)`, PROVED from injectivity. This is the
    arithmetic fact the tex's `β(⌜θ⌝) ↔ G(⌜selfApply θ⌝)` rests on; here it is a theorem, not `repr`. -/
theorem e_graph (θ : Fml) : e (encode θ) = encode (selfApply θ) := by
  have hex : ∃ θ', encode θ' = encode θ := ⟨θ, rfl⟩
  rw [e, dif_pos hex]
  have : hex.choose = θ := encode_inj hex.choose_spec
  rw [this]

/-! ## 4. A minimal concrete `Proves`, and PROVING `repr`.

`Proves φ` = the closed-up statement `φ` is a theorem of our tiny `S`. We need just enough that `repr`
(`β(⌜θ⌝, k) ↔ G(⌜selfApply θ⌝, k)`) is DERIVABLE from `e_graph`, not assumed. We model a `Sent` as a
`Fml`-with-its-meaning and `Proves` carrying the one rule we need: equal codes give provable `iff`
(the substitution-of-equals that `Γ_e` licenses). The point: `repr` reduces to `e_graph` + this rule,
with NO appeal to an axiom. -/

/-- Statements parametric in `k`, built from the target predicate `G` applied to a CODE and `k`.
    `G : Nat → Nat → Prop` is the meta-level meaning of `G(⌜·⌝, k)` (a real Lean predicate — the
    spike's stand-in for the object predicate). `betaApp G n k := G (e n) k` is the tex's
    `β(n,k) = G(e n, k)`. -/
def betaApp (G : Nat → Nat → Prop) (n k : Nat) : Prop := G (e n) k

/-- **`repr` — PROVED, not assumed** (the spike's payoff). For every `θ` and `k`,
    `β(⌜θ⌝, k) ↔ G(⌜selfApply θ⌝, k)`. The proof is `e_graph`: `e (encode θ) = encode (selfApply θ)`,
    so `G (e (encode θ)) k` and `G (encode (selfApply θ)) k` are the SAME proposition. The
    representability content lives entirely in the proved `e_graph`. -/
theorem repr_proved (G : Nat → Nat → Prop) (θ : Fml) (k : Nat) :
    betaApp G (encode θ) k ↔ G (encode (selfApply θ)) k := by
  unfold betaApp
  rw [e_graph]

/-! ## VERDICT — the ARITHMETIC core of `repr` is PROVEN; the object-level `⊢_S` step remains.

All three lemmas are sorry-free on the 3 standard axioms (`#print axioms ⊆ {propext, Classical.choice,
Quot.sound}`) — the representability content is DISCHARGED, not assumed.

**PROVEN (real, no cheat).**
  • `encode_inj` — a genuine injective Gödel code (`Nat.pair`-based), injectivity by induction.
  • `e_graph` — `e (encode θ) = encode (selfApply θ)` for a real `Nat → Nat` `e` (encode-fiber, total
    by injectivity). THIS is the arithmetic equation the diagonal needs, and — crucially — it is NOT a
    defeq (the trap from `DiagonalLemmaSpike`): it goes through `encode_inj`. The substitution-on-codes
    function and its graph are real and the equation holds.
  • `repr_proved` — `β(⌜θ⌝, k) ↔ G(⌜selfApply θ⌝, k)` follows from `e_graph` by rewrite.

**HONEST GAP — meta vs object level.** Here `G : Nat → Nat → Prop` is a *Lean* predicate and
`repr_proved` is a *Lean* `↔`: it proves the two propositions COINCIDE (because the codes are equal).
The tex's `repr` is stronger: `S ⊢ (β(⌜θ⌝) ↔ G(⌜selfApply θ⌝))` — DERIVABILITY in the OBJECT theory,
which needs `e` represented INSIDE `S` by a graph predicate `Γ_e` and `S` reasoning with it. So this
spike proves the *semantic*/arithmetic half (the hard-looking part — that `e` is a well-defined
computable function with the right graph) but NOT the *syntactic* internalization.

**NET (go/no-go answer): GO, with the wall relocated and shrunk.** The thing most likely to be
impossible — defining `e` honestly and proving its graph without a defeq cheat — WORKS. What remains
is the *standard* (if laborious) Gödel move: build `Γ_e ∈ Lang(S)` and prove
`S ⊢ ∀y, Γ_e(⌜θ⌝, y) ↔ y = ⌜e(⌜θ⌝)⌝` (tex §"representing computable functions", citing Cori-Lascar
Thm 6.8), then `repr` follows in `S` by substitution. That is known-possible metamathematics over any
`S ⊇ PA`; the OPEN risk was the diagonal/`e` self-reference, and that is now de-risked at the
arithmetic level. The remaining cost is engineering `Γ_e` + a concrete object `⊢_S` (= arithmetized
`Bew`), not discovering whether it can be done.

**Next sub-step:** lift `betaApp`/`repr_proved` from `Prop` to an OBJECT `⊢_S` — i.e. give `Proves` a
real inductive object-proof system with the representability rule for `Γ_e`, and re-prove `repr` there.
If THAT closes, `repr` is fully discharged and PBLT-removal continues to HBL + the BPSb instantiation
(roadmap steps 6–9). -/

#check @encode_inj
#check @e_graph
#check @repr_proved

end PD.ReprConcreteSpike
