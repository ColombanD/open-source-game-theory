import ArithS.Agents.Code
import ArithS.Box.Cut
import ArithS.Length.MetaLength
import ArithS.Notation

/-!
# ArithS.Readings — the nine trusted definitions, read at `V = ℕ`

Every trusted definition is stated for an arbitrary model `V` of `𝗜𝚺₁`, because the Löb argument needs
the box INSIDE every model. A reader wants ℕ. This file states, once per definition and under one
name each, what the definition says at `ℕ` — each proved from the lemma that already carries the
fact, so the reading can never drift from the definition. The Tour cites these; the trusted-base
files point here from their reading guides.

| # | definition | its ℕ reading here |
|---|---|---|
| 1 | `swap` | `swap_involutive` — τ is an involution on the symbols |
| 2 | `TAct` | `TAct_sound_nat` — ℕ is a model of `TAct` (soundness, the negative method) |
| 3 | `proofLen` | `proofLen_nat` — on the code of a meta derivation it is the meta symbol count |
| 4 | `LenBox` (`□[k] φ`) | `box_nat` — `□[k] ⌜σ⌝` holds iff some meta derivation of `σ` has length `≤ k` |
| 5 | program codes | `progCode_*` — the engine's constructors map to the tagged codes |
| 6 | descriptions | `description_nat`, `binNumeral_nat` — the term's code is the code's term and it DENOTES the code |
| 7 | the guard | `guard_nat` — the runtime guard code is the code of the guard sentence, true iff `opp` plays `a` against `me` |
| 8 | substitution | `progCode_subst` — `substCode` is the engine's `Prog.subst` on codes |
| 9 | the evaluator | `eval_deterministic_nat`, `eval_monotone_nat` |
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct

/-! ### 1. The transposition is an involution -/

theorem swap_involutive {k : ℕ} (f : LAct.Func k) : swap.func (swap.func f) = f := swap_swap_func f

/-! ### 2. ℕ is a model of `TAct` -/

/-- Soundness: every `TAct`-theorem is true in ℕ (with `c_C ↦ 0`, `c_D ↦ 1`). This is the whole
negative method of the cells: a guard that is FALSE in ℕ is never found. -/
theorem TAct_sound_nat : ℕ↓[LAct] ⊧* TAct := models_TAct

/-! ### 3. The length of a quoted derivation is its meta length -/

theorem proofLen_nat {Γ : Finset (Proposition LAct)} (d : TAct ⟹₂ Γ) :
    proofLen TAct (⌜d⌝ : ℕ) = proofLenMeta d := proofLen_quote d

/-! ### 4. The box at ℕ: "a derivation of length `≤ k` exists" -/

/-- At a meta budget the object-variable box is the parametric-bound box `LenBoxNat`. -/
theorem box_nat_iff_lenBoxNat (k φ : ℕ) :
    □[k] φ ↔ LenBoxNat (codeBound : ℕ → ℕ) k TAct φ := by
  have := lenBox_numeral (V := ℕ) TAct k φ
  rwa [Nat.numeral_eq] at this

/-- **The reading of the box.** `□[k] ⌜σ⌝` holds in ℕ iff there is a (meta) `TAct`-derivation of `σ`
whose symbol count is at most `k`. The code bound `codeBound k` inside `LenBox` is invisible here:
properness guarantees every derivation of length `≤ k` has a code below it. -/
theorem box_nat (k : ℕ) (σ : Sentence LAct) :
    □[k] (⌜σ⌝ : ℕ) ↔ ∃ d : TAct ⟹₂ {(σ : Proposition LAct)}, proofLenMeta d ≤ k := by
  rw [box_nat_iff_lenBoxNat]
  exact ⟨derivation_of_lenBoxNat,
    fun ⟨d, hd⟩ ↦ lenBoxNat_of_derivation smallCodes_LAct smallRelCodes_LAct d hd⟩

/-! ### 5. Program codes: the engine's constructors -/

example (a : PD.Action) : progCode (.const a) = pConst (actCode a) := progCode_const a
example (p : PD.Prog) : progCode (.bot p) = pBot (progCode p) := progCode_bot p
example (p q : PD.Prog) : progCode (.sim p q) = pSim (progCode p) (progCode q) := progCode_sim p q
example (k : ℕ) (φ : PD.Formula) (p q : PD.Prog) :
    progCode (.search k φ p q) = pSearch k (templateCode φ) (progCode p) (progCode q) :=
  progCode_search k φ p q

/-! ### 6. Descriptions: the term of a code, and what it denotes -/

/-- The code of the description term of `x` is `codeTerm x`, and the term denotes `x`. -/
theorem description_nat (x : ℕ) :
    (⌜codeTermMeta x⌝ : ℕ) = codeTerm x ∧
    (codeTermMeta x).val (s := standardModel ℕ) ![] Empty.elim = x :=
  ⟨quote_codeTermMeta_nat x, val_codeTermMeta x⟩

/-- The same for the binary numeral of `n` (the leaves of every description). -/
theorem binNumeral_nat (n : ℕ) :
    (⌜binNumeralMeta n⌝ : ℕ) = binNumeral n ∧
    (binNumeralMeta n).val (s := standardModel ℕ) ![] Empty.elim = n :=
  ⟨quote_binNumeralMeta_nat n, val_binNumeralMeta n⟩

/-! ### 7. The guard: its code, and its truth -/

/-- The runtime guard code of the template "opp plays `a` against me" at the frame `(me, opp)` is the
code of the guard SENTENCE, and that sentence is true in ℕ iff `opp` really plays `a` against `me`. -/
theorem guard_nat (a me opp : ℕ) :
    guardCode (⌜guardTemplate a⌝ : ℕ) me opp = ⌜guardSentence a me opp⌝ ∧
    (ℕ↓[LAct] ⊧ guardSentence a me opp ↔ ∃ n, EvalGraph n opp me opp a) :=
  ⟨(quote_guardSentence a me opp).symm, models_guardSentence_iff a me opp⟩

/-! ### 8. Substitution agrees with the engine -/

example {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp) (hopp : opp ≠ .self ∧ opp ≠ .opp)
    (p : PD.Prog) (hp : fragP p = true) :
    progCode (p.subst me opp) = substCode (progCode me) (progCode opp) (progCode p) :=
  progCode_subst hme hopp p hp

/-! ### 9. The evaluator at ℕ is a deterministic, fuel-monotone partial function -/

theorem eval_deterministic_nat {n n' me opp p a a' : ℕ}
    (h : EvalGraph n me opp p a) (h' : EvalGraph n' me opp p a') : a = a' :=
  EvalGraph.unique' h h'

theorem eval_monotone_nat {n n' me opp p a : ℕ} (h : n ≤ n') (e : EvalGraph n me opp p a) :
    EvalGraph n' me opp p a :=
  EvalGraph.mono_le h e

end ArithS
