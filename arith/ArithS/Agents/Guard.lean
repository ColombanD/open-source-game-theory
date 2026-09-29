import ArithS.Agents.Prog
import ArithS.Box.BewV
import ArithS.Agents.Bnum
import ArithS.Agents.ProgT

/-!
# ArithS.Guard — the runtime guard sentence, on codes

`search k g p q` evaluated at `(me, opp)` searches for a proof of the sentence obtained by
filling the stored template `g` (a formula code with SIX free variables — the me-triple
`x₁ u₁ w₁` in `#0 #1 #2`, the opp-triple `x₂ u₂ w₂` in `#3 #4 #5`; roadmap M3 step (a)) with
the CANONICAL DESCRIPTIONS of `me` and `opp`:

* a program `x` is described by the triple `(progT (dnum x), dU x, dW x)`, meaning
  `relabel (dU x) (dW x) (dnum x)`: `dnum x = min x (swapcode x)` as the STRUCTURAL TERM of
  its code over the polynomial pairing, with binary-numeral leaves (`ArithS.ProgT`, since
  2026-09-11 — roadmap M4 item U0: a searcher's description is then the `k`-instance of a
  fixed term, `ArithS.Instance`; before that the binary numeral `bnum (dnum x)` of the whole
  code, `ArithS.Bnum`, length `O(log x)` — Critch's assumption (b); with unary numerals the
  description of a searcher of budget `k` is longer than `k` and no search can ever succeed,
  the retired `Vacuity.lean`, commit 470ee43), and the two term codes `dU x, dW x` are the
  constant symbols `c_C, c_D` in the order that reconstructs `x`, or the numerals `0, 1` in
  the tie case `x = swapcode x`.

So the swap of the two constants turns the description of `x` into that of `swapcode x`
SYNTACTICALLY, in every case. `guardCode g me opp` is Σ₁-definable; the corresponding
meta sentence and the code equation are in `ArithS.Template`. The action term
`actTermCode a` (`c_a` for `a ∈ {0, 1}`) is kept for the closed template instances
`guardTemplate a` of `ArithS.Template`; it no longer enters `descVec`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Term codes of the action constants -/

/-- The term code of the constant symbol with code `2 + u` (`c_C` for `u = 0`, `c_D` for `u = 1`). -/
noncomputable def csym (u : V) : V := ^func 0 (2 + u) 0

noncomputable def csymGraph : 𝚺₁.Semisentence 2 := .mkSigma “y u. !qqFuncDef y 0 (2 + u) 0”

instance csym.defined : 𝚺₁-Function₁[V] csym via csymGraph := .mk fun v ↦ by
  simp [csymGraph, csym]

/-! ### Canonical descriptions -/

/-- The canonical numeral of the τ-orbit of `x`. -/
noncomputable def dnum (x : V) : V := if x ≤ swapcode x then x else swapcode x

/-- First re-valuation term: `c_C` if `x` is canonical, `c_D` if `swapcode x` is, `0` on a tie. -/
noncomputable def dU (x : V) : V :=
  if x < swapcode x then csym 0 else if swapcode x < x then csym 1 else numeral 0

/-- Second re-valuation term: `c_D` if `x` is canonical, `c_C` if `swapcode x` is, `1` on a tie. -/
noncomputable def dW (x : V) : V :=
  if x < swapcode x then csym 1 else if swapcode x < x then csym 0 else numeral 1

/-- The action term: `c_a` for `a ∈ {0, 1}`, the numeral otherwise. -/
noncomputable def actTermCode (a : V) : V :=
  if a = 0 then csym 0 else if a = 1 then csym 1 else numeral a

section definability

noncomputable def dnumGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ s, !relabelDef s 1 0 x ∧ (x ≤ s → y = x) ∧ (s < x → y = s)”

instance dnum.defined : 𝚺₁-Function₁[V] dnum via dnumGraph := .mk fun v ↦ by
  suffices (v 1 ≤ swapcode (v 1) → v 0 = v 1) ∧ (swapcode (v 1) < v 1 → v 0 = swapcode (v 1)) ↔
      v 0 = dnum (v 1) by simpa [dnumGraph]
  unfold dnum
  generalize swapcode (v 1) = s
  rcases le_or_gt (v 1) s with h | h
  · rw [if_pos h]
    exact ⟨fun H ↦ H.1 h, fun H ↦ ⟨fun _ ↦ H, fun h' ↦ absurd h' (not_lt.mpr h)⟩⟩
  · rw [if_neg (not_le.mpr h)]
    exact ⟨fun H ↦ H.2 h, fun H ↦ ⟨fun h' ↦ absurd h' (not_le.mpr h), fun _ ↦ H⟩⟩

noncomputable def dUGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ s, !relabelDef s 1 0 x ∧ ∃ c0, !csymGraph c0 0 ∧ ∃ c1, !csymGraph c1 1 ∧ ∃ z, !numeralGraph z 0 ∧
    (x < s → y = c0) ∧ (s < x → y = c1) ∧ (x = s → y = z)”

instance dU.defined : 𝚺₁-Function₁[V] dU via dUGraph := .mk fun v ↦ by
  suffices (v 1 < swapcode (v 1) → v 0 = csym 0) ∧ (swapcode (v 1) < v 1 → v 0 = csym 1) ∧
      (v 1 = swapcode (v 1) → v 0 = numeral 0) ↔ v 0 = dU (v 1) by simpa [dUGraph]
  unfold dU
  generalize swapcode (v 1) = s
  rcases lt_trichotomy (v 1) s with h | h | h
  · rw [if_pos h]
    exact ⟨fun H ↦ H.1 h, fun H ↦ ⟨fun _ ↦ H, fun h' ↦ absurd h' (lt_asymm h), fun h' ↦ absurd h' h.ne⟩⟩
  · subst h; rw [if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _)]
    exact ⟨fun H ↦ H.2.2 rfl, fun H ↦ ⟨fun h' ↦ absurd h' (_root_.lt_irrefl _), fun h' ↦ absurd h' (_root_.lt_irrefl _), fun _ ↦ H⟩⟩
  · rw [if_neg (lt_asymm h), if_pos h]
    exact ⟨fun H ↦ H.2.1 h, fun H ↦ ⟨fun h' ↦ absurd h' (lt_asymm h), fun _ ↦ H, fun h' ↦ absurd h' h.ne'⟩⟩

noncomputable def dWGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ s, !relabelDef s 1 0 x ∧ ∃ c0, !csymGraph c0 0 ∧ ∃ c1, !csymGraph c1 1 ∧ ∃ z, !numeralGraph z 1 ∧
    (x < s → y = c1) ∧ (s < x → y = c0) ∧ (x = s → y = z)”

instance dW.defined : 𝚺₁-Function₁[V] dW via dWGraph := .mk fun v ↦ by
  suffices (v 1 < swapcode (v 1) → v 0 = csym 1) ∧ (swapcode (v 1) < v 1 → v 0 = csym 0) ∧
      (v 1 = swapcode (v 1) → v 0 = numeral 1) ↔ v 0 = dW (v 1) by simpa [dWGraph]
  unfold dW
  generalize swapcode (v 1) = s
  rcases lt_trichotomy (v 1) s with h | h | h
  · rw [if_pos h]
    exact ⟨fun H ↦ H.1 h, fun H ↦ ⟨fun _ ↦ H, fun h' ↦ absurd h' (lt_asymm h), fun h' ↦ absurd h' h.ne⟩⟩
  · subst h; rw [if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _)]
    exact ⟨fun H ↦ H.2.2 rfl, fun H ↦ ⟨fun h' ↦ absurd h' (_root_.lt_irrefl _), fun h' ↦ absurd h' (_root_.lt_irrefl _), fun _ ↦ H⟩⟩
  · rw [if_neg (lt_asymm h), if_pos h]
    exact ⟨fun H ↦ H.2.1 h, fun H ↦ ⟨fun h' ↦ absurd h' (lt_asymm h), fun _ ↦ H, fun h' ↦ absurd h' h.ne'⟩⟩

noncomputable def actTermCodeGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y a. ∃ c0, !csymGraph c0 0 ∧ ∃ c1, !csymGraph c1 1 ∧ ∃ z, !numeralGraph z a ∧
    (a = 0 → y = c0) ∧ (a = 1 → y = c1) ∧ (a ≠ 0 → a ≠ 1 → y = z)”

instance actTermCode.defined : 𝚺₁-Function₁[V] actTermCode via actTermCodeGraph := .mk fun v ↦ by
  suffices (v 1 = 0 → v 0 = csym 0) ∧ (v 1 = 1 → v 0 = csym 1) ∧
      (v 1 ≠ 0 → v 1 ≠ 1 → v 0 = numeral (v 1)) ↔ v 0 = actTermCode (v 1) by simpa [actTermCodeGraph]
  unfold actTermCode
  by_cases h0 : v 1 = 0
  · simp [h0]
  · by_cases h1 : v 1 = 1
    · simp [h0, h1]
    · simp [h0, h1]

end definability

/-! ### The guard code -/

/-- The description vector `?[progT (dnum me), dU me, dW me, progT (dnum opp), dU opp, dW opp]`. -/
noncomputable def descVec (me opp : V) : V :=
  progT (dnum me) ∷ dU me ∷ dW me ∷ progT (dnum opp) ∷ dU opp ∷ dW opp ∷ 0

/-- Fill the six-variable template `g` with the descriptions of `me` and `opp`. -/
noncomputable def guardCode (g me opp : V) : V := subst LAct (descVec me opp) g

noncomputable def descVecGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y me opp. ∃ n₁, !dnumGraph n₁ me ∧ ∃ t₁, !progTGraph t₁ n₁ ∧ ∃ u₁, !dUGraph u₁ me ∧ ∃ w₁, !dWGraph w₁ me ∧
    ∃ n₂, !dnumGraph n₂ opp ∧ ∃ t₂, !progTGraph t₂ n₂ ∧ ∃ u₂, !dUGraph u₂ opp ∧ ∃ w₂, !dWGraph w₂ opp ∧
    ∃ v₅, !adjoinDef v₅ w₂ 0 ∧ ∃ v₄, !adjoinDef v₄ u₂ v₅ ∧
    ∃ v₃, !adjoinDef v₃ t₂ v₄ ∧ ∃ v₂, !adjoinDef v₂ w₁ v₃ ∧ ∃ v₁, !adjoinDef v₁ u₁ v₂ ∧ !adjoinDef y t₁ v₁”

instance descVec.defined : 𝚺₁-Function₂ (descVec : V → V → V) via descVecGraph := .mk fun v ↦ by
  simp [descVecGraph, descVec]

noncomputable def guardCodeGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y g me opp. ∃ w, !descVecGraph w me opp ∧ !(substsGraph LAct) y w g”

instance guardCode.defined : 𝚺₁-Function₃ (guardCode : V → V → V → V) via guardCodeGraph :=
  .mk fun v ↦ by simp [guardCodeGraph, guardCode]

/-! ### The guard code with the node budget (route c, 2026-09-23)

`ROUTE_B_SCOPE.md` §8: a stored template may refer to the searching node's OWN budget through a
SEVENTH free variable `#6`. The evaluator's `search` clause (`ArithS.Eval`) fills the template with
`descVecB me opp k` — the six descriptions of the frame in `#0..#5` and the binary numeral of the
node's budget in `#6` — so a frozen snapshot whose budget equals the searcher's is described by a TERM
in the slot and the stored template is a CONSTANT (`Cells/JustSlot`). The budget slot is LAST so that
every six-variable template is literally unchanged: it never reads `#6`
(`guardCodeB_of_template`, `ArithS.Subst`, the gate lemma of the design). -/

/-- The description vector with the node budget: `descVec me opp` extended by `bnum k` in the
seventh slot. -/
noncomputable def descVecB (me opp k : V) : V :=
  progT (dnum me) ∷ dU me ∷ dW me ∷ progT (dnum opp) ∷ dU opp ∷ dW opp ∷ bnum k ∷ 0

/-- Fill the template `g` with the descriptions of `me`, `opp` and the node budget `k`. -/
noncomputable def guardCodeB (g me opp k : V) : V := subst LAct (descVecB me opp k) g

noncomputable def descVecBGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y me opp k. ∃ n₁, !dnumGraph n₁ me ∧ ∃ t₁, !progTGraph t₁ n₁ ∧ ∃ u₁, !dUGraph u₁ me ∧ ∃ w₁, !dWGraph w₁ me ∧
    ∃ n₂, !dnumGraph n₂ opp ∧ ∃ t₂, !progTGraph t₂ n₂ ∧ ∃ u₂, !dUGraph u₂ opp ∧ ∃ w₂, !dWGraph w₂ opp ∧
    ∃ b, !bnumGraph b k ∧
    ∃ v₆, !adjoinDef v₆ b 0 ∧ ∃ v₅, !adjoinDef v₅ w₂ v₆ ∧ ∃ v₄, !adjoinDef v₄ u₂ v₅ ∧
    ∃ v₃, !adjoinDef v₃ t₂ v₄ ∧ ∃ v₂, !adjoinDef v₂ w₁ v₃ ∧ ∃ v₁, !adjoinDef v₁ u₁ v₂ ∧ !adjoinDef y t₁ v₁”

instance descVecB.defined : 𝚺₁-Function₃ (descVecB : V → V → V → V) via descVecBGraph := .mk fun v ↦ by
  simp [descVecBGraph, descVecB]

noncomputable def guardCodeBGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “y g me opp k. ∃ w, !descVecBGraph w me opp k ∧ !(substsGraph LAct) y w g”

instance guardCodeB.defined : 𝚺₁-Function₄ (guardCodeB : V → V → V → V → V) via guardCodeBGraph :=
  .mk fun v ↦ by simp [guardCodeBGraph, guardCodeB]

/-! ### The guard code with the budget slot KEPT (the `.sim` debt of route c, discharged 2026-09-24)

A seven-variable template stored inside a SIMULATED program must be instantiated by the OUTER frame
(the engine's `Prog.subst` descends into every guard) while its budget slot must stay the budget of
the node that eventually runs it. `gsubst` (`ArithS.Subst`) therefore fills `#0..#5` of a
seven-variable template with the outer descriptions and KEEPS `#6` a variable: `guardCodeSlot g me opp
:= subst (descVecSlot me opp) g` with `descVecSlot me opp = descVec me opp` extended by `^#6`. The
evaluator's `search` clause later fills that one variable with the node's budget
(`guardCodeB_gsubst₇`, `ArithS.Subst`: `guardCodeB (gsubst me opp g) me' opp' k = guardCodeB g me opp k`). -/

/-- The description vector with the budget slot kept as the variable `#6`: `descVec me opp` extended
by `^#6` in the seventh slot. -/
noncomputable def descVecSlot (me opp : V) : V :=
  progT (dnum me) ∷ dU me ∷ dW me ∷ progT (dnum opp) ∷ dU opp ∷ dW opp ∷ ^#6 ∷ 0

/-- Fill `#0..#5` of the seven-variable template `g` with the descriptions of `me` and `opp`, keeping
the budget slot `#6` free. -/
noncomputable def guardCodeSlot (g me opp : V) : V := subst LAct (descVecSlot me opp) g

noncomputable def descVecSlotGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y me opp. ∃ n₁, !dnumGraph n₁ me ∧ ∃ t₁, !progTGraph t₁ n₁ ∧ ∃ u₁, !dUGraph u₁ me ∧ ∃ w₁, !dWGraph w₁ me ∧
    ∃ n₂, !dnumGraph n₂ opp ∧ ∃ t₂, !progTGraph t₂ n₂ ∧ ∃ u₂, !dUGraph u₂ opp ∧ ∃ w₂, !dWGraph w₂ opp ∧
    ∃ b, !qqBvarDef b 6 ∧
    ∃ v₆, !adjoinDef v₆ b 0 ∧ ∃ v₅, !adjoinDef v₅ w₂ v₆ ∧ ∃ v₄, !adjoinDef v₄ u₂ v₅ ∧
    ∃ v₃, !adjoinDef v₃ t₂ v₄ ∧ ∃ v₂, !adjoinDef v₂ w₁ v₃ ∧ ∃ v₁, !adjoinDef v₁ u₁ v₂ ∧ !adjoinDef y t₁ v₁”

instance descVecSlot.defined : 𝚺₁-Function₂ (descVecSlot : V → V → V) via descVecSlotGraph := .mk fun v ↦ by
  simp [descVecSlotGraph, descVecSlot, numeral_eq_natCast]

noncomputable def guardCodeSlotGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y g me opp. ∃ w, !descVecSlotGraph w me opp ∧ !(substsGraph LAct) y w g”

instance guardCodeSlot.defined : 𝚺₁-Function₃ (guardCodeSlot : V → V → V → V) via guardCodeSlotGraph :=
  .mk fun v ↦ by simp [guardCodeSlotGraph, guardCodeSlot]

end ArithS
