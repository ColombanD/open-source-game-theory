import ArithS.Outcome.Matrix.DupocBot
import ArithS.Outcome.Matrix.DIMCID
import ArithS.Audit.RedCellAudit
import ArithS.Audit.RedCellUnsound
import ArithS.Necessitation.ClosedNec
import ArithS.Readings

/-!
# ArithS.Tour — a guided tour of PA-`S'`, in one file

Open this file first. It restates the nine trusted definitions of `ArithS/README.md` §2 at `V = ℕ`
(each `example … := rfl` is kept in sync with the real definition by the compiler; the reading of each at ℕ is a named theorem of `ArithS.Readings`, cited here), walks through the
red cell — the one cell to understand fully — names the headline theorems, and ends with the axiom
census of the results it cites. Every `#check` prints the statement the paper quotes; nothing here
proves anything new.

Notation (`ArithS.Notation`): `□[k] φ` is `LenBox TAct k φ`, the paper's `□_k φ` / `⊢_k φ`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct
open PD.Bots

/-! ## 1. The nine trusted definitions, at ℕ -/

/-! ### 1. The language: `ℒₒᵣ` plus two constant symbols, and the transposition τ -/

example : LAct = ℒₒᵣ + Language.constant Act := rfl
example : swap.func (LAct.const Act.C) = LAct.const Act.D := rfl
example : swap.func (LAct.const Act.D) = LAct.const Act.C := rfl
#check @swap_involutive

/-! ### 2. The theory: PA plus "the constants are the two action values, in one of the two orders" -/

#check (TAct : Theory LAct)
#check actionAxiom            -- (c_C = 0 ∧ c_D = 1) ∨ (c_C = 1 ∧ c_D = 0)
#check TAct_complete_of_readings   -- true in both readings of every model of PA ⇒ a `TAct`-theorem
#check TAct_sound_nat              -- ℕ is a model: a found guard is a true play

/-! ### 3. The length: the symbol count of a derivation code (symbol-blind, so τ preserves it) -/

#check (proofLen TAct : ℕ → ℕ)
#check (proofLenMeta : (TAct ⟹₂ _) → ℕ)
#check @proofLen_nat               -- on a quoted derivation, the meta symbol count

/-! ### 4. The box: "a proof of length ≤ k exists" — Δ₁, because the code is bounded too -/

example (k φ : ℕ) : □[k] φ = LenBox TAct k φ := rfl
#print LenBox                      -- ∃ d < codeBound k, Proof T d φ ∧ proofLen T d ≤ k
#check box_nat                     -- at ℕ: some meta derivation of σ has symbol count ≤ k
#check (LenBox.defined TAct)       -- the Δ₁ formula that says the same inside PA
#check @lenBoxUnbounded_iff_lenBox -- the code bound is invisible: same as the Σ₁ box in every model

/-! ### 5. Program codes, on the polynomial pairing `ppair x y = (x + y)² + y` -/

#check @pSearch
example (k : ℕ) : bot DupocBot k = progCode (DupocBot k) := rfl
#check progCode_DupocBot_search    -- the engine's DupocBot, as a code: a search on its guard template

/-! ### 6. Descriptions: a program enters a sentence as a TERM, in binary numerals (Critch's (b)) -/

#check @codeTerm
#check @binNumeral
#check @descriptions
#check description_nat             -- the term's code is `codeTerm`, and the term denotes the code

/-! ### 7. The guard template and the runtime guard -/

#check guardTemplate               -- "opp plays `a` against me", six description slots
#check @template                   -- the general translation of an engine guard formula
#check @guardCode                  -- fill the slots with the descriptions of the frame
#check @guardCodeB                 -- ... and the node's own budget in the seventh slot
#check guard_nat                   -- the guard code is the code of a sentence, true iff opp plays a against me

/-! ### 8. Substitution: the engine's one-shot `Prog.subst`, on codes -/

#check @substCode_self
#check @substCode_bot              -- `.bot` is frozen
#check @substCode_search           -- a stored template is instantiated with the OUTER frame
#check @progCode_subst             -- agreement with the engine

/-! ### 9. The evaluator: a Σ₁ fixpoint, one clause per constructor; `search` consults the box -/

#check @EvalGraph.case_iff
#check @EvalGraph.unique'          -- deterministic at ℕ
#check @EvalGraph.mono_le          -- fuel-monotone at ℕ
#check @eval_deterministic_nat

/-! ## 2. Outcomes, in the engine's vocabulary -/

#check @OutcomeSpecA
example : OutcomeSpecA .universal (bot DupocBot) (bot CupodBot) (some (.D, .C)) :=
  outcome_DupocBot_vs_CupodBot

/-! ## 3. The red cell, step by step

`DupocBot k` ("cooperate iff I can prove, within `k`, that you cooperate with me") against
`CupodBot k` ("defect iff I can prove, within `k`, that you defect against me"), at every shared
budget `k`. Neither guard is ever found, and both searchers take their else branch: Dupoc defects,
Cupod cooperates. Four ingredients, no Löb, no census:

1. **Symmetry.** τ exchanges the two constants; it maps Dupoc's guard sentence to Cupod's and
   preserves proof length exactly. So Dupoc's guard is found within `k` iff Cupod's is. -/

#check guard_DupocBot_iff_guard_CupodBot

/-! 2. **Soundness.** `ℕ` is a model of `TAct`, so a found guard is a TRUE play. If Cupod's guard
   were found, Dupoc would really defect against Cupod. -/

#check @play_of_found_opp_self

/-! 3. **Determinism.** But if Dupoc's guard is found (by 1), Dupoc takes its then-branch and
   cooperates. Two plays of one program in one frame agree — contradiction. -/

#check @EvalGraph.unique'

/-! 4. **The cell.** Hence neither guard is found; both else-branches fire. -/

#check snd_DupocBot_vs_CupodBot    -- on the engine's codes `progCode (DupocBot k)`
#check red_cell                    -- the same on the hand-written twins `Dupoc k` / `Cupod k`

/-! ## 4. Löb: the parametric bounded Löb theorem, with its one hypothesis discharged -/

#check LoebSound                   -- "a proof of p(k) within the budget makes p(k) true, in both readings"
#check @family_found               -- ... ⇒ p(k) is FOUND for all large k (the arithmetized `pblt_engine`)
#check boundedInnerNec_sixteen     -- Critch's assumption (d), a theorem: PA verifies its own short proofs, polynomially
#check closedInnerNec_sixteen
#check pblt
#check dupoc_self_coop             -- Dupoc cooperates with itself for all large k (the hand-written twin)
#check outcome_DupocBot_vs_DupocBot -- the same cell on the engine's `progCode (DupocBot k)`

/-! ## 5. Where `S'` contradicts the rule-based `S` -/

#check dimcid_vs_closed            -- DIMCID defects against every closed program
#check outcome_DIMCID_vs_DupocBot  -- the engine has (C, D) at EVERY k; `S'` has (D, D) for all large k

/-! ## 6. The floors: no side taken -/

#check dich_DupocBot_vs_DBot       -- ¬hinge → the engine's value; hinge → the other value
#check hinge_reduces_to_bounded_consistency_DupocBot_vs_DBot

/-! ## 7. Negative controls: the definitions are not vacuous -/

#check search_is_real              -- "unprovable at k" is not "too long to state"
#check guard_fits
#check red_cell_flips_when_unsound -- with `c_C = c_D` added, both guards are found and the cell flips
#check tbad_inconsistent

/-! ## 8. The census -/

#print axioms outcome_DupocBot_vs_CupodBot
#print axioms pblt
#print axioms dupoc_self_coop
#print axioms outcome_DIMCID_vs_DupocBot

end ArithS
