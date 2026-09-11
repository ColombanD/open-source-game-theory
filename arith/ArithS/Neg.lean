import ArithS.Code
import ArithS.Fit

/-!
# ArithS.Neg — T2-NEG: no budget-keeping transfer exists, at any inflation (roadmap M3, step (d))

The engine's transcript-cost model charges an ATOM by the number of evaluation steps of
its play certificate, never by the size of its conclusion: `AtomProvable.mk` needs only
`n ≤ k` for the run cost `n`, so `Pf 1 (.plays (.const C) q C)` holds for EVERY program `q`
(`PlaysProof.const` costs `c_leaf = 1`; this is the exception in `Base/Exclusion.pf_size_or_atom`).
Any arithmetical realization of that atom must WRITE `q` — at least the canonical numeral of
its code — and a `TAct`-proof is at least as long as its conclusion (`flen_le_of_lenProvable`,
`ArithS.ProofLength`). So for the bot-iterates `q = .bot^n (.const C)`, whose codes have bit
length `≥ n`, the shortest proof of the realized atom grows without bound while the engine's
budget stays `1`: no function `e` can make `Pf k φ → TAct ⊢_{e k} tr φ` true.

* `no_budget_keeping_transfer`: the impossibility, PARAMETRIC in the realization `tr` — the
  one hypothesis is that `tr (.plays p q a)` is at least as long as the bit length of the
  canonical numeral `dnum (pcode q)` of a closed `q`;
* `size_dnum_le_flen_trAt`: the hypothesis holds for the concrete bounded translation
  `trAt me opp φ := tmpl φ ⇜ descTerms (pcode me) (pcode opp)` of `ArithS.Code` (the closed
  description of `q` is a binary numeral whose length is at least the bit length);
* `no_budget_keeping_transfer_tmpl` / `no_budget_keeping_transfer_guardCode`: the instance,
  the second one phrased on the code `guardCode (tcode φ) (pcode me) (pcode opp)` that the
  arithmetized evaluator actually consults.

This is the precise reason T2 is stated as T2-NEG + T2-AGENT + T2-CORE (roadmap "M3 DESIGN
DECISION"): where the engine counts characters, PA-`S` agrees; where it charges evaluation
steps and cheap citations (`search_t`'s `numCost k`), no PA proof length can match, and
budget-keeping soundness is exactly Critch's assumption (d), left as M4.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

/-! ### Bot-iterates and the bit length of their codes -/

/-- `.bot^n p`. -/
def botIter : ℕ → PD.Prog → PD.Prog
  | 0, p => p
  | n + 1, p => .bot (botIter n p)

/-- `pBot^n x`. -/
noncomputable def pBotIter : ℕ → ℕ → ℕ
  | 0, x => x
  | n + 1, x => pBot (pBotIter n x)

lemma pcode_botIter (n : ℕ) (p : PD.Prog) : pcode (botIter n p) = pBotIter n (pcode p) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [botIter, pBotIter, ih]

lemma closedP_botIter_succ (n : ℕ) (p : PD.Prog) : closedP (botIter (n + 1) p) = true := rfl

lemma swapcode_pBotIter (n x : ℕ) : swapcode (pBotIter n x) = pBotIter n (swapcode x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pBotIter, swapcode, ih]

/-- `pBot` more than doubles: `ppair 3 x + 1 = (3 + x)² + x + 1 > 2x`. -/
lemma two_mul_lt_pBot (x : ℕ) : 2 * x < pBot x := by
  unfold pBot ppair
  show 2 * x < (3 + x) * (3 + x) + x + 1
  nlinarith

/-- The bit length grows by at least one per `pBot`. -/
lemma size_lt_size_pBot (x : ℕ) : Nat.size x < Nat.size (pBot x) := by
  rw [Nat.lt_size]
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [Nat.size_zero, Nat.pow_zero]
    have := two_mul_lt_pBot 0
    omega
  · exact le_trans (two_pow_size_le x hx) (le_of_lt (two_mul_lt_pBot x))

lemma le_size_pBotIter (n x : ℕ) : n ≤ Nat.size (pBotIter n x) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have := size_lt_size_pBot (pBotIter n x)
    show n + 1 ≤ Nat.size (pBot (pBotIter n x))
    omega

/-- The canonical numeral of a bot-iterate's code (`dnum`: the smaller of the code and its
transposition, itself a bot-iterate) has bit length at least `n`. -/
lemma le_size_dnum_pBotIter (n x : ℕ) : n ≤ Nat.size (dnum (pBotIter n x)) := by
  unfold dnum
  split_ifs with h
  · exact le_size_pBotIter n x
  · rw [swapcode_pBotIter]; exact le_size_pBotIter n _

/-! ### A binary numeral is at least as long as the bit length it writes -/

/-- The lower bound matching `tlen_bnumT`: `size n ≤ tlen (bnumT n)`. -/
theorem size_le_tlen_bnumT (n : ℕ) :
    Nat.size n ≤ tlen (Rew.emb (bnumT n) : SyntacticSemiterm ℒₒᵣ 0) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | k
    · rw [bnumT_zero, tlen_emb_closed_zero, Nat.size_zero]; omega
    · rw [bnumT_one, tlen_emb_closed_one, Nat.size_one]
    · have hs : Nat.size (k + 1 + 1) ≤ Nat.size ((k + 1 + 1) / 2) + 1 := by
        rw [Nat.size_le, Nat.pow_succ]
        have := Nat.lt_size_self ((k + 1 + 1) / 2)
        omega
      have ih' := ih ((k + 1 + 1) / 2) (by omega)
      by_cases he : (k + 1 + 1) % 2 = 0
      · rw [bnumT_even (by omega) he, tlen_emb_closed_mul, tlen_emb_twoT]
        omega
      · rw [bnumT_odd (by omega) (by omega), tlen_emb_closed_add, tlen_emb_closed_mul, tlen_emb_twoT,
          tlen_emb_closed_one]
        omega

/-! ### The realized atom writes the description of its second program -/

/-- A description is longer than its numeral term. -/
lemma flen_emb_descF_ge {n : ℕ} (X T U W : Semiterm LAct Empty (n + 1)) :
    tlen (Rew.emb T : SyntacticSemiterm LAct (n + 1)) + 1 ≤
      flen (Rewriting.emb (descF X T U W) : Semiproposition LAct n) := by
  unfold descF
  simp only [Rewriting.emb, Rewriting.app_exs, Rew.q_emb, LogicalConnective.HomClass.map_and,
    Semiformula.rew_rel, flen_exs, flen_and, flen_rel, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  omega

/-- **The concrete translation writes `q`**: for a closed `q`, the sentence `trAt me opp
(.plays p q a)` is at least as long as the bit length of the canonical numeral of `pcode q`. -/
theorem size_dnum_le_flen_trAt (me opp p q : PD.Prog) (a : PD.Action) (hq : closedP q = true) :
    Nat.size (dnum (pcode q)) ≤ flen (Rewriting.emb (trAt me opp (.plays p q a)) : Proposition LAct) := by
  unfold trAt
  rw [tmpl_plays]
  unfold progGraph
  rw [progAux_of_ne (closedP_ne_self hq) (closedP_ne_opp hq), closedDesc_subst]
  simp only [Rewriting.subst, Rewriting.emb, Rewriting.app_exs, Rew.q_emb, LogicalConnective.HomClass.map_and,
    rew_descF, rew_cl, flen_exs, flen_and]
  have hB : tlen (Rew.emb (cl (dnumT (pcode q))) : SyntacticSemiterm LAct 4) + 1 ≤
      flen ((Rewriting.app Rew.emb) (descF
        ((Rew.subst (descTerms (pcode me) (pcode opp))).q.q.q.q (Rew.bShift (![#1, #3, #4, #5, #6, #7, #8] 0)))
        (cl (dnumT (pcode q))) (cl (dUT (pcode q))) (cl (dWT (pcode q))))) := by
    have h := flen_emb_descF_ge (n := 3)
      ((Rew.subst (descTerms (pcode me) (pcode opp))).q.q.q.q (Rew.bShift (![#1, #3, #4, #5, #6, #7, #8] 0)))
      (cl (dnumT (pcode q))) (cl (dUT (pcode q))) (cl (dWT (pcode q)))
    exact h
  have hT : Nat.size (dnum (pcode q)) ≤ tlen (Rew.emb (cl (dnumT (pcode q))) : SyntacticSemiterm LAct 4) := by
    rw [tlen_emb_cl]
    unfold dnumT
    rw [tlen_emb_lMap_emb]
    exact size_le_tlen_bnumT _
  omega

/-! ### T2-NEG -/

/-- **T2-NEG — no budget-keeping transfer at any inflation.** For every `e : ℕ → ℕ` and every
realization `tr` that writes (the canonical numeral of) the second program of a play-atom,
some engine theorem `Pf k φ` has NO `TAct`-proof of length `≤ e k` of `tr φ`. Witness: `k = 1`,
`φ = .plays (.const C) (.bot^(e 1 + 1) (.const C)) C`, whose engine certificate is the
one-step `PlaysProof.const` (cost `c_leaf = 1`) while its realization is longer than `e 1`. -/
theorem no_budget_keeping_transfer (e : ℕ → ℕ) (tr : PD.Formula → Sentence LAct)
    (htr : ∀ (p q : PD.Prog) (a : PD.Action), closedP q = true →
      Nat.size (dnum (pcode q)) ≤ flen (Rewriting.emb (tr (.plays p q a)) : Proposition LAct)) :
    ∃ (k : ℕ) (φ : PD.Formula), PD.Pf k φ ∧ ¬ LenProvable (fbound : ℕ → ℕ) (e k) TAct (⌜tr φ⌝ : ℕ) := by
  refine ⟨1, .plays (.const .C) (botIter (e 1 + 1) (.const .C)) .C, ?_, ?_⟩
  · exact PD.Pf.atom (PD.AtomProvable.mk PD.PlaysProof.const (le_refl _))
  · intro h
    have h1 := flen_le_of_lenProvable h
    have h2 := htr (.const .C) (botIter (e 1 + 1) (.const .C)) .C (closedP_botIter_succ _ _)
    have h3 : e 1 + 1 ≤ Nat.size (dnum (pcode (botIter (e 1 + 1) (.const .C)))) := by
      rw [pcode_botIter]; exact le_size_dnum_pBotIter _ _
    omega

/-- **T2-NEG for the concrete bounded translation** `trAt me opp` of `ArithS.Code`. -/
theorem no_budget_keeping_transfer_tmpl (e : ℕ → ℕ) (me opp : PD.Prog) :
    ∃ (k : ℕ) (φ : PD.Formula), PD.Pf k φ ∧ ¬ LenProvable (fbound : ℕ → ℕ) (e k) TAct (⌜trAt me opp φ⌝ : ℕ) :=
  no_budget_keeping_transfer e (trAt me opp) (fun p q a hq ↦ size_dnum_le_flen_trAt me opp p q a hq)

/-- The same, on the code the arithmetized evaluator consults at a search node: the guard
code of the template code at the players' codes. -/
theorem no_budget_keeping_transfer_guardCode (e : ℕ → ℕ) (me opp : PD.Prog) :
    ∃ (k : ℕ) (φ : PD.Formula), PD.Pf k φ ∧
      ¬ LenProvable (fbound : ℕ → ℕ) (e k) TAct (guardCode (tcode φ) (pcode me) (pcode opp)) := by
  obtain ⟨k, φ, hpf, h⟩ := no_budget_keeping_transfer_tmpl e me opp
  exact ⟨k, φ, hpf, by rwa [quote_trAt] at h⟩

end ArithS
