import ArithS.Outcome.Spec
import ArithS.Theory.Symmetry
import ArithS.Cells.Common.Syntax
import ArithS.Cells.RedCellEngine
import ArithS.Cells.DupocEngine

/-!
# ArithS.Cells.Transposition — the transposition theorem of the arithmetized evaluator

**What this file proves.** The symmetry τ (the exchange of the two actions `C`/`D`) is a symmetry of
the evaluator: transposing both programs transposes what they play.

* Code level, at ℕ (`evalGraph_transposeCode`, `evalGraph_transposeCode_iff`): for `Transposable`
  codes `me`, `opp`, `p`,

      EvalGraph n me opp p a ↔
        EvalGraph n (transposeCode me) (transposeCode opp) (transposeCode p) (swapAction a)

  at the SAME fuel `n`, for every value `a` (not only the two actions). Consequences on the reading
  layer: `plays_transposeCode_iff`, `diverges_transposeCode_iff`, `outcomeAtA_transposeCode_iff`.
* Engine level (`plays_transpose`, `outcomeAtA_transpose`, `outcomeSpecA_transpose`): for programs of
  the search-bot fragment `fragP` (no tau constructor, no `.box` in a guard — the hypothesis of the
  existing `transposeCode_progCode`, nothing stronger),

      plays (progCode L) (progCode R) a ↔ plays (progCode L.transpose) (progCode R.transpose) a.swap

  and the same for a whole cell `OutcomeSpecA regime (bot L) (bot R) r`, in every budget regime.
* The one non-structural step is the search clause, and its content is a fact about the box alone
  (`lenBox_revalueTemplate_iff`): `□[k] x ↔ □[k] (revalueTemplate 1 0 x)` for EVERY code `x` — a
  proof code of `x` forces `x` to be a formula code, the formula is decoded (`IsSemiformula.sound`),
  the proof is transposed at the same length (`transpose_exists`) and properness puts the new code
  below the code bound. No hypothesis on `x`.
* A sanity corollary: `(CupodBot, CupodBot) = (D, D)` eventually, re-derived in one line from
  `loeb_DupocBot_vs_DupocBot`, and the red-cell symmetry as an instance of `plays_transpose`.

**The well-formedness predicate.** `Transposable p` (an inductive predicate on codes): `p` is built
from `pConst`, `pSelf`, `pOpp`, `pBot`, `pSim`, `pIte`, `pSearch`, `pTvote`, hereditarily through the
program positions, and every `pSearch k g p q` node stores a template `g` with
`IsSemiformula LAct 7 g`. Why it is needed:

* *Seven variables.* The search clause consults `guardCodeB g me opp k`, the stored template filled
  with a seven-entry description vector. τ commutes with that instantiation
  (`revalueTemplate_guardCodeB`) and with the substitution of a frame under `pSim`
  (`isSemiformula_substTemplate₇`) only when the template reads no variable beyond the seven slots;
  on a code with more free variables the instantiation is a junk value on which the two sides need
  not agree. A six-variable template is in particular a seven-variable one
  (`isSemiformula_seven_of_six`).
* *Votes.* `transposeCode` FREEZES the entries of a `pTvote` (the engine's τ̂ does the same: the vote
  thresholds on C-mass). The theorem still holds on `pTvote` nodes, and needs nothing of the entries:
  an entry runs in its own frame `(pBot I, pBot I)`, the same evaluation on both sides, so the vote
  count is unchanged and only the two branches are transposed. `Transposable` therefore constrains
  the branches of a vote and leaves its entry list arbitrary.
* *Systems are excluded.* `pSys d i` and `pSelfIdx j` are not `Transposable`: a system member is
  closed by `sysCloseCode`, whose stored templates are thirteen-variable (`sysCloseTemplateAt`), and
  no τ-equivariance of `listGet`/`sysCloseCode` is available. This matches the engine level, where
  `fragP` has no tau constructor at all.

`Transposable` is preserved by `transposeCode` (`Transposable.transpose`) and by `substCode`
(`Transposable.subst`; frames change under `pSim`), and holds of `progCode p` for every `p` in the
fragment (`transposable_progCode`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct
open PD.Bots

/-! ### 0. `transposeCode` on the constructors, `swapAction` is injective -/

section equations

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma transposeCode_pConst (a : V) : transposeCode (pConst a) = pConst (swapAction a) := revalue_const 1 0 a

lemma transposeCode_pSelf : transposeCode (pSelf : V) = pSelf := revalue_self 1 0

lemma transposeCode_pOpp : transposeCode (pOpp : V) = pOpp := revalue_opp 1 0

lemma transposeCode_pSim (p q : V) : transposeCode (pSim p q) = pSim (transposeCode p) (transposeCode q) :=
  revalue_sim 1 0 p q

lemma transposeCode_pIte (b a p q : V) :
    transposeCode (pIte b a p q) = pIte (transposeCode b) (swapAction a) (transposeCode p) (transposeCode q) :=
  revalue_ite 1 0 b a p q

lemma transposeCode_pSearch (k g p q : V) :
    transposeCode (pSearch k g p q) = pSearch k (revalueTemplate 1 0 g) (transposeCode p) (transposeCode q) :=
  revalue_search 1 0 k g p q

/-- The entries of a vote are frozen by τ; the branches are transposed. -/
lemma transposeCode_pTvote (v θ p q : V) :
    transposeCode (pTvote v θ p q) = pTvote v θ (transposeCode p) (transposeCode q) :=
  revalue_tvote 1 0 v θ p q

lemma swapAction_inj {a b : V} (h : swapAction a = swapAction b) : a = b := by
  have h' := congrArg swapAction h
  rwa [swapAction_swapAction, swapAction_swapAction] at h'

end equations

/-! ### 1. The box is τ-symmetric on every code -/

/-- A proof of `x` of length `≤ k` transposes into a proof of `revalueTemplate 1 0 x` of the same
length — for EVERY code `x`: the proof code forces `x` to be a formula code. -/
theorem lenBoxNat_revalueTemplate {k x : ℕ} (h : LenBoxNat (codeBound : ℕ → ℕ) k TAct x) :
    LenBoxNat (codeBound : ℕ → ℕ) k TAct (revalueTemplate 1 0 x) := by
  rcases h with ⟨d, _, hd, hk⟩
  have hx : IsFormula LAct x := hd.2.isFormulaSet x (by rw [hd.1]; simp)
  obtain ⟨φ, rfl⟩ := IsSemiformula.sound hx
  rw [revalueTemplate_quote]
  have e : (ORingStructure.numeral k : ℕ) = k := by simp
  obtain ⟨b, rfl⟩ := Proof.sound' hd
  obtain ⟨b', hb'⟩ := transpose_exists φ b
  rw [proofLen_quote, e] at hk
  have hk' : proofLenMeta b ≤ k := by
    rcases le_def.mp hk with h | h
    · exact Nat.le_of_eq h
    · exact Nat.le_of_lt h
  refine ⟨⌜b'⌝, ?_, ⟨?_, derivation_quote b'⟩, ?_⟩
  · rw [e, codeBound_nat]
    refine Nat.lt_succ_of_le (le_trans (quote_derivation_le smallCodes_LAct smallRelCodes_LAct b')
      (F_mono ?_))
    rw [hb']
    exact Nat.mul_le_mul_left 12 hk'
  · rw [fstIdx_quote b']
    exact Derivation2.Sequent.quote_singleton _
  · rw [proofLen_quote, hb', e]; exact hk

/-- **The box does not see τ**: `□[k] x ↔ □[k] (τ x)`, on every code and at every budget. -/
theorem lenBox_revalueTemplate_iff (k x : ℕ) :
    LenBox TAct k x ↔ LenBox TAct k (revalueTemplate 1 0 x) := by
  rw [lenBox_nat, lenBox_nat]
  refine ⟨lenBoxNat_revalueTemplate, fun h ↦ ?_⟩
  have h' := lenBoxNat_revalueTemplate h
  rwa [revalueTemplate_swap_swap] at h'

/-- **The search clause**: the guard of a seven-variable template is found in the frame `(me, opp)`
iff the transposed template's guard is found in the transposed frame, at the same budget. -/
theorem lenBox_guardCodeB_transposeCode {g : ℕ} (hg : IsSemiformula LAct 7 g) (me opp k : ℕ) :
    LenBox TAct k (guardCodeB g me opp k) ↔
    LenBox TAct k (guardCodeB (revalueTemplate 1 0 g) (transposeCode me) (transposeCode opp) k) := by
  rw [← revalueTemplate_guardCodeB hg]
  exact lenBox_revalueTemplate_iff k _

/-! ### 2. The well-formedness predicate -/

/-- `Transposable p`: the code `p` is built from the seven program constructors and `pTvote`,
hereditarily through the program positions, and every stored template is a seven-variable formula
code. The entries of a vote are unconstrained (τ freezes them and they run in their own frame);
`pSys`/`pSelfIdx` are excluded. See the module docstring. -/
inductive Transposable : ℕ → Prop
  | const (a : ℕ) : Transposable (pConst a)
  | self : Transposable (pSelf : ℕ)
  | opp : Transposable (pOpp : ℕ)
  | bot {p : ℕ} : Transposable p → Transposable (pBot p)
  | sim {p q : ℕ} : Transposable p → Transposable q → Transposable (pSim p q)
  | ite {b p q : ℕ} (a : ℕ) : Transposable b → Transposable p → Transposable q → Transposable (pIte b a p q)
  | search {g p q : ℕ} (k : ℕ) : IsSemiformula LAct 7 g → Transposable p → Transposable q →
      Transposable (pSearch k g p q)
  | tvote {p q : ℕ} (v θ : ℕ) : Transposable p → Transposable q → Transposable (pTvote v θ p q)

/-- τ preserves well-formedness. -/
theorem Transposable.transpose {p : ℕ} (hp : Transposable p) : Transposable (transposeCode p) := by
  induction hp with
  | const a => rw [transposeCode_pConst]; exact .const _
  | self => rw [transposeCode_pSelf]; exact .self
  | opp => rw [transposeCode_pOpp]; exact .opp
  | bot _ ih => rw [transposeCode_pBot]; exact .bot ih
  | sim _ _ ihp ihq => rw [transposeCode_pSim]; exact .sim ihp ihq
  | ite a _ _ _ ihb ihp ihq => rw [transposeCode_pIte]; exact .ite _ ihb ihp ihq
  | search k hg _ _ ihp ihq =>
    rw [transposeCode_pSearch]
    exact .search k (isSemiformula_revalueTemplate_swap_iff.mpr hg) ihp ihq
  | tvote v θ _ _ ihp ihq => rw [transposeCode_pTvote]; exact .tvote v θ ihp ihq

/-- Substituting a well-formed frame into a well-formed program gives a well-formed program (the
frame of a `pSim`). -/
theorem Transposable.subst {p me opp : ℕ} (hp : Transposable p) (hme : Transposable me)
    (hopp : Transposable opp) : Transposable (substCode me opp p) := by
  induction hp with
  | const a => rw [substCode_const]; exact .const a
  | self => rw [substCode_self]; exact hme
  | opp => rw [substCode_opp]; exact hopp
  | bot h _ => rw [substCode_bot]; exact .bot h
  | sim _ _ ihp ihq => rw [substCode_sim]; exact .sim ihp ihq
  | ite a _ _ _ ihb ihp ihq => rw [substCode_ite]; exact .ite a ihb ihp ihq
  | search k hg _ _ ihp ihq =>
    rw [substCode_search]
    exact .search k (isSemiformula_substTemplate₇ hg me opp) ihp ihq
  | tvote v θ _ _ ihp ihq => rw [substCode_tvote]; exact .tvote v θ ihp ihq

/-! ### 3. The transposition theorem, on codes -/

/-- **Transposition of the evaluator** (one direction): if `p` plays `a` in the frame `(me, opp)`
with fuel `n`, then `τ p` plays `τ a` in the frame `(τ me, τ opp)` with the same fuel. -/
theorem evalGraph_transposeCode {n me opp p a : ℕ} (hme : Transposable me) (hopp : Transposable opp)
    (hp : Transposable p) (h : EvalGraph n me opp p a) :
    EvalGraph n (transposeCode me) (transposeCode opp) (transposeCode p) (swapAction a) := by
  induction n generalizing me opp p a with
  | zero => exact absurd h EvalGraph.zero_iff
  | succ n ih =>
    cases hp with
    | const a' =>
      rw [EvalGraph.const_iff] at h
      rw [transposeCode_pConst, EvalGraph.const_iff, h]
    | self =>
      rw [EvalGraph.self_iff] at h
      rw [transposeCode_pSelf, EvalGraph.self_iff]
      exact ih hme hopp hme h
    | opp =>
      rw [EvalGraph.opp_iff] at h
      rw [transposeCode_pOpp, EvalGraph.opp_iff]
      exact ih hme hopp hopp h
    | bot hp' =>
      rw [EvalGraph.bot_iff] at h
      rw [transposeCode_pBot, EvalGraph.bot_iff]
      exact ih hme hopp hp' h
    | sim hp' hq =>
      rw [EvalGraph.sim_iff] at h
      rw [transposeCode_pSim, EvalGraph.sim_iff, ← transposeCode_substCode, ← transposeCode_substCode]
      exact ih (hp'.subst hme hopp) (hq.subst hme hopp) (hp'.subst hme hopp) h
    | ite a' hb hp' hq =>
      obtain ⟨r, hr, hc⟩ := EvalGraph.ite_iff.mp h
      rw [transposeCode_pIte, EvalGraph.ite_iff]
      refine ⟨swapAction r, ih hme hopp hb hr, ?_⟩
      rcases hc with ⟨e, hc⟩ | ⟨e, hc⟩
      · exact Or.inl ⟨by rw [e], ih hme hopp hp' hc⟩
      · exact Or.inr ⟨fun e' ↦ e (swapAction_inj e'), ih hme hopp hq hc⟩
    | search k hg hp' hq =>
      rw [transposeCode_pSearch, EvalGraph.search_iff]
      rcases EvalGraph.search_iff.mp h with ⟨e, hc⟩ | ⟨e, hc⟩
      · exact Or.inl ⟨(lenBox_guardCodeB_transposeCode hg me opp k).mp e, ih hme hopp hp' hc⟩
      · exact Or.inr ⟨fun e' ↦ e ((lenBox_guardCodeB_transposeCode hg me opp k).mpr e'), ih hme hopp hq hc⟩
    | tvote v θ hp' hq =>
      rw [transposeCode_pTvote, EvalGraph.tvote_iff]
      rcases EvalGraph.tvote_iff.mp h with ⟨hv, hc⟩ | ⟨w, I, rest, hv, hc⟩
      · refine Or.inl ⟨hv, ?_⟩
        rcases hc with ⟨e, hc⟩ | ⟨e, hc⟩
        · exact Or.inl ⟨e, ih hme hopp hp' hc⟩
        · exact Or.inr ⟨e, ih hme hopp hq hc⟩
      · refine Or.inr ⟨w, I, rest, hv, ?_⟩
        rcases hc with ⟨e, hc⟩ | ⟨e, r, hI, hc⟩
        · exact Or.inl ⟨e, ih hme hopp hp' hc⟩
        · refine Or.inr ⟨e, r, hI, ?_⟩
          rcases hc with ⟨f, hc⟩ | ⟨f, hc⟩
          · have h' := ih hme hopp (Transposable.tvote rest _ hp' hq) hc
            rw [transposeCode_pTvote] at h'
            exact Or.inl ⟨f, h'⟩
          · have h' := ih hme hopp (Transposable.tvote rest _ hp' hq) hc
            rw [transposeCode_pTvote] at h'
            exact Or.inr ⟨f, h'⟩

/-- **Transposition of the evaluator**: `p` plays `a` in the frame `(me, opp)` iff `τ p` plays `τ a`
in the frame `(τ me, τ opp)`, at the same fuel — for every value `a`. -/
theorem evalGraph_transposeCode_iff {n me opp p a : ℕ} (hme : Transposable me) (hopp : Transposable opp)
    (hp : Transposable p) :
    EvalGraph n me opp p a ↔
    EvalGraph n (transposeCode me) (transposeCode opp) (transposeCode p) (swapAction a) := by
  refine ⟨evalGraph_transposeCode hme hopp hp, fun h ↦ ?_⟩
  have h' := evalGraph_transposeCode hme.transpose hopp.transpose hp.transpose h
  simpa only [transposeCode_transposeCode, swapAction_swapAction] using h'

/-- The same with the transposed value on the left: `τ p` plays `a` iff `p` plays `τ a`. -/
theorem evalGraph_transposeCode_iff' {n me opp p a : ℕ} (hme : Transposable me) (hopp : Transposable opp)
    (hp : Transposable p) :
    EvalGraph n (transposeCode me) (transposeCode opp) (transposeCode p) a ↔
    EvalGraph n me opp p (swapAction a) := by
  rw [evalGraph_transposeCode_iff hme hopp hp, swapAction_swapAction]

/-! ### 4. Plays, divergence and outcomes, on codes -/

/-- τ on an outcome: both actions are exchanged; a divergence stays a divergence. -/
def transposeOutcome : Option PD.Outcome → Option PD.Outcome
  | some (a, b) => some (a.swap, b.swap)
  | none => none

@[simp] lemma transposeOutcome_some (a b : PD.Action) : transposeOutcome (some (a, b)) = some (a.swap, b.swap) := rfl
@[simp] lemma transposeOutcome_none : transposeOutcome none = none := rfl

@[simp] lemma transposeOutcome_transposeOutcome (r : Option PD.Outcome) :
    transposeOutcome (transposeOutcome r) = r := by
  rcases r with _ | ⟨a, b⟩
  · rfl
  · simp

/-- **Plays transpose**: `me` plays `a` against `opp` iff `τ me` plays `τ a` against `τ opp`. -/
theorem plays_transposeCode_iff {me opp : ℕ} (hme : Transposable me) (hopp : Transposable opp) (a : PD.Action) :
    plays me opp a ↔ plays (transposeCode me) (transposeCode opp) a.swap := by
  unfold plays
  rw [actCode_swap]
  exact exists_congr fun n ↦ evalGraph_transposeCode_iff hme hopp hme

/-- **Divergence transposes.** -/
theorem diverges_transposeCode_iff {me opp : ℕ} (hme : Transposable me) (hopp : Transposable opp) :
    diverges me opp ↔ diverges (transposeCode me) (transposeCode opp) := by
  unfold diverges
  refine ⟨fun h n a ha ↦ h n _ ((evalGraph_transposeCode_iff' hme hopp hme).mp ha),
    fun h n a ha ↦ h n _ ((evalGraph_transposeCode_iff hme hopp hme).mp ha)⟩

/-- **Outcomes transpose**, on codes. -/
theorem outcomeAtA_transposeCode_iff {L R : ℕ} (hL : Transposable L) (hR : Transposable R)
    (r : Option PD.Outcome) :
    OutcomeAtA L R r ↔ OutcomeAtA (transposeCode L) (transposeCode R) (transposeOutcome r) := by
  rcases r with _ | ⟨a, b⟩
  · exact and_congr (diverges_transposeCode_iff hL hR) (diverges_transposeCode_iff hR hL)
  · exact and_congr (plays_transposeCode_iff hL hR a) (plays_transposeCode_iff hR hL b)

/-! ### 5. The engine level: programs of the search-bot fragment -/

/-- The code of a fragment program is well-formed: its stored templates are the seven-variable
`templateCodeAt`. -/
theorem transposable_progCode : ∀ p : PD.Prog, fragP p = true → Transposable (progCode p)
  | .const a, _ => by rw [progCode_const]; exact .const _
  | .self, _ => by rw [progCode_self]; exact .self
  | .opp, _ => by rw [progCode_opp]; exact .opp
  | .bot p, h => by
    simp only [fragP] at h
    rw [progCode_bot]; exact .bot (transposable_progCode p h)
  | .sim p q, h => by
    simp only [fragP, Bool.and_eq_true] at h
    rw [progCode_sim]; exact .sim (transposable_progCode p h.1) (transposable_progCode q h.2)
  | .ite b a p q, h => by
    simp only [fragP, Bool.and_eq_true] at h
    rw [progCode_ite]
    exact .ite _ (transposable_progCode b h.1.1) (transposable_progCode p h.1.2) (transposable_progCode q h.2)
  | .search k φ p q, h => by
    simp only [fragP, Bool.and_eq_true] at h
    rw [progCode_search]
    exact .search k (isSemiformula_templateCodeAt₇ φ k (noSelfIdxF_of_fragF φ h.1.1))
      (transposable_progCode p h.1.2) (transposable_progCode q h.2)
  | .tvote _ _ _ _, h => by simp [fragP] at h
  | .sys _ _, h => by simp [fragP] at h
  | .selfIdx _, h => by simp [fragP] at h

/-- **Plays transpose, on the engine's programs**: `L` plays `a` against `R` iff the transposed `L`
plays the other action against the transposed `R`. -/
theorem plays_transpose {L R : PD.Prog} (hL : fragP L = true) (hR : fragP R = true) (a : PD.Action) :
    plays (progCode L) (progCode R) a ↔ plays (progCode L.transpose) (progCode R.transpose) a.swap := by
  rw [← transposeCode_progCode L hL, ← transposeCode_progCode R hR]
  exact plays_transposeCode_iff (transposable_progCode L hL) (transposable_progCode R hR) a

/-- **Divergence transposes, on the engine's programs.** -/
theorem diverges_transpose {L R : PD.Prog} (hL : fragP L = true) (hR : fragP R = true) :
    diverges (progCode L) (progCode R) ↔ diverges (progCode L.transpose) (progCode R.transpose) := by
  rw [← transposeCode_progCode L hL, ← transposeCode_progCode R hR]
  exact diverges_transposeCode_iff (transposable_progCode L hL) (transposable_progCode R hR)

/-- **Outcomes transpose, on the engine's programs.** -/
theorem outcomeAtA_transpose {L R : PD.Prog} (hL : fragP L = true) (hR : fragP R = true)
    (r : Option PD.Outcome) :
    OutcomeAtA (progCode L) (progCode R) r ↔
    OutcomeAtA (progCode L.transpose) (progCode R.transpose) (transposeOutcome r) := by
  rw [← transposeCode_progCode L hL, ← transposeCode_progCode R hR]
  exact outcomeAtA_transposeCode_iff (transposable_progCode L hL) (transposable_progCode R hR) r

/-- **Cells transpose**: a cell of budget-indexed fragment bots holds iff the transposed cell holds
with the transposed outcome, in every budget regime. (A closed bot `const P` is the constant family
`bot fun _ ↦ P`.) -/
theorem outcomeSpecA_transpose {regime : PD.BudgetRegime} {L R : ℕ → PD.Prog}
    (hL : ∀ k, fragP (L k) = true) (hR : ∀ k, fragP (R k) = true) (r : Option PD.Outcome) :
    OutcomeSpecA regime (bot L) (bot R) r ↔
    OutcomeSpecA regime (bot fun k ↦ (L k).transpose) (bot fun k ↦ (R k).transpose) (transposeOutcome r) := by
  cases regime with
  | nobudget => exact outcomeAtA_transpose (hL 0) (hR 0) r
  | universal => exact forall_congr' fun k ↦ outcomeAtA_transpose (hL k) (hR k) r
  | eventual =>
    exact exists_congr fun k₀ ↦ forall_congr' fun k ↦ imp_congr_right fun _ ↦
      outcomeAtA_transpose (hL k) (hR k) r

/-! ### 6. Sanity: two transposed cells from their mirrors -/

/-- `(CupodBot, CupodBot) = (D, D)` eventually, from `(DupocBot, DupocBot) = (C, C)`
(`loeb_DupocBot_vs_DupocBot`): `(DupocBot k).transpose = CupodBot k` by `rfl`. -/
example : OutcomeSpecA .eventual (bot CupodBot) (bot CupodBot) (some (.D, .D)) :=
  (outcomeSpecA_transpose (L := DupocBot) (R := DupocBot) fragP_DupocBot fragP_DupocBot (some (.C, .C))).mp
    (OutcomeSpecA.eventual_of (by
      obtain ⟨k₀, h⟩ := loeb_DupocBot_vs_DupocBot
      exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph₂ (h k hk) (h k hk)⟩))

/-- The symmetry of the red cell, at every budget: what `DupocBot k` plays against `CupodBot k` is
the transposition of what `CupodBot k` plays against `DupocBot k`. -/
example (k : ℕ) (a : PD.Action) :
    plays (progCode (DupocBot k)) (progCode (CupodBot k)) a ↔
    plays (progCode (CupodBot k)) (progCode (DupocBot k)) a.swap :=
  plays_transpose (fragP_DupocBot k) (fragP_CupodBot k) a

/-! ### A program against its own transpose -/

/-- **A program and its transpose mirror each other**: what `A` plays against `τ̂A` is the transposition of
what `τ̂A` plays against `A`. -/
theorem plays_transpose_self {A : PD.Prog} (hA : fragP A = true) (hA' : fragP A.transpose = true)
    (a : PD.Action) :
    plays (progCode A) (progCode A.transpose) a ↔ plays (progCode A.transpose) (progCode A) a.swap := by
  have h := plays_transpose hA hA' a
  rwa [PD.Prog.transpose_transpose] at h

/-- **A program and its transpose play OPPOSITE actions**, whenever both play: the outcome of `A` against
`τ̂A` is never `(C, C)` nor `(D, D)`. -/
theorem opposite_of_plays_transpose {A : PD.Prog} (hA : fragP A = true) (hA' : fragP A.transpose = true)
    {a b : PD.Action} (ha : plays (progCode A) (progCode A.transpose) a)
    (hb : plays (progCode A.transpose) (progCode A) b) : b = a.swap :=
  plays_unique hb ((plays_transpose_self hA hA' a).mp ha)

end ArithS
