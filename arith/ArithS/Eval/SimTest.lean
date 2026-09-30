import ArithS.Eval.EvalN

/-!
# ArithS.SimTest — sanity checks for the `pSim` clause (roadmap M3 step (b))

`Mirror := pSim pOpp pSelf`, the code of the engine's `MirrorBot := .sim .opp .self`
("simulate the opponent against itself"): against a constant bot it plays the constant; against
itself it never terminates (the engine's `none`); it is τ-symmetric, and substitution commutes
with τ on it.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping

/-- The code of the engine's `MirrorBot`. -/
noncomputable def Mirror : ℕ := pSim pOpp pSelf

/-- Mirror plays the constant against a constant bot (fuel 2: one `sim` step, one `const` step). -/
theorem mirror_vs_const (a : ℕ) : EvalGraph 2 Mirror (pConst a) Mirror a := by
  unfold Mirror
  rw [show (2 : ℕ) = 1 + 1 from rfl, EvalGraph.sim_iff, substCode_opp, substCode_self,
    show (1 : ℕ) = 0 + 1 from rfl, EvalGraph.const_iff]

/-- Mirror vs Mirror never terminates: `sim` re-enters the same frame at every step. -/
theorem mirror_vs_mirror (n : ℕ) : ∀ a, ¬EvalGraph n Mirror Mirror Mirror a := by
  induction n with
  | zero => intro a h; exact EvalGraph.zero_iff h
  | succ n ih =>
    intro a h
    unfold Mirror at h
    rw [EvalGraph.sim_iff, substCode_opp, substCode_self] at h
    exact ih a h

/-- Determinism through the `sim` clause: any result of Mirror against `pConst a` is `a`. -/
theorem mirror_vs_const_unique {n a b : ℕ} (h : EvalGraph n Mirror (pConst a) Mirror b) : b = a :=
  EvalGraph.unique' h (mirror_vs_const a)

theorem transposeCode_Mirror : transposeCode Mirror = Mirror := by
  unfold Mirror transposeCode; simp

/-- `transposeCode_substCode` at Mirror. -/
theorem transposeCode_substCode_Mirror (me opp : ℕ) :
    transposeCode (substCode me opp Mirror) = substCode (transposeCode me) (transposeCode opp) Mirror := by
  rw [transposeCode_substCode, transposeCode_Mirror]

/-- The outer-reference semantics on a concrete searcher: a search node placed under `sim`
evaluates its guard against the OUTER frame, whatever the inner frame is. -/
theorem sim_search_outer_guard (n k g p q me opp a : ℕ) (hg : IsSemiformula LAct 6 g) :
    EvalGraph (n + 1 + 1) me opp (pSim (pSearch k g p q) pSelf) a ↔
    ((LenBox TAct k (guardCode g me opp) ∧
        EvalGraph n (pSearch k (substTemplate me opp g) (substCode me opp p) (substCode me opp q)) me
          (substCode me opp p) a) ∨
      (¬LenBox TAct k (guardCode g me opp) ∧
        EvalGraph n (pSearch k (substTemplate me opp g) (substCode me opp p) (substCode me opp q)) me
          (substCode me opp q) a)) := by
  rw [EvalGraph.sim_iff, substCode_search, substCode_self, EvalGraph.search_iff, guardCodeB_substTemplate hg,
    substTemplate_of_template hg]

/-- The same on a SEVEN-variable template (route (c)'s budget slot; the `.sim` debt discharged): a search node placed under `sim` evaluates its guard against the OUTER frame at ITS OWN
budget `k` — `guardCodeB g me opp k`, not `guardCodeB g (substCode me opp (pSearch k g p q)) me k`, the
inner frame's. -/
theorem sim_search_outer_guard₇ (n k g p q me opp a : ℕ) (hg : IsSemiformula LAct 7 g) :
    EvalGraph (n + 1 + 1) me opp (pSim (pSearch k g p q) pSelf) a ↔
    ((LenBox TAct k (guardCodeB g me opp k) ∧
        EvalGraph n (pSearch k (substTemplate me opp g) (substCode me opp p) (substCode me opp q)) me
          (substCode me opp p) a) ∨
      (¬LenBox TAct k (guardCodeB g me opp k) ∧
        EvalGraph n (pSearch k (substTemplate me opp g) (substCode me opp p) (substCode me opp q)) me
          (substCode me opp q) a)) := by
  rw [EvalGraph.sim_iff, substCode_search, substCode_self, EvalGraph.search_iff, guardCodeB_substTemplate₇ hg]

end ArithS
