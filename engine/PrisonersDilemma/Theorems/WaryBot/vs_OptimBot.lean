import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.LlmGenerations.OptimBot
import PrisonersDilemma.Theorems.WaryBot.Helpers
import PrisonersDilemma.Theorems.LlmGenerations.LlmLemmas
import PrisonersDilemma.Base.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # WaryBot vs OptimBot — the large-`k` `(C, C)` outcome

Both bots' aggressive branches are unreachable at large `k`: WaryBot cannot refute
OptimBot's cooperation (`neg B` census), so it trusts; and OptimBot's rung guards
(`Wary plays C/D vs Optim`) are unprovable, so it falls through to its fallback `C`.
The entangled `.neg`-guard fixpoint is closed by the WV budget census. -/

/-- WaryBot's C-cert (via the `search_f` floor) costs more than `k`. -/
theorem wo_wary_C_cert_cost (k : Nat) (O : Prog) :
    ∀ n, PlaysProof (WaryBot k) O (WaryBot k) Action.C n → k < n := by
  intro n cert
  unfold WaryBot at cert
  cases cert with
  | search_t hg hp => cases hp
  | search_f hneg hp => simp only [c_node] at *; omega

/-- `Wary plays C vs Optim` is floor-unprovable at every budget `≤ k`. -/
theorem wo_wary_C_vs_optim_unprov (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (WaryBot k) (OptimBot k k) Action.C) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k (· = .plays (WaryBot k) (OptimBot k k) Action.C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · rintro K' hK' φ' rfl hA
    cases hA with
    | mk hpp hn => have := wo_wary_C_cert_cost k (OptimBot k k) _ hpp; omega
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; subst h3; simp [WaryBot] at hme
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [WaryBot] at hme
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [WaryBot] at hme
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; simp [WaryBot] at hme
  · rintro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3; simp [WaryBot] at h1
  · rintro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3; subst h1; simp [WaryBot] at hme
  · rintro me oppo c hS L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases L with
    | nil => simp [searchPlug, WaryBot] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        simp only [searchPlug, WaryBot, Prog.search.injEq] at hme
        obtain ⟨_, _, hthen, _⟩ := hme
        cases tl with
        | nil => simp [searchPlug] at hthen
        | cons hd2 tl2 => obtain ⟨g2, ψ2, e2⟩ := hd2; simp [searchPlug] at hthen
  · rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    exfalso
    cases hd with
    | iteL z aT other => simp [ctxPlug, WaryBot] at hme
    | searchL g ψ e =>
        simp only [ctxPlug, WaryBot, Prog.search.injEq] at hme
        obtain ⟨_, _, hthen, _⟩ := hme
        cases L with
        | nil => simp [ctxPlug] at hthen
        | cons hd2 tl2 => cases hd2 <;> simp [ctxPlug] at hthen
  · -- polarity plug: WaryBot's `.neg` guard blocks every `elseL` layer, and its
    -- then-slot `.const .D ≠` any C-plug
    rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    exfalso
    cases hd with
    | thenL g ψ e =>
        simp only [plug2, WaryBot, Prog.search.injEq] at hme
        obtain ⟨-, -, hplug, -⟩ := hme
        cases L with
        | nil => simp [plug2] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [plug2] at hplug
    | elseL g P' Q' c' q =>
        simp only [plug2, WaryBot, Prog.search.injEq] at hme
        exact absurd hme.2.1 (by simp)

/-- OptimBot's D-cert vs WaryBot pays the floor: the only cheap path (rung-1 inner D)
    demands a proof of the floor-unprovable `Wary plays C vs Optim`. -/
theorem wo_optim_noD (k : Nat) :
    ∀ n, PlaysProof (OptimBot k k) (WaryBot k) (OptimBot k k) Action.D n → k < n := by
  intro n cert
  unfold OptimBot at cert
  cases cert with
  | search_t hg hp =>
      cases hp with
      | search_t hg2 hp2 =>
          cases hp2
          exfalso
          have hg' : Pf k (.plays (WaryBot k) (OptimBot k k) Action.C) := by
            simpa [Formula.subst, Prog.subst, OptimBot] using hg
          exact wo_wary_C_vs_optim_unprov k k _ hg' le_rfl rfl
      | search_f hneg2 hp2 => simp only [c_node] at *; omega
  | search_f hneg hp => simp only [c_node] at *; omega

/-- Under a `.sim`/`.bot (.sim …)` frame, a subst image being the literal `OptimBot`
    forces the opponent slot to be `OptimBot` (the outer guard's atoms are not
    producible otherwise). Companion of `WaryCensus.subst_eq_wary`. -/
theorem wo_subst_eq_optim {k : Nat} {q me o : Prog}
    (hme : (∃ p₂ q₂, me = .sim p₂ q₂) ∨ (∃ p₂ q₂, me = .bot (.sim p₂ q₂)))
    (h : q.subst me o = OptimBot k k) : o = OptimBot k k := by
  cases q with
  | const a => simp [Prog.subst, OptimBot] at h
  | self =>
      rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
        simp [Prog.subst, OptimBot] at h
  | opp => simpa [Prog.subst] using h
  | bot p => simp [Prog.subst, OptimBot] at h
  | sim p q => simp [Prog.subst, OptimBot] at h
  | ite b a p q => simp [Prog.subst, OptimBot] at h
  | search K φg pp qq =>
      simp only [OptimBot, Prog.subst, Prog.search.injEq] at h
      obtain ⟨hK, hg, hp, hq⟩ := h
      cases φg with
      | neg f1 => simp [Formula.subst] at hg
      | impl f1 f2 => simp [Formula.subst] at hg
      | box n' f1 => simp [Formula.subst] at hg
      | eq p' q' => simp [Formula.subst] at hg
      | diag g' f1 => simp [Formula.subst] at hg
      | plays x y a =>
          simp only [Formula.subst, Formula.plays.injEq] at hg
          obtain ⟨hx, hy, -⟩ := hg
          cases x with
          | const a' => simp [Prog.subst] at hx
          | bot p' => simp [Prog.subst] at hx
          | sim p' q' => simp [Prog.subst] at hx
          | ite b' a' p' q' => simp [Prog.subst] at hx
          | search K' g' p' q' => simp [Prog.subst] at hx
          | self =>
              rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
                simp [Prog.subst] at hx
          | opp =>
              simp only [Prog.subst] at hx
              cases y with
              | const a' => simp [Prog.subst] at hy
              | bot p' => simp [Prog.subst] at hy
              | sim p' q' => simp [Prog.subst] at hy
              | ite b' a' p' q' => simp [Prog.subst] at hy
              | search K' g' p' q' => simp [Prog.subst] at hy
              | self =>
                  rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
                    simp [Prog.subst] at hy
              | opp =>
                  simp only [Prog.subst] at hy
                  rw [hx] at hy
                  exact absurd hy (by simp)

/-- The entangled C-atom relation for the budget census: the singleton
    `(OptimBot, WaryBot)`. -/
def WO_S (k : Nat) : Prog → Prog → Prop :=
  fun p q => p = OptimBot k k ∧ q = WaryBot k

/-- **The heart of the matchup**: `S` cannot REFUTE OptimBot's cooperation against
    WaryBot at budget `k`. The WV budget census forces `Optim plays C vs Wary` true;
    `atomNeg` is blocked because OptimBot's only cheap D-cert cites the
    floor-unprovable `Wary plays C vs Optim`. -/
theorem wo_no_neg_B (k : Nat) :
    ¬ Pf k (.neg (.plays (OptimBot k k) (WaryBot k) Action.C)) := by
  intro h
  have hWV := PD.LlmLemmas.wv_budget_census k (WO_S k)
    (by rintro oppo z ⟨_, hq⟩; simp [WaryBot] at hq)
    (by
      rintro p q o ⟨hp, hq⟩
      exfalso
      have ho1 : o = OptimBot k k := wo_subst_eq_optim (Or.inl ⟨p, q, rfl⟩) hp
      have ho2 : o = WaryBot k := WaryCensus.subst_eq_wary (Or.inl ⟨p, q, rfl⟩) hq
      rw [ho1] at ho2; simp [OptimBot, WaryBot] at ho2)
    (by
      rintro p q o ⟨hp, hq⟩
      exfalso
      have ho1 : o = OptimBot k k := wo_subst_eq_optim (Or.inr ⟨p, q, rfl⟩) hp
      have ho2 : o = WaryBot k := WaryCensus.subst_eq_wary (Or.inr ⟨p, q, rfl⟩) hq
      rw [ho1] at ho2; simp [OptimBot, WaryBot] at ho2)
    (by rintro p q ⟨hp, hq⟩ n cert; subst hp; subst hq; exact wo_optim_noD k n cert)
    k _ h le_rfl
  rw [WV_neg, WV_plays] at hWV
  exact hWV (Or.inl ⟨rfl, rfl, rfl⟩)

/-- WaryBot trusts OptimBot: its refutation guard is unprovable, so it takes the
    `.const .C` else-branch. -/
theorem wo_wary_plays_C (k fuel : Nat) :
    play (fuel + 2) (WaryBot k) (OptimBot k k) = some .C := by
  have hg : proofSearch k (.neg (.plays (OptimBot k k) (WaryBot k) Action.C)) = false := by
    cases hcase : proofSearch k (.neg (.plays (OptimBot k k) (WaryBot k) Action.C)) with
    | false => rfl
    | true => exact absurd ((proofSearch_spec _ _).1 hcase) (wo_no_neg_B k)
  show eval (fuel + 2) (WaryBot k) (OptimBot k k) (WaryBot k) = some .C
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- `Wary plays C vs Optim` is unprovable at `k` (floor). -/
theorem wo_proofSearch_false_G1 (k : Nat) :
    proofSearch k (Formula.plays (WaryBot k) (OptimBot k k) Action.C) = false := by
  cases hcase : proofSearch k (Formula.plays (WaryBot k) (OptimBot k k) Action.C) with
  | false => rfl
  | true =>
      exact absurd (wo_wary_C_vs_optim_unprov k k _ ((proofSearch_spec _ _).1 hcase)
        le_rfl rfl) id

/-- `Wary plays D vs Optim` is semantically false (WaryBot cooperates), hence
    unprovable. -/
theorem wo_proofSearch_false_G3 (k : Nat) :
    proofSearch k (Formula.plays (WaryBot k) (OptimBot k k) Action.D) = false := by
  cases hcase : proofSearch k (Formula.plays (WaryBot k) (OptimBot k k) Action.D) with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨n, hn⟩ := Pf_sound _ _ ((proofSearch_spec _ _).1 hcase)
      have hC : play (n + 2) (WaryBot k) (OptimBot k k) = some .C :=
        wo_wary_plays_C k n
      have hD : play (n + 2) (WaryBot k) (OptimBot k k) = some .D := by
        have := eval_mono_le hn (n + 2) (by omega)
        simpa [play] using this
      rw [hC] at hD; cases hD

/-- OptimBot cooperates against WaryBot: both rung guards are unprovable, so it falls
    through every rung to the fallback. -/
theorem wo_optim_plays_C (k fuel : Nat) :
    play (fuel + 5) (OptimBot k k) (WaryBot k) = some .C := by
  have hG1 := wo_proofSearch_false_G1 k
  have hG3 := wo_proofSearch_false_G3 k
  show eval (fuel + 5) (OptimBot k k) (WaryBot k) (OptimBot k k) = some .C
  conv_lhs => rw [OptimBot]
  simp only [eval, Prog.subst, Formula.subst]
  simp only [OptimBot] at hG1 hG3
  simp only [hG1, hG3, if_false, Bool.false_eq_true]

/-- **WaryBot vs OptimBot: `(C, C)`** for all `k`. WaryBot trusts (cannot refute
    OptimBot's cooperation); OptimBot cooperates (rung guards unprovable). -/
theorem llm_outcome_WaryBot_vs_OptimBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (WaryBot k) (OptimBot k k) = some (.C, .C) := by
  refine ⟨0, fun k _ => ⟨5, ?_⟩⟩
  have hA : play 5 (WaryBot k) (OptimBot k k) = some .C := by
    simpa using wo_wary_plays_C k 3
  have hB : play 5 (OptimBot k k) (WaryBot k) = some .C := by
    simpa using wo_optim_plays_C k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
