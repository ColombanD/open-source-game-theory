import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.PrudentBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! ### PrudentBot same-`k` self-play — the honest `(D, D)` outcome (floor formalized 2026-07-09).

HISTORY: `prudence_self_prudent`/`prudent_self_loeb_premise`/the same-`k`
`outcome_PrudentBot_vs_PrudentBot` (mutual cooperation) were RETIRED 2026-07-02 as
axiom artifacts: PrudentBot's prudence about ITSELF ("I defect vs `.bot DefectBot`")
is an else-play of its OWN outer search — floor `k`, self-referentially unaffordable
at any single `k`. Cooperative self-play needs the two-tier `PrudentBot2` (below —
Critch/MIRI's PA+1 prudence).

RESOLVED (2026-07-09): the floor is a THEOREM — `no_provable_prudence_self_tail`, an
instance of `no_provable_searcherPlay_tail` (Base/Exclusion.lean; the target atom is
the SEARCHER'S OWN else-play, no simulator detour). The self-prudence guard fails at
every budget, so whichever way the outer Löbian guard resolves, PrudentBot defects
against itself: `outcome_PrudentBot_vs_PrudentBot = (D, D)` at every `k`. Bounded
Hume: a same-strength prover cannot certify its own failed search, so single-tier
prudence is self-defeating — mutual defection is the honest fixed point, and
`PrudentBot2`'s budget hierarchy (kIn > kOut) is exactly what escapes it. -/

/-- The floor at PrudentBot's own doorstep: no ≤ k certificate concludes any formula
    whose spine tail is PrudentBot's self-prudence fact "I play D vs `.bot DefectBot`"
    — the fact is TRUE (`PrudentBot_plays_D_vs_bot_DefectBot`), but it is the else-play
    of PrudentBot's own budget-`k` search. -/
theorem no_provable_prudence_self_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (PrudentBot k) (.bot DefectBot) .D) φ → False := by
  intro K φ hp hK ht
  refine no_provable_searcherPlay_tail k (.plays .opp .self .C)
      (.search k (.plays .opp (.bot DefectBot) .D) (.const .C) (.const .D))
      (.const .D) (.bot DefectBot) .D ?_ ?_ ?_ ?_ ?_ K φ hp hK ?_
  · simpa [Formula.subst, Prog.subst, PrudentBot] using
      interp_bot_DefectBot_plays_C_false (PrudentBot k)
  · intro c0 c1 h; simp at h
  · intro k₂ ψ₂ c1 h; simp at h
  · -- the searcher is not a telescope plugging the ELSE action (its then-actions
    -- are C at every depth, the target is D)
    intro L h
    cases L with
    | nil => simp [searchPlug] at h
    | cons hd tl =>
        obtain ⟨g₁, ψ₁, e₁⟩ := hd
        simp only [searchPlug, Prog.search.injEq] at h
        obtain ⟨-, -, h, -⟩ := h
        cases tl with
        | nil => simp [searchPlug] at h
        | cons hd' tl' =>
            obtain ⟨g₂, ψ₂', e₂⟩ := hd'
            simp only [searchPlug, Prog.search.injEq] at h
            obtain ⟨-, -, h, -⟩ := h
            cases tl' with
            | nil => simp [searchPlug] at h
            | cons hd'' tl'' =>
                obtain ⟨g₃, ψ₃, e₃⟩ := hd''
                simp [searchPlug] at h
  · -- nor a MIXED telescope: the inner search's then-branch is `.const .C ≠ .const .D`
    intro L h
    cases L with
    | nil => simp [ctxPlug] at h
    | cons hd tl =>
        cases hd with
        | searchL g' ψ' e' =>
            simp only [ctxPlug, Prog.search.injEq] at h
            exact const_ne_ctxPlug (by decide) tl h.2.2.1
        | iteL z' aT' other' => simp [ctxPlug] at h
  · simpa [PrudentBot] using ht

/-- PrudentBot's prudence guard about ITSELF fails at every budget — the floor's bite:
    its own defection vs `.bot DefectBot` is real but costs more than `k` to certify. -/
theorem proofSearch_false_prudence_self (k : Nat) :
    proofSearch k (.plays (PrudentBot k) (.bot DefectBot) .D) = false := by
  cases h : proofSearch k (.plays (PrudentBot k) (.bot DefectBot) .D) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => no_provable_prudence_self_tail k k _ hp le_rfl (by simp))
  | false => rfl

/-- PrudentBot defects against ITSELF at the same budget: if the outer (Löbian) guard
    fails, the else defects; if it fires, the self-prudence guard is floor-blocked and
    the inner else defects. Either way, D. -/
theorem PrudentBot_plays_D_against_self (k fuel : Nat) :
    play (fuel + 3) (PrudentBot k) (PrudentBot k) = some .D := by
  cases h1 : proofSearch k (.plays (PrudentBot k) (PrudentBot k) .C) with
  | false =>
      simpa [Nat.add_assoc] using
        PrudentBot_plays_D_of_search_false k (fuel + 1) (PrudentBot k) h1
  | true =>
      exact prudent_eval_inner_false k fuel (PrudentBot k) h1
        (proofSearch_false_prudence_self k)

/-- **The honest same-`k` PrudentBot self-play — `(D, D)` at every budget.** Two equal
    provers, each needing to certify its own failed search to trust the other: neither
    can, both defect. The cooperative fixed point exists only one tier up
    (`outcome_PrudentBot2_vs_PrudentBot2`, below). -/
theorem outcome_PrudentBot_vs_PrudentBot (k fuel : Nat) :
    outcome (fuel + 3) (PrudentBot k) (PrudentBot k) = some (.D, .D) := by
  have hA := PrudentBot_plays_D_against_self k fuel
  simp [outcome, hA]

/-! ### PrudentBot SELF-PLAY — RECOVERED with the two-tier `PrudentBot2` (T3.2b, 2026-07-03).

`PrudentBot2 k (4k+100)`: prudence at a strictly larger budget than the cooperation search —
the bounded PA+1. Its self-prudence ("I defect vs `.bot DefectBot`") is an else-play of its
OWN outer search, floored at `k`; the inner literal `4k+100` affords it. -/

/-- `PrudentBot2 k j` defects against `.bot DefectBot` — certified at the outer FLOOR `k`:
    `search_f` over the `atomNeg` refutation of the outer guard ("botDefect cooperates
    with me"). -/
theorem prudence_P2 (k j : Nat) :
    Pf (k + Nat.log2 k + Nat.log2 j + 22)
      (.plays (PrudentBot2 k j) (.bot DefectBot) .D) := by
  have hneg : Pf (Nat.log2 k + Nat.log2 j + 20)
      (.neg (.plays (.bot DefectBot) (PrudentBot2 k j) .C)) := by
    refine Pf.atomNeg (.bot DefectBot) (PrudentBot2 k j) .D .C 2
      ⟨PlaysProof.bot PlaysProof.const, by decide⟩ (by decide) ?_
    simp only [numCost, Formula.size, Prog.size, DefectBot, PrudentBot2]
    omega
  refine Pf.atom (⟨PlaysProof.search_f hneg PlaysProof.const, ?_⟩ :
    AtomProvable (k + Nat.log2 k + Nat.log2 j + 22)
      (.plays (PrudentBot2 k j) (.bot DefectBot) .D))
  show c_leaf + (Nat.log2 k + Nat.log2 j + 20) + k + c_node ≤ _
  simp only [c_leaf, c_node]
  omega

/-- Both guards fired ⇒ `PrudentBot2` cooperates. -/
theorem P2_eval_both_true (k j fuel : Nat) (q : Prog)
    (h1 : proofSearch k (.plays q (PrudentBot2 k j) .C) = true)
    (h2 : proofSearch j (.plays q (.bot DefectBot) .D) = true) :
    play (fuel + 3) (PrudentBot2 k j) q = some .C := by
  show eval (fuel + 3) (PrudentBot2 k j) q (PrudentBot2 k j) = some .C
  unfold PrudentBot2 at h1 ⊢
  simp [eval, Prog.subst, Formula.subst, h1, h2]

/-- Outer guard failed ⇒ `PrudentBot2` defects. -/
theorem P2_eval_outer_false (k j fuel : Nat) (q : Prog)
    (h1 : proofSearch k (.plays q (PrudentBot2 k j) .C) = false) :
    play (fuel + 2) (PrudentBot2 k j) q = some .D := by
  show eval (fuel + 2) (PrudentBot2 k j) q (PrudentBot2 k j) = some .D
  unfold PrudentBot2 at h1 ⊢
  simp [eval, Prog.subst, Formula.subst, h1]

/-- Inversion: a cooperative play forces the outer guard. -/
theorem P2_outer_true_of_play_C (k j n : Nat) (q : Prog)
    (h : play n (PrudentBot2 k j) q = some .C) :
    proofSearch k (.plays q (PrudentBot2 k j) .C) = true := by
  cases hps : proofSearch k (.plays q (PrudentBot2 k j) .C) with
  | true => rfl
  | false =>
    exfalso
    have hD : play (n + 2) (PrudentBot2 k j) q = some .D := P2_eval_outer_false k j n q hps
    have hC : play (n + 2) (PrudentBot2 k j) q = some .C := by
      unfold play at h ⊢; exact eval_mono_le h (n + 2) (by omega)
    rw [hC] at hD; cases hD

/-- The self-play Löb premise — `searchThenSearch_t` on the two-tier shape, its inner
    prudence premise the floored `prudence_P2` (fits: `k + log2 k + log2 j + 22 ≤ 4k+100`). -/
theorem P2_self_loeb_premise (k : Nat) :
    Pf (30 * Nat.log2 k + 800)
      (.impl (.box k (.plays (PrudentBot2 k (4*k+100)) (PrudentBot2 k (4*k+100)) .C))
             (.plays (PrudentBot2 k (4*k+100)) (PrudentBot2 k (4*k+100)) .C)) := by
  have hlk := log2_le_self k
  have hlgj := log2_stagger4_le k
  refine Pf.searchThenSearch_t k (4*k+100)
    (k + Nat.log2 k + Nat.log2 (4*k+100) + 22)
    (.plays .opp .self .C) (.plays .opp (.bot DefectBot) .D)
    .C .D (.const .D) (PrudentBot2 k (4*k+100)) (PrudentBot2 k (4*k+100)) rfl
    (by simpa [Formula.subst, Prog.subst] using prudence_P2 k (4*k+100)) (by omega) ?_
  simp only [numCost, Formula.subst, Prog.subst, Formula.size, Prog.size, PrudentBot2, DefectBot,
    c_guard]
  omega

/-- **Two-tier PrudentBot self-play → (C, C)** for all large enough `k` — the recovery of
    the retired same-`k` self-cooperation, at the honest (PA+1-style) parameterization. -/
theorem outcome_PrudentBot2_vs_PrudentBot2 :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot2 k (4*k+100)) (PrudentBot2 k (4*k+100))
        = some (.C, .C) := by
  have hφsz : ∀ k,
      (Formula.plays (PrudentBot2 k (4*k+100)) (PrudentBot2 k (4*k+100)) .C).size
      ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    have hlgj := log2_stagger4_le k
    simp only [numCost, Formula.size, Prog.size, PrudentBot2, DefectBot]
    omega
  have hpm : ∀ k, 30 * Nat.log2 k + 800 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id
    (fun k => Formula.plays (PrudentBot2 k (4*k+100)) (PrudentBot2 k (4*k+100)) .C)
    (fun k => 30 * Nat.log2 k + 800) 0 hφsz hpm
    (fun k _ => P2_self_loeb_premise k)
  refine ⟨k₂, fun k hk => ?_⟩
  have hlk := log2_le_self k
  have hlgj := log2_stagger4_le k
  obtain ⟨m, hm⟩ := hk₂ k hk
  obtain ⟨n, hplay⟩ := Pf_sound m _ hm
  have hpsOuter : proofSearch k
      (.plays (PrudentBot2 k (4*k+100)) (PrudentBot2 k (4*k+100)) .C) = true :=
    P2_outer_true_of_play_C k (4*k+100) n _ hplay
  have hprud : proofSearch (4*k+100)
      (.plays (PrudentBot2 k (4*k+100)) (.bot DefectBot) .D) = true := by
    refine (proofSearch_spec _ _).2 (Pf_mono (prudence_P2 k (4*k+100)) ?_)
    omega
  refine ⟨3, ?_⟩
  have hA : play 3 (PrudentBot2 k (4*k+100)) (PrudentBot2 k (4*k+100)) = some .C := by
    simpa using P2_eval_both_true k (4*k+100) 0 (PrudentBot2 k (4*k+100)) hpsOuter hprud
  exact outcome_of_plays _ _ _ _ _ hA hA
end PD.Theorems
