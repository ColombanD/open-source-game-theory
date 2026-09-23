import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Outcome

/-!
# DIMCID vs CupodBot — `(D, D)` past the Löb threshold, by MUTUAL bounded Löb

The last stipulated frontier cell, and the ALIGNED counterpart of
`vs_DupocBot.lean`: each bot's guard asks for exactly the action the other's
THEN-branch produces, so the cycle is self-supporting and bounded Löb closes it
on MUTUAL DEFECTION. The value the enlarged-zoo table stipulated — here it is
correct, unlike the `DupocBot` and `CIMCIC` entries the same method overturned.

Predicted by the tau layer's alignment rule (`Tau/Theorems/TauDIMCID/Helpers`,
"The ENTANGLED cells"), where the same pair is the zoo's first ALIGNED-on-`D`
system.

* `Af` = "DIMCID plays D vs Cupod", `Bf` = "Cupod plays D vs DIMCID".
* **Leg 1** (`□Af → Bf`) is CupodBot's own source reading: its guard is literally
  "my opponent defects against me", so `searchBranch` gives it directly.
* **Leg 2** (`□Bf → Af`) is DIMCID's: `searchBranch` yields
  `□(DIMCID-plays-C → Bf) → Af`, and `implK` (`Bf → (anything → Bf)`) pushed
  under the box by `boxIntro`/`axK` supplies the missing step. The same bridge
  the DIMCID diagonal needs (`Tau`'s `dimcid_quine_loeb_premise`).

Contrast the anti-aligned `DIMCID × DupocBot`, where the actions mismatch, no
cycle closes, and the FLOOR forces both defaults instead.
-/

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- **The mutual engine**: past a threshold, DIMCID's defection against CupodBot
    is provable. `Bf` is DIMCID's GUARD FORMULA (not a plays-atom) — the same
    assignment base `llm_outcome_CIMCIC_vs_DupocBot` uses, which is what keeps
    both legs inside `implTrans` and avoids `axK` (whose subscript arithmetic the
    same-`k` engine cannot satisfy). -/
theorem dc_mutual :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ m, Pf m (.plays (DIMCID k) (CupodBot k) Action.D) := by
  have hlog : ∀ k, Nat.log2 k ≤ k := log2_le_self
  refine mutual_pblt_engine_id
    (fun k => .plays (DIMCID k) (CupodBot k) Action.D)
    (fun k => .impl (.plays (DIMCID k) (CupodBot k) Action.C)
                    (.plays (CupodBot k) (DIMCID k) Action.D))
    (fun k => 100 * Nat.log2 k + 1000) (fun k => 100 * Nat.log2 k + 1000) 0
    ?_ ?_ (fun k => le_rfl) (fun k => le_rfl) ?_ ?_
  · intro k
    have := hlog k
    simp only [Formula.size, Prog.size, DIMCID, CupodBot, numCost]
    omega
  · intro k
    have := hlog k
    simp only [Formula.size, Prog.size, DIMCID, CupodBot, numCost]
    omega
  · -- Leg 1: □Af → Bf. CupodBot reads its own guard (which IS `Af`), giving
    -- `□Af → Cupod plays D`; `implK` then weakens that into DIMCID's guard.
    intro k _
    have hcup : Pf ((Formula.impl
          (.box k (.plays (DIMCID k) (CupodBot k) Action.D))
          (.plays (CupodBot k) (DIMCID k) Action.D)).size)
        (.impl (.box k (.plays (DIMCID k) (CupodBot k) Action.D))
               (.plays (CupodBot k) (DIMCID k) Action.D)) := by
      have := Pf.searchBranch k (.plays .opp .self Action.D) .D .C
        (CupodBot k) (DIMCID k) rfl (Nat.le_refl _)
      simpa [CupodBot, Formula.subst, Prog.subst] using this
    have hK := Pf.implK (.plays (CupodBot k) (DIMCID k) Action.D)
        (.plays (DIMCID k) (CupodBot k) Action.C) (Nat.le_refl _)
    have htr := Pf.implTrans _ _ _ _ _ hcup hK (Nat.le_refl _)
    refine Pf_mono htr ?_
    have := hlog k
    simp only [Formula.size, Prog.size, DIMCID, CupodBot, numCost]
    omega
  · -- Leg 2: □Bf → Af. `Bf` IS DIMCID's substituted guard, so `searchBranch`
    -- gives this directly.
    intro k _
    have hread : Pf ((Formula.impl
          (.box k (.impl (.plays (DIMCID k) (CupodBot k) Action.C)
                         (.plays (CupodBot k) (DIMCID k) Action.D)))
          (.plays (DIMCID k) (CupodBot k) Action.D)).size)
        (.impl
          (.box k (.impl (.plays (DIMCID k) (CupodBot k) Action.C)
                         (.plays (CupodBot k) (DIMCID k) Action.D)))
          (.plays (DIMCID k) (CupodBot k) Action.D)) := by
      have := Pf.searchBranch k
        (.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D))
        Action.D Action.C (DIMCID k) (CupodBot k) rfl (Nat.le_refl _)
      simpa [DIMCID, Formula.subst, Prog.subst] using this
    refine Pf_mono hread ?_
    have := hlog k
    simp only [Formula.size, Prog.size, DIMCID, CupodBot, numCost]
    omega

/-- From a real DEFECTING play of DIMCID against CupodBot, DIMCID's guard must
    have fired (eval inversion — a failed search takes the trusting `C`). -/
theorem dc_guard_fired (k n : Nat)
    (h : play n (DIMCID k) (CupodBot k) = some .D) :
    Pf k (.impl (.plays (DIMCID k) (CupodBot k) Action.C)
                (.plays (CupodBot k) (DIMCID k) Action.D)) := by
  have hguard : proofSearch k
      (.impl (.plays (DIMCID k) (CupodBot k) Action.C)
             (.plays (CupodBot k) (DIMCID k) Action.D)) = true := by
    cases hps : proofSearch k
        (.impl (.plays (DIMCID k) (CupodBot k) Action.C)
               (.plays (CupodBot k) (DIMCID k) Action.D)) with
    | true => rfl
    | false =>
        exfalso
        have hps' : proofSearch k
            ((Formula.impl (.plays .self .opp Action.C)
                           (.plays .opp .self Action.D)).subst
              (DIMCID k) (CupodBot k)) = false := hps
        rcases n with _ | _ | n
        · simp [play, eval] at h
        · simp [play, eval, DIMCID] at h
        · have hev : play (n + 2) (DIMCID k) (CupodBot k) = some .C := by
            show (if proofSearch k
                    ((Formula.impl (.plays .self .opp Action.C)
                                   (.plays .opp .self Action.D)).subst
                      (DIMCID k) (CupodBot k))
                  then eval (n + 1) (DIMCID k) (CupodBot k) (.const Action.D)
                  else eval (n + 1) (DIMCID k) (CupodBot k) (.const Action.C)) = some .C
            rw [hps']; simp [eval]
          rw [hev] at h; cases h
  exact (proofSearch_spec _ _).1 hguard

/-- With the guard provable at `k`, DIMCID's own defection is cheaply certified
    (`search_t` cites via `c_guard`, not the premise transcript). -/
theorem dc_af_at_k (k : Nat) (hthr : Nat.log2 k + 3 ≤ k)
    (hBf : Pf k (.impl (.plays (DIMCID k) (CupodBot k) Action.C)
                       (.plays (CupodBot k) (DIMCID k) Action.D))) :
    Pf k (.plays (DIMCID k) (CupodBot k) Action.D) := by
  have hBf' : Pf k ((Formula.impl (.plays .self .opp Action.C)
                                  (.plays .opp .self Action.D)).subst
      (DIMCID k) (CupodBot k)) := hBf
  refine Pf.atom (⟨PlaysProof.search_t hBf' PlaysProof.const, ?_⟩ :
    AtomProvable k (.plays (DIMCID k) (CupodBot k) Action.D))
  show c_leaf + c_guard k + c_node ≤ k
  simp only [c_leaf, c_node, c_guard, numCost]; omega

/-- CupodBot defects once DIMCID's defection is provable at `k` — its guard IS
    that atom. -/
theorem dc_CupodBot_plays_D (k fuel : Nat)
    (hAf : Pf k (.plays (DIMCID k) (CupodBot k) Action.D)) :
    play (fuel + 2) (CupodBot k) (DIMCID k) = some .D := by
  have hguard : proofSearch k (.plays (DIMCID k) (CupodBot k) Action.D) = true :=
    (proofSearch_spec _ _).2 hAf
  show eval (fuel + 2) (CupodBot k) (DIMCID k) (CupodBot k) = some .D
  unfold CupodBot at hguard ⊢
  simp [eval, Prog.subst, Formula.subst, hguard]

/-- **DIMCID vs CupodBot → (D, D)** for all sufficiently large `k`: the ALIGNED
    pair, closed by mutual bounded Löb on defection. -/
@[outcome]
theorem outcome_DIMCID_vs_CupodBot :
    OutcomeSpec .eventual 2
      DIMCID CupodBot (some (.D, .D)) := by
  obtain ⟨ke, hke⟩ := dc_mutual
  obtain ⟨kt, hkt⟩ := linear_log2_add_le 1 3
  refine ⟨max ke kt, fun k hk fuel => outcome_at_of_ex ?_ ?_ fuel⟩
  -- The old existential-fuel argument, verbatim: some fuel determines the outcome…
  · have hkke : ke < k := lt_of_le_of_lt (Nat.le_max_left _ _) hk
    have hkkt : Nat.log2 k + 3 ≤ k := by
      have := hkt k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk)); omega
    obtain ⟨m, hm⟩ := hke k hkke
    obtain ⟨n, hnA⟩ := Pf_sound m _ hm
    have hBf := dc_guard_fired k n hnA
    have hAf := dc_af_at_k k hkkt hBf
    have hB : play (n + 2) (CupodBot k) (DIMCID k) = some .D := dc_CupodBot_plays_D k n hAf
    have hnA' : eval n (DIMCID k) (CupodBot k) (DIMCID k) = some .D := hnA
    have hA : play (n + 2) (DIMCID k) (CupodBot k) = some .D :=
      eval_mono_le hnA' (n + 2) (Nat.le_add_right _ 2)
    exact ⟨n + 2, outcome_of_plays _ _ _ _ _ hA hB⟩
  -- …and the match is determined at fuel 2 whatever the oracle says, so
  -- determinism (`play_unique`) pins the value there and monotonicity does the rest.
  · exact outcome_total_of_plays (play_search_const_total _ _ _ _ _ 0) (play_search_const_total _ _ _ _ _ 0)
end PD.Theorems
