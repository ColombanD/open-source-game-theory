import PrisonersDilemma.Bots.LlmGenerations.OptimBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # OptimBot vs DefectBot → (D, D) at STAGGERED budgets — the `searchElseChain` payoff

The first outcome unlocked by the mixed-polarity reading rule (integrated
2026-08-04 from the Tier-2 proposal): OptimBot's defection against DefectBot lives
at the end of an else-else-then-then path — two REFUTED "DefectBot cooperates"
rungs (each paying the `search_f` floor `kOpp`), the fired "DefectBot defects"
rung, and the rung-3 self-search. `searchElseChain` internalizes that path as the
Löb premise `□_{kSelf} φD → φD` at cost `2·kOpp + O(log)`; at `kSelf = 65536·kOpp`
the premise fits `bloeb_engine`'s budget schema, the self-search fires, and the
outcome is `(D, D)`. At UNIFORM budgets the premise exceeds the asking budget and
OptimBot falls through to `C` — the recorded `open_blocked` cell; the stagger is
the honest price of self-knowledge that must replay two failed searches. -/

/-- The four-layer mixed-polarity decomposition of OptimBot's rung-3 defection. -/
theorem optim_plug2_decomp (k K : Nat) :
    OptimBot k K = plug2
      [ .elseL k .opp .self Action.C
          (.search K (.plays .self .opp Action.D) (.const Action.D)
            (.search k (.plays .opp .self Action.C)
              (.search K (.plays .self .opp Action.C) (.const Action.C)
                (.search k (.plays .opp .self Action.D)
                  (.search K (.plays .self .opp Action.D) (.const Action.D)
                    (.const Action.C))
                  (.const Action.C)))
              (.search k (.plays .opp .self Action.D)
                (.search K (.plays .self .opp Action.D) (.const Action.D)
                  (.const Action.C))
                (.const Action.C)))),
        .elseL k .opp .self Action.C
          (.search K (.plays .self .opp Action.C) (.const Action.C)
            (.search k (.plays .opp .self Action.D)
              (.search K (.plays .self .opp Action.D) (.const Action.D)
                (.const Action.C))
              (.const Action.C))),
        .thenL k (.plays .opp .self Action.D) (.const Action.C),
        .thenL K (.plays .self .opp Action.D) (.const Action.C) ]
      (.const Action.D) := rfl

/-- **The Löb premise via `searchElseChain`** — parametric in both budgets: the
    `bloeb_engine` premise for OptimBot's defection against DefectBot costs
    `2·k` (the two refuted cooperation rungs' floors) plus logarithmic overhead. -/
theorem od_loeb_premise (k K : Nat) (h1 : 1 ≤ k) :
    Pf (2 * k + 1000 * (Nat.log2 k + Nat.log2 K) + 100000)
       (.impl (.box K (.plays (OptimBot k K) DefectBot Action.D))
              (.plays (OptimBot k K) DefectBot Action.D)) := by
  set O := OptimBot k K with hO
  have hlogO : Nat.log2 k ≤ k := log2_le_self _
  -- the Σ₁ refutation of "DefectBot cooperates with O" (its actual play is D)
  have hneg : Pf (20 * (Nat.log2 k + Nat.log2 K) + 2000)
      (.neg (.plays DefectBot O Action.C)) := by
    refine Pf.atomNeg DefectBot O .D .C c_leaf
      ⟨(PlaysProof.const :
          PlaysProof DefectBot O (.const Action.D) Action.D c_leaf), le_rfl⟩
      (by decide) ?_
    simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot, c_leaf, hO]
    omega
  -- the cheap boxed fact for the fired rung: "DefectBot defects against O"
  have hboxD : Pf (300 * (Nat.log2 k + Nat.log2 K) + 50000)
      (.box k (.plays DefectBot O Action.D)) := by
    have hlog1 : Nat.log2 1 = 0 := by decide
    have hb1 : Pf (100 * (Nat.log2 k + Nat.log2 K) + 20000)
        (.box 1 (.plays DefectBot O Action.D)) := by
      refine Pf.boxIntro 1 _ _
        (Pf.atom ⟨(PlaysProof.const :
            PlaysProof DefectBot O (.const Action.D) Action.D c_leaf),
          by decide⟩) ?_
      simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot, hO, hlog1]
      omega
    have hmono : Pf (100 * (Nat.log2 k + Nat.log2 K) + 20000)
        (.impl (.box 1 (.plays DefectBot O Action.D))
               (.box k (.plays DefectBot O Action.D))) := by
      refine Pf.boxMono 1 k _ _ h1 ?_
      simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot, hO, hlog1]
      omega
    refine Pf.mp _ _ _ _ hmono hb1 ?_
    simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot, hO]
    omega
  -- the mixed-polarity chain over the four-layer telescope
  have hchain := Pf.searchElseChain
    (.elseL k .opp .self Action.C _) _ Action.D O DefectBot
    (optim_plug2_decomp k K)
    (k := 2 * k + 100 * (Nat.log2 k + Nat.log2 K) + 4000)
    (by
      simp only [layersCost, layerCost, guards2, guard2, implChain, List.foldr,
        Formula.size, Prog.size, Formula.subst, Prog.subst, numCost, c_guard,
        c_node, OptimBot, DefectBot, hO]
      omega)
  simp only [guards2, guard2, implChain, List.foldr, Formula.subst, Prog.subst]
    at hchain
  -- discharge the two refutation antecedents and the fired rung's box
  have h2 := Pf.mp _ _ _ _ hchain hneg (k :=
      2 * k + 200 * (Nat.log2 k + Nat.log2 K) + 10000) (by
    simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot, hO]
    omega)
  have h3 := Pf.mp _ _ _ _ h2 hneg (k :=
      2 * k + 300 * (Nat.log2 k + Nat.log2 K) + 16000) (by
    simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot, hO]
    omega)
  have h4 := Pf.mp _ _ _ _ h3 hboxD (k :=
      2 * k + 1000 * (Nat.log2 k + Nat.log2 K) + 100000) (by
    simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot, hO]
    omega)
  exact h4

/-- The target atom's size, in logs of both budgets. -/
theorem od_atom_size (k K : Nat) :
    (Formula.plays (OptimBot k K) DefectBot Action.D).size
      ≤ 20 * (Nat.log2 k + Nat.log2 K) + 200 := by
  simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot]
  omega

/-- **The bootstrap**: at the stagger `kSelf = 65536·k`, `bloeb_engine` turns the
    premise into `Pf kSelf φD` — OptimBot provably defects against DefectBot. -/
theorem od_D_provable_at_stagger :
    ∃ k₂, ∀ k, k > k₂ →
      proofSearch (65536 * k)
        (.plays (OptimBot k (65536 * k)) DefectBot Action.D) = true := by
  obtain ⟨Ka, hKa⟩ := linear_log2_add_le 40000000 8000000000
  refine ⟨max 1 Ka, fun k hk => ?_⟩
  have h1 : 1 ≤ k := (lt_of_le_of_lt (Nat.le_max_left _ _) hk).le
  have hKk : k ≥ Ka := (lt_of_le_of_lt (Nat.le_max_right _ _) hk).le
  set KS := 65536 * k with hKS
  have hkKS : k ≤ KS := by omega
  have hlkS : Nat.log2 k ≤ Nat.log2 KS := log2_mono hkKS
  have hbig : 40000000 * Nat.log2 KS + 8000000000 ≤ KS :=
    hKa KS (by omega)
  have hs := od_atom_size k KS
  set φ := Formula.plays (OptimBot k KS) DefectBot Action.D with hφ
  set P := 2 * k + 1000 * (Nat.log2 k + Nat.log2 KS) + 100000 with hP
  set W := P + φ.size + Nat.log2 KS + 8 with hW
  have hWk : 8192 * W ≤ KS := by
    rw [hW, hP]
    omega
  have hlg : Nat.log2 (1024 * W) ≤ Nat.log2 KS := log2_mono (by omega)
  have hl₁ : Nat.log2 (32 * W) ≤ Nat.log2 KS := log2_mono (by omega)
  have hl₃ : Nat.log2 (2048 * W) ≤ Nat.log2 KS := log2_mono (by omega)
  have hl₅ : Nat.log2 (8192 * W) ≤ Nat.log2 KS := log2_mono (by omega)
  have hLoeb : Pf P (.impl (.box KS φ) φ) := od_loeb_premise k KS h1
  have hpf : Pf (4096 * W) φ := by
    refine bloeb_engine φ P KS
      (1024 * W) (32 * W) (2048 * W) (2048 * W) (8192 * W)
      (16 * W) (16 * W) (64 * W) (32 * W) (128 * W) (32 * W) (16 * W)
      (256 * W) (512 * W) (16 * W) (640 * W) (704 * W) (768 * W) (2048 * W) (4096 * W)
      hLoeb ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · (try simp only [numCost, Formula.size]); omega
  have hpfk : Pf KS φ := Pf_mono hpf (by omega)
  exact (proofSearch_spec KS φ).2 hpfk

/-- The failed rungs: "DefectBot cooperates with OptimBot" is false, hence its
    guard search fails at every budget (soundness). -/
theorem od_ps_false_defC (k K B : Nat) :
    proofSearch B (.plays DefectBot (OptimBot k K) Action.C) = false := by
  cases h : proofSearch B (.plays DefectBot (OptimBot k K) Action.C) with
  | true =>
      exact absurd (proofSearch_sound _ _ h) (interp_DefectBot_plays_C_false _)
  | false => rfl

/-- The fired rung: "DefectBot defects against OptimBot" is certifiable at any
    positive budget. -/
theorem od_ps_true_defD (k K B : Nat) (hB : 1 ≤ B) :
    proofSearch B (.plays DefectBot (OptimBot k K) Action.D) = true := by
  refine (proofSearch_spec _ _).2 (Pf.atom ⟨(PlaysProof.const :
    PlaysProof DefectBot (OptimBot k K) (.const Action.D) Action.D c_leaf), ?_⟩)
  simp only [c_leaf]
  omega

/-- OptimBot's play: both cooperation rungs fail, the defection rung fires, and
    the staggered self-proof certifies rung 3's inner search. -/
theorem OptimBot_plays_D_against_DefectBot (k K fuel : Nat) (h1 : 1 ≤ k)
    (hD : proofSearch K (.plays (OptimBot k K) DefectBot Action.D) = true) :
    play (fuel + 6) (OptimBot k K) DefectBot = some .D := by
  have hg1 := od_ps_false_defC k K k
  have hg3 := od_ps_true_defD k K k h1
  show eval (fuel + 6) (OptimBot k K) DefectBot (OptimBot k K) = some .D
  unfold OptimBot at hg1 hg3 hD ⊢
  simp [eval, Prog.subst, Formula.subst, hg1, hg3, hD]

/-- **OptimBot vs DefectBot → (D, D) at the stagger `kSelf = 65536·kOpp`** — the
    flip predicted in `outcome_status.toml`, delivered by `searchElseChain`. -/
theorem llm_outcome_OptimBot_vs_DefectBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (OptimBot k (65536 * k)) DefectBot = some (.D, .D) := by
  obtain ⟨k₂, hk₂⟩ := od_D_provable_at_stagger
  refine ⟨k₂, fun k hk => ⟨6, ?_⟩⟩
  have h1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · omega
    · exact h
  have hA : play 6 (OptimBot k (65536 * k)) DefectBot = some .D := by
    simpa using OptimBot_plays_D_against_DefectBot k (65536 * k) 0 h1 (hk₂ k hk)
  have hB : play 6 DefectBot (OptimBot k (65536 * k)) = some .D := by
    simpa using play_DefectBot 5 (OptimBot k (65536 * k))
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
