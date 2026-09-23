import PrisonersDilemma.Bots.LlmGenerations.OptimBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.DefectBot.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems

theorem optim_dbot_selfD_loeb (k S : Nat) (hk : 2 ≤ k) :
    Pf (500 * k + 500 * Nat.log2 S + 500 * Nat.log2 k + 100000)
      (.impl (.box S (.plays (OptimBot k S) DefectBot.bot Action.D))
        (.plays (OptimBot k S) DefectBot.bot Action.D)) := by
  have hchain := Pf.searchElseChain
    (SearchLayer2.elseL k .opp .self Action.C
      (.search S (.plays .self .opp Action.D) (.const Action.D)
        (.search k (.plays .opp .self Action.C)
          (.search S (.plays .self .opp Action.C) (.const Action.C)
            (.search k (.plays .opp .self Action.D)
              (.search S (.plays .self .opp Action.D) (.const Action.D) (.const Action.C))
              (.const Action.C)))
          (.search k (.plays .opp .self Action.D)
            (.search S (.plays .self .opp Action.D) (.const Action.D) (.const Action.C))
            (.const Action.C)))))
    [ SearchLayer2.elseL k .opp .self Action.C
        (.search S (.plays .self .opp Action.C) (.const Action.C)
          (.search k (.plays .opp .self Action.D)
            (.search S (.plays .self .opp Action.D) (.const Action.D) (.const Action.C))
            (.const Action.C))),
      SearchLayer2.thenL k (.plays .opp .self Action.D) (.const Action.C),
      SearchLayer2.thenL S (.plays .self .opp Action.D) (.const Action.C) ]
    Action.D (OptimBot k S) DefectBot.bot (by unfold OptimBot; rfl) (Nat.le_refl _)
  simp only [guard2, guards2, implChain, List.foldr, Formula.subst, Prog.subst] at hchain
  have href : Pf _ (.neg (.plays DefectBot.bot (OptimBot k S) Action.C)) :=
    Pf.atomNeg DefectBot.bot (OptimBot k S) .D .C 2
      ⟨PlaysProof.bot PlaysProof.const, by decide⟩ (by decide) (Nat.le_refl _)
  have hcertD : AtomProvable k (.plays DefectBot.bot (OptimBot k S) Action.D) :=
    ⟨PlaysProof.bot PlaysProof.const, by show c_leaf + c_node ≤ k; simp only [c_leaf, c_node]; omega⟩
  have hbox3 : Pf _ (.box k (.plays DefectBot.bot (OptimBot k S) Action.D)) :=
    Pf.boxIntro k _ _ (Pf.atom hcertD) (Nat.le_refl _)
  have h1 := Pf.mp _ _ _ _ hchain href (Nat.le_refl _)
  have h2 := Pf.mp _ _ _ _ h1 href (Nat.le_refl _)
  have h3 := Pf.mp _ _ _ _ h2 hbox3 (Nat.le_refl _)
  refine Pf_mono h3 ?_
  simp only [numCost, Formula.size, Prog.size, OptimBot, DefectBot, layersCost, layerCost,
    c_node, c_guard]
  have hlS := log2_le_self S
  have hlk := log2_le_self k
  omega

theorem optim_dbot_atom_size (k S : Nat) :
    (Formula.plays (OptimBot k S) DefectBot.bot Action.D).size
      ≤ 30 * Nat.log2 k + 30 * Nat.log2 S + 300 := by
  simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot]
  have hlS := log2_le_self S
  have hlk := log2_le_self k
  omega

theorem optim_log2_1e8 (k : Nat) (hk : 1 ≤ k) :
    Nat.log2 (100000000 * k) ≤ Nat.log2 k + 27 := by
  have h1 : k < 2 ^ (Nat.log2 k + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by norm_num) k
  have h3 : 100000000 * k < 2 ^ (Nat.log2 k + 28) := by
    have hp : 1 ≤ (2:Nat) ^ (Nat.log2 k + 1) := Nat.one_le_two_pow
    have he : (2:Nat) ^ (Nat.log2 k + 28) = 2 ^ (Nat.log2 k + 1) * 134217728 := by
      rw [show Nat.log2 k + 28 = (Nat.log2 k + 1) + 27 from rfl, pow_add]; norm_num
    omega
  have := (Nat.log2_lt (by omega)).2 h3
  omega

theorem optim_dbot_selfD_provable :
    ∃ k₂, ∀ k, k > k₂ →
      proofSearch (100000000 * k) (.plays (OptimBot k (100000000 * k)) DefectBot.bot Action.D) = true := by
  refine ⟨100, fun k hk => ?_⟩
  have h1 : 1 ≤ k := by omega
  have h2k : 2 ≤ k := by omega
  have hpm := optim_dbot_selfD_loeb k (100000000 * k) h2k
  have hlogS : Nat.log2 (100000000 * k) ≤ Nat.log2 k + 27 := optim_log2_1e8 k h1
  have hsz := optim_dbot_atom_size k (100000000 * k)
  set φ := Formula.plays (OptimBot k (100000000 * k)) DefectBot.bot Action.D with hφ
  set pm := 500 * k + 500 * Nat.log2 (100000000 * k) + 500 * Nat.log2 k + 100000 with hpmdef
  set W := pm + φ.size + Nat.log2 (100000000 * k) + 8 with hW
  have hWbound : 8192 * W ≤ 100000000 * k := by
    have hlk := log2_le_self k
    rw [hW, hpmdef]
    omega
  have hlg : Nat.log2 (1024 * W) ≤ Nat.log2 (100000000 * k) := log2_mono (by omega)
  have hl₁ : Nat.log2 (32 * W) ≤ Nat.log2 (100000000 * k) := log2_mono (by omega)
  have hl₃ : Nat.log2 (2048 * W) ≤ Nat.log2 (100000000 * k) := log2_mono (by omega)
  have hl₅ : Nat.log2 (8192 * W) ≤ Nat.log2 (100000000 * k) := log2_mono (by omega)
  have hpf : Pf (4096 * W) φ := by
    refine bloeb_engine φ pm (100000000 * k)
      (1024 * W) (32 * W) (2048 * W) (2048 * W) (8192 * W)
      (16 * W) (16 * W) (64 * W) (32 * W) (128 * W) (32 * W) (16 * W)
      (256 * W) (512 * W) (16 * W) (640 * W) (704 * W) (768 * W) (2048 * W) (4096 * W)
      hpm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · (try simp only [numCost, Formula.size]); omega
  have hpfS : Pf (100000000 * k) φ := Pf_mono hpf (by omega)
  exact (proofSearch_spec (100000000 * k) φ).2 hpfS

theorem optim_ps_oppC_false (k S : Nat) :
    proofSearch k (.plays DefectBot.bot (OptimBot k S) Action.C) = false := by
  cases h : proofSearch k (.plays DefectBot.bot (OptimBot k S) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_bot_DefectBot_plays_C_false _)
  | false => rfl

theorem optim_ps_oppD_true (k S : Nat) (hk : 2 ≤ k) :
    proofSearch k (.plays DefectBot.bot (OptimBot k S) Action.D) = true :=
  (proofSearch_spec _ _).2 (Pf.atom
    ⟨PlaysProof.bot PlaysProof.const, by show c_leaf + c_node ≤ k; simp only [c_leaf, c_node]; omega⟩)

theorem optim_plays_D_vs_botDefect (k S fuel : Nat)
    (hselfD : proofSearch S (.plays (OptimBot k S) DefectBot.bot Action.D) = true)
    (hoppC : proofSearch k (.plays DefectBot.bot (OptimBot k S) Action.C) = false)
    (hoppD : proofSearch k (.plays DefectBot.bot (OptimBot k S) Action.D) = true) :
    play (fuel + 10) (OptimBot k S) DefectBot.bot = some .D := by
  show eval (fuel + 10) (OptimBot k S) DefectBot.bot (OptimBot k S) = some .D
  unfold OptimBot at hselfD hoppC hoppD ⊢
  simp [eval, Prog.subst, Formula.subst, hselfD, hoppC, hoppD]

theorem dbot_plays_C_vs_optim (k S fuel : Nat)
    (hselfD : proofSearch S (.plays (OptimBot k S) DefectBot.bot Action.D) = true)
    (hoppC : proofSearch k (.plays DefectBot.bot (OptimBot k S) Action.C) = false)
    (hoppD : proofSearch k (.plays DefectBot.bot (OptimBot k S) Action.D) = true) :
    play (fuel + 12) DBot (OptimBot k S) = some .C := by
  have hInner : play (fuel + 10) (OptimBot k S) DefectBot.bot = some .D :=
    optim_plays_D_vs_botDefect k S fuel hselfD hoppC hoppD
  have hGuard : eval (fuel + 11) DBot (OptimBot k S) (.sim .opp (.bot DefectBot)) = some .D :=
    eval_sim_opp_bot_of_play (fuel + 10) DBot (OptimBot k S) DefectBot Action.D hInner
  have hPlay := play_ite_from_guard
    fuel 11 DBot (OptimBot k S) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C) Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem no_provable_DBot_C_vs_optim (k S : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays DBot (OptimBot k S) .C) φ → False := by
  intro K φ hp hK ht
  refine no_provable_probeFirst_tail k DefectBot (.const .D) (.const .C) .C .C
      (.plays .opp .self .C)
      (.search S (.plays .self .opp Action.D) (.const Action.D)
        (.search k (.plays .opp .self Action.C)
          (.search S (.plays .self .opp Action.C) (.const Action.C)
            (.search k (.plays .opp .self Action.D)
              (.search S (.plays .self .opp Action.D) (.const Action.D) (.const Action.C))
              (.const Action.C)))
          (.search k (.plays .opp .self Action.D)
            (.search S (.plays .self .opp Action.D) (.const Action.D) (.const Action.C))
            (.const Action.C))))
      (.search k (.plays .opp .self Action.C)
        (.search S (.plays .self .opp Action.C) (.const Action.C)
          (.search k (.plays .opp .self Action.D)
            (.search S (.plays .self .opp Action.D) (.const Action.D) (.const Action.C))
            (.const Action.C)))
        (.search k (.plays .opp .self Action.D)
          (.search S (.plays .self .opp Action.D) (.const Action.D) (.const Action.C))
          (.const Action.C)))
      ?_ ?_ ?_ K φ hp hK ?_
  · simpa [Formula.subst, Prog.subst, OptimBot] using
      interp_bot_DefectBot_plays_C_false
        (.search k (.plays .opp .self Action.C) _ _)
  · intro k' ψ c0 c1 h; simp at h
  · exact fun L => const_ne_ctxPlug (by decide) L
  · simpa [DBot, OptimBot] using ht

theorem optim_ps_DBotC_false (k S : Nat) :
    proofSearch k (.plays DBot (OptimBot k S) Action.C) = false := by
  cases h : proofSearch k (.plays DBot (OptimBot k S) Action.C) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => no_provable_DBot_C_vs_optim k S k _ hp le_rfl (by simp))
  | false => rfl

theorem interp_DBot_plays_D_vs_optim_false (k S : Nat)
    (hselfD : proofSearch S (.plays (OptimBot k S) DefectBot.bot Action.D) = true)
    (hoppC : proofSearch k (.plays DefectBot.bot (OptimBot k S) Action.C) = false)
    (hoppD : proofSearch k (.plays DefectBot.bot (OptimBot k S) Action.D) = true) :
    ¬ (Formula.plays DBot (OptimBot k S) .D).interp := by
  rintro ⟨n, hn⟩
  have hC : play (n + 12) DBot (OptimBot k S) = some .C :=
    dbot_plays_C_vs_optim k S n hselfD hoppC hoppD
  have hmono : play (n + 12) DBot (OptimBot k S) = some .D := by
    unfold play at hn ⊢; exact eval_mono_le hn (n + 12) (by omega)
  rw [hC] at hmono; cases hmono

theorem optim_ps_DBotD_false (k S : Nat)
    (hselfD : proofSearch S (.plays (OptimBot k S) DefectBot.bot Action.D) = true)
    (hoppC : proofSearch k (.plays DefectBot.bot (OptimBot k S) Action.C) = false)
    (hoppD : proofSearch k (.plays DefectBot.bot (OptimBot k S) Action.D) = true) :
    proofSearch k (.plays DBot (OptimBot k S) Action.D) = false := by
  cases h : proofSearch k (.plays DBot (OptimBot k S) Action.D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_DBot_plays_D_vs_optim_false k S hselfD hoppC hoppD)
  | false => rfl

theorem optim_plays_C_vs_dbot (k S fuel : Nat)
    (hC : proofSearch k (.plays DBot (OptimBot k S) Action.C) = false)
    (hD : proofSearch k (.plays DBot (OptimBot k S) Action.D) = false) :
    play (fuel + 12) (OptimBot k S) DBot = some .C := by
  show eval (fuel + 12) (OptimBot k S) DBot (OptimBot k S) = some .C
  unfold OptimBot at hC hD ⊢
  simp [eval, Prog.subst, Formula.subst, hC, hD]

theorem llm_outcome_OptimBot_vs_DBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (OptimBot k (100000000 * k)) DBot = some (.C, .C) := by
  obtain ⟨k₂, hk₂⟩ := optim_dbot_selfD_provable
  refine ⟨max k₂ 2, fun k hk => ?_⟩
  have hkk₂ : k > k₂ := lt_of_le_of_lt (Nat.le_max_left _ _) hk
  have h2k : 2 ≤ k := le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk)
  set S := 100000000 * k with hS
  have hselfD : proofSearch S (.plays (OptimBot k S) DefectBot.bot Action.D) = true :=
    hk₂ k hkk₂
  have hoppC : proofSearch k (.plays DefectBot.bot (OptimBot k S) Action.C) = false :=
    optim_ps_oppC_false k S
  have hoppD : proofSearch k (.plays DefectBot.bot (OptimBot k S) Action.D) = true :=
    optim_ps_oppD_true k S h2k
  have hC : proofSearch k (.plays DBot (OptimBot k S) Action.C) = false :=
    optim_ps_DBotC_false k S
  have hD : proofSearch k (.plays DBot (OptimBot k S) Action.D) = false :=
    optim_ps_DBotD_false k S hselfD hoppC hoppD
  refine ⟨12, ?_⟩
  have hA : play 12 (OptimBot k S) DBot = some .C := by
    have := optim_plays_C_vs_dbot k S 0 hC hD
    simpa using this
  have hB : play 12 DBot (OptimBot k S) = some .C := by
    have := dbot_plays_C_vs_optim k S 0 hselfD hoppC hoppD
    simpa using this
  exact outcome_of_plays 12 _ _ _ _ hA hB

end PD.Theorems
