import PrisonersDilemma.Bots.LlmGenerations.OptimBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # OptimBot vs TitForTatBot → (D, D) at STAGGERED budgets (searchElseChain). -/

theorem ot_plug2_decomp (k K : Nat) :
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

private def ot_rung2 (k K : Nat) : Prog :=
  Prog.search k (Formula.plays Prog.opp Prog.self Action.C)
    (Prog.search K (Formula.plays Prog.self Prog.opp Action.C) (Prog.const Action.C)
      (Prog.search k (Formula.plays Prog.opp Prog.self Action.D)
        (Prog.search K (Formula.plays Prog.self Prog.opp Action.D) (Prog.const Action.D)
          (Prog.const Action.C))
        (Prog.const Action.C)))
    (Prog.search k (Formula.plays Prog.opp Prog.self Action.D)
      (Prog.search K (Formula.plays Prog.self Prog.opp Action.D) (Prog.const Action.D)
        (Prog.const Action.C))
      (Prog.const Action.C))

/-! ## Certificates -/

theorem ot_optim_D_cert_vs_botCB (k K : Nat)
    (hOuter : Pf k (.plays (.bot CooperateBot) (OptimBot k K) Action.C))
    (hInner : Pf K (.plays (OptimBot k K) (.bot CooperateBot) Action.D)) :
    ∃ n, PlaysProof (OptimBot k K) (.bot CooperateBot) (OptimBot k K) Action.D n
      ∧ n ≤ Nat.log2 k + Nat.log2 K + 10 := by
  refine ⟨_, PlaysProof.search_t ?_ (PlaysProof.search_t ?_ PlaysProof.const), ?_⟩
  · simpa [Formula.subst, Prog.subst, OptimBot] using hOuter
  · simpa [Formula.subst, Prog.subst, OptimBot] using hInner
  · simp only [c_leaf, c_guard, c_node, numCost]; omega

theorem ot_tft_D_cert_vs_Optim (k K : Nat)
    (hOuter : Pf k (.plays (.bot CooperateBot) (OptimBot k K) Action.C))
    (hInner : Pf K (.plays (OptimBot k K) (.bot CooperateBot) Action.D)) :
    ∃ n, PlaysProof TitForTatBot (OptimBot k K) TitForTatBot Action.D n
      ∧ n ≤ Nat.log2 k + Nat.log2 K + 20 := by
  obtain ⟨cn, cert, hcn⟩ := ot_optim_D_cert_vs_botCB k K hOuter hInner
  have hg : PlaysProof TitForTatBot (OptimBot k K)
      (.sim .opp (.bot CooperateBot)) Action.D (cn + c_node) := by
    refine PlaysProof.sim ?_
    simpa [Prog.subst] using cert
  refine ⟨_, PlaysProof.ite_f (a' := Action.C) hg (by decide) PlaysProof.const, ?_⟩
  simp only [c_leaf, c_node]; omega

theorem ot_botCB_C_Pf (k K : Nat) (hk : 2 ≤ k) :
    Pf k (.plays (.bot CooperateBot) (OptimBot k K) Action.C) := by
  have hcert : AtomProvable 2 (.plays (.bot CooperateBot) (OptimBot k K) Action.C) :=
    ⟨(PlaysProof.bot PlaysProof.const :
        PlaysProof (.bot CooperateBot) (OptimBot k K) (.bot CooperateBot) Action.C (c_leaf + c_node)),
     by simp [c_leaf, c_node]⟩
  exact Pf_mono (Pf.atom hcert) hk

/-! ## Inner Löb premise & bootstrap: OptimBot defects against .bot CooperateBot -/

theorem ot_inner_loeb (k K : Nat) (h2 : 2 ≤ k) :
    Pf (300 * (Nat.log2 k + Nat.log2 K) + 3000)
       (.impl (.box K (.plays (OptimBot k K) (.bot CooperateBot) Action.D))
              (.plays (OptimBot k K) (.bot CooperateBot) Action.D)) := by
  have hcert : AtomProvable 2 (.plays (.bot CooperateBot) (OptimBot k K) Action.C) :=
    ⟨(PlaysProof.bot PlaysProof.const :
        PlaysProof (.bot CooperateBot) (OptimBot k K) (.bot CooperateBot) Action.C (c_leaf + c_node)),
     by simp [c_leaf, c_node]⟩
  have hbox2 : Pf _ (.box 2 (.plays (.bot CooperateBot) (OptimBot k K) Action.C)) :=
    Pf.boxIntro 2 _ _ (Pf.atom hcert) (Nat.le_refl _)
  have hmono : Pf _ (.impl (.box 2 (.plays (.bot CooperateBot) (OptimBot k K) Action.C))
                           (.box k (.plays (.bot CooperateBot) (OptimBot k K) Action.C))) :=
    Pf.boxMono 2 k _ _ h2 (Nat.le_refl _)
  have hboxk : Pf _ (.box k (.plays (.bot CooperateBot) (OptimBot k K) Action.C)) :=
    Pf.mp _ _ _ _ hmono hbox2 (Nat.le_refl _)
  have hchain := Pf.searchChain k (Formula.plays .opp .self Action.C)
    (ot_rung2 k K)
    [(K, (Formula.plays Prog.self Prog.opp Action.D), ot_rung2 k K)]
    Action.D (OptimBot k K) (.bot CooperateBot) rfl (Nat.le_refl _)
  simp only [searchGuards, implChain, List.foldr, Formula.subst, Prog.subst] at hchain
  have hfinal := Pf.mp _ _ _ _ hchain hboxk (Nat.le_refl _)
  refine Pf_mono hfinal ?_
  have hlog2 : Nat.log2 2 = 1 := by decide
  have hlogk : Nat.log2 k ≤ k := log2_le_self _
  simp only [Formula.size, Prog.size, numCost, OptimBot, CooperateBot, hlog2]
  omega

theorem ot_inner_atom_size (k K : Nat) :
    (Formula.plays (OptimBot k K) (.bot CooperateBot) Action.D).size
      ≤ 20 * (Nat.log2 k + Nat.log2 K) + 200 := by
  simp only [Formula.size, Prog.size, numCost, OptimBot, CooperateBot]
  omega

theorem ot_inner_D_at_stagger :
    ∃ k₂, ∀ k, k > k₂ →
      Pf (65536 * k) (.plays (OptimBot k (65536 * k)) (.bot CooperateBot) Action.D) := by
  obtain ⟨Ka, hKa⟩ := linear_log2_add_le 40000000 8000000000
  refine ⟨max 2 Ka, fun k hk => ?_⟩
  have h2 : 2 ≤ k := (lt_of_le_of_lt (Nat.le_max_left _ _) hk).le
  have hKk : k ≥ Ka := (lt_of_le_of_lt (Nat.le_max_right _ _) hk).le
  set KS := 65536 * k with hKS
  have hlkS : Nat.log2 k ≤ Nat.log2 KS := log2_mono (by omega)
  have hbig : 40000000 * Nat.log2 KS + 8000000000 ≤ KS := hKa KS (by omega)
  have hs := ot_inner_atom_size k KS
  set φ := Formula.plays (OptimBot k KS) (.bot CooperateBot) Action.D with hφ
  set P := 300 * (Nat.log2 k + Nat.log2 KS) + 3000 with hP
  set W := P + φ.size + Nat.log2 KS + 8 with hW
  have hWk : 8192 * W ≤ KS := by rw [hW, hP]; omega
  have hlg : Nat.log2 (1024 * W) ≤ Nat.log2 KS := log2_mono (by omega)
  have hl₁ : Nat.log2 (32 * W) ≤ Nat.log2 KS := log2_mono (by omega)
  have hl₃ : Nat.log2 (2048 * W) ≤ Nat.log2 KS := log2_mono (by omega)
  have hl₅ : Nat.log2 (8192 * W) ≤ Nat.log2 KS := log2_mono (by omega)
  have hLoeb : Pf P (.impl (.box KS φ) φ) := ot_inner_loeb k KS h2
  have hpf : Pf (4096 * W) φ := by
    refine bloeb_engine φ P KS
      (1024 * W) (32 * W) (2048 * W) (2048 * W) (8192 * W)
      (16 * W) (16 * W) (64 * W) (32 * W) (128 * W) (32 * W) (16 * W)
      (256 * W) (512 * W) (16 * W) (640 * W) (704 * W) (768 * W) (2048 * W) (4096 * W)
      hLoeb ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · (try simp only [numCost, Formula.size]); omega
  exact Pf_mono hpf (by omega)

/-! ## Outer Löb premise (searchElseChain) & bootstrap: OptimBot defects against TFT -/

theorem ot_loeb_premise (k K : Nat) (h2 : 2 ≤ k)
    (hcnk : Nat.log2 k + Nat.log2 K + 20 ≤ k)
    (hInner : Pf K (.plays (OptimBot k K) (.bot CooperateBot) Action.D)) :
    Pf (2 * k + 1000 * (Nat.log2 k + Nat.log2 K) + 100000)
       (.impl (.box K (.plays (OptimBot k K) TitForTatBot Action.D))
              (.plays (OptimBot k K) TitForTatBot Action.D)) := by
  set O := OptimBot k K with hO
  have hOuterPf := ot_botCB_C_Pf k K h2
  have hlogO : Nat.log2 k ≤ k := log2_le_self _
  obtain ⟨cn, cert, hcn⟩ := ot_tft_D_cert_vs_Optim k K hOuterPf hInner
  have hlogcn : Nat.log2 cn ≤ cn := log2_le_self _
  have hcnk' : cn ≤ k := by omega
  have hneg : Pf (20 * (Nat.log2 k + Nat.log2 K) + 2000)
      (.neg (.plays TitForTatBot O Action.C)) := by
    refine Pf.atomNeg TitForTatBot O .D .C cn ⟨cert, le_rfl⟩ (by decide) ?_
    simp only [Formula.size, Prog.size, numCost, OptimBot, TitForTatBot, CooperateBot, hO]
    omega
  have hboxD : Pf (300 * (Nat.log2 k + Nat.log2 K) + 50000)
      (.box k (.plays TitForTatBot O Action.D)) := by
    have hb1 : Pf (100 * (Nat.log2 k + Nat.log2 K) + 20000)
        (.box cn (.plays TitForTatBot O Action.D)) := by
      refine Pf.boxIntro cn _ _ (Pf.atom ⟨cert, le_rfl⟩) ?_
      simp only [Formula.size, Prog.size, numCost, OptimBot, TitForTatBot, CooperateBot, hO]
      omega
    have hmono : Pf (100 * (Nat.log2 k + Nat.log2 K) + 20000)
        (.impl (.box cn (.plays TitForTatBot O Action.D))
               (.box k (.plays TitForTatBot O Action.D))) := by
      refine Pf.boxMono cn k _ _ hcnk' ?_
      simp only [Formula.size, Prog.size, numCost, OptimBot, TitForTatBot, CooperateBot, hO]
      omega
    refine Pf.mp _ _ _ _ hmono hb1 ?_
    simp only [Formula.size, Prog.size, numCost, OptimBot, TitForTatBot, CooperateBot, hO]
    omega
  have hchain := Pf.searchElseChain
    (.elseL k .opp .self Action.C _) _ Action.D O TitForTatBot
    (ot_plug2_decomp k K)
    (k := 2 * k + 100 * (Nat.log2 k + Nat.log2 K) + 4000)
    (by
      simp only [layersCost, layerCost, guards2, guard2, implChain, List.foldr,
        Formula.size, Prog.size, Formula.subst, Prog.subst, numCost, c_guard,
        c_node, OptimBot, TitForTatBot, CooperateBot, hO]
      omega)
  simp only [guards2, guard2, implChain, List.foldr, Formula.subst, Prog.subst]
    at hchain
  have h2m := Pf.mp _ _ _ _ hchain hneg (k :=
      2 * k + 200 * (Nat.log2 k + Nat.log2 K) + 10000) (by
    simp only [Formula.size, Prog.size, numCost, OptimBot, TitForTatBot, CooperateBot, hO]
    omega)
  have h3m := Pf.mp _ _ _ _ h2m hneg (k :=
      2 * k + 300 * (Nat.log2 k + Nat.log2 K) + 16000) (by
    simp only [Formula.size, Prog.size, numCost, OptimBot, TitForTatBot, CooperateBot, hO]
    omega)
  have h4m := Pf.mp _ _ _ _ h3m hboxD (k :=
      2 * k + 1000 * (Nat.log2 k + Nat.log2 K) + 100000) (by
    simp only [Formula.size, Prog.size, numCost, OptimBot, TitForTatBot, CooperateBot, hO]
    omega)
  exact h4m

theorem ot_D_atom_size (k K : Nat) :
    (Formula.plays (OptimBot k K) TitForTatBot Action.D).size
      ≤ 20 * (Nat.log2 k + Nat.log2 K) + 200 := by
  simp only [Formula.size, Prog.size, numCost, OptimBot, TitForTatBot, CooperateBot]
  omega

theorem ot_log_65536 (k : Nat) : Nat.log2 (65536 * k) ≤ Nat.log2 k + 16 := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp
  have h1 : k < 2 ^ (Nat.log2 k + 1) := by
    rw [Nat.log2_eq_log_two]; exact Nat.lt_pow_succ_log_self (by norm_num) k
  have h3 : 65536 * k < 2 ^ (Nat.log2 k + 17) := by
    have : (2:Nat) ^ (Nat.log2 k + 17) = 2 ^ (Nat.log2 k + 1) * 65536 := by
      rw [show Nat.log2 k + 17 = (Nat.log2 k + 1) + 16 from rfl, pow_add]; norm_num
    omega
  have := (Nat.log2_lt (by omega)).2 h3
  omega

/-- The staggered inner Löb premise, packaged with the log stagger bound. -/
theorem ot_inner_D_at_stagger_bundled :
    ∃ k₂, ∀ k, k > k₂ →
      2 ≤ k ∧ (Nat.log2 k + Nat.log2 (65536 * k) + 20 ≤ k) ∧
      Pf (65536 * k) (.plays (OptimBot k (65536 * k)) (.bot CooperateBot) Action.D) := by
  obtain ⟨k₁, hinner⟩ := ot_inner_D_at_stagger
  obtain ⟨Kb, hKb⟩ := linear_log2_add_le 3 100
  refine ⟨max (max 2 k₁) Kb, fun k hk => ?_⟩
  have h2 : 2 ≤ k := (lt_of_le_of_lt (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hk).le
  have hk1 : k > k₁ := lt_of_le_of_lt (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hk
  have hKbk : k ≥ Kb := (lt_of_le_of_lt (Nat.le_max_right _ _) hk).le
  refine ⟨h2, ?_, hinner k hk1⟩
  have hst := ot_log_65536 k
  have := hKb k hKbk
  omega

theorem ot_D_provable_at_stagger :
    ∃ k₂, ∀ k, k > k₂ →
      proofSearch (65536 * k)
        (.plays (OptimBot k (65536 * k)) TitForTatBot Action.D) = true := by
  obtain ⟨k₁, hb⟩ := ot_inner_D_at_stagger_bundled
  obtain ⟨Ka, hKa⟩ := linear_log2_add_le 40000000 8000000000
  refine ⟨max k₁ Ka, fun k hk => ?_⟩
  obtain ⟨h2, hcnk, hInner⟩ := hb k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hKk : k ≥ Ka := (lt_of_le_of_lt (Nat.le_max_right _ _) hk).le
  set KS := 65536 * k with hKS
  have hlk2 : Nat.log2 k ≤ Nat.log2 KS := log2_mono (by omega)
  have hLoeb := ot_loeb_premise k KS h2 hcnk hInner
  have hbig : 40000000 * Nat.log2 KS + 8000000000 ≤ KS := hKa KS (by omega)
  have hs := ot_D_atom_size k KS
  set φ := Formula.plays (OptimBot k KS) TitForTatBot Action.D with hφ
  set P := 2 * k + 1000 * (Nat.log2 k + Nat.log2 KS) + 100000 with hP
  set W := P + φ.size + Nat.log2 KS + 8 with hW
  have hWk : 8192 * W ≤ KS := by rw [hW, hP]; omega
  have hlg : Nat.log2 (1024 * W) ≤ Nat.log2 KS := log2_mono (by omega)
  have hl₁ : Nat.log2 (32 * W) ≤ Nat.log2 KS := log2_mono (by omega)
  have hl₃ : Nat.log2 (2048 * W) ≤ Nat.log2 KS := log2_mono (by omega)
  have hl₅ : Nat.log2 (8192 * W) ≤ Nat.log2 KS := log2_mono (by omega)
  have hpf : Pf (4096 * W) φ := by
    refine bloeb_engine φ P KS
      (1024 * W) (32 * W) (2048 * W) (2048 * W) (8192 * W)
      (16 * W) (16 * W) (64 * W) (32 * W) (128 * W) (32 * W) (16 * W)
      (256 * W) (512 * W) (16 * W) (640 * W) (704 * W) (768 * W) (2048 * W) (4096 * W)
      hLoeb ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · (try simp only [numCost, Formula.size]); omega
  have hpfk : Pf KS φ := Pf_mono hpf (by omega)
  exact (proofSearch_spec KS φ).2 hpfk

/-! ## Eval side -/

theorem ot_ps_botCB_C (k K : Nat) (hk : 2 ≤ k) :
    proofSearch k (.plays (.bot CooperateBot) (OptimBot k K) Action.C) = true := by
  have hcert : AtomProvable 2 (.plays (.bot CooperateBot) (OptimBot k K) Action.C) :=
    ⟨(PlaysProof.bot PlaysProof.const :
        PlaysProof (.bot CooperateBot) (OptimBot k K) (.bot CooperateBot) Action.C (c_leaf + c_node)),
     by simp [c_leaf, c_node]⟩
  exact (proofSearch_spec _ _).2 (Pf_mono (Pf.atom hcert) hk)

theorem ot_optim_plays_D_vs_botCB (k K fuel : Nat) (hk : 2 ≤ k)
    (hD : proofSearch K (.plays (OptimBot k K) (.bot CooperateBot) Action.D) = true) :
    play (fuel + 6) (OptimBot k K) (.bot CooperateBot) = some .D := by
  have hOuter := ot_ps_botCB_C k K hk
  show eval (fuel + 6) (OptimBot k K) (.bot CooperateBot) (OptimBot k K) = some .D
  unfold OptimBot at hOuter hD ⊢
  simp [eval, Prog.subst, Formula.subst, hOuter, hD]

theorem ot_tft_plays_D_vs_optim (k K fuel : Nat) (hk : 2 ≤ k)
    (hD : proofSearch K (.plays (OptimBot k K) (.bot CooperateBot) Action.D) = true) :
    play (fuel + 8) TitForTatBot (OptimBot k K) = some .D := by
  have hOptD : play (fuel + 6) (OptimBot k K) (.bot CooperateBot) = some .D :=
    ot_optim_plays_D_vs_botCB k K fuel hk hD
  have hGuard : eval (fuel + 7) TitForTatBot (OptimBot k K)
      (.sim .opp (.bot CooperateBot)) = some .D :=
    eval_sim_opp_bot_of_play (fuel + 6) TitForTatBot (OptimBot k K) CooperateBot Action.D hOptD
  have hPlay := eval_ite_from_guard
    (fuel + 7) TitForTatBot (OptimBot k K) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D) Action.C Action.D hGuard
  show eval (fuel + 8) TitForTatBot (OptimBot k K) TitForTatBot = some .D
  rw [show TitForTatBot = .ite (.sim .opp (.bot CooperateBot)) Action.C
        (.const Action.C) (.const Action.D) from rfl] at *
  rw [hPlay]; rfl

theorem ot_interp_tft_C_false (k K : Nat) (hk : 2 ≤ k)
    (hD : proofSearch K (.plays (OptimBot k K) (.bot CooperateBot) Action.D) = true) :
    ¬ (Formula.plays TitForTatBot (OptimBot k K) .C).interp := by
  rintro ⟨n, hn⟩
  have hDplay : play (n + 8) TitForTatBot (OptimBot k K) = some .D :=
    ot_tft_plays_D_vs_optim k K n hk hD
  have hCplay : play (n + 8) TitForTatBot (OptimBot k K) = some .C := by
    unfold play at hn ⊢; exact eval_mono_le hn (n + 8) (by omega)
  rw [hCplay] at hDplay; cases hDplay

theorem ot_ps_tft_C_false (k K : Nat) (hk : 2 ≤ k)
    (hD : proofSearch K (.plays (OptimBot k K) (.bot CooperateBot) Action.D) = true) :
    proofSearch k (.plays TitForTatBot (OptimBot k K) Action.C) = false := by
  cases h : proofSearch k (.plays TitForTatBot (OptimBot k K) Action.C) with
  | true => exact absurd (proofSearch_sound _ _ h) (ot_interp_tft_C_false k K hk hD)
  | false => rfl

theorem ot_ps_tft_D_true (k K : Nat) (hk : 2 ≤ k)
    (hcnk : Nat.log2 k + Nat.log2 K + 20 ≤ k)
    (hInnerPf : Pf K (.plays (OptimBot k K) (.bot CooperateBot) Action.D)) :
    proofSearch k (.plays TitForTatBot (OptimBot k K) Action.D) = true := by
  have hOuterPf := ot_botCB_C_Pf k K hk
  obtain ⟨n, cert, hn⟩ := ot_tft_D_cert_vs_Optim k K hOuterPf hInnerPf
  exact (proofSearch_spec _ _).2 (Pf.atom ⟨cert, by omega⟩)

/-- OptimBot plays D against TFT: rung1&2 fail, rung3 fires with staggered self-proof. -/
theorem ot_optim_plays_D_vs_tft (k K fuel : Nat) (hk : 2 ≤ k)
    (hcnk : Nat.log2 k + Nat.log2 K + 20 ≤ k)
    (hInnerPf : Pf K (.plays (OptimBot k K) (.bot CooperateBot) Action.D))
    (hInnerPS : proofSearch K (.plays (OptimBot k K) (.bot CooperateBot) Action.D) = true)
    (hDtft : proofSearch K (.plays (OptimBot k K) TitForTatBot Action.D) = true) :
    play (fuel + 6) (OptimBot k K) TitForTatBot = some .D := by
  have hG1 := ot_ps_tft_C_false k K hk hInnerPS
  have hG3 := ot_ps_tft_D_true k K hk hcnk hInnerPf
  show eval (fuel + 6) (OptimBot k K) TitForTatBot (OptimBot k K) = some .D
  unfold OptimBot at hG1 hG3 hDtft ⊢
  simp [eval, Prog.subst, Formula.subst, hG1, hG3, hDtft]

/-! ## Final outcome -/

theorem llm_outcome_OptimBot_vs_TitForTatBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (OptimBot k (65536 * k)) TitForTatBot = some (.D, .D) := by
  obtain ⟨k₁, hbundle⟩ := ot_inner_D_at_stagger_bundled
  obtain ⟨k₂, hDtft⟩ := ot_D_provable_at_stagger
  refine ⟨max k₁ k₂, fun k hk => ⟨8, ?_⟩⟩
  obtain ⟨h2, hcnk, hInnerPf⟩ := hbundle k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hDtftk := hDtft k (lt_of_le_of_lt (Nat.le_max_right _ _) hk)
  set KS := 65536 * k with hKS
  have hInnerPS : proofSearch KS (.plays (OptimBot k KS) (.bot CooperateBot) Action.D) = true :=
    (proofSearch_spec _ _).2 hInnerPf
  have hA : play 8 (OptimBot k KS) TitForTatBot = some .D := by
    simpa using ot_optim_plays_D_vs_tft k KS 2 h2 hcnk hInnerPf hInnerPS hDtftk
  have hB : play 8 TitForTatBot (OptimBot k KS) = some .D := by
    simpa using ot_tft_plays_D_vs_optim k KS 0 h2 hInnerPS
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
