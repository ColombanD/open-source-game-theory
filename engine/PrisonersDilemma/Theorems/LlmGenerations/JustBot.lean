import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.DupocBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot
import PrisonersDilemma.Theorems.LlmGenerations.PrudentBot
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems



/-- One evaluation step of JustBot: it consults its guard `proofSearch` and takes
    the corresponding constant branch (cooperate iff the guard fires). -/
theorem JustBot_eval_step (k fuel : Nat) (X : Prog) (a : Action)
    (hg : proofSearch k (Formula.plays X (.bot (DupocBot k)) Action.C)
            = (a == Action.C)) :
    play (fuel + 2) (JustBot k) X = some a := by
  -- The guard `proofSearch` argument is definitionally `.plays X (.bot (DupocBot k)) .C`.
  show (if proofSearch k (Formula.plays X (.bot (DupocBot k)) Action.C)
          then eval (fuel + 1) (JustBot k) X (.const Action.C)
          else eval (fuel + 1) (JustBot k) X (.const Action.D)) = some a
  rw [hg]
  cases a with
  | C => simp [eval]; rfl
  | D => simp [eval]; rfl

-- DefectBot --

/-- JustBot's substituted guard against DefectBot is false: DefectBot never plays C
    (against DupocBot or anything), so the guard search fails. -/
theorem proofSearch_false_for_JustBot_vs_DefectBot (k : Nat) :
    proofSearch k (Formula.plays DefectBot (.bot (DupocBot k)) Action.C) = false := by
  cases h : proofSearch k (Formula.plays DefectBot (.bot (DupocBot k)) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_DefectBot_plays_C_false _)
  | false => rfl

/-- JustBot defects against DefectBot: its guard fails. -/
theorem JustBot_plays_D_against_DefectBot (k fuel : Nat) :
    play (fuel + 2) (JustBot k) DefectBot = some .D := by
  refine JustBot_eval_step k fuel DefectBot .D ?_
  simpa using proofSearch_false_for_JustBot_vs_DefectBot k

/-- JustBot vs DefectBot: mutual defection. -/
theorem outcome_JustBot_vs_DefectBot (k fuel : Nat) :
    outcome (fuel + 2) (JustBot k) DefectBot = some (.D, .D) := by
  have hA : play (fuel + 2) (JustBot k) DefectBot = some .D :=
    JustBot_plays_D_against_DefectBot k fuel
  have hB : play (fuel + 2) DefectBot (JustBot k) = some .D := by
    simpa [Nat.add_comm] using play_DefectBot (fuel + 1) (JustBot k)
  exact outcome_of_plays _ _ _ _ _ hA hB

-- CooperateBot --

/-- JustBot's substituted guard against CooperateBot is true: CooperateBot
    cooperates against DupocBot (it cooperates against everything). -/
theorem proofSearch_true_for_JustBot_vs_CooperateBot :
    ∃ k, proofSearch k (Formula.plays CooperateBot (.bot (DupocBot k)) Action.C) = true := by
  exact ⟨atom_cost 1, (proofSearch_spec _ _).2 (Pf.atom ⟨PlaysProof.const, by decide⟩)⟩

/-- JustBot cooperates against CooperateBot: its guard succeeds. -/
theorem JustBot_plays_C_against_CooperateBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays CooperateBot (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 2) (JustBot k) CooperateBot = some .C := by
  refine JustBot_eval_step k fuel CooperateBot .C ?_
  simpa using hk

/-- JustBot vs CooperateBot: mutual cooperation. -/
theorem outcome_JustBot_vs_CooperateBot (fuel : Nat) :
    ∃ k, outcome (fuel + 2) (JustBot k) CooperateBot = some (.C, .C) := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_JustBot_vs_CooperateBot
  refine ⟨k, ?_⟩
  have hA : play (fuel + 2) (JustBot k) CooperateBot = some .C :=
    JustBot_plays_C_against_CooperateBot k fuel hk
  have hB : play (fuel + 2) CooperateBot (JustBot k) = some .C := by
    simpa [Nat.add_comm] using play_CooperateBot (fuel + 1) (JustBot k)
  exact outcome_of_plays _ _ _ _ _ hA hB

-- TitForTatBot --

/-- The shared guard: `(.bot CooperateBot)` cooperates against `(.bot (DupocBot k))`.
    Pf at budget `atom_cost 2` (a `.bot`-wrapped constant cooperates in two
    steps); we lift it to any `k ≥ atom_cost 2` via monotonicity. -/
theorem proofSearch_botCB_vs_botDupoc (k : Nat) (hk : k ≥ atom_cost 2) :
    proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true := by
  refine (proofSearch_spec _ _).2 (Pf.atom ⟨PlaysProof.bot PlaysProof.const, ?_⟩)
  have h7 : atom_cost 2 = 7 := by decide
  show c_leaf + c_node ≤ k
  simp only [c_leaf, c_node]
  omega

/-- DupocBot (`.bot`-wrapped) cooperates against `.bot CooperateBot`: once the
    shared guard fires, its `.search` takes the `.const .C` branch (after one extra
    fuel step to unwrap the `.bot`). -/
theorem botDupocBot_plays_C_against_bot_CooperateBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 3) (.bot (DupocBot k)) (.bot CooperateBot) = some .C := by
  show eval (fuel + 3) (.bot (DupocBot k)) (.bot CooperateBot) (.bot (DupocBot k)) = some .C
  rw [eval]   -- unwrap the `.bot` body, exposing DupocBot's `.search`
  show (if proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C)
          then eval (fuel + 1) (.bot (DupocBot k)) (.bot CooperateBot) (.const Action.C)
          else eval (fuel + 1) (.bot (DupocBot k)) (.bot CooperateBot) (.const Action.D)) = some .C
  rw [hk]; simp [eval]

/-- TitForTatBot cooperates against `.bot (DupocBot k)`: its probe sees DupocBot
    cooperate against `.bot CooperateBot`, so the `ite` selects the cooperate
    branch. -/
theorem TitForTatBot_plays_C_against_bot_DupocBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 5) TitForTatBot (.bot (DupocBot k)) = some .C := by
  have hDupoc : play (fuel + 3) (.bot (DupocBot k)) (.bot CooperateBot) = some .C :=
    botDupocBot_plays_C_against_bot_CooperateBot k fuel hk
  have hGuard :
      eval (fuel + 4) TitForTatBot (.bot (DupocBot k)) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) TitForTatBot (.bot (DupocBot k)) CooperateBot Action.C hDupoc)
  have hPlay := play_ite_from_guard
    fuel 4 TitForTatBot (.bot (DupocBot k)) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

/-- JustBot's guard against `.bot CooperateBot` is the *same* shared formula
    `.plays (.bot CooperateBot) (.bot (DupocBot k)) .C`, so JustBot cooperates
    against `.bot CooperateBot` whenever the shared guard fires. This is what makes
    TFT (which probes its opponent against `.bot CooperateBot`) cooperate with
    JustBot. -/
theorem JustBot_plays_C_against_bot_CooperateBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 2) (JustBot k) (.bot CooperateBot) = some .C := by
  refine JustBot_eval_step k fuel (.bot CooperateBot) .C ?_
  simpa using hk

/-- TitForTatBot cooperates against JustBot: its probe sees JustBot cooperate
    against `.bot CooperateBot` (same shared guard), so the `ite` cooperates. -/
theorem TitForTatBot_plays_C_against_JustBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 4) TitForTatBot (JustBot k) = some .C := by
  have hJust : play (fuel + 2) (JustBot k) (.bot CooperateBot) = some .C :=
    JustBot_plays_C_against_bot_CooperateBot k fuel hk
  have hGuard :
      eval (fuel + 3) TitForTatBot (JustBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (JustBot k) CooperateBot Action.C hJust)
  have hPlay := play_ite_from_guard
    fuel 3 TitForTatBot (JustBot k) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

/-- JustBot cooperates against TitForTatBot: its guard fires. -/
theorem JustBot_plays_C_against_TitForTatBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays TitForTatBot (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 2) (JustBot k) TitForTatBot = some .C := by
  refine JustBot_eval_step k fuel TitForTatBot .C ?_
  simpa using hk

/-- JustBot vs TitForTatBot: mutual cooperation. Both legs ride the shared guard at
    budget `atom_cost 5`. -/
theorem outcome_JustBot_vs_TitForTatBot :
    ∃ k, ∀ fuel, outcome (fuel + 5) (JustBot k) TitForTatBot = some (.C, .C) := by
  let k := atom_cost 5
  have hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true :=
    proofSearch_botCB_vs_botDupoc k (atom_cost_mono (by omega))
  have hGuardTFT : proofSearch k (Formula.plays TitForTatBot (.bot (DupocBot k)) Action.C) = true := by
    -- hand certificate: TFT's probe runs `.bot (DupocBot k)`'s FIRED search (hk), so
    -- ite_t ∘ sim ∘ bot ∘ search_t ∘ const; cost = log2 k + 7 ≤ k (k = atom_cost 5 = 21).
    refine (proofSearch_spec _ _).2 (Pf.atom
      (⟨PlaysProof.ite_t (PlaysProof.sim (PlaysProof.bot
          (PlaysProof.search_t ((proofSearch_spec _ _).1 hk) PlaysProof.const)))
        rfl PlaysProof.const, ?_⟩ :
        AtomProvable k (.plays TitForTatBot (.bot (DupocBot k)) .C)))
    show c_leaf + c_guard k + c_node + c_node + c_node + c_leaf + c_node ≤ k
    decide
  refine ⟨k, fun fuel => ?_⟩
  have hA : play (fuel + 5) (JustBot k) TitForTatBot = some .C := by
    simpa [Nat.add_assoc] using JustBot_plays_C_against_TitForTatBot k (fuel + 3) hGuardTFT
  have hB : play (fuel + 5) TitForTatBot (JustBot k) = some .C := by
    simpa [Nat.add_assoc] using TitForTatBot_plays_C_against_JustBot k (fuel + 1) hk
  exact outcome_of_plays _ _ _ _ _ hA hB


--- DBot ---

-- .bot DefectBot cannot play C against anything
theorem ps_false_bot_DefectBot_vs_bot_DupocBot_JB (k : Nat) :
    proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) = false := by
  cases h : proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) with
  | true =>
    exact absurd (proofSearch_sound _ _ h) (by
      rintro ⟨n, hn⟩
      rcases n with _ | _ | n
      · simp [play, eval] at hn
      · simp [play, eval] at hn
      · simp [play, eval, DefectBot] at hn)
  | false => rfl

-- .bot (DupocBot k) defects against .bot DefectBot: its guard fails (DefectBot plays D)
theorem bot_DupocBot_plays_D_against_bot_DefectBot_JB (k fuel : Nat) :
    play (fuel + 3) (.bot (DupocBot k)) (.bot DefectBot) = some .D := by
  have hg := ps_false_bot_DefectBot_vs_bot_DupocBot_JB k
  show eval (fuel + 3) (.bot (DupocBot k)) (.bot DefectBot) (.bot (DupocBot k)) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

-- DBot cooperates against .bot (DupocBot k): its sim probe sees D, so takes .const .C
theorem DBot_plays_C_against_bot_DupocBot_JB (k fuel : Nat) :
    play (fuel + 5) DBot (.bot (DupocBot k)) = some .C := by
  have hInner : play (fuel + 3) (.bot (DupocBot k)) (.bot DefectBot) = some .D :=
    bot_DupocBot_plays_D_against_bot_DefectBot_JB k fuel
  have hGuard : eval (fuel + 4) DBot (.bot (DupocBot k)) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 3) DBot (.bot (DupocBot k)) DefectBot .D hInner
  have hPlay := play_ite_from_guard
    fuel 4 DBot (.bot (DupocBot k)) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C) Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

-- JustBot k defects against .bot DefectBot: its guard (.plays .bot DefectBot ...) fails
theorem JustBot_plays_D_against_bot_DefectBot_JB (k fuel : Nat) :
    play (fuel + 2) (JustBot k) (.bot DefectBot) = some .D := by
  have hg := ps_false_bot_DefectBot_vs_bot_DupocBot_JB k
  show eval (fuel + 2) (JustBot k) (.bot DefectBot) (JustBot k) = some .D
  unfold JustBot
  simp [eval, Prog.subst, Formula.subst, hg]

-- DBot cooperates against JustBot k: sim probe sees JustBot defects → DBot cooperates
theorem DBot_plays_C_against_JustBot_JB (k fuel : Nat) :
    play (fuel + 4) DBot (JustBot k) = some .C := by
  have hInner : play (fuel + 2) (JustBot k) (.bot DefectBot) = some .D :=
    JustBot_plays_D_against_bot_DefectBot_JB k fuel
  have hGuard : eval (fuel + 3) DBot (JustBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 2) DBot (JustBot k) DefectBot .D hInner
  have hPlay := play_ite_from_guard
    fuel 3 DBot (JustBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C) Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

/-! ### JustBot vs DBot — the honest `(D, C)` outcome (floor formalized 2026-07-09).

HISTORY: `outcome_JustBot_vs_DBot` was RETIRED 2026-07-02 as an axiom artifact: DBot's
C-play against `.bot (DupocBot k)` (JustBot's frozen guard target) crosses Dupoc's
FAILED probe search (vs `.bot DefectBot`), so its certificate pays the `search_f`
floor — cost > k for every k — and JustBot's guard can never see "DBot plays C vs
`.bot DupocBot`" within the shared budget `k`.

RESOLVED (2026-07-09): the floor is a THEOREM — `no_provable_DBot_C_vs_botDupoc_tail`,
an instance of `no_provable_probeFirst_tail_botOpp` (Base/Exclusion.lean; the
`.bot`-wrapped-searcher variant, since JustBot's guard target is the FROZEN
`.bot (DupocBot k)`). JustBot's guard fails at every budget, so JustBot defects while
DBot — whose probe already watched JustBot defect vs `.bot DefectBot` — cooperates:
`outcome_JustBot_vs_DBot = (D, C)` at every budget. -/

/-- The floor for the DBot pair: no ≤ k certificate concludes any formula whose spine
    tail is "DBot plays C against `.bot (DupocBot k)`" (JustBot's guard instance). -/
theorem no_provable_DBot_C_vs_botDupoc_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      rightTail φ = .plays DBot (.bot (DupocBot k)) .C → False := by
  intro K φ hp hK ht
  refine no_provable_probeFirst_tail_botOpp k DefectBot (.const .D) (.const .C) .C .C
      (.plays .opp .self .C) (.const .C) (.const .D) ?_ ?_ K φ hp hK ?_
  · simpa [Formula.subst, Prog.subst, DupocBot] using
      interp_bot_DefectBot_plays_C_false (.bot (DupocBot k))
  · intro k' ψ c0 c1 h; simp at h
  · simpa [DBot, DupocBot] using ht

/-- JustBot's guard fails against DBot at every budget — the floor's bite. -/
theorem proofSearch_false_for_DBot_vs_botDupoc (k : Nat) :
    proofSearch k (.plays DBot (.bot (DupocBot k)) .C) = false := by
  cases h : proofSearch k (.plays DBot (.bot (DupocBot k)) .C) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => no_provable_DBot_C_vs_botDupoc_tail k k _ hp le_rfl (by simp))
  | false => rfl

/-- JustBot defects against DBot: it can never afford the certificate of DBot's
    (true!) cooperation with `.bot DupocBot`. -/
theorem JustBot_plays_D_against_DBot (k fuel : Nat) :
    play (fuel + 2) (JustBot k) DBot = some .D := by
  have hg := proofSearch_false_for_DBot_vs_botDupoc k
  show eval (fuel + 2) (JustBot k) DBot (JustBot k) = some .D
  unfold JustBot
  simp [eval, Prog.subst, Formula.subst, hg]

/-- **The honest JustBot×DBot outcome — `(D, C)` at every budget.** -/
theorem outcome_JustBot_vs_DBot (k fuel : Nat) :
    outcome (fuel + 4) (JustBot k) DBot = some (.D, .C) := by
  have hA : play (fuel + 4) (JustBot k) DBot = some .D := by
    simpa [Nat.add_assoc] using JustBot_plays_D_against_DBot k (fuel + 2)
  have hB : play (fuel + 4) DBot (JustBot k) = some .C :=
    DBot_plays_C_against_JustBot_JB k fuel
  simp [outcome, hA, hB]

/-! ### JustBot2 — the FREEZE TRICK: cooperation with DBot recovered (2026-07-09).

`outcome_JustBot_vs_DBot = (D, C)` above is an artifact of BUDGET-TYING, not of the
matchup: JustBot's guard fact "DBot plays C vs `.bot (DupocBot k)`" costs exactly
`k + log₂ k + 26` (the snapshot's `search_f` floor `k`, plus the `atomNeg` refutation
and the replay overhead) — one floor above JustBot's own budget `k`. `JustBot2 K k`
decouples the dials: at `K ≥ k + log₂ k + 26` the certificate fits, the guard fires,
and the FairBot×DBot handshake returns at staggered internal budgets. Constructive
companion to the floor impossibilities: the `(D, C)` outcomes are about budget-TIED
bots, not about the pairs. -/

/-- **The staggered certificate**: DBot's cooperation with the frozen snapshot IS
    affordable one floor up — the honest price of the fact JustBot's guard requests.
    Structure: replay DBot's `ite` (else-branch C), whose guard simulates the snapshot
    against `.bot DefectBot`; the snapshot's probe search fails, certified by
    `search_f` over the `atomNeg` refutation (DefectBot's actual D-play refutes the
    C-claim) — paying the floor `k`. Total: `k + log₂ k + 26`. -/
theorem provable_DBot_C_vs_botDupoc (k K : Nat) (hK : k + Nat.log2 k + 26 ≤ K) :
    Pf K (.plays DBot (.bot (DupocBot k)) .C) := by
  have hneg : Pf (Nat.log2 k + 20)
      (.neg (.plays (.bot DefectBot) (.bot (DupocBot k)) .C)) := by
    refine Pf.atomNeg (.bot DefectBot) (.bot (DupocBot k)) .D .C 2
      ⟨PlaysProof.bot PlaysProof.const, by decide⟩ (by decide) ?_
    simp only [Formula.size, Prog.size, DupocBot, DefectBot, numCost]
    omega
  refine Pf.atom
    ⟨PlaysProof.ite_f
      (PlaysProof.sim (PlaysProof.bot (PlaysProof.search_f hneg PlaysProof.const)))
      (by decide) PlaysProof.const, ?_⟩
  simp only [c_leaf, c_node]
  omega

/-- JustBot2's guard fires against DBot once `K` clears the staggered price. -/
theorem proofSearch_true_DBot_vs_botDupoc (k K : Nat)
    (hK : k + Nat.log2 k + 26 ≤ K) :
    proofSearch K (.plays DBot (.bot (DupocBot k)) .C) = true :=
  (proofSearch_spec _ _).2 (provable_DBot_C_vs_botDupoc k K hK)

/-- JustBot2 cooperates with DBot: the staggered budget affords the certificate the
    single-parameter JustBot could never see. -/
theorem JustBot2_plays_C_against_DBot (k K fuel : Nat)
    (hK : k + Nat.log2 k + 26 ≤ K) :
    play (fuel + 2) (JustBot2 K k) DBot = some .C := by
  have hg := proofSearch_true_DBot_vs_botDupoc k K hK
  show eval (fuel + 2) (JustBot2 K k) DBot (JustBot2 K k) = some .C
  unfold JustBot2
  simp [eval, Prog.subst, Formula.subst, hg]

/-- JustBot2's guard fails against `.bot DefectBot` at every budget (the formula is
    false — DefectBot never cooperates with the snapshot). -/
theorem ps_false_bot_DefectBot_vs_botDupoc_J2 (k K : Nat) :
    proofSearch K (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) = false := by
  cases h : proofSearch K (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) with
  | true => exact absurd (proofSearch_sound _ _ h) (interp_bot_DefectBot_plays_C_false _)
  | false => rfl

theorem JustBot2_plays_D_against_bot_DefectBot (k K fuel : Nat) :
    play (fuel + 2) (JustBot2 K k) (.bot DefectBot) = some .D := by
  have hg := ps_false_bot_DefectBot_vs_botDupoc_J2 k K
  show eval (fuel + 2) (JustBot2 K k) (.bot DefectBot) (JustBot2 K k) = some .D
  unfold JustBot2
  simp [eval, Prog.subst, Formula.subst, hg]

/-- DBot cooperates with JustBot2: its probe watches JustBot2 defect vs
    `.bot DefectBot`. -/
theorem DBot_plays_C_against_JustBot2 (k K fuel : Nat) :
    play (fuel + 4) DBot (JustBot2 K k) = some .C := by
  have hInner : play (fuel + 2) (JustBot2 K k) (.bot DefectBot) = some .D :=
    JustBot2_plays_D_against_bot_DefectBot k K fuel
  have hGuard : eval (fuel + 3) DBot (JustBot2 K k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 2) DBot (JustBot2 K k) DefectBot .D hInner
  have hPlay := play_ite_from_guard
    fuel 3 DBot (JustBot2 K k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C) Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

/-- **The recovered handshake — `(C, C)` at staggered internal budgets, every `k`.**
    The freeze trick in action: `JustBot2 (2k+64) k` affords the certificate of DBot's
    cooperation with its frozen snapshot (floor `k` < budget `2k+64`), while DBot's
    run-priced probe needs no proofs at all. Compare `outcome_JustBot_vs_DBot =
    (D, C)`: same matchup, budgets tied, guard starved by its own floor. -/
theorem outcome_JustBot2_vs_DBot (k fuel : Nat) :
    outcome (fuel + 4) (JustBot2 (2*k + 64) k) DBot = some (.C, .C) := by
  have hK : k + Nat.log2 k + 26 ≤ 2*k + 64 := by
    have := log2_le_self k
    omega
  have hA : play (fuel + 4) (JustBot2 (2*k + 64) k) DBot = some .C := by
    simpa [Nat.add_assoc] using JustBot2_plays_C_against_DBot k (2*k + 64) (fuel + 2) hK
  have hB : play (fuel + 4) DBot (JustBot2 (2*k + 64) k) = some .C :=
    DBot_plays_C_against_JustBot2 k (2*k + 64) fuel
  simp [outcome, hA, hB]

theorem outcome_JustBot_vs_OBot :
    ∃ k, ∀ n, outcome (n + 6) (JustBot k) OBot = some (.D, .D) := by
  let k := atom_cost 5
  refine ⟨k, fun n => ?_⟩

  have hPSCB : proofSearch k (.plays (.bot CooperateBot) (.bot (DupocBot k)) .C) = true := by
    have hPlay : play 2 (.bot CooperateBot) (.bot (DupocBot k)) = some .C :=
      play_bot_CooperateBot 0 (.bot (DupocBot k))
    exact (proofSearch_spec _ _).2 (Pf.atom ⟨PlaysProof.bot PlaysProof.const, by decide⟩)

  have hPSDB : proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) = false := by
    cases h : proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) with
    | true  => exact absurd (proofSearch_sound _ _ h) (interp_bot_DefectBot_plays_C_false _)
    | false => rfl

  have hPlay_botDupoc_botCB : ∀ N, play (N + 3) (.bot (DupocBot k)) (.bot CooperateBot) = some .C := by
    intro N
    show eval (N + 3) (.bot (DupocBot k)) (.bot CooperateBot) (.bot (DupocBot k)) = some .C
    show eval (N + 2) (.bot (DupocBot k)) (.bot CooperateBot) (DupocBot k) = some .C
    unfold DupocBot at hPSCB ⊢
    simp [eval, Prog.subst, Formula.subst, hPSCB]

  have hPlay_botDupoc_botDB : ∀ N, play (N + 3) (.bot (DupocBot k)) (.bot DefectBot) = some .D := by
    intro N
    show eval (N + 3) (.bot (DupocBot k)) (.bot DefectBot) (.bot (DupocBot k)) = some .D
    show eval (N + 2) (.bot (DupocBot k)) (.bot DefectBot) (DupocBot k) = some .D
    unfold DupocBot at hPSDB ⊢
    simp [eval, Prog.subst, Formula.subst, hPSDB]

  have hObotD : ∀ N, play (N + 6) OBot (.bot (DupocBot k)) = some .D := by
    intro N
    have hOuter : eval (N + 5) OBot (.bot (DupocBot k)) (.sim .opp (.bot CooperateBot)) = some .C :=
      eval_sim_opp_bot_of_play (N + 4) OBot (.bot (DupocBot k)) CooperateBot .C
        (by simpa [Nat.add_assoc] using hPlay_botDupoc_botCB (N + 1))
    have hInner : eval (N + 4) OBot (.bot (DupocBot k)) (.sim .opp (.bot DefectBot)) = some .D :=
      eval_sim_opp_bot_of_play (N + 3) OBot (.bot (DupocBot k)) DefectBot .D
        (hPlay_botDupoc_botDB N)
    have hPlay := play_ite_from_guard
      N 5 OBot (.bot (DupocBot k)) (.sim .opp (.bot CooperateBot))
      (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
      (.const Action.D)
      Action.C Action.C
      (by rfl) hOuter
    have hInnerIte :
        eval (N + 5) OBot (.bot (DupocBot k))
          (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D)) =
            some .D := by
      simpa [Nat.add_assoc] using
        (eval_ite_from_guard (N + 4) OBot (.bot (DupocBot k))
          (.sim .opp (.bot DefectBot)) (.const Action.C) (.const Action.D)
          Action.C Action.D hInner)
    simpa [Nat.add_assoc, hInnerIte] using hPlay

  have hPSObot : proofSearch k (.plays OBot (.bot (DupocBot k)) .C) = false := by
    cases h : proofSearch k (.plays OBot (.bot (DupocBot k)) .C) with
    | true =>
        exfalso
        obtain ⟨N, hC⟩ := proofSearch_sound _ _ h
        have hD : play 6 OBot (.bot (DupocBot k)) = some .D := hObotD 0
        have hC' : play (max N 6) OBot (.bot (DupocBot k)) = some .C := by
          unfold play
          exact eval_mono_le hC (max N 6) (Nat.le_max_left _ _)
        have hD' : play (max N 6) OBot (.bot (DupocBot k)) = some .D := by
          unfold play
          exact eval_mono_le hD (max N 6) (Nat.le_max_right _ _)
        rw [hC'] at hD'
        cases hD'
    | false => rfl

  have hA : play (n + 6) (JustBot k) OBot = some .D := by
    show eval (n + 6) (JustBot k) OBot (JustBot k) = some .D
    unfold JustBot
    simp [eval, Prog.subst, Formula.subst, hPSObot]

  have hJustC_botCB : ∀ N, play (N + 2) (JustBot k) (.bot CooperateBot) = some .C := by
    intro N
    show eval (N + 2) (JustBot k) (.bot CooperateBot) (JustBot k) = some .C
    unfold JustBot
    simp [eval, Prog.subst, Formula.subst, hPSCB]

  have hJustD_botDB : ∀ N, play (N + 2) (JustBot k) (.bot DefectBot) = some .D := by
    intro N
    show eval (N + 2) (JustBot k) (.bot DefectBot) (JustBot k) = some .D
    unfold JustBot
    simp [eval, Prog.subst, Formula.subst, hPSDB]

  have hB : play (n + 6) OBot (JustBot k) = some .D := by
    have hOuter : eval (n + 5) OBot (JustBot k) (.sim .opp (.bot CooperateBot)) = some .C :=
      eval_sim_opp_bot_of_play (n + 4) OBot (JustBot k) CooperateBot .C
        (by simpa [Nat.add_assoc] using hJustC_botCB (n + 2))
    have hInner : eval (n + 4) OBot (JustBot k) (.sim .opp (.bot DefectBot)) = some .D :=
      eval_sim_opp_bot_of_play (n + 3) OBot (JustBot k) DefectBot .D
        (by simpa [Nat.add_assoc] using hJustD_botDB (n + 1))
    have hPlay := play_ite_from_guard
      n 5 OBot (JustBot k) (.sim .opp (.bot CooperateBot))
      (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
      (.const Action.D)
      Action.C Action.C
      (by rfl) hOuter
    have hInnerIte :
        eval (n + 5) OBot (JustBot k)
          (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D)) =
            some .D := by
      simpa [Nat.add_assoc] using
        (eval_ite_from_guard (n + 4) OBot (JustBot k)
          (.sim .opp (.bot DefectBot)) (.const Action.C) (.const Action.D)
          Action.C Action.D hInner)
    simpa [Nat.add_assoc, hInnerIte] using hPlay

  exact outcome_of_plays _ _ _ _ _ hA hB


-- CupodTrollBot --

/-! ### JustBot × CupodTrollBot — RETIRED (2026-07-02, the false-guard repair).

CupodTrollBot's cooperation against `.bot (DupocBot k)` is an ELSE-play of its own `.eq`
search (the opponent is not literally `CupodBot k`), so its certificate pays the `search_f`
floor — JustBot's guard at the same `k` can never afford it. Staggered-budget restatement
(Troll at `j`, JustBot at `k ≥ j + O(log)`) is T3.2b; cf. the staggered
`outcome_CupodTrollBot_vs_DupocBot` in `Theorems/CupodTrollBot.lean`. -/

/-! ### JustBot × CupodTrollBot — RECOVERED with STAGGERED budgets (T3.2b, 2026-07-03).

`JustBot (4j+100)` vs `CupodTrollBot j`: JustBot's bigger budget affords Troll's
`search_f`-floored else-certificate (Troll cooperates because its `.eq` recognition guard
FAILS against `.bot (DupocBot (4j+100))`, refuted by `Derivation.eqNeg`). Holds for EVERY
`j` — no eventuality. -/

theorem outcome_JustBot_vs_CupodTrollBot (j fuel : Nat) :
    outcome (fuel + 2) (JustBot (4*j+100)) (CupodTrollBot j) = some (.C, .C) := by
  have hlj := log2_le_self j
  have hlgj := log2_stagger4_le j
  have hne : Prog.bot (DupocBot (4*j+100)) ≠ CupodBot j := by simp [CupodBot]
  -- the eqNeg refutation of Troll's recognition guard, at its own size
  have hneg : Pf ((Formula.neg (.eq (.bot (DupocBot (4*j+100))) (CupodBot j))).size)
      (.neg (.eq (.bot (DupocBot (4*j+100))) (CupodBot j))) :=
    Pf.eqNeg _ _ hne (Nat.le_refl _)
  -- Troll's floored else-certificate, affordable in JustBot's 4j+100 budget
  have hguard : proofSearch (4*j+100)
      (.plays (CupodTrollBot j) (.bot (DupocBot (4*j+100))) .C) = true := by
    refine (proofSearch_spec _ _).2 (Pf.atom (atom_monotone _ (4*j+100) _ ?_
      (⟨PlaysProof.search_f hneg PlaysProof.const, Nat.le_refl _⟩ :
        AtomProvable
          (c_leaf + (Formula.neg (.eq (.bot (DupocBot (4*j+100))) (CupodBot j))).size
            + j + c_node)
          (.plays (CupodTrollBot j) (.bot (DupocBot (4*j+100))) .C))))
    simp only [numCost, c_leaf, c_node, Formula.size, Prog.size, DupocBot, CupodBot]
    omega
  have hA : play (fuel + 2) (JustBot (4*j+100)) (CupodTrollBot j) = some .C := by
    refine JustBot_eval_step (4*j+100) fuel (CupodTrollBot j) .C ?_
    simpa using hguard
  have hB : play (fuel + 2) (CupodTrollBot j) (JustBot (4*j+100)) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot j fuel (JustBot (4*j+100))
      (by simp [JustBot, CupodBot])
  exact outcome_of_plays _ _ _ _ _ hA hB

/-! ### JustBot vs EBot — the honest `(D, C)` outcome (floor formalized 2026-07-09).

HISTORY: `outcome_JustBot_vs_EBot` was RETIRED 2026-07-02 as an axiom artifact: EBot's
C-play against `.bot (DupocBot k)` crosses Dupoc's FAILED outer-probe search (vs
`.bot DefectBot`) — the `search_f` floor, unaffordable within the shared budget.

RESOLVED (2026-07-09): `no_provable_EBot_C_vs_botDupoc_tail` (the `.bot`-wrapped
variant, as for DBot above). JustBot defects at every budget; EBot's probes watch
JustBot defect vs `.bot DefectBot` and cooperate vs `.bot CooperateBot` (both
run-priced), so EBot cooperates: `outcome_JustBot_vs_EBot = (D, C)` for every
`k ≥ 2` (the Σ₁ price of the `.bot CooperateBot` probe certificate). -/

/-- The floor for the EBot pair: no ≤ k certificate concludes any formula whose spine
    tail is "EBot plays C against `.bot (DupocBot k)`" (JustBot's guard instance). -/
theorem no_provable_EBot_C_vs_botDupoc_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      rightTail φ = .plays EBot (.bot (DupocBot k)) .C → False := by
  intro K φ hp hK ht
  refine no_provable_probeFirst_tail_botOpp k DefectBot (.const .D)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))
      .C .C (.plays .opp .self .C) (.const .C) (.const .D) ?_ ?_ K φ hp hK ?_
  · simpa [Formula.subst, Prog.subst, DupocBot] using
      interp_bot_DefectBot_plays_C_false (.bot (DupocBot k))
  · intro k' ψ c0 c1 h; simp at h
  · simpa [EBot, DupocBot] using ht

/-- JustBot's guard fails against EBot at every budget — the floor's bite. -/
theorem proofSearch_false_for_EBot_vs_botDupoc (k : Nat) :
    proofSearch k (.plays EBot (.bot (DupocBot k)) .C) = false := by
  cases h : proofSearch k (.plays EBot (.bot (DupocBot k)) .C) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => no_provable_EBot_C_vs_botDupoc_tail k k _ hp le_rfl (by simp))
  | false => rfl

/-- JustBot defects against EBot: it can never afford the certificate of EBot's
    (true!) cooperation with `.bot DupocBot`. -/
theorem JustBot_plays_D_against_EBot (k fuel : Nat) :
    play (fuel + 2) (JustBot k) EBot = some .D := by
  have hg := proofSearch_false_for_EBot_vs_botDupoc k
  show eval (fuel + 2) (JustBot k) EBot (JustBot k) = some .D
  unfold JustBot
  simp [eval, Prog.subst, Formula.subst, hg]

/-- The `.bot CooperateBot` probe guard vs `.bot DupocBot` is Σ₁-certifiable at run
    price, feeding `JustBot_plays_C_against_bot_CooperateBot` at every `k ≥ 2`. -/
theorem proofSearch_true_bot_CooperateBot_vs_botDupoc (k : Nat) (hk : 2 ≤ k) :
    proofSearch k (.plays (.bot CooperateBot) (.bot (DupocBot k)) .C) = true :=
  (proofSearch_spec _ _).2 (Pf.atom
    ⟨PlaysProof.bot PlaysProof.const, by simp only [c_leaf, c_node]; omega⟩)

/-- EBot cooperates with JustBot: probe 1 watches JustBot defect vs `.bot DefectBot`
    (descend), probe 2 watches it cooperate vs `.bot CooperateBot` (the shared guard
    fires Σ₁-cheaply) — EBot takes the cooperate branch. Pure simulation, no floor. -/
theorem EBot_plays_C_against_JustBot (k fuel : Nat) (hk : 2 ≤ k) :
    play (fuel + 5) EBot (JustBot k) = some .C := by
  have hP1 : play (fuel + 3) (JustBot k) (.bot DefectBot) = some .D := by
    simpa [Nat.add_assoc] using JustBot_plays_D_against_bot_DefectBot_JB k (fuel + 1)
  have hG1 : eval (fuel + 4) EBot (JustBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 3) EBot (JustBot k) DefectBot .D hP1
  have hP2 : play (fuel + 2) (JustBot k) (.bot CooperateBot) = some .C :=
    JustBot_plays_C_against_bot_CooperateBot k fuel
      (proofSearch_true_bot_CooperateBot_vs_botDupoc k hk)
  have hG2 : eval (fuel + 3) EBot (JustBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 2) EBot (JustBot k) CooperateBot .C hP2
  have hInner : eval (fuel + 4) EBot (JustBot k)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))) = some .C := by
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hG2]; rfl
  show eval (fuel + 5) EBot (JustBot k)
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .D)
        (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
          (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))) = some .C
  rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hG1]
  exact hInner

/-- **The honest JustBot×EBot outcome — `(D, C)` for every `k ≥ 2`.** -/
theorem outcome_JustBot_vs_EBot (k fuel : Nat) (hk : 2 ≤ k) :
    outcome (fuel + 5) (JustBot k) EBot = some (.D, .C) := by
  have hA : play (fuel + 5) (JustBot k) EBot = some .D := by
    simpa [Nat.add_assoc] using JustBot_plays_D_against_EBot k (fuel + 3)
  have hB := EBot_plays_C_against_JustBot k fuel hk
  simp [outcome, hA, hB]


-- JustBot --

/-- Inversion: a `.bot DupocBot` self-play cooperation forces its guard to fire. -/
theorem ps_k_of_play_botDupoc_self (k N : Nat)
    (h : play N (.bot (DupocBot k)) (.bot (DupocBot k)) = some .C) :
    proofSearch k (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C) = true := by
  cases hps : proofSearch k (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C) with
  | true => rfl
  | false =>
    exfalso
    have hD : play (N + 3) (.bot (DupocBot k)) (.bot (DupocBot k)) = some .D := by
      show eval (N + 3) (.bot (DupocBot k)) (.bot (DupocBot k)) (.bot (DupocBot k)) = some .D
      unfold DupocBot at hps ⊢
      simp [eval, Prog.subst, Formula.subst, hps]
    have hC : play (N + 3) (.bot (DupocBot k)) (.bot (DupocBot k)) = some .C := by
      unfold play at h ⊢
      exact eval_mono_le h (N + 3) (by omega)
    rw [hC] at hD
    cases hD

/-- Löb premise for `.bot DupocBot` self-play, via `botSearchStep`. -/
theorem botdupoc_loeb_premise (k : Nat) :
    Pf (20 * Nat.log2 k + 150)
      (.impl (.box k (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C))
             (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C)) := by
  -- transcript-tight: a single `botSearchStep` leaf, O(log k) — unconditionally.
  refine Pf.botSearchStep k (.plays .opp .self .C) .C .D (.bot (DupocBot k)) (.bot (DupocBot k)) rfl ?_
  simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot]
  omega

/-- For large `k`, `.bot DupocBot` self-play cooperates (its guard provably fires). -/
theorem botDupoc_self_coop :
    ∃ k₂, ∀ k, k₂ < k →
      proofSearch k (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C) = true := by
  let φ : Nat → Formula := fun k => .plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C
  have hLoeb : ∀ k, k > 0 →
      Pf (20 * Nat.log2 k + 150) (.impl (.box k (φ k)) (φ k)) := by
    intro k _
    exact botdupoc_loeb_premise k
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C).size ≤ _
    simp only [numCost, Formula.size, Prog.size, DupocBot]
    omega
  have hpm : ∀ k, 20 * Nat.log2 k + 150 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 20 * Nat.log2 k + 150) 0 hφsz hpm hLoeb
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := Pf_sound m (φ k) hm
  obtain ⟨n, hn⟩ := hInterp
  exact ps_k_of_play_botDupoc_self k n hn

/-- JustBot vs JustBot: mutual cooperation for sufficiently large `k`. -/
theorem outcome_JustBot_vs_JustBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (JustBot k) (JustBot k) = some (.C, .C) := by
  obtain ⟨k₂, hk₂⟩ := botDupoc_self_coop
  obtain ⟨KL, hKL⟩ := linear_log2_add_le 1 3
  refine ⟨max k₂ KL, fun k hk => ?_⟩
  have hk2 : k₂ < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hKLk : Nat.log2 k + 3 ≤ k := by
    have := hKL k (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk))
    omega
  have hdd : proofSearch k (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C) = true := hk₂ k hk2
  have hd' : proofSearch k (.plays (JustBot k) (.bot (DupocBot k)) .C) = true := by
    -- hand certificate: JustBot's own search FIRED (hdd) — search_t ∘ const, log2 k + 3 chars
    refine (proofSearch_spec _ _).2 (Pf.atom
      (⟨PlaysProof.search_t ((proofSearch_spec _ _).1 hdd) PlaysProof.const, ?_⟩ :
        AtomProvable k (.plays (JustBot k) (.bot (DupocBot k)) .C)))
    show c_leaf + c_guard k + c_node ≤ k
    simp only [numCost, c_leaf, c_guard, c_node]
    omega
  have hJJ : ∀ f, play (f + 2) (JustBot k) (JustBot k) = some .C := by
    intro f
    refine JustBot_eval_step k f (JustBot k) .C ?_
    simpa using hd'
  exact ⟨2, outcome_of_plays _ _ _ _ _ (by simpa using hJJ 0) (by simpa using hJJ 0)⟩


-- PrudentBot --

/-- When `.bot (DupocBot k)`'s guard fails, it defects against PrudentBot. -/
theorem bot_dupoc_D_vs_prudent (k fuel : Nat)
    (hk : proofSearch k (.plays (PrudentBot k) (.bot (DupocBot k)) .C) = false) :
    play (fuel + 3) (.bot (DupocBot k)) (PrudentBot k) = some .D := by
  show eval (fuel + 3) (.bot (DupocBot k)) (PrudentBot k) (.bot (DupocBot k)) = some .D
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- Inversion: a cooperating play on `.bot (DupocBot k)`'s leg forces its guard
    (PrudentBot plays C vs `.bot DupocBot`) to have fired. -/
theorem ps_k_of_play_botdupoc (k n : Nat)
    (h : play n (.bot (DupocBot k)) (PrudentBot k) = some .C) :
    proofSearch k (.plays (PrudentBot k) (.bot (DupocBot k)) .C) = true := by
  cases hps : proofSearch k (.plays (PrudentBot k) (.bot (DupocBot k)) .C) with
  | true => rfl
  | false =>
    exfalso
    have hD : play (n + 3) (.bot (DupocBot k)) (PrudentBot k) = some .D :=
      bot_dupoc_D_vs_prudent k n hps
    have hC : play (n + 3) (.bot (DupocBot k)) (PrudentBot k) = some .C := by
      unfold play at h ⊢; exact eval_mono_le h (n + 3) (by omega)
    rw [hC] at hD; cases hD

/-! ### JustBot × PrudentBot — RETIRED at same-`k` (2026-07-02, the false-guard repair).

The former `prudent_botdupoc_legPD`/`legDP`/`prudent_botdupoc_coop`/
`outcome_JustBot_vs_PrudentBot` were axiom artifacts: PrudentBot's prudence fact
"`.bot (DupocBot k)` defects vs `.bot DefectBot`" is an ELSE-play of Dupoc's own search
(floor `k`), unaffordable inside PrudentBot's same-`k` inner search; and JustBot's own
defection vs `.bot DefectBot` (consumed as PrudentBot's prudence about JustBot) is
JustBot's OWN else-play — same floor. Staggered budgets (PrudentBot at `j ≥ k + O(log k)`,
via the two-budget mutual wrapper) are T3.2b; cf. the PrudentBot×DupocBot tombstone in
`Theorems/LlmGenerations/PrudentBot.lean`. -/


/-! ### JustBot × PrudentBot — RECOVERED with STAGGERED budgets (T3.2b, 2026-07-03).

`JustBot k` vs `PrudentBot (2k+64)`: PrudentBot's inner search affords `.bot (DupocBot k)`'s
`search_f`-floored prudence certificate, and PrudentBot's outer guard affords JustBot's own
floored defection-vs-DefectBot certificate; the mutual Löb chain runs through
`mutual_pblt_engine_staggered` on the (botDupoc, PrudentBot) leg pair. -/

/-- `.bot (DupocBot k)`'s else-play vs `.bot DefectBot`, certified at the FLOOR. -/
theorem prudence_botdupoc (k : Nat) :
    Pf (k + Nat.log2 k + 17) (.plays (.bot (DupocBot k)) (.bot DefectBot) .D) := by
  have hneg : Pf (Nat.log2 k + 14)
      (.neg (.plays (.bot DefectBot) (.bot (DupocBot k)) .C)) := by
    refine Pf.atomNeg (.bot DefectBot) (.bot (DupocBot k)) .D .C 2
      ⟨PlaysProof.bot PlaysProof.const, by decide⟩ (by decide) ?_
    simp only [numCost, Formula.size, Prog.size, DefectBot, DupocBot]
    omega
  have hcert := atom_search_f_bot_top k (Nat.log2 k + 14) (.plays .opp .self .C) .C .D
    (.bot DefectBot) hneg
  exact Pf.atom (atom_monotone _ _ _ (by omega) hcert)

/-- JustBot's else-play vs `.bot DefectBot`, certified at the FLOOR (consumed as
    PrudentBot's prudence fact about JustBot). -/
theorem justbot_prudence (k : Nat) :
    Pf (k + Nat.log2 k + 16) (.plays (JustBot k) (.bot DefectBot) .D) := by
  have hneg : Pf (Nat.log2 k + 14)
      (.neg (.plays (.bot DefectBot) (.bot (DupocBot k)) .C)) := by
    refine Pf.atomNeg (.bot DefectBot) (.bot (DupocBot k)) .D .C 2
      ⟨PlaysProof.bot PlaysProof.const, by decide⟩ (by decide) ?_
    simp only [numCost, Formula.size, Prog.size, DefectBot, DupocBot]
    omega
  have hcert := atom_search_f_top k (Nat.log2 k + 14)
    (.plays .opp (.bot (DupocBot k)) .C) .C .D (.bot DefectBot) hneg
  exact Pf.atom (atom_monotone _ _ _ (by omega) hcert)

/-- Leg 1 (staggered): `□_{2k+64} φD' → φP'` — `PrudentBot (2k+64)` reads its stacked
    searches against `.bot (DupocBot k)`; the inner prudence is `prudence_botdupoc`. -/
theorem prudent_botdupoc_legPD (k : Nat) :
    Pf (30 * Nat.log2 k + 700)
      (.impl (.box (2*k+64) (.plays (.bot (DupocBot k)) (PrudentBot (2*k+64)) .C))
             (.plays (PrudentBot (2*k+64)) (.bot (DupocBot k)) .C)) := by
  have hlk := log2_le_self k
  have hlg := log2_stagger_le k
  refine Pf.searchThenSearch_t (2*k+64) (2*k+64) (k + Nat.log2 k + 17)
    (.plays .opp .self .C) (.plays .opp (.bot DefectBot) .D)
    .C .D (.const .D) (PrudentBot (2*k+64)) (.bot (DupocBot k)) rfl
    (by simpa [Formula.subst, Prog.subst] using prudence_botdupoc k) (by omega) ?_
  simp only [numCost, Formula.subst, Prog.subst, Formula.size, Prog.size, DupocBot, PrudentBot,
    DefectBot, c_guard]
  omega

/-- Leg 2 (staggered): `□_k φP' → φD'` — `.bot (DupocBot k)`'s `botSearchStep` leaf. -/
theorem prudent_botdupoc_legDP (k : Nat) :
    Pf (30 * Nat.log2 k + 700)
      (.impl (.box k (.plays (PrudentBot (2*k+64)) (.bot (DupocBot k)) .C))
             (.plays (.bot (DupocBot k)) (PrudentBot (2*k+64)) .C)) := by
  have hlg := log2_stagger_le k
  refine Pf.botSearchStep k (.plays .opp .self .C) .C .D (.bot (DupocBot k)) (PrudentBot (2*k+64)) rfl ?_
  simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot, PrudentBot, DefectBot]
  omega

/-- `.bot (DupocBot k)`'s staggered-opponent play lemmas (generic in the opponent). -/
theorem bot_dupoc_D_vs_any (k fuel : Nat) (q : Prog)
    (hk : proofSearch k (.plays q (.bot (DupocBot k)) .C) = false) :
    play (fuel + 3) (.bot (DupocBot k)) q = some .D := by
  show eval (fuel + 3) (.bot (DupocBot k)) q (.bot (DupocBot k)) = some .D
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

theorem ps_k_of_play_botdupoc_any (k n : Nat) (q : Prog)
    (h : play n (.bot (DupocBot k)) q = some .C) :
    proofSearch k (.plays q (.bot (DupocBot k)) .C) = true := by
  cases hps : proofSearch k (.plays q (.bot (DupocBot k)) .C) with
  | true => rfl
  | false =>
    exfalso
    have hD : play (n + 3) (.bot (DupocBot k)) q = some .D := bot_dupoc_D_vs_any k n q hps
    have hC : play (n + 3) (.bot (DupocBot k)) q = some .C := by
      unfold play at h ⊢; exact eval_mono_le h (n + 3) (by omega)
    rw [hC] at hD; cases hD

/-- **JustBot k vs PrudentBot (2k+64) → (C, C)** for all large enough `k` — the
    staggered-budget recovery of the retired same-`k` theorem. -/
theorem outcome_JustBot_vs_PrudentBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (JustBot k) (PrudentBot (2*k+64)) = some (.C, .C) := by
  obtain ⟨KL, hKL⟩ := linear_log2_add_le 1 3
  have hsD : ∀ k, (Formula.plays (.bot (DupocBot k)) (PrudentBot (2*k+64)) .C).size
      ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    have hlg := log2_stagger_le k
    simp only [numCost, Formula.size, Prog.size, PrudentBot, DupocBot, DefectBot]
    omega
  have hsP : ∀ k, (Formula.plays (PrudentBot (2*k+64)) (.bot (DupocBot k)) .C).size
      ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    have hlg := log2_stagger_le k
    simp only [numCost, Formula.size, Prog.size, PrudentBot, DupocBot, DefectBot]
    omega
  have hpb : ∀ k, 30 * Nat.log2 k + 700 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := mutual_pblt_engine_staggered
    (fun k => Formula.plays (.bot (DupocBot k)) (PrudentBot (2*k+64)) .C)
    (fun k => Formula.plays (PrudentBot (2*k+64)) (.bot (DupocBot k)) .C)
    (fun k => 2*k+64)
    (fun k => 30 * Nat.log2 k + 700) (fun k => 30 * Nat.log2 k + 700) 0
    (fun k => by show k ≤ 2*k+64; omega) log2_stagger_le hsD hsP hpb hpb
    (fun k _ => prudent_botdupoc_legPD k)
    (fun k _ => prudent_botdupoc_legDP k)
  refine ⟨max k₂ KL, fun k hk => ?_⟩
  have hk2 : k > k₂ := lt_of_le_of_lt (le_max_left _ _) hk
  have hKLk : Nat.log2 k + 3 ≤ k := by
    have := hKL k (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk))
    omega
  have hlk := log2_le_self k
  obtain ⟨m, hm⟩ := hk₂ k hk2
  obtain ⟨n, hplayD⟩ := Pf_sound m _ hm
  -- botDupoc's guard fired: JustBot's own guard about PrudentBot holds at k
  have hA_ps : proofSearch k
      (.plays (PrudentBot (2*k+64)) (.bot (DupocBot k)) .C) = true :=
    ps_k_of_play_botdupoc_any k n (PrudentBot (2*k+64)) hplayD
  -- JustBot cooperates (its guard is exactly hA_ps)
  have hA : play 4 (JustBot k) (PrudentBot (2*k+64)) = some .C := by
    refine JustBot_eval_step k 2 (PrudentBot (2*k+64)) .C ?_
    simpa using hA_ps
  -- PrudentBot's outer guard: JustBot's cooperative play, certified through its fired search
  have houter : proofSearch (2*k+64)
      (.plays (JustBot k) (PrudentBot (2*k+64)) .C) = true := by
    refine (proofSearch_spec _ _).2 (Pf.atom
      (⟨PlaysProof.search_t ((proofSearch_spec _ _).1 hA_ps) PlaysProof.const, ?_⟩ :
        AtomProvable (2*k+64) (.plays (JustBot k) (PrudentBot (2*k+64)) .C)))
    show c_leaf + c_guard k + c_node ≤ 2*k+64
    simp only [numCost, c_leaf, c_guard, c_node]
    omega
  -- PrudentBot's prudence about JustBot: the floored certificate fits its bigger budget
  have hprud : proofSearch (2*k+64) (.plays (JustBot k) (.bot DefectBot) .D) = true := by
    refine (proofSearch_spec _ _).2 (Pf_mono (justbot_prudence k) ?_)
    omega
  have hB : play 4 (PrudentBot (2*k+64)) (JustBot k) = some .C := by
    simpa using prudent_eval_both_true (2*k+64) 1 (JustBot k) houter hprud
  exact ⟨4, outcome_of_plays _ _ _ _ _ hA hB⟩

-- DupocBot --

theorem outcome_JustBot_vs_DupocBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (JustBot k) (DupocBot k) = some (.C, .C) := by
  let φ : Nat → Formula :=
    fun k => Formula.plays (DupocBot k) (.bot (DupocBot k)) .C
-- The two transparency legs, transcript-tight; `mutual_pblt_engine_id` lowers the premise
  -- subscript internally and runs the Löb chain (the old same-subscript `mutual_loeb`
  -- factoring is underivable under transcript cost).
  have legPD : ∀ k, Pf (30 * Nat.log2 k + 300)
      (.impl (.box k (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C))
             (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C)) := by
    intro k
    refine Pf.botSearchStep k (.plays .opp .self .C) .C .D (.bot (DupocBot k)) (DupocBot k) rfl ?_
    simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot]
    omega
  have legDP : ∀ k, Pf (30 * Nat.log2 k + 300)
      (.impl (.box k (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C))
             (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C)) := by
    intro k
    refine Pf.searchBranch k (.plays .opp .self .C) .C .D (DupocBot k) (.bot (DupocBot k)) rfl ?_
    simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot]
    omega
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C).size ≤ _
    simp only [numCost, Formula.size, Prog.size, DupocBot]
    omega
  have hsB : ∀ k,
      (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    simp only [numCost, Formula.size, Prog.size, DupocBot]
    omega
  have hpb : ∀ k, 30 * Nat.log2 k + 300 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := mutual_pblt_engine_id φ
    (fun k => Formula.plays (.bot (DupocBot k)) (DupocBot k) .C)
    (fun k => 30 * Nat.log2 k + 300) (fun k => 30 * Nat.log2 k + 300) 0
    hφsz hsB hpb hpb (fun k _ => legPD k) (fun k _ => legDP k)
  obtain ⟨KL, hKL⟩ := linear_log2_add_le 1 3
  refine ⟨max k₂ KL, ?_⟩
  intro k hk
  have hkk2 : k₂ < k := by
    have := Nat.le_max_left k₂ KL; omega
  have hKLk : Nat.log2 k + 3 ≤ k := by
    have h1 := Nat.le_max_right k₂ KL
    have := hKL k (by omega)
    omega
  obtain ⟨m, hm⟩ := hk₂ k hkk2
  have hAint : (φ k).interp := Pf_sound m _ hm
  obtain ⟨n, hplayA⟩ := hAint
  have hBtrue :
      proofSearch k (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C) = true := by
    cases hps : proofSearch k (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C) with
    | true => rfl
    | false =>
      exfalso
      have hgen : ∀ N, play N (DupocBot k) (.bot (DupocBot k)) = some .C → False := by
        intro N hN
        cases N with
        | zero => simp [play, eval] at hN
        | succ N0 =>
          cases N0 with
          | zero => simp [play, eval, DupocBot, Prog.subst, Formula.subst] at hN
          | succ N1 =>
            have hd : play (N1 + 2) (DupocBot k) (.bot (DupocBot k)) = some .D := by
              show eval (N1 + 2) (DupocBot k) (.bot (DupocBot k)) (DupocBot k) = some .D
              unfold DupocBot at hps ⊢
              simp [eval, Prog.subst, Formula.subst, hps]
            rw [hd] at hN; cases hN
      exact hgen n hplayA
  have hAplay2 : play 2 (DupocBot k) (.bot (DupocBot k)) = some .C := by
    show eval 2 (DupocBot k) (.bot (DupocBot k)) (DupocBot k) = some .C
    unfold DupocBot at hBtrue ⊢
    simp [eval, Prog.subst, Formula.subst, hBtrue]
  have hGA : proofSearch k
      (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C) = true := by
    -- hand certificate: Dupoc's search FIRED (hBtrue) — search_t ∘ const
    refine (proofSearch_spec _ _).2 (Pf.atom
      (⟨PlaysProof.search_t ((proofSearch_spec _ _).1 hBtrue) PlaysProof.const, ?_⟩ :
        AtomProvable k (.plays (DupocBot k) (.bot (DupocBot k)) .C)))
    show c_leaf + c_guard k + c_node ≤ k
    simp only [numCost, c_leaf, c_guard, c_node]
    omega
  have hJ : play 2 (JustBot k) (DupocBot k) = some .C := by
    show eval 2 (JustBot k) (DupocBot k) (JustBot k) = some .C
    unfold JustBot
    simp [eval, Prog.subst, Formula.subst, hGA]
  have hGJ : proofSearch k
      (Formula.plays (JustBot k) (DupocBot k) .C) = true := by
    -- hand certificate: JustBot's search FIRED (hGA) — search_t ∘ const
    refine (proofSearch_spec _ _).2 (Pf.atom
      (⟨PlaysProof.search_t ((proofSearch_spec _ _).1 hGA) PlaysProof.const, ?_⟩ :
        AtomProvable k (.plays (JustBot k) (DupocBot k) .C)))
    show c_leaf + c_guard k + c_node ≤ k
    simp only [numCost, c_leaf, c_guard, c_node]
    omega
  have hD : play 2 (DupocBot k) (JustBot k) = some .C := by
    show eval 2 (DupocBot k) (JustBot k) (DupocBot k) = some .C
    unfold DupocBot at hGJ ⊢
    simp [eval, Prog.subst, Formula.subst, hGJ]
  exact ⟨2, outcome_of_plays _ _ _ _ _ hJ hD⟩

end PD.Theorems
