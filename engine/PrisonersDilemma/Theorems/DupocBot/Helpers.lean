import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems
/-- Proof search is false for DefectBot -/
theorem proofSearch_false_for_DefectBot (k : Nat) :
    proofSearch k (.plays DefectBot (DupocBot k) .C) = false := by
  cases h : proofSearch k (.plays DefectBot (DupocBot k) .C) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_DefectBot_plays_C_false _)
  | false => rfl

/-- Proof search is true for CooperateBot vs DupocBot k at budget/index
    `atom_cost 1`. -/
theorem proofSearch_true_for_CooperateBot :
    ∃ k, proofSearch k (.plays CooperateBot (DupocBot k) .C) = true :=
  let k := atom_cost 1
  ⟨k, (proofSearch_spec _ _).2 (Pf.atom ⟨PlaysProof.const, by decide⟩)⟩


-- DBot --

/-- Proof search is false for `.bot DefectBot` against DupocBot: `.bot DefectBot`
    can never play C, so the proof search must fail. -/
theorem proofSearch_false_for_bot_DefectBot (k : Nat) :
    proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) = false := by
  cases h : proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_bot_DefectBot_plays_C_false _)
  | false => rfl

/-- DupocBot defects against `.bot DefectBot` because the search guard fails. -/
theorem DupocBot_plays_D_against_bot_DefectBot (k fuel : Nat) :
    play (fuel + 2) (DupocBot k) (.bot DefectBot) = some .D := by
  have hg := proofSearch_false_for_bot_DefectBot k
  show eval (fuel + 2) (DupocBot k) (.bot DefectBot) (DupocBot k) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- DBot probes its opponent against `.bot DefectBot`; DupocBot defects on that
    probe, so DBot's `ite` selects the cooperate branch. -/
theorem DBot_plays_C_against_DupocBot (k fuel : Nat) :
    play (fuel + 4) DBot (DupocBot k) = some .C := by
  have hDupoc : play (fuel + 2) (DupocBot k) (.bot DefectBot) = some .D :=
    DupocBot_plays_D_against_bot_DefectBot k fuel
  have hGuard :
      eval (fuel + 3) DBot (DupocBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) DBot (DupocBot k) DefectBot Action.D hDupoc)
  have hPlay := play_ite_from_guard
    fuel 3 DBot (DupocBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C)
    Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

/-! ### DupocBot vs DBot — the honest `(D, C)` outcome (floor formalized 2026-07-09).

HISTORY: the former `proofSearch_true_for_DBot`/`DupocBot_vs_DBot` (mutual cooperation
at a common budget) were ARTIFACTS of the inconsistent `atom_complete_false_guard`
axiom, retired 2026-07-02 with the false-guard repair. Honestly: DBot's C-play against
`DupocBot k` crosses Dupoc's own FAILED probe search (vs `.bot DefectBot`), so its
certificate pays the `search_f` floor — cost > k for EVERY k — and `DupocBot k` can
never prove "DBot plays C vs me" within its own budget (Critch-faithful: certifying
one's own failed bounded search costs more than the search budget itself; the guard
formula is TRUE, so soundness gives nothing — only cost accounting closes it).

RESOLVED (2026-07-09): the floor is now a THEOREM — `no_provable_DBot_C_tail` is the
cost lower bound (no ≤ k certificate exists), by strong induction on the budget:
* the transparency leaves die by the census (`Base/Exclusion.tail_plays_readable`) — DBot's
  shape (an `.ite` with a `.const` then-branch) is not bridge-readable;
* `atom` dies inside the `PlaysProof` replay: DBot's guard forces Dupoc's probe play,
  where `search_t` is refuted by soundness (`.bot DefectBot` never cooperates) and
  `search_f` carries the literal floor summand `k` — over budget by arithmetic;
* the `app`/`weakenImpl`/`implTrans`/`diagF`/`impS2` regress descends because
  transcript cumulativity makes every premise budget strictly smaller.
Hence Dupoc's guard search FAILS at its own budget and the honest outcome is `(D, C)`
(`outcome_DupocBot_vs_DBot`) — the asymmetry in the flesh: the simulator (DBot) can
afford to watch the searcher fail, the searcher can never afford to watch itself. -/

/-- **The `search_f` floor, formalized as a cost lower bound**: no proof of ≤ k
    characters concludes any formula whose implication-spine tail is
    "DBot plays C against `DupocBot k`" — in particular (spine of length zero) the
    guard instance itself is unprovable at Dupoc's own budget. Instance of the
    generalized `no_provable_probeFirst_C_tail` (Base/Exclusion.lean): DBot is the
    probe-first simulator with `q = .const .C`, DupocBot the budget-`k` searcher. -/
theorem no_provable_DBot_C_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays DBot (DupocBot k) .C) φ → False := by
  intro K φ hp hK ht
  refine no_provable_probeFirst_tail k DefectBot (.const .D) (.const .C) .C .C
      (.plays .opp .self .C) (.const .C) (.const .D) ?_ ?_ ?_ K φ hp hK ?_
  · simpa [Formula.subst, Prog.subst, DupocBot] using
      interp_bot_DefectBot_plays_C_false (DupocBot k)
  · intro k' ψ c0 c1 h; simp at h
  · exact fun L => const_ne_ctxPlug (by decide) L
  · simpa [DBot, DupocBot] using ht

/-- Dupoc's guard search fails against DBot AT EVERY budget — the floor's bite: the
    guard formula is true, but every certificate costs more than `k`. -/
theorem proofSearch_false_for_DBot_vs_Dupoc (k : Nat) :
    proofSearch k (.plays DBot (DupocBot k) .C) = false := by
  cases h : proofSearch k (.plays DBot (DupocBot k) .C) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => no_provable_DBot_C_tail k k _ hp le_rfl (by simp))
  | false => rfl

/-- DupocBot defects against DBot: its guard can never afford the certificate of
    DBot's (true!) cooperation. -/
theorem DupocBot_plays_D_against_DBot (k fuel : Nat) :
    play (fuel + 2) (DupocBot k) DBot = some .D := by
  have hg := proofSearch_false_for_DBot_vs_Dupoc k
  show eval (fuel + 2) (DupocBot k) DBot (DupocBot k) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

-- OBot --

/-- DupocBot cooperates with `.bot CooperateBot` once its search guard succeeds. -/
theorem DupocBot_plays_C_against_bot_CooperateBot (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    play (fuel + 2) (DupocBot k) (.bot CooperateBot) = some .C := by
  show eval (fuel + 2) (DupocBot k) (.bot CooperateBot) (DupocBot k) = some .C
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- OBot defects against DupocBot: outer probe sees DupocBot cooperate against
    `.bot CooperateBot` (search succeeds), so OBot descends into the inner ite.
    The inner probe sees DupocBot defect against `.bot DefectBot` (search fails),
    so OBot takes the defect branch. -/
theorem OBot_plays_D_against_DupocBot (k fuel : Nat)
    (hCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    play (fuel + 5) OBot (DupocBot k) = some .D := by
  have hDupocC : play (fuel + 3) (DupocBot k) (.bot CooperateBot) = some .C := by
    simpa [Nat.add_assoc] using DupocBot_plays_C_against_bot_CooperateBot k (fuel + 1) hCB
  have hOuterGuard :
      eval (fuel + 4) OBot (DupocBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) OBot (DupocBot k) CooperateBot Action.C hDupocC)
  have hDupocD : play (fuel + 2) (DupocBot k) (.bot DefectBot) = some .D :=
    DupocBot_plays_D_against_bot_DefectBot k fuel
  have hInnerGuard :
      eval (fuel + 3) OBot (DupocBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) OBot (DupocBot k) DefectBot Action.D hDupocD)
  have hPlay := play_ite_from_guard
    fuel 4 OBot (DupocBot k) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.C Action.C
    (by rfl) hOuterGuard
  have hInner :
      eval (fuel + 4) OBot (DupocBot k)
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D)) =
          some .D := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) OBot (DupocBot k)
        (.sim .opp (.bot DefectBot)) (.const Action.C) (.const Action.D)
        Action.C Action.D hInnerGuard)
  simpa [hInner] using hPlay

/-- Semantically, OBot never plays C against DupocBot (given the `.bot CB`
    proof-search succeeds). -/
theorem interp_OBot_plays_C_false (k : Nat)
    (hCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    ¬ (Formula.plays OBot (DupocBot k) .C).interp := by
  rintro ⟨n, hn⟩
  have hDB : proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) = false :=
    proofSearch_false_for_bot_DefectBot k
  cases n with
  | zero => simp only [play, eval, reduceCtorEq] at hn
  | succ m =>
      cases m with
      | zero => simp [play, eval, OBot] at hn
      | succ m =>
          cases m with
          | zero => simp [play, eval, OBot] at hn
          | succ m =>
              cases m with
              | zero =>
                  simp [play, eval, OBot, DupocBot, Prog.subst, Formula.subst] at hn
              | succ fuel =>
                  cases fuel with
                  | zero =>
                      unfold DupocBot at hCB hDB
                      simp [play, eval, OBot, DupocBot, Prog.subst, Formula.subst, hCB, hDB] at hn
                  | succ fuel =>
                      have hD : play (fuel + 5) OBot (DupocBot k) = some .D := by
                        simpa [Nat.add_assoc] using OBot_plays_D_against_DupocBot k fuel hCB
                      rw [hD] at hn
                      cases hn

/-- Proof search is false for OBot vs DupocBot k, given the `.bot CB` search succeeds. -/
theorem proofSearch_false_for_OBot (k : Nat)
    (hCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    proofSearch k (.plays OBot (DupocBot k) .C) = false := by
  cases h : proofSearch k (.plays OBot (DupocBot k) .C) with
  | true => exact absurd (proofSearch_sound _ _ h) (interp_OBot_plays_C_false k hCB)
  | false => rfl

/-- DupocBot defects against OBot: its search for "OBot plays C" fails, so it
    falls through to the defect branch. -/
theorem DupocBot_plays_D_against_OBot (k fuel : Nat)
    (hCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    play (fuel + 2) (DupocBot k) OBot = some .D := by
  have hOBot : proofSearch k (.plays OBot (DupocBot k) .C) = false :=
    proofSearch_false_for_OBot k hCB
  show eval (fuel + 2) (DupocBot k) OBot (DupocBot k) = some .D
  unfold DupocBot at hOBot ⊢
  simp [eval, Prog.subst, Formula.subst, hOBot]

/-- Proof search is true for `.bot CooperateBot` vs DupocBot k at budget
    `atom_cost 2`. -/
theorem proofSearch_true_for_bot_CooperateBot :
    ∃ k, proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true :=
  let k := atom_cost 2
  ⟨k, (proofSearch_spec _ _).2 (Pf.atom ⟨PlaysProof.bot PlaysProof.const, by decide⟩)⟩


-- TitForTatBot --

/-- TitForTatBot cooperates with DupocBot: its probe sees DupocBot cooperate
    against `.bot CooperateBot` (search succeeds), so the `ite` selects the
    cooperate branch. -/
theorem TitForTatBot_plays_C_against_DupocBot (k fuel : Nat)
    (hCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    play (fuel + 4) TitForTatBot (DupocBot k) = some .C := by
  have hDupocC : play (fuel + 2) (DupocBot k) (.bot CooperateBot) = some .C :=
    DupocBot_plays_C_against_bot_CooperateBot k fuel hCB
  have hGuard :
      eval (fuel + 3) TitForTatBot (DupocBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (DupocBot k) CooperateBot Action.C hDupocC)
  have hPlay := play_ite_from_guard
    fuel 3 TitForTatBot (DupocBot k) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

/-- Proof search k is true for TFT vs DupocBot k. The `.bot CooperateBot` guard
    fires at fuel 2 (budget `atom_cost 2`); that is
    lifted to `atom_cost 4` via monotonicity so TFT
    can cooperate at fuel 4, then bounded completeness gives the TFT budget. -/
theorem proofSearch_true_for_TitForTatBot :
    ∃ k, proofSearch k (.plays TitForTatBot (DupocBot k) .C) = true := by
  let kTFT := atom_cost 4
  -- Dupoc's guard vs `.bot CooperateBot` FIRES; TFT's certificate is built by hand:
  -- ite_t over the probe (sim → Dupoc's fired search_t) then the cooperate leaf.
  have hCBprov : Pf kTFT (.plays (.bot CooperateBot) (DupocBot kTFT) .C) :=
    Pf.atom ⟨PlaysProof.bot PlaysProof.const, by decide⟩
  refine ⟨kTFT, (proofSearch_spec _ _).2 (Pf.atom
    (⟨PlaysProof.ite_t (PlaysProof.sim (PlaysProof.search_t hCBprov PlaysProof.const))
      rfl PlaysProof.const, ?_⟩ :
      AtomProvable kTFT (.plays TitForTatBot (DupocBot kTFT) .C)))⟩
  show c_leaf + c_guard kTFT + c_node + c_node + c_leaf + c_node ≤ kTFT
  decide

/-- DupocBot cooperates with TFT once its search for "TFT plays C" succeeds. -/
theorem DupocBot_plays_C_against_TitForTatBot (k fuel : Nat)
    (hk : proofSearch k (.plays TitForTatBot (DupocBot k) .C) = true) :
    play (fuel + 2) (DupocBot k) TitForTatBot = some .C := by
  show eval (fuel + 2) (DupocBot k) TitForTatBot (DupocBot k) = some .C
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]


-- EBot --

/-- EBot cooperates with DupocBot: outer probe (`.bot DefectBot`) sees DupocBot
    defect (always), so EBot descends into the inner ite. The next probe
    (`.bot CooperateBot`) sees DupocBot cooperate (search succeeds), so EBot
    cooperates. -/
theorem EBot_plays_C_against_DupocBot (k fuel : Nat)
    (hCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    play (fuel + 5) EBot (DupocBot k) = some .C := by
  have hDupocD : play (fuel + 3) (DupocBot k) (.bot DefectBot) = some .D := by
    simpa [Nat.add_assoc] using DupocBot_plays_D_against_bot_DefectBot k (fuel + 1)
  have hGuard1 :
      eval (fuel + 4) EBot (DupocBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) EBot (DupocBot k) DefectBot Action.D hDupocD)
  have hDupocC : play (fuel + 2) (DupocBot k) (.bot CooperateBot) = some .C :=
    DupocBot_plays_C_against_bot_CooperateBot k fuel hCB
  have hGuard2 :
      eval (fuel + 3) EBot (DupocBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) EBot (DupocBot k) CooperateBot Action.C hDupocC)
  have hInner :
      eval (fuel + 4) EBot (DupocBot k)
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
          (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))) =
        some .C := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) EBot (DupocBot k)
        (.sim .opp (.bot CooperateBot)) (.const Action.C)
        (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))
        Action.C Action.C hGuard2)
  have hPlay := play_ite_from_guard
    fuel 4 EBot (DupocBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D)
    (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
      (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
    Action.C Action.D
    (by rfl) hGuard1
  simpa [Nat.add_assoc, hInner] using hPlay

/-! ### DupocBot vs EBot — the honest `(D, C)` outcome (floor formalized 2026-07-09).

HISTORY: `proofSearch_true_for_EBot`/`DupocBot_vs_EBot` (mutual cooperation at a common
budget) were RETIRED 2026-07-02 as axiom artifacts: EBot's C-play against `DupocBot k`
crosses Dupoc's own FAILED outer-probe search (vs `.bot DefectBot`), so its certificate
pays the `search_f` floor — cost > k for every k.

RESOLVED (2026-07-09): the floor is a THEOREM — `no_provable_EBot_C_tail`, the same
instance of `no_provable_probeFirst_C_tail` as DBot (EBot shares DBot's first probe;
only the else-branch `q` differs, and the floor fires before `q` is ever consulted).
Dupoc's guard fails at every budget, so Dupoc defects while EBot — whose probes are
run-priced simulations, no floor — cooperates: `outcome_DupocBot_vs_EBot = (D, C)`
for every `k ≥ 2` (the tiny bound is the Σ₁ price of certifying the `.bot CooperateBot`
probe that steers EBot's second guard). -/

/-- The floor for the EBot pair: no ≤ k certificate concludes any formula whose
    spine tail is "EBot plays C against `DupocBot k`". -/
theorem no_provable_EBot_C_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays EBot (DupocBot k) .C) φ → False := by
  intro K φ hp hK ht
  refine no_provable_probeFirst_tail k DefectBot (.const .D)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))
      .C .C (.plays .opp .self .C) (.const .C) (.const .D) ?_ ?_ ?_ K φ hp hK ?_
  · simpa [Formula.subst, Prog.subst, DupocBot] using
      interp_bot_DefectBot_plays_C_false (DupocBot k)
  · intro k' ψ c0 c1 h; simp at h
  · exact fun L => const_ne_ctxPlug (by decide) L
  · simpa [EBot, DupocBot] using ht

/-- Dupoc's guard search fails against EBot at every budget — the floor's bite. -/
theorem proofSearch_false_for_EBot_vs_Dupoc (k : Nat) :
    proofSearch k (.plays EBot (DupocBot k) .C) = false := by
  cases h : proofSearch k (.plays EBot (DupocBot k) .C) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => no_provable_EBot_C_tail k k _ hp le_rfl (by simp))
  | false => rfl

/-- DupocBot defects against EBot: its guard can never afford the certificate of
    EBot's (true!) cooperation. -/
theorem DupocBot_plays_D_against_EBot (k fuel : Nat) :
    play (fuel + 2) (DupocBot k) EBot = some .D := by
  have hg := proofSearch_false_for_EBot_vs_Dupoc k
  show eval (fuel + 2) (DupocBot k) EBot (DupocBot k) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- The `.bot CooperateBot` probe guard is Σ₁-certifiable at run price (a two-character
    `bot`+`const` replay), discharging `EBot_plays_C_against_DupocBot`'s hypothesis. -/
theorem proofSearch_true_for_bot_CooperateBot_vs_Dupoc (k : Nat) (hk : 2 ≤ k) :
    proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true :=
  (proofSearch_spec _ _).2 (Pf.atom
    ⟨PlaysProof.bot PlaysProof.const, by simp only [c_leaf, c_node]; omega⟩)

/-- DupocBot cooperates with EBot once its search for "EBot plays C" succeeds. -/
theorem DupocBot_plays_C_against_EBot (k fuel : Nat)
    (hk : proofSearch k (.plays EBot (DupocBot k) .C) = true) :
    play (fuel + 2) (DupocBot k) EBot = some .C := by
  show eval (fuel + 2) (DupocBot k) EBot (DupocBot k) = some .C
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]


-- DupocBot --

/-- DUPOC-specific Löb premise (critch22 Theorem 3.7 substitution into PBLT),
    **character-faithful and transcript-tight**. The `searchBranch` derivation concluding
    `□_k (DUPOC plays C vs DUPOC) → (DUPOC plays C vs DUPOC)` is a single leaf whose
    transcript is exactly its conclusion: `5 * log2 k + 33` characters (`DupocBot k` is
    structurally identical to `CupodBot k`, so each costs `log2 k + 7`). Under the
    transcript cost model the premise is `Pf (5·log2 k + 33)` UNCONDITIONALLY —
    no `K₀` eventuality — and the small budget is exactly what `pblt_engine_id`
    consumes (do NOT weaken it up to `k`; the Löb chain needs `pm ≪ k`).

    The conclusion is *definitionally* the `searchBranch` conclusion: the guard
    `(.plays .opp .self .C).subst (DupocBot k) (DupocBot k)` unfolds to
    `.plays (DupocBot k) (DupocBot k) .C`. -/
theorem dupoc_loeb_premise (k : Nat) :
    Pf (5 * Nat.log2 k + 33)
      (.impl (.box k (.plays (DupocBot k) (DupocBot k) .C))
             (.plays (DupocBot k) (DupocBot k) .C)) := by
  refine Pf.searchBranch k (.plays .opp .self .C) .C .D (DupocBot k) (DupocBot k) rfl ?_
  simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot]
  omega


-- MirrorBot --

/-- Löb premise for DupocBot vs MirrorBot. Combines source-code transparency
    of DupocBot's `.search` body (`□_k φ_A → φ_B`) with `.sim` source
    transparency for MirrorBot (`φ_B → φ_A`), chained by `Dynamics.hypSyll`
    into the closed `□_k φ → φ` that PBLT requires. (Symmetric to
    `cupod_mirror_loeb_premise`.) -/
theorem dupoc_mirror_loeb_premise (k : Nat) :
    Pf (20 * Nat.log2 k + 150)
      (.impl (.box k (.plays MirrorBot (DupocBot k) .C))
             (.plays MirrorBot (DupocBot k) .C)) := by
  -- The `hypSyll` TRANSCRIPT pays both leaves plus its conclusion (transcript cost model):
  -- searchBranch leaf + simStep leaf + the `□_k … → …` conclusion — all `O(log k)`;
  -- `20·log2 k + 150` is a generous uniform bound, valid for ALL `k` (no K₀ eventuality).
  -- Pf-only: a `hypSyll` TREE smuggled through `struct` becomes a FLAT `implTrans`
  -- of two bare leaves — same two transparency steps, same total budget.
  refine Pf.implTrans _ _ _ (5 * Nat.log2 k + 50) (5 * Nat.log2 k + 50)
    (Pf.searchBranch k (.plays .opp .self .C) .C .D (DupocBot k) MirrorBot rfl ?_)
    (Pf.simStep MirrorBot .opp .self (DupocBot k) .C rfl ?_) ?_ <;>
  · simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot, MirrorBot]
    omega

/-- Once `proofSearch k = true`, DupocBot's eval against MirrorBot takes the
    cooperate branch. -/
theorem DupocBot_plays_C_against_MirrorBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (DupocBot k) .C) = true) :
    play (fuel + 2) (DupocBot k) MirrorBot = some .C := by
  show eval (fuel + 2) (DupocBot k) MirrorBot (DupocBot k) = some .C
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- MirrorBot mirrors DupocBot's cooperate via the `.sim .opp .self` swap. -/
theorem MirrorBot_plays_C_against_DupocBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (DupocBot k) .C) = true) :
    play (fuel + 3) MirrorBot (DupocBot k) = some .C := by
  have hDupoc : play (fuel + 2) (DupocBot k) MirrorBot = some .C :=
    DupocBot_plays_C_against_MirrorBot k fuel hk
  simpa [play, eval, Prog.subst, MirrorBot] using hDupoc

/-- Dual of `DupocBot_plays_C_against_MirrorBot`: when proofSearch fails,
    DupocBot falls through to its `.const .D` defect branch. -/
theorem DupocBot_plays_D_against_MirrorBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (DupocBot k) .C) = false) :
    play (fuel + 2) (DupocBot k) MirrorBot = some .D := by
  show eval (fuel + 2) (DupocBot k) MirrorBot (DupocBot k) = some .D
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- Dual of `MirrorBot_plays_C_against_DupocBot`: MirrorBot mirrors the defect
    branch via the `.sim .opp .self` swap. -/
theorem MirrorBot_plays_D_against_DupocBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (DupocBot k) .C) = false) :
    play (fuel + 3) MirrorBot (DupocBot k) = some .D := by
  have hDupoc : play (fuel + 2) (DupocBot k) MirrorBot = some .D :=
    DupocBot_plays_D_against_MirrorBot k fuel hk
  simpa [play, eval, Prog.subst, MirrorBot] using hDupoc

/-- Inversion: from a `play` witness on MirrorBot's leg, recover that DupocBot's
    proof-search guard at parameter `k` must have fired. The play can only be
    `some .C` if DupocBot's `.search` took the `.const .C` branch, which requires
    `proofSearch k = true`. -/
theorem proofSearch_k_of_play_MirrorBot_dupoc
    (k n : Nat) (h : play n MirrorBot (DupocBot k) = some .C) :
    proofSearch k (.plays MirrorBot (DupocBot k) .C) = true := by
  cases hps : proofSearch k (.plays MirrorBot (DupocBot k) .C) with
  | true  => rfl
  | false =>
    exfalso
    rcases n with _ | _ | _ | n
    · simp [play, eval] at h
    · simp [play, eval, MirrorBot] at h
    · have hev : play 2 MirrorBot (DupocBot k) = none := by
        unfold DupocBot
        simp [play, eval, Prog.subst, MirrorBot, Formula.subst]
      rw [hev] at h
      cases h
    · have hev : play (n + 3) MirrorBot (DupocBot k) = some .D := by
        simpa using MirrorBot_plays_D_against_DupocBot k n hps
      rw [hev] at h
      cases h


-- CupodBot --

/-! ### The red cell's machinery — the τ-transposition route (2026-08-20)

Cupod is the τ̂-transpose of Dupoc (`Base/Transpose`; the paper's Def 1.11 holds
by `rfl` here), so the two substituted guards are each other's τ-images:
`ρ₁ = "Cupod plays C vs Dupoc"` (Dupoc's guard) transposes to
`ρ₂ = "Dupoc plays D vs Cupod"` (Cupod's guard). `Pf.transpose` (Thm 1.10,
same budget) plus soundness plus `eval` determinism then kill BOTH guards at
every budget `k` — no floor census, no exclusion machinery. Consumed by
`Theorems/DupocBot/vs_CupodBot.lean` (the paper's Thm 1.14). -/

theorem transpose_DupocBot (k : Nat) : (DupocBot k).transpose = CupodBot k := by
  simp [DupocBot, CupodBot, Prog.transpose, Formula.transpose, Action.swap]

theorem transpose_CupodBot (k : Nat) : (CupodBot k).transpose = DupocBot k := by
  simp [DupocBot, CupodBot, Prog.transpose, Formula.transpose, Action.swap]

/-- `ρ₁^τ = ρ₂`: Dupoc's substituted guard transposes to Cupod's. -/
theorem rho1_transpose (k : Nat) :
    (Formula.plays (CupodBot k) (DupocBot k) Action.C).transpose
      = .plays (DupocBot k) (CupodBot k) Action.D := by
  simp [Formula.transpose, transpose_CupodBot, transpose_DupocBot, Action.swap]

/-- `ρ₂^τ = ρ₁` (τ is an involution). -/
theorem rho2_transpose (k : Nat) :
    (Formula.plays (DupocBot k) (CupodBot k) Action.D).transpose
      = .plays (CupodBot k) (DupocBot k) Action.C := by
  simp [Formula.transpose, transpose_CupodBot, transpose_DupocBot, Action.swap]

/-- Dupoc's guard `ρ₁ = "Cupod plays C vs Dupoc"` is unprovable at Dupoc's own
    budget: `□_k ρ₁` would fire Dupoc's search (→ Dupoc plays `C`) while its
    τ-image `□_k ρ₂` is sound (→ Dupoc plays `D`) — `eval` can't do both. -/
theorem not_Pf_dupoc_guard (k : Nat) :
    ¬ Pf k (.plays (CupodBot k) (DupocBot k) .C) := by
  intro h1
  -- Thm 1.10: transport the proof across τ, so `□_k ρ₂` holds too
  have h2 : Pf k (.plays (DupocBot k) (CupodBot k) .D) := by
    have := Pf.transpose h1
    rwa [rho1_transpose] at this
  -- `□_k ρ₁` fires Dupoc's search: Dupoc plays C at fuel 2
  have hps : proofSearch k (.plays (CupodBot k) (DupocBot k) .C) = true :=
    (proofSearch_spec _ _).2 h1
  have hC : eval 2 (DupocBot k) (CupodBot k) (DupocBot k) = some .C := by
    unfold DupocBot at hps ⊢
    simp [eval, Prog.subst, Formula.subst, hps]
  -- `□_k ρ₂` is sound: Dupoc plays D at some fuel
  obtain ⟨N, hD⟩ := Pf_sound _ _ h2
  have hD' : eval N (DupocBot k) (CupodBot k) (DupocBot k) = some .D := hD
  exact absurd (eval_det hC hD') (by decide)

/-- Cupod's guard `ρ₂` is unprovable too: its τ-image is `ρ₁`. -/
theorem not_Pf_cupod_guard (k : Nat) :
    ¬ Pf k (.plays (DupocBot k) (CupodBot k) .D) := by
  intro h
  have h1 : Pf k (.plays (CupodBot k) (DupocBot k) .C) := by
    have := Pf.transpose h
    rwa [rho2_transpose] at this
  exact not_Pf_dupoc_guard k h1

/-- Dupoc's search fails: the oracle's boolean reflection of `not_Pf_dupoc_guard`. -/
theorem proofSearch_false_dupoc_guard (k : Nat) :
    proofSearch k (.plays (CupodBot k) (DupocBot k) .C) = false := by
  cases h : proofSearch k (.plays (CupodBot k) (DupocBot k) .C) with
  | true => exact absurd ((proofSearch_spec _ _).1 h) (not_Pf_dupoc_guard k)
  | false => rfl

/-- Cupod's search fails too. -/
theorem proofSearch_false_cupod_guard (k : Nat) :
    proofSearch k (.plays (DupocBot k) (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays (DupocBot k) (CupodBot k) .D) with
  | true => exact absurd ((proofSearch_spec _ _).1 h) (not_Pf_cupod_guard k)
  | false => rfl

/-- Dupoc defaults: `D` against Cupod. -/
theorem DupocBot_plays_D_vs_CupodBot (k fuel : Nat) :
    play (fuel + 2) (DupocBot k) (CupodBot k) = some .D := by
  have hg := proofSearch_false_dupoc_guard k
  show eval (fuel + 2) (DupocBot k) (CupodBot k) (DupocBot k) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- Cupod defaults: `C` against Dupoc. -/
theorem CupodBot_plays_C_vs_DupocBot (k fuel : Nat) :
    play (fuel + 2) (CupodBot k) (DupocBot k) = some .C := by
  have hg := proofSearch_false_cupod_guard k
  show eval (fuel + 2) (CupodBot k) (DupocBot k) (CupodBot k) = some .C
  unfold CupodBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-! ## The defection floor, generic in the opponent (2026-08-21)

DupocBot's `D` is its ELSE-slot, so any certificate of it crosses `search_f` and
pays the full failed budget. The mirror of `no_provable_DIMCID_C_tail`; together
they close the ANTI-ALIGNED pair `DIMCID × DupocBot`, exactly as the tau layer's
alignment rule predicts. -/

/-- No proof of ≤ k characters concludes any formula whose guarded spine tail is
    "DupocBot plays D against O": `search_t` concludes the then-constant `.C`
    (action mismatch), `search_f` pays the floor. -/
theorem no_provable_DupocBot_D_tail (k : Nat) (O : Prog) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (DupocBot k) O .D) φ → False := by
  intro K φ hp hK ht
  refine no_provable_tailToS_floor k (· = .plays (DupocBot k) O .D)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 ht)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · intro K' hK' φ' hφ'
    cases hφ'
    intro hA
    cases hA with
    | mk hpp hn =>
      unfold DupocBot at hpp
      cases hpp with
      | search_t hProv hbr => cases hbr
      | search_f hneg hbr => simp only [c_node] at hn; omega
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    unfold DupocBot at hme
    injection hme with e1 e2 e3 e4
    simp at e3
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3
    subst h1
    unfold DupocBot at hme; simp at hme
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3
    subst h1
    unfold DupocBot at hme; simp at hme
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3
    subst h1
    unfold DupocBot at hme; simp at hme
  · intro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3
    unfold DupocBot at h1; simp at h1
  · intro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3
    subst h1
    unfold DupocBot at hme; simp at hme
  · intro me oppo c hS L hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    cases L with
    | nil => unfold DupocBot at hme; simp [searchPlug] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        unfold DupocBot at hme
        simp only [searchPlug, Prog.search.injEq] at hme
        have hcontra := hme.2.2.1
        rw [searchPlug_eq_ctxPlug tl (.const .D)] at hcontra
        exact const_ne_ctxPlug (by decide) _ hcontra
  · intro me oppo c hS hd L hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    exfalso
    cases hd with
    | searchL g ψ e =>
        unfold DupocBot at hme
        simp only [ctxPlug, Prog.search.injEq] at hme
        have hcontra := hme.2.2.1
        exact const_ne_ctxPlug (by decide) L hcontra
    | iteL z aT other => unfold DupocBot at hme; simp [ctxPlug] at hme
  · intro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases hd with
    | thenL g ψ e =>
        simp only [plug2, DupocBot, Prog.search.injEq] at hme
        obtain ⟨-, -, hplug, -⟩ := hme
        exfalso
        cases L with
        | nil => simp [plug2] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [plug2] at hplug
    | elseL g P' Q' c' q =>
        simp only [plug2, DupocBot, Prog.search.injEq] at hme
        obtain ⟨rfl, -, -, -⟩ := hme
        simp only [layersCost, layerCost, c_node]
        omega
  · intro me oppo c hS defs i _ _ _ hme _
    injection hS with h1 h2 h3
    subst h1
    unfold DupocBot at hme; simp at hme

end PD.Theorems
