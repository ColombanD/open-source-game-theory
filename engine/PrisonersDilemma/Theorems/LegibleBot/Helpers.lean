import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # LegibleBot matchup helpers — the floor-dominated regime

LegibleBot's guard `□_kIn (I play C)` contains its own substituted source, so at
budgets below the guard's size the SIZE FLOOR (`proofSearch_false_box_undersized`)
forces the illegible else-branch: it defects against EVERYONE, including
CooperateBot. Every lemma is stated for the WHOLE floor regime (size hypotheses,
discharged `by decide` at concrete budgets). The non-degenerate regime — where the
guard fits and bounded Löb fires it through two boxes — is RESOLVED (2026-07-30)
at staggered dials `LegibleBot (2*k+64) k`: `searchBranch` + `box4` + `implTrans`
yield the single-box Löb premise and `pblt_engine` closes it (the large-`k` core
below). Floor lemmas verified against the deterministic pre-pass (2026-07-29). -/

/-- **The floor**: below the substituted box-guard's size, LegibleBot cannot
    certify its own legibility and defects. -/
theorem LegibleBot_defects_floor (kOut kIn fuel : Nat) (opponent : Prog)
    (hsz : kOut < (Formula.box kIn (.plays (LegibleBot kOut kIn) opponent .C)).size) :
    play (fuel + 2) (LegibleBot kOut kIn) opponent = some .D := by
  have hg := proofSearch_false_box_undersized hsz
  show eval (fuel + 2) (LegibleBot kOut kIn) opponent (LegibleBot kOut kIn) = some .D
  unfold LegibleBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-! ## How the rest of the zoo plays against a floor-regime LegibleBot -/

/-- MirrorBot mirrors the floor-defection back. -/
theorem MirrorBot_plays_D_against_LegibleBot_floor (kOut kIn fuel : Nat)
    (hszM : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) MirrorBot .C)).size) :
    play (fuel + 3) MirrorBot (LegibleBot kOut kIn) = some .D := by
  have h := LegibleBot_defects_floor kOut kIn fuel MirrorBot hszM
  show eval (fuel + 3) MirrorBot (LegibleBot kOut kIn) MirrorBot = some .D
  simpa [eval, MirrorBot, Prog.subst] using h

/-- TitForTatBot's CooperateBot probe sees the floor-defection and punishes. -/
theorem TitForTatBot_plays_D_against_LegibleBot_floor (kOut kIn fuel : Nat)
    (hszCB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot CooperateBot) .C)).size) :
    play (fuel + 4) TitForTatBot (LegibleBot kOut kIn) = some .D := by
  have hL : play (fuel + 2) (LegibleBot kOut kIn) (.bot CooperateBot) = some .D :=
    LegibleBot_defects_floor kOut kIn fuel _ hszCB
  have hGuard : eval (fuel + 3) TitForTatBot (LegibleBot kOut kIn)
      (.sim .opp (.bot CooperateBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (LegibleBot kOut kIn)
        CooperateBot .D hL)
  have hPlay := play_ite_from_guard fuel 3 TitForTatBot (LegibleBot kOut kIn)
    (.sim .opp (.bot CooperateBot)) (.const .C) (.const .D) .C .D (by rfl) hGuard
  simpa [eval] using hPlay

/-- DBot's DefectBot probe sees the floor-defection, so DBot cooperates (it only
    exploits bots that cooperate with defectors). -/
theorem DBot_plays_C_against_LegibleBot_floor (kOut kIn fuel : Nat)
    (hszDB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot DefectBot) .C)).size) :
    play (fuel + 4) DBot (LegibleBot kOut kIn) = some .C := by
  have hL : play (fuel + 2) (LegibleBot kOut kIn) (.bot DefectBot) = some .D :=
    LegibleBot_defects_floor kOut kIn fuel _ hszDB
  have hGuard : eval (fuel + 3) DBot (LegibleBot kOut kIn)
      (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) DBot (LegibleBot kOut kIn)
        DefectBot .D hL)
  have hPlay := play_ite_from_guard fuel 3 DBot (LegibleBot kOut kIn)
    (.sim .opp (.bot DefectBot)) (.const .D) (.const .C) .C .D (by rfl) hGuard
  simpa [eval] using hPlay

/-- OBot's first probe (vs CooperateBot) already sees the floor-defection and
    OBot defects. -/
theorem OBot_plays_D_against_LegibleBot_floor (kOut kIn fuel : Nat)
    (hszCB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot CooperateBot) .C)).size) :
    play (fuel + 4) OBot (LegibleBot kOut kIn) = some .D := by
  have hL : play (fuel + 2) (LegibleBot kOut kIn) (.bot CooperateBot) = some .D :=
    LegibleBot_defects_floor kOut kIn fuel _ hszCB
  have hGuard : eval (fuel + 3) OBot (LegibleBot kOut kIn)
      (.sim .opp (.bot CooperateBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) OBot (LegibleBot kOut kIn)
        CooperateBot .D hL)
  have hPlay := play_ite_from_guard fuel 3 OBot (LegibleBot kOut kIn)
    (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D)) (.const .D)
    .C .D (by rfl) hGuard
  simpa [eval] using hPlay

/-- EBot walks all three probes (DefectBot, CooperateBot, MirrorBot), sees the
    floor-defection each time, and defects. -/
theorem EBot_plays_D_against_LegibleBot_floor (kOut kIn fuel : Nat)
    (hszDB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot DefectBot) .C)).size)
    (hszCB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot CooperateBot) .C)).size)
    (hszM : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot MirrorBot) .C)).size) :
    play (fuel + 6) EBot (LegibleBot kOut kIn) = some .D := by
  have hL1 : play (fuel + 4) (LegibleBot kOut kIn) (.bot DefectBot) = some .D :=
    LegibleBot_defects_floor kOut kIn (fuel + 2) _ hszDB
  have hL2 : play (fuel + 3) (LegibleBot kOut kIn) (.bot CooperateBot) = some .D :=
    LegibleBot_defects_floor kOut kIn (fuel + 1) _ hszCB
  have hL3 : play (fuel + 2) (LegibleBot kOut kIn) (.bot MirrorBot) = some .D :=
    LegibleBot_defects_floor kOut kIn fuel _ hszM
  have hG1 : eval (fuel + 5) EBot (LegibleBot kOut kIn)
      (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 4) EBot (LegibleBot kOut kIn)
        DefectBot .D hL1)
  have hG2 : eval (fuel + 4) EBot (LegibleBot kOut kIn)
      (.sim .opp (.bot CooperateBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) EBot (LegibleBot kOut kIn)
        CooperateBot .D hL2)
  have hG3 : eval (fuel + 3) EBot (LegibleBot kOut kIn)
      (.sim .opp (.bot MirrorBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) EBot (LegibleBot kOut kIn)
        MirrorBot .D hL3)
  have hInner3 : eval (fuel + 4) EBot (LegibleBot kOut kIn)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)) = some .D := by
    have h := eval_ite_from_guard (fuel + 3) EBot (LegibleBot kOut kIn)
      (.sim .opp (.bot MirrorBot)) (.const .C) (.const .D) .C .D hG3
    simpa [Nat.add_assoc, eval] using h
  have hInner2 : eval (fuel + 5) EBot (LegibleBot kOut kIn)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))) = some .D := by
    have h := eval_ite_from_guard (fuel + 4) EBot (LegibleBot kOut kIn)
      (.sim .opp (.bot CooperateBot)) (.const .C)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)) .C .D hG2
    rw [show fuel + 4 + 1 = fuel + 5 by omega] at h
    simpa [hInner3] using h
  have hPlay := play_ite_from_guard fuel 5 EBot (LegibleBot kOut kIn)
    (.sim .opp (.bot DefectBot)) (.const .D)
    (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))
    .C .D (by rfl) hG1
  simpa [hInner2] using hPlay

/-- CIMCIC's implication guard hits the size floor against a same-budget
    LegibleBot. -/
theorem CIMCIC_plays_D_against_LegibleBot_floor (k fuel : Nat)
    (hszI : k < (Formula.impl (.plays (CIMCIC k) (LegibleBot k k) .C)
      (.plays (LegibleBot k k) (CIMCIC k) .C)).size) :
    play (fuel + 2) (CIMCIC k) (LegibleBot k k) = some .D := by
  have hg := proofSearch_false_impl_undersized hszI
  show eval (fuel + 2) (CIMCIC k) (LegibleBot k k) (CIMCIC k) = some .D
  unfold CIMCIC at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- DIMCID's implication guard hits the size floor; it cooperates by default. -/
theorem DIMCID_plays_C_against_LegibleBot_floor (k fuel : Nat)
    (hszI : k < (Formula.impl (.plays (DIMCID k) (LegibleBot k k) .C)
      (.plays (LegibleBot k k) (DIMCID k) .D)).size) :
    play (fuel + 2) (DIMCID k) (LegibleBot k k) = some .C := by
  have hg := proofSearch_false_impl_undersized hszI
  show eval (fuel + 2) (DIMCID k) (LegibleBot k k) (DIMCID k) = some .C
  unfold DIMCID at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]


/-- **The Löb premise** `□_k ψ → ψ` (ψ = "LegibleBot (2k+64) k plays C vs X"),
    fully opponent-generic: any `X` whose source size obeys the linear side
    condition. Construction: `searchBranch` reads the `.search` body giving
    `□_{2k+64}(□_k ψ) → ψ`; `box4` (object GL-4 — the step LegibleBot was built
    to exercise) gives `□_k ψ → □_{2k+64}(□_k ψ)`, its side condition
    `k + |□_k ψ| ≤ 2k+64` being exactly what the stagger buys; `implTrans`
    composes. Transcript is `O(log k + |X|)`. -/
theorem legible_loeb_premise (k : Nat) (X : Prog)
    (hk : 3 * Nat.log2 k + X.size + 40 ≤ k) :
    Pf (20 * Nat.log2 k + 6 * X.size + 200)
       (.impl (.box k (.plays (LegibleBot (2*k+64) k) X .C))
              (.plays (LegibleBot (2*k+64) k) X .C)) := by
  have hstag : Nat.log2 (2*k+64) ≤ Nat.log2 k + 8 := log2_stagger_le k
  -- (a) searchBranch: □_{2k+64}(□_k ψ) → ψ
  have leg1 : Pf ((Formula.impl
        (.box (2*k+64) (.box k (.plays (LegibleBot (2*k+64) k) X .C)))
        (.plays (LegibleBot (2*k+64) k) X .C)).size)
      (.impl (.box (2*k+64) (.box k (.plays (LegibleBot (2*k+64) k) X .C)))
        (.plays (LegibleBot (2*k+64) k) X .C)) := by
    have := Pf.searchBranch (2*k+64) (.box k (.plays .self .opp Action.C))
      Action.C Action.D (LegibleBot (2*k+64) k) X rfl (Nat.le_refl _)
    simpa [LegibleBot, Formula.subst, Prog.subst] using this
  -- (b) box4: □_k ψ → □_{2k+64}(□_k ψ)
  have leg2 : Pf ((Formula.impl
        (.box k (.plays (LegibleBot (2*k+64) k) X .C))
        (.box (2*k+64) (.box k (.plays (LegibleBot (2*k+64) k) X .C)))).size)
      (.impl (.box k (.plays (LegibleBot (2*k+64) k) X .C))
        (.box (2*k+64) (.box k (.plays (LegibleBot (2*k+64) k) X .C)))) := by
    refine Pf.box4 k (2*k+64) _ (.plays (LegibleBot (2*k+64) k) X .C) ?_ (Nat.le_refl _)
    simp only [Formula.size, LegibleBot, Prog.size, numCost]
    omega
  -- (c) compose
  refine Pf.implTrans _ _ _ _ _ leg2 leg1 ?_
  simp only [Formula.size, LegibleBot, Prog.size, numCost]
  omega

/-- **The engine fires**: `LegibleBot (2k+64) k` PROVABLY cooperates with any
    opponent FAMILY `X : Nat → Prog` of source size ≤ `B + 20·log2 k`, at large
    `k` (`pblt_engine` at `f = id` — the Löb premise's box subscript is exactly
    the inner dial). The family form covers fixed opponents (constant families),
    budget-carrying opponents (`B` absorbs their size), and `k`-indexed ones
    (self-play, CIMCIC, DIMCID). Conclusion at the `Pf` level — the CIMCIC
    matchup consumes the certificate, not just the play. -/
theorem LegibleBot_cooperates_Pf (X : Nat → Prog) (B : Nat)
    (hXsz : ∀ k, (X k).size ≤ B + 20 * Nat.log2 k) :
    ∃ k₂, ∀ k, k > k₂ →
      ∃ m, Pf m (.plays (LegibleBot (2*k+64) k) (X k) .C) := by
  let φ : Nat → Formula := fun k => .plays (LegibleBot (2*k+64) k) (X k) .C
  let pm : Nat → Nat := fun k => 20 * Nat.log2 k + 6 * (X k).size + 200
  obtain ⟨Kc, hKc⟩ := linear_log2_add_le 23 (B + 40)
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le (8192 * 163) (8192 * (7 * B + 300))
  have hLoeb : ∀ k, k > max Kc Ksz → Pf (pm k) (.impl (.box (id k) (φ k)) (φ k)) := by
    intro k hk
    have hc : 23 * Nat.log2 k + (B + 40) ≤ k :=
      hKc k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_left _ _) hk))
    have hx := hXsz k
    exact legible_loeb_premise k (X k) (by omega)
  have hsz : ∀ k, k > max Kc Ksz →
      8192 * (pm k + (φ k).size + Nat.log2 (id k) + 8) ≤ id k := by
    intro k hk
    have hbig := hKsz k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
    have hx := hXsz k
    have hst := log2_stagger_le k
    have hφsz : (φ k).size = Nat.log2 (2*k+64) + Nat.log2 k + 10 + (X k).size := by
      show (Formula.plays (LegibleBot (2*k+64) k) (X k) .C).size = _
      simp only [Formula.size, LegibleBot, Prog.size, numCost]
      omega
    have hpmval : pm k = 20 * Nat.log2 k + 6 * (X k).size + 200 := rfl
    show 8192 * (pm k + (φ k).size + Nat.log2 (id k) + 8) ≤ id k
    rw [hφsz, hpmval]
    simp only [id]
    omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine φ id pm (max Kc Ksz) hLoeb hsz
  exact ⟨k₂, hk₂⟩

/-- Play-level corollary of `LegibleBot_cooperates_Pf`, via soundness
    (`interp (.plays p q a)` IS `∃ n, play n p q = some a`). -/
theorem LegibleBot_cooperates_large (X : Nat → Prog) (B : Nat)
    (hXsz : ∀ k, (X k).size ≤ B + 20 * Nat.log2 k) :
    ∃ k₂, ∀ k, k > k₂ →
      ∃ n, play n (LegibleBot (2*k+64) k) (X k) = some .C := by
  obtain ⟨k₂, h⟩ := LegibleBot_cooperates_Pf X B hXsz
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := h k hk
  exact Pf_sound m _ hm

/-- **Guard-fire extraction**: a C-play means the search guard actually fired
    (the else-branch plays D), so `□_k ψ` is provable at the OUTER budget —
    recovering a BOUNDED certificate that the engine's unbounded `∃ m` hides.
    (`interp (.box k ψ) = Pf k ψ` then yields `Pf k ψ` on demand.) -/
theorem LegibleBot_playC_gives_box (k n : Nat) (X : Prog)
    (h : play n (LegibleBot (2*k+64) k) X = some .C) :
    Pf (2*k+64) (.box k (.plays (LegibleBot (2*k+64) k) X .C)) := by
  cases n with
  | zero => simp [play, eval] at h
  | succ n' =>
    cases hg : proofSearch (2*k+64)
        ((Formula.box k (.plays .self .opp Action.C)).subst (LegibleBot (2*k+64) k) X) with
    | true =>
        have := (proofSearch_spec _ _).1 hg
        simpa [Formula.subst, Prog.subst] using this
    | false =>
        exfalso
        have h'' : (if proofSearch (2*k+64)
              ((Formula.box k (.plays .self .opp Action.C)).subst (LegibleBot (2*k+64) k) X)
            then eval n' (LegibleBot (2*k+64) k) X (.const Action.C)
            else eval n' (LegibleBot (2*k+64) k) X (.const Action.D)) = some Action.C := h
        rw [hg] at h''
        cases n' with
        | zero => simp [eval] at h''
        | succ m => simp [eval] at h''

/-- **The DIMCID census**: no ≤`k` proof concludes any formula tailed at
    "LegibleBot (2k+64) k plays D vs DIMCID k". The D-play is LegibleBot's
    ELSE-play, so its only atom certificate is `search_f` at the `2k+64 > k`
    floor; every source-transparency rule is killed ACTION-refined (the set
    kernel, `CIMCIC/vs_DIMCID.lean` pattern — LegibleBot is a both-const
    searcher exactly like CIMCIC, so the singleton wrapper does not apply). -/
theorem ld_no_provable_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (LegibleBot (2*k+64) k) (DIMCID k) Action.D) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k
    (· = .plays (LegibleBot (2*k+64) k) (DIMCID k) Action.D)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · -- atom killer: D is the else-branch; search_t's branch mismatches, search_f floors
    rintro K' hK' φ' rfl hA
    cases hA with
    | mk hpp hn =>
      unfold LegibleBot at hpp
      cases hpp with
      | search_t hg hbr => cases hbr
      | search_f hneg hbr => simp only [c_node] at hn; omega
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold LegibleBot at hme; simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by decide)
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [LegibleBot] at hme
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [LegibleBot] at hme
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; simp [LegibleBot] at hme
  · rintro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3; simp [LegibleBot] at h1
  · rintro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold LegibleBot at hme; simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by simp)
  · rintro me oppo c hS L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases L with
    | nil => simp [searchPlug, LegibleBot] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        simp only [searchPlug, LegibleBot, Prog.search.injEq] at hme
        cases tl with
        | nil => simp [searchPlug] at hme
        | cons hd2 tl2 => obtain ⟨g2, ψ2, e2⟩ := hd2; simp [searchPlug] at hme
  · rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases hd with
    | searchL g ψ e =>
        simp only [ctxPlug, LegibleBot, Prog.search.injEq] at hme
        obtain ⟨rfl, rfl, hplug, rfl⟩ := hme
        cases L with
        | nil => simp [ctxPlug] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [ctxPlug] at hplug
    | iteL z aT other => simp [ctxPlug, LegibleBot] at hme
  · rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    exfalso
    cases hd with
    | thenL g ψ e =>
        simp only [plug2, LegibleBot, Prog.search.injEq] at hme
        obtain ⟨-, -, hplug, -⟩ := hme
        cases L with
        | nil => simp [plug2] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [plug2] at hplug
    | elseL g P' Q' c' q =>
        simp only [plug2, LegibleBot, Prog.search.injEq] at hme
        exact absurd hme.2.1 (by simp)

/-- DIMCID's substituted guard against LegibleBot is unprovable at DIMCID's own
    budget: its spine tail is the census-blocked D-play, and its antecedent is a
    different atom. -/
theorem ld_dimcid_guard_not_provable (k : Nat) :
    ¬ Pf k (.impl (.plays (DIMCID k) (LegibleBot (2*k+64) k) Action.C)
                  (.plays (LegibleBot (2*k+64) k) (DIMCID k) Action.D)) := by
  intro h
  refine ld_no_provable_tail k k _ h le_rfl ?_
  refine ⟨rfl, ?_⟩
  intro hA
  simp only [TailTo] at hA
  exact absurd hA (by simp [LegibleBot, DIMCID])

/-- DIMCID's guard search fails against LegibleBot (soundness of `proofSearch`
    + the census). -/
theorem proofSearch_false_dimcid_vs_legible (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (LegibleBot (2*k+64) k)) = false := by
  cases hps : proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (LegibleBot (2*k+64) k)) with
  | false => rfl
  | true =>
      exact absurd ((proofSearch_spec k _).1 hps) (ld_dimcid_guard_not_provable k)

/-- DIMCID falls through to its cooperate branch against the staggered
    LegibleBot — at EVERY `k` (the census needs no eventuality). -/
theorem DIMCID_plays_C_against_LegibleBot (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) (LegibleBot (2*k+64) k) = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) (LegibleBot (2*k+64) k))
          then eval (fuel + 1) (DIMCID k) (LegibleBot (2*k+64) k) (.const Action.D)
          else eval (fuel + 1) (DIMCID k) (LegibleBot (2*k+64) k) (.const Action.C))
        = some Action.C
  rw [proofSearch_false_dimcid_vs_legible k]; simp [eval]

end PD.Theorems
