import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.DupocBot
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

-- Dupoc --

/-!
# PrudentBot vs DupocBot → (C, C)

This matchup is a **search-vs-search modal fixed point with no unboxed `.sim`
leg**: PrudentBot reads "DupocBot cooperates with me" (`searchThenSearch_t`,
boxed) and DupocBot reads "PrudentBot cooperates with me" (`searchBranch`, boxed).
Both transparency legs are *boxed*:

* leg1 (`searchThenSearch_t` on PrudentBot, prudence atom discharged):
  `□_k (DupocBot plays C vs PrudentBot) → (PrudentBot plays C vs DupocBot)`;
* leg2 (`searchBranch` on DupocBot):
  `□_k (PrudentBot plays C vs DupocBot) → (DupocBot plays C vs PrudentBot)`.

For the MirrorBot/TFT matchups one leg is an *unboxed* `.sim` (`simStep`), and
`searchBranch` + `simStep` chain directly into the closed `□_k φ → φ` that `PBLT`
consumes. Here neither leg is a `.sim`, so that route is unavailable: composing two
*boxed* implications into `□_k φ → φ` needs to strip a box, which the source-
transparency rules cannot do.

**The closing ingredient is object-form Σ₁-completeness for play-atoms**,
`⊢ (p plays a vs q) → □_k (p plays a vs q)` — the certificate-gated `Pf.atomBoxImpl`
constructor (ProofSystem.lean; the witness-free axiom form `atom_box_provable_impl`
was removed as unsound — its sound conditional content is `atom_box_provable_impl_sound`
in Base/Soundness).
A `.plays` atom is Σ₁, so "true ⟹ provable" is sound reflection (NOT the GL-excluded
general `φ → □φ`, which fails on Π₁ truths). Applied to the play-atom `φ_P`:
`atomBoxImpl ⊳ leg2` yields the *unboxed-antecedent* implication
`φ_P → φ_D` (stripping the box `searchBranch` needs), which composes with `leg1`
into `□_k φ_D → φ_D`. That is exactly the role `simStep` plays for the `.sim`
matchups, now recovered for genuine search-vs-search via Σ₁-reflection rather than
`.sim` source-transparency.

The cooperative leg is *also* independently true with no axioms at all
(`dupocShaped_self_loeb_interp` below), which is why selecting `(C, C)` — the
intended Critch fixed point — is sound: the cooperative equilibrium is consistent,
and GL-4 is what lets `S` *prove* it rather than merely admit its consistency.
-/

/-! ## The cooperative Löb premise is true (no axioms) -/

/-- **The cooperative Löb premise is true, for any Dupoc-shaped cooperator.**
    `A = .search k (.plays .opp .self c) (.const c) (.const d)` cooperates `c` iff it
    proves the opponent plays `c` with it; for any opponent `B`, the implication
    `□_k (A plays c vs B) → (A plays c vs B)` holds. Proved with no new axioms via
    `A`'s own `.search` inversion. (The `(C,C)` outcome below does not use this; it
    is recorded as the semantic justification that the cooperative equilibrium is
    consistent.) -/
theorem dupocShaped_self_loeb_interp
    (k : Nat) (c d : Action) (B : Prog)
    (A : Prog) (hA : A = .search k (.plays .opp .self c) (.const c) (.const d)) :
    (Formula.impl (.box k (Formula.plays A B c)) (Formula.plays A B c)).interp := by
  subst hA
  show (Formula.box k (Formula.plays _ B c)).interp → (Formula.plays _ B c).interp
  intro hbox
  have hps : proofSearch k (Formula.plays
      (.search k (.plays .opp .self c) (.const c) (.const d)) B c) = true :=
    (proofSearch_spec _ _).2 hbox
  obtain ⟨n, hplay⟩ := proofSearch_sound _ _ hps
  cases hg : proofSearch k (Formula.plays B
      (.search k (.plays .opp .self c) (.const c) (.const d)) c) with
  | true =>
    refine ⟨2, ?_⟩
    show eval 2 _ B _ = some c
    simp [eval, Prog.subst, Formula.subst, hg]
  | false =>
    have hD : play (n + 2)
        (.search k (.plays .opp .self c) (.const c) (.const d)) B = some d := by
      show eval (n + 2) _ B _ = some d
      simp [eval, Prog.subst, Formula.subst, hg]
    have hC : play (n + 2)
        (.search k (.plays .opp .self c) (.const c) (.const d)) B = some c := by
      unfold play at hplay ⊢; exact eval_mono_le hplay (n + 2) (by omega)
    rw [hC] at hD
    obtain rfl : c = d := by injection hD
    exact ⟨n, hplay⟩

/-! ## Supporting lemmas for the (C, C) outcome -/

abbrev φD (k : Nat) : Formula := Formula.plays (DupocBot k) (PrudentBot k) Action.C
abbrev φP (k : Nat) : Formula := Formula.plays (PrudentBot k) (DupocBot k) Action.C

/-- Prudence atom: DupocBot plays D vs `.bot DefectBot` (its cooperation search
    fails — `.bot DefectBot` never cooperates — so it defects). -/
theorem dupoc_plays_D_vs_bot_DB (k fuel : Nat) :
    play (fuel + 2) (DupocBot k) (.bot DefectBot) = some .D := by
  have hg : proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) = false := by
    cases h : proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) with
    | true  => exact absurd (proofSearch_sound _ _ h) (interp_bot_DefectBot_plays_C_false _)
    | false => rfl
  show eval (fuel + 2) (DupocBot k) (.bot DefectBot) (DupocBot k) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-! ### PrudentBot × DupocBot — RETIRED at same-`k` (2026-07-02, the false-guard repair).

The former `prudence_dupoc`/`prudent_dupoc_legPD`/`prudent_dupoc_legDP`/
`outcome_PrudentBot_vs_DupocBot` (mutual cooperation at ONE shared `k`) were artifacts of
the inconsistent axiom. Honestly: PrudentBot's prudence fact "DupocBot k defects vs
`.bot DefectBot`" is an ELSE-play of Dupoc's own search, so its certificate pays the
`search_f` floor `k` — PrudentBot's inner search at the SAME `k` can never afford it.
The Critch-faithful replacement is STAGGERED budgets — `PrudentBot j` vs `DupocBot k`
with `j ≥ k + O(log k)` (the prudence certificate = `Pf.atomNeg` refutation +
`search_f`, cost `k + log2 k + O(1)`), through the two-budget `mutual_pblt` wrapper —
planned as T3.2b (`DECIDABILITY_ROADMAP.md`). Notably this rediscovers why the original
MIRI PrudentBot checks prudence in a STRONGER system (PA+1): same-strength prudence is
self-referentially impossible. -/


-- PrudentBot --

/-! ### PrudentBot × DupocBot — RECOVERED with STAGGERED budgets (T3.2b, 2026-07-03).

`PrudentBot (2k+64)` vs `DupocBot k`: the bigger bot's inner search affords the partner's
`search_f` floor (Dupoc's else-play vs `.bot DefectBot` certifies at `k + log2 k + 15`),
and the mutual Löb chain runs through the two-budget `mutual_pblt_engine_staggered`.
Critch-faithful: prudence must live in a strictly larger budget than the bot it probes —
the bounded analogue of MIRI PrudentBot's PA+1 prudence. -/

/-- Dupoc's else-play vs `.bot DefectBot`, certified at the FLOOR: `search_f` over the
    `atomNeg` refutation of Dupoc's guard ("botDefect cooperates" — refuted by botDefect's
    actual bot∘const defection certificate). -/
theorem prudence_dupoc (k : Nat) :
    Pf (k + Nat.log2 k + 15) (.plays (DupocBot k) (.bot DefectBot) .D) := by
  have hneg : Pf (Nat.log2 k + 13)
      (.neg (.plays (.bot DefectBot) (DupocBot k) .C)) := by
    refine Pf.atomNeg (.bot DefectBot) (DupocBot k) .D .C 2
      ⟨PlaysProof.bot PlaysProof.const, by decide⟩ (by decide) ?_
    simp only [numCost, Formula.size, Prog.size, DefectBot, DupocBot]
    omega
  have hcert := atom_search_f_top k (Nat.log2 k + 13) (.plays .opp .self .C) .C .D
    (.bot DefectBot) hneg
  exact Pf.atom (atom_monotone _ _ _ (by omega) hcert)

/-- Leg 1 (staggered): `□_{2k+64} φD → φP` — `PrudentBot (2k+64)`'s stacked-search read;
    the inner prudence premise `prudence_dupoc` fits its literal (`k + log2 k + 15 ≤ 2k+64`),
    and the rule CITES the inner search (`c_guard`), keeping the leg's transcript O(log k). -/
theorem prudent_dupoc_legPD (k : Nat) :
    Pf (30 * Nat.log2 k + 700)
      (.impl (.box (2*k+64) (.plays (DupocBot k) (PrudentBot (2*k+64)) .C))
             (.plays (PrudentBot (2*k+64)) (DupocBot k) .C)) := by
  have hlk := log2_le_self k
  have hlg := log2_stagger_le k
  refine Pf.searchThenSearch_t (2*k+64) (2*k+64) (k + Nat.log2 k + 15)
    (.plays .opp .self .C) (.plays .opp (.bot DefectBot) .D)
    .C .D (.const .D) (PrudentBot (2*k+64)) (DupocBot k) rfl
    (by simpa [Formula.subst, Prog.subst] using prudence_dupoc k) (by omega) ?_
  simp only [numCost, Formula.subst, Prog.subst, Formula.size, Prog.size, DupocBot, PrudentBot,
    DefectBot, c_guard]
  omega

/-- Leg 2 (staggered): `□_k φP → φD` — `DupocBot k`'s `searchBranch` leaf. -/
theorem prudent_dupoc_legDP (k : Nat) :
    Pf (30 * Nat.log2 k + 700)
      (.impl (.box k (.plays (PrudentBot (2*k+64)) (DupocBot k) .C))
             (.plays (DupocBot k) (PrudentBot (2*k+64)) .C)) := by
  have hlg := log2_stagger_le k
  refine Pf.searchBranch k (.plays .opp .self .C) .C .D (DupocBot k) (PrudentBot (2*k+64)) rfl ?_
  simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot, PrudentBot, DefectBot]
  omega

/-- Dupoc's staggered-opponent play lemmas (generic in the opponent). -/
theorem dupoc_C_vs_any (k fuel : Nat) (q : Prog)
    (hk : proofSearch k (.plays q (DupocBot k) .C) = true) :
    play (fuel + 2) (DupocBot k) q = some .C := by
  show eval (fuel + 2) (DupocBot k) q (DupocBot k) = some .C
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

theorem dupoc_D_vs_any (k fuel : Nat) (q : Prog)
    (hk : proofSearch k (.plays q (DupocBot k) .C) = false) :
    play (fuel + 2) (DupocBot k) q = some .D := by
  show eval (fuel + 2) (DupocBot k) q (DupocBot k) = some .D
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

theorem ps_k_of_play_dupoc_any (k n : Nat) (q : Prog)
    (h : play n (DupocBot k) q = some .C) :
    proofSearch k (.plays q (DupocBot k) .C) = true := by
  cases hps : proofSearch k (.plays q (DupocBot k) .C) with
  | true  => rfl
  | false =>
    exfalso
    have hD : play (n + 2) (DupocBot k) q = some .D := dupoc_D_vs_any k n q hps
    have hC : play (n + 2) (DupocBot k) q = some .C := by
      unfold play at h ⊢; exact eval_mono_le h (n + 2) (by omega)
    rw [hC] at hD; cases hD

/-- **PrudentBot (2k+64) vs DupocBot k → (C, C)** for all large enough `k` — the
    staggered-budget recovery of the retired same-`k` theorem. -/
theorem outcome_PrudentBot_vs_DupocBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot (2*k+64)) (DupocBot k) = some (.C, .C) := by
  obtain ⟨KL, hKL⟩ := linear_log2_add_le 1 3
  have hsD : ∀ k, (Formula.plays (DupocBot k) (PrudentBot (2*k+64)) .C).size
      ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    have hlg := log2_stagger_le k
    simp only [numCost, Formula.size, Prog.size, PrudentBot, DupocBot, DefectBot]
    omega
  have hsP : ∀ k, (Formula.plays (PrudentBot (2*k+64)) (DupocBot k) .C).size
      ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    have hlg := log2_stagger_le k
    simp only [numCost, Formula.size, Prog.size, PrudentBot, DupocBot, DefectBot]
    omega
  have hpb : ∀ k, 30 * Nat.log2 k + 700 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := mutual_pblt_engine_staggered
    (fun k => Formula.plays (DupocBot k) (PrudentBot (2*k+64)) .C)
    (fun k => Formula.plays (PrudentBot (2*k+64)) (DupocBot k) .C)
    (fun k => 2*k+64)
    (fun k => 30 * Nat.log2 k + 700) (fun k => 30 * Nat.log2 k + 700) 0
    (fun k => by show k ≤ 2*k+64; omega) log2_stagger_le hsD hsP hpb hpb
    (fun k _ => prudent_dupoc_legPD k)
    (fun k _ => prudent_dupoc_legDP k)
  refine ⟨max k₂ KL, fun k hk => ?_⟩
  have hk2 : k > k₂ := lt_of_le_of_lt (le_max_left _ _) hk
  have hKLk : Nat.log2 k + 3 ≤ k := by
    have := hKL k (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk))
    omega
  obtain ⟨m, hm⟩ := hk₂ k hk2
  obtain ⟨n, hplayD⟩ := Pf_sound m _ hm
  -- Dupoc's guard fired (inversion from its actual cooperative play)
  have hpsP : proofSearch k (.plays (PrudentBot (2*k+64)) (DupocBot k) .C) = true :=
    ps_k_of_play_dupoc_any k n (PrudentBot (2*k+64)) hplayD
  -- Dupoc's play atom, certified through its fired search (search_t cites)
  have hpsD : proofSearch (2*k+64)
      (.plays (DupocBot k) (PrudentBot (2*k+64)) .C) = true := by
    refine (proofSearch_spec _ _).2 (Pf.atom
      (⟨PlaysProof.search_t ((proofSearch_spec _ _).1 hpsP) PlaysProof.const, ?_⟩ :
        AtomProvable (2*k+64) (.plays (DupocBot k) (PrudentBot (2*k+64)) .C)))
    show c_leaf + c_guard k + c_node ≤ 2*k+64
    have hlk := log2_le_self k
    simp only [numCost, c_leaf, c_guard, c_node]
    omega
  -- Prudent's inner prudence guard at its own (bigger) literal
  have hprud : proofSearch (2*k+64) (.plays (DupocBot k) (.bot DefectBot) .D) = true := by
    refine (proofSearch_spec _ _).2 (Pf_mono (prudence_dupoc k) ?_)
    have hlk := log2_le_self k
    omega
  refine ⟨4, ?_⟩
  have hA : play 4 (PrudentBot (2*k+64)) (DupocBot k) = some .C := by
    simpa using prudent_eval_both_true (2*k+64) 1 (DupocBot k) hpsD hprud
  have hB : play 4 (DupocBot k) (PrudentBot (2*k+64)) = some .C := by
    simpa using dupoc_C_vs_any k 2 (PrudentBot (2*k+64)) hpsP
  exact outcome_of_plays _ _ _ _ _ hA hB
end PD.Theorems
