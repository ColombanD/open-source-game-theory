import ArithS.Cells.DimcidFlips

/-!
# ArithS.Cells.FloorVerdicts — the floor verdict pass: the settled halves and the true guards of the
genuine floors

`Research/Notes/ROUTE_B_CENSUS.md` "S' status per cell". The engine closes 32 cells by a
floor CENSUS (a true guard that `S` cannot prove within the budget: `no_provable_tailToS_floor`,
`searcherElse`, `probeFirst`, `nested`, `searcherPlay`, `botSearcherElse`) and one (Prudent × EBot) by a
floor-paying Löb premise. `Cells/DimcidFlips` showed that seven of them are not floors in PA-`S'`
(DIMCID's guard is self-fulfilling and FOUND). This module records the verdict on the rest — every
remaining floor cell without an `S'` statement, OptimBot/LegibleBot and the four staggered companions
excluded — under the trichotomy of `ARITHMETIZED_S_RESULTS.md`:

* (F) the guard is FALSE in ℕ ⇒ never found, by soundness (an SND cell);
* (P) the guard is TRUE and PROVABLE within the budget ⇒ found (self-fulfilling Löb or positive);
* (G) the guard is TRUE and its only proofs are longer than the budget for a reason that is a genuine
  proof-length LOWER BOUND.

**The verdict: every one of the 24 worklist cells (and the two `cenU` cells CIMCIC × DBot/EBot) is (G) on
at least one side, and NONE is (F) or (P) as a cell.** The reason is uniform. In each of them the floor
guard is a TRUE Σ₁ sentence "X plays a against Y" whose only evaluation witness runs through the ELSE
branch of some search node — a node whose guard σ is FALSE in ℕ. The else clause of `EvalGraph` is
`¬ LenBox TAct k ⌜σ⌝`, a bounded universal statement, and a `TAct`-proof of it is, up to an additive
constant, a proof of the BOUNDED CONSISTENCY statement `Con_TAct(k + c)`: `TAct ⊢ ¬σ` cheaply (evaluator
determinism), so a proof of σ of length ≤ k yields a contradiction of length ≤ k + c, and conversely a
contradiction of length ≤ k − c yields a proof of σ by ex falso. Whether `TAct` proves `Con_TAct(k)` with a
proof of length ≤ k is a Pudlák-type question (lower bound `k^ε`, polynomial upper bound; the LINEAR case is
open) — a genuine lower-bound question, not a fact this development can settle either way. The engine's
`+k` floor (`search_f` pays the failed budget) is its stipulated answer. So these cells are the honest
residue of the "floors dropped" decision: `S'` does not claim them, and their engine values rest on the
reflection assumption stated in prose.

What IS unconditional, and proved here — the machine-checked shape of each residue:

1. **The settled halves** (`floor_<L>_vs_<R>_left`/`_right`): the play of the side whose value does NOT
   depend on the floor — a search-free opponent reacting to certified probes (DBot/EBot/OBot/CupodTroll
   against the searcher's soundness-forced else-plays and its positively found guards), or a searcher whose
   guard is FALSE by such a probe (Guardian against CIMCIC/Dupoc/Just: their cooperation with
   `.bot CooperateBot` is a found positive guard, so Guardian's guard is false). Each at the engine's fuel,
   at every `k` or for all large `k`.
2. **The true guards** (`floor_<L>_vs_<R>_true`): the floor side's consulted sentence `sentenceAt me opp φ` IS true
   in ℕ — the "TRUE" clause of the (G) verdict, machine-checked; the residue is exactly its provability within
   `k`. For the two-searcher bistable cells (Wary × Dupoc/Just/Prudent, Cupod × Prudent both ways, Just × Cupod,
   CIMCIC × Cupod) no side is settled — each guard's truth depends on the other's found-ness — so they get a
   verdict and nothing else; for the four PRUDENCE floors (Prudent × Dupoc/Prudent, Just × Prudent,
   CIMCIC × Prudent) the floor is the inner guard "opp defects against `.bot DefectBot`", true at every `k`
   because the opponent's guard against that probe is false — recorded as `_true`.
3. **Prudent × EBot** (LOEB-FP): EBot's cooperation rests on Prudent's Löb cooperation with `.bot MirrorBot`
   (the `Cells/PrudentMirror` family re-instantiated at the closed code `pBot Mirror` via `describes_closed`) —
   not built here; Prudent's side is (G) (EBot's first rung needs Prudent's else-play against `.bot DefectBot`).

Naming: the method prefix `floor` (added to the scheme of `Cells/Names.lean`) marks the residue of a genuine
floor cell; `L`/`R` are the engine constructors (every statement is on `progCode (X k)`); suffixes `_left`/`_right`
= the settled play of that player, `_true` = the floor guard's truth in ℕ. New sub-plays: `pos_DupocBot_vs_botCB`,
`pos_botDupocBot_vs_botCB` (the `k̂`-chain lemmas of `Cells/KhatCells` at ℕ), `snd_JustBot_vs_botDB`; the code
inequalities `progCode_DupocBot/JustBot/CIMCIC_ne_CupodBot` (CupodTroll's `.eq` guard is false against them).

Conventions: every threshold EXISTENTIAL; `simp` never sees a closed quote; statements pin the fuel to the
engine's pad (`EvalGraph.mono_le` lifts); no `sorry`, no `axiom`, no `native_decide`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open PD.Bots

/-! ### 1. Code inequalities: CupodTroll's `.eq` guard against the searchers -/

section codes

lemma pConst_zero_ne_one : pConst (0 : ℕ) ≠ pConst 1 := fun h ↦ absurd (pConst_inj h) (by decide)

lemma progCode_DupocBot_ne_CupodBot (k : ℕ) : progCode (DupocBot k) ≠ progCode (CupodBot k) := by
  rw [progCode_DupocBot_search, progCode_CupodBot]
  intro e
  exact pConst_zero_ne_one (pSearch_inj e).2.2.1

lemma progCode_JustBot_ne_CupodBot (k : ℕ) : progCode (JustBot k) ≠ progCode (CupodBot k) := by
  rw [progCode_JustBot, progCode_CupodBot]
  intro e
  exact pConst_zero_ne_one (pSearch_inj e).2.2.1

lemma progCode_CIMCIC_ne_CupodBot (k : ℕ) : progCode (CIMCIC k) ≠ progCode (CupodBot k) := by
  rw [progCode_CIMCIC_search, progCode_CupodBot]
  intro e
  exact pConst_zero_ne_one (pSearch_inj e).2.2.1

lemma progCode_botDupocBot_ne_CupodBot (k : ℕ) : progCode (PD.Prog.bot (DupocBot k)) ≠ progCode (CupodBot k) := by
  rw [progCode_bot, progCode_CupodBot]
  exact pBot_ne_pSearch _ _ _ _ _

end codes

/-! ### 2. Sub-plays: the searchers against the frozen probes -/

section subplays

/-- Dupoc cooperates with `.bot CooperateBot` for all large `k` (its guard is a true closed atom, found:
`dupoc_botCB_V` at ℕ). -/
theorem pos_DupocBot_vs_botCB :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (progCode (DupocBot k)) (pBot (pConst 0)) (progCode (DupocBot k)) 0 := by
  obtain ⟨kHat, h⟩ := dupoc_botCB_V
  refine ⟨kHat, fun k hk ↦ ?_⟩
  have hp := h ℕ k (le_def.mpr (Or.inr (by rw [natCast_nat]; omega)))
  rwa [← progCode_DupocBot_SV] at hp

/-- The frozen snapshot `.bot (DupocBot k)` cooperates with `.bot CooperateBot` for all large `k`
(`botDupoc_botCB_V` at ℕ). -/
theorem pos_botDupocBot_vs_botCB :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 3 (pBot (progCode (DupocBot k))) (pBot (pConst 0)) (pBot (progCode (DupocBot k))) 0 := by
  obtain ⟨kHat, h⟩ := botDupoc_botCB_V
  refine ⟨kHat, fun k hk ↦ ?_⟩
  have hp := h ℕ k (le_def.mpr (Or.inr (by rw [natCast_nat]; omega)))
  rwa [← progCode_DupocBot_SV] at hp

/-- Just defects against `.bot DefectBot` at every `k` (its guard "`.bot DefectBot` plays C against the
snapshot" is false). -/
theorem snd_JustBot_vs_botDB (k : ℕ) :
    EvalGraph 2 (progCode (JustBot k)) (pBot (pConst 1)) (progCode (JustBot k)) 1 := by
  have := just_D_of_probe k (opp := .bot DefectBot) properPlayer_botDB (N := 2)
    (by rw [progCode_botDB]; exact bot_const_play 0 _ _ _)
  rwa [progCode_botDB] at this

end subplays

/-! ### 3. DupocBot's floor cells: `× DBot`, `× EBot`, `× CupodTrollBot` (engine `(D, C)`, `(D, C)`, `(D, C)`) -/

section dupoc

/-- **DBot cooperates with `DupocBot k` at every `k`** (the settled half of `outcome_DupocBot_vs_DBot`, engine
`(D, C)` by the floor `no_provable_DBot_C_tail`): Dupoc defects against `.bot DefectBot` (guard false), so DBot
does not punish it. -/
theorem floor_DupocBot_vs_DBot_right (k : ℕ) :
    EvalGraph 4 (progCode DBot) (progCode (DupocBot k)) (progCode DBot) (actCode .C) :=
  dbot_C_of_probe_D (snd_DupocBot_vs_botDB k)

/-- **Dupoc's guard against DBot is TRUE in ℕ** at every `k`: the residue of the cell is its provability within
`k`, i.e. a proof of DBot's run, which passes through Dupoc's else-branch against `.bot DefectBot`
(`¬ LenBox TAct k ⌜botDB plays C against Dupoc k⌝`, a bounded-consistency statement). -/
theorem floor_DupocBot_vs_DBot_true (k : ℕ) : ℕ↓[LAct] ⊧ sentenceAt (DupocBot k) DBot phiDu := by
  rw [← sentenceAt_subst (DupocBot k) DBot (properPlayer_DupocBot k) sfp_DBot.1 phiDu rfl]
  show ℕ↓[LAct] ⊧ sentenceAt (DupocBot k) DBot (.plays DBot (DupocBot k) .C)
  rw [models_sentenceAt_plays _ _ _ _ _ sfp_DBot.1 (properPlayer_DupocBot k)]
  exact ⟨4, floor_DupocBot_vs_DBot_right k⟩

/-- **EBot cooperates with `DupocBot k` for all large `k`** (the settled half of `outcome_DupocBot_vs_EBot`,
engine `(D, C)` by the floor `no_provable_EBot_C_tail`): Dupoc defects against `.bot DefectBot` (guard false)
and cooperates with `.bot CooperateBot` (guard found). -/
theorem floor_DupocBot_vs_EBot_right :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 5 (progCode EBot) (progCode (DupocBot k)) (progCode EBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := pos_DupocBot_vs_botCB
  exact ⟨k₀, fun k hk ↦ ebot_C_of_probes (snd_DupocBot_vs_botDB k) (h k hk)⟩

/-- **Dupoc's guard against EBot is TRUE in ℕ** for all large `k` (residue: EBot's run through Dupoc's
else-branch against `.bot DefectBot`). -/
theorem floor_DupocBot_vs_EBot_true :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ℕ↓[LAct] ⊧ sentenceAt (DupocBot k) EBot phiDu := by
  obtain ⟨k₀, h⟩ := floor_DupocBot_vs_EBot_right
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [← sentenceAt_subst (DupocBot k) EBot (properPlayer_DupocBot k) sfp_EBot.1 phiDu rfl]
  show ℕ↓[LAct] ⊧ sentenceAt (DupocBot k) EBot (.plays EBot (DupocBot k) .C)
  rw [models_sentenceAt_plays _ _ _ _ _ sfp_EBot.1 (properPlayer_DupocBot k)]
  exact ⟨5, h k hk⟩

/-- **CupodTroll cooperates with `DupocBot k` at every `k`** (the settled half of
`outcome_DupocBot_vs_CupodTrollBot`, engine `(D, C)` by the floor `no_provable_searcherElse_tail`): its `.eq`
guard is false. -/
theorem floor_DupocBot_vs_CupodTrollBot_right (k : ℕ) :
    EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (DupocBot k)) (progCode (CupodTrollBot k)) (actCode .C) :=
  ctb_C_of_ne k (properPlayer_DupocBot k) (progCode_DupocBot_ne_CupodBot k)

/-- **Dupoc's guard against CupodTroll is TRUE in ℕ** at every `k` (residue: CupodTroll's run through its
else-branch, `¬ LenBox TAct k ⌜Dupoc k is CupodBot k⌝`, a false closed equation). -/
theorem floor_DupocBot_vs_CupodTrollBot_true (k : ℕ) :
    ℕ↓[LAct] ⊧ sentenceAt (DupocBot k) (CupodTrollBot k) phiDu := by
  rw [← sentenceAt_subst (DupocBot k) (CupodTrollBot k) (properPlayer_DupocBot k) (properPlayer_CupodTrollBot k) phiDu rfl]
  show ℕ↓[LAct] ⊧ sentenceAt (DupocBot k) (CupodTrollBot k) (.plays (CupodTrollBot k) (DupocBot k) .C)
  rw [models_sentenceAt_plays _ _ _ _ _ (properPlayer_CupodTrollBot k) (properPlayer_DupocBot k)]
  exact ⟨2, floor_DupocBot_vs_CupodTrollBot_right k⟩

end dupoc

/-! ### 4. JustBot's floor cells: `× DBot`, `× EBot`, `× CupodTrollBot` (engine `(D, C)` ×3) -/

section just

/-- **DBot cooperates with `JustBot k` at every `k`** (the settled half of `outcome_JustBot_vs_DBot`, engine
`(D, C)` by the floor `probeFirst_tail_botOpp`): Just defects against `.bot DefectBot`. -/
theorem floor_JustBot_vs_DBot_right (k : ℕ) :
    EvalGraph 4 (progCode DBot) (progCode (JustBot k)) (progCode DBot) (actCode .C) :=
  dbot_C_of_probe_D (snd_JustBot_vs_botDB k)

/-- **Just's guard against DBot is TRUE in ℕ** at every `k`: DBot cooperates with the snapshot
`.bot (DupocBot k)`, which defects against `.bot DefectBot` (residue: that else-branch). -/
theorem floor_JustBot_vs_DBot_true (k : ℕ) : ℕ↓[LAct] ⊧ sentenceAt (JustBot k) DBot (phiJ k) := by
  rw [← sentenceAt_subst (JustBot k) DBot (properPlayer_JustBot k) sfp_DBot.1 (phiJ k) rfl]
  show ℕ↓[LAct] ⊧ sentenceAt (JustBot k) DBot (.plays DBot (.bot (DupocBot k)) .C)
  rw [models_sentenceAt_plays _ _ _ _ _ sfp_DBot.1 (properPlayer_bot _), progCode_bot]
  exact ⟨5, dbot_C_of_probe_D (snd_botDupocBot_vs_botDB k)⟩

/-- **EBot cooperates with `JustBot k` for all large `k`** (the settled half of `outcome_JustBot_vs_EBot`,
engine `(D, C)` by the floor `probeFirst_tail_botOpp`): Just defects against `.bot DefectBot` and cooperates
with `.bot CooperateBot` (found). -/
theorem floor_JustBot_vs_EBot_right :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 5 (progCode EBot) (progCode (JustBot k)) (progCode EBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := pos_JustBot_vs_botCB
  exact ⟨k₀, fun k hk ↦ ebot_C_of_probes (snd_JustBot_vs_botDB k) (h k hk)⟩

/-- **Just's guard against EBot is TRUE in ℕ** for all large `k`: EBot cooperates with the snapshot
`.bot (DupocBot k)` (defects against `.bot DefectBot`, cooperates with `.bot CooperateBot`). -/
theorem floor_JustBot_vs_EBot_true :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ℕ↓[LAct] ⊧ sentenceAt (JustBot k) EBot (phiJ k) := by
  obtain ⟨k₀, h⟩ := pos_botDupocBot_vs_botCB
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [← sentenceAt_subst (JustBot k) EBot (properPlayer_JustBot k) sfp_EBot.1 (phiJ k) rfl]
  show ℕ↓[LAct] ⊧ sentenceAt (JustBot k) EBot (.plays EBot (.bot (DupocBot k)) .C)
  rw [models_sentenceAt_plays _ _ _ _ _ sfp_EBot.1 (properPlayer_bot _), progCode_bot]
  exact ⟨6, ebot_C_of_probes (snd_botDupocBot_vs_botDB k) (h k hk)⟩

/-- **CupodTroll cooperates with `JustBot k` at every `k`** (the settled half of
`outcome_JustBot_vs_CupodTrollBot`, engine `(D, C)` by the floor `no_provable_searcherElse_tail`). -/
theorem floor_JustBot_vs_CupodTrollBot_right (k : ℕ) :
    EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (JustBot k)) (progCode (CupodTrollBot k)) (actCode .C) :=
  ctb_C_of_ne k (properPlayer_JustBot k) (progCode_JustBot_ne_CupodBot k)

/-- **Just's guard against CupodTroll is TRUE in ℕ** at every `k`: CupodTroll cooperates with the snapshot
(its `.eq` guard is false there too). -/
theorem floor_JustBot_vs_CupodTrollBot_true (k : ℕ) :
    ℕ↓[LAct] ⊧ sentenceAt (JustBot k) (CupodTrollBot k) (phiJ k) := by
  rw [← sentenceAt_subst (JustBot k) (CupodTrollBot k) (properPlayer_JustBot k) (properPlayer_CupodTrollBot k) (phiJ k) rfl]
  show ℕ↓[LAct] ⊧ sentenceAt (JustBot k) (CupodTrollBot k) (.plays (CupodTrollBot k) (.bot (DupocBot k)) .C)
  rw [models_sentenceAt_plays _ _ _ _ _ (properPlayer_CupodTrollBot k) (properPlayer_bot _)]
  exact ⟨2, ctb_C_of_ne k (properPlayer_bot _) (progCode_botDupocBot_ne_CupodBot k)⟩

end just

/-! ### 5. CIMCIC's floor cells: `× CupodTrollBot`, `× DBot`, `× EBot` (engine `(D, C)` ×3) -/

section cimcic

/-- **CupodTroll cooperates with `CIMCIC k` at every `k`** (the settled half of
`llm_outcome_CIMCIC_vs_CupodTrollBot`, engine `(D, C)` by the floor `cimcic_ctb_guard_unprovable_tail`). -/
theorem floor_CIMCIC_vs_CupodTrollBot_right (k : ℕ) :
    EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (CIMCIC k)) (progCode (CupodTrollBot k)) (actCode .C) :=
  ctb_C_of_ne k (properPlayer_CIMCIC k) (progCode_CIMCIC_ne_CupodBot k)

/-- **CIMCIC's guard against CupodTroll is TRUE in ℕ** at every `k` (its consequent "CupodTroll plays C
against me" holds; residue: CupodTroll's else-branch). -/
theorem floor_CIMCIC_vs_CupodTrollBot_true (k : ℕ) :
    ℕ↓[LAct] ⊧ sentenceAt (CIMCIC k) (CupodTrollBot k) phiC := by
  rw [← sentenceAt_subst (CIMCIC k) (CupodTrollBot k) (properPlayer_CIMCIC k) (properPlayer_CupodTrollBot k) phiC rfl]
  change ℕ↓[LAct] ⊧ sentenceAt (CIMCIC k) (CupodTrollBot k)
    (.impl (.plays (CIMCIC k) (CupodTrollBot k) .C) (.plays (CupodTrollBot k) (CIMCIC k) .C))
  rw [models_sentenceAt_impl, models_sentenceAt_plays _ _ _ _ _ (properPlayer_CupodTrollBot k) (properPlayer_CIMCIC k)]
  exact fun _ ↦ ⟨2, floor_CIMCIC_vs_CupodTrollBot_right k⟩

/-- **DBot cooperates with `CIMCIC k` at every `k`** (the settled half of `llm_outcome_CIMCIC_vs_DBot`, engine
`(D, C)` by the unreadability census): CIMCIC's guard against `.bot DefectBot` is self-refuting, so it defects
there. -/
theorem floor_CIMCIC_vs_DBot_right (k : ℕ) :
    EvalGraph 4 (progCode DBot) (progCode (CIMCIC k)) (progCode DBot) (actCode .C) :=
  dbot_C_of_probe_D (snd_CIMCIC_vs_botDB k)

/-- **CIMCIC's guard against DBot is TRUE in ℕ** at every `k` (residue: DBot's run through CIMCIC's
else-branch against `.bot DefectBot` — the self-refuting guard's non-provability, a bounded-consistency
statement). -/
theorem floor_CIMCIC_vs_DBot_true (k : ℕ) : ℕ↓[LAct] ⊧ sentenceAt (CIMCIC k) DBot phiC := by
  rw [← sentenceAt_subst (CIMCIC k) DBot (properPlayer_CIMCIC k) sfp_DBot.1 phiC rfl]
  change ℕ↓[LAct] ⊧ sentenceAt (CIMCIC k) DBot (.impl (.plays (CIMCIC k) DBot .C) (.plays DBot (CIMCIC k) .C))
  rw [models_sentenceAt_impl, models_sentenceAt_plays _ _ _ _ _ sfp_DBot.1 (properPlayer_CIMCIC k)]
  exact fun _ ↦ ⟨4, floor_CIMCIC_vs_DBot_right k⟩

/-- **EBot cooperates with `CIMCIC k` for all large `k`** (the settled half of `llm_outcome_CIMCIC_vs_EBot`,
engine `(D, C)`): CIMCIC defects against `.bot DefectBot` (self-refuting guard) and cooperates with
`.bot CooperateBot` (found). -/
theorem floor_CIMCIC_vs_EBot_right :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 5 (progCode EBot) (progCode (CIMCIC k)) (progCode EBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := pos_CIMCIC_vs_botCB
  exact ⟨k₀, fun k hk ↦ ebot_C_of_probes (snd_CIMCIC_vs_botDB k) (h k hk)⟩

/-- **CIMCIC's guard against EBot is TRUE in ℕ** for all large `k`. -/
theorem floor_CIMCIC_vs_EBot_true :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ℕ↓[LAct] ⊧ sentenceAt (CIMCIC k) EBot phiC := by
  obtain ⟨k₀, h⟩ := floor_CIMCIC_vs_EBot_right
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [← sentenceAt_subst (CIMCIC k) EBot (properPlayer_CIMCIC k) sfp_EBot.1 phiC rfl]
  change ℕ↓[LAct] ⊧ sentenceAt (CIMCIC k) EBot (.impl (.plays (CIMCIC k) EBot .C) (.plays EBot (CIMCIC k) .C))
  rw [models_sentenceAt_impl, models_sentenceAt_plays _ _ _ _ _ sfp_EBot.1 (properPlayer_CIMCIC k)]
  exact fun _ ↦ ⟨5, h k hk⟩

end cimcic

/-! ### 6. GuardianBot's floor cells: `× CIMCIC`, `× DupocBot`, `× JustBot`, `× PrudentBot` (engine `(C, D)` ×4) -/

section guardian

/-- **Guardian cooperates with `CIMCIC k` for all large `k`** (the settled half of
`llm_outcome_GuardianBot_vs_CIMCIC`, engine `(C, D)` by the floor `gc_no_provable_tail`): CIMCIC cooperates
with `.bot CooperateBot` (guard found), so Guardian's guard is FALSE — an SND side. -/
theorem floor_GuardianBot_vs_CIMCIC_left :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (GuardianBot k)) (progCode (CIMCIC k)) (progCode (GuardianBot k)) (actCode .C) := by
  obtain ⟨k₀, h⟩ := pos_CIMCIC_vs_botCB
  exact ⟨k₀, fun k hk ↦ guardian_C_of_probe k (properPlayer_CIMCIC k) (h k hk)⟩

/-- **CIMCIC's guard against Guardian is TRUE in ℕ** for all large `k` (residue: Guardian's run through its
else-branch). -/
theorem floor_GuardianBot_vs_CIMCIC_true :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ℕ↓[LAct] ⊧ sentenceAt (CIMCIC k) (GuardianBot k) phiC := by
  obtain ⟨k₀, h⟩ := floor_GuardianBot_vs_CIMCIC_left
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [← sentenceAt_subst (CIMCIC k) (GuardianBot k) (properPlayer_CIMCIC k) (properPlayer_GuardianBot k) phiC rfl]
  change ℕ↓[LAct] ⊧ sentenceAt (CIMCIC k) (GuardianBot k)
    (.impl (.plays (CIMCIC k) (GuardianBot k) .C) (.plays (GuardianBot k) (CIMCIC k) .C))
  rw [models_sentenceAt_impl, models_sentenceAt_plays _ _ _ _ _ (properPlayer_GuardianBot k) (properPlayer_CIMCIC k)]
  exact fun _ ↦ ⟨2, h k hk⟩

/-- **Guardian cooperates with `DupocBot k` for all large `k`** (the settled half of
`llm_outcome_GuardianBot_vs_DupocBot`, engine `(C, D)` by the floor `gd_no_provable_C_tail`): Dupoc cooperates
with `.bot CooperateBot` (found), so Guardian's guard is FALSE. -/
theorem floor_GuardianBot_vs_DupocBot_left :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (GuardianBot k)) (progCode (DupocBot k)) (progCode (GuardianBot k)) (actCode .C) := by
  obtain ⟨k₀, h⟩ := pos_DupocBot_vs_botCB
  exact ⟨k₀, fun k hk ↦ guardian_C_of_probe k (properPlayer_DupocBot k) (h k hk)⟩

/-- **Dupoc's guard against Guardian is TRUE in ℕ** for all large `k`. -/
theorem floor_GuardianBot_vs_DupocBot_true :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ℕ↓[LAct] ⊧ sentenceAt (DupocBot k) (GuardianBot k) phiDu := by
  obtain ⟨k₀, h⟩ := floor_GuardianBot_vs_DupocBot_left
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [← sentenceAt_subst (DupocBot k) (GuardianBot k) (properPlayer_DupocBot k) (properPlayer_GuardianBot k) phiDu rfl]
  show ℕ↓[LAct] ⊧ sentenceAt (DupocBot k) (GuardianBot k) (.plays (GuardianBot k) (DupocBot k) .C)
  rw [models_sentenceAt_plays _ _ _ _ _ (properPlayer_GuardianBot k) (properPlayer_DupocBot k)]
  exact ⟨2, h k hk⟩

/-- **Guardian cooperates with `JustBot k` for all large `k`** (the settled half of
`llm_outcome_GuardianBot_vs_JustBot`, engine `(C, D)` by the floor `gjb_no_provable_Guardian_C_vs_botDupoc`):
Just cooperates with `.bot CooperateBot` (found), so Guardian's guard is FALSE. -/
theorem floor_GuardianBot_vs_JustBot_left :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (GuardianBot k)) (progCode (JustBot k)) (progCode (GuardianBot k)) (actCode .C) := by
  obtain ⟨k₀, h⟩ := pos_JustBot_vs_botCB
  exact ⟨k₀, fun k hk ↦ guardian_C_of_probe k (properPlayer_JustBot k) (h k hk)⟩

/-- **Just's guard against Guardian is TRUE in ℕ** for all large `k`: Guardian cooperates with the snapshot
`.bot (DupocBot k)` (which cooperates with `.bot CooperateBot`, found). -/
theorem floor_GuardianBot_vs_JustBot_true :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ℕ↓[LAct] ⊧ sentenceAt (JustBot k) (GuardianBot k) (phiJ k) := by
  obtain ⟨k₀, h⟩ := pos_botDupocBot_vs_botCB
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [← sentenceAt_subst (JustBot k) (GuardianBot k) (properPlayer_JustBot k) (properPlayer_GuardianBot k) (phiJ k) rfl]
  show ℕ↓[LAct] ⊧ sentenceAt (JustBot k) (GuardianBot k) (.plays (GuardianBot k) (.bot (DupocBot k)) .C)
  rw [models_sentenceAt_plays _ _ _ _ _ (properPlayer_GuardianBot k) (properPlayer_bot _)]
  refine ⟨2, guardian_C_of_probe k (properPlayer_bot _) (N := 3) ?_⟩
  rw [progCode_bot]
  exact h k hk

/-- **Guardian's guard against Prudent is TRUE in ℕ** at every `k` (`llm_outcome_GuardianBot_vs_PrudentBot`,
engine `(C, D)` by the floors `gvp_no_Pf_prudent_D`/`pvg_no_Pf_guardian_C`): Prudent defects against
`.bot CooperateBot` because its prudence guard is false there — an else-play, so the guard is a floor on
Guardian's side; Prudent's outer guard is a floor on the other (Guardian's else-play), its prudence guard is
positive (Guardian defects against `.bot DefectBot`, found). -/
theorem floor_GuardianBot_vs_PrudentBot_true (k : ℕ) :
    ℕ↓[LAct] ⊧ sentenceAt (GuardianBot k) (PrudentBot k) phiG := by
  rw [← sentenceAt_subst (GuardianBot k) (PrudentBot k) (properPlayer_GuardianBot k) (properPlayer_PrudentBot k) phiG rfl]
  show ℕ↓[LAct] ⊧ sentenceAt (GuardianBot k) (PrudentBot k) (.plays (PrudentBot k) (.bot CooperateBot) .D)
  rw [models_sentenceAt_plays _ _ _ _ _ (properPlayer_PrudentBot k) properPlayer_botCB, progCode_botCB]
  exact ⟨3, snd_PrudentBot_vs_botCB k⟩

end guardian

/-! ### 7. CupodBot × OBot (engine `(C, D)`) -/

section cupod

/-- **OBot defects against `CupodBot k` for all large `k`** (the settled half of `outcome_CupodBot_vs_OBot`,
engine `(C, D)` by the floor `no_provable_OBot_D_tail`): Cupod cooperates with `.bot CooperateBot` (guard
false) but defects against `.bot DefectBot` (guard found) — the opportunist OBot detects. -/
theorem floor_CupodBot_vs_OBot_right :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 5 (progCode OBot) (progCode (CupodBot k)) (progCode OBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := pos_CupodBot_vs_botDB
  exact ⟨k₀, fun k hk ↦ obot_D_of_probes (snd_CupodBot_vs_botCB k) (h k hk)⟩

/-- **Cupod's guard against OBot is TRUE in ℕ** for all large `k` (residue: OBot's run through Cupod's
else-branch against `.bot CooperateBot`). -/
theorem floor_CupodBot_vs_OBot_true :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ℕ↓[LAct] ⊧ sentenceAt (CupodBot k) OBot phiCu := by
  obtain ⟨k₀, h⟩ := floor_CupodBot_vs_OBot_right
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [← sentenceAt_subst (CupodBot k) OBot (properPlayer_CupodBot k) sfp_OBot.1 phiCu rfl]
  show ℕ↓[LAct] ⊧ sentenceAt (CupodBot k) OBot (.plays OBot (CupodBot k) .D)
  rw [models_sentenceAt_plays _ _ _ _ _ sfp_OBot.1 (properPlayer_CupodBot k)]
  exact ⟨5, h k hk⟩

end cupod

/-! ### 8. The prudence floors: Prudent × DupocBot, Prudent × PrudentBot, JustBot × PrudentBot, CIMCIC × PrudentBot
(engine `(D, D)` ×4) — the inner guard "opp defects against `.bot DefectBot`" is TRUE at every `k`, by the
opponent's else-play against that probe -/

section prudence

/-- **Prudent's prudence guard against `DupocBot k` is TRUE in ℕ** at every `k` (`outcome_PrudentBot_vs_DupocBot`,
engine `(D, D)` by the floor `proofSearch_false_DupocBot_D_vs_bot_DefectBot`): Dupoc defects against
`.bot DefectBot` because its guard is false there. -/
theorem floor_PrudentBot_vs_DupocBot_true (k : ℕ) :
    ℕ↓[LAct] ⊧ sentenceAt (PrudentBot k) (DupocBot k) phiPi := by
  rw [← sentenceAt_subst (PrudentBot k) (DupocBot k) (properPlayer_PrudentBot k) (properPlayer_DupocBot k) phiPi rfl]
  show ℕ↓[LAct] ⊧ sentenceAt (PrudentBot k) (DupocBot k) (.plays (DupocBot k) (.bot DefectBot) .D)
  rw [models_sentenceAt_plays _ _ _ _ _ (properPlayer_DupocBot k) properPlayer_botDB, progCode_botDB]
  exact ⟨2, snd_DupocBot_vs_botDB k⟩

/-- **Prudent's prudence guard against `PrudentBot k` is TRUE in ℕ** at every `k`
(`outcome_PrudentBot_vs_PrudentBot`, engine `(D, D)` by the floor `no_provable_prudence_self_tail`). -/
theorem floor_PrudentBot_vs_PrudentBot_true (k : ℕ) :
    ℕ↓[LAct] ⊧ sentenceAt (PrudentBot k) (PrudentBot k) phiPi := by
  rw [← sentenceAt_subst (PrudentBot k) (PrudentBot k) (properPlayer_PrudentBot k) (properPlayer_PrudentBot k) phiPi rfl]
  show ℕ↓[LAct] ⊧ sentenceAt (PrudentBot k) (PrudentBot k) (.plays (PrudentBot k) (.bot DefectBot) .D)
  rw [models_sentenceAt_plays _ _ _ _ _ (properPlayer_PrudentBot k) properPlayer_botDB, progCode_botDB]
  exact ⟨2, snd_PrudentBot_vs_botDB k⟩

/-- **Prudent's prudence guard against `JustBot k` is TRUE in ℕ** at every `k` (`outcome_JustBot_vs_PrudentBot`,
engine `(D, D)` by the floor `no_provable_botSearcherElse_tail`). -/
theorem floor_JustBot_vs_PrudentBot_true (k : ℕ) :
    ℕ↓[LAct] ⊧ sentenceAt (PrudentBot k) (JustBot k) phiPi := by
  rw [← sentenceAt_subst (PrudentBot k) (JustBot k) (properPlayer_PrudentBot k) (properPlayer_JustBot k) phiPi rfl]
  show ℕ↓[LAct] ⊧ sentenceAt (PrudentBot k) (JustBot k) (.plays (JustBot k) (.bot DefectBot) .D)
  rw [models_sentenceAt_plays _ _ _ _ _ (properPlayer_JustBot k) properPlayer_botDB, progCode_botDB]
  exact ⟨2, snd_JustBot_vs_botDB k⟩

/-- **Prudent's prudence guard against `CIMCIC k` is TRUE in ℕ** at every `k` (`llm_outcome_CIMCIC_vs_PrudentBot`,
engine `(D, D)` by the floor `cimcic_pb_prudence_unprovable_tail`): CIMCIC's guard against `.bot DefectBot`
is self-refuting, so it defects there. -/
theorem floor_CIMCIC_vs_PrudentBot_true (k : ℕ) :
    ℕ↓[LAct] ⊧ sentenceAt (PrudentBot k) (CIMCIC k) phiPi := by
  rw [← sentenceAt_subst (PrudentBot k) (CIMCIC k) (properPlayer_PrudentBot k) (properPlayer_CIMCIC k) phiPi rfl]
  show ℕ↓[LAct] ⊧ sentenceAt (PrudentBot k) (CIMCIC k) (.plays (CIMCIC k) (.bot DefectBot) .D)
  rw [models_sentenceAt_plays _ _ _ _ _ (properPlayer_CIMCIC k) properPlayer_botDB, progCode_botDB]
  exact ⟨2, snd_CIMCIC_vs_botDB k⟩

end prudence

/-! ### 9. The settled halves at ONE threshold -/

section census

/-- **The floor verdict pass, the settled halves at one threshold**: the eventual halves of the thirteen
single-floor cells (Dupoc × DBot/EBot/CupodTroll, Just × DBot/EBot/CupodTroll, CIMCIC × CupodTroll/DBot/EBot,
Guardian × CIMCIC/Dupoc/Just, Cupod × OBot) — the non-floor side of each, unconditional in PA-`S'`. -/
theorem floor_settled_census :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 4 (progCode DBot) (progCode (DupocBot k)) (progCode DBot) (actCode .C) ∧
      EvalGraph 5 (progCode EBot) (progCode (DupocBot k)) (progCode EBot) (actCode .C) ∧
      EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (DupocBot k)) (progCode (CupodTrollBot k)) (actCode .C) ∧
      EvalGraph 4 (progCode DBot) (progCode (JustBot k)) (progCode DBot) (actCode .C) ∧
      EvalGraph 5 (progCode EBot) (progCode (JustBot k)) (progCode EBot) (actCode .C) ∧
      EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (JustBot k)) (progCode (CupodTrollBot k)) (actCode .C) ∧
      EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (CIMCIC k)) (progCode (CupodTrollBot k)) (actCode .C) ∧
      EvalGraph 4 (progCode DBot) (progCode (CIMCIC k)) (progCode DBot) (actCode .C) ∧
      EvalGraph 5 (progCode EBot) (progCode (CIMCIC k)) (progCode EBot) (actCode .C) ∧
      EvalGraph 2 (progCode (GuardianBot k)) (progCode (CIMCIC k)) (progCode (GuardianBot k)) (actCode .C) ∧
      EvalGraph 2 (progCode (GuardianBot k)) (progCode (DupocBot k)) (progCode (GuardianBot k)) (actCode .C) ∧
      EvalGraph 2 (progCode (GuardianBot k)) (progCode (JustBot k)) (progCode (GuardianBot k)) (actCode .C) ∧
      EvalGraph 5 (progCode OBot) (progCode (CupodBot k)) (progCode OBot) (actCode .D) := by
  obtain ⟨k₁, h₁⟩ := floor_DupocBot_vs_EBot_right
  obtain ⟨k₂, h₂⟩ := floor_JustBot_vs_EBot_right
  obtain ⟨k₃, h₃⟩ := floor_CIMCIC_vs_EBot_right
  obtain ⟨k₄, h₄⟩ := floor_GuardianBot_vs_CIMCIC_left
  obtain ⟨k₅, h₅⟩ := floor_GuardianBot_vs_DupocBot_left
  obtain ⟨k₆, h₆⟩ := floor_GuardianBot_vs_JustBot_left
  obtain ⟨k₇, h₇⟩ := floor_CupodBot_vs_OBot_right
  refine ⟨k₁ + k₂ + k₃ + k₄ + k₅ + k₆ + k₇, fun k hk ↦ ?_⟩
  exact ⟨floor_DupocBot_vs_DBot_right k, h₁ k (by omega), floor_DupocBot_vs_CupodTrollBot_right k,
    floor_JustBot_vs_DBot_right k, h₂ k (by omega), floor_JustBot_vs_CupodTrollBot_right k,
    floor_CIMCIC_vs_CupodTrollBot_right k, floor_CIMCIC_vs_DBot_right k, h₃ k (by omega),
    h₄ k (by omega), h₅ k (by omega), h₆ k (by omega), h₇ k (by omega)⟩

end census

end ArithS
