import PrisonersDilemma.Pf
import PrisonersDilemma.Theorems.LlmGenerations.CIMCIC
import PrisonersDilemma.Theorems.DupocBot

/-!
# Spike — the unified `Pf` DEMO ports (exclusion + cooperation, on real bots)

**2026-07-14: the core was PROMOTED** — `Pf`, `Pf_mono`, the exact round-trip
`pf_iff_provable`, `Pf_sound`, and the Löb/PBLT engines (`bloeb_engine_pf`,
`pblt_engine_pf`, `pblt_engine_id_pf`) now live in `PrisonersDilemma/Pf.lean`
(root-imported, namespace `PD`). This file keeps the two DEMO ports that validate the
design on real bots — they intentionally duplicate engine theorems, so they stay a spike:

1. **The CIMCIC exclusion** (negative side): the engine's TWO nested inductions
   (`cimcic_no_deriv_forbidden` + the 26-argument positional `Provable.rec` of
   `cimcic_no_provable_forbidden`, forced by the mutual block) become ONE flat
   `induction … with` over `Pf` with NAMED arms; the engine theorem
   `¬ Provable k (cimcic_guard k)` is re-derived through the iff.
2. **The DupocBot cooperation** (constructive side): the transparency legs as bare
   constructors (no `Provable.struct ⟨Derivation.…, _⟩` ceremony;
   `dupoc_mirror_loeb_premise_pf` turns a `hypSyll`-tree-in-glue into a flat
   `implTrans` of two leaves), and `outcome_DupocBot_vs_DupocBot'` (critch22 Thm 3.7)
   re-proved end-to-end inside `Pf`, exiting only via `Pf_sound`.

Design history: `Research/Notes/UNIFIED_PF_SKETCH.md`. Toy predecessor:
`UnifiedPfSpike.lean` (same directory).

NOT root-imported. Check:
  `lake env lean PrisonersDilemma/Research/Spikes/unified_pf/PfEngineSpike.lean`
-/

namespace PD.UnifiedPf

open PD PD.BaseTheorems

/-! ## 1. The demo port — CIMCIC vs DefectBot exclusion, ONE flat induction

Engine original (`Theorems/LlmGenerations/CIMCIC.lean`): TWO inductions —
`cimcic_no_deriv_forbidden` (9 named arms over `Derivation`) feeding the `struct` arm of
`cimcic_no_provable_forbidden` (a 26-argument POSITIONAL `Provable.rec`, forced by the
mutual block). Here: ONE `induction … with`, every arm NAMED, no nesting, no positional
lambda-counting. Reuses the engine's `CimcicForbiddenC` motive and
`cimcic_consequent_not_provable` (the false-atom refutation) verbatim. -/

open PD.Theorems PD.Bots in
/-- No `Pf` concludes a `Forbidden` formula — the unified replacement for BOTH
    `cimcic_no_deriv_forbidden` AND `cimcic_no_provable_forbidden`. -/
theorem cimcic_no_pf_forbidden (k : Nat) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ → ¬ CimcicForbiddenC k φ := by
  intro m φ h
  induction h with
  -- the execution bridge bottoms out on the false consequent atom
  | atom hatom =>
      intro hF
      cases hatom with
      | mk cert hle =>
          simp only [CimcicForbiddenC] at hF
          obtain ⟨hp, hq, ha⟩ := hF
          subst hp; subst hq; subst ha
          exact cimcic_consequent_not_provable k _ (Provable.atom (.mk cert hle))
  -- source-transparency leaves: the consequent's subject is a `.search`/`.sim`/`.ite`
  -- program, never `DefectBot` (= `.const .D`) — syntactic no-confusion.
  | searchBranch g ψ a b me opponent hme hle =>
      intro hF; subst hme; simp only [CimcicForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | simStep me p q opponent a hme hle =>
      intro hF; subst hme; simp only [CimcicForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | botSimStep me p q opponent a hme hle =>
      intro hF; subst hme; simp only [CimcicForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | botSearchStep g ψ a b me opponent hme hle =>
      intro hF; subst hme; simp only [CimcicForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | iteBranchSearch_t g z a' c0 c1 ψ q me opponent hme hle =>
      intro hF; subst hme; simp only [CimcicForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | searchThenSearch_t k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opponent hme _hprud hmk hle _ih =>
      intro hF; subst hme; simp only [CimcicForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  -- non-`.plays`/-`.impl` conclusions: the motive is `False` there.
  | eqRefl p hle => intro hF; simp only [CimcicForbiddenC] at hF
  | eqNeg p q hne hle => intro hF; simp only [CimcicForbiddenC] at hF
  | atomNeg p q b aN m' hatom hne hle => intro hF; simp only [CimcicForbiddenC] at hF
  | boxIntro kIn K φ' _hprem hle _ih => intro hF; simp only [CimcicForbiddenC] at hF
  | atomBoxImpl kBox p q a hatom hle => intro hF; simp only [CimcicForbiddenC] at hF
  | axK a b c m' K φ' α _hprem hgate hle _ih => intro hF; simp only [CimcicForbiddenC] at hF
  | box4 a b K φ' hgate hsz => intro hF; simp only [CimcicForbiddenC] at hF
  | diagB pm fb g K tgt _hgate hle _ih => intro hF; simp only [CimcicForbiddenC] at hF
  | axKf a b c K φ' α hgate hsz => intro hF; simp only [CimcicForbiddenC] at hF
  | boxMono a b K φ' hab hsz => intro hF; simp only [CimcicForbiddenC] at hF
  -- implication-forming rules: the motive peels the `.impl`; recurse on the premise
  -- that carries the consequent chain.
  | mp m₁ m₂ φ' α _h1 _h2 hle ih1 _ih2 => intro hF; exact ih1 hF
  | implTrans φ' ψ χ a b _h1 _h2 hle _ih1 ih2 => intro hF; exact ih2 hF
  | weakenImpl φ' ψ m' _hψ hle ih => intro hF; exact ih hF
  | impS2 φ' ψ χ m₁ m₂ K _h1 _h2 hle ih1 _ih2 => intro hF; exact ih1 hF
  | diagF pm fb g K tgt _hgate hle ih => intro hF; exact ih hF

open PD.Theorems in
/-- The engine's headline exclusion, RE-DERIVED through the round-trip: CIMCIC's guard
    against DefectBot is unprovable — `pf_of_provable` carries a hypothetical engine proof
    into `Pf`, where the ONE flat induction kills it. Byte-identical statement to the
    engine's `cimcic_guard_not_provable`. -/
theorem cimcic_guard_not_provable' (k : Nat) : ¬ Provable k (cimcic_guard k) := by
  intro h
  exact cimcic_no_pf_forbidden k (pf_of_provable h) ⟨rfl, rfl, rfl⟩

/-! ## 2. Bonus demo — the flat cooperation leg (no `struct ⟨…⟩` ceremony)

The engine builds a Löb leg as `Provable.struct ⟨Derivation.searchBranch …, size-proof⟩` —
reaching THROUGH the glue. In `Pf` the leg is the bare constructor. -/

example (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
    (hme : me = .search g ψ (.const a) (.const b))
    (hsz : (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k) :
    Pf k (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)) :=
  Pf.searchBranch g ψ a b me opponent hme hsz    -- one constructor, no embedding

/-! ## 3. The COOPERATION port — DupocBot self-play `(C, C)`, end-to-end in `Pf`

The constructive side of the ledger (the exclusion port above is the negative side). The
engine's pipeline: transparency leg (`Provable.struct ⟨Derivation.…, size⟩`) →
`bloeb_engine` (the 14-step internalized GL chain) → `pblt_engine_id` → soundness →
`outcome`. The engines are ported in `PrisonersDilemma/Pf.lean`; here are the bot-facing
pieces. -/

open PD.Bots

/-- The DUPOC Löb premise as ONE bare leaf — no `Provable.struct ⟨Derivation.…, _⟩`
    ceremony (compare `Theorems/DupocBot.lean: dupoc_loeb_premise`). Same honest
    transcript `5·log2 k + 33`. -/
theorem dupoc_loeb_premise_pf (k : Nat) :
    Pf (5 * Nat.log2 k + 33)
      (.impl (.box k (.plays (DupocBot k) (DupocBot k) .C))
             (.plays (DupocBot k) (DupocBot k) .C)) := by
  refine Pf.searchBranch k (.plays .opp .self .C) .C .D (DupocBot k) (DupocBot k) rfl ?_
  simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot]
  omega

/-- The SHOWCASE: the DupocBot×MirrorBot Löb premise. Engine version
    (`dupoc_mirror_loeb_premise`): a `Derivation.hypSyll` TREE (searchBranch + simStep)
    embedded through `Provable.struct` — build a `Type`-level object, then glue. Here: a
    flat `Pf.implTrans` of two bare leaves — the same two transparency steps as siblings,
    each leaf charged its own conclusion, the chain charged the sum. Same total budget
    `20·log2 k + 150`. -/
theorem dupoc_mirror_loeb_premise_pf (k : Nat) :
    Pf (20 * Nat.log2 k + 150)
      (.impl (.box k (.plays MirrorBot (DupocBot k) .C))
             (.plays MirrorBot (DupocBot k) .C)) := by
  refine Pf.implTrans _ _ _ (5 * Nat.log2 k + 50) (5 * Nat.log2 k + 50)
    (Pf.searchBranch k (.plays .opp .self .C) .C .D (DupocBot k) MirrorBot rfl ?_)
    (Pf.simStep MirrorBot .opp .self (DupocBot k) .C rfl ?_) ?_ <;>
  · simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size,
      DupocBot, MirrorBot]
    omega

/-- **DUPOC self-play cooperates — critch22 Theorem 3.7, re-proved end-to-end in `Pf`.**
    Statement byte-identical to the engine's `outcome_DupocBot_vs_DupocBot`; the whole
    Löb argument (premise → chain → PBLT) runs inside `Pf`, exiting only through
    `Pf_sound` to collapse provability into a `play` witness. -/
theorem outcome_DupocBot_vs_DupocBot' :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DupocBot k) (DupocBot k) = some (.C, .C) := by
  let φ : Nat → Formula := fun k => .plays (DupocBot k) (DupocBot k) .C
  have hLoeb :
      ∀ k, k > 0 →
        Pf (5 * Nat.log2 k + 33) (.impl (.box k (φ k)) (φ k)) := by
    intro k _
    exact dupoc_loeb_premise_pf k
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays (DupocBot k) (DupocBot k) .C).size ≤ _
    simp only [numCost, Formula.size, Prog.size, DupocBot]
    omega
  have hpm : ∀ k, 5 * Nat.log2 k + 33 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id_pf φ (fun k => 5 * Nat.log2 k + 33) 0 hφsz hpm hLoeb
  refine ⟨k₂, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := Pf_sound hm
  obtain ⟨n, hn⟩ := hInterp
  refine ⟨n, ?_⟩
  simp [outcome, hn]

/-! ## VERDICT

* `Pf` (22 constructors, ONE type, `Prop`-valued with the budget as an index) typechecks
  against the REAL engine and is now a BUILD module (`PrisonersDilemma/Pf.lean`) with the
  exact transfer theorem `pf_iff_provable`.
* The CIMCIC exclusion port: 2 nested inductions / 25 arms / positional 26-lambda
  `Provable.rec` → 1 named `induction … with` / 22 arms / no nesting. The engine theorem
  is recovered through the iff (`cimcic_guard_not_provable'`).
* The COOPERATION port (both sides of the ledger demonstrated): the full internalized
  Löb pipeline — `bloeb_engine_pf` (a pure rename: nothing in the 14-step chain was
  `Provable`-specific), the transparency legs WITHOUT the `struct ⟨Derivation.…⟩`
  ceremony (`dupoc_mirror_loeb_premise_pf`: a `hypSyll`-tree-in-glue becomes a flat
  `implTrans` of two bare leaves), and `outcome_DupocBot_vs_DupocBot'` (critch22 Thm 3.7)
  re-proved end-to-end inside `Pf`, exiting only via `Pf_sound`.
* Everything compiles with ZERO axioms beyond Lean's 3 standard ones (inherited from the
  engine; nothing new postulated).

What this does NOT yet do (the honest boundary): make `Pf` PRIMITIVE.
`PlaysProof.search_t` still consumes `Provable`, the metatheory (T31–T54) still speaks
`Derivation`/`Provable`, and retiring those means mutualizing `Pf` with the execution
layer and re-proving ~16k lines — see
`Research/Notes/PF_REPLACEMENT_ASSESSMENT.md` for the full replacement analysis. -/

#check @cimcic_no_pf_forbidden
#check @cimcic_guard_not_provable'
#check @outcome_DupocBot_vs_DupocBot'

-- Axiom audit: expect at most Lean's standard three (propext, Classical.choice, Quot.sound).
#print axioms cimcic_guard_not_provable'
#print axioms outcome_DupocBot_vs_DupocBot'

end PD.UnifiedPf
