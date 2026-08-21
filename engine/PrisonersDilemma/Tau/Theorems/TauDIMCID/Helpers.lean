import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Tau.Theorems.TauCIMCIC.Helpers

/-!
# Tau/Theorems/TauDIMCID/Helpers — the asymmetric `.impl`-guard row

τ(DIMCID)'s guard at hypothesis T is `me coops with I_T → I_T DEFECTS on me`
(`dimG`), searched at budget k, firing `D` with default `C` — CIMCIC's twin at the
opposite consequent polarity. The row splits by what the consequent costs:

* **provable** (defect, ebot, obot, guardian, dbot, cupodTroll, and the
  DIAGONAL): `weakenImpl` turns a certificate of the partner's DEFECTION into the
  implication and DIMCID defects. Note the inversion against CIMCIC: the cells
  where CIMCIC's row is floor-blocked are exactly the ones whose defection is a
  cheap positive atom here.
* **false or floor-priced** (coop, tftSim, tftPf, just): the consequent claims a
  cooperator defects — refutable or uncitable — so the search fails and DIMCID
  falls through to its trusting default.
* **entangled** (dupoc, cupod, cimcic): `.sys` systems, resolved by the alignment
  rule (`_resolve_entangled`'s Lean counterpart) in the sections below.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## The guard shape -/

/-- The substituted DIMCID guard: frame `me`, hypothesis instance `I`. -/
abbrev dimG (me I : Prog) : Formula :=
  .impl (.plays me (.bot I) Action.C) (.plays (.bot I) me Action.D)

/-- The stored guard substitutes to `dimG` — `.self` is the only pronoun in it. -/
theorem dimG_subst (I me o : Prog) :
    (Formula.impl (.plays .self (.bot I) Action.C)
                  (.plays (.bot I) .self Action.D)).subst me o
      = dimG me I := rfl

/-- `weakenImpl`, packaged: a provable DEFECTION consequent fires DIMCID's guard. -/
theorem pf_dimG_of_consequent {K m : Nat} {me I : Prog}
    (h : Pf m (.plays (.bot I) me Action.D))
    (hK : m + (dimG me I).size ≤ K) :
    Pf K (dimG me I) :=
  Pf.weakenImpl _ _ m h hK

/-! ## Generic play lemmas for the fire-D / default-C stage -/

/-- A prove-stage firing `D` defects when its substituted guard is provable… -/
theorem searchGuardD_plays_D {k : Nat} {g : Formula} (me opp : Prog)
    (h : proofSearch k (g.subst me opp) = true) :
    ∃ N, eval N me opp (.search k g (.const .D) (.const .C)) = some Action.D := by
  refine ⟨2, ?_⟩
  rw [eval, h]
  rfl

/-- …and cooperates when it is not. -/
theorem searchGuardD_plays_C {k : Nat} {g : Formula} (me opp : Prog)
    (h : proofSearch k (g.subst me opp) = false) :
    ∃ N, eval N me opp (.search k g (.const .D) (.const .C)) = some Action.C := by
  refine ⟨2, ?_⟩
  rw [eval, h, if_neg (by simp)]
  rfl

/-! ## THE DIAGONAL — a genuine Löb fixpoint on DEFECTION

CIMCIC's diagonal was free (`implRefl`: after subst its guard is `φ → φ`).
DIMCID's is not: the substituted guard is `φ → ψ` where φ and ψ name the SAME
player at OPPOSITE actions ("if I cooperate with myself, I defect against
myself"). It closes by bounded Löb exactly as base
`llm_outcome_DIMCID_vs_DIMCID` does — provable self-defection makes the guard
true by `implK`, the search fires, and the fire-action IS `D`. Self-fulfilling
suspicion. -/

/-- The Löb premise, box-subscript parameterized (as base `dimcid_loeb_premise`):
    `□_b(self-defection) → self-defection` whenever `b` leaves `axK` room. Via
    `implK` (`D → (C → D)`) pushed under the box, then chained with the
    `botSearchStep` reading of DIMCID's own frozen source.

    Stated over the PEELED program (`Dq k`) rather than `inst … .dimcid .dimcid`
    so every `Formula.size` side-condition stays syntactically transparent to
    `omega` — an opaque `set`/`let` binding hides them and the arithmetic fails. -/
private abbrev Dq (k : Nat) : Prog :=
  .search k (.impl (.plays .self .self Action.C) (.plays .self .self Action.D))
    (.const .D) (.const .C)

private theorem dimcid_quine_loeb_premise (k b : Nat)
    (hb : b + 10 * Nat.log2 k + 140 ≤ k) :
    Pf (100 * Nat.log2 k + 100000)
      (.impl (.box b (probeD (Dq k))) (probeD (Dq k))) := by
  -- leg 1: S reads the frozen searcher's own source
  have leg1 : Pf ((Formula.impl
        (.box k (.impl (.plays (.bot (Dq k)) (.bot (Dq k)) Action.C)
                       (.plays (.bot (Dq k)) (.bot (Dq k)) Action.D)))
        (.plays (.bot (Dq k)) (.bot (Dq k)) Action.D)).size)
      (.impl (.box k (.impl (.plays (.bot (Dq k)) (.bot (Dq k)) Action.C)
                            (.plays (.bot (Dq k)) (.bot (Dq k)) Action.D)))
             (.plays (.bot (Dq k)) (.bot (Dq k)) Action.D)) := by
    have := Pf.botSearchStep k
      (.impl (.plays .self .self Action.C) (.plays .self .self Action.D))
      Action.D Action.C (.bot (Dq k)) (.bot (Dq k)) rfl (Nat.le_refl _)
    simpa [Formula.subst, Prog.subst] using this
  -- leg 2: `D → (C → D)` boxed, then distributed by axK
  have step1 := Pf.implK (.plays (.bot (Dq k)) (.bot (Dq k)) Action.D)
      (.plays (.bot (Dq k)) (.bot (Dq k)) Action.C) (Nat.le_refl _)
  have step2 := Pf.boxIntro _ _ _ step1 (Nat.le_refl _)
  have step3 := Pf.axK _ b k _ _
      (.plays (.bot (Dq k)) (.bot (Dq k)) Action.D)
      (.impl (.plays (.bot (Dq k)) (.bot (Dq k)) Action.C)
             (.plays (.bot (Dq k)) (.bot (Dq k)) Action.D))
      step2
      (by simp only [Dq, Formula.size, Prog.size, numCost] at hb ⊢; omega)
      (Nat.le_refl _)
  have hchain := Pf.implTrans _ _ _ _ _ step3 leg1 (Nat.le_refl _)
  refine Pf_mono hchain ?_
  -- Two `Nat.log2` applications block `omega`: one on the VARIABLE box subscript
  -- `b` (bounded by `hb` through `log2_mono`), one on a compound size (bounded by
  -- `log2_le_self` after `generalize` names its argument). The base
  -- `dimcid_loeb_premise` spells the latter out by hand; naming it is the robust
  -- form.
  have hlog := Nat.log2_le_self k
  have hlogb : Nat.log2 b ≤ Nat.log2 k := log2_mono (by omega)
  simp only [probeD, Dq, Formula.size, Prog.size, numCost]
  generalize hA : (Nat.log2 k + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1 + 1 + 1 + 1 +
              (Nat.log2 k + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1 + 1 + 1 + 1) +
            1 +
          (Nat.log2 k + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1 + 1 + 1 + 1 +
                  (Nat.log2 k + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1 + 1 + 1 + 1) +
                1 +
              (Nat.log2 k + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1 + 1 + 1 + 1 +
                  (Nat.log2 k + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1 + 1 + 1 + 1) +
                1) +
            1) +
        1) = A
  have hA2 : Nat.log2 A ≤ A := log2_le_self A
  omega

/-- From an actual DEFECTING play of the wrapped quine against itself, the guard
    must have fired (eval inversion — a failed search takes the trusting C).

    NOTE the guard here is DIMCID's IMPLICATION, not the `probeD` atom: the
    quine's guard and its conclusion are different formulas (that is exactly what
    distinguishes this diagonal from Cupod's). -/
private theorem dimcid_probeD_true_of_play (k n : Nat)
    (h : play n (.bot (Dq k)) (.bot (Dq k)) = some .D) :
    proofSearch k
      ((Formula.impl (.plays .self .self Action.C)
                     (.plays .self .self Action.D)).subst (.bot (Dq k)) (.bot (Dq k)))
      = true := by
  cases hps : proofSearch k
      ((Formula.impl (.plays .self .self Action.C)
                     (.plays .self .self Action.D)).subst (.bot (Dq k)) (.bot (Dq k))) with
  | true => rfl
  | false =>
      exfalso
      match n with
      | 0 => simp [play, eval, Dq] at h
      | 1 => simp [play, eval, Dq] at h
      | 2 => simp [play, eval, Dq, hps] at h
      | n + 3 => simp [play, eval, Dq, hps] at h

/-- **THE LÖB BIT**: past a threshold τ(DIMCID)'s self-DEFECTION atom is provable.

    The fixpoint runs on the atom `probeD (Dq k)` ("the quine defects against
    itself"), exactly as base `llm_outcome_DIMCID_vs_DIMCID` does; the guard is
    then provable from it by `implK` (that is what
    `dimcid_quine_loeb_premise` internalizes). Box subscript `f k = k - O(log k)`:
    `axK` must fit the consequent, so the staggering is forced — the same one the
    base proof needs. -/
theorem ps_probeD_dimcid_quine :
    ∃ k₂, ∀ k, k₂ < k → proofSearch k (probeD (Dq k)) = true := by
  set φ : Nat → Formula := fun k => probeD (Dq k) with hφ
  set f : Nat → Nat := fun k => k - (10 * Nat.log2 k + 140) with hf
  set pm : Nat → Nat := fun k => 100 * Nat.log2 k + 100000 with hpm
  obtain ⟨Kc, hKc⟩ := linear_log2_add_le 10 140
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le (8192 * 103 + 10) (8192 * 100034 + 140)
  have hLoeb : ∀ k, k > max Kc Ksz → Pf (pm k) (.impl (.box (f k) (φ k)) (φ k)) := by
    intro k hk
    have hc : 10 * Nat.log2 k + 140 ≤ k :=
      hKc k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_left _ _) hk))
    have hcancel : f k + (10 * Nat.log2 k + 140) = k := Nat.sub_add_cancel hc
    exact dimcid_quine_loeb_premise k (f k) (by omega)
  have hsz : ∀ k, k > max Kc Ksz →
      8192 * (pm k + (φ k).size + Nat.log2 (f k) + 8) ≤ f k := by
    intro k hk
    have hc : 10 * Nat.log2 k + 140 ≤ k :=
      hKc k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_left _ _) hk))
    have hcancel : f k + (10 * Nat.log2 k + 140) = k := Nat.sub_add_cancel hc
    have hlogf : Nat.log2 (f k) ≤ Nat.log2 k := log2_mono (by omega)
    have hbig := hKsz k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
    have hφsz : (φ k).size = 2 * Nat.log2 k + 25 := by
      simp only [hφ, probeD, Dq, Formula.size, Prog.size, numCost]
      omega
    rw [hφsz]
    simp only [hpm]
    omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine φ f pm (max Kc Ksz) hLoeb hsz
  obtain ⟨Kt, hKt⟩ := linear_log2_add_le 1 8
  refine ⟨max k₂ Kt, fun k hk => ?_⟩
  have hkt : 1 * Nat.log2 k + 8 ≤ k :=
    hKt k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  obtain ⟨m, hm⟩ := hk₂ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  obtain ⟨n, hn⟩ := Pf_sound m _ hm
  -- the atom is TRUE; a true self-defection means the guard fired
  have hplay : play n (.bot (Dq k)) (.bot (Dq k)) = some .D := hn
  have hguard := dimcid_probeD_true_of_play k n hplay
  -- and a fired guard makes the atom provable at budget k (search_t, cheap cite)
  refine (proofSearch_spec _ _).2 ?_
  refine Pf.atom ⟨PlaysProof.bot (PlaysProof.search_t
    ((proofSearch_spec _ _).1 hguard) PlaysProof.const), ?_⟩
  have := hcl; have := hcn
  simp only [c_guard, numCost]
  omega

/-- **τ(DIMCID) DEFECTS AGAINST ITSELF** past the Löb threshold. -/
theorem dimcid_quine_plays_D {k : Nat}
    (hq : proofSearch k
      ((Formula.impl (.plays .self .self Action.C)
                     (.plays .self .self Action.D)).subst (.bot (Dq k)) (.bot (Dq k)))
      = true) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .dimcid))
      (.bot (inst (tauZoo k) .dimcid .dimcid)) (inst (tauZoo k) .dimcid .dimcid)
      = some Action.D := by
  rw [inst_dimcid_quine k]
  exact searchGuardD_plays_D _ _ hq

end PD.Tau
